/**CFile****************************************************************

  FileName    [wlcReadSmt.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcReadSmt.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// parser name types
typedef enum { 
    PRS_SMT_NONE = 0, 
    PRS_SMT_INPUT,    
    PRS_SMT_CONST,    
    PRS_SMT_LET,   
    PRS_SMT_ASSERT
} Prs_ManType_t; 

// parser
typedef struct Prs_Smt_t_ Prs_Smt_t;
struct Prs_Smt_t_
{
    // input data
    char *       pName;       // file name
    char *       pBuffer;     // file contents
    char *       pLimit;      // end of file
    char *       pCur;        // current position
    Abc_Nam_t *  pStrs;       // string manager
    // network structure
    Vec_Int_t    vData;       
    // error handling
    char ErrorStr[1000];      
};


// create error message
static inline int Prs_SmtErrorSet( Prs_Smt_t * p, char * pError, int Value )
{
    assert( !p->ErrorStr[0] );
    sprintf( p->ErrorStr, "%s", pError );
    return Value;
}
// clear error message
static inline void Prs_SmtErrorClear( Prs_Smt_t * p )
{
    p->ErrorStr[0] = '\0';
}
// print error message
static inline int Prs_SmtErrorPrint( Prs_Smt_t * p )
{
    char * pThis; int iLine = 0;
    if ( !p->ErrorStr[0] ) return 1;
    for ( pThis = p->pBuffer; pThis < p->pCur; pThis++ )
        iLine += (int)(*pThis == '\n');
    printf( "Line %d: %s\n", iLine, p->ErrorStr );
    return 0;
}
static inline char * Prs_SmtLoadFile( char * pFileName, char ** ppLimit )
{
    char * pBuffer;
    int nFileSize, RetValue;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open input file.\n" );
        return NULL;
    }
    // get the file size, in bytes
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile );  
    // move the file current reading position to the beginning
    rewind( pFile ); 
    // load the contents of the file into memory
    pBuffer = ABC_ALLOC( char, nFileSize + 3 );
    pBuffer[0] = '\n';
    RetValue = fread( pBuffer+1, nFileSize, 1, pFile );
    // terminate the string with '\0'
    pBuffer[nFileSize + 0] = '\n';
    pBuffer[nFileSize + 1] = '\0';
    *ppLimit = pBuffer + nFileSize + 2;
    return pBuffer;
}
static inline Prs_Smt_t * Prs_SmtAlloc( char * pFileName )
{
    Prs_Smt_t * p;
    char * pBuffer, * pLimit;
    pBuffer = Prs_SmtLoadFile( pFileName, &pLimit );
    if ( pBuffer == NULL )
        return NULL;
    p = ABC_CALLOC( Prs_Smt_t, 1 );
    p->pName   = pFileName;
    p->pBuffer = pBuffer;
    p->pLimit  = pLimit;
    p->pCur    = pBuffer;
    p->pStrs   = Abc_NamStart( 1000, 24 );
    Vec_IntGrow ( &p->vData, 1000 );
    return p;
}

static inline void Prs_SmtFree( Prs_Smt_t * p )
{
    if ( p->pStrs )
        Abc_NamDeref( p->pStrs );
    Vec_IntErase( &p->vData );
    ABC_FREE( p->pBuffer );
    ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Prs_SmtRemoveComments( Prs_Smt_t * p )
{
    char * pTemp;
    for ( pTemp = p->pBuffer; pTemp < p->pLimit; pTemp++ )
        if ( *pTemp == ';' )
            while ( *pTemp && *pTemp != '\n' )
                *pTemp++ = ' ';
}
static inline void Prs_SmtSkipSpaces( Prs_Smt_t * p )
{
    while ( *p->pCur == ' ' || *p->pCur == '\t' || *p->pCur == '\r' || *p->pCur == '\n' )
        p->pCur++;
}
static inline int Prs_SmtIsWord( Prs_Smt_t * p, char * pWord )
{
    Prs_SmtSkipSpaces( p );
    if ( strncmp( p->pCur, pWord, strlen(pWord) ) )
        return 0;
    p->pCur += strlen(pWord);
    Prs_SmtSkipSpaces( p );
    return 1;
}
static inline char * Prs_SmtFindNextPar( Prs_Smt_t * p )
{
    char * pTemp; int Count = 1;
    for ( pTemp = p->pCur; pTemp < p->pLimit; pTemp++ )
    {
        if ( *pTemp == '(' )
            Count++;
        else if ( *pTemp == ')' )
            Count--;
        if ( Count == 0 )
            break;
    }
    assert( *pTemp == ')' );
    return pTemp;
}
static inline int Prs_SmtParseLet( Prs_Smt_t * p, char * pLimit, int Type )
{
    char * pToken;
    assert( *pLimit == ')' );
    *pLimit = 0;
    Vec_IntPush( &p->vData, 0 );
    Vec_IntPush( &p->vData, Type );
    pToken = strtok( p->pCur, " ()" );
    while ( pToken )
    {
        if ( pToken[0] != '_' && pToken[0] != '=' )
            Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, pToken, NULL) );
        pToken = strtok( NULL, " ()" );
    }
    assert( *pLimit == 0 );
    *pLimit = ')';
    p->pCur = pLimit;
    return 1;
}
static inline int Prs_SmtParseFun( Prs_Smt_t * p, char * pLimit, int Type )
{
    char * pToken;
    assert( *pLimit == ')' );
    *pLimit = 0;
    Vec_IntPush( &p->vData, 0 );
    Vec_IntPush( &p->vData, Type );
    pToken = strtok( p->pCur, " ()" );
    assert( pToken != NULL );
    Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, pToken, NULL) );
    pToken = strtok( NULL, " ()" );
    if ( pToken[0] == '_' )
        pToken = strtok( NULL, " ()" );
    if ( !strcmp(pToken, "Bool") )
    {
        Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, "1", NULL) );
        pToken = strtok( NULL, " ()" );
        if ( !strcmp(pToken, "false") )
            Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, "#b0", NULL) );
        else if ( !strcmp(pToken, "true") )
            Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, "#b1", NULL) );
        else assert( 0 );
    }
    else if ( !strcmp(pToken, "BitVec") )
    {
        pToken = strtok( NULL, " ()" );
        Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, pToken, NULL) );
        pToken = strtok( NULL, " ()" );
        if ( pToken )
        {
            Vec_IntPush( &p->vData, Abc_NamStrFindOrAdd(p->pStrs, pToken, NULL) );
            pToken = strtok( NULL, " ()" );
            if ( pToken != NULL )
                return Prs_SmtErrorSet(p, "Trailing symbols are not recognized.", 0);
        }
    }
    else 
        return Prs_SmtErrorSet(p, "Expecting either \"Bool\" or \"BitVec\".", 0);
    assert( *pLimit == 0 );
    *pLimit = ')';
    p->pCur = pLimit;
    return 1;
}
int Prs_SmtReadLines( Prs_Smt_t * p )
{
    Prs_SmtSkipSpaces( p );
    while ( *p->pCur == '(' )
    {
        p->pCur++;
        if ( Prs_SmtIsWord(p, "let") )
        {
            assert( *p->pCur == '(' );
            p->pCur++;
            if ( !Prs_SmtParseLet( p, Prs_SmtFindNextPar(p), PRS_SMT_LET ) )
                return 0;
            assert( *p->pCur == ')' );
            p->pCur++;
        }
        else if ( Prs_SmtIsWord(p, "declare-fun")  )
        {
            if ( !Prs_SmtParseFun( p, Prs_SmtFindNextPar(p), PRS_SMT_INPUT ) )
                return 0;
            assert( *p->pCur == ')' );
            p->pCur++;
        }
        else if ( Prs_SmtIsWord(p, "define-fun") )
        {
            if ( !Prs_SmtParseFun( p, Prs_SmtFindNextPar(p), PRS_SMT_CONST ) )
                return 0;
            assert( *p->pCur == ')' );
            p->pCur++;
        }
        else if ( Prs_SmtIsWord(p, "check-sat") )
        {
            Vec_IntPush( &p->vData, 0 );
            return 1;
        }
        else if ( Prs_SmtIsWord(p, "assert") )
        {}
        else if ( Prs_SmtIsWord(p, "set-option") || Prs_SmtIsWord(p, "set-logic") )
            p->pCur = Prs_SmtFindNextPar(p) + 1;
        else
            break;
            //return Prs_SmtErrorSet(p, "Unsupported directive.", 0);
        Prs_SmtSkipSpaces( p );
    }
    // finish parsing assert
    if ( !Prs_SmtParseLet( p, Prs_SmtFindNextPar(p), PRS_SMT_ASSERT ) )
        return 0;
    assert( *p->pCur == ')' );
    Vec_IntPush( &p->vData, 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Prs_SmtPrintParser( Prs_Smt_t * p )
{
    int Entry, i;
    Vec_IntForEachEntry( &p->vData, Entry, i )
    {
        if ( Entry == 0 )
        {
            printf( "\n" );
            if ( i == Vec_IntSize(&p->vData) - 1 )
                break;
            Entry = Vec_IntEntry(&p->vData, ++i);
            if ( Entry == PRS_SMT_INPUT )
                printf( "declare-fun" );
            else if ( Entry == PRS_SMT_CONST )
                printf( "define-fun" );
            else if ( Entry == PRS_SMT_LET )
                printf( "let" );
            else if ( Entry == PRS_SMT_ASSERT )
                printf( "assert" );
            else assert(0);
            continue;
        }
        printf( " %s", Abc_NamStr(p->pStrs, Entry) );
    }
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Prs_SmtReadConstant( Wlc_Ntk_t * pNtk, char * pStr, int nBits, Vec_Int_t * vFanins, char * pName )
{
    char Buffer[100];
    int i, nDigits, iObj, NameId, fFound;
    Vec_IntClear( vFanins );
    if ( pStr[0] != '#' )
    {
        // handle decimal number
        int Number = atoi( pStr );
        nBits = Abc_Base2Log( Number+1 );
        assert( nBits < 32 );
        Vec_IntPush( vFanins, Number );
    }
    else if ( pStr[1] == 'b' )
    {
        if ( nBits == -1 )
            nBits = strlen(pStr+2);
        Vec_IntFill( vFanins, Abc_BitWordNum(nBits), 0 );
        for ( i = 0; i < nBits; i++ )
            if ( pStr[2+i] == '1' )
                Abc_InfoSetBit( (unsigned *)Vec_IntArray(vFanins), nBits-1-i );
            else if ( pStr[2+i] != '0' )
                return 0;
    }
    else if ( pStr[1] == 'x' )
    {
        if ( nBits == -1 )
            nBits = strlen(pStr+2)*4;
        Vec_IntFill( vFanins, Abc_BitWordNum(nBits), 0 );
        nDigits = Abc_TtReadHexNumber( (word *)Vec_IntArray(vFanins), pStr+2 );
        if ( nDigits != (nBits + 3)/4 )
            assert( 0 );
    }
    else return 0;
    // create constant node
    iObj = Wlc_ObjAlloc( pNtk, WLC_OBJ_CONST, 0, nBits-1, 0 );
    Wlc_ObjAddFanins( pNtk, Wlc_NtkObj(pNtk, iObj), vFanins );
    // add node's name
    if ( pName == NULL )
    {
        sprintf( Buffer, "_c%d_", iObj );
        pName = Buffer;
    }
    NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pName, &fFound );
    assert( !fFound );
    assert( iObj == NameId );
    return NameId;
}
static inline int Prs_SmtReadName( Wlc_Ntk_t * pNtk, char * pStr, int nBits, Vec_Int_t * vFanins )
{
    if ( (pStr[0] >= '0' && pStr[0] <= '9') || pStr[0] == '#' )
    {
        Vec_Int_t * vTemp = Vec_IntAlloc(0);
        int NameId = Prs_SmtReadConstant( pNtk, pStr, nBits, vTemp, NULL );
        Vec_IntFree( vTemp );
        if ( !NameId )
            return 0;
        Vec_IntPush( vFanins, NameId );
        return 1;
    }
    else
    {
        // read name
        int fFound, NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pStr, &fFound );
        assert( fFound );
        Vec_IntPush( vFanins, NameId );
        return 1;
    }
}
static inline int Prs_SmtStrToType( char * pName )
{
    int Type = 0;
    if ( !strcmp(pName, "ite") )
        Type = WLC_OBJ_MUX;           // 08: multiplexer
    else if ( !strcmp(pName, "bvlshr") )
        Type = WLC_OBJ_SHIFT_R;       // 09: shift right
    else if ( !strcmp(pName, "bvashr") )
        Type = WLC_OBJ_SHIFT_RA;      // 10: shift right (arithmetic)
    else if ( !strcmp(pName, "bvshl") )
        Type = WLC_OBJ_SHIFT_L;       // 11: shift left
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_SHIFT_LA;    // 12: shift left (arithmetic)
    else if ( !strcmp(pName, "rotate_right") )
        Type = WLC_OBJ_ROTATE_R;      // 13: rotate right
    else if ( !strcmp(pName, "rotate_left") )
        Type = WLC_OBJ_ROTATE_L;      // 14: rotate left
    else if ( !strcmp(pName, "bvnot") )
        Type = WLC_OBJ_BIT_NOT;       // 15: bitwise NOT
    else if ( !strcmp(pName, "bvand") )
        Type = WLC_OBJ_BIT_AND;       // 16: bitwise AND
    else if ( !strcmp(pName, "bvor") )
        Type = WLC_OBJ_BIT_OR;        // 17: bitwise OR
    else if ( !strcmp(pName, "bvxor") )
        Type = WLC_OBJ_BIT_XOR;       // 18: bitwise XOR
    else if ( !strcmp(pName, "extract") )
        Type = WLC_OBJ_BIT_SELECT;    // 19: bit selection
    else if ( !strcmp(pName, "concat") )
        Type = WLC_OBJ_BIT_CONCAT;    // 20: bit concatenation
    else if ( !strcmp(pName, "zero_extend") )
        Type = WLC_OBJ_BIT_ZEROPAD;   // 21: zero padding
    else if ( !strcmp(pName, "sign_extend") )
        Type = WLC_OBJ_BIT_SIGNEXT;   // 22: sign extension
    else if ( !strcmp(pName, "not") )
        Type = WLC_OBJ_LOGIC_NOT;     // 23: logic NOT
    else if ( !strcmp(pName, "and") )
        Type = WLC_OBJ_LOGIC_AND;     // 24: logic AND
    else if ( !strcmp(pName, "or") )
        Type = WLC_OBJ_LOGIC_OR;      // 25: logic OR
    else if ( !strcmp(pName, "bvcomp") )
        Type = WLC_OBJ_COMP_EQU;      // 26: compare equal
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_COMP_NOTEQU;   // 27: compare not equal
    else if ( !strcmp(pName, "bvult") )
        Type = WLC_OBJ_COMP_LESS;     // 28: compare less
    else if ( !strcmp(pName, "bvugt") )
        Type = WLC_OBJ_COMP_MORE;     // 29: compare more
    else if ( !strcmp(pName, "bvule") )
        Type = WLC_OBJ_COMP_LESSEQU;  // 30: compare less or equal
    else if ( !strcmp(pName, "bvuge") )
        Type = WLC_OBJ_COMP_MOREEQU;  // 31: compare more or equal
    else if ( !strcmp(pName, "bvredand") )
        Type = WLC_OBJ_REDUCT_AND;    // 32: reduction AND
    else if ( !strcmp(pName, "bvredor") )
        Type = WLC_OBJ_REDUCT_OR;     // 33: reduction OR
    else if ( !strcmp(pName, "bvredxor") )
        Type = WLC_OBJ_REDUCT_XOR;    // 34: reduction XOR
    else if ( !strcmp(pName, "bvadd") )
        Type = WLC_OBJ_ARI_ADD;       // 35: arithmetic addition
    else if ( !strcmp(pName, "bvsub") )
        Type = WLC_OBJ_ARI_SUB;       // 36: arithmetic subtraction
    else if ( !strcmp(pName, "bvmul") )
        Type = WLC_OBJ_ARI_MULTI;     // 37: arithmetic multiplier
    else if ( !strcmp(pName, "bvdiv") )
        Type = WLC_OBJ_ARI_DIVIDE;    // 38: arithmetic division
    else if ( !strcmp(pName, "bvurem") )
        Type = WLC_OBJ_ARI_MODULUS;   // 39: arithmetic modulus
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_ARI_POWER;     // 40: arithmetic power
    else if ( !strcmp(pName, "bvneg") )
        Type = WLC_OBJ_ARI_MINUS;     // 41: arithmetic minus
//    else if ( !strcmp(pName, "") )
//        Type = WLC_OBJ_TABLE;         // 42: bit table
    else assert( 0 );
    return Type;
}
static inline int Prs_SmtReadNode( Prs_Smt_t * p, Wlc_Ntk_t * pNtk, Vec_Int_t * vData, int i, Vec_Int_t * vFanins, int * pRange )
{
    int Type, NameId;
    char * pName = Abc_NamStr( p->pStrs, Vec_IntEntry(vData, i) );
    // read type
    Type = Prs_SmtStrToType( pName );
    if ( Type == 0 )
        return 0;
    *pRange = 0;
    Vec_IntClear( vFanins );
    if ( Type == WLC_OBJ_COMP_EQU )
    {
        *pRange = 1;
        Prs_SmtReadName( pNtk, Abc_NamStr(p->pStrs, Vec_IntEntry(vData, ++i)), -1, vFanins );
        Prs_SmtReadName( pNtk, Abc_NamStr(p->pStrs, Vec_IntEntry(vData, ++i)), -1, vFanins );
        return WLC_OBJ_COMP_EQU;
    }
    else if ( Type == WLC_OBJ_LOGIC_NOT )
    {
        pName  = Abc_NamStr( p->pStrs, Vec_IntEntry(vData, ++i) );
        if ( !strcmp(pName, "bvcomp") )
        {
            *pRange = 1;
            Prs_SmtReadName( pNtk, Abc_NamStr(p->pStrs, Vec_IntEntry(vData, ++i)), -1, vFanins );
            Prs_SmtReadName( pNtk, Abc_NamStr(p->pStrs, Vec_IntEntry(vData, ++i)), -1, vFanins );
            return WLC_OBJ_COMP_NOTEQU;   // 26: compare equal
        }
        i--;
    }
    else if ( Type == WLC_OBJ_BIT_SELECT )
    {
        int End, Beg;
        pName = Abc_NamStr( p->pStrs, Vec_IntEntry(vData, ++i) );
        End = atoi( pName );
        pName = Abc_NamStr( p->pStrs, Vec_IntEntry(vData, ++i) );
        Beg = atoi( pName );
        pName = Abc_NamStr( p->pStrs, Vec_IntEntry(vData, ++i) );
        Prs_SmtReadName( pNtk, pName, -1, vFanins );
        Vec_IntPush( vFanins, (End << 16) | Beg );
        *pRange = End - Beg + 1;
        return WLC_OBJ_BIT_SELECT;
    }
    while ( Vec_IntEntry(vData, ++i) )
        Prs_SmtReadName( pNtk, Abc_NamStr(p->pStrs, Vec_IntEntry(vData, i)), -1, vFanins );
    if ( Type == WLC_OBJ_ROTATE_R || Type == WLC_OBJ_ROTATE_L )
    {
        int * pArray = Vec_IntArray(vFanins);
        assert( Vec_IntSize(vFanins) == 2 );
        ABC_SWAP( int, pArray[0], pArray[1] );
    }    
    if ( Type >= WLC_OBJ_LOGIC_NOT && Type <= WLC_OBJ_REDUCT_XOR )
        *pRange = 1;
    else if ( Type == WLC_OBJ_BIT_CONCAT )
    {
        int k;
        Vec_IntForEachEntry( vFanins, NameId, k )
            *pRange += Wlc_ObjRange( Wlc_NtkObj(pNtk, NameId) );
    }
    else if ( Type == WLC_OBJ_MUX )
    {
        int * pArray = Vec_IntArray(vFanins);
        assert( Vec_IntSize(vFanins) == 3 );
        ABC_SWAP( int, pArray[1], pArray[2] );
        NameId = Vec_IntEntry(vFanins, 1);
        *pRange = Wlc_ObjRange( Wlc_NtkObj(pNtk, NameId) );
    }
    else // to determine range, look at the first argument
    {
        NameId = Vec_IntEntry(vFanins, 0);
        *pRange = Wlc_ObjRange( Wlc_NtkObj(pNtk, NameId) );
    }
    return Type;
}
Wlc_Ntk_t * Prs_SmtBuild( Prs_Smt_t * p )
{
    Wlc_Ntk_t * pNtk;
    char * pName, * pBits, * pConst;
    Vec_Int_t * vFanins = Vec_IntAlloc( 100 );
    int i, iObj, Type, Entry, NameId, fFound, Range;
    // start network and create primary inputs
    pNtk = Wlc_NtkAlloc( p->pName, Vec_IntCountEntry(&p->vData, 0) + 100 );
    pNtk->pManName = Abc_NamStart( 1000, 24 );
    for ( i = 0; i < Vec_IntSize(&p->vData) - 1; )
    {
        assert( Vec_IntEntry(&p->vData, i) == 0 );
        if ( Vec_IntEntry(&p->vData, ++i) == PRS_SMT_INPUT )
        {
            pName = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            pBits = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            iObj = Wlc_ObjAlloc( pNtk, WLC_OBJ_PI, 0, atoi(pBits)-1, 0 );
            NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pName, &fFound );
            assert( !fFound );
            assert( iObj == NameId );
        }
        while ( Vec_IntEntry(&p->vData, ++i) );
    }
    // create logic nodes
    for ( i = 0; i < Vec_IntSize(&p->vData) - 1; )
    {
        assert( Vec_IntEntry(&p->vData, i) == 0 );
        Entry = Vec_IntEntry(&p->vData, ++i);
        if ( Entry == PRS_SMT_INPUT )
        {}
        else if ( Entry == PRS_SMT_CONST )
        {
            pName  = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            pBits  = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            pConst = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            // create new node
            if ( !Prs_SmtReadConstant( pNtk, pConst, atoi(pBits), vFanins, pName ) )
                return NULL;
        }
        else if ( Entry == PRS_SMT_LET )
        {
            pName = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            Type = Prs_SmtReadNode( p, pNtk, &p->vData, ++i, vFanins, &Range );
            if ( Type == WLC_OBJ_NONE )
                return NULL;
            assert( Range > 0 );
            // create new node
            iObj = Wlc_ObjAlloc( pNtk, Type, 0, Range-1, 0 );
            Wlc_ObjAddFanins( pNtk, Wlc_NtkObj(pNtk, iObj), vFanins );
            // add node's name
            NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pName, &fFound );
            assert( !fFound );
            assert( iObj == NameId );
        }
        else if ( Entry == PRS_SMT_ASSERT )
        {
            Type = WLC_OBJ_BUF;
            Vec_IntClear( vFanins );
            pName = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
            if ( !strcmp(pName, "not") )
            {
                Type = WLC_OBJ_LOGIC_NOT;
                pName = Abc_NamStr( p->pStrs, Vec_IntEntry(&p->vData, ++i) );
                Range = 1;
            }
            // add fanin
            NameId = Abc_NamStrFindOrAdd( pNtk->pManName, pName, &fFound );
            assert( fFound );
            Vec_IntPush( vFanins, NameId );
            // find range
            if ( Type == WLC_OBJ_BUF )
            {
                // find range
                iObj = Vec_IntEntry(vFanins, 0);
                Range = Wlc_ObjRange( Wlc_NtkObj(pNtk, iObj) );
                assert( Range == 1 );
            }
            // create new node
            iObj = Wlc_ObjAlloc( pNtk, Type, 0, Range-1, 0 );
            Wlc_ObjAddFanins( pNtk, Wlc_NtkObj(pNtk, iObj), vFanins );
            Wlc_ObjSetCo( pNtk, Wlc_NtkObj(pNtk, iObj), 0 );
            // add node's name
            NameId = Abc_NamStrFindOrAdd( pNtk->pManName, "miter_output", &fFound );
            assert( !fFound );
            assert( iObj == NameId );
            break;
        }
        else assert( 0 );
        while ( Vec_IntEntry(&p->vData, ++i) );
    }
    Vec_IntFree( vFanins );
    // create nameIDs
    vFanins = Vec_IntStartNatural( Wlc_NtkObjNumMax(pNtk) );
    Vec_IntAppend( &pNtk->vNameIds, vFanins );
    Vec_IntFree( vFanins );
    return pNtk;
}
Wlc_Ntk_t * Wlc_ReadSmt( char * pFileName )
{
    Wlc_Ntk_t * pNtk = NULL;
    Prs_Smt_t * p = Prs_SmtAlloc( pFileName );
    if ( p == NULL )
        return NULL;
    Prs_SmtRemoveComments( p );
    Prs_SmtReadLines( p );
    //Prs_SmtPrintParser( p );
    if ( Prs_SmtErrorPrint(p) )
    {
        pNtk = Prs_SmtBuild( p );
    }
    Prs_SmtFree( p );
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

