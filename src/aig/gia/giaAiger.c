/**CFile****************************************************************

  FileName    [giaAiger.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Procedures to read/write binary AIGER format developed by
  Armin Biere, Johannes Kepler University (http://fmv.jku.at/)]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAiger.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Extracts one unsigned AIG edge from the input buffer.]

  Description [This procedure is a slightly modified version of Armin Biere's
  procedure "unsigned decode (FILE * file)". ]
  
  SideEffects [Updates the current reading position.]

  SeeAlso     []

***********************************************************************/
unsigned Gia_ReadAigerDecode( unsigned char ** ppPos )
{
    unsigned x = 0, i = 0;
    unsigned char ch;
    while ((ch = *(*ppPos)++) & 0x80)
        x |= (ch & 0x7f) << (7 * i++);
    return x | (ch << (7 * i));
}

/**Function*************************************************************

  Synopsis    [Decodes the encoded array of literals.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_WriteDecodeLiterals( unsigned char ** ppPos, int nEntries )
{
    Vec_Int_t * vLits;
    int Lit, LitPrev, Diff, i;
    vLits = Vec_IntAlloc( nEntries );
    LitPrev = Gia_ReadAigerDecode( ppPos );
    Vec_IntPush( vLits, LitPrev );
    for ( i = 1; i < nEntries; i++ )
    {
//        Diff = Lit - LitPrev;
//        Diff = (Lit < LitPrev)? -Diff : Diff;
//        Diff = ((2 * Diff) << 1) | (int)(Lit < LitPrev);
        Diff = Gia_ReadAigerDecode( ppPos );
        Diff = (Diff & 1)? -(Diff >> 1) : Diff >> 1;
        Lit  = Diff + LitPrev;
        Vec_IntPush( vLits, Lit );
        LitPrev = Lit;
    }
    return vLits;
}


/**Function*************************************************************

  Synopsis    [Returns the file size.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_FixFileName( char * pFileName )
{
    char * pName;
    for ( pName = pFileName; *pName; pName++ )
        if ( *pName == '>' )
            *pName = '\\';
}

/**Function*************************************************************

  Synopsis    [Returns the file size.]

  Description [The file should be closed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_FileSize( char * pFileName )
{
    FILE * pFile;
    int nFileSize;
    pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Gia_FileSize(): The file is unavailable (absent or open).\n" );
        return 0;
    }
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile ); 
    fclose( pFile );
    return nFileSize;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Gia_FileNameGeneric( char * FileName )
{
    char * pDot, * pRes;
    pRes = Gia_UtilStrsav( FileName );
    if ( (pDot = strrchr( pRes, '.' )) )
        *pDot = 0;
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Read integer from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ReadInt( unsigned char * pPos )
{
    int i, Value = 0;
    for ( i = 0; i < 4; i++ )
        Value = (Value << 8) | *pPos++;
    return Value;
}

/**Function*************************************************************

  Synopsis    [Reads decoded value.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Gia_ReadDiffValue( unsigned char ** ppPos, int iPrev )
{
    int Item = Gia_ReadAigerDecode( ppPos );
    if ( Item & 1 )
        return iPrev + (Item >> 1);
    return iPrev - (Item >> 1);
}

/**Function*************************************************************

  Synopsis    [Read equivalence classes from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Rpr_t * Gia_ReadEquivClasses( unsigned char ** ppPos, int nSize )
{
    Gia_Rpr_t * pReprs;
    unsigned char * pStop;
    int i, Item, fProved, iRepr, iNode;
    pStop = *ppPos;
    pStop += Gia_ReadInt( *ppPos ); *ppPos += 4;
    pReprs = ABC_CALLOC( Gia_Rpr_t, nSize );
    for ( i = 0; i < nSize; i++ )
        pReprs[i].iRepr = GIA_VOID;
    iRepr = iNode = 0;
    while ( *ppPos < pStop )
    {
        Item = Gia_ReadAigerDecode( ppPos );
        if ( Item & 1 )
        {
            iRepr += (Item >> 1);
            iNode = iRepr;
//printf( "\nRepr = %d ", iRepr );
            continue;
        }
        Item >>= 1;
        fProved = (Item & 1);
        Item >>= 1;
        iNode += Item;
        pReprs[iNode].fProved = fProved;
        pReprs[iNode].iRepr = iRepr;
        assert( iRepr < iNode );
//printf( "Node = %d ", iNode );
    }
    return pReprs;
}

/**Function*************************************************************

  Synopsis    [Read flop classes from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ReadFlopClasses( unsigned char ** ppPos, Vec_Int_t * vClasses, int nSize )
{
    int nAlloc = Gia_ReadInt( *ppPos ); *ppPos += 4;
    assert( nAlloc/4 == nSize );
    assert( Vec_IntSize(vClasses) == nSize );
    memcpy( Vec_IntArray(vClasses), *ppPos, 4*nSize );
    *ppPos += 4 * nSize;
}

/**Function*************************************************************

  Synopsis    [Read equivalence classes from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ReadMapping( unsigned char ** ppPos, int nSize )
{
    int * pMapping;
    unsigned char * pStop;
    int k, j, nFanins, nAlloc, iNode = 0, iOffset = nSize;
    pStop = *ppPos;
    pStop += Gia_ReadInt( *ppPos ); *ppPos += 4;
    nAlloc = nSize + pStop - *ppPos;
    pMapping = ABC_CALLOC( int, nAlloc );
    while ( *ppPos < pStop )
    {
        k = iOffset;
        pMapping[k++] = nFanins = Gia_ReadAigerDecode( ppPos );
        for ( j = 0; j <= nFanins; j++ )
            pMapping[k++] = iNode = Gia_ReadDiffValue( ppPos, iNode );
        pMapping[iNode] = iOffset;
        iOffset = k;
    }
    assert( iOffset <= nAlloc );
    return pMapping;
}

/**Function*************************************************************

  Synopsis    [Read switching from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned char * Gia_ReadSwitching( unsigned char ** ppPos, int nSize )
{
    unsigned char * pSwitching;
    int nAlloc = Gia_ReadInt( *ppPos ); *ppPos += 4;
    assert( nAlloc == nSize );
    pSwitching = ABC_ALLOC( unsigned char, nSize );
    memcpy( pSwitching, *ppPos, nSize );
    *ppPos += nSize;
    return pSwitching;
}

/**Function*************************************************************

  Synopsis    [Read placement from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Plc_t * Gia_ReadPlacement( unsigned char ** ppPos, int nSize )
{
    Gia_Plc_t * pPlacement;
    int nAlloc = Gia_ReadInt( *ppPos ); *ppPos += 4;
    assert( nAlloc/4 == nSize );
    pPlacement = ABC_ALLOC( Gia_Plc_t, nSize );
    memcpy( pPlacement, *ppPos, 4*nSize );
    *ppPos += 4 * nSize;
    return pPlacement;
}

/**Function*************************************************************

  Synopsis    [Reads the AIG in the binary AIGER format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ReadAiger( char * pFileName, int fCheck )
{
    FILE * pFile;
    Gia_Man_t * pNew;
    Vec_Int_t * vLits = NULL;
    Vec_Int_t * vNodes, * vDrivers;//, * vTerms;
    int iObj, iNode0, iNode1;
    int nTotal, nInputs, nOutputs, nLatches, nAnds, nFileSize, i;//, iTerm, nDigits;
    unsigned char * pDrivers, * pSymbols, * pCur;//, * pType;
    char * pContents, * pName;
    unsigned uLit0, uLit1, uLit;

    // read the file into the buffer
    Gia_FixFileName( pFileName );
    nFileSize = Gia_FileSize( pFileName );
    pFile = fopen( pFileName, "rb" );
    pContents = ABC_ALLOC( char, nFileSize );
    fread( pContents, nFileSize, 1, pFile );
    fclose( pFile );

    // check if the input file format is correct
    if ( strncmp(pContents, "aig", 3) != 0 || (pContents[3] != ' ' && pContents[3] != '2') )
    {
        fprintf( stdout, "Wrong input file format.\n" );
        free( pContents );
        return NULL;
    }

    // read the file type
    pCur = (unsigned char *)pContents;  while ( *pCur++ != ' ' );
    // read the number of objects
    nTotal = atoi( (char *)pCur );    while ( *pCur++ != ' ' );
    // read the number of inputs
    nInputs = atoi( (char *)pCur );   while ( *pCur++ != ' ' );
    // read the number of latches
    nLatches = atoi( (char *)pCur );  while ( *pCur++ != ' ' );
    // read the number of outputs
    nOutputs = atoi( (char *)pCur );  while ( *pCur++ != ' ' );
    // read the number of nodes
    nAnds = atoi( (char *)pCur );     while ( *pCur++ != '\n' );  
    // check the parameters
    if ( nTotal != nInputs + nLatches + nAnds )
    {
        fprintf( stdout, "The paramters are wrong.\n" );
        return NULL;
    }

    // allocate the empty AIG
    pNew = Gia_ManStart( nTotal + nLatches + nOutputs + 1 );
    pName = Gia_FileNameGeneric( pFileName );
    pNew->pName = Gia_UtilStrsav( pName );
//    pNew->pSpec = Gia_UtilStrsav( pFileName );
    ABC_FREE( pName );

    // prepare the array of nodes
    vNodes = Vec_IntAlloc( 1 + nTotal );
    Vec_IntPush( vNodes, 0 );

    // create the PIs
    for ( i = 0; i < nInputs + nLatches; i++ )
    {
        iObj = Gia_ManAppendCi(pNew);    
        Vec_IntPush( vNodes, iObj );
    }

    // remember the beginning of latch/PO literals
    pDrivers = pCur;
    if ( pContents[3] == ' ' ) // standard AIGER
    {
        // scroll to the beginning of the binary data
        for ( i = 0; i < nLatches + nOutputs; )
            if ( *pCur++ == '\n' )
                i++;
    }
    else // modified AIGER
    {
        vLits = Gia_WriteDecodeLiterals( &pCur, nLatches + nOutputs );
    }

    // create the AND gates
    for ( i = 0; i < nAnds; i++ )
    {
        uLit = ((i + 1 + nInputs + nLatches) << 1);
        uLit1 = uLit  - Gia_ReadAigerDecode( &pCur );
        uLit0 = uLit1 - Gia_ReadAigerDecode( &pCur );
//        assert( uLit1 > uLit0 );
        iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), uLit0 & 1 );
        iNode1 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit1 >> 1), uLit1 & 1 );
        assert( Vec_IntSize(vNodes) == i + 1 + nInputs + nLatches );
//        Vec_IntPush( vNodes, Gia_And(pNew, iNode0, iNode1) );
        Vec_IntPush( vNodes, Gia_ManAppendAnd(pNew, iNode0, iNode1) );
    }

    // remember the place where symbols begin
    pSymbols = pCur;

    // read the latch driver literals
    vDrivers = Vec_IntAlloc( nLatches + nOutputs );
    if ( pContents[3] == ' ' ) // standard AIGER
    {
        pCur = pDrivers;
        for ( i = 0; i < nLatches; i++ )
        {
            uLit0 = atoi( (char *)pCur );  while ( *pCur++ != '\n' );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }
        // read the PO driver literals
        for ( i = 0; i < nOutputs; i++ )
        {
            uLit0 = atoi( (char *)pCur );  while ( *pCur++ != '\n' );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }

    }
    else
    {
        // read the latch driver literals
        for ( i = 0; i < nLatches; i++ )
        {
            uLit0 = Vec_IntEntry( vLits, i );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }
        // read the PO driver literals
        for ( i = 0; i < nOutputs; i++ )
        {
            uLit0 = Vec_IntEntry( vLits, i+nLatches );
            iNode0 = Gia_LitNotCond( Vec_IntEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );
            Vec_IntPush( vDrivers, iNode0 );
        }
        Vec_IntFree( vLits );
    }

    // create the POs
    for ( i = 0; i < nOutputs; i++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vDrivers, nLatches + i) );
    for ( i = 0; i < nLatches; i++ )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vDrivers, i) );
    Vec_IntFree( vDrivers );

    // create the latches
    Gia_ManSetRegNum( pNew, nLatches );

    // check if there are other types of information to read
    pCur = pSymbols;
    if ( (char *)pCur + 1 < pContents + nFileSize && *pCur == 'c' )
    {
        pCur++;
        if ( *pCur == 'e' )
        {
            pCur++;
            // read equivalence classes
            pNew->pReprs = Gia_ReadEquivClasses( &pCur, Gia_ManObjNum(pNew) );
            pNew->pNexts = Gia_ManDeriveNexts( pNew );
        }
        if ( *pCur == 'f' )
        {
            pCur++;
            // read flop classes
            pNew->vFlopClasses = Vec_IntStart( Gia_ManRegNum(pNew) );
            Gia_ReadFlopClasses( &pCur, pNew->vFlopClasses, Gia_ManRegNum(pNew) );
        }
        if ( *pCur == 'm' )
        {
            pCur++;
            // read mapping
            pNew->pMapping = Gia_ReadMapping( &pCur, Gia_ManObjNum(pNew) );
        }
        if ( *pCur == 'p' )
        {
            pCur++;
            // read placement
            pNew->pPlacement = Gia_ReadPlacement( &pCur, Gia_ManObjNum(pNew) );
        }
        if ( *pCur == 's' )
        { 
            pCur++;
            // read switching activity
            pNew->pSwitching = Gia_ReadSwitching( &pCur, Gia_ManObjNum(pNew) );
        }
        if ( *pCur == 'c' )
        {
            pCur++;
            // read number of constraints
            pNew->nConstrs = Gia_ReadInt( pCur ); pCur += 4;
        }
        if ( *pCur == 'n' )
        {
            pCur++;
            // read model name
            ABC_FREE( pNew->pName );
            pNew->pName = Gia_UtilStrsav( (char *)pCur );
        }
    }

    // skipping the comments
    ABC_FREE( pContents );
    Vec_IntFree( vNodes );
/*
    // check the result
    if ( fCheck && !Gia_ManCheck( pNew ) )
    {
        printf( "Gia_ReadAiger: The network check has failed.\n" );
        Gia_ManStop( pNew );
        return NULL;
    }
*/
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Adds one unsigned AIG edge to the output buffer.]

  Description [This procedure is a slightly modified version of Armin Biere's
  procedure "void encode (FILE * file, unsigned x)" ]
  
  SideEffects [Returns the current writing position.]

  SeeAlso     []

***********************************************************************/
int Gia_WriteAigerEncode( unsigned char * pBuffer, int Pos, unsigned x )
{
    unsigned char ch;
    while (x & ~0x7f)
    {
        ch = (x & 0x7f) | 0x80;
        pBuffer[Pos++] = ch;
        x >>= 7;
    }
    ch = x;
    pBuffer[Pos++] = ch;
    return Pos;
}

/**Function*************************************************************

  Synopsis    [Create the array of literals to be written.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_WriteAigerLiterals( Gia_Man_t * p )
{
    Vec_Int_t * vLits;
    Gia_Obj_t * pObj;
    int i;
    vLits = Vec_IntAlloc( Gia_ManPoNum(p) );
    Gia_ManForEachRi( p, pObj, i )
        Vec_IntPush( vLits, Gia_ObjFaninLit0p(p, pObj) );
    Gia_ManForEachPo( p, pObj, i )
        Vec_IntPush( vLits, Gia_ObjFaninLit0p(p, pObj) );
    return vLits;
}

/**Function*************************************************************

  Synopsis    [Creates the binary encoded array of literals.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Gia_WriteEncodeLiterals( Vec_Int_t * vLits )
{
    Vec_Str_t * vBinary;
    int Pos = 0, Lit, LitPrev, Diff, i;
    vBinary = Vec_StrAlloc( 2 * Vec_IntSize(vLits) );
    LitPrev = Vec_IntEntry( vLits, 0 );
    Pos = Gia_WriteAigerEncode( (unsigned char *)Vec_StrArray(vBinary), Pos, LitPrev ); 
    Vec_IntForEachEntryStart( vLits, Lit, i, 1 )
    {
        Diff = Lit - LitPrev;
        Diff = (Lit < LitPrev)? -Diff : Diff;
        Diff = (Diff << 1) | (int)(Lit < LitPrev);
        Pos = Gia_WriteAigerEncode( (unsigned char *)Vec_StrArray(vBinary), Pos, Diff );
        LitPrev = Lit;
        if ( Pos + 10 > vBinary->nCap )
            Vec_StrGrow( vBinary, vBinary->nCap+1 );
    }
    vBinary->nSize = Pos;
/*
    // verify
    {
        extern Vec_Int_t * Gia_WriteDecodeLiterals( char ** ppPos, int nEntries );
        char * pPos = Vec_StrArray( vBinary );
        Vec_Int_t * vTemp = Gia_WriteDecodeLiterals( &pPos, Vec_IntSize(vLits) );
        for ( i = 0; i < Vec_IntSize(vLits); i++ )
        {
            int Entry1 = Vec_IntEntry(vLits,i);
            int Entry2 = Vec_IntEntry(vTemp,i);
            assert( Entry1 == Entry2 );
        }
        Vec_IntFree( vTemp );
    }
*/
    return vBinary;
}

/**Function*************************************************************

  Synopsis    [Write integer into the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_WriteInt( unsigned char * pPos, int Value )
{
    int i;
    for ( i = 3; i >= 0; i-- )
        *pPos++ = (Value >> (8*i)) & 255;
}

/**Function*************************************************************

  Synopsis    [Read equivalence classes from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned char * Gia_WriteEquivClasses( Gia_Man_t * p, int * pEquivSize )
{
    unsigned char * pBuffer;
    int iRepr, iNode, iPrevRepr, iPrevNode, iLit, nItems, iPos;
    assert( p->pReprs && p->pNexts );
    // count the number of entries to be written
    nItems = 0;
    for ( iRepr = 1; iRepr < Gia_ManObjNum(p); iRepr++ )
    {
        nItems += Gia_ObjIsConst( p, iRepr );
        if ( !Gia_ObjIsHead(p, iRepr) )
            continue;
        Gia_ClassForEachObj( p, iRepr, iNode )
            nItems++;
    }
    pBuffer = ABC_ALLOC( unsigned char, sizeof(int) * (nItems + 1) );
    // write constant class
    iPos = Gia_WriteAigerEncode( pBuffer, 4, Gia_Var2Lit(0, 1) );
//printf( "\nRepr = %d ", 0 );
    iPrevNode = 0;
    for ( iNode = 1; iNode < Gia_ManObjNum(p); iNode++ )
        if ( Gia_ObjIsConst(p, iNode) )
        {
//printf( "Node = %d ", iNode );
            iLit = Gia_Var2Lit( iNode - iPrevNode, Gia_ObjProved(p, iNode) );
            iPrevNode = iNode;
            iPos = Gia_WriteAigerEncode( pBuffer, iPos, Gia_Var2Lit(iLit, 0) );
        }
    // write non-constant classes
    iPrevRepr = 0;
    Gia_ManForEachClass( p, iRepr )
    {
//printf( "\nRepr = %d ", iRepr );
        iPos = Gia_WriteAigerEncode( pBuffer, iPos, Gia_Var2Lit(iRepr - iPrevRepr, 1) );
        iPrevRepr = iPrevNode = iRepr;
        Gia_ClassForEachObj1( p, iRepr, iNode )
        {
//printf( "Node = %d ", iNode );
            iLit = Gia_Var2Lit( iNode - iPrevNode, Gia_ObjProved(p, iNode) );
            iPrevNode = iNode;
            iPos = Gia_WriteAigerEncode( pBuffer, iPos, Gia_Var2Lit(iLit, 0) );
        }
    }
    Gia_WriteInt( pBuffer, iPos );
    *pEquivSize = iPos;
    return pBuffer;
}

/**Function*************************************************************

  Synopsis    [Reads decoded value.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_WriteDiffValue( unsigned char * pPos, int iPos, int iPrev, int iThis )
{
    if ( iPrev < iThis )
        return Gia_WriteAigerEncode( pPos, iPos, Gia_Var2Lit(iThis - iPrev, 1) );
    return Gia_WriteAigerEncode( pPos, iPos, Gia_Var2Lit(iPrev - iThis, 0) );
}

/**Function*************************************************************

  Synopsis    [Read equivalence classes from the string.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned char * Gia_WriteMapping( Gia_Man_t * p, int * pMapSize )
{
    unsigned char * pBuffer;
    int i, k, iPrev, iFan, nItems, iPos = 4;
    assert( p->pMapping );
    // count the number of entries to be written
    nItems = 0;
    Gia_ManForEachLut( p, i )
        nItems += 2 + Gia_ObjLutSize( p, i );
    pBuffer = ABC_ALLOC( unsigned char, sizeof(int) * (nItems + 1) );
    // write non-constant classes
    iPrev = 0;
    Gia_ManForEachLut( p, i )
    {
//printf( "\nSize = %d ", Gia_ObjLutSize(p, i) );
        iPos = Gia_WriteAigerEncode( pBuffer, iPos, Gia_ObjLutSize(p, i) );
        Gia_LutForEachFanin( p, i, iFan, k )
        {
//printf( "Fan = %d ", iFan );
            iPos = Gia_WriteDiffValue( pBuffer, iPos, iPrev, iFan );
            iPrev = iFan;
        }
        iPos = Gia_WriteDiffValue( pBuffer, iPos, iPrev, i );
        iPrev = i;
//printf( "Node = %d ", i );
    }
//printf( "\n" );
    Gia_WriteInt( pBuffer, iPos );
    *pMapSize = iPos;
    return pBuffer;
}

/**Function*************************************************************

  Synopsis    [Writes the AIG in the binary AIGER format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_WriteAiger( Gia_Man_t * pInit, char * pFileName, int fWriteSymbols, int fCompact )
{
    FILE * pFile;
    Gia_Man_t * p;
    Gia_Obj_t * pObj;
    int i, nBufferSize, Pos;
    unsigned char * pBuffer;
    unsigned uLit0, uLit1, uLit;

    if ( Gia_ManCoNum(pInit) == 0 )
    {
        printf( "AIG cannot be written because it has no POs.\n" );
        return;
    }

    // start the output stream
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Gia_WriteAiger(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    // create normalized AIG
    if ( !Gia_ManIsNormalized(pInit) )
    {
//        printf( "Gia_WriteAiger(): Normalizing AIG for writing.\n" );
        p = Gia_ManDupNormalized( pInit );
    }
    else
        p = pInit;

    // write the header "M I L O A" where M = I + L + A
    fprintf( pFile, "aig%s %u %u %u %u %u\n", 
        fCompact? "2" : "",
        Gia_ManCiNum(p) + Gia_ManAndNum(p), 
        Gia_ManPiNum(p),
        Gia_ManRegNum(p),
        Gia_ManPoNum(p),
        Gia_ManAndNum(p) );

    if ( !fCompact ) 
    {
        // write latch drivers
        Gia_ManForEachRi( p, pObj, i )
            fprintf( pFile, "%u\n", Gia_ObjFaninLit0p(p, pObj) );
        // write PO drivers
        Gia_ManForEachPo( p, pObj, i )
            fprintf( pFile, "%u\n", Gia_ObjFaninLit0p(p, pObj) );
    }
    else
    {
        Vec_Int_t * vLits = Gia_WriteAigerLiterals( p );
        Vec_Str_t * vBinary = Gia_WriteEncodeLiterals( vLits );
        fwrite( Vec_StrArray(vBinary), 1, Vec_StrSize(vBinary), pFile );
        Vec_StrFree( vBinary );
        Vec_IntFree( vLits );
    }

    // write the nodes into the buffer
    Pos = 0;
    nBufferSize = 6 * Gia_ManAndNum(p) + 100; // skeptically assuming 3 chars per one AIG edge
    pBuffer = ABC_ALLOC( unsigned char, nBufferSize );
    Gia_ManForEachAnd( p, pObj, i )
    {
        uLit  = Gia_Var2Lit( i, 0 );
        uLit0 = Gia_ObjFaninLit0( pObj, i );
        uLit1 = Gia_ObjFaninLit1( pObj, i );
        assert( uLit0 < uLit1 );
        Pos = Gia_WriteAigerEncode( pBuffer, Pos, uLit  - uLit1 );
        Pos = Gia_WriteAigerEncode( pBuffer, Pos, uLit1 - uLit0 );
        if ( Pos > nBufferSize - 10 )
        {
            printf( "Gia_WriteAiger(): AIGER generation has failed because the allocated buffer is too small.\n" );
            fclose( pFile );
            if ( p != pInit )
                Gia_ManStop( p );
            return;
        }
    }
    assert( Pos < nBufferSize );

    // write the buffer
    fwrite( pBuffer, 1, Pos, pFile );
    ABC_FREE( pBuffer );

    // write the comment
    fprintf( pFile, "c" );
    // write equivalences
    if ( p->pReprs && p->pNexts )
    {
        int nEquivSize;
        unsigned char * pEquivs = Gia_WriteEquivClasses( p, &nEquivSize );
        fprintf( pFile, "e" );
        fwrite( pEquivs, 1, nEquivSize, pFile );
        ABC_FREE( pEquivs );
    }
    // write flop classes
    if ( p->vFlopClasses )
    {
        unsigned char Buffer[10];
        int nSize = 4*Gia_ManRegNum(p);
        Gia_WriteInt( Buffer, nSize );
        fprintf( pFile, "f" );
        fwrite( Buffer, 1, 4, pFile );
        fwrite( Vec_IntArray(p->vFlopClasses), 1, nSize, pFile );
    }
    // write mapping
    if ( p->pMapping )
    {
        int nMapSize;
        unsigned char * pMaps = Gia_WriteMapping( p, &nMapSize );
        fprintf( pFile, "m" );
        fwrite( pMaps, 1, nMapSize, pFile );
        ABC_FREE( pMaps );
    }
    // write placement
    if ( p->pPlacement )
    {
        unsigned char Buffer[10];
        int nSize = 4*Gia_ManObjNum(p);
        Gia_WriteInt( Buffer, nSize );
        fprintf( pFile, "p" );
        fwrite( Buffer, 1, 4, pFile );
        fwrite( p->pPlacement, 1, nSize, pFile );
    }
    // write flop classes
    if ( p->pSwitching )
    {
        unsigned char Buffer[10];
        int nSize = Gia_ManObjNum(p);
        Gia_WriteInt( Buffer, nSize );
        fprintf( pFile, "s" );
        fwrite( Buffer, 1, 4, pFile );
        fwrite( p->pSwitching, 1, nSize, pFile );
    }
    // write constraints
    if ( p->nConstrs )
    {
        unsigned char Buffer[10];
        Gia_WriteInt( Buffer, p->nConstrs );
        fprintf( pFile, "c" );
        fwrite( Buffer, 1, 4, pFile );
    }
    // write name
    if ( p->pName )
        fprintf( pFile, "n%s%c", p->pName, '\0' );
    fprintf( pFile, "\nThis file was produced by the GIA package in ABC on %s\n", Gia_TimeStamp() );
    fprintf( pFile, "For information about AIGER format, refer to %s\n", "http://fmv.jku.at/aiger" );
    fclose( pFile );
    if ( p != pInit )
        Gia_ManStop( p );
}

/**Function*************************************************************

  Synopsis    [Writes the AIG in the binary AIGER format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_DumpAiger( Gia_Man_t * p, char * pFilePrefix, int iFileNum, int nFileNumDigits )
{
    char Buffer[100];
    sprintf( Buffer, "%s%0*d.aig", pFilePrefix, nFileNumDigits, iFileNum );
    Gia_WriteAiger( p, Buffer, 0, 0 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

