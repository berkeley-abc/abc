/**CFile****************************************************************

  FileName    [ioReadPlaMo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedure to read network from file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadPlaMo.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ioAbc.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Mop_Man_t_ Mop_Man_t;
struct Mop_Man_t_
{
    int              nIns;
    int              nOuts;
    int              nWordsIn;
    int              nWordsOut;
    Vec_Wrd_t *      vWordsIn;
    Vec_Wrd_t *      vWordsOut;
    Vec_Int_t *      vCubes; 
};

static inline int    Mop_ManIsSopSymb( char c ) {  return c == '0' || c == '1' || c == '-'; }
static inline int    Mop_ManIsSpace( char c )   {  return c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r'; }

static inline word * Mop_ManCubeIn( Mop_Man_t * p, int i )  { return Vec_WrdEntryP(p->vWordsIn,   p->nWordsIn  * i); }
static inline word * Mop_ManCubeOut( Mop_Man_t * p, int i ) { return Vec_WrdEntryP(p->vWordsOut,  p->nWordsOut * i); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mop_Man_t * Mop_ManAlloc( int nIns, int nOuts, int nCubes )
{
    Mop_Man_t * p   = ABC_CALLOC( Mop_Man_t, 1 );
    p->nIns         = nIns;
    p->nOuts        = nOuts;
    p->nWordsIn     = Abc_Bit6WordNum( 2*nIns );
    p->nWordsOut    = Abc_Bit6WordNum( nOuts );
    p->vWordsIn     = Vec_WrdStart( p->nWordsIn * nCubes );
    p->vWordsOut    = Vec_WrdStart( p->nWordsOut * nCubes );
    p->vCubes       = Vec_IntAlloc( nCubes );
    return p;
}
void Mop_ManStop( Mop_Man_t * p )
{
    Vec_WrdFree( p->vWordsIn );
    Vec_WrdFree( p->vWordsOut );
    Vec_IntFree( p->vCubes );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Reads the file into a character buffer.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Mop_ManLoadFile( char * pFileName )
{
    FILE * pFile;
    int nFileSize, RetValue;
    char * pContents;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        Abc_Print( -1, "Mop_ManLoadFile(): The file is unavailable (absent or open).\n" );
        return NULL;
    }
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile ); 
    if ( nFileSize == 0 )
    {
        Abc_Print( -1, "Mop_ManLoadFile(): The file is empty.\n" );
        return NULL;
    }
    pContents = ABC_ALLOC( char, nFileSize + 10 );
    rewind( pFile );
    RetValue = fread( pContents, nFileSize, 1, pFile );
    fclose( pFile );
    strcpy( pContents + nFileSize, "\n" );
    return pContents;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Mop_ManReadParams( char * pBuffer, int * pnIns, int * pnOuts )
{
    char * pIns  = strstr( pBuffer, ".i " );
    char * pOuts = strstr( pBuffer, ".o " );
    char * pStr  = pBuffer; int nCubes = 0;
    if ( pIns == NULL || pOuts == NULL )
        return -1;
    *pnIns  = atoi( pIns + 2 );
    *pnOuts = atoi( pOuts + 2 );
    while ( *pStr )
        nCubes += (*pStr++ == '\n');
    return nCubes;
}
Mop_Man_t * Mop_ManRead( char * pFileName )
{
    Mop_Man_t * p;
    int nIns, nOuts, nCubes, iCube;
    char * pToken, * pBuffer = Mop_ManLoadFile( pFileName );
    if ( pBuffer == NULL )
        return NULL;
    nCubes = Mop_ManReadParams( pBuffer, &nIns, &nOuts );
    if ( nCubes == -1 )
        return NULL;
    p = Mop_ManAlloc( nIns, nOuts, nCubes );
    // get the first cube
    pToken = strtok( pBuffer, "\n" );
    while ( pToken )
    {
        while ( Mop_ManIsSpace(*pToken) )
            pToken++;
        if ( Mop_ManIsSopSymb(*pToken) )
            break;
        pToken = strtok( NULL, "\n" );
    }
    // read cubes
    for ( iCube = 0; pToken && Mop_ManIsSopSymb(*pToken); iCube++ )
    {
        char * pTokenCopy = pToken;
        int i, o, nVars[2] = {nIns, nOuts};
        word * pCube[2] = { Mop_ManCubeIn(p, iCube), Mop_ManCubeOut(p, iCube) }; 
        for ( o = 0; o < 2; o++ )
        {
            while ( Mop_ManIsSpace(*pToken) )
                pToken++;
            for ( i = 0; i < nVars[o]; i++, pToken++ )
            {
                if ( !Mop_ManIsSopSymb(*pToken) )
                {
                    printf( "Cannot read cube %d (%s).\n", iCube+1, pTokenCopy );
                    ABC_FREE( pBuffer );
                    Mop_ManStop( p );
                    return NULL;
                }
                if ( o == 1 )
                {
                    if ( *pToken == '1' )
                        Abc_TtSetBit( pCube[o], i );
                }
                else if ( *pToken == '0' )
                    Abc_TtSetBit( pCube[o], 2*i );
                else if ( *pToken == '1' )
                    Abc_TtSetBit( pCube[o], 2*i+1 );
            }
        }
        assert( iCube < nCubes );
        Vec_IntPush( p->vCubes, iCube );
        pToken = strtok( NULL, "\n" );
    }
    ABC_FREE( pBuffer );
    return p;
}
void Mop_ManPrint( Mop_Man_t * p )
{
    int i, k, iCube;
    printf( ".%d\n", p->nIns );
    printf( ".%d\n", p->nOuts );
    Vec_IntForEachEntry( p->vCubes, iCube, i )
    {
        char Symb[4] = { '-', '0', '1', '?' };
        word * pCubeIn  = Mop_ManCubeIn( p, iCube );
        word * pCubeOut = Mop_ManCubeOut( p, iCube );
        for ( k = 0; k < p->nIns; k++ )
            printf( "%c", Symb[Abc_TtGetQua(pCubeIn, k)] );
        printf( " " );
        for ( k = 0; k < p->nOuts; k++ )
            printf( "%d", Abc_TtGetBit(pCubeOut, k) );
        printf( "\n" );
    }
    printf( ".e\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Mop_ManCountOnes( word * pCube, int nWords )
{
    int w, Count = 0;
    for ( w = 0; w < nWords; w++ )
        Count += Abc_TtCountOnes( pCube[w] );
    return Count;
}
static inline int Mop_ManCountOutputLits( Mop_Man_t * p )
{
    int i, iCube, nOutLits = 0;
    Vec_IntForEachEntry( p->vCubes, iCube, i )
        nOutLits += Mop_ManCountOnes( Mop_ManCubeOut(p, iCube), p->nWordsOut );
    return nOutLits;
}
static inline Vec_Wec_t * Mop_ManCreateGroups( Mop_Man_t * p )
{
    int i, iCube;
    Vec_Wec_t * vGroups = Vec_WecStart( p->nIns );
    Vec_IntForEachEntry( p->vCubes, iCube, i )
        Vec_WecPush( vGroups, Mop_ManCountOnes(Mop_ManCubeIn(p, iCube), p->nWordsIn), iCube );
    return vGroups;
}
static inline int Mop_ManCheckContain( word * pBig, word * pSmall, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        if ( pSmall[w] != (pSmall[w] & pBig[w]) )
            return 0;
    return 1;
}
void Mop_ManReduce( Mop_Man_t * p )
{
    abctime clk = Abc_Clock();
    Vec_Int_t * vGroup, * vGroup2;
    int w, i, k, c1, c2, iCube1, iCube2;
    int nOutLits, nOutLits2, nEqual = 0, nContain = 0;
    Vec_Wec_t * vGroups = Mop_ManCreateGroups( p );
    nOutLits = Mop_ManCountOutputLits( p );
    // check identical cubes within each group
    Vec_WecForEachLevel( vGroups, vGroup, i )
    {
        Vec_IntForEachEntry( vGroup, iCube1, c1 )
        if ( iCube1 != -1 )
        {
            word * pCube1Out, * pCube1 = Mop_ManCubeIn( p, iCube1 );
            Vec_IntForEachEntryStart( vGroup, iCube2, c2, c1+1 )
            if ( iCube2 != -1 )
            {
                word * pCube2Out, * pCube2 = Mop_ManCubeIn( p, iCube2 );
                if ( memcmp(pCube1, pCube2, sizeof(word)*p->nWordsIn) )
                    continue;
                // merge cubes
                pCube1Out = Mop_ManCubeOut( p, iCube1 );
                pCube2Out = Mop_ManCubeOut( p, iCube2 );
                for ( w = 0; w < p->nWordsOut; w++ )
                    pCube1Out[w] |= pCube2Out[w];
                Vec_IntWriteEntry( vGroup, c2, -1 );
                nEqual++;
            }
        }
    }
    // check contained cubes
    Vec_WecForEachLevel( vGroups, vGroup, i )
    {
        // compare cubes in vGroup with cubes containing more literals
        Vec_WecForEachLevelStart( vGroups, vGroup2, k, i+1 )
        {
            Vec_IntForEachEntry( vGroup, iCube1, c1 )
            if ( iCube1 != -1 )
            {
                word * pCube1Out, * pCube1 = Mop_ManCubeIn( p, iCube1 );
                Vec_IntForEachEntry( vGroup2, iCube2, c2 )
                if ( iCube2 != -1 )
                {
                    word * pCube2Out, * pCube2 = Mop_ManCubeIn( p, iCube2 );
                    if ( !Mop_ManCheckContain(pCube2, pCube1, p->nWordsIn) )
                        continue;
                    pCube1Out = Mop_ManCubeOut( p, iCube1 );
                    pCube2Out = Mop_ManCubeOut( p, iCube2 );
                    for ( w = 0; w < p->nWordsOut; w++ )
                        pCube2Out[w] &= ~pCube1Out[w];
                    for ( w = 0; w < p->nWordsOut; w++ )
                        if ( pCube2Out[w] )
                            break;
                    if ( w < p->nWordsOut ) // has output literals
                        continue;
                    // remove larger cube
                    Vec_IntWriteEntry( vGroup2, c2, -1 );
                    nContain++;
                }
            }
        }
    }
    nOutLits2 = Mop_ManCountOutputLits( p );
    // reload cubes
    Vec_IntClear( p->vCubes );
    Vec_WecForEachLevel( vGroups, vGroup, i )
        Vec_IntForEachEntry( vGroup, iCube1, c1 )
            if ( iCube1 != -1 )
                Vec_IntPush( p->vCubes, iCube1 );
    Vec_WecFree( vGroups );

    printf( "Reduced %d equal and %d contained cubes. Output lits: %d -> %d.   ", nEqual, nContain, nOutLits, nOutLits2 );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wec_t * Mop_ManCubeCount( Mop_Man_t * p )
{
    int i, k, iCube;
    Vec_Wec_t * vOuts = Vec_WecStart( p->nOuts );
    Vec_IntForEachEntry( p->vCubes, iCube, i )
    if ( iCube != -1 )
    {
        word * pCube = Mop_ManCubeOut( p, iCube );
        for ( k = 0; k < p->nOuts; k++ )
            if ( Abc_TtGetBit( pCube, k ) )
                Vec_WecPush( vOuts, k, iCube );
    }
    return vOuts;
}
Abc_Ntk_t * Mop_ManDerive( Mop_Man_t * p, char * pFileName )
{
    int i, k, c, iCube; 
    char Symb[4] = { '-', '0', '1', '?' };     // cube symbols
    Vec_Str_t * vSop  = Vec_StrAlloc( 1000 );  // storage for one SOP
    Vec_Wec_t * vOuts = Mop_ManCubeCount( p ); // cube count for each output
    Abc_Ntk_t * pNtk  = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    pNtk->pName = Extra_UtilStrsav( pFileName );
    pNtk->pSpec = Extra_UtilStrsav( pFileName );
    for ( i = 0; i < p->nIns; i++ )
        Abc_NtkCreatePi(pNtk);
    for ( i = 0; i < p->nOuts; i++ )
    {
        Vec_Int_t * vThis = Vec_WecEntry( vOuts, i );
        Abc_Obj_t * pPo   = Abc_NtkCreatePo(pNtk);
        Abc_Obj_t * pNode = Abc_NtkCreateNode(pNtk);
        Abc_ObjAddFanin( pPo, pNode );
        if ( Vec_IntSize(vThis) == 0 )
        {
            pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtk->pManFunc, " 0\n" );
            continue;
        }
        for ( k = 0; k < p->nIns; k++ )
            Abc_ObjAddFanin( pNode, Abc_NtkPi(pNtk, k) );
        Vec_StrClear( vSop );
        Vec_IntForEachEntry( vThis, iCube, c )
        {
            word * pCube = Mop_ManCubeIn( p, iCube );
            for ( k = 0; k < p->nIns; k++ )
                Vec_StrPush( vSop, Symb[Abc_TtGetQua(pCube, k)] );
            Vec_StrAppend( vSop, " 1\n" );
        }
        Vec_StrPush( vSop, '\0' );
        pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtk->pManFunc, Vec_StrArray(vSop) );
    }
    Vec_StrFree( vSop );
    Vec_WecFree( vOuts );
    Abc_NtkAddDummyPiNames( pNtk );
    Abc_NtkAddDummyPoNames( pNtk );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Mop_ManTest( char * pFileName, int fVerbose )
{
    Abc_Ntk_t * pNtk = NULL;
    Mop_Man_t * p = Mop_ManRead( pFileName );
    if ( p == NULL )
        return NULL;
    //Mop_ManPrint( p );
    Mop_ManReduce( p );
    //Mop_ManPrint( p );
    pNtk = Mop_ManDerive( p, pFileName );
    Mop_ManStop( p );
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_IMPL_END

