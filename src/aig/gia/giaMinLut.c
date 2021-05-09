/**CFile****************************************************************

  FileName    [giaMinLut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Collapsing AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaMinLut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "giaAig.h"
#include "base/main/mainInt.h"
#include "opt/sfm/sfm.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#include "bdd/dsd/dsd.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Vec_WrdReadText( char * pFileName, Vec_Wrd_t ** pvSimI, Vec_Wrd_t ** pvSimO, int nIns, int nOuts )
{
    int i, nSize, iLine, nLines, nWords;
    char pLine[1000];
    Vec_Wrd_t * vSimI, * vSimO;
    FILE * pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return;
    }
    fseek( pFile, 0, SEEK_END );  
    nSize = ftell( pFile );  
    if ( nSize % (nIns + nOuts + 1) > 0 )
    {
        printf( "Cannot read file with simulation data that is not aligned at 8 bytes (remainder = %d).\n", nSize % (nIns + nOuts + 1) );
        fclose( pFile );
        return;
    }
    rewind( pFile );
    nLines = nSize / (nIns + nOuts + 1);
    nWords = (nLines + 63)/64;
    vSimI  = Vec_WrdStart( nIns *nWords );
    vSimO  = Vec_WrdStart( nOuts*nWords );
    for ( iLine = 0; fgets( pLine, 1000, pFile ); iLine++ )
    {
        for ( i = 0; i < nIns; i++ )
            if ( pLine[i] == '1' )
                Abc_TtXorBit( Vec_WrdArray(vSimI) + i*nWords, iLine );
            else assert( pLine[i] == '0' );
        for ( i = 0; i < nOuts; i++ )
            if ( pLine[nIns+i] == '1' )
                Abc_TtXorBit( Vec_WrdArray(vSimO) + i*nWords, iLine );
            else assert( pLine[nIns+i] == '0' );
    }
    fclose( pFile );
    *pvSimI = vSimI;
    *pvSimO = vSimO;
    printf( "Read %d words of simulation data for %d inputs and %d outputs.\n", nWords, nIns, nOuts );
}
void Gia_ManSimInfoTransform( int fSmall )
{
    int nIns  = fSmall ? 32 : 64;
    int nOuts = fSmall ? 10 : 35;
    char * pFileName = fSmall ? "io_s.txt" : "io_l.txt";
    Vec_Wrd_t * vSimI, * vSimO;
    Vec_WrdReadText( pFileName, &vSimI, &vSimO, nIns, nOuts );
    Vec_WrdDumpBin( Extra_FileNameGenericAppend(pFileName, ".simi"), vSimI, 1 );
    Vec_WrdDumpBin( Extra_FileNameGenericAppend(pFileName, ".simo"), vSimO, 1 );
    Vec_WrdFree( vSimI );
    Vec_WrdFree( vSimO );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManSimInfoTry( Gia_Man_t * p, Vec_Wrd_t * vSimI, Vec_Wrd_t * vSimO )
{
    extern Vec_Wrd_t * Gia_ManSimulateWordsOut( Gia_Man_t * p, Vec_Wrd_t * vSimsIn );
    Vec_Wrd_t * vSimsOut = Gia_ManSimulateWordsOut( p, vSimI );
    word * pSim0 = Vec_WrdArray(p->vSims);
    int i, Count, nWords = Vec_WrdSize(vSimO) / Gia_ManCoNum(p);
    Gia_Obj_t * pObj; 
    assert( Vec_WrdSize(vSimI) / Gia_ManCiNum(p) == nWords );
    assert( Vec_WrdSize(vSimI) % Gia_ManCiNum(p) == 0 );
    assert( Vec_WrdSize(vSimO) % Gia_ManCoNum(p) == 0 );
    Abc_TtClear( pSim0, nWords );
    Gia_ManForEachCo( p, pObj, i )
    {
        word * pSimImpl = Vec_WrdEntryP( vSimsOut, i * nWords );
        word * pSimGold = Vec_WrdEntryP( vSimO,    i * nWords );
        Abc_TtOrXor( pSim0, pSimImpl, pSimGold, nWords );
    }
    Count = Abc_TtCountOnesVec( pSim0, nWords );
    printf( "Number of failed patterns is %d (out of %d). The first one is %d\n", 
        Count, 64*nWords, Abc_TtFindFirstBit2(pSim0, nWords) );
    Vec_WrdFreeP( &p->vSims );
    Vec_WrdFreeP( &vSimsOut );
    p->nSimWords = -1;
    return Count;
}
void Gia_ManSimInfoTryTest( Gia_Man_t * p, int fSmall )
{
    abctime clk = Abc_Clock();
    int nIns  = fSmall ? 32 : 64;
    int nOuts = fSmall ? 10 : 35;
    char * pFileNameI = fSmall ? "s.simi" : "l.simi";
    char * pFileNameO = fSmall ? "s.simo" : "l.simo";
    Vec_Wrd_t * vSimI = Vec_WrdReadBin( pFileNameI, 1 );
    Vec_Wrd_t * vSimO = Vec_WrdReadBin( pFileNameO, 1 );
    Gia_ManSimInfoTry( p, vSimI, vSimO );
    Vec_WrdFree( vSimI );
    Vec_WrdFree( vSimO );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSimInfoPassTest( Gia_Man_t * p, int fSmall )
{
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManDoMuxMapping( Gia_Man_t * p )
{
    extern Gia_Man_t * Gia_ManPerformMfs( Gia_Man_t * p, Sfm_Par_t * pPars );
    Gia_Man_t * pTemp, * pNew = Gia_ManDup( p );
    Jf_Par_t Pars, * pPars = &Pars; int c, nIters = 2;
    Sfm_Par_t Pars2, * pPars2 = &Pars2;
    Lf_ManSetDefaultPars( pPars );
    Sfm_ParSetDefault( pPars2 );
    pPars2->nTfoLevMax  =    5;
    pPars2->nDepthMax   =  100;
    pPars2->nWinSizeMax = 2000;
    for ( c = 0; c < nIters; c++ )
    {
        pNew = Lf_ManPerformMapping( pTemp = pNew, pPars );
        Gia_ManStop( pTemp );
        pNew = Gia_ManPerformMfs( pTemp = pNew, pPars2 );
        Gia_ManStop( pTemp );
        if ( c == nIters-1 )
            break;
        pNew = (Gia_Man_t *)Dsm_ManDeriveGia( pTemp = pNew, 0 );
        Gia_ManStop( pTemp );
    }
    return pNew;
}
Gia_Man_t * Gia_ManDoMuxTransform( Gia_Man_t * p, int fReorder )
{
    extern Gia_Man_t * Abc_NtkStrashToGia( Abc_Ntk_t * pNtk );
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    extern int Abc_NtkBddToMuxesPerformGlo( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew, int Limit, int fReorder );
    Gia_Man_t * pRes = NULL;
    Aig_Man_t * pMan = Gia_ManToAig( p, 0 );
    Abc_Ntk_t * pNtk = Abc_NtkFromAigPhase( pMan );
    Abc_Ntk_t * pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    pNtk->pName = Extra_UtilStrsav( pMan->pName );
    Aig_ManStop( pMan );
    if ( Abc_NtkBddToMuxesPerformGlo( pNtk, pNtkNew, 1000000, fReorder ) )
    {
        Abc_Ntk_t * pStrash = Abc_NtkStrash( pNtkNew, 1, 1, 0 );
        pRes = Abc_NtkStrashToGia( pStrash );
        Abc_NtkDelete( pStrash );
    }
    Abc_NtkDelete( pNtkNew );
    Abc_NtkDelete( pNtk );
    return pRes;
}
int Gia_ManDoTest1( Gia_Man_t * p, int fReorder )
{
    Gia_Man_t * pTemp, * pNew; int Res;
    pNew = Gia_ManDoMuxTransform( p, fReorder );
    pNew = Gia_ManDoMuxMapping( pTemp = pNew );
    Gia_ManStop( pTemp );
    Res = Gia_ManLutNum( pNew );
    Gia_ManStop( pNew );
    return Res;
}
Gia_Man_t * Gia_ManPerformMinLut( Gia_Man_t * p, int GroupSize, int LutSize, int fVerbose )
{
    Gia_Man_t * pNew = NULL;
    int Res1, Res2, Result = 0;
    int g, nGroups = Gia_ManCoNum(p) / GroupSize;
    assert( Gia_ManCoNum(p) % GroupSize == 0 );
    assert( GroupSize <= 64 );
    for ( g = 0; g < nGroups; g++ )
    {
        Gia_Man_t * pNew;//, * pTemp;
        int fTrimPis = 0;
        int o, pPos[64];
        for ( o = 0; o < GroupSize; o++ )
            pPos[o] = g*GroupSize+o;
        pNew = Gia_ManDupCones( p, pPos, GroupSize, fTrimPis );
        printf( "%3d / %3d :  ", g, nGroups );
        printf( "Test1 = %4d   ", Res1 = Gia_ManDoTest1(pNew, 0) );
        printf( "Test2 = %4d   ", Res2 = Gia_ManDoTest1(pNew, 1) );
        printf( "Test  = %4d   ", Abc_MinInt(Res1, Res2) );
        printf( "\n" );
        Result += Abc_MinInt(Res1, Res2);
        //Gia_ManPrintStats( pNew, NULL );
        Gia_ManStop( pNew );
    }
    printf( "Total LUT count = %d.\n", Result );
    return pNew;
}

#else

Gia_Man_t * Gia_ManPerformMinLut( Gia_Man_t * p, int GroupSize, int LutSize, int fVerbose )
{
    return NULL;
}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

