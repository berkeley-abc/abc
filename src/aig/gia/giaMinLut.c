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

