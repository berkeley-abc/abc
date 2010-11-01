/**CFile****************************************************************

  FileName    [mfxMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedures working with the manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfxMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfxInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mfx_Man_t * Mfx_ManAlloc( Mfx_Par_t * pPars )
{
    Mfx_Man_t * p;
    // start the manager
    p = ABC_ALLOC( Mfx_Man_t, 1 );
    memset( p, 0, sizeof(Mfx_Man_t) );
    p->pPars     = pPars;
    p->vProjVars = Vec_IntAlloc( 100 );
    p->vDivLits  = Vec_IntAlloc( 100 );
    p->nDivWords = Aig_BitWordNum(p->pPars->nDivMax + MFX_FANIN_MAX);
    p->vDivCexes = Vec_PtrAllocSimInfo( p->pPars->nDivMax+MFX_FANIN_MAX+1, p->nDivWords );
    p->pMan      = Int_ManAlloc();
    p->vMem      = Vec_IntAlloc( 0 );
    p->vLevels   = Vec_VecStart( 32 );
    p->vFanins   = Vec_PtrAlloc( 32 );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfx_ManClean( Mfx_Man_t * p )
{
    if ( p->pAigWin )
        Aig_ManStop( p->pAigWin );
    if ( p->pCnf )
        Cnf_DataFree( p->pCnf );
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    if ( p->vRoots )
        Vec_PtrFree( p->vRoots );
    if ( p->vSupp )
        Vec_PtrFree( p->vSupp );
    if ( p->vNodes )
        Vec_PtrFree( p->vNodes );
    if ( p->vDivs )
        Vec_PtrFree( p->vDivs );
    p->pAigWin = NULL;
    p->pCnf    = NULL;
    p->pSat    = NULL;
    p->vRoots  = NULL;
    p->vSupp   = NULL;
    p->vNodes  = NULL;
    p->vDivs   = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfx_ManPrint( Mfx_Man_t * p )
{
    if ( p->pPars->fResub )
    {
        printf( "Reduction in nodes = %5d. (%.2f %%) ", 
            p->nTotalNodesBeg-p->nTotalNodesEnd, 
            100.0*(p->nTotalNodesBeg-p->nTotalNodesEnd)/p->nTotalNodesBeg );
        printf( "Reduction in edges = %5d. (%.2f %%) ", 
            p->nTotalEdgesBeg-p->nTotalEdgesEnd, 
            100.0*(p->nTotalEdgesBeg-p->nTotalEdgesEnd)/p->nTotalEdgesBeg );
        printf( "\n" );
        printf( "Nodes = %d. Try = %d. Resub = %d. Div = %d. SAT calls = %d. Timeouts = %d.\n", 
            Nwk_ManNodeNum(p->pNtk), p->nNodesTried, p->nNodesResub, p->nTotalDivs, p->nSatCalls, p->nTimeOuts );
        if ( p->pPars->fSwapEdge )
            printf( "Swappable edges = %d. Total edges = %d. Ratio = %5.2f.\n", 
                p->nNodesResub, Nwk_ManGetTotalFanins(p->pNtk), 1.00 * p->nNodesResub / Nwk_ManGetTotalFanins(p->pNtk) );
//        else
//            Mfx_PrintResubStats( p );
//        printf( "Average ratio of DCs in the resubed nodes = %.2f.\n", 1.0*p->nDcMints/(64 * p->nNodesResub) );
    }
    else
    {
        printf( "Nodes = %d. Try = %d. Total mints = %d. Local DC mints = %d. Ratio = %5.2f.\n", 
            Nwk_ManNodeNum(p->pNtk), p->nNodesTried, p->nMintsTotal, p->nMintsTotal-p->nMintsCare, 
            1.0 * (p->nMintsTotal-p->nMintsCare) / p->nMintsTotal );
//        printf( "Average ratio of sequential DCs in the global space = %5.2f.\n", 
//            1.0-(p->dTotalRatios/p->nNodesTried) );
        printf( "Nodes resyn = %d. Ratio = %5.2f.  Total AIG node gain = %d. Timeouts = %d.\n", 
            p->nNodesDec, 1.0 * p->nNodesDec / p->nNodesTried, p->nNodesGained, p->nTimeOuts );
    }
/*
    ABC_PRTP( "Win", p->timeWin            ,  p->timeTotal );
    ABC_PRTP( "Div", p->timeDiv            ,  p->timeTotal );
    ABC_PRTP( "Aig", p->timeAig            ,  p->timeTotal );
    ABC_PRTP( "Cnf", p->timeCnf            ,  p->timeTotal );
    ABC_PRTP( "Sat", p->timeSat-p->timeInt ,  p->timeTotal );
    ABC_PRTP( "Int", p->timeInt            ,  p->timeTotal );
    ABC_PRTP( "ALL", p->timeTotal          ,  p->timeTotal );
*/
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfx_ManStop( Mfx_Man_t * p )
{
    if ( p->pPars->fVerbose )
        Mfx_ManPrint( p );
    if ( p->vTruth )
        Vec_IntFree( p->vTruth );
    if ( p->pManDec )
        Bdc_ManFree( p->pManDec );
    if ( p->pCare )
        Aig_ManStop( p->pCare );
    if ( p->vSuppsInv )
        Vec_VecFree( (Vec_Vec_t *)p->vSuppsInv );
    if ( p->vProbs )
        Vec_IntFree( p->vProbs );
    Mfx_ManClean( p );
    Int_ManFree( p->pMan );
    Vec_IntFree( p->vMem );
    Vec_VecFree( p->vLevels );
    Vec_PtrFree( p->vFanins );
    Vec_IntFree( p->vProjVars );
    Vec_IntFree( p->vDivLits );
    Vec_PtrFree( p->vDivCexes );
    ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

