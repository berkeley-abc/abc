/**CFile****************************************************************

  FileName    [mfsMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The good old minimization with complete don't-cares.]

  Synopsis    [Procedures working with the manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mfsMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mfsInt.h"

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
Mfs_Man_t * Mfs_ManAlloc( Mfs_Par_t * pPars )
{
    Mfs_Man_t * p;
    // start the manager
    p = ALLOC( Mfs_Man_t, 1 );
    memset( p, 0, sizeof(Mfs_Man_t) );
    p->pPars     = pPars;
    p->vProjVars = Vec_IntAlloc( 100 );
    p->vDivLits  = Vec_IntAlloc( 100 );
    p->nDivWords = Aig_BitWordNum(p->pPars->nDivMax + MFS_FANIN_MAX);
    p->vDivCexes = Vec_PtrAllocSimInfo( p->pPars->nDivMax+MFS_FANIN_MAX+1, p->nDivWords );
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
void Mfs_ManClean( Mfs_Man_t * p )
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
void Mfs_ManPrint( Mfs_Man_t * p )
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
            Abc_NtkNodeNum(p->pNtk), p->nNodesTried, p->nNodesResub, p->nTotalDivs, p->nSatCalls, p->nTimeOuts );
        if ( p->pPars->fSwapEdge )
            printf( "Swappable edges = %d. Total edges = %d. Ratio = %5.2f.\n", 
                p->nNodesResub, Abc_NtkGetTotalFanins(p->pNtk), 1.00 * p->nNodesResub / Abc_NtkGetTotalFanins(p->pNtk) );
        else
            Abc_NtkMfsPrintResubStats( p );
    }
    else
    {
        printf( "Nodes = %d.  Care mints = %d. Total mints = %d. Ratio = %5.2f.\n", 
            p->nNodesTried, p->nMintsCare, p->nMintsTotal, 1.0 * p->nMintsCare / p->nMintsTotal );
    }
    PRTP( "Win", p->timeWin            ,  p->timeTotal );
    PRTP( "Div", p->timeDiv            ,  p->timeTotal );
    PRTP( "Aig", p->timeAig            ,  p->timeTotal );
    PRTP( "Cnf", p->timeCnf            ,  p->timeTotal );
    PRTP( "Sat", p->timeSat-p->timeInt ,  p->timeTotal );
    PRTP( "Int", p->timeInt            ,  p->timeTotal );
    PRTP( "ALL", p->timeTotal          ,  p->timeTotal );

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Mfs_ManStop( Mfs_Man_t * p )
{
    if ( p->pPars->fVerbose )
        Mfs_ManPrint( p );
    if ( p->pCare )
        Aig_ManStop( p->pCare );
    if ( p->vSuppsInv )
        Vec_VecFree( (Vec_Vec_t *)p->vSuppsInv );
    Mfs_ManClean( p );
    Int_ManFree( p->pMan );
    Vec_IntFree( p->vMem );
    Vec_VecFree( p->vLevels );
    Vec_PtrFree( p->vFanins );
    Vec_IntFree( p->vProjVars );
    Vec_IntFree( p->vDivLits );
    Vec_PtrFree( p->vDivCexes );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


