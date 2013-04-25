/**CFile****************************************************************

  FileName    [sscCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT sweeping under constraints.]

  Synopsis    [The core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: sscCore.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sscInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [This procedure sets default parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssc_ManSetDefaultParams( Ssc_Pars_t * p )
{
    memset( p, 0, sizeof(Ssc_Pars_t) );
    p->nWords         =     4;  // the number of simulation words
    p->nBTLimit       =  1000;  // conflict limit at a node
    p->nSatVarMax     =  5000;  // the max number of SAT variables
    p->nCallsRecycle  =   100;  // calls to perform before recycling SAT solver
    p->fVerbose       =     0;  // verbose stats
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssc_ManStop( Ssc_Man_t * p )
{
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    Vec_IntFreeP( &p->vSatVars );
    Gia_ManStopP( &p->pFraig );
    Vec_IntFreeP( &p->vPivot );
    ABC_FREE( p );
}
Ssc_Man_t * Ssc_ManStart( Gia_Man_t * pAig, Gia_Man_t * pCare, Ssc_Pars_t * pPars )
{
    Ssc_Man_t * p;
    p = ABC_CALLOC( Ssc_Man_t, 1 );
    p->pPars  = pPars;
    p->pAig   = pAig;
    p->pCare  = pCare;
    p->pFraig = Gia_ManDup( p->pCare );
    Gia_ManInvertPos( p->pFraig );
    Ssc_ManStartSolver( p );
    if ( p->pSat == NULL )
    {
        printf( "Constraints are UNSAT after propagation.\n" );
        Ssc_ManStop( p );
        return NULL;
    }
    p->vPivot = Ssc_GiaFindPivotSim( p->pFraig );
//    Vec_IntFreeP( &p->vPivot  );
    if ( p->vPivot == NULL )
        p->vPivot = Ssc_ManFindPivotSat( p );
    if ( p->vPivot == NULL )
    {
        printf( "Constraints are UNSAT or conflict limit is too low.\n" );
        Ssc_ManStop( p );
        return NULL;
    }
    Vec_IntPrint( p->vPivot );
    return p;
}

/**Function*************************************************************

  Synopsis    [Performs computation of AIGs with choices.]

  Description [Takes several AIGs and performs choicing.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Ssc_PerformSweeping( Gia_Man_t * pAig, Gia_Man_t * pCare, Ssc_Pars_t * pPars )
{
    Ssc_Man_t * p;
    Gia_Man_t * pResult;
    clock_t clk, clkTotal = clock();
    int i;
    assert( Gia_ManRegNum(pCare) == 0 );
    assert( Gia_ManPiNum(pAig) == Gia_ManPiNum(pCare) );
    assert( Gia_ManIsNormalized(pAig) );
    assert( Gia_ManIsNormalized(pCare) );
    // reset random numbers
    Gia_ManRandom( 1 );
    // sweeping manager
    p = Ssc_ManStart( pAig, pCare, pPars );
    if ( p == NULL )
        return Gia_ManDup( pAig );
    // perform simulation 
clk = clock();
    for ( i = 0; i < 16; i++ )
    {
        Ssc_GiaRandomPiPattern( pAig, 10, NULL );
        Ssc_GiaSimRound( pAig );
        Ssc_GiaClassesRefine( pAig );
        Gia_ManEquivPrintClasses( pAig, 0, 0 );
    }
p->timeSimInit += clock() - clk;
    // remember the resulting AIG
    pResult = Gia_ManEquivReduce( pAig, 1, 0, 0 );
    if ( pResult == NULL )
    {
        printf( "There is no equivalences.\n" );
        pResult = Gia_ManDup( pAig );
    }
    Ssc_ManStop( p );
    // count the number of representatives
    if ( pPars->fVerbose ) 
    {
        Gia_ManEquivPrintClasses( pAig, 0, 0 );
        Abc_Print( 1, "Reduction in AIG nodes:%8d  ->%8d.  ", Gia_ManAndNum(pAig), Gia_ManAndNum(pResult) );
        Abc_PrintTime( 1, "Time", clock() - clkTotal );
    }
    return pResult;
}
Gia_Man_t * Ssc_PerformSweepingConstr( Gia_Man_t * p, Ssc_Pars_t * pPars )
{
    Gia_Man_t * pAig, * pCare, * pResult;
    int i;
    if ( p->nConstrs == 0 )
    {
        pAig = Gia_ManDup( p );
        pCare = Gia_ManStart( Gia_ManPiNum(p) + 2 );
        pCare->pName = Abc_UtilStrsav( "care" );
        for ( i = 0; i < Gia_ManPiNum(p); i++ )
            Gia_ManAppendCi( pCare );
        Gia_ManAppendCo( pCare, 1 );
    }
    else
    {
        Vec_Int_t * vOuts = Vec_IntStartNatural( Gia_ManPoNum(p) );
        pAig = Gia_ManDupCones( p, Vec_IntArray(vOuts), Gia_ManPoNum(p) - p->nConstrs, 0 );
        pCare = Gia_ManDupCones( p, Vec_IntArray(vOuts) + Gia_ManPoNum(p) - p->nConstrs, p->nConstrs, 0 );
        Vec_IntFree( vOuts );
    }
    pResult = Ssc_PerformSweeping( pAig, pCare, pPars );
    Gia_ManStop( pAig );
    Gia_ManStop( pCare );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

