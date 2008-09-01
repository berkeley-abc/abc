/**CFile****************************************************************

  FileName    [sswMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Calls to the SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswMan.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ssw_Man_t * Ssw_ManCreate( Aig_Man_t * pAig, Ssw_Pars_t * pPars )
{
    Ssw_Man_t * p;
    // create interpolation manager
    p = ALLOC( Ssw_Man_t, 1 );
    memset( p, 0, sizeof(Ssw_Man_t) );
    p->pPars        = pPars;
    p->pAig         = pAig;
    p->nFrames      = pPars->nFramesK + 1;
    Aig_ManFanoutStart( pAig );
    // SAT solving
    p->nSatVars     = 1;
    p->pSatVars     = CALLOC( int, Aig_ManObjNumMax(p->pAig) );
    p->vFanins      = Vec_PtrAlloc( 100 );
    p->vSimRoots    = Vec_PtrAlloc( 1000 );
    p->vSimClasses  = Vec_PtrAlloc( 1000 );
    // equivalences proved
//    p->pReprsProved = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAig) );
    p->pNodeToFraig = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAig) * p->nFrames );
    return p;
}

/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManCountEquivs( Ssw_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i, nEquivs = 0;
    Aig_ManForEachObj( p->pAig, pObj, i )
//        nEquivs += ( p->pReprsProved[i] != NULL );
        nEquivs += ( Aig_ObjRepr(p->pAig, pObj) != NULL );
    return nEquivs;
}

/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManPrintStats( Ssw_Man_t * p )
{
    printf( "Parameters: Frames = %d. Conf limit = %d. Constrs = %d.\n", 
        p->pPars->nFramesK, p->pPars->nBTLimit, p->pPars->nConstrs );
    printf( "AIG       : PI = %d. PO = %d. Latch = %d. Node = %d.\n", 
        Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), Saig_ManRegNum(p->pAig), Aig_ManNodeNum(p->pAig) );
    printf( "SAT solver: Vars = %d.\n", p->nSatVars );
    printf( "SAT calls : All = %6d. Unsat = %6d. Sat = %6d. Fail = %6d.\n", 
        p->nSatCalls, p->nSatCalls-p->nSatCallsSat-p->nSatFailsReal, 
        p->nSatCallsSat, p->nSatFailsReal );
    printf( "Equivs    : All = %6d.\n", Ssw_ManCountEquivs(p) );
    printf( "Runtime statistics:\n" );
    p->timeOther = p->timeTotal-p->timeBmc-p->timeReduce-p->timeSimSat-p->timeSat;
    PRTP( "BMC        ", p->timeBmc,      p->timeTotal );
    PRTP( "Spec reduce", p->timeReduce,   p->timeTotal );
    PRTP( "Sim SAT    ", p->timeSimSat,   p->timeTotal );
    PRTP( "SAT solving", p->timeSat,      p->timeTotal );
    PRTP( "  sat      ", p->timeSatSat,   p->timeTotal );
    PRTP( "  unsat    ", p->timeSatUnsat, p->timeTotal );
    PRTP( "  undecided", p->timeSatUndec, p->timeTotal );
    PRTP( "Other      ", p->timeOther,    p->timeTotal );
    PRTP( "TOTAL      ", p->timeTotal,    p->timeTotal );
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManCleanup( Ssw_Man_t * p )
{
    Aig_ManCleanMarkB( p->pAig );
    if ( p->pFrames )
    {
        Aig_ManStop( p->pFrames );
        p->pFrames = NULL;
    }
    if ( p->pSat )
    {
        sat_solver_delete( p->pSat );
        p->pSat = NULL;
        p->nSatVars = 0;
    }
    memset( p->pNodeToFraig, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p->pAig) * p->nFrames );
    p->nConstrTotal = 0;
    p->nConstrReduced = 0;
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManStop( Ssw_Man_t * p )
{
    if ( p->pPars->fVerbose )
        Ssw_ManPrintStats( p );
    if ( p->ppClasses )
        Ssw_ClassesStop( p->ppClasses );
    Vec_PtrFree( p->vFanins );
    Vec_PtrFree( p->vSimRoots );
    Vec_PtrFree( p->vSimClasses );
    FREE( p->pNodeToFraig );
//    FREE( p->pReprsProved );
    FREE( p->pSatVars );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Starts the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManStartSolver( Ssw_Man_t * p )
{
    int Lit;
    assert( p->pSat == NULL );
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, 10000 );
    // var 0 is not used
    // var 1 is reserved for const1 node - add the clause
    Lit = toLit( 1 );
    if ( p->pPars->fPolarFlip )
        Lit = lit_neg( Lit );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    p->nSatVars = 2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


