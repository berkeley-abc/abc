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
    // prepare the sequential AIG
    assert( Saig_ManRegNum(pAig) > 0 );
    Aig_ManFanoutStart( pAig );
    Aig_ManSetPioNumbers( pAig );
    // create interpolation manager
    p = ALLOC( Ssw_Man_t, 1 );
    memset( p, 0, sizeof(Ssw_Man_t) );
    p->pPars         = pPars;
    p->pAig          = pAig;
    p->nFrames       = pPars->nFramesK + 1;
    p->pNodeToFraig  = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAig) * p->nFrames );
    // SAT solving
    p->pSatVars      = CALLOC( int, Aig_ManObjNumMax(p->pAig) * p->nFrames );
    p->vFanins       = Vec_PtrAlloc( 100 );
    p->vSimRoots     = Vec_PtrAlloc( 1000 );
    p->vSimClasses   = Vec_PtrAlloc( 1000 );
    // allocate storage for sim pattern
    p->nPatWords     = Aig_BitWordNum( Saig_ManPiNum(pAig) * p->nFrames + Saig_ManRegNum(pAig) );
    p->pPatWords     = ALLOC( unsigned, p->nPatWords ); 
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
    double nMemory = 1.0*Aig_ManObjNumMax(p->pAig)*p->nFrames*(2*sizeof(int)+2*sizeof(void*))/(1<<20);

    printf( "Parameters: Frames = %d. Conf limit = %d. Constrs = %d. Max lev = %d. Mem = %0.2f Mb.\n", 
        p->pPars->nFramesK, p->pPars->nBTLimit, p->pPars->nConstrs, p->pPars->nMaxLevs, nMemory );
    printf( "AIG       : PI = %d. PO = %d. Latch = %d. Node = %d.  Ave SAT vars = %d.\n", 
        Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), Saig_ManRegNum(p->pAig), Aig_ManNodeNum(p->pAig), 
        p->nSatVarsTotal/p->pPars->nIters );
    printf( "SAT calls : Proof = %d. Cex = %d. Fail = %d. FailReal = %d.  Equivs = %d. Str = %d.\n", 
        p->nSatProof, p->nSatCallsSat, p->nSatFails, p->nSatFailsReal, Ssw_ManCountEquivs(p), p->nStrangers );
    printf( "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
        p->nNodesBeg, p->nNodesEnd, 100.0*(p->nNodesBeg-p->nNodesEnd)/(p->nNodesBeg?p->nNodesBeg:1), 
        p->nRegsBeg, p->nRegsEnd, 100.0*(p->nRegsBeg-p->nRegsEnd)/(p->nRegsBeg?p->nRegsBeg:1) );

    p->timeOther = p->timeTotal-p->timeBmc-p->timeReduce-p->timeSimSat-p->timeSat;
    PRTP( "BMC        ", p->timeBmc,      p->timeTotal );
    PRTP( "Spec reduce", p->timeReduce,   p->timeTotal );
    PRTP( "Sim SAT    ", p->timeSimSat,   p->timeTotal );
    PRTP( "SAT solving", p->timeSat,      p->timeTotal );
    PRTP( "  unsat    ", p->timeSatUnsat, p->timeTotal );
    PRTP( "  sat      ", p->timeSatSat,   p->timeTotal );
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
        memset( p->pNodeToFraig, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p->pAig) * p->nFrames );
    }
    if ( p->pSat )
    {
//        printf( "Vars = %d. Clauses = %d. Learnts = %d.\n", p->pSat->size, p->pSat->clauses.size, p->pSat->learnts.size );
        p->nSatVarsTotal += p->pSat->size;
        sat_solver_delete( p->pSat );
        p->pSat = NULL;
        memset( p->pSatVars, 0, sizeof(int) * Aig_ManObjNumMax(p->pAig) * p->nFrames );
    }
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
    if ( p->pSml )      
        Ssw_SmlStop( p->pSml );
    Vec_PtrFree( p->vFanins );
    Vec_PtrFree( p->vSimRoots );
    Vec_PtrFree( p->vSimClasses );
    FREE( p->pNodeToFraig );
    FREE( p->pSatVars );
    FREE( p->pPatWords );
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
    sat_solver_setnvars( p->pSat, 1000 );
    // var 0 is not used
    // var 1 is reserved for const1 node - add the clause
    p->nSatVars = 1;
    Lit = toLit( p->nSatVars );
    if ( p->pPars->fPolarFlip )
        Lit = lit_neg( Lit );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    Ssw_ObjSetSatNum( p, Aig_ManConst1(p->pAig), p->nSatVars++ );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


