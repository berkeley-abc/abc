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
    p->pNodeToFrames = CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAig) * p->nFrames );
    p->vCommon       = Vec_PtrAlloc( 100 );
    p->iOutputLit    = -1;
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

    printf( "Parameters: F = %d. AddF = %d. C-lim = %d. Constr = %d. MaxLev = %d. Mem = %0.2f Mb.\n", 
        p->pPars->nFramesK, p->pPars->nFramesAddSim, p->pPars->nBTLimit, p->pPars->nConstrs, p->pPars->nMaxLevs, nMemory );
    printf( "AIG       : PI = %d. PO = %d. Latch = %d. Node = %d.  Ave SAT vars = %d.\n", 
        Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), Saig_ManRegNum(p->pAig), Aig_ManNodeNum(p->pAig), 
        0/p->pPars->nIters );
    printf( "SAT calls : Proof = %d. Cex = %d. Fail = %d. Equivs = %d. Str = %d.\n", 
        p->nSatProof, p->nSatCallsSat, p->nSatFailsTotal, Ssw_ManCountEquivs(p), p->nStrangers );
    printf( "SAT solver: Vars = %d. Max cone = %d. Recycles = %d. Rounds = %d.\n", 
        0, p->nConeMax, p->nRecycles, p->nSimRounds );
    printf( "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
        p->nNodesBeg, p->nNodesEnd, 100.0*(p->nNodesBeg-p->nNodesEnd)/(p->nNodesBeg?p->nNodesBeg:1), 
        p->nRegsBeg, p->nRegsEnd, 100.0*(p->nRegsBeg-p->nRegsEnd)/(p->nRegsBeg?p->nRegsBeg:1) );

    p->timeOther = p->timeTotal-p->timeBmc-p->timeReduce-p->timeMarkCones-p->timeSimSat-p->timeSat;
    PRTP( "BMC        ", p->timeBmc,       p->timeTotal );
    PRTP( "Spec reduce", p->timeReduce,    p->timeTotal );
    PRTP( "Mark cones ", p->timeMarkCones, p->timeTotal );
    PRTP( "Sim SAT    ", p->timeSimSat,    p->timeTotal );
    PRTP( "SAT solving", p->timeSat,       p->timeTotal );
    PRTP( "  unsat    ", p->timeSatUnsat,  p->timeTotal );
    PRTP( "  sat      ", p->timeSatSat,    p->timeTotal );
    PRTP( "  undecided", p->timeSatUndec,  p->timeTotal );
    PRTP( "Other      ", p->timeOther,     p->timeTotal );
    PRTP( "TOTAL      ", p->timeTotal,     p->timeTotal );
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManCleanup( Ssw_Man_t * p )
{
    assert( p->pMSat == NULL );
    if ( p->pFrames )
    {
        Aig_ManCleanMarkA( p->pFrames );
        Aig_ManStop( p->pFrames );
        p->pFrames = NULL;
        memset( p->pNodeToFrames, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p->pAig) * p->nFrames );
    }
    if ( p->vSimInfo )  
    {
        Vec_PtrFree( p->vSimInfo );
        p->vSimInfo = NULL;
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
    Aig_ManCleanMarkA( p->pAig );
    Aig_ManCleanMarkB( p->pAig );
    if ( p->pPars->fVerbose )
        Ssw_ManPrintStats( p );
    if ( p->ppClasses )
        Ssw_ClassesStop( p->ppClasses );
    if ( p->pSml )      
        Ssw_SmlStop( p->pSml );
    if ( p->vDiffPairs )
        Vec_IntFree( p->vDiffPairs );
    Vec_PtrFree( p->vCommon );
    FREE( p->pNodeToFrames );
    FREE( p->pPatWords );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


