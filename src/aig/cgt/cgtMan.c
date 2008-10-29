/**CFile****************************************************************

  FileName    [cgtMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Clock gating package.]

  Synopsis    [Manipulation of clock gating manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cgtMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cgtInt.h"

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
Cgt_Man_t * Cgt_ManCreate( Aig_Man_t * pAig, Aig_Man_t * pCare, Cgt_Par_t * pPars )
{
    Cgt_Man_t * p;
    // prepare the sequential AIG
    assert( Saig_ManRegNum(pAig) > 0 );
    Aig_ManFanoutStart( pAig );
    Aig_ManSetPioNumbers( pAig );
    // create interpolation manager
    p = ALLOC( Cgt_Man_t, 1 ); 
    memset( p, 0, sizeof(Cgt_Man_t) );
    p->pPars      = pPars;
    p->pAig       = pAig;
    p->vGatesAll  = Vec_VecStart( Saig_ManRegNum(pAig) );
    p->vFanout    = Vec_PtrAlloc( 1000 );
    p->nPattWords = 16;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManClean( Cgt_Man_t * p )
{
    if ( p->pPart )
    {
        Aig_ManStop( p->pPart );
        p->pPart = NULL;
    }
    if ( p->pCnf )
    {
        Cnf_DataFree( p->pCnf );
        p->pCnf = NULL;
    }
    if ( p->pSat )
    {
        sat_solver_delete( p->pSat );
        p->pSat = NULL;
    }
    if ( p->vPatts )
    {
        Vec_PtrFree( p->vPatts );
        p->vPatts = NULL;
    }
}


/**Function*************************************************************

  Synopsis    [Prints stats of the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManPrintStats( Cgt_Man_t * p )
{
/*
    double nMemory = 1.0*Aig_ManObjNumMax(p->pAig)*p->nFrames*(2*sizeof(int)+2*sizeof(void*))/(1<<20);

    printf( "Parameters: F = %d. AddF = %d. C-lim = %d. Constr = %d. MaxLev = %d. Mem = %0.2f Mb.\n", 
        p->pPars->nFramesK, p->pPars->nFramesAddSim, p->pPars->nBTLimit, p->pPars->nConstrs, p->pPars->nMaxLevs, nMemory );
    printf( "AIG       : PI = %d. PO = %d. Latch = %d. Node = %d.  Ave SAT vars = %d.\n", 
        Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), Saig_ManRegNum(p->pAig), Aig_ManNodeNum(p->pAig), 
        0/p->pPars->nIters );
    printf( "SAT calls : Proof = %d. Cex = %d. Fail = %d. Lits proved = %d.\n", 
        p->nSatProof, p->nSatCallsSat, p->nSatFailsReal, Cgt_ManCountEquivs(p) );
    printf( "SAT solver: Vars max = %d. Calls max = %d. Recycles = %d. Sim rounds = %d.\n", 
        p->nVarsMax, p->nCallsMax, p->nRecyclesTotal, p->nSimRounds );
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
*/
}

/**Function*************************************************************

  Synopsis    [Frees the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cgt_ManStop( Cgt_Man_t * p )
{
    if ( p->pPars->fVerbose )
        Cgt_ManPrintStats( p );
    if ( p->pFrame )
        Aig_ManStop( p->pFrame );
    Cgt_ManClean( p );
    Vec_PtrFree( p->vFanout );
    Vec_PtrFree( p->vGates );
    Vec_VecFree( p->vGatesAll );
    free( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


