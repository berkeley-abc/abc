/**CFile****************************************************************

  FileName    [ifSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Sequential mapping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifSeq.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int  If_ManBinarySearchPeriod( If_Man_t * p, int Mode );
static int  If_ManBinarySearch_rec( If_Man_t * p, int Mode, int FiMin, int FiMax );
static int  If_ManPerformMappingRoundSeq( If_Man_t * p, int Mode, int nIter, char * pLabel );
static int  If_ManPrepareMappingSeq( If_Man_t * p );
static int  If_ObjPerformMappingLatch( If_Man_t * p, If_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs sequential mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMappingSeq( If_Man_t * p )
{
    int PeriodBest, Mode = 0;

    // collect nodes in the sequential order
    If_ManPrepareMappingSeq( p );

    // perform combinational mapping to get the upper bound on the clock period
    If_ManPerformMappingRound( p, 2, 0, 0, NULL );
    p->RequiredGlo = If_ManDelayMax( p, 0 );

    // set parameters
    p->nCutsUsed = p->pPars->nCutsMax;
    p->nAttempts = 0;
    p->nMaxIters = 50;
    p->Period    = (int)p->RequiredGlo;

    // make sure the clock period words
    if ( !If_ManBinarySearchPeriod( p, Mode ) )
    {
        printf( "If_ManPerformMappingSeq(): The upper bound on the clock period cannot be computed.\n" );
        return 0;
    }

    // perform binary search
    PeriodBest = If_ManBinarySearch_rec( p, Mode, 0, p->Period );

    // recompute the best l-values
    if ( p->Period != PeriodBest )
    {
        p->Period = PeriodBest;
        if ( !If_ManBinarySearchPeriod( p, Mode ) )
        {
            printf( "If_ManPerformMappingSeq(): The final clock period cannot be confirmed.\n" );
            return 0;
        }
    }
/*
    // fix the problem with non-converged delays
    If_ManForEachNode( p, pObj, i )
        if ( pObj->LValue < -ABC_INFINITY/2 )
            pObj->LValue = (float)0.0;
    // write the retiming lags
    p->vLags = Vec_IntStart( If_ManObjNum(p) + 1 );
    If_ManForEachNode( p, pObj, i )
        Vec_IntWriteEntry( vLags, i, Abc_NodeComputeLag(pObj->LValue, p->Period) );
*/
/*
    // print the statistic into a file
    {
        FILE * pTable;
        pTable = fopen( "a/seqmap__stats.txt", "a+" );
        fprintf( pTable, "%d ", p->Period );
        fprintf( pTable, "\n" );
        fclose( pTable );
    }
*/
    // print the result
    if ( p->pPars->fLiftLeaves )
    {
//        if ( p->pPars->fVerbose )   
            printf( "The best clock period is %3d. (Currently, network is not modified, so mapping will fail.)\n", p->Period );
        return 0;
    }
//    if ( p->pPars->fVerbose )   
        printf( "The best clock period is %3d.\n", p->Period );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManBinarySearch_rec( If_Man_t * p, int Mode, int FiMin, int FiMax )
{
    assert( FiMin < FiMax );
    if ( FiMin + 1 == FiMax )
        return FiMax;
    // compute the median
    p->Period = FiMin + (FiMax - FiMin)/2;
    if ( If_ManBinarySearchPeriod( p, Mode ) )
        return If_ManBinarySearch_rec( p, Mode, FiMin, p->Period ); // Median is feasible
    else 
        return If_ManBinarySearch_rec( p, Mode, p->Period, FiMax ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManBinarySearchPeriod( If_Man_t * p, int Mode )
{
    If_Obj_t * pObj;
    int i, c, fConverged;
    int fResetRefs = 0;

    p->nAttempts++;

    // set l-values of all nodes to be minus infinity, except PIs and constants
    If_ManForEachObj( p, pObj, i )
    {
        pObj->nCuts = 1;
        If_ObjSetLValue( pObj, -IF_FLOAT_LARGE );
        if ( fResetRefs )
            pObj->nRefs = 0;
    }
    If_ObjSetLValue( If_ManConst1(p), (float)0.0 );
    If_ManForEachPi( p, pObj, i )
        If_ObjSetLValue( pObj, (float)0.0 );

    // reset references to their original state
    if ( fResetRefs )
    {
        If_ManForEachObj( p, pObj, i )
        {
            if ( If_ObjIsCo(pObj) )
                continue;
            if ( pObj->pFanin0 ) pObj->pFanin0->nRefs++;
            if ( pObj->pFanin1 ) pObj->pFanin1->nRefs++;
        }
    }

    // update all values iteratively
    fConverged = 0;
    for ( c = 1; c <= p->nMaxIters; c++ )
    {
        if ( !If_ManPerformMappingRoundSeq( p, Mode, c, NULL ) )
        {
            fConverged = 1;
            break;
        }
        p->RequiredGlo = If_ManDelayMax( p, 1 );
        if ( p->RequiredGlo > p->Period + p->fEpsilon )
            break; 
    }

    // report the results
    if ( p->pPars->fVerbose )
    {
        p->AreaGlo = p->pPars->fLiftLeaves? If_ManScanMappingSeq(p) : If_ManScanMapping(p);
        printf( "Attempt = %2d.  Iters = %3d.  Area = %10.2f.  Fi = %6.2f.  ", p->nAttempts, c, p->AreaGlo, (float)p->Period );
        if ( fConverged )
            printf( "  Feasible" );
        else if ( c > p->nMaxIters )
            printf( "Infeasible (timeout)" );
        else
            printf( "Infeasible" );
        printf( "\n" );
    }
    return fConverged;
}

/**Function*************************************************************

  Synopsis    [Performs one pass of l-value computation over all nodes.]

  Description [Experimentally it was found that checking POs changes
  is not enough to detect the convergence of l-values in the network.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPerformMappingRoundSeq( If_Man_t * p, int Mode, int nIter, char * pLabel )
{
    ProgressBar * pProgress;
    If_Obj_t * pObj;
    int i, clk = clock();
    int fVeryVerbose = 0;
    int fChange = 0;
    assert( Mode >= 0 && Mode <= 2 );
    if ( !p->pPars->fVerbose )
        pProgress = Extra_ProgressBarStart( stdout, If_ManObjNum(p) );
    // map the internal nodes
    p->nCutsMerged = 0;
    If_ManForEachNode( p, pObj, i )
    {
        if ( !p->pPars->fVerbose )
            Extra_ProgressBarUpdate( pProgress, i, pLabel );
        // consider the camse of an AND gate
        assert( If_ObjIsAnd(pObj) );
        If_ObjPerformMappingAnd( p, pObj, Mode );
        if ( pObj->fRepr )
            If_ObjPerformMappingChoice( p, pObj, Mode );
        // check if updating happens
        if ( If_ObjLValue(pObj) < If_ObjCutBest(pObj)->Delay - p->fEpsilon )
        {
            If_ObjSetLValue( pObj, If_ObjCutBest(pObj)->Delay );
            fChange = 1;
        }
//if ( If_ObjLValue(pObj) > -1000.0 )
//printf( "Node %d %.2f  ", pObj->Id, If_ObjLValue(pObj) );
    }
    if ( !p->pPars->fVerbose )
        Extra_ProgressBarStop( pProgress );
    // propagate arrival times from the registers
    Vec_PtrForEachEntry( p->vLatchOrder, pObj, i )
        fChange |= If_ObjPerformMappingLatch( p, pObj );
//printf( "\n\n" );
    // compute area and delay
    if ( fVeryVerbose )
    {
        p->RequiredGlo = If_ManDelayMax( p, 1 );
        p->AreaGlo = p->pPars->fLiftLeaves? If_ManScanMappingSeq(p) : If_ManScanMapping(p);
        printf( "S%d:  Fi = %6.2f. Del = %6.2f. Area = %8.2f. Cuts = %8d. Lim = %2d. Ave = %5.2f. ", 
             nIter, (float)p->Period, p->RequiredGlo, p->AreaGlo, p->nCutsMerged, p->nCutsUsed, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
        PRT( "T", clock() - clk );
    }
    return fChange;
}

/**Function*************************************************************

  Synopsis    [Collects latches in the topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void If_ManCollectLatches_rec( If_Obj_t * pObj, Vec_Ptr_t * vLatches )
{
    if ( !If_ObjIsLatch(pObj) )
        return;
    if ( pObj->fMark )
        return;
    pObj->fMark = 1;
    If_ManCollectLatches_rec( pObj->pFanin0, vLatches );
    Vec_PtrPush( vLatches, pObj );
}

/**Function*************************************************************

  Synopsis    [Collects latches in the topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * If_ManCollectLatches( If_Man_t * p )
{
    Vec_Ptr_t * vLatches;
    If_Obj_t * pObj;
    int i;
    // collect latches 
    vLatches = Vec_PtrAlloc( p->pPars->nLatches );
    Vec_PtrForEachEntryStart( p->vCis, pObj, i, If_ManCiNum(p) - p->pPars->nLatches )
        If_ManCollectLatches_rec( pObj, vLatches );
    // clean marks
    Vec_PtrForEachEntry( vLatches, pObj, i )
        pObj->fMark = 0;
    assert( Vec_PtrSize(vLatches) == p->pPars->nLatches );
    return vLatches;
}

/**Function*************************************************************

  Synopsis    [Prepares for sequential mapping by linking the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManPrepareMappingSeq( If_Man_t * p )
{
    If_Obj_t * pObj, * pObjLi, * pObjLo, * pTemp;
    If_Cut_t * pCut;
    int i;
    // link the latch outputs (PIs) directly to the drivers of latch inputs (POs)
    for ( i = 0; i < p->pPars->nLatches; i++ )
    {
        pObjLo = If_ManCi( p, If_ManCiNum(p) - p->pPars->nLatches + i );
        pObjLi = If_ManCo( p, If_ManCoNum(p) - p->pPars->nLatches + i );
        pObjLo->pFanin0 = If_ObjFanin0( pObjLi );
        pObjLo->fCompl0 = If_ObjFaninC0( pObjLi );
//        pObjLo->pFanin0 = pObjLi;
    }
    // collect latches
    p->vLatchOrder = If_ManCollectLatches( p );
    // propagate elementary cuts 
    if ( p->pPars->fLiftLeaves )
    {
        Vec_PtrForEachEntry( p->vLatchOrder, pObj, i )
        {
            pCut = If_ObjCutTriv(pObj);
            If_CutCopy( pCut, If_ObjFanin0(pObj)->Cuts );
            If_CutLift( pCut );
            pCut->Delay  -= p->Period;
            pCut->fCompl ^= pObj->fCompl0;

            pTemp = If_ManObj(p, pCut->pLeaves[0] >> 8);
            assert( !If_ObjIsLatch(pTemp) );
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs mapping of the latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ObjPerformMappingLatch( If_Man_t * p, If_Obj_t * pObj )
{
    If_Obj_t * pFanin;
    If_Cut_t * pCut;
    float LValueOld;
    int i;
    assert( If_ObjIsLatch(pObj) );
    // save old l-value
    LValueOld = If_ObjLValue(pObj);
    pFanin = If_ObjFanin0(pObj);
    assert( pFanin->nCuts > 0 );
    if ( !p->pPars->fLiftLeaves )
    {
        pObj->nCuts = 1;
        If_ObjSetLValue( pObj, If_ObjLValue(pFanin) - p->Period );
    }
    else
    {
        pObj->nCuts = pFanin->nCuts;
        If_ObjForEachCut( pObj, pCut, i )
        {
            If_CutCopy( pCut, pFanin->Cuts + i );
            If_CutLift( pCut );
            pCut->Delay  -= p->Period;
            pCut->fCompl ^= pObj->fCompl0;
        }
    }
    return LValueOld != If_ObjLValue(pObj);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


