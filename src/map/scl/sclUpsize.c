/**CFile****************************************************************

  FileName    [sclUpsize.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Selective increase of gate sizes.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclUpsize.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"
#include "sclMan.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect TFO of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclFindTFO_rec( Abc_Obj_t * pObj, Vec_Int_t * vNodes, Vec_Int_t * vCos )
{
    Abc_Obj_t * pNext;
    int i;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    if ( Abc_ObjIsCo(pObj) )
    {
        Vec_IntPush( vCos, Abc_ObjId(pObj) );
        return;
    }
    assert( Abc_ObjIsNode(pObj) );
    Abc_ObjForEachFanout( pObj, pNext, i )
        Abc_SclFindTFO_rec( pNext, vNodes, vCos );
    if ( Abc_ObjFaninNum(pObj) > 0 )
        Vec_IntPush( vNodes, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclFindTFO( Abc_Ntk_t * p, Vec_Int_t * vPath )
{
    Vec_Int_t * vNodes, * vCos;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    assert( Vec_IntSize(vPath) > 0 );
    vCos = Vec_IntAlloc( 100 );
    vNodes = Vec_IntAlloc( 100 );
    // collect nodes in the TFO
    Abc_NtkIncrementTravId( p ); 
    Abc_NtkForEachObjVec( vPath, p, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( Abc_ObjIsNode(pFanin) )
                Abc_SclFindTFO_rec( pFanin, vNodes, vCos );
    // reverse order
    Vec_IntReverseOrder( vNodes );
//    Vec_IntSort( vNodes, 0 );
//Vec_IntPrint( vNodes );
//Vec_IntPrint( vCos );
    Vec_IntAppend( vNodes, vCos );
    Vec_IntFree( vCos );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collect near-critical COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindCriticalCoWindow( SC_Man * p, int Window )
{
    float fMaxArr = Abc_SclReadMaxDelay( p ) * (100.0 - Window) / 100.0;
    Vec_Int_t * vPivots;
    Abc_Obj_t * pObj;
    int i;
    vPivots = Vec_IntAlloc( 100 );
    Abc_NtkForEachCo( p->pNtk, pObj, i )
        if ( Abc_SclObjTimeMax(p, pObj) >= fMaxArr )
            Vec_IntPush( vPivots, Abc_ObjId(pObj) );
    assert( Vec_IntSize(vPivots) > 0 );
    return vPivots;
}

/**Function*************************************************************

  Synopsis    [Collect near-critical internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclFindCriticalNodeWindow_rec( SC_Man * p, Abc_Obj_t * pObj, Vec_Int_t * vPath, float fSlack, int fDept )
{
    Abc_Obj_t * pNext;
    float fArrMax, fSlackFan;
    int i;
    if ( Abc_ObjIsCi(pObj) )
        return;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    assert( Abc_ObjIsNode(pObj) );
    // compute the max arrival time of the fanins
    if ( fDept )
        fArrMax = p->pSlack[Abc_ObjId(pObj)];
    else
        fArrMax = Abc_SclGetMaxDelayNodeFanins( p, pObj );
    assert( fArrMax >= 0 );
    // traverse all fanins whose arrival times are within a window
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        if ( Abc_ObjIsCi(pNext) || Abc_ObjFaninNum(pNext) == 0 )
            continue;
        assert( Abc_ObjIsNode(pNext) );
        if ( fDept )
            fSlackFan = fSlack - (p->pSlack[Abc_ObjId(pNext)] - fArrMax);
        else
            fSlackFan = fSlack - (fArrMax - Abc_SclObjTimeMax(p, pNext));
        if ( fSlackFan >= 0 )
            Abc_SclFindCriticalNodeWindow_rec( p, pNext, vPath, fSlackFan, fDept );
    }
    if ( Abc_ObjFaninNum(pObj) > 0 )
        Vec_IntPush( vPath, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclFindCriticalNodeWindow( SC_Man * p, Vec_Int_t * vPathCos, int Window, int fDept )
{
    float fMaxArr = Abc_SclReadMaxDelay( p );
    float fSlackMax = fMaxArr * Window / 100.0;
    Vec_Int_t * vPath = Vec_IntAlloc( 100 );
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkIncrementTravId( p->pNtk ); 
    Abc_NtkForEachObjVec( vPathCos, p->pNtk, pObj, i )
    {
        float fSlackThis = fSlackMax - (fMaxArr - Abc_SclObjTimeMax(p, pObj));
        if ( fSlackThis >= 0 )
            Abc_SclFindCriticalNodeWindow_rec( p, Abc_ObjFanin0(pObj), vPath, fSlackThis, fDept );
    }
    // label critical nodes
    Abc_NtkForEachObjVec( vPathCos, p->pNtk, pObj, i )
        pObj->fMarkA = 1;
    Abc_NtkForEachObjVec( vPath, p->pNtk, pObj, i )
        pObj->fMarkA = 1;
    return vPath;  
}
void Abc_SclUnmarkCriticalNodeWindow( SC_Man * p, Vec_Int_t * vPath )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachObjVec( vPath, p->pNtk, pObj, i )
        pObj->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Find the array of nodes to be updated.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindNodesToUpdate( Abc_Obj_t * pPivot, Vec_Int_t ** pvEvals )
{
    Abc_Ntk_t * p = Abc_ObjNtk(pPivot);
    Abc_Obj_t * pObj, * pNext, * pNext2;
    Vec_Int_t * vNodes;
    int i, k;
    assert( Abc_ObjIsNode(pPivot) );
    assert( pPivot->fMarkA );
    // collect fanins, node, and fanouts
    vNodes = Vec_IntAlloc( 16 );
    Abc_ObjForEachFanin( pPivot, pNext, i )
        if ( Abc_ObjIsNode(pNext) && Abc_ObjFaninNum(pNext) > 0 )
            Vec_IntPush( vNodes, Abc_ObjId(pNext) );
    Vec_IntPush( vNodes, Abc_ObjId(pPivot) );
    Abc_ObjForEachFanout( pPivot, pNext, i )
        if ( Abc_ObjIsNode(pNext) && pNext->fMarkA )
        {
            Vec_IntPush( vNodes, Abc_ObjId(pNext) );
            Abc_ObjForEachFanout( pNext, pNext2, k )
                if ( Abc_ObjIsNode(pNext2) && pNext2->fMarkA )
                    Vec_IntPush( vNodes, Abc_ObjId(pNext2) );
        }
    Vec_IntUniqify( vNodes );
    // label nodes
    Abc_NtkForEachObjVec( vNodes, p, pObj, i )
    {
        assert( pObj->fMarkB == 0 );
        pObj->fMarkB = 1;
    }
    // collect nodes visible from the critical paths
    *pvEvals = Vec_IntAlloc( 10 );
    Abc_NtkForEachObjVec( vNodes, p, pObj, i )
        Abc_ObjForEachFanout( pObj, pNext, k )
            if ( pNext->fMarkA && !pNext->fMarkB )
//            if ( !pNext->fMarkB )
            {
                assert( pObj->fMarkB );
                Vec_IntPush( *pvEvals, Abc_ObjId(pObj) );
                break;
            }
    assert( Vec_IntSize(*pvEvals) > 0 );
    // label nodes
    Abc_NtkForEachObjVec( vNodes, p, pObj, i )
        pObj->fMarkB = 0;
    return vNodes;
}


/**Function*************************************************************

  Synopsis    [Computes the set of gates to upsize.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclFindUpsizes( SC_Man * p, Vec_Int_t * vPathNodes, int Ratio, int Notches, int iIter )
{
    SC_Cell * pCellOld, * pCellNew;
    Vec_Int_t * vRecalcs, * vEvals;
    Abc_Obj_t * pObj, * pTemp;
    float dGain, dGainBest;
    int i, k, n, gateBest, Limit, iIterLast;

    // compute savings due to upsizing each node
    Vec_QueClear( p->vNodeByGain );
    Abc_NtkForEachObjVec( vPathNodes, p->pNtk, pObj, i )
    {
        iIterLast = Vec_IntEntry(p->vNodeIter, Abc_ObjId(pObj));
        if ( iIterLast >= 0 && iIterLast + 10 > iIter )
            continue;
        // compute nodes to recalculate timing and nodes to evaluate afterwards
        vRecalcs = Abc_SclFindNodesToUpdate( pObj, &vEvals );
        assert( Vec_IntSize(vEvals) > 0 );
        //printf( "%d -> %d\n", Vec_IntSize(vRecalcs), Vec_IntSize(vEvals) );
        // save old gate, timing, fanin load
        pCellOld = Abc_SclObjCell( p, pObj );
        Abc_SclConeStore( p, vRecalcs );
        Abc_SclLoadStore( p, pObj );
        // try different gate sizes for this node
        gateBest = -1;
        dGainBest = 0.0;
        SC_RingForEachCell( pCellOld, pCellNew, k )
        {
            if ( pCellNew == pCellOld )
                continue;
            if ( k > Notches )
                break;
            // set new cell
            Abc_SclObjSetCell( p, pObj, pCellNew );
            Abc_SclUpdateLoad( p, pObj, pCellOld, pCellNew );
            // recompute timing
            Abc_SclTimeCone( p, vRecalcs );
            // set old cell
            Abc_SclObjSetCell( p, pObj, pCellOld );
            Abc_SclLoadRestore( p, pObj );
            // evaluate gain
            dGain = 0.0;
            Abc_NtkForEachObjVec( vEvals, p->pNtk, pTemp, n )
                dGain += Abc_SclObjGain( p, pTemp );
            dGain /= Vec_IntSize(vEvals);
            // save best gain
            if ( dGainBest < dGain )
            {
                dGainBest = dGain;
                gateBest = pCellNew->Id;
            }
        }
        // remember savings
        if ( gateBest >= 0 )
        {
            assert( dGainBest > 0.0 );
            Vec_FltWriteEntry( p->vNode2Gain, Abc_ObjId(pObj), dGainBest );
            Vec_IntWriteEntry( p->vNode2Gate, Abc_ObjId(pObj), gateBest );
            Vec_QuePush( p->vNodeByGain, Abc_ObjId(pObj) );
        }
        // put back old cell and timing
        Abc_SclObjSetCell( p, pObj, pCellOld );
        Abc_SclConeRestore( p, vRecalcs );
        // cleanup
        Vec_IntFree( vRecalcs );
        Vec_IntFree( vEvals );
    }
    if ( Vec_QueSize(p->vNodeByGain) < 3 )
        return 0;

    Limit = Abc_MinInt( Vec_QueSize(p->vNodeByGain), (int)(0.01 * Ratio * Vec_IntSize(vPathNodes)) + 1 ); 
//printf( "\nSelecting %d out of %d\n", Limit, Vec_QueSize(p->vNodeByGain) );
    for ( i = 0; i < Limit; i++ )
    {
        // get the object
        pObj = Abc_NtkObj( p->pNtk, Vec_QuePop(p->vNodeByGain) );
        assert( pObj->fMarkA );
        // find old and new gates
        pCellOld = Abc_SclObjCell( p, pObj );
        pCellNew = SC_LibCell( p->pLib, Vec_IntEntry(p->vNode2Gate, Abc_ObjId(pObj)) );
        assert( pCellNew != NULL );
//        printf( "%6d  %20s -> %20s  ", Abc_ObjId(pObj), pCellOld->pName, pCellNew->pName );
//        printf( "gain is %f\n", Vec_FltEntry(p->vNode2Gain, Abc_ObjId(pObj)) );
        // update gate
        Abc_SclUpdateLoad( p, pObj, pCellOld, pCellNew );
        p->SumArea += pCellNew->area - pCellOld->area;
        Abc_SclObjSetCell( p, pObj, pCellNew );
        // record the update
        Vec_IntPush( p->vUpdates, Abc_ObjId(pObj) );
        Vec_IntPush( p->vUpdates, pCellNew->Id );
        // remember when this node was upsized
        Vec_IntWriteEntry( p->vNodeIter, Abc_ObjId(pObj), iIter );
    }
    return Limit;
}
void Abc_SclApplyUpdateToBest( Vec_Int_t * vGates, Vec_Int_t * vGatesBest, Vec_Int_t * vUpdate )
{
    int i, ObjId, GateId, GateId2; 
    Vec_IntForEachEntryDouble( vUpdate, ObjId, GateId, i )
        Vec_IntWriteEntry( vGatesBest, ObjId, GateId );
    Vec_IntClear( vUpdate );
    Vec_IntForEachEntryTwo( vGates, vGatesBest, GateId, GateId2, i )
        assert( GateId == GateId2 );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePrintDiffs( SC_Man * p, SC_Lib * pLib, Abc_Ntk_t * pNtk )
{
    float fDiff = (float)0.001;
    int k;
    Abc_Obj_t * pObj;

    SC_Pair * pTimes = ABC_ALLOC( SC_Pair, p->nObjs );
    SC_Pair * pSlews = ABC_ALLOC( SC_Pair, p->nObjs );
    SC_Pair * pLoads = ABC_ALLOC( SC_Pair, p->nObjs );

    memcpy( pTimes, p->pTimes, sizeof(SC_Pair) * p->nObjs );
    memcpy( pSlews, p->pSlews, sizeof(SC_Pair) * p->nObjs );
    memcpy( pLoads, p->pLoads, sizeof(SC_Pair) * p->nObjs );

    Abc_SclTimeNtkRecompute( p, NULL, NULL, 0, 0 );

    Abc_NtkForEachNode( pNtk, pObj, k )
    {
        if ( Abc_AbsFloat(p->pLoads[k].rise - pLoads[k].rise) > fDiff )
            printf( "%6d : load rise differs %12.6f   %f %f\n", k, SC_LibCapFf(pLib, p->pLoads[k].rise)-SC_LibCapFf(pLib, pLoads[k].rise), SC_LibCapFf(pLib, p->pLoads[k].rise), SC_LibCapFf(pLib, pLoads[k].rise) );
        if ( Abc_AbsFloat(p->pLoads[k].fall - pLoads[k].fall) > fDiff )
            printf( "%6d : load fall differs %12.6f   %f %f\n", k, SC_LibCapFf(pLib, p->pLoads[k].fall)-SC_LibCapFf(pLib, pLoads[k].fall), SC_LibCapFf(pLib, p->pLoads[k].fall), SC_LibCapFf(pLib, pLoads[k].fall) );

        if ( Abc_AbsFloat(p->pSlews[k].rise - pSlews[k].rise) > fDiff )
            printf( "%6d : slew rise differs %12.6f   %f %f\n", k, SC_LibTimePs(pLib, p->pSlews[k].rise)-SC_LibTimePs(pLib, pSlews[k].rise), SC_LibTimePs(pLib, p->pSlews[k].rise), SC_LibTimePs(pLib, pSlews[k].rise) );
        if ( Abc_AbsFloat(p->pSlews[k].fall - pSlews[k].fall) > fDiff )
            printf( "%6d : slew fall differs %12.6f   %f %f\n", k, SC_LibTimePs(pLib, p->pSlews[k].fall)-SC_LibTimePs(pLib, pSlews[k].fall), SC_LibTimePs(pLib, p->pSlews[k].fall), SC_LibTimePs(pLib, pSlews[k].fall) );

        if ( Abc_AbsFloat(p->pTimes[k].rise - pTimes[k].rise) > fDiff )
            printf( "%6d : time rise differs %12.6f   %f %f\n", k, SC_LibTimePs(pLib, p->pTimes[k].rise)-SC_LibTimePs(pLib, pTimes[k].rise), SC_LibTimePs(pLib, p->pTimes[k].rise), SC_LibTimePs(pLib, pTimes[k].rise) );
        if ( Abc_AbsFloat(p->pTimes[k].fall - pTimes[k].fall) > fDiff )
            printf( "%6d : time fall differs %12.6f   %f %f\n", k, SC_LibTimePs(pLib, p->pTimes[k].fall)-SC_LibTimePs(pLib, pTimes[k].fall), SC_LibTimePs(pLib, p->pTimes[k].fall), SC_LibTimePs(pLib, pTimes[k].fall) );
    }

/*
if ( memcmp( pTimes, p->pTimes, sizeof(SC_Pair) * p->nObjs ) )
    printf( "Times differ!\n" );
if ( memcmp( pSlews, p->pSlews, sizeof(SC_Pair) * p->nObjs ) )
    printf( "Slews differ!\n" );
if ( memcmp( pLoads, p->pLoads, sizeof(SC_Pair) * p->nObjs ) )
    printf( "Loads differ!\n" );
*/

    ABC_FREE( pTimes );
    ABC_FREE( pSlews );
    ABC_FREE( pLoads );
}

/**Function*************************************************************

  Synopsis    [Print cumulative statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePrint( SC_Man * p, int Iter, int win, int nPathPos, int nPathNodes, int nUpsizes, int nTFOs, int fVerbose )
{
    printf( "%4d ",          Iter );
    printf( "Win:%3d. ",     win );
    printf( "PO:%5d. ",      nPathPos );
    printf( "Path:%6d. ",    nPathNodes );
    printf( "Gate:%5d. ",    nUpsizes );
    printf( "TFO:%6d. ",     nTFOs );
    printf( "A: " );
    printf( "%.2f ",         p->SumArea );
    printf( "(%+5.1f %%)  ",   100.0 * (p->SumArea - p->SumArea0)/ p->SumArea0 );
    printf( "D: " );
    printf( "%.2f ps ",      SC_LibTimePs(p->pLib, p->MaxDelay) );
    printf( "(%+5.1f %%)  ", 100.0 * (p->MaxDelay - p->MaxDelay0)/ p->MaxDelay0 );
    printf( "B: " );
    printf( "%.2f ps ",      SC_LibTimePs(p->pLib, p->BestDelay) );
    printf( "(%+5.1f %%)",   100.0 * (p->BestDelay - p->MaxDelay0)/ p->MaxDelay0 );
    printf( "%8.2f sec",     1.0*(Abc_Clock() - p->timeTotal)/(CLOCKS_PER_SEC) );
    printf( "%c", fVerbose ? '\n' : '\r' );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, SC_UpSizePars * pPars )
{
    SC_Man * p;
    Vec_Int_t * vPathPos = NULL;    // critical POs
    Vec_Int_t * vPathNodes = NULL;  // critical nodes and PIs
    Vec_Int_t * vTFO;
    abctime clk, nRuntimeLimit = pPars->TimeOut ? pPars->TimeOut * CLOCKS_PER_SEC + Abc_Clock() : 0;
    int i, win, nUpsizes = -1, nFramesNoChange = 0;
    int nAllPos, nAllNodes, nAllTfos, nAllUpsizes;

    if ( pPars->fVerbose )
    {
        printf( "Upsizing parameters: " );
        printf( "Iters =%5d.  ",          pPars->nIters   );
        printf( "Time window =%3d %%. ",  pPars->Window   );
        printf( "Update ratio =%3d %%. ", pPars->Ratio    );
        printf( "Max steps =%3d. ",       pPars->Notches  );
        printf( "UseDept =%2d. ",         pPars->fUseDept );
        printf( "Timeout =%4d sec",       pPars->TimeOut  );
        printf( "\n" );
    }

    // prepare the manager; collect init stats
    p = Abc_SclManStart( pLib, pNtk, 1, pPars->fUseDept, 0 );
    p->timeTotal  = Abc_Clock();
    assert( p->vGatesBest == NULL );
    p->vGatesBest = Vec_IntDup( p->vGates );
    p->BestDelay  = p->MaxDelay0;

    // perform upsizing
    nAllPos = nAllNodes = nAllTfos = nAllUpsizes = 0;
    for ( i = 0; i < pPars->nIters; i++ )
    {
        for ( win = pPars->Window; win <= 100;  win *= 2 )
        {
            // detect critical path
            clk = Abc_Clock();
            vPathPos   = Abc_SclFindCriticalCoWindow( p, win );
            vPathNodes = Abc_SclFindCriticalNodeWindow( p, vPathPos, win, pPars->fUseDept );
            p->timeCone += Abc_Clock() - clk;

            // selectively upsize the nodes
            clk = Abc_Clock();
            nUpsizes   = Abc_SclFindUpsizes( p, vPathNodes, pPars->Ratio, pPars->Notches, i );
            p->timeSize += Abc_Clock() - clk;

            // unmark critical path
            clk = Abc_Clock();
            Abc_SclUnmarkCriticalNodeWindow( p, vPathNodes );
            Abc_SclUnmarkCriticalNodeWindow( p, vPathPos );
            p->timeCone += Abc_Clock() - clk;
            if ( nUpsizes > 0 )
                break;
            Vec_IntFree( vPathPos );
            Vec_IntFree( vPathNodes );
        }
        if ( nUpsizes == 0 )
            break;

        // update timing information
        clk = Abc_Clock();
        if ( pPars->fUseDept )
        {
            vTFO = Vec_IntAlloc( 0 );
            Abc_SclTimeNtkRecompute( p, NULL, NULL, pPars->fUseDept, 0 );
        }
        else
        {
            vTFO = Abc_SclFindTFO( p->pNtk, vPathNodes );
            Abc_SclTimeCone( p, vTFO );
        }
        p->timeTime += Abc_Clock() - clk;
//        Abc_SclUpsizePrintDiffs( p, pLib, pNtk );

        // save the best network
        p->MaxDelay = Abc_SclReadMaxDelay( p );
        if ( p->BestDelay > p->MaxDelay )
        {
            p->BestDelay = p->MaxDelay;
            Abc_SclApplyUpdateToBest( p->vGates, p->vGatesBest, p->vUpdates );
            nFramesNoChange = 0;
        }
        else
            nFramesNoChange++;
        if ( nFramesNoChange > pPars->nIterNoChange )
        {
            Vec_IntFree( vPathPos );
            Vec_IntFree( vPathNodes );
            Vec_IntFree( vTFO );
            break;
        }

        // report and cleanup
        Abc_SclUpsizePrint( p, i, win, Vec_IntSize(vPathPos), Vec_IntSize(vPathNodes), nUpsizes, Vec_IntSize(vTFO), pPars->fVeryVerbose || (pPars->fVerbose && nFramesNoChange == 0) ); //|| (i == nIters-1) );
        nAllPos     += Vec_IntSize(vPathPos);
        nAllNodes   += Vec_IntSize(vPathNodes);
        nAllTfos    += Vec_IntSize(vTFO);
        nAllUpsizes += nUpsizes;
        Vec_IntFree( vPathPos );
        Vec_IntFree( vPathNodes );
        Vec_IntFree( vTFO );
        // check timeout
        if ( nRuntimeLimit && Abc_Clock() > nRuntimeLimit )
            break;
    }
    // update for best gates and recompute timing
    ABC_SWAP( Vec_Int_t *, p->vGatesBest, p->vGates );
    Abc_SclTimeNtkRecompute( p, &p->SumArea, &p->MaxDelay, 0, 0 );
    if ( pPars->fVerbose )
        Abc_SclUpsizePrint( p, i, pPars->Window, nAllPos/(i?i:1), nAllNodes/(i?i:1), nAllUpsizes/(i?i:1), nAllTfos/(i?i:1), 1 );
    else
        printf( "                                                                                                                                              \r" );
    // report runtime
    p->timeTotal = Abc_Clock() - p->timeTotal;
    if ( pPars->fVerbose )
    {
        p->timeOther = p->timeTotal - p->timeCone - p->timeSize - p->timeTime;
        ABC_PRTP( "Runtime: Critical path", p->timeCone,  p->timeTotal );
        ABC_PRTP( "Runtime: Sizing eval  ", p->timeSize,  p->timeTotal );
        ABC_PRTP( "Runtime: Timing update", p->timeTime,  p->timeTotal );
        ABC_PRTP( "Runtime: Other        ", p->timeOther, p->timeTotal );
        ABC_PRTP( "Runtime: TOTAL        ", p->timeTotal, p->timeTotal );
    }
    if ( pPars->fDumpStats )
        Abc_SclDumpStats( p, "stats2.txt", p->timeTotal );
    if ( nRuntimeLimit && Abc_Clock() > nRuntimeLimit )
        printf( "Gate sizing timed out at %d seconds.\n", pPars->TimeOut );

    // save the result and quit
    Abc_SclManSetGates( pLib, pNtk, p->vGates ); // updates gate pointers
    Abc_SclManFree( p );
//    Abc_NtkCleanMarkAB( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

