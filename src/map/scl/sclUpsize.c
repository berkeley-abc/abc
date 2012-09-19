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

extern Vec_Int_t * Abc_SclFindCriticalCoWindow( SC_Man * p, int Window );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect TFO of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclFindTFO_rec( Abc_Obj_t * pObj, Vec_Int_t * vVisited )
{
    Abc_Obj_t * pNext;
    int i;
//    if ( Abc_ObjIsCo(pObj) )
//        return;
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return;
    Abc_NodeSetTravIdCurrent( pObj );
    Abc_ObjForEachFanout( pObj, pNext, i )
        Abc_SclFindTFO_rec( pNext, vVisited );
    Vec_IntPush( vVisited, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclFindTFO( Abc_Ntk_t * p, Vec_Int_t * vPath )
{
    Vec_Int_t * vVisited;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    assert( Vec_IntSize(vPath) > 0 );
    vVisited = Vec_IntAlloc( 100 );
    // collect nodes in the TFO
    Abc_NtkIncrementTravId( p ); 
    Abc_NtkForEachObjVec( vPath, p, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
            if ( Abc_ObjIsNode(pFanin) )
                Abc_SclFindTFO_rec( pFanin, vVisited );
    // reverse order
    Vec_IntReverseOrder( vVisited );
    return vVisited;
}

/**Function*************************************************************

  Synopsis    [Collect near-critical COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclFindCriticalCoWindow( SC_Man * p, int Window )
{
    float fMaxArr = Abc_SclGetMaxDelay( p ) * (100.0 - Window) / 100.0;
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
void Abc_SclFindCriticalNodeWindow_rec( SC_Man * p, Abc_Obj_t * pObj, Vec_Int_t * vPath, float fSlack )
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
    fArrMax = Abc_SclGetMaxDelayNodeFanins( p, pObj );
    // traverse all fanins whose arrival times are within a window
    Abc_ObjForEachFanin( pObj, pNext, i )
    {
        fSlackFan = fSlack - (fArrMax - Abc_SclObjTimeMax(p, pNext));
        if ( fSlackFan >= 0 )
            Abc_SclFindCriticalNodeWindow_rec( p, pNext, vPath, fSlackFan );
    }
    Vec_IntPush( vPath, Abc_ObjId(pObj) );
}
Vec_Int_t * Abc_SclFindCriticalNodeWindow( SC_Man * p, Vec_Int_t * vPathCos, int Window )
{
    float fMaxArr = Abc_SclGetMaxDelay( p );
    float fSlack = fMaxArr * Window / 100.0;
    Vec_Int_t * vPath = Vec_IntAlloc( 100 );
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkIncrementTravId( p->pNtk ); 
    Abc_NtkForEachObjVec( vPathCos, p->pNtk, pObj, i )
        Abc_SclFindCriticalNodeWindow_rec( p, Abc_ObjFanin0(pObj), vPath, fSlack - (fMaxArr - Abc_SclObjTimeMax(p, pObj)) );
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
        if ( Abc_ObjIsNode(pNext) )
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
    // collect nodes pointed to by non-labeled nodes
    *pvEvals = Vec_IntAlloc( 10 );
    Abc_NtkForEachObjVec( vNodes, p, pObj, i )
        Abc_ObjForEachFanout( pObj, pNext, k )
            if ( pNext->fMarkA && !pNext->fMarkB )
            {
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

  Synopsis    [Compute gain in changing the gate size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Abc_SclFindGain( SC_Man * p, Vec_Int_t * vCone, Vec_Int_t * vEvals )
{
    double dGain = 0;
    Abc_Obj_t * pObj;
    int i;
    Abc_SclConeStore( p, vCone );
    Abc_SclTimeCone( p, vCone );
    Abc_NtkForEachObjVec( vEvals, p->pNtk, pObj, i )
        dGain += Abc_SclObjGain( p, pObj );
    Abc_SclConeRestore( p, vCone );
    dGain /= Vec_IntSize(vEvals);
    return (float)dGain;
}

/**Function*************************************************************

  Synopsis    [Begin by upsizing gates will many fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_SclFindUpsizes( SC_Man * p, Vec_Int_t * vPathNodes, int Ratio )
{
    SC_Cell * pCellOld, * pCellNew;
    Vec_Flt_t * vSavings; // best gain for each node
    Vec_Int_t * vBests;   // best gate for each node
    Vec_Int_t * vCone, * vEvals, * vUpdates;
    Abc_Obj_t * pObj;
    float dGain, dGainBest = 0;
    int i, k, Entry, gateBest = -1;
    int nUpsizes = 0;

//    return nUpsizes;

    vSavings = Vec_FltAlloc( Vec_IntSize(vPathNodes) );
    vBests = Vec_IntAlloc( Vec_IntSize(vPathNodes) );
    Abc_NtkForEachObjVec( vPathNodes, p->pNtk, pObj, i )
    {
        dGainBest = 0;
        pCellOld  = Abc_SclObjCell( p, pObj );
        // try different gate sizes for this node
        vCone = Abc_SclFindNodesToUpdate( pObj, &vEvals );
        SC_RingForEachCell( pCellOld, pCellNew, k )
        {
            if ( pCellNew == pCellOld )
                continue;
            Abc_SclObjSetCell( p, pObj, pCellNew );
    //printf( "changing %s for %s at node %d   ", pCellOld->pName, pCellNew->pName, Abc_ObjId(pObj) );
            Abc_SclUpdateLoad( p, pObj, pCellOld, pCellNew );
            dGain = Abc_SclFindGain( p, vCone, vEvals );
            Abc_SclUpdateLoad( p, pObj, pCellNew, pCellOld );
    //printf( "gain is %f\n", dGain );
            if ( dGainBest < dGain )
            {
                dGainBest = dGain;
                gateBest = pCellNew->Id;
            }
        }
        assert( dGainBest >= 0.0 );
        Vec_IntFree( vCone );
        Vec_IntFree( vEvals );
        Abc_SclObjSetCell( p, pObj, pCellOld );
        Vec_FltPush( vSavings, dGainBest );
        Vec_IntPush( vBests, gateBest );
    }
    assert( Vec_IntSize(vBests) == Vec_IntSize(vPathNodes) );

    // we have computed the gains - find the best ones
    {
        Vec_Int_t * vCosts;
        float Max = Vec_FltFindMax( vSavings );
        float Factor = 1.0 * (1<<28) / Max, This;
        int i, Limit, * pPerm;
        // find a good factor
        vCosts = Vec_IntAlloc( Vec_FltSize(vSavings) );
        Vec_FltForEachEntry( vSavings, This, i )
        {
            Vec_IntPush( vCosts, (int)(This * Factor) );
            assert( (int)(This * Factor) < (1<<30) );
        }
        pPerm = Abc_QuickSortCost( Vec_IntArray(vCosts), Vec_IntSize(vCosts), 1 );
        assert( Vec_FltEntry(vSavings, pPerm[0]) >= Vec_FltEntry(vSavings, pPerm[Vec_FltSize(vSavings)-1]) );
        // find those that are good to update
        Limit = Abc_MaxInt( 1, (int)(0.01 * Ratio * Vec_IntSize(vBests)) ); 
        vUpdates = Vec_IntAlloc( Limit );
        for ( i = 0; i < Limit; i++ )
            if ( Vec_FltEntry(vSavings, pPerm[i]) > 0 )
                Vec_IntPush( vUpdates, pPerm[i] );
        Vec_IntFree( vCosts );
        ABC_FREE( pPerm );
    }

    // update the network
    Vec_IntForEachEntry( vUpdates, Entry, i )
    {
        // get the object
        pObj = Abc_NtkObj( p->pNtk, Vec_IntEntry(vPathNodes, Entry) );
        // find new gate
        pCellOld = Abc_SclObjCell( p, pObj );
        pCellNew = SC_LibCell( p->pLib, Vec_IntEntry(vBests, Entry) );
        assert( pCellNew != NULL );
        // update gate
        Abc_SclUpdateLoad( p, pObj, pCellOld, pCellNew );
        p->SumArea += pCellNew->area - pCellOld->area;
        Abc_SclObjSetCell( p, pObj, pCellNew );
        nUpsizes++;
    }

    Vec_IntFree( vUpdates );
    Vec_IntFree( vBests );
    Vec_FltFree( vSavings );
    return nUpsizes;
}


/**Function*************************************************************

  Synopsis    [Print cumulative statistics.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePrint( SC_Man * p, int Iter, Vec_Int_t * vPathPos, Vec_Int_t * vPathNodes, Vec_Int_t * vTFO, int nUpsizes )
{
    printf( "Iter %3d  ",     Iter );
    printf( "PO:%5d. ",       Vec_IntSize(vPathPos) );
    printf( "Node:%6d. ",     Vec_IntSize(vPathNodes) );
    printf( "TFO:%6d. ",      Vec_IntSize(vTFO) );
    printf( "Size:%5d. ",     nUpsizes );
    printf( "D: " );
    printf( "%.2f ps ",       SC_LibTimePs(p->pLib, p->MaxDelay) );
    printf( "(%+5.1f %%)  ",  100.0 * (p->MaxDelay - p->MaxDelay0)/ p->MaxDelay0 );
    printf( "A: " );
    printf( "%.2f ",          p->SumArea );
    printf( "(%+5.1f %%)  ",  100.0 * (p->SumArea - p->SumArea0)/ p->SumArea0 );
    Abc_PrintTime( 1, "Time", clock() - p->clkStart );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpsizePerform( SC_Lib * pLib, Abc_Ntk_t * pNtk, int Window, int Ratio, int nIters, int fVerbose )
{
    SC_Man * p;
    Vec_Int_t * vPathPos;    // critical POs
    Vec_Int_t * vPathNodes;  // critical nodes and PIs
    Vec_Int_t * vTFO;
    int i, nUpsizes = -1;

    // prepare the manager; collect init stats
    p = Abc_SclManStart( pLib, pNtk, 1 );

    // perform upsizing
    for ( i = 0; nUpsizes && i < nIters; i++ )
    {
        vPathPos   = Abc_SclFindCriticalCoWindow( p, Window );
        vPathNodes = Abc_SclFindCriticalNodeWindow( p, vPathPos, Window );
        nUpsizes   = Abc_SclFindUpsizes( p, vPathNodes, Ratio );
        Abc_SclUnmarkCriticalNodeWindow( p, vPathNodes );
        Abc_SclUnmarkCriticalNodeWindow( p, vPathPos );

        // update info
        vTFO = Abc_SclFindTFO( p->pNtk, vPathNodes );
//        Abc_SclTimeNtkRecompute( p, &p->SumArea, &p->MaxDelay );
        Abc_SclConeStore( p, vTFO );
        Abc_SclTimeCone( p, vTFO );
        p->MaxDelay = Abc_SclGetMaxDelay( p );

        Abc_SclUpsizePrint( p, i, vPathPos, vPathNodes, vTFO, nUpsizes );
        Vec_IntFree( vPathPos );
        Vec_IntFree( vPathNodes );
        Vec_IntFree( vTFO );

        if ( i && i % 50 == 0 )
            Abc_SclComputeLoad( p );
    }
//    Abc_NtkCleanMarkAB( pNtk );

    // save the result and quit
    Abc_SclManSetGates( pLib, pNtk, p->vGates ); // updates gate pointers
    Abc_SclManFree( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

