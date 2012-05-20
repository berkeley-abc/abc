/**CFile****************************************************************

  FileName    [ifUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifUtil.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets all the node copy to NULL.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManCleanNodeCopy( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    If_ManForEachObj( p, pObj, i )
        If_ObjSetCopy( pObj, NULL );
}

/**Function*************************************************************

  Synopsis    [Sets all the cut data to NULL.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManCleanCutData( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    If_ManForEachObj( p, pObj, i )
        If_CutSetData( If_ObjCutBest(pObj), NULL );
}

/**Function*************************************************************

  Synopsis    [Sets all visited marks to 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManCleanMarkV( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    If_ManForEachObj( p, pObj, i )
        pObj->fVisit = 0;
}

/**Function*************************************************************

  Synopsis    [Returns the max delay of the POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManDelayMax( If_Man_t * p, int fSeq )
{
    If_Obj_t * pObj;
    float DelayBest;
    int i;
    if ( p->pPars->fLatchPaths && (p->pPars->nLatchesCi == 0 || p->pPars->nLatchesCo == 0) )
    {
        Abc_Print( 0, "Delay optimization of latch path is not performed because there is no latches.\n" );
        p->pPars->fLatchPaths = 0;
    }
    DelayBest = -IF_FLOAT_LARGE;
    if ( fSeq )
    {
        assert( p->pPars->nLatchesCi > 0 );
        If_ManForEachPo( p, pObj, i )
            if ( DelayBest < If_ObjArrTime(If_ObjFanin0(pObj)) )
                 DelayBest = If_ObjArrTime(If_ObjFanin0(pObj));
    }
    else if ( p->pPars->fLatchPaths )
    {
        If_ManForEachLatchInput( p, pObj, i )
            if ( DelayBest < If_ObjArrTime(If_ObjFanin0(pObj)) )
                 DelayBest = If_ObjArrTime(If_ObjFanin0(pObj));
    }
    else 
    {
        If_ManForEachCo( p, pObj, i )
            if ( DelayBest < If_ObjArrTime(If_ObjFanin0(pObj)) )
                 DelayBest = If_ObjArrTime(If_ObjFanin0(pObj));
    }
    return DelayBest;
}

/**Function*************************************************************

  Synopsis    [Computes the required times of all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManComputeRequired( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i, Counter;
    float reqTime;

    // compute area, clean required times, collect nodes used in the mapping
//    p->AreaGlo = If_ManScanMapping( p );
    If_ManMarkMapping( p );

    if ( p->pManTim == NULL )
    {
        // consider the case when the required times are given
        if ( p->pPars->pTimesReq )
        {
            assert( !p->pPars->fAreaOnly );
            // make sure that the required time hold
            Counter = 0;
            If_ManForEachCo( p, pObj, i )
            {
                if ( If_ObjArrTime(If_ObjFanin0(pObj)) > p->pPars->pTimesReq[i] + p->fEpsilon )
                {
                    Counter++;
    //                Abc_Print( 0, "Required times are violated for output %d (arr = %d; req = %d).\n", 
    //                    i, (int)If_ObjArrTime(If_ObjFanin0(pObj)), (int)p->pPars->pTimesReq[i] );
                }
                If_ObjFanin0(pObj)->Required = p->pPars->pTimesReq[i];
            }
            if ( Counter )
                Abc_Print( 0, "Required times are violated for %d outputs.\n", Counter );
        }
        else
        {
            // get the global required times
            p->RequiredGlo = If_ManDelayMax( p, 0 );
/*
            ////////////////////////////////////////
            // redefine the delay target (positive number means percentage)    
            if ( p->pPars->DelayTarget > 0 )
                p->pPars->DelayTarget = p->RequiredGlo * (100.0 + p->pPars->DelayTarget) / 100.0; 
            ////////////////////////////////////////
*/
            // update the required times according to the target
            if ( p->pPars->DelayTarget != -1 )
            {
                if ( p->RequiredGlo > p->pPars->DelayTarget + p->fEpsilon )
                {
                    if ( p->fNextRound == 0 )
                    {
                        p->fNextRound = 1;
                        Abc_Print( 0, "Cannot meet the target required times (%4.2f). Mapping continues anyway.\n", p->pPars->DelayTarget );
                    }
                }
                else if ( p->RequiredGlo < p->pPars->DelayTarget - p->fEpsilon )
                {
                    if ( p->fNextRound == 0 )
                    {
                        p->fNextRound = 1;
//                        Abc_Print( 0, "Relaxing the required times from (%4.2f) to the target (%4.2f).\n", p->RequiredGlo, p->pPars->DelayTarget );
                    }
                    p->RequiredGlo = p->pPars->DelayTarget;
                }
            }
            // do not propagate required times if area minimization is requested
            if ( p->pPars->fAreaOnly ) 
                return;
            // set the required times for the POs
            if ( p->pPars->fLatchPaths )
            {
                If_ManForEachLatchInput( p, pObj, i )
                    If_ObjFanin0(pObj)->Required = p->RequiredGlo;
            }
            else 
            {
                If_ManForEachCo( p, pObj, i )
                    If_ObjFanin0(pObj)->Required = p->RequiredGlo;
            }
        }
        // go through the nodes in the reverse topological order
    //    Vec_PtrForEachEntry( If_Obj_t *, p->vMapped, pObj, i )
    //        If_CutPropagateRequired( p, pObj, If_ObjCutBest(pObj), pObj->Required );
        If_ManForEachObjReverse( p, pObj, i )
        {
            if ( pObj->nRefs == 0 )
                continue;
            If_CutPropagateRequired( p, pObj, If_ObjCutBest(pObj), pObj->Required );
        }
    }
    else
    {
        // get the global required times
        p->RequiredGlo = If_ManDelayMax( p, 0 );
        // update the required times according to the target
        if ( p->pPars->DelayTarget != -1 )
        {
            if ( p->RequiredGlo > p->pPars->DelayTarget + p->fEpsilon )
            {
                if ( p->fNextRound == 0 )
                {
                    p->fNextRound = 1;
                    Abc_Print( 0, "Cannot meet the target required times (%4.2f). Mapping continues anyway.\n", p->pPars->DelayTarget );
                }
            }
            else if ( p->RequiredGlo < p->pPars->DelayTarget - p->fEpsilon )
            {
                if ( p->fNextRound == 0 )
                {
                    p->fNextRound = 1;
//                    Abc_Print( 0, "Relaxing the required times from (%4.2f) to the target (%4.2f).\n", p->RequiredGlo, p->pPars->DelayTarget );
                }
                p->RequiredGlo = p->pPars->DelayTarget;
            }
        }
        // do not propagate required times if area minimization is requested
        if ( p->pPars->fAreaOnly ) 
            return;
        // set the required times for the POs
        Tim_ManIncrementTravId( p->pManTim );
        if ( p->vCoAttrs )
        {
            assert( If_ManCoNum(p) == Vec_IntSize(p->vCoAttrs) );
            If_ManForEachCo( p, pObj, i )
            { 
                if ( Vec_IntEntry(p->vCoAttrs, i) == -1 )       // -1=internal
                    continue;
                if ( Vec_IntEntry(p->vCoAttrs, i) == 0 )        //  0=optimize
                    Tim_ManSetCoRequired( p->pManTim, i, p->RequiredGlo );
                else if ( Vec_IntEntry(p->vCoAttrs, i) == 1 )   //  1=keep
                    Tim_ManSetCoRequired( p->pManTim, i, If_ObjArrTime(If_ObjFanin0(pObj)) );
                else if ( Vec_IntEntry(p->vCoAttrs, i) == 2 )   //  2=relax
                    Tim_ManSetCoRequired( p->pManTim, i, IF_FLOAT_LARGE );
                else assert( 0 );
            }
        }
        else if ( p->pPars->fLatchPaths )
        {
            If_ManForEachPo( p, pObj, i )
                Tim_ManSetCoRequired( p->pManTim, i, IF_FLOAT_LARGE );
            If_ManForEachLatchInput( p, pObj, i )
                Tim_ManSetCoRequired( p->pManTim, i, p->RequiredGlo );
        }
        else  
        {
            Tim_ManSetCoRequiredAll( p->pManTim, p->RequiredGlo );
//            If_ManForEachCo( p, pObj, i )
//                Tim_ManSetCoRequired( p->pManTim, pObj->IdPio, p->RequiredGlo );
        }
        // go through the nodes in the reverse topological order
        If_ManForEachObjReverse( p, pObj, i )
        {
            if ( If_ObjIsAnd(pObj) )
            {
                if ( pObj->nRefs == 0 )
                    continue;
                If_CutPropagateRequired( p, pObj, If_ObjCutBest(pObj), pObj->Required );
            }
            else if ( If_ObjIsCi(pObj) )
            {
                reqTime = pObj->Required;
                Tim_ManSetCiRequired( p->pManTim, pObj->IdPio, reqTime );
            }
            else if ( If_ObjIsCo(pObj) )
            {
                reqTime = Tim_ManGetCoRequired( p->pManTim, pObj->IdPio );
                If_ObjFanin0(pObj)->Required = IF_MIN( reqTime, If_ObjFanin0(pObj)->Required );
            }
            else if ( If_ObjIsConst1(pObj) )
            {
            }
            else // add the node to the mapper
                assert( 0 );
        }
    }
}
 
#if 0

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMapping_rec( If_Man_t * p, If_Obj_t * pObj, If_Obj_t ** ppStore )
{
    If_Obj_t * pLeaf;
    If_Cut_t * pCutBest;
    float aArea;
    int i;
    if ( pObj->nRefs++ || If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) )
        return 0.0;
    // store the node in the structure by level
    assert( If_ObjIsAnd(pObj) );
    pObj->pCopy = (char *)ppStore[pObj->Level]; 
    ppStore[pObj->Level] = pObj;
    // visit the transitive fanin of the selected cut
    pCutBest = If_ObjCutBest(pObj);
    p->nNets += pCutBest->nLeaves;
    aArea = If_CutLutArea( p, pCutBest );
    If_CutForEachLeaf( p, pCutBest, pLeaf, i )
        aArea += If_ManScanMapping_rec( p, pLeaf, ppStore );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description [Collects the nodes in reverse topological order in array 
  p->vMapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMapping( If_Man_t * p )
{
    If_Obj_t * pObj, ** ppStore;
    float aArea;
    int i;
    assert( !p->pPars->fLiftLeaves );
    // clean all references
    p->nNets = 0;
    If_ManForEachObj( p, pObj, i )
    {
        pObj->Required = IF_FLOAT_LARGE;
        pObj->nVisits  = pObj->nVisitsCopy;
        pObj->nRefs    = 0;
    }
    // allocate place to store the nodes
    ppStore = ABC_ALLOC( If_Obj_t *, p->nLevelMax + 1 );
    memset( ppStore, 0, sizeof(If_Obj_t *) * (p->nLevelMax + 1) );
    // collect nodes reachable from POs in the DFS order through the best cuts
    aArea = 0;
    If_ManForEachCo( p, pObj, i )
        aArea += If_ManScanMapping_rec( p, If_ObjFanin0(pObj), ppStore );
    // reconnect the nodes in reverse topological order
    Vec_PtrClear( p->vMapped );
    for ( i = p->nLevelMax; i >= 0; i-- )
        for ( pObj = ppStore[i]; pObj; pObj = pObj->pCopy )
            Vec_PtrPush( p->vMapped, pObj );
    ABC_FREE( ppStore );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description [Collects the nodes in reverse topological order in array 
  p->vMapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMappingDirect( If_Man_t * p )
{
    If_Obj_t * pObj, ** ppStore;
    float aArea;
    int i;
    assert( !p->pPars->fLiftLeaves );
    // clean all references
    If_ManForEachObj( p, pObj, i )
    {
        pObj->Required = IF_FLOAT_LARGE;
        pObj->nVisits  = pObj->nVisitsCopy;
        pObj->nRefs    = 0;
    }
    // allocate place to store the nodes
    ppStore = ABC_ALLOC( If_Obj_t *, p->nLevelMax + 1 );
    memset( ppStore, 0, sizeof(If_Obj_t *) * (p->nLevelMax + 1) );
    // collect nodes reachable from POs in the DFS order through the best cuts
    aArea = 0;
    If_ManForEachCo( p, pObj, i )
        aArea += If_ManScanMapping_rec( p, If_ObjFanin0(pObj), ppStore );
    // reconnect the nodes in reverse topological order
    Vec_PtrClear( p->vMapped );
//    for ( i = p->nLevelMax; i >= 0; i-- )
    for ( i = 0; i <= p->nLevelMax; i++ )
        for ( pObj = ppStore[i]; pObj; pObj = pObj->pCopy )
            Vec_PtrPush( p->vMapped, pObj );
    ABC_FREE( ppStore );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMappingSeq_rec( If_Man_t * p, If_Obj_t * pObj, Vec_Ptr_t * vMapped )
{
    If_Obj_t * pLeaf;
    If_Cut_t * pCutBest;
    float aArea;
    int i, Shift;
    // treat latches transparently
    if ( If_ObjIsLatch(pObj) )
        return If_ManScanMappingSeq_rec( p, If_ObjFanin0(pObj), vMapped );
    // consider trivial cases
    if ( pObj->nRefs++ || If_ObjIsPi(pObj) || If_ObjIsConst1(pObj) )
        return 0.0;
    // store the node in the structure by level
    assert( If_ObjIsAnd(pObj) );
    // visit the transitive fanin of the selected cut
    pCutBest = If_ObjCutBest(pObj);
    aArea = If_ObjIsAnd(pObj)? If_CutLutArea(p, pCutBest) : (float)0.0;
    If_CutForEachLeafSeq( p, pCutBest, pLeaf, Shift, i )
        aArea += If_ManScanMappingSeq_rec( p, pLeaf, vMapped );
    // add the node
    Vec_PtrPush( vMapped, pObj );
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description [Collects the nodes in reverse topological order in array 
  p->vMapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManScanMappingSeq( If_Man_t * p )
{
    If_Obj_t * pObj;
    float aArea;
    int i;
    assert( p->pPars->fLiftLeaves );
    // clean all references
    If_ManForEachObj( p, pObj, i )
        pObj->nRefs = 0;
    // collect nodes reachable from POs in the DFS order through the best cuts
    aArea = 0;
    Vec_PtrClear( p->vMapped );
    If_ManForEachPo( p, pObj, i )
        aArea += If_ManScanMappingSeq_rec( p, If_ObjFanin0(pObj), p->vMapped );
    return aArea;
}

#endif

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description [Collects the nodes in reverse topological order in array 
  p->vMapping.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManResetOriginalRefs( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    If_ManForEachObj( p, pObj, i )
        pObj->nRefs = 0;
    If_ManForEachObj( p, pObj, i )
    {
        if ( If_ObjIsAnd(pObj) )
        {
            pObj->pFanin0->nRefs++;
            pObj->pFanin1->nRefs++;
        }
        else if ( If_ObjIsCo(pObj) )
            pObj->pFanin0->nRefs++;
    }
}

/**Function*************************************************************

  Synopsis    [Computes cross-cut of the circuit.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManCrossCut( If_Man_t * p )
{
    If_Obj_t * pObj, * pFanin;
    int i, nCutSize = 0, nCutSizeMax = 0;
    If_ManForEachObj( p, pObj, i )
    {
        if ( !If_ObjIsAnd(pObj) )
            continue;
        // consider the node
        if ( nCutSizeMax < ++nCutSize )
            nCutSizeMax = nCutSize;
        if ( pObj->nVisits == 0 )
            nCutSize--;
        // consider the fanins
        pFanin = If_ObjFanin0(pObj);
        if ( !If_ObjIsCi(pFanin) && --pFanin->nVisits == 0 )
            nCutSize--;
        pFanin = If_ObjFanin1(pObj);
        if ( !If_ObjIsCi(pFanin) && --pFanin->nVisits == 0 )
            nCutSize--;
        // consider the choice class
        if ( pObj->fRepr )
            for ( pFanin = pObj; pFanin; pFanin = pFanin->pEquiv )
                if ( !If_ObjIsCi(pFanin) && --pFanin->nVisits == 0 )
                    nCutSize--;
    }
    If_ManForEachObj( p, pObj, i )
    {
        assert( If_ObjIsCi(pObj) || pObj->fVisit == 0 );
        pObj->nVisits = pObj->nVisitsCopy;
    }
    assert( nCutSize == 0 );
//    Abc_Print( 1, "Max cross cut size = %6d.\n", nCutSizeMax );
    return nCutSizeMax;
}

/**Function*************************************************************

  Synopsis    [Computes the reverse topological order of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * If_ManReverseOrder( If_Man_t * p )
{
    Vec_Ptr_t * vOrder;
    If_Obj_t * pObj, ** ppStore;
    int i;
    // allocate place to store the nodes
    ppStore = ABC_ALLOC( If_Obj_t *, p->nLevelMax + 1 );
    memset( ppStore, 0, sizeof(If_Obj_t *) * (p->nLevelMax + 1) );
    // add the nodes
    If_ManForEachObj( p, pObj, i )
    {
        assert( pObj->Level >= 0 && pObj->Level <= (unsigned)p->nLevelMax );
        pObj->pCopy = (char *)ppStore[pObj->Level]; 
        ppStore[pObj->Level] = pObj;
    }
    vOrder = Vec_PtrAlloc( If_ManObjNum(p) );
    for ( i = p->nLevelMax; i >= 0; i-- )
        for ( pObj = ppStore[i]; pObj; pObj = (If_Obj_t *)pObj->pCopy )
            Vec_PtrPush( vOrder, pObj );
    ABC_FREE( ppStore );
    // print the order
//    Vec_PtrForEachEntry( If_Obj_t *, vOrder, pObj, i )
//        Abc_Print( 1, "Obj %2d   Type %d  Level = %d\n", pObj->Id, pObj->Type, pObj->Level );
    return vOrder;
}
 
/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_ManMarkMapping_rec( If_Man_t * p, If_Obj_t * pObj )
{
    If_Obj_t * pLeaf;
    If_Cut_t * pCutBest;
    float * pSwitching = p->vSwitching? (float*)p->vSwitching->pArray : NULL;
    float aArea;
    int i;
    if ( pObj->nRefs++ || If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) )
        return 0.0;
    // store the node in the structure by level
    assert( If_ObjIsAnd(pObj) );
    // visit the transitive fanin of the selected cut
    pCutBest = If_ObjCutBest(pObj);
    p->nNets += pCutBest->nLeaves;
    aArea = If_CutLutArea( p, pCutBest );
    If_CutForEachLeaf( p, pCutBest, pLeaf, i )
    {
        p->dPower += pSwitching? pSwitching[pLeaf->Id] : 0.0;
        aArea += If_ManMarkMapping_rec( p, pLeaf );
    }
    return aArea;
}

/**Function*************************************************************

  Synopsis    [Computes area, references, and nodes used in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ManMarkMapping( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    If_ManForEachObj( p, pObj, i )
    {
        pObj->Required = IF_FLOAT_LARGE;
        pObj->nVisits = pObj->nVisitsCopy;
        pObj->nRefs = 0;
    }
    p->nNets = 0;
    p->dPower = 0.0;
    p->AreaGlo = 0.0;
    If_ManForEachCo( p, pObj, i )
        p->AreaGlo += If_ManMarkMapping_rec( p, If_ObjFanin0(pObj) );
}

/**Function*************************************************************

  Synopsis    [Collects nodes used in the mapping in the topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * If_ManCollectMappingDirect( If_Man_t * p )
{
    Vec_Ptr_t * vOrder;
    If_Obj_t * pObj;
    int i;
    If_ManMarkMapping( p );
    vOrder = Vec_PtrAlloc( If_ManObjNum(p) );
    If_ManForEachObj( p, pObj, i )
        if ( If_ObjIsAnd(pObj) && pObj->nRefs )
            Vec_PtrPush( vOrder, pObj );
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Collects nodes used in the mapping in the topological order.]

  Description [Represents mapping as an array of integers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * If_ManCollectMappingInt( If_Man_t * p )
{
    Vec_Int_t * vOrder;
    If_Cut_t * pCutBest;
    If_Obj_t * pObj;
    int i, k, nLeaves, * ppLeaves;
    If_ManMarkMapping( p );
    vOrder = Vec_IntAlloc( If_ManObjNum(p) );
    If_ManForEachObj( p, pObj, i )
        if ( If_ObjIsAnd(pObj) && pObj->nRefs )
        {
            pCutBest = If_ObjCutBest( pObj );
            nLeaves  = If_CutLeaveNum( pCutBest ); 
            ppLeaves = If_CutLeaves( pCutBest );
            // save the number of leaves, the leaves, and finally, the root
            Vec_IntPush( vOrder, nLeaves );
            for ( k = 0; k < nLeaves; k++ )
                Vec_IntPush( vOrder, ppLeaves[k] );
            Vec_IntPush( vOrder, pObj->Id );
        }
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Returns the number of POs pointing to the same internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManCountSpecialPos( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i, Counter = 0;
    // clean all marks
    If_ManForEachPo( p, pObj, i )
        If_ObjFanin0(pObj)->fMark = 0;
    // label nodes 
    If_ManForEachPo( p, pObj, i )
        if ( !If_ObjFaninC0(pObj) )
            If_ObjFanin0(pObj)->fMark = 1;
    // label nodes 
    If_ManForEachPo( p, pObj, i )
        if ( If_ObjFaninC0(pObj) )
            Counter += If_ObjFanin0(pObj)->fMark;
    // clean all marks
    If_ManForEachPo( p, pObj, i )
        If_ObjFanin0(pObj)->fMark = 0;
    return Counter;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

