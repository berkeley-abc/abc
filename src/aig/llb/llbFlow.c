/**CFile****************************************************************

  FileName    [llbFlow.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [BDD based reachability.]

  Synopsis    [Flow computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: llbFlow.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "llbInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Llb_Flw_t_ Llb_Flw_t;
struct Llb_Flw_t_
{
    unsigned    Source  :    1;  // source of the graph
    unsigned    Sink    :    1;  // sink of the graph
    unsigned    Flow    :    1;  // node has flow
    unsigned    Mark    :    1;  // visited node
    unsigned    Id      :   14;  // ID of the corresponding node
    unsigned    nFanins :   14;  // number of fanins
    Llb_Flw_t * Fanins[0];       // fanins
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Llb_Flw_t * Llb_FlwAlloc( Vec_Int_t * vMem, Vec_Ptr_t * vStore, int Id, int nFanins )
{
    Llb_Flw_t * p;
    int nWords = (sizeof(Llb_Flw_t) + nFanins * sizeof(void *)) / sizeof(int);
    p = (Llb_Flw_t *)Vec_IntFetch( vMem, nWords );
    memset( p, 1, nWords * sizeof(int) );
    p->Id      = Id;
    p->nFanins = 0;//nFanins;
    Vec_PtrWriteEntry( vStore, Id, p );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_FlwAddFanin( Llb_Flw_t * pFrom, Llb_Flw_t * pTo )
{
    pFrom->Fanins[pFrom->nFanins++] = pTo;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_AigCreateFlw( Aig_Man_t * p, Vec_Int_t ** pvMem, Vec_Ptr_t ** pvTops, Vec_Ptr_t ** pvBots )
{
    Llb_Flw_t * pFlwTop, * pFlwBot;
    Vec_Ptr_t * vTops, * vBots;
    Vec_Int_t * vMem;
    Aig_Obj_t * pObj;
    int i;
    vMem  = Vec_IntAlloc( Aig_ManObjNumMax(p) * (sizeof(Llb_Flw_t) + sizeof(void *) * 8) );
    vBots = Vec_PtrStart( Aig_ManObjNumMax(p) );
    vTops = Vec_PtrStart( Aig_ManObjNumMax(p) );
    Aig_ManForEachObj( p, pObj, i )
    {
        pFlwBot = Llb_FlwAlloc( vMem, vBots, i, Aig_ObjIsPo(pObj) + 2 * Aig_ObjIsNode(pObj) );
        pFlwTop = Llb_FlwAlloc( vMem, vTops, i, Aig_ObjRefs(pObj) + 1 );
        Llb_FlwAddFanin( pFlwBot, pFlwTop );
        Llb_FlwAddFanin( pFlwTop, pFlwBot );
        Llb_FlwAddFanin( pFlwBot, (Llb_Flw_t *)Vec_PtrEntry(vTops, Aig_ObjFaninId0(pObj)) );
        Llb_FlwAddFanin( pFlwBot, (Llb_Flw_t *)Vec_PtrEntry(vTops, Aig_ObjFaninId1(pObj)) );
        Llb_FlwAddFanin( (Llb_Flw_t *)Vec_PtrEntry(vTops, Aig_ObjFaninId0(pObj)), pFlwBot );
        Llb_FlwAddFanin( (Llb_Flw_t *)Vec_PtrEntry(vTops, Aig_ObjFaninId1(pObj)), pFlwBot );
    }
    Aig_ManForEachObj( p, pObj, i )
    {
        pFlwBot = (Llb_Flw_t *)Vec_PtrEntry( vBots, i );
        pFlwTop = (Llb_Flw_t *)Vec_PtrEntry( vTops, i );
        assert( pFlwBot->nFanins == (unsigned)Aig_ObjIsPo(pObj) + 2 * Aig_ObjIsNode(pObj) );
        assert( pFlwTop->nFanins == (unsigned)Aig_ObjRefs(pObj) + 1 );
    }
    *pvMem  = vMem;
    *pvTops = vTops;
    *pvBots = vBots;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_AigCleanMarks( Vec_Ptr_t * vFlw )
{
    Llb_Flw_t * pFlw;
    int i;
    Vec_PtrForEachEntry( Llb_Flw_t *, vFlw, pFlw, i )
        pFlw->Mark = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_AigCleanFlow( Vec_Ptr_t * vFlw )
{
    Llb_Flw_t * pFlw;
    int i;
    Vec_PtrForEachEntry( Llb_Flw_t *, vFlw, pFlw, i )
        pFlw->Flow = 0;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Llb_AigCollectCut( Vec_Ptr_t * vNodes, Vec_Ptr_t * vBots, Vec_Ptr_t * vTops )
{
    Vec_Int_t * vCut;
    Llb_Flw_t * pFlwBot, * pFlwTop;
    Aig_Obj_t * pObj;
    int i;
    vCut = Vec_IntAlloc( 100 );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        pFlwBot = (Llb_Flw_t *)Vec_PtrEntry( vBots, i );
        pFlwTop = (Llb_Flw_t *)Vec_PtrEntry( vTops, i );
        if ( pFlwBot->Mark && !pFlwTop->Mark )
            Vec_IntPush( vCut, i );
    }
    return vCut;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_AigPushFlow_rec( Llb_Flw_t * pFlw, Llb_Flw_t * pFlwPrev, Vec_Ptr_t * vMarked, Vec_Ptr_t * vFlowed )
{
    int i;
    if ( pFlw->Mark )
        return 0;
    pFlw->Mark = 1;
    Vec_PtrPush( vMarked, pFlw );
    if ( pFlw->Source )
        return 0;
    if ( pFlw->Sink )
    {
        pFlw->Flow = 1;
        Vec_PtrPush( vFlowed, pFlw );
        return 1;
    }
//    assert( Aig_ObjIsNode(pObj) );
    for ( i = 0; i < (int)pFlw->nFanins; i++ )
    {
        if ( pFlw->Fanins[i] == pFlwPrev )
            continue;
        if ( Llb_AigPushFlow_rec( pFlw->Fanins[i], pFlw, vMarked, vFlowed ) )
            break;
    }
    if ( i == (int)pFlw->nFanins )
        return 0;
    if ( i == 0 )
    {
        pFlw->Flow = 1;
        Vec_PtrPush( vFlowed, pFlw );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_AigPushFlow( Vec_Ptr_t * vFlwBots, Vec_Ptr_t * vMarked, Vec_Ptr_t * vFlowed )
{
    Llb_Flw_t * pFlw;
    int i, Counter = 0;
    Vec_PtrForEachEntry( Llb_Flw_t *, vFlwBots, pFlw, i )
    {
        pFlw->Mark = 1;
        if ( Llb_AigPushFlow_rec( pFlw->Fanins[0], pFlw, vMarked, vFlowed ) )
        {
            Counter++;
            pFlw->Flow = 1;
            Vec_PtrPush( vFlowed, pFlw );
        }
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Llb_AigFindMinCut( Vec_Ptr_t * vNodes, Vec_Ptr_t * vFlwBots, Vec_Ptr_t * vFlwTop, Vec_Ptr_t * vFlwBots2, Vec_Ptr_t * vFlwTop2 )
{
    Vec_Int_t * vCut;
    Vec_Ptr_t * vMarked, * vFlowed;
    int Value;
    vMarked = Vec_PtrAlloc( 100 );
    vFlowed = Vec_PtrAlloc( 100 );
    Value = Llb_AigPushFlow( vFlwBots2, vMarked, vFlowed );
    Llb_AigCleanMarks( vMarked );
    Value = Llb_AigPushFlow( vFlwBots2, vMarked, vFlowed );
    assert( Value == 0 );
    vCut = Llb_AigCollectCut( vNodes, vFlwBots, vFlwTop );
    Llb_AigCleanMarks( vMarked );
    Llb_AigCleanFlow( vFlowed );
    return vCut;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_AigCollectFlowTerminals( Aig_Man_t * p, Vec_Ptr_t * vFlws, Vec_Int_t * vCut )
{
    Vec_Ptr_t * pFlwRes;
    Aig_Obj_t * pObj;
    int i;
    pFlwRes = Vec_PtrAlloc( Vec_IntSize(vCut) );
    Aig_ManForEachNodeVec( p, vCut, pObj, i )
        Vec_PtrPush( pFlwRes, Vec_PtrEntry( vFlws, Aig_ObjId(pObj) ) );
    return pFlwRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_AigMarkFlowTerminals( Vec_Ptr_t * vFlws, int fSource, int fSink )
{
    Llb_Flw_t * pFlw;
    int i;
    Vec_PtrForEachEntry( Llb_Flw_t *, vFlws, pFlw, i )
    {
        pFlw->Source = fSource;
        pFlw->Sink   = fSink;
    }
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_ManCollectNodes_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    assert( Aig_ObjIsNode(pObj) );
    Llb_ManCollectNodes_rec( p, Aig_ObjFanin0(pObj), vNodes );
    Llb_ManCollectNodes_rec( p, Aig_ObjFanin1(pObj), vNodes );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_ManCollectNodes( Aig_Man_t * p, Vec_Int_t * vCut1, Vec_Int_t * vCut2 )
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    Aig_ManIncrementTravId( p );
    Aig_ManForEachNodeVec( p, vCut1, pObj, i )
        Aig_ObjSetTravIdCurrent( p, pObj );
    vNodes = Vec_PtrAlloc( Aig_ManObjNumMax(p) );
    Aig_ManForEachNodeVec( p, vCut2, pObj, i )
        Llb_ManCollectNodes_rec( p, pObj, vNodes );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_ManCountNodes_rec( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Aig_ObjSetTravIdCurrent(p, pObj);
    assert( Aig_ObjIsNode(pObj) );
    return 1 + Llb_ManCountNodes_rec( p, Aig_ObjFanin0(pObj) ) +
               Llb_ManCountNodes_rec( p, Aig_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_ManCountNodes( Aig_Man_t * p, Vec_Int_t * vCut1, Vec_Int_t * vCut2 )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    Aig_ManIncrementTravId( p );
    Aig_ManForEachNodeVec( p, vCut1, pObj, i )
        Aig_ObjSetTravIdCurrent( p, pObj );
    Aig_ManForEachNodeVec( p, vCut2, pObj, i )
        Counter += Llb_ManCountNodes_rec( p, pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Computes starting cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Llb_ManComputeCioCut( Aig_Man_t * pAig, int fCollectCos )
{
    Vec_Int_t * vCut;
    Aig_Obj_t * pObj;
    int i;
    vCut = Vec_IntAlloc( 500 );
    if ( fCollectCos )
        Aig_ManForEachPo( pAig, pObj, i )
            Vec_IntPush( vCut, Aig_ObjId(pObj) );
    else
        Aig_ManForEachPi( pAig, pObj, i )
            Vec_IntPush( vCut, Aig_ObjId(pObj) );
    return vCut;
}

/**Function*************************************************************

  Synopsis    [Inserts the new cut into the array.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_ManCutInsert( Aig_Man_t * p, Vec_Ptr_t * vCuts, Vec_Int_t * vVols, int iEntry, Vec_Int_t * vCutNew )
{
    Vec_Int_t * vCut1, * vCut2; 
    int Vol1, Vol2;
    Vec_PtrInsert( vCuts, iEntry, vCutNew );
    Vec_IntInsert( vVols, iEntry, -1 );
    vCut1 = (Vec_Int_t *)Vec_PtrEntry( vCuts, iEntry );
    vCut2 = (Vec_Int_t *)Vec_PtrEntry( vCuts, iEntry+1 );
    Vol1  = Llb_ManCountNodes( p, vCut1, vCutNew );
    Vol2  = Llb_ManCountNodes( p, vCutNew, vCut2 );
    Vec_IntWriteEntry( vVols, iEntry-1, Vol1 );
    Vec_IntWriteEntry( vVols, iEntry,   Vol2 );
}

/**Function*************************************************************

  Synopsis    [Returns the set of cuts resulting from the flow computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_ManComputePartitioning( Aig_Man_t * p, int nVolumeMin, int nVolumeMax )
{ 
    Vec_Ptr_t * vCuts, * vFlwTops, * vFlwBots;
    Vec_Int_t * vVols, * vCut1, * vCut2, * vCut, * vMem; 
    int nMaxValue, iEntry;
    vCuts = Vec_PtrAlloc( 1000 );
    vVols = Vec_IntAlloc( 1000 );
    // prepare flow computation
    Llb_AigCreateFlw( p, &vMem, &vFlwTops, &vFlwBots );
    // start with regular cuts
    Vec_PtrPush( vCuts, Llb_ManComputeCioCut(p, 0) );
    Vec_PtrPush( vCuts, Llb_ManComputeCioCut(p, 1) );
    Vec_IntPush( vVols, Aig_ManNodeNum(p) );
    // split cuts with the largest volume
    while ( (nMaxValue = Vec_IntFindMax(vVols)) > nVolumeMax )
    {
        Vec_Ptr_t * vNodes, * vFlwBots2, * vFlwTops2; 
        iEntry = Vec_IntFind( vVols, nMaxValue );  assert( iEntry >= 0 );
        vCut1  = (Vec_Int_t *)Vec_PtrEntry( vCuts, iEntry );
        vCut2  = (Vec_Int_t *)Vec_PtrEntry( vCuts, iEntry+1 );
        // collect nodes
        vNodes = Llb_ManCollectNodes( p, vCut1, vCut1 );
        assert( Vec_PtrSize(vNodes) == nMaxValue );
        assert( Llb_ManCountNodes(p, vCut1, vCut2) == nMaxValue );
        // collect sources and sinks
        vFlwBots2 = Llb_AigCollectFlowTerminals( p, vFlwBots, vCut1 );
        vFlwTops2 = Llb_AigCollectFlowTerminals( p, vFlwTops, vCut2 );
        // mark sources and sinks
        Llb_AigMarkFlowTerminals( vFlwBots2, 1, 0 );
        Llb_AigMarkFlowTerminals( vFlwTops2, 0, 1 );
        vCut = Llb_AigFindMinCut( vNodes, vFlwBots, vFlwTops, vFlwBots2, vFlwTops2 );
        Llb_AigMarkFlowTerminals( vFlwBots2, 0, 0 );
        Llb_AigMarkFlowTerminals( vFlwTops2, 0, 0 );
        // insert new cut
        Llb_ManCutInsert( p, vCuts, vVols, iEntry+1, vCut );
        // deallocate
        Vec_PtrFree( vNodes );
        Vec_PtrFree( vFlwBots2 );
        Vec_PtrFree( vFlwTops2 );
    }
    Vec_IntFree( vMem );
    Vec_PtrFree( vFlwTops );
    Vec_PtrFree( vFlwBots );
    return vCuts;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Llb_ManMarkPivotNodesFlow( Aig_Man_t * p, Vec_Ptr_t * vCuts )
{
    Vec_Int_t * vVar2Obj, * vCut;
    Aig_Obj_t * pObj;
    int i, k;
    // mark inputs/outputs
    Aig_ManForEachPi( p, pObj, i )
        pObj->fMarkA = 1;
    Saig_ManForEachLi( p, pObj, i )
        pObj->fMarkA = 1;

    // mark internal pivot nodes
    Vec_PtrForEachEntry( Vec_Int_t *, vCuts, vCut, i )
        Aig_ManForEachNodeVec( p, vCut, pObj, k )
            pObj->fMarkA = 1;

    // assign variable numbers
    Aig_ManConst1(p)->fMarkA = 0;
    vVar2Obj = Vec_IntAlloc( 100 );
    Aig_ManForEachPi( p, pObj, i )
        Vec_IntPush( vVar2Obj, Aig_ObjId(pObj) );
    Aig_ManForEachNode( p, pObj, i )
        if ( pObj->fMarkA )
            Vec_IntPush( vVar2Obj, Aig_ObjId(pObj) );
    Saig_ManForEachLi( p, pObj, i )
        Vec_IntPush( vVar2Obj, Aig_ObjId(pObj) );
    return vVar2Obj;
}

/**Function*************************************************************

  Synopsis    [Returns the set of cuts resulting from the flow computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_ManPartitionUsingFlow( Llb_Man_t * p, Vec_Ptr_t * vCuts )
{ 
    Vec_Int_t * vCut1, * vCut2;
    int i;
    vCut1 = (Vec_Int_t *)Vec_PtrEntry( vCuts, 0 );
    Vec_PtrForEachEntryStart( Vec_Int_t *, vCuts, vCut1, i, 1 )
    {
        vCut2 = (Vec_Int_t *)Vec_PtrEntry( vCuts, i );
        Llb_ManGroupCreateFromCuts( p, vCut1, vCut2 );
        vCut1 = vCut2;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Llb_Man_t * Llb_ManStartFlow( Aig_Man_t * pAigGlo, Aig_Man_t * pAig, Gia_ParLlb_t * pPars )
{
    Vec_Ptr_t * vCuts;
    Llb_Man_t * p;
    vCuts = Llb_ManComputePartitioning( pAig, pPars->nVolumeMin, pPars->nVolumeMax );
    Aig_ManCleanMarkA( pAig );
    p = ABC_CALLOC( Llb_Man_t, 1 );
    p->pAigGlo  = pAigGlo;
    p->pPars    = pPars;
    p->pAig     = pAig;
    p->vVar2Obj = Llb_ManMarkPivotNodesFlow( p->pAig, vCuts );
    p->vObj2Var = Vec_IntInvert( p->vVar2Obj, -1 );
    Llb_ManPrepareVarMap( p );
    Aig_ManCleanMarkA( pAig );
    Llb_ManPartitionUsingFlow( p, vCuts );
    Vec_VecFreeP( (Vec_Vec_t **)&vCuts );
    return p;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

