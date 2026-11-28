/**CFile****************************************************************

  FileName    [paResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Placement-aware resubstitution.]

  Author      [Anqi Lu, from abcResub.c by Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paResub.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"
#include <math.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Fixed resubstitution parameters: cuts of up to 8 leaves, up to two new nodes.
#define PA_RS_CUT_MAX 8

#define PA_RS_DIV1_MAX 150 // the max number of divisors to consider
#define PA_RS_DIV2_MAX 500 // the max number of pair-wise divisors to consider

typedef struct Pa_ManRes_t_ Pa_ManRes_t;
struct Pa_ManRes_t_
{
    // Every truth-valid candidate is ranked by the placement evaluator.
    int nPaRequired;       // required level of the root
    int nPaGain;           // node gain of the best candidate
    double dPaScore;       // score of the best candidate
    Dec_Graph_t * pPaBest; // the best candidate
    Vec_Ptr_t * vPaLeaves; // candidate divisor boundary
    int fLazyPairs;        // two-node candidates only when no one-node candidate gains
    // paramers
    int nLeavesMax; // the max number of leaves in the cone
    int nDivsMax;   // the max number of divisors in the cone
    // representation of the cone
    Abc_Obj_t * pRoot; // the root of the cone
    int nLeaves;       // the number of leaves
    int nDivs;         // the number of all divisor (including leaves)
    int nMffc;         // the size of MFFC
    int nLastGain;     // the gain the number of nodes
    Vec_Ptr_t * vDivs; // the divisors
    // representation of the simulation info
    int nBits;         // the number of simulation bits
    int nWords;        // the number of unsigneds for siminfo
    Vec_Ptr_t * vSims; // simulation info
    unsigned * pInfo;  // pointer to simulation info
    // observability don't-cares
    unsigned * pCareSet;
    // internal divisor storage
    Vec_Ptr_t * vDivs1UP;  // the single-node unate divisors
    Vec_Ptr_t * vDivs1UN;  // the single-node unate divisors
    Vec_Ptr_t * vDivs1B;   // the single-node binate divisors
    Vec_Ptr_t * vDivs2UP0; // the double-node unate divisors
    Vec_Ptr_t * vDivs2UP1; // the double-node unate divisors
    Vec_Ptr_t * vDivs2UN0; // the double-node unate divisors
    Vec_Ptr_t * vDivs2UN1; // the double-node unate divisors
    // other data
    Vec_Ptr_t * vTemp; // temporary array of nodes
};

// external procedures
static Pa_ManRes_t * Pa_ManResubStart( int nLeavesMax, int nDivsMax );
static void Pa_ManResubStop( Pa_ManRes_t * p );
static Dec_Graph_t * Pa_ManResubEval( Pa_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves );

// other procedures
static int Pa_ManResubCollectDivs( Pa_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int Required );
static void Pa_ManResubSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords );

static void Pa_ManResubDivsS( Pa_ManRes_t * p, int Required );
static void Pa_ManResubDivsD( Pa_ManRes_t * p, int Required );
static Dec_Graph_t * Pa_ManResubQuit( Pa_ManRes_t * p );
static void Pa_ManResubDivs0( Pa_ManRes_t * p );
static void Pa_ManResubDivs1( Pa_ManRes_t * p, int Required );
static void Pa_ManResubDivs12( Pa_ManRes_t * p, int Required );
static void Pa_ManResubDivs2( Pa_ManRes_t * p, int Required );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Placement-aware resubstitution.]

  Description [Cuts of up to 8 leaves, up to two new nodes, level update.
               Divisors may lie beyond the traversal frontier, so timing is
               exact.]

***********************************************************************/
static int Pa_NtkResubstituteInt( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds, int fLazyPairs )
{
    Pa_ManRes_t * pManRes;
    Abc_ManCut_t * pManCut;
    Dec_Graph_t * pFForm;
    Vec_Ptr_t * vLeaves;
    Abc_Obj_t * pNode;
    int i, nNodes, RetValue = 1;

    assert( Abc_NtkIsStrash( pNtk ) );
    if ( !Pa_ManHasPlacement( pNtk ) )
        return -1;
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    if ( !Pa_ManBeginPass( pNtk ) )
        return -1;
    if ( !Pa_ManPrepareTimingPass( pNtk ) )
    {
        Pa_ManEndPass( pNtk );
        return -1;
    }
    pManCut = Abc_NtkManCutStart( PA_RS_CUT_MAX, 100000, 100000, 100000 );
    pManRes = Pa_ManResubStart( PA_RS_CUT_MAX, PA_RS_DIV1_MAX );
    pManRes->fLazyPairs = fLazyPairs;
    Abc_NtkStartReverseLevels( pNtk, 0 );

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax( pNtk );
    Abc_NtkCleanMarkAB( pNtk );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( Abc_NodeIsPersistant( pNode ) || Abc_ObjFanoutNum( pNode ) > 1000 )
            continue;
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        if ( pFilter && !pFilter->fVisit( pFilter->pData, pNode ) )
            continue;
        vLeaves = Abc_NodeFindCut( pManCut, pNode, 0 );
        pFForm = Pa_ManResubEval( pManRes, pNode, vLeaves );
        if ( pFilter && pFilter->fDone )
            pFilter->fDone( pFilter->pData, pNode, pFForm != NULL && pManRes->nLastGain >= 0 );
        if ( pFForm == NULL )
            continue;
        if ( pManRes->nLastGain < 0 )
        {
            Dec_GraphFree( pFForm );
            continue;
        }
        {
            int j;
            Dec_Node_t * pDec;
            Vec_PtrClear( pManRes->vPaLeaves );
            Dec_GraphForEachLeaf( pFForm, pDec, j )
                Vec_PtrPushUnique( pManRes->vPaLeaves, Abc_ObjRegular( (Abc_Obj_t *)pDec->pFunc ) );
            if ( !Pa_ManCommitCandidate( pNode, pFForm, pManRes->vPaLeaves, 1, pManRes->nLastGain ) )
            {
                Dec_GraphFree( pFForm );
                RetValue = -1;
                break;
            }
        }
        Dec_GraphFree( pFForm );
    }
    Pa_ManResubStop( pManRes );
    Abc_NtkManCutStop( pManCut );
    // clean the data field
    Abc_NtkForEachObj( pNtk, pNode, i ) pNode->pData = NULL;

    if ( RetValue >= 0 && !Pa_ManBeginEdit( pNtk ) )
        RetValue = -1;
    if ( fReassignIds )
        Abc_NtkReassignIds( pNtk );
    if ( RetValue >= 0 && !Pa_ManFinishEdit( pNtk ) )
        RetValue = -1;
    if ( RetValue >= 0 && !Pa_ManEndPass( pNtk ) )
        RetValue = -1;
    if ( RetValue < 0 )
        Pa_ManClearPlacement();
    Abc_NtkStopReverseLevels( pNtk );
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Pa_NtkResubstitute: The network check has failed.\n" );
        return 0;
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Placement-aware resubstitution with exact timing.]

  Description [Cuts of up to 8 leaves, at most two added nodes, level
               update. fReassignIds puts the nodes into DFS order at the
               end. fLazyPairs tries two-node candidates only for MFFCs of
               three or more nodes without a gaining one-node candidate.
               Returns 1 on success, 0 if the network check fails and -1 if
               the placement could not be maintained.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_NtkResubstitute( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds, int fLazyPairs )
{
    int RetValue;
    Pa_ManSetExactTiming( 1 );
    RetValue = Pa_NtkResubstituteInt( pNtk, pFilter, fReassignIds, fLazyPairs );
    Pa_ManSetExactTiming( 0 );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Pa_ManRes_t * Pa_ManResubStart( int nLeavesMax, int nDivsMax )
{
    Pa_ManRes_t * p;
    unsigned * pData;
    int i, k;
    assert( sizeof( unsigned ) == 4 );
    p = ABC_ALLOC( Pa_ManRes_t, 1 );
    memset( p, 0, sizeof( Pa_ManRes_t ) );
    p->nLeavesMax = nLeavesMax;
    p->nDivsMax = nDivsMax;
    p->vDivs = Vec_PtrAlloc( p->nDivsMax );
    // allocate simulation info
    p->nBits = ( 1 << p->nLeavesMax );
    p->nWords = ( p->nBits <= 32 ) ? 1 : ( p->nBits / 32 );
    p->pInfo = ABC_ALLOC( unsigned, p->nWords *( p->nDivsMax + 1 ) );
    memset( p->pInfo, 0, sizeof( unsigned ) * p->nWords * p->nLeavesMax );
    p->vSims = Vec_PtrAlloc( p->nDivsMax );
    for ( i = 0; i < p->nDivsMax; i++ )
        Vec_PtrPush( p->vSims, p->pInfo + i * p->nWords );
    // assign the care set
    p->pCareSet = p->pInfo + p->nDivsMax * p->nWords;
    Abc_InfoFill( p->pCareSet, p->nWords );
    // set elementary truth tables
    for ( k = 0; k < p->nLeavesMax; k++ )
    {
        pData = (unsigned *)p->vSims->pArray[k];
        for ( i = 0; i < p->nBits; i++ )
            if ( i & ( 1 << k ) )
                pData[i >> 5] |= ( 1u << ( i & 31 ) );
    }
    // create the remaining divisors
    p->vDivs1UP = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1UN = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1B = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UP0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UP1 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UN0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UN1 = Vec_PtrAlloc( p->nDivsMax );
    p->vTemp = Vec_PtrAlloc( p->nDivsMax );
    p->vPaLeaves = Vec_PtrAlloc( 4 );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubStop( Pa_ManRes_t * p )
{
    Vec_PtrFree( p->vDivs );
    Vec_PtrFree( p->vSims );
    Vec_PtrFree( p->vDivs1UP );
    Vec_PtrFree( p->vDivs1UN );
    Vec_PtrFree( p->vDivs1B );
    Vec_PtrFree( p->vDivs2UP0 );
    Vec_PtrFree( p->vDivs2UP1 );
    Vec_PtrFree( p->vDivs2UN0 );
    Vec_PtrFree( p->vDivs2UN1 );
    Vec_PtrFree( p->vTemp );
    Vec_PtrFree( p->vPaLeaves );
    if ( p->pPaBest )
        Dec_GraphFree( p->pPaBest );
    ABC_FREE( p->pInfo );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubCollectDivs_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vInternal )
{
    // skip visited nodes
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    Abc_NodeSetTravIdCurrent( pNode );
    // collect the fanins
    Pa_ManResubCollectDivs_rec( Abc_ObjFanin0( pNode ), vInternal );
    Pa_ManResubCollectDivs_rec( Abc_ObjFanin1( pNode ), vInternal );
    // collect the internal node
    if ( pNode->fMarkA == 0 )
        Vec_PtrPush( vInternal, pNode );
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_ManResubCollectDivs( Pa_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves, int Required )
{
    Abc_Obj_t *pNode, *pFanout;
    int i, k, Limit, Counter;

    Vec_PtrClear( p->vDivs1UP );
    Vec_PtrClear( p->vDivs1UN );
    Vec_PtrClear( p->vDivs1B );

    // add the leaves of the cuts to the divisors
    Vec_PtrClear( p->vDivs );
    Abc_NtkIncrementTravId( pRoot->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pNode, i )
    {
        Vec_PtrPush( p->vDivs, pNode );
        Abc_NodeSetTravIdCurrent( pNode );
    }

    // mark nodes in the MFFC
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i ) pNode->fMarkA = 1;
    // collect the cone (without MFFC)
    Pa_ManResubCollectDivs_rec( pRoot, p->vDivs );
    // unmark the current MFFC
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i ) pNode->fMarkA = 0;

    // check if the number of divisors is not exceeded
    if ( Vec_PtrSize( p->vDivs ) - Vec_PtrSize( vLeaves ) + Vec_PtrSize( p->vTemp ) >=
         Vec_PtrSize( p->vSims ) - p->nLeavesMax )
        return 0;

    // get the number of divisors to collect
    Limit = Vec_PtrSize( p->vSims ) - p->nLeavesMax -
            ( Vec_PtrSize( p->vDivs ) - Vec_PtrSize( vLeaves ) + Vec_PtrSize( p->vTemp ) );

    // explore the fanouts, which are not in the MFFC
    Counter = 0;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs, pNode, i )
    {
        if ( Abc_ObjFanoutNum( pNode ) > 100 )
        {
            continue;
        }
        // if the fanout has both fanins in the set, add it
        Abc_ObjForEachFanout( pNode, pFanout, k )
        {
            if ( Abc_NodeIsTravIdCurrent( pFanout ) || Abc_ObjIsCo( pFanout ) || (int)pFanout->Level > Required )
                continue;
            if ( Abc_NodeIsTravIdCurrent( Abc_ObjFanin0( pFanout ) ) &&
                 Abc_NodeIsTravIdCurrent( Abc_ObjFanin1( pFanout ) ) )
            {
                if ( Abc_ObjFanin0( pFanout ) == pRoot || Abc_ObjFanin1( pFanout ) == pRoot )
                    continue;
                Vec_PtrPush( p->vDivs, pFanout );
                Abc_NodeSetTravIdCurrent( pFanout );
                // quit computing divisors if there is too many of them
                if ( ++Counter == Limit )
                    goto Quits;
            }
        }
    }

Quits:
    // get the number of divisors
    p->nDivs = Vec_PtrSize( p->vDivs );

    // add the nodes in the MFFC
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vTemp, pNode, i ) Vec_PtrPush( p->vDivs, pNode );
    assert( pRoot == Vec_PtrEntryLast( p->vDivs ) );

    assert( Vec_PtrSize( p->vDivs ) - Vec_PtrSize( vLeaves ) <= Vec_PtrSize( p->vSims ) - p->nLeavesMax );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs simulation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords )
{
    Abc_Obj_t * pObj;
    unsigned *puData0, *puData1, *puData;
    int i, k;
    assert( Vec_PtrSize( vDivs ) - nLeaves <= Vec_PtrSize( vSims ) - nLeavesMax );
    // simulate
    Vec_PtrForEachEntry( Abc_Obj_t *, vDivs, pObj, i )
    {
        if ( i < nLeaves )
        { // initialize the leaf
            pObj->pData = Vec_PtrEntry( vSims, i );
            continue;
        }
        // set storage for the node's simulation info
        pObj->pData = Vec_PtrEntry( vSims, i - nLeaves + nLeavesMax );
        // get pointer to the simulation info
        puData = (unsigned *)pObj->pData;
        puData0 = (unsigned *)Abc_ObjFanin0( pObj )->pData;
        puData1 = (unsigned *)Abc_ObjFanin1( pObj )->pData;
        // simulate
        if ( Abc_ObjFaninC0( pObj ) && Abc_ObjFaninC1( pObj ) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & ~puData1[k];
        else if ( Abc_ObjFaninC0( pObj ) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & puData1[k];
        else if ( Abc_ObjFaninC1( pObj ) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & ~puData1[k];
        else
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & puData1[k];
    }
    // normalize
    Vec_PtrForEachEntry( Abc_Obj_t *, vDivs, pObj, i )
    {
        puData = (unsigned *)pObj->pData;
        pObj->fPhase = ( puData[0] & 1 );
        if ( pObj->fPhase )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData[k];
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_ManResubQuit0( Abc_Obj_t * pRoot, Abc_Obj_t * pObj )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot;
    pGraph = Dec_GraphCreate( 1 );
    Dec_GraphNode( pGraph, 0 )->pFunc = pObj;
    eRoot = Dec_EdgeCreate( 0, pObj->fPhase );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_ManResubQuit1( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1;
    assert( Abc_ObjRegular( pObj0 ) != Abc_ObjRegular( pObj1 ) );
    pGraph = Dec_GraphCreate( 2 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular( pObj0 );
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular( pObj1 );
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular( pObj0 )->fPhase ^ Abc_ObjIsComplement( pObj0 ) );
    eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular( pObj1 )->fPhase ^ Abc_ObjIsComplement( pObj1 ) );
    if ( fOrGate )
        eRoot = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
    else
        eRoot = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_ManResubQuit21( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2,
                                        int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1, eNode2;
    assert( Abc_ObjRegular( pObj0 ) != Abc_ObjRegular( pObj1 ) );
    assert( Abc_ObjRegular( pObj0 ) != Abc_ObjRegular( pObj2 ) );
    assert( Abc_ObjRegular( pObj1 ) != Abc_ObjRegular( pObj2 ) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular( pObj0 );
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular( pObj1 );
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular( pObj2 );
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular( pObj0 )->fPhase ^ Abc_ObjIsComplement( pObj0 ) );
    eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular( pObj1 )->fPhase ^ Abc_ObjIsComplement( pObj1 ) );
    eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular( pObj2 )->fPhase ^ Abc_ObjIsComplement( pObj2 ) );
    if ( fOrGate )
    {
        eRoot = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        eRoot = Dec_GraphAddNodeOr( pGraph, eNode2, eRoot );
    }
    else
    {
        eRoot = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
        eRoot = Dec_GraphAddNodeAnd( pGraph, eNode2, eRoot );
    }
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_ManResubQuit2( Abc_Obj_t * pRoot, Abc_Obj_t * pObj0, Abc_Obj_t * pObj1, Abc_Obj_t * pObj2,
                                       int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, ePrev, eNode0, eNode1, eNode2;
    assert( Abc_ObjRegular( pObj0 ) != Abc_ObjRegular( pObj1 ) );
    assert( Abc_ObjRegular( pObj0 ) != Abc_ObjRegular( pObj2 ) );
    assert( Abc_ObjRegular( pObj1 ) != Abc_ObjRegular( pObj2 ) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Abc_ObjRegular( pObj0 );
    Dec_GraphNode( pGraph, 1 )->pFunc = Abc_ObjRegular( pObj1 );
    Dec_GraphNode( pGraph, 2 )->pFunc = Abc_ObjRegular( pObj2 );
    eNode0 = Dec_EdgeCreate( 0, Abc_ObjRegular( pObj0 )->fPhase ^ Abc_ObjIsComplement( pObj0 ) );
    if ( Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
    {
        eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular( pObj1 )->fPhase );
        eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular( pObj2 )->fPhase );
        ePrev = Dec_GraphAddNodeOr( pGraph, eNode1, eNode2 );
    }
    else
    {
        eNode1 = Dec_EdgeCreate( 1, Abc_ObjRegular( pObj1 )->fPhase ^ Abc_ObjIsComplement( pObj1 ) );
        eNode2 = Dec_EdgeCreate( 2, Abc_ObjRegular( pObj2 )->fPhase ^ Abc_ObjIsComplement( pObj2 ) );
        ePrev = Dec_GraphAddNodeAnd( pGraph, eNode1, eNode2 );
    }
    if ( fOrGate )
        eRoot = Dec_GraphAddNodeOr( pGraph, eNode0, ePrev );
    else
        eRoot = Dec_GraphAddNodeAnd( pGraph, eNode0, ePrev );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Derives single-node unate/binate divisors.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubDivsS( Pa_ManRes_t * p, int Required )
{
    int fMoreDivs = 1; // bug fix by Siang-Yun Lee
    Abc_Obj_t * pObj;
    unsigned *puData, *puDataR;
    int i, w;
    Vec_PtrClear( p->vDivs1UP );
    Vec_PtrClear( p->vDivs1UN );
    Vec_PtrClear( p->vDivs1B );
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntryStop( Abc_Obj_t *, p->vDivs, pObj, i, p->nDivs )
    {
        if ( (int)pObj->Level > Required - 1 )
            continue;

        puData = (unsigned *)pObj->pData;
        // check positive containment
        for ( w = 0; w < p->nWords; w++ )
            if ( puData[w] & ~puDataR[w] & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
        {
            Vec_PtrPush( p->vDivs1UP, pObj );
            continue;
        }
        if ( fMoreDivs )
        {
            for ( w = 0; w < p->nWords; w++ )
                if ( ~puData[w] & ~puDataR[w] & p->pCareSet[w] ) // care set
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs1UP, Abc_ObjNot( pObj ) );
                continue;
            }
        }
        // check negative containment
        for ( w = 0; w < p->nWords; w++ )
            if ( ~puData[w] & puDataR[w] & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
        {
            Vec_PtrPush( p->vDivs1UN, pObj );
            continue;
        }
        if ( fMoreDivs )
        {
            for ( w = 0; w < p->nWords; w++ )
                if ( puData[w] & puDataR[w] & p->pCareSet[w] ) // care set
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs1UN, Abc_ObjNot( pObj ) );
                continue;
            }
        }
        // add the node to binates
        Vec_PtrPush( p->vDivs1B, pObj );
    }
}

/**Function*************************************************************

  Synopsis    [Derives double-node unate/binate divisors.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubDivsD( Pa_ManRes_t * p, int Required )
{
    Abc_Obj_t *pObj0, *pObj1;
    unsigned *puData0, *puData1, *puDataR;
    int i, k, w;
    Vec_PtrClear( p->vDivs2UP0 );
    Vec_PtrClear( p->vDivs2UP1 );
    Vec_PtrClear( p->vDivs2UN0 );
    Vec_PtrClear( p->vDivs2UN1 );
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1B, pObj0, i )
    {
        if ( (int)pObj0->Level > Required - 2 )
            continue;

        puData0 = (unsigned *)pObj0->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1B, pObj1, k, i + 1 )
        {
            if ( (int)pObj1->Level > Required - 2 )
                continue;

            puData1 = (unsigned *)pObj1->pData;

            if ( Vec_PtrSize( p->vDivs2UP0 ) < PA_RS_DIV2_MAX )
            {
                // get positive unate divisors
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( puData0[w] & puData1[w] ) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, pObj0 );
                    Vec_PtrPush( p->vDivs2UP1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( ~puData0[w] & puData1[w] ) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, Abc_ObjNot( pObj0 ) );
                    Vec_PtrPush( p->vDivs2UP1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( puData0[w] & ~puData1[w] ) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, pObj0 );
                    Vec_PtrPush( p->vDivs2UP1, Abc_ObjNot( pObj1 ) );
                }
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( puData0[w] | puData1[w] ) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, Abc_ObjNot( pObj0 ) );
                    Vec_PtrPush( p->vDivs2UP1, Abc_ObjNot( pObj1 ) );
                }
            }

            if ( Vec_PtrSize( p->vDivs2UN0 ) < PA_RS_DIV2_MAX )
            {
                // get negative unate divisors
                for ( w = 0; w < p->nWords; w++ )
                    if ( ~( puData0[w] & puData1[w] ) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, pObj0 );
                    Vec_PtrPush( p->vDivs2UN1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
                    if ( ~( ~puData0[w] & puData1[w] ) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, Abc_ObjNot( pObj0 ) );
                    Vec_PtrPush( p->vDivs2UN1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
                    if ( ~( puData0[w] & ~puData1[w] ) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, pObj0 );
                    Vec_PtrPush( p->vDivs2UN1, Abc_ObjNot( pObj1 ) );
                }
                for ( w = 0; w < p->nWords; w++ )
                    if ( ~( puData0[w] | puData1[w] ) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, Abc_ObjNot( pObj0 ) );
                    Vec_PtrPush( p->vDivs2UN1, Abc_ObjNot( pObj1 ) );
                }
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_ManResubQuit( Pa_ManRes_t * p )
{
    Dec_Graph_t * pGraph;
    unsigned * upData;
    int w;
    upData = (unsigned *)p->pRoot->pData;
    for ( w = 0; w < p->nWords; w++ )
        if ( upData[w] & p->pCareSet[w] ) // care set
            break;
    if ( w != p->nWords )
        return NULL;
    // get constant node graph
    if ( p->pRoot->fPhase )
        pGraph = Dec_GraphCreateConst1();
    else
        pGraph = Dec_GraphCreateConst0();
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Keeps a truth-valid candidate if it ranks best so far.]

  Description [Takes ownership of a truth-valid graph and keeps it if it
               ranks best so far, using its actual divisor boundary rather
               than the simulation cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubConsider( Pa_ManRes_t * p, Dec_Graph_t * pGraph )
{
    Dec_Node_t * pDec;
    Abc_Obj_t * pLeaf;
    int i, Saved, Gain;
    double Score;
    Vec_PtrClear( p->vPaLeaves );
    Dec_GraphForEachLeaf( pGraph, pDec, i )
        Vec_PtrPushUnique( p->vPaLeaves, Abc_ObjRegular( (Abc_Obj_t *)pDec->pFunc ) );
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vPaLeaves, pLeaf, i ) pLeaf->vFanouts.nSize++;
    Abc_NtkIncrementTravId( p->pRoot->pNtk );
    Saved = Abc_NodeMffcLabelAig( p->pRoot );
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vPaLeaves, pLeaf, i ) pLeaf->vFanouts.nSize--;
    if ( Pa_ManEvaluateCandidate( p->pRoot, pGraph, Saved, p->nPaRequired, 0, &Gain, &Score, NULL, NULL, NULL ) &&
         Gain >= 0 )
    {
        if ( Score > 1.0e-10 && ( p->pPaBest == NULL || Score > p->dPaScore + 1.0e-10 ||
                                  ( fabs( Score - p->dPaScore ) <= 1.0e-10 && Gain > p->nPaGain ) ) )
        {
            if ( p->pPaBest )
                Dec_GraphFree( p->pPaBest );
            p->pPaBest = pGraph;
            p->dPaScore = Score;
            p->nPaGain = Gain;
            return;
        }
    }
    Dec_GraphFree( pGraph );
}

/**Function*************************************************************

  Synopsis    [Tries the divisors that implement the root without new nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubDivs0( Pa_ManRes_t * p )
{
    Abc_Obj_t * pObj;
    unsigned *puData, *puDataR;
    int i, w;
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntryStop( Abc_Obj_t *, p->vDivs, pObj, i, p->nDivs )
    {
        puData = (unsigned *)pObj->pData;
        for ( w = 0; w < p->nWords; w++ )
            if ( ( puData[w] ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
            Pa_ManResubConsider( p, Pa_ManResubQuit0( p->pRoot, pObj ) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubDivs1( Pa_ManRes_t * p, int Required )
{
    Abc_Obj_t *pObj0, *pObj1;
    unsigned *puData0, *puData1, *puDataR;
    int i, k, w;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular( pObj0 )->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UP, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular( pObj1 )->pData;
            if ( Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) )
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( ( ~puData0[w] | ~puData1[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Abc_ObjIsComplement( pObj0 ) )
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( ( ~puData0[w] | puData1[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Abc_ObjIsComplement( pObj1 ) )
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( ( puData0[w] | ~puData1[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                        break;
            }
            else
            {
                for ( w = 0; w < p->nWords; w++ )
                    if ( ( ( puData0[w] | puData1[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( w == p->nWords )
                Pa_ManResubConsider( p, Pa_ManResubQuit1( p->pRoot, pObj0, pObj1, 1 ) );
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular( pObj0 )->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UN, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular( pObj1 )->pData;
            // Check the AND of the two divisors directly.
            for ( w = 0; w < p->nWords; ++w )
            {
                unsigned A = Abc_ObjIsComplement( pObj0 ) ? ~puData0[w] : puData0[w];
                unsigned B = Abc_ObjIsComplement( pObj1 ) ? ~puData1[w] : puData1[w];
                if ( ( ( A & B ) ^ puDataR[w] ) & p->pCareSet[w] )
                    break;
            }
            if ( w == p->nWords )
                Pa_ManResubConsider( p, Pa_ManResubQuit1( p->pRoot, pObj0, pObj1, 0 ) );
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubDivs12( Pa_ManRes_t * p, int Required )
{
    Abc_Obj_t *pObj0, *pObj1, *pObj2;
    unsigned *puData0, *puData1, *puData2, *puDataR;
    int i, k, j, w = 0;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular( pObj0 )->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UP, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular( pObj1 )->pData;
            Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UP, pObj2, j, k + 1 )
            {
                puData2 = (unsigned *)Abc_ObjRegular( pObj2 )->pData;
                if ( Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | ~puData1[w] | ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | ~puData1[w] | puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | puData1[w] | ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | puData1[w] | puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) &&
                          Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | ~puData1[w] | ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | ~puData1[w] | puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | puData1[w] | ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | puData1[w] | puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else
                    assert( 0 );
                if ( w == p->nWords )
                {
                    // Rank all three groupings, not just ABC's level-based one.
                    Pa_ManResubConsider( p, Pa_ManResubQuit21( p->pRoot, pObj0, pObj1, pObj2, 1 ) );
                    Pa_ManResubConsider( p, Pa_ManResubQuit21( p->pRoot, pObj0, pObj2, pObj1, 1 ) );
                    Pa_ManResubConsider( p, Pa_ManResubQuit21( p->pRoot, pObj1, pObj2, pObj0, 1 ) );
                }
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular( pObj0 )->pData;
        Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UN, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Abc_ObjRegular( pObj1 )->pData;
            Vec_PtrForEachEntryStart( Abc_Obj_t *, p->vDivs1UN, pObj2, j, k + 1 )
            {
                puData2 = (unsigned *)Abc_ObjRegular( pObj2 )->pData;
                if ( Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & ~puData1[w] & ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & ~puData1[w] & puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & puData1[w] & ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & puData1[w] & puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) &&
                          Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & ~puData1[w] & ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & ~puData1[w] & puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & puData1[w] & ~puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Abc_ObjIsComplement( pObj0 ) && !Abc_ObjIsComplement( pObj1 ) &&
                          !Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & puData1[w] & puData2[w] ) ^ puDataR[w] ) & p->pCareSet[w] ) // care set
                            break;
                }
                else
                    assert( 0 );
                if ( w == p->nWords )
                {
                    Pa_ManResubConsider( p, Pa_ManResubQuit21( p->pRoot, pObj0, pObj1, pObj2, 0 ) );
                    Pa_ManResubConsider( p, Pa_ManResubQuit21( p->pRoot, pObj0, pObj2, pObj1, 0 ) );
                    Pa_ManResubConsider( p, Pa_ManResubQuit21( p->pRoot, pObj1, pObj2, pObj0, 0 ) );
                }
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_ManResubDivs2( Pa_ManRes_t * p, int Required )
{
    Abc_Obj_t *pObj0, *pObj1, *pObj2;
    unsigned *puData0, *puData1, *puData2, *puDataR;
    int i, k, w;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular( pObj0 )->pData;
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs2UP0, pObj1, k )
        {
            pObj2 = (Abc_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, k );

            puData1 = (unsigned *)Abc_ObjRegular( pObj1 )->pData;
            puData2 = (unsigned *)Abc_ObjRegular( pObj2 )->pData;
            if ( Abc_ObjIsComplement( pObj0 ) )
            {
                if ( Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | ( puData1[w] | puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj1 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | ( ~puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | ( puData1[w] & ~puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] | ( puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
            }
            else
            {
                if ( Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | ( puData1[w] | puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj1 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | ( ~puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | ( puData1[w] & ~puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] | ( puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
            }
            if ( w == p->nWords )
                Pa_ManResubConsider( p, Pa_ManResubQuit2( p->pRoot, pObj0, pObj1, pObj2, 1 ) );
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Abc_ObjRegular( pObj0 )->pData;
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vDivs2UN0, pObj1, k )
        {
            pObj2 = (Abc_Obj_t *)Vec_PtrEntry( p->vDivs2UN1, k );

            puData1 = (unsigned *)Abc_ObjRegular( pObj1 )->pData;
            puData2 = (unsigned *)Abc_ObjRegular( pObj2 )->pData;
            if ( Abc_ObjIsComplement( pObj0 ) )
            {
                if ( Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & ( puData1[w] | puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj1 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & ( ~puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & ( puData1[w] & ~puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( ~puData0[w] & ( puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
            }
            else
            {
                if ( Abc_ObjIsComplement( pObj1 ) && Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & ( puData1[w] | puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj1 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & ( ~puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Abc_ObjIsComplement( pObj2 ) )
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & ( puData1[w] & ~puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
                        if ( ( ( puData0[w] & ( puData1[w] & puData2[w] ) ) ^ puDataR[w] ) &
                             p->pCareSet[w] ) // care set
                            break;
                }
            }
            if ( w == p->nWords )
                Pa_ManResubConsider( p, Pa_ManResubQuit2( p->pRoot, pObj0, pObj1, pObj2, 0 ) );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Evaluates resubstution of one cut.]

  Description [Returns the graph to add if any.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t * Pa_ManResubEval( Pa_ManRes_t * p, Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves )
{
    extern int Abc_NodeMffcInside( Abc_Obj_t * pNode, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vInside );
    Dec_Graph_t * pGraph;
    int Required = Abc_ObjRequiredLevel( pRoot );

    p->pRoot = pRoot;
    p->nLeaves = Vec_PtrSize( vLeaves );
    p->nLastGain = -1;

    // collect the MFFC
    p->nMffc = Abc_NodeMffcInside( pRoot, vLeaves, p->vTemp );
    assert( p->nMffc > 0 );

    // collect the divisor nodes
    if ( !Pa_ManResubCollectDivs( p, pRoot, vLeaves, Required ) )
        return NULL;

    // simulate the nodes
    Pa_ManResubSimulate( p->vDivs, p->nLeaves, p->vSims, p->nLeavesMax, p->nWords );

    p->pPaBest = NULL;
    p->nPaRequired = Required;
    p->nPaGain = -1;
    p->dPaScore = -ABC_INFINITY;
    pGraph = Pa_ManResubQuit( p );
    if ( pGraph )
        Pa_ManResubConsider( p, pGraph );
    Pa_ManResubDivs0( p );
    if ( p->nMffc >= 1 )
    {
        Pa_ManResubDivsS( p, Required );
        Pa_ManResubDivs1( p, Required );
    }
    // Two-node candidates for MFFCs of two or more nodes; lazily, only for
    // MFFCs of three or more nodes without a gaining one-node candidate.
    if ( p->fLazyPairs ? p->nMffc >= 3 && !( p->pPaBest != NULL && p->nPaGain > 0 ) : p->nMffc >= 2 )
    {
        Pa_ManResubDivs12( p, Required );
        Pa_ManResubDivsD( p, Required );
        Pa_ManResubDivs2( p, Required );
    }
    pGraph = p->pPaBest;
    p->pPaBest = NULL;
    if ( pGraph )
        p->nLastGain = p->nPaGain;
    return pGraph;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
