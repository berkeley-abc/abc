/**CFile****************************************************************

  FileName    [ivyBalance.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Algebraic AIG balancing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyBalance.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Ivy_NodeBalance( Ivy_Obj_t * pNode, int fUpdateLevel, Vec_Ptr_t * vFront, Vec_Ptr_t * vSpots );

// this procedure returns 1 if the node cannot be expanded
static inline int Ivy_NodeStopFanin( Ivy_Obj_t * pNode, int iFanin )
{
    if ( iFanin == 0 )
        return Ivy_ObjFanin0(pNode)->Type != pNode->Type || Ivy_ObjRefs(Ivy_ObjFanin0(pNode)) > 1 || Ivy_ObjFaninC0(pNode);
    else
        return Ivy_ObjFanin1(pNode)->Type != pNode->Type || Ivy_ObjRefs(Ivy_ObjFanin1(pNode)) > 1 || Ivy_ObjFaninC1(pNode);
}

// this procedure returns 1 if the node cannot be recursively dereferenced
static inline int Ivy_NodeBalanceDerefFanin( Ivy_Obj_t * pNode, int iFanin )
{
    if ( iFanin == 0 )
        return Ivy_ObjFanin0(pNode)->Type == pNode->Type && Ivy_ObjRefs(Ivy_ObjFanin0(pNode)) == 0 && !Ivy_ObjFaninC0(pNode);
    else
        return Ivy_ObjFanin1(pNode)->Type == pNode->Type && Ivy_ObjRefs(Ivy_ObjFanin1(pNode)) == 0 && !Ivy_ObjFaninC1(pNode);
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs algebraic balancing of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManBalance( Ivy_Man_t * p, int fUpdateLevel )
{
    Vec_Int_t * vNodes;
    Vec_Ptr_t * vFront, * vSpots;
    Ivy_Obj_t * pNode;
    int i;
    vSpots = Vec_PtrAlloc( 50 );
    vFront = Vec_PtrAlloc( 50 );
    vNodes = Ivy_ManDfs( p );
    Ivy_ManForEachNodeVec( p, vNodes, pNode, i )
    {
        if ( Ivy_ObjIsBuf(pNode) )
            continue;
        // fix the fanin buffer problem
        Ivy_NodeFixBufferFanins( pNode );
        // skip node if it became a buffer
        if ( Ivy_ObjIsBuf(pNode) )
            continue;
        // skip nodes with one fanout if type of the node is the same as type of the fanout
        // such nodes will be processed when the fanouts are processed
        if ( Ivy_ObjRefs(pNode) == 1 && Ivy_ObjIsExor(pNode) == Ivy_ObjExorFanout(pNode) )
            continue;
        assert( Ivy_ObjRefs(pNode) > 0 );
        // do not balance the node if both if its fanins have more than one fanout
        if ( Ivy_NodeStopFanin(pNode, 0) && Ivy_NodeStopFanin(pNode, 1) )
             continue;
        // try balancing this node
        Ivy_NodeBalance( pNode, fUpdateLevel, vFront, vSpots );
    }
    Vec_IntFree( vNodes );
    Vec_PtrFree( vSpots );
    Vec_PtrFree( vFront );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Dereferences MFFC of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeBalanceDeref_rec( Ivy_Obj_t * pNode )
{
    Ivy_Obj_t * pFan;
    // deref the first fanin
    pFan = Ivy_ObjFanin0(pNode);
    Ivy_ObjRefsDec( pFan );
    if ( Ivy_NodeBalanceDerefFanin(pNode, 0) )
        Ivy_NodeBalanceDeref_rec( pFan );
    // deref the second fanin
    pFan = Ivy_ObjFanin1(pNode);
    Ivy_ObjRefsDec( pFan );
    if ( Ivy_NodeBalanceDerefFanin(pNode, 1) )
        Ivy_NodeBalanceDeref_rec( pFan );
}

/**Function*************************************************************

  Synopsis    [Removes nodes inside supergate and determines frontier.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeBalanceCollect_rec( Ivy_Obj_t * pNode, Vec_Ptr_t * vSpots, Vec_Ptr_t * vFront )
{
    Ivy_Obj_t * pFanin;
    // skip visited nodes
    if ( Vec_PtrFind(vSpots, pNode) >= 0 )
        return;
    // collect node
    Vec_PtrPush( vSpots, pNode );
    // first fanin
    pFanin = Ivy_ObjFanin0(pNode);
    if ( Ivy_ObjRefs(pFanin) == 0 )
        Ivy_NodeBalanceCollect_rec( pFanin, vSpots, vFront );
    else if ( Ivy_ObjIsExor(pNode) && Vec_PtrFind(vFront, Ivy_ObjChild0(pNode)) >= 0 )
        Vec_PtrRemove( vFront, Ivy_ObjChild0(pNode) );
    else
        Vec_PtrPushUnique( vFront, Ivy_ObjChild0(pNode) );
    // second fanin
    pFanin = Ivy_ObjFanin1(pNode);
    if ( Ivy_ObjRefs(pFanin) == 0 )
        Ivy_NodeBalanceCollect_rec( pFanin, vSpots, vFront );
    else if ( Ivy_ObjIsExor(pNode) && Vec_PtrFind(vFront, Ivy_ObjChild1(pNode)) >= 0 )
        Vec_PtrRemove( vFront, Ivy_ObjChild1(pNode) );
    else
        Vec_PtrPushUnique( vFront, Ivy_ObjChild1(pNode) );
}

/**Function*************************************************************

  Synopsis    [Comparison procedure for two nodes by level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_BalanceCompareByLevel( Ivy_Obj_t ** pp1, Ivy_Obj_t ** pp2 )
{
    int Level1 = Ivy_ObjLevel( *pp1 );
    int Level2 = Ivy_ObjLevel( *pp2 );
    if ( Level1 > Level2 )
        return -1;
    if ( Level1 < Level2 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Removes nodes inside supergate and determines frontier.]

  Description [Return 1 if the output needs to be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_NodeBalancePrepare( Ivy_Obj_t * pNode, Vec_Ptr_t * vFront, Vec_Ptr_t * vSpots )
{
    Ivy_Man_t * pMan = Ivy_ObjMan( pNode );
    Ivy_Obj_t * pObj, * pNext;
    int i, k, Counter = 0;
    // dereference the cone
    Ivy_NodeBalanceDeref_rec( pNode );
    // collect the frontier and the internal nodes
    Vec_PtrClear( vFront );
    Vec_PtrClear( vSpots );
    Ivy_NodeBalanceCollect_rec( pNode, vSpots, vFront );
    // remove all the nodes
    Vec_PtrForEachEntry( vSpots, pObj, i )
    {
        // skip the first entry (the node itself)
        if ( i == 0 ) continue;
        // collect the free entries
        Vec_IntPush( pMan->vFree, pObj->Id );
        Ivy_ObjDelete( pObj, 1 );
    }
    // sort nodes by level in decreasing order
    qsort( (void *)Vec_PtrArray(vFront), Vec_PtrSize(vFront), sizeof(Ivy_Obj_t *), 
            (int (*)(const void *, const void *))Ivy_BalanceCompareByLevel );
    // check if there are nodes and their complements
    Counter = 0;
    Vec_PtrForEachEntry( vFront, pObj, i )
    {
        if ( i == Vec_PtrSize(vFront) - 1 )
            break;
        pNext = Vec_PtrEntry( vFront, i+1 );
        if ( Ivy_Regular(pObj) == Ivy_Regular(pNext) )
        {
            assert( pObj == Ivy_Not(pNext) );
            Vec_PtrWriteEntry( vFront, i, NULL );
            Vec_PtrWriteEntry( vFront, i+1, NULL );
            i++;
            Counter++;
        }
    }
    // if there are no complemented pairs, go ahead and balance
    if ( Counter == 0 )
        return 0;
    // if there are complemented pairs and this is AND, create const 0
    if ( Counter > 0 && Ivy_ObjIsAnd(pNode) )
    {
        Vec_PtrClear( vFront );
        Vec_PtrPush( vFront, Ivy_ManConst0(pMan) );
        return 0;
    }
    assert( Counter > 0 && Ivy_ObjIsExor(pNode) );
    // remove the pairs
    k = 0;
    Vec_PtrForEachEntry( vFront, pObj, i )
        if ( pObj ) 
            Vec_PtrWriteEntry( vFront, k++, pObj );
    Vec_PtrShrink( vFront, k );
    // add constant zero node if nothing is left
    if ( Vec_PtrSize(vFront) == 0 )
        Vec_PtrPush( vFront, Ivy_ManConst0(pMan) );
    // return 1 if the number of pairs is odd (need to complement the output)
    return Counter & 1;
}

/**Function*************************************************************

  Synopsis    [Finds the left bound on the next candidate to be paired.]

  Description [The nodes in the array are in the decreasing order of levels. 
  The last node in the array has the smallest level. By default it would be paired 
  with the next node on the left. However, it may be possible to pair it with some
  other node on the left, in such a way that the new node is shared. This procedure
  finds the index of the left-most node, which can be paired with the last node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_NodeBalanceFindLeft( Vec_Ptr_t * vSuper )
{
    Ivy_Obj_t * pNodeRight, * pNodeLeft;
    int Current;
    // if two or less nodes, pair with the first
    if ( Vec_PtrSize(vSuper) < 3 )
        return 0;
    // set the pointer to the one before the last
    Current = Vec_PtrSize(vSuper) - 2;
    pNodeRight = Vec_PtrEntry( vSuper, Current );
    // go through the nodes to the left of this one
    for ( Current--; Current >= 0; Current-- )
    {
        // get the next node on the left
        pNodeLeft = Vec_PtrEntry( vSuper, Current );
        // if the level of this node is different, quit the loop
        if ( Ivy_Regular(pNodeLeft)->Level != Ivy_Regular(pNodeRight)->Level )
            break;
    }
    Current++;    
    // get the node, for which the equality holds
    pNodeLeft = Vec_PtrEntry( vSuper, Current );
    assert( Ivy_Regular(pNodeLeft)->Level == Ivy_Regular(pNodeRight)->Level );
    return Current;
}

/**Function*************************************************************

  Synopsis    [Moves closer to the end the node that is best for sharing.]

  Description [If there is no node with sharing, randomly chooses one of 
  the legal nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeBalancePermute( Ivy_Man_t * pMan, Vec_Ptr_t * vSuper, int LeftBound, int fExor )
{
    Ivy_Obj_t * pNode1, * pNode2, * pNode3, * pGhost;
    int RightBound, i;
    // get the right bound
    RightBound = Vec_PtrSize(vSuper) - 2;
    assert( LeftBound <= RightBound );
    if ( LeftBound == RightBound )
        return;
    // get the two last nodes
    pNode1 = Vec_PtrEntry( vSuper, RightBound + 1 );
    pNode2 = Vec_PtrEntry( vSuper, RightBound     );
    // find the first node that can be shared
    for ( i = RightBound; i >= LeftBound; i-- )
    {
        pNode3 = Vec_PtrEntry( vSuper, i );
        pGhost = Ivy_ObjCreateGhost( pNode1, pNode3, fExor? IVY_EXOR : IVY_AND, IVY_INIT_NONE );
        if ( Ivy_TableLookup( pGhost ) )
        {
            if ( pNode3 == pNode2 )
                return;
            Vec_PtrWriteEntry( vSuper, i,          pNode2 );
            Vec_PtrWriteEntry( vSuper, RightBound, pNode3 );
            return;
        }
    }
/*
    // we did not find the node to share, randomize choice
    {
        int Choice = rand() % (RightBound - LeftBound + 1);
        pNode3 = Vec_PtrEntry( vSuper, LeftBound + Choice );
        if ( pNode3 == pNode2 )
            return;
        Vec_PtrWriteEntry( vSuper, LeftBound + Choice, pNode2 );
        Vec_PtrWriteEntry( vSuper, RightBound,         pNode3 );
    }
*/
}

/**Function*************************************************************

  Synopsis    [Inserts a new node in the order by levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeBalancePushUniqueOrderByLevel( Vec_Ptr_t * vFront, Ivy_Obj_t * pNode )
{
    Ivy_Obj_t * pNode1, * pNode2;
    int i;
    if ( Vec_PtrPushUnique(vFront, pNode) )
        return;
    // find the p of the node
    for ( i = vFront->nSize-1; i > 0; i-- )
    {
        pNode1 = vFront->pArray[i  ];
        pNode2 = vFront->pArray[i-1];
        if ( Ivy_Regular(pNode1)->Level <= Ivy_Regular(pNode2)->Level )
            break;
        vFront->pArray[i  ] = pNode2;
        vFront->pArray[i-1] = pNode1;
    }
}

/**Function*************************************************************

  Synopsis    [Balances one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_NodeBalance( Ivy_Obj_t * pNode, int fUpdateLevel, Vec_Ptr_t * vFront, Vec_Ptr_t * vSpots )
{
    Ivy_Man_t * pMan = Ivy_ObjMan( pNode );
    Ivy_Obj_t * pFan0, * pFan1, * pNodeNew;
    int fCompl, LeftBound;
    // remove internal nodes and derive the frontier
    fCompl = Ivy_NodeBalancePrepare( pNode, vFront, vSpots );
    assert( Vec_PtrSize(vFront) > 0 );
    // balance the nodes
    while ( Vec_PtrSize(vFront) > 1 )
    {
        // find the left bound on the node to be paired
        LeftBound = (!fUpdateLevel)? 0 : Ivy_NodeBalanceFindLeft( vFront );
        // find the node that can be shared (if no such node, randomize choice)
        Ivy_NodeBalancePermute( pMan, vFront, LeftBound, Ivy_ObjIsExor(pNode) );
        // pull out the last two nodes
        pFan0 = Vec_PtrPop(vFront);  assert( !Ivy_ObjIsConst1(Ivy_Regular(pFan0)) );
        pFan1 = Vec_PtrPop(vFront);  assert( !Ivy_ObjIsConst1(Ivy_Regular(pFan1)) );
        // create the new node
        pNodeNew = Ivy_ObjCreate( Ivy_ObjCreateGhost(pFan0, pFan1, Ivy_ObjType(pNode), IVY_INIT_NONE) );
        // add the new node to the frontier
        Ivy_NodeBalancePushUniqueOrderByLevel( vFront, pNodeNew );
    }
    assert( Vec_PtrSize(vFront) == 1 );
    // perform the replacement
    Ivy_ObjReplace( pNode, Ivy_NotCond(Vec_PtrPop(vFront), fCompl), 1, 1 ); 
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


