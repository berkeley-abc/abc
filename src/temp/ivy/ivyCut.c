/**CFile****************************************************************

  FileName    [ivyCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [Computes reconvergence driven sequential cut.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyCut.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Evaluate the cost of removing the node from the set of leaves.]

  Description [Returns the number of new leaves that will be brought in.
  Returns large number if the node cannot be removed from the set of leaves.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ivy_NodeGetLeafCostOne( Ivy_Man_t * p, int Leaf, Vec_Int_t * vInside )
{
    Ivy_Obj_t * pNode;
    int nLatches, FaninLeaf, Cost;
    // make sure leaf is not a contant node
    assert( Leaf > 0 ); 
    // get the node
    pNode = Ivy_ManObj( p, Ivy_LeafId(Leaf) );
    // cannot expand over the PI node
    if ( Ivy_ObjIsPi(pNode) || Ivy_ObjIsConst1(pNode) )
        return 999;
    // get the number of latches
    nLatches = Ivy_LeafLat(Leaf) + Ivy_ObjIsLatch(pNode);
    if ( nLatches > 15 )
        return 999;
    // get the first fanin
    FaninLeaf = Ivy_LeafCreate( Ivy_ObjFaninId0(pNode), nLatches );
    Cost = FaninLeaf && (Vec_IntFind(vInside, FaninLeaf) == -1);
    // quit if this is the one fanin node
    if ( Ivy_ObjIsLatch(pNode) || Ivy_ObjIsBuf(pNode) )
        return Cost;
    assert( Ivy_ObjIsNode(pNode) );
    // get the second fanin
    FaninLeaf = Ivy_LeafCreate( Ivy_ObjFaninId1(pNode), nLatches );
    Cost += FaninLeaf && (Vec_IntFind(vInside, FaninLeaf) == -1);
    return Cost;
}

/**Function*************************************************************

  Synopsis    [Builds reconvergence-driven cut by changing one leaf at a time.]

  Description [This procedure looks at the current leaves and tries to change 
  one leaf at a time in such a way that the cut grows as little as possible.
  In evaluating the fanins, this procedure looks only at their immediate 
  predecessors (this is why it is called a one-level construction procedure).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManSeqFindCut_int( Ivy_Man_t * p, Vec_Int_t * vFront, Vec_Int_t * vInside, int nSizeLimit )
{
    Ivy_Obj_t * pNode;
    int CostBest, CostCur, Leaf, LeafBest, Next, nLatches, i;
    int LeavesBest[10];
    int Counter;

    // add random selection of the best fanin!!!

    // find the best fanin
    CostBest = 99;
    LeafBest = -1;
    Counter = -1;
//printf( "Evaluating fanins of the cut:\n" );
    Vec_IntForEachEntry( vFront, Leaf, i )
    {
        CostCur = Ivy_NodeGetLeafCostOne( p, Leaf, vInside );
//printf( "    Fanin %s has cost %d.\n", Ivy_ObjName(pNode), CostCur );
        if ( CostBest > CostCur )
        {
            CostBest = CostCur;
            LeafBest = Leaf;
            LeavesBest[0] = Leaf;
            Counter = 1;
        }
        else if ( CostBest == CostCur )
            LeavesBest[Counter++] = Leaf;

        if ( CostBest <= 1 ) // can be if ( CostBest <= 1 )
            break;
    }
    if ( CostBest == 99 )
        return 0;
//        return Ivy_NodeBuildCutLevelTwo_int( vInside, vFront, nFaninLimit );

    assert( CostBest < 3 );
    if ( Vec_IntSize(vFront) - 1 + CostBest > nSizeLimit )
        return 0;
//        return Ivy_NodeBuildCutLevelTwo_int( vInside, vFront, nFaninLimit );

    assert( Counter > 0 );
printf( "%d", Counter );

    LeafBest = LeavesBest[rand() % Counter];

    // remove the node from the array
    assert( LeafBest >= 0 );
    Vec_IntRemove( vFront, LeafBest );
//printf( "Removing fanin %s.\n", Ivy_ObjName(pNode) );

    // get the node and its latches
    pNode = Ivy_ManObj( p, Ivy_LeafId(LeafBest) );
    nLatches = Ivy_LeafLat(LeafBest) + Ivy_ObjIsLatch(pNode);
    assert( Ivy_ObjIsNode(pNode) || Ivy_ObjIsLatch(pNode) || Ivy_ObjIsBuf(pNode) );

    // add the left child to the fanins
    Next = Ivy_LeafCreate( Ivy_ObjFaninId0(pNode), nLatches );
    if ( Next && Vec_IntFind(vInside, Next) == -1 )
    {
//printf( "Adding fanin %s.\n", Ivy_ObjName(pNext) );
        Vec_IntPush( vFront, Next );
        Vec_IntPush( vInside, Next );
    }

    // quit if this is the one fanin node
    if ( Ivy_ObjIsLatch(pNode) || Ivy_ObjIsBuf(pNode) )
        return 1;
    assert( Ivy_ObjIsNode(pNode) );

    // add the right child to the fanins
    Next = Ivy_LeafCreate( Ivy_ObjFaninId1(pNode), nLatches );
    if ( Next && Vec_IntFind(vInside, Next) == -1 )
    {
//printf( "Adding fanin %s.\n", Ivy_ObjName(pNext) );
        Vec_IntPush( vFront, Next );
        Vec_IntPush( vInside, Next );
    }
    assert( Vec_IntSize(vFront) <= nSizeLimit );
    // keep doing this
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes one sequential cut of the given size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManSeqFindCut( Ivy_Obj_t * pRoot, Vec_Int_t * vFront, Vec_Int_t * vInside, int nSize )
{
    assert( !Ivy_IsComplement(pRoot) );
    assert( Ivy_ObjIsNode(pRoot) );
    assert( Ivy_ObjFaninId0(pRoot) );
    assert( Ivy_ObjFaninId1(pRoot) );

    // start the cut 
    Vec_IntClear( vFront );
    Vec_IntPush( vFront, Ivy_LeafCreate(Ivy_ObjFaninId0(pRoot), 0) );
    Vec_IntPush( vFront, Ivy_LeafCreate(Ivy_ObjFaninId1(pRoot), 0) );

    // start the visited nodes
    Vec_IntClear( vInside );
    Vec_IntPush( vInside, Ivy_LeafCreate(pRoot->Id, 0) );
    Vec_IntPush( vInside, Ivy_LeafCreate(Ivy_ObjFaninId0(pRoot), 0) );
    Vec_IntPush( vInside, Ivy_LeafCreate(Ivy_ObjFaninId1(pRoot), 0) );

    // compute the cut
    while ( Ivy_ManSeqFindCut_int( Ivy_ObjMan(pRoot), vFront, vInside, nSize ) );
    assert( Vec_IntSize(vFront) <= nSize );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


