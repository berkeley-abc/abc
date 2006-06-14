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



/**Function*************************************************************

  Synopsis    [Comparison for node pointers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManFindAlgCutCompare( Ivy_Obj_t ** pp1, Ivy_Obj_t ** pp2 )
{
    if ( *pp1 < *pp2 )
        return -1;
    if ( *pp1 > *pp2 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computing one algebraic cut.]

  Description [Returns 1 if the tree-leaves of this node where traversed 
  and found to have no external references (and have not been collected). 
  Returns 0 if the tree-leaves have external references and are collected.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManFindAlgCut_rec( Ivy_Obj_t * pRoot, Ivy_Type_t Type, Vec_Ptr_t * vFront )
{
    int RetValue0, RetValue1;
    Ivy_Obj_t * pRootR = Ivy_Regular(pRoot);
    assert( Type != IVY_EXOR || !Ivy_IsComplement(pRoot) );
    // if the node is a buffer skip through it
    if ( Ivy_ObjIsBuf(pRootR) )
        return Ivy_ManFindAlgCut_rec( Ivy_NotCond(Ivy_ObjChild0(pRootR), Ivy_IsComplement(pRoot)), Type, vFront );
    // if the node is the end of the tree, return
    if ( Ivy_IsComplement(pRoot) || Ivy_ObjIsCi(pRoot) || Ivy_ObjType(pRoot) != Type )
    {
        if ( Ivy_ObjRefs(pRootR) == 1 )
            return 1;
        assert( Ivy_ObjRefs(pRootR) > 1 );
        Vec_PtrPush( vFront, pRoot );
        return 0;
    }
    // branch on the node
    assert( Ivy_ObjIsNode(pRoot) );
    RetValue0 = Ivy_ManFindAlgCut_rec( Ivy_ObjChild0(pRoot), Type, vFront );
    RetValue1 = Ivy_ManFindAlgCut_rec( Ivy_ObjChild1(pRoot), Type, vFront );
    // the case when both have no external referenced
    if ( RetValue0 && RetValue1 )
    {
        if ( Ivy_ObjRefs(pRoot) == 1 )
            return 1;
        assert( Ivy_ObjRefs(pRoot) > 1 );
        Vec_PtrPush( vFront, pRoot );
        return 0;
    }
    // the case when one of them has external references
    if ( RetValue0 )
        Vec_PtrPush( vFront, Ivy_ObjChild0(pRoot) );
    if ( RetValue1 )
        Vec_PtrPush( vFront, Ivy_ObjChild1(pRoot) );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computing one algebraic cut.]

  Description [Algebraic cut stops when we hit (a) CI, (b) complemented edge,
  (c) boundary of different gates. Returns 1 if this is a pure tree.
  Returns -1 if the contant 0 is detected. Return 0 if the array can be used.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManFindAlgCut( Ivy_Obj_t * pRoot, Vec_Ptr_t * vFront )
{
    Ivy_Obj_t * pObj, * pPrev;
    int RetValue, i, k;
    assert( !Ivy_IsComplement(pRoot) );
    // clear the frontier and collect the nodes
    Vec_PtrClear( vFront );
    RetValue = Ivy_ManFindAlgCut_rec( pRoot, Ivy_ObjType(pRoot), vFront );
    // return if the node is the root of a tree
    if ( RetValue == 1 )
        return 1;
    // sort the entries to in increasing order
    Vec_PtrSort( vFront, Ivy_ManFindAlgCutCompare );
    // remove duplicated
    k = 1;
    Vec_PtrForEachEntryStart( vFront, pObj, i, 1 )
    {
        pPrev = (k == 0 ? NULL : Vec_PtrEntry(vFront, k-1));
        if ( pObj == pPrev )
        {
            if ( Ivy_ObjIsExor(pRoot) )
                k--;
            continue;
        }
        if ( pObj == Ivy_Not(pPrev) )
            return -1;
        Vec_PtrWriteEntry( vFront, k++, pObj );
    }
    if ( k == 0 )
        return -1;
    Vec_PtrShrink( vFront, k );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManTestCutsAlg( Ivy_Man_t * p )
{
    Vec_Ptr_t * vFront;
    Ivy_Obj_t * pObj, * pTemp;
    int i, k, RetValue;
    vFront = Vec_PtrAlloc( 100 );
    Ivy_ManForEachObj( p, pObj, i )
    {
        if ( !Ivy_ObjIsNode(pObj) )
            continue;
        if ( Ivy_ObjIsMuxType(pObj) )
        {
            printf( "m " );
            continue;
        }
        if ( pObj->Id == 509 )
        {
            int y = 0;
        }

        RetValue = Ivy_ManFindAlgCut( pObj, vFront );
        if ( Ivy_ObjIsExor(pObj) )
            printf( "x" );
        if ( RetValue == -1 )
            printf( "Const0 " );
        else if ( RetValue == 1 || Vec_PtrSize(vFront) <= 2 )
            printf( ". " );
        else
            printf( "%d ", Vec_PtrSize(vFront) );
        
        printf( "( " );
        Vec_PtrForEachEntry( vFront, pTemp, k )
            printf( "%d ", Ivy_ObjRefs(Ivy_Regular(pTemp)) );
        printf( ")\n" );

        if ( Vec_PtrSize(vFront) == 5 )
        {
            int x = 0;
        }
    }
    printf( "\n" );
    Vec_PtrFree( vFront );
}




/**Function*************************************************************

  Synopsis    [Computing Boolean cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManFindBoolCut_rec( Ivy_Obj_t * pObj, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vVolume, Ivy_Obj_t * pPivot )
{
    int RetValue0, RetValue1;
    if ( pObj == pPivot )
    {
        Vec_PtrPushUnique( vLeaves, pObj );
        Vec_PtrPushUnique( vVolume, pObj );
        return 1;        
    }
    if ( pObj->fMarkA )
        return 0;

//    assert( !Ivy_ObjIsCi(pObj) );
    if ( Ivy_ObjIsCi(pObj) )
        return 0;

    if ( Ivy_ObjIsBuf(pObj) )
    {
        RetValue0 = Ivy_ManFindBoolCut_rec( Ivy_ObjFanin0(pObj), vLeaves, vVolume, pPivot );
        if ( !RetValue0 )
            return 0;
        Vec_PtrPushUnique( vVolume, pObj );
        return 1;
    }
    assert( Ivy_ObjIsNode(pObj) );
    RetValue0 = Ivy_ManFindBoolCut_rec( Ivy_ObjFanin0(pObj), vLeaves, vVolume, pPivot );
    RetValue1 = Ivy_ManFindBoolCut_rec( Ivy_ObjFanin1(pObj), vLeaves, vVolume, pPivot );
    if ( !RetValue0 && !RetValue1 )
        return 0;
    // add new leaves
    if ( !RetValue0 )
    {
        Vec_PtrPushUnique( vLeaves, Ivy_ObjFanin0(pObj) );
        Vec_PtrPushUnique( vVolume, Ivy_ObjFanin0(pObj) );
    }
    if ( !RetValue1 )
    {
        Vec_PtrPushUnique( vLeaves, Ivy_ObjFanin1(pObj) );
        Vec_PtrPushUnique( vVolume, Ivy_ObjFanin1(pObj) );
    }
    Vec_PtrPushUnique( vVolume, pObj );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns the cost of one node (how many new nodes are added.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManFindBoolCutCost( Ivy_Obj_t * pObj )
{
    int Cost;
    // make sure the node is in the construction zone
    assert( pObj->fMarkA == 1 );  
    // cannot expand over the PI node
    if ( Ivy_ObjIsCi(pObj) )
        return 999;
    // always expand over the buffer
    if ( Ivy_ObjIsBuf(pObj) )
        return !Ivy_ObjFanin0(pObj)->fMarkA;
    // get the cost of the cone
    Cost = (!Ivy_ObjFanin0(pObj)->fMarkA) + (!Ivy_ObjFanin1(pObj)->fMarkA);
    // return the number of nodes to be added to the leaves if this node is removed
    return Cost;
}

/**Function*************************************************************

  Synopsis    [Computing Boolean cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManFindBoolCut( Ivy_Obj_t * pRoot, Vec_Ptr_t * vFront, Vec_Ptr_t * vVolume, Vec_Ptr_t * vLeaves )
{
    Ivy_Obj_t * pObj, * pFaninC, * pFanin0, * pFanin1, * pPivot;
    int RetValue, LevelLimit, Lev, k;
    assert( !Ivy_IsComplement(pRoot) );
    // clear the frontier and collect the nodes
    Vec_PtrClear( vFront );
    Vec_PtrClear( vVolume );
    if ( Ivy_ObjIsMuxType(pRoot) )
        pFaninC = Ivy_ObjRecognizeMux( pRoot, &pFanin0, &pFanin1 );
    else
    {
        pFaninC = NULL;
        pFanin0 = Ivy_ObjFanin0(pRoot);
        pFanin1 = Ivy_ObjFanin1(pRoot); 
    }
    // start cone A
    pFanin0->fMarkA = 1;
    Vec_PtrPush( vFront, pFanin0 );
    Vec_PtrPush( vVolume, pFanin0 );
    // start cone B
    pFanin1->fMarkB = 1;
    Vec_PtrPush( vFront, pFanin1 );
    Vec_PtrPush( vVolume, pFanin1 );
    // iteratively expand until the common node (pPivot) is found or limit is reached
    assert( Ivy_ObjLevel(pRoot) == Ivy_ObjLevelNew(pRoot) );
    pPivot = NULL;
    LevelLimit = IVY_MAX( Ivy_ObjLevel(pRoot) - 10, 1 );
    for ( Lev = Ivy_ObjLevel(pRoot) - 1; Lev >= LevelLimit; Lev-- )
    {
        while ( 1 )
        {
            // find the next node to expand on this level
            Vec_PtrForEachEntry( vFront, pObj, k )
                if ( (int)pObj->Level == Lev )
                    break;
            if ( k == Vec_PtrSize(vFront) )
                break;
            assert( (int)pObj->Level <= Lev );
            assert( pObj->fMarkA ^ pObj->fMarkB );
            // remove the old node
            Vec_PtrRemove( vFront, pObj );

            // expand this node
            pFanin0 = Ivy_ObjFanin0(pObj);
            if ( !pFanin0->fMarkA && !pFanin0->fMarkB )
            {
                Vec_PtrPush( vFront, pFanin0 );
                Vec_PtrPush( vVolume, pFanin0 );
            }
            // mark the new nodes
            if ( pObj->fMarkA )
                pFanin0->fMarkA = 1; 
            if ( pObj->fMarkB )
                pFanin0->fMarkB = 1; 

            if ( Ivy_ObjIsBuf(pObj) )
            {
                if ( pFanin0->fMarkA && pFanin0->fMarkB )
                {
                    pPivot = pFanin0;
                    break;
                }
                continue;
            }

            // expand this node
            pFanin1 = Ivy_ObjFanin1(pObj); 
            if ( !pFanin1->fMarkA && !pFanin1->fMarkB )
            {
                Vec_PtrPush( vFront, pFanin1 );
                Vec_PtrPush( vVolume, pFanin1 );
            }
            // mark the new nodes
            if ( pObj->fMarkA )
                pFanin1->fMarkA = 1; 
            if ( pObj->fMarkB )
                pFanin1->fMarkB = 1; 

            // consider if it is time to quit
            if ( pFanin0->fMarkA && pFanin0->fMarkB )
            {
                pPivot = pFanin0;
                break;
            }
            if ( pFanin1->fMarkA && pFanin1->fMarkB )
            {
                pPivot = pFanin1;
                break;
            }
        }
        if ( pPivot != NULL )
            break;
    }
    if ( pPivot == NULL )
        return 0;
    // if the MUX control is defined, it should not be
    if ( pFaninC && !pFaninC->fMarkA && !pFaninC->fMarkB )
        Vec_PtrPush( vFront, pFaninC );
    // clean the markings
    Vec_PtrForEachEntry( vVolume, pObj, k )
        pObj->fMarkA = pObj->fMarkB = 0;

    // mark the nodes on the frontier (including the pivot)
    Vec_PtrForEachEntry( vFront, pObj, k )
        pObj->fMarkA = 1;
    // cut exists, collect all the nodes on the shortest path to the pivot
    Vec_PtrClear( vLeaves );
    Vec_PtrClear( vVolume );
    RetValue = Ivy_ManFindBoolCut_rec( pRoot, vLeaves, vVolume, pPivot );
    assert( RetValue == 1 );
    // unmark the nodes on the frontier (including the pivot)
    Vec_PtrForEachEntry( vFront, pObj, k )
        pObj->fMarkA = 0;

    // mark the nodes in the volume
    Vec_PtrForEachEntry( vVolume, pObj, k )
        pObj->fMarkA = 1;
    // expand the cut without increasing its size
    while ( 1 )
    {
        Vec_PtrForEachEntry( vLeaves, pObj, k )
            if ( Ivy_ManFindBoolCutCost(pObj) < 2 )
                break;
        if ( k == Vec_PtrSize(vLeaves) )
            break;
        // the node can be expanded
        // remove the old node
        Vec_PtrRemove( vLeaves, pObj );
        // expand this node
        pFanin0 = Ivy_ObjFanin0(pObj);
        if ( !pFanin0->fMarkA )
        {
            pFanin0->fMarkA = 1;
            Vec_PtrPush( vVolume, pFanin0 );
            Vec_PtrPush( vLeaves, pFanin0 );
        }
        if ( Ivy_ObjIsBuf(pObj) )
            continue;
        // expand this node
        pFanin1 = Ivy_ObjFanin1(pObj);
        if ( !pFanin1->fMarkA )
        {
            pFanin1->fMarkA = 1;
            Vec_PtrPush( vVolume, pFanin1 );
            Vec_PtrPush( vLeaves, pFanin1 );
        }        
    }
    // unmark the nodes in the volume
    Vec_PtrForEachEntry( vVolume, pObj, k )
        pObj->fMarkA = 0;
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManTestCutsBool( Ivy_Man_t * p )
{
    Vec_Ptr_t * vFront, * vVolume, * vLeaves;
    Ivy_Obj_t * pObj, * pTemp;
    int i, k, RetValue;
    vFront = Vec_PtrAlloc( 100 );
    vVolume = Vec_PtrAlloc( 100 );
    vLeaves = Vec_PtrAlloc( 100 );
    Ivy_ManForEachObj( p, pObj, i )
    {
        if ( !Ivy_ObjIsNode(pObj) )
            continue;
        if ( Ivy_ObjIsMuxType(pObj) )
        {
            printf( "m" );
            continue;
        }
        if ( Ivy_ObjIsExor(pObj) )
            printf( "x" );
        RetValue = Ivy_ManFindBoolCut( pObj, vFront, vVolume, vLeaves );
        if ( RetValue == 0 )
            printf( "- " );
        else
            printf( "%d ", Vec_PtrSize(vLeaves) );
/*        
        printf( "( " );
        Vec_PtrForEachEntry( vFront, pTemp, k )
            printf( "%d ", Ivy_ObjRefs(Ivy_Regular(pTemp)) );
        printf( ")\n" );
*/
    }
    printf( "\n" );
    Vec_PtrFree( vFront );
    Vec_PtrFree( vVolume );
    Vec_PtrFree( vLeaves );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


