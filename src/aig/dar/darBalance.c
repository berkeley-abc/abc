/**CFile****************************************************************

  FileName    [darBalance.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Algebraic AIG balancing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darBalance.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Dar_Obj_t * Dar_NodeBalance_rec( Dar_Man_t * pNew, Dar_Obj_t * pObj, Vec_Vec_t * vStore, int Level, int fUpdateLevel );
static Vec_Ptr_t * Dar_NodeBalanceCone( Dar_Obj_t * pObj, Vec_Vec_t * vStore, int Level );
static int         Dar_NodeBalanceFindLeft( Vec_Ptr_t * vSuper );
static void        Dar_NodeBalancePermute( Dar_Man_t * p, Vec_Ptr_t * vSuper, int LeftBound, int fExor );
static void        Dar_NodeBalancePushUniqueOrderByLevel( Vec_Ptr_t * vStore, Dar_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs algebraic balancing of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Man_t * Dar_ManBalance( Dar_Man_t * p, int fUpdateLevel )
{
    Dar_Man_t * pNew;
    Dar_Obj_t * pObj, * pObjNew;
    Vec_Vec_t * vStore;
    int i;
    // create the new manager 
    pNew = Dar_ManStart();
    // map the PI nodes
    Dar_ManCleanData( p );
    Dar_ManConst1(p)->pData = Dar_ManConst1(pNew);
    Dar_ManForEachPi( p, pObj, i )
        pObj->pData = Dar_ObjCreatePi(pNew);
    // balance the AIG
    vStore = Vec_VecAlloc( 50 );
    Dar_ManForEachPo( p, pObj, i )
    {
        pObjNew = Dar_NodeBalance_rec( pNew, Dar_ObjFanin0(pObj), vStore, 0, fUpdateLevel );
        Dar_ObjCreatePo( pNew, Dar_NotCond( pObjNew, Dar_ObjFaninC0(pObj) ) );
    }
    Vec_VecFree( vStore );
    // remove dangling nodes
//    Dar_ManCreateRefs( pNew );
//    if ( i = Dar_ManCleanup( pNew ) )
//        printf( "Cleanup after balancing removed %d dangling nodes.\n", i );
    // check the resulting AIG
    if ( !Dar_ManCheck(pNew) )
        printf( "Dar_ManBalance(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns the new node constructed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_NodeBalance_rec( Dar_Man_t * pNew, Dar_Obj_t * pObjOld, Vec_Vec_t * vStore, int Level, int fUpdateLevel )
{
    Dar_Obj_t * pObjNew;
    Vec_Ptr_t * vSuper;
    int i;
    assert( !Dar_IsComplement(pObjOld) );
    // return if the result is known
    if ( pObjOld->pData )
        return pObjOld->pData;
    assert( Dar_ObjIsNode(pObjOld) );
    // get the implication supergate
    vSuper = Dar_NodeBalanceCone( pObjOld, vStore, Level );
    // check if supergate contains two nodes in the opposite polarity
    if ( vSuper->nSize == 0 )
        return pObjOld->pData = Dar_ManConst0(pNew);
    if ( Vec_PtrSize(vSuper) < 2 )
        printf( "BUG!\n" );
    // for each old node, derive the new well-balanced node
    for ( i = 0; i < Vec_PtrSize(vSuper); i++ )
    {
        pObjNew = Dar_NodeBalance_rec( pNew, Dar_Regular(vSuper->pArray[i]), vStore, Level + 1, fUpdateLevel );
        vSuper->pArray[i] = Dar_NotCond( pObjNew, Dar_IsComplement(vSuper->pArray[i]) );
    }
    // build the supergate
    pObjNew = Dar_NodeBalanceBuildSuper( pNew, vSuper, Dar_ObjType(pObjOld), fUpdateLevel );
    // make sure the balanced node is not assigned
//    assert( pObjOld->Level >= Dar_Regular(pObjNew)->Level );
    assert( pObjOld->pData == NULL );
    return pObjOld->pData = pObjNew;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes of the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_NodeBalanceCone_rec( Dar_Obj_t * pRoot, Dar_Obj_t * pObj, Vec_Ptr_t * vSuper )
{
    int RetValue1, RetValue2, i;
    // check if the node is visited
    if ( Dar_Regular(pObj)->fMarkB )
    {
        // check if the node occurs in the same polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == pObj )
                return 1;
        // check if the node is present in the opposite polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == Dar_Not(pObj) )
                return -1;
        assert( 0 );
        return 0;
    }
    // if the new node is complemented or a PI, another gate begins
    if ( pObj != pRoot && (Dar_IsComplement(pObj) || Dar_ObjType(pObj) != Dar_ObjType(pRoot) || Dar_ObjRefs(pObj) > 1) )
    {
        Vec_PtrPush( vSuper, pObj );
        Dar_Regular(pObj)->fMarkB = 1;
        return 0;
    }
    assert( !Dar_IsComplement(pObj) );
    assert( Dar_ObjIsNode(pObj) );
    // go through the branches
    RetValue1 = Dar_NodeBalanceCone_rec( pRoot, Dar_ObjChild0(pObj), vSuper );
    RetValue2 = Dar_NodeBalanceCone_rec( pRoot, Dar_ObjChild1(pObj), vSuper );
    if ( RetValue1 == -1 || RetValue2 == -1 )
        return -1;
    // return 1 if at least one branch has a duplicate
    return RetValue1 || RetValue2;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes of the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Dar_NodeBalanceCone( Dar_Obj_t * pObj, Vec_Vec_t * vStore, int Level )
{
    Vec_Ptr_t * vNodes;
    int RetValue, i;
    assert( !Dar_IsComplement(pObj) );
    // extend the storage
    if ( Vec_VecSize( vStore ) <= Level )
        Vec_VecPush( vStore, Level, 0 );
    // get the temporary array of nodes
    vNodes = Vec_VecEntry( vStore, Level );
    Vec_PtrClear( vNodes );
    // collect the nodes in the implication supergate
    RetValue = Dar_NodeBalanceCone_rec( pObj, pObj, vNodes );
    assert( vNodes->nSize > 1 );
    // unmark the visited nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Dar_Regular(pObj)->fMarkB = 0;
    // if we found the node and its complement in the same implication supergate, 
    // return empty set of nodes (meaning that we should use constant-0 node)
    if ( RetValue == -1 )
        vNodes->nSize = 0;
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Procedure used for sorting the nodes in decreasing order of levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_NodeCompareLevelsDecrease( Dar_Obj_t ** pp1, Dar_Obj_t ** pp2 )
{
    int Diff = Dar_ObjLevel(Dar_Regular(*pp1)) - Dar_ObjLevel(Dar_Regular(*pp2));
    if ( Diff > 0 )
        return -1;
    if ( Diff < 0 ) 
        return 1;
    return 0; 
}

/**Function*************************************************************

  Synopsis    [Builds implication supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dar_Obj_t * Dar_NodeBalanceBuildSuper( Dar_Man_t * p, Vec_Ptr_t * vSuper, Dar_Type_t Type, int fUpdateLevel )
{
    Dar_Obj_t * pObj1, * pObj2;
    int LeftBound;
    assert( vSuper->nSize > 1 );
    // sort the new nodes by level in the decreasing order
    Vec_PtrSort( vSuper, Dar_NodeCompareLevelsDecrease );
    // balance the nodes
    while ( vSuper->nSize > 1 )
    {
        // find the left bound on the node to be paired
        LeftBound = (!fUpdateLevel)? 0 : Dar_NodeBalanceFindLeft( vSuper );
        // find the node that can be shared (if no such node, randomize choice)
        Dar_NodeBalancePermute( p, vSuper, LeftBound, Type == DAR_AIG_EXOR );
        // pull out the last two nodes
        pObj1 = Vec_PtrPop(vSuper);
        pObj2 = Vec_PtrPop(vSuper);
        Dar_NodeBalancePushUniqueOrderByLevel( vSuper, Dar_Oper(p, pObj1, pObj2, Type) );
    }
    return Vec_PtrEntry(vSuper, 0);
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
int Dar_NodeBalanceFindLeft( Vec_Ptr_t * vSuper )
{
    Dar_Obj_t * pObjRight, * pObjLeft;
    int Current;
    // if two or less nodes, pair with the first
    if ( Vec_PtrSize(vSuper) < 3 )
        return 0;
    // set the pointer to the one before the last
    Current = Vec_PtrSize(vSuper) - 2;
    pObjRight = Vec_PtrEntry( vSuper, Current );
    // go through the nodes to the left of this one
    for ( Current--; Current >= 0; Current-- )
    {
        // get the next node on the left
        pObjLeft = Vec_PtrEntry( vSuper, Current );
        // if the level of this node is different, quit the loop
        if ( Dar_ObjLevel(Dar_Regular(pObjLeft)) != Dar_ObjLevel(Dar_Regular(pObjRight)) )
            break;
    }
    Current++;    
    // get the node, for which the equality holds
    pObjLeft = Vec_PtrEntry( vSuper, Current );
    assert( Dar_ObjLevel(Dar_Regular(pObjLeft)) == Dar_ObjLevel(Dar_Regular(pObjRight)) );
    return Current;
}

/**Function*************************************************************

  Synopsis    [Moves closer to the end the node that is best for sharing.]

  Description [If there is no node with sharing, randomly chooses one of 
  the legal nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_NodeBalancePermute( Dar_Man_t * p, Vec_Ptr_t * vSuper, int LeftBound, int fExor )
{
    Dar_Obj_t * pObj1, * pObj2, * pObj3, * pGhost;
    int RightBound, i;
    // get the right bound
    RightBound = Vec_PtrSize(vSuper) - 2;
    assert( LeftBound <= RightBound );
    if ( LeftBound == RightBound )
        return;
    // get the two last nodes
    pObj1 = Vec_PtrEntry( vSuper, RightBound + 1 );
    pObj2 = Vec_PtrEntry( vSuper, RightBound     );
    if ( Dar_Regular(pObj1) == p->pConst1 || Dar_Regular(pObj2) == p->pConst1 )
        return;
    // find the first node that can be shared
    for ( i = RightBound; i >= LeftBound; i-- )
    {
        pObj3 = Vec_PtrEntry( vSuper, i );
        if ( Dar_Regular(pObj3) == p->pConst1 )
        {
            Vec_PtrWriteEntry( vSuper, i,          pObj2 );
            Vec_PtrWriteEntry( vSuper, RightBound, pObj3 );
            return;
        }
        pGhost = Dar_ObjCreateGhost( p, pObj1, pObj3, fExor? DAR_AIG_EXOR : DAR_AIG_AND );
        if ( Dar_TableLookup( p, pGhost ) )
        {
            if ( pObj3 == pObj2 )
                return;
            Vec_PtrWriteEntry( vSuper, i,          pObj2 );
            Vec_PtrWriteEntry( vSuper, RightBound, pObj3 );
            return;
        }
    }
/*
    // we did not find the node to share, randomize choice
    {
        int Choice = rand() % (RightBound - LeftBound + 1);
        pObj3 = Vec_PtrEntry( vSuper, LeftBound + Choice );
        if ( pObj3 == pObj2 )
            return;
        Vec_PtrWriteEntry( vSuper, LeftBound + Choice, pObj2 );
        Vec_PtrWriteEntry( vSuper, RightBound,         pObj3 );
    }
*/
}

/**Function*************************************************************

  Synopsis    [Inserts a new node in the order by levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_NodeBalancePushUniqueOrderByLevel( Vec_Ptr_t * vStore, Dar_Obj_t * pObj )
{
    Dar_Obj_t * pObj1, * pObj2;
    int i;
    if ( Vec_PtrPushUnique(vStore, pObj) )
        return;
    // find the p of the node
    for ( i = vStore->nSize-1; i > 0; i-- )
    {
        pObj1 = vStore->pArray[i  ];
        pObj2 = vStore->pArray[i-1];
        if ( Dar_ObjLevel(Dar_Regular(pObj1)) <= Dar_ObjLevel(Dar_Regular(pObj2)) )
            break;
        vStore->pArray[i  ] = pObj2;
        vStore->pArray[i-1] = pObj1;
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


