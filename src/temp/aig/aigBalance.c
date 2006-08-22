/**CFile****************************************************************

  FileName    [aigBalance.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Minimalistic And-Inverter Graph package.]

  Synopsis    [Algebraic AIG balancing.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: aigBalance.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/
 
#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Aig_Obj_t * Aig_NodeBalance_rec( Aig_Man_t * pNew, Aig_Obj_t * pObj, Vec_Vec_t * vStore, int Level, int fUpdateLevel );
static Vec_Ptr_t * Aig_NodeBalanceCone( Aig_Obj_t * pObj, Vec_Vec_t * vStore, int Level );
static int         Aig_NodeBalanceFindLeft( Vec_Ptr_t * vSuper );
static void        Aig_NodeBalancePermute( Aig_Man_t * p, Vec_Ptr_t * vSuper, int LeftBound, int fExor );
static void        Aig_NodeBalancePushUniqueOrderByLevel( Vec_Ptr_t * vStore, Aig_Obj_t * pObj );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs algebraic balancing of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManBalance( Aig_Man_t * p, int fUpdateLevel )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pObjNew;
    Vec_Vec_t * vStore;
    int i;
    // create the new manager 
    pNew = Aig_ManStart();
    pNew->fRefCount = 0;
    // map the PI nodes
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // balance the AIG
    vStore = Vec_VecAlloc( 50 );
    Aig_ManForEachPo( p, pObj, i )
    {
        pObjNew = Aig_NodeBalance_rec( pNew, Aig_ObjFanin0(pObj), vStore, 0, fUpdateLevel );
        Aig_ObjCreatePo( pNew, Aig_NotCond( pObjNew, Aig_ObjFaninC0(pObj) ) );
    }
    Vec_VecFree( vStore );
    // remove dangling nodes
//    Aig_ManCreateRefs( pNew );
//    if ( i = Aig_ManCleanup( pNew ) )
//        printf( "Cleanup after balancing removed %d dangling nodes.\n", i );
    // check the resulting AIG
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManBalance(): The check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns the new node constructed.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_NodeBalance_rec( Aig_Man_t * pNew, Aig_Obj_t * pObjOld, Vec_Vec_t * vStore, int Level, int fUpdateLevel )
{
    Aig_Obj_t * pObjNew;
    Vec_Ptr_t * vSuper;
    int i;
    assert( !Aig_IsComplement(pObjOld) );
    // return if the result is known
    if ( pObjOld->pData )
        return pObjOld->pData;
    assert( Aig_ObjIsNode(pObjOld) );
    // get the implication supergate
    vSuper = Aig_NodeBalanceCone( pObjOld, vStore, Level );
    // check if supergate contains two nodes in the opposite polarity
    if ( vSuper->nSize == 0 )
        return pObjOld->pData = Aig_ManConst0(pNew);
    if ( Vec_PtrSize(vSuper) < 2 )
        printf( "BUG!\n" );
    // for each old node, derive the new well-balanced node
    for ( i = 0; i < Vec_PtrSize(vSuper); i++ )
    {
        pObjNew = Aig_NodeBalance_rec( pNew, Aig_Regular(vSuper->pArray[i]), vStore, Level + 1, fUpdateLevel );
        vSuper->pArray[i] = Aig_NotCond( pObjNew, Aig_IsComplement(vSuper->pArray[i]) );
    }
    // build the supergate
    pObjNew = Aig_NodeBalanceBuildSuper( pNew, vSuper, Aig_ObjType(pObjOld), fUpdateLevel );
    // make sure the balanced node is not assigned
//    assert( pObjOld->Level >= Aig_Regular(pObjNew)->Level );
    assert( pObjOld->pData == NULL );
    return pObjOld->pData = pObjNew;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes of the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeBalanceCone_rec( Aig_Obj_t * pRoot, Aig_Obj_t * pObj, Vec_Ptr_t * vSuper )
{
    int RetValue1, RetValue2, i;
    // check if the node is visited
    if ( Aig_Regular(pObj)->fMarkB )
    {
        // check if the node occurs in the same polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == pObj )
                return 1;
        // check if the node is present in the opposite polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == Aig_Not(pObj) )
                return -1;
        assert( 0 );
        return 0;
    }
    // if the new node is complemented or a PI, another gate begins
    if ( pObj != pRoot && (Aig_IsComplement(pObj) || Aig_ObjType(pObj) != Aig_ObjType(pRoot) || Aig_ObjRefs(pObj) > 1) )
    {
        Vec_PtrPush( vSuper, pObj );
        Aig_Regular(pObj)->fMarkB = 1;
        return 0;
    }
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_ObjIsNode(pObj) );
    // go through the branches
    RetValue1 = Aig_NodeBalanceCone_rec( pRoot, Aig_ObjChild0(pObj), vSuper );
    RetValue2 = Aig_NodeBalanceCone_rec( pRoot, Aig_ObjChild1(pObj), vSuper );
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
Vec_Ptr_t * Aig_NodeBalanceCone( Aig_Obj_t * pObj, Vec_Vec_t * vStore, int Level )
{
    Vec_Ptr_t * vNodes;
    int RetValue, i;
    assert( !Aig_IsComplement(pObj) );
    // extend the storage
    if ( Vec_VecSize( vStore ) <= Level )
        Vec_VecPush( vStore, Level, 0 );
    // get the temporary array of nodes
    vNodes = Vec_VecEntry( vStore, Level );
    Vec_PtrClear( vNodes );
    // collect the nodes in the implication supergate
    RetValue = Aig_NodeBalanceCone_rec( pObj, pObj, vNodes );
    assert( vNodes->nSize > 1 );
    // unmark the visited nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Aig_Regular(pObj)->fMarkB = 0;
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
int Aig_NodeCompareLevelsDecrease( Aig_Obj_t ** pp1, Aig_Obj_t ** pp2 )
{
    int Diff = Aig_ObjLevel(Aig_Regular(*pp1)) - Aig_ObjLevel(Aig_Regular(*pp2));
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
Aig_Obj_t * Aig_NodeBalanceBuildSuper( Aig_Man_t * p, Vec_Ptr_t * vSuper, Aig_Type_t Type, int fUpdateLevel )
{
    Aig_Obj_t * pObj1, * pObj2;
    int LeftBound;
    assert( vSuper->nSize > 1 );
    // sort the new nodes by level in the decreasing order
    Vec_PtrSort( vSuper, Aig_NodeCompareLevelsDecrease );
    // balance the nodes
    while ( vSuper->nSize > 1 )
    {
        // find the left bound on the node to be paired
        LeftBound = (!fUpdateLevel)? 0 : Aig_NodeBalanceFindLeft( vSuper );
        // find the node that can be shared (if no such node, randomize choice)
        Aig_NodeBalancePermute( p, vSuper, LeftBound, Type == AIG_EXOR );
        // pull out the last two nodes
        pObj1 = Vec_PtrPop(vSuper);
        pObj2 = Vec_PtrPop(vSuper);
        Aig_NodeBalancePushUniqueOrderByLevel( vSuper, Aig_Oper(p, pObj1, pObj2, Type) );
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
int Aig_NodeBalanceFindLeft( Vec_Ptr_t * vSuper )
{
    Aig_Obj_t * pObjRight, * pObjLeft;
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
        if ( Aig_ObjLevel(Aig_Regular(pObjLeft)) != Aig_ObjLevel(Aig_Regular(pObjRight)) )
            break;
    }
    Current++;    
    // get the node, for which the equality holds
    pObjLeft = Vec_PtrEntry( vSuper, Current );
    assert( Aig_ObjLevel(Aig_Regular(pObjLeft)) == Aig_ObjLevel(Aig_Regular(pObjRight)) );
    return Current;
}

/**Function*************************************************************

  Synopsis    [Moves closer to the end the node that is best for sharing.]

  Description [If there is no node with sharing, randomly chooses one of 
  the legal nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeBalancePermute( Aig_Man_t * p, Vec_Ptr_t * vSuper, int LeftBound, int fExor )
{
    Aig_Obj_t * pObj1, * pObj2, * pObj3, * pGhost;
    int RightBound, i;
    // get the right bound
    RightBound = Vec_PtrSize(vSuper) - 2;
    assert( LeftBound <= RightBound );
    if ( LeftBound == RightBound )
        return;
    // get the two last nodes
    pObj1 = Vec_PtrEntry( vSuper, RightBound + 1 );
    pObj2 = Vec_PtrEntry( vSuper, RightBound     );
    if ( Aig_Regular(pObj1) == p->pConst1 || Aig_Regular(pObj2) == p->pConst1 )
        return;
    // find the first node that can be shared
    for ( i = RightBound; i >= LeftBound; i-- )
    {
        pObj3 = Vec_PtrEntry( vSuper, i );
        if ( Aig_Regular(pObj3) == p->pConst1 )
        {
            Vec_PtrWriteEntry( vSuper, i,          pObj2 );
            Vec_PtrWriteEntry( vSuper, RightBound, pObj3 );
            return;
        }
        pGhost = Aig_ObjCreateGhost( p, pObj1, pObj3, fExor? AIG_EXOR : AIG_AND );
        if ( Aig_TableLookup( p, pGhost ) )
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
void Aig_NodeBalancePushUniqueOrderByLevel( Vec_Ptr_t * vStore, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObj1, * pObj2;
    int i;
    if ( Vec_PtrPushUnique(vStore, pObj) )
        return;
    // find the p of the node
    for ( i = vStore->nSize-1; i > 0; i-- )
    {
        pObj1 = vStore->pArray[i  ];
        pObj2 = vStore->pArray[i-1];
        if ( Aig_ObjLevel(Aig_Regular(pObj1)) <= Aig_ObjLevel(Aig_Regular(pObj2)) )
            break;
        vStore->pArray[i  ] = pObj2;
        vStore->pArray[i-1] = pObj1;
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


