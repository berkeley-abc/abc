/**CFile****************************************************************

  FileName    [abcBalance.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Performs global balancing of the AIG by the number of levels.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcBalance.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
static void        Abc_NtkBalancePerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkAig, bool fDuplicate );
static Abc_Obj_t * Abc_NodeBalance_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, Vec_Vec_t * vStorage, int Level, bool fDuplicate );
static Vec_Ptr_t * Abc_NodeBalanceCone( Abc_Obj_t * pNode, Vec_Vec_t * vSuper, int Level, int fDuplicate );
static int         Abc_NodeBalanceCone_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vSuper, bool fFirst, bool fDuplicate );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Balances the AIG network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkBalance( Abc_Ntk_t * pNtk, bool fDuplicate )
{
    Abc_Ntk_t * pNtkAig;
    assert( Abc_NtkIsStrash(pNtk) );
    // perform balancing
    pNtkAig = Abc_NtkStartFrom( pNtk, ABC_NTK_STRASH, ABC_FUNC_AIG );
    Abc_NtkBalancePerform( pNtk, pNtkAig, fDuplicate );
    Abc_NtkFinalize( pNtk, pNtkAig );
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkDup( pNtk->pExdc );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkBalance: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Balances the AIG network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBalancePerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkAig, bool fDuplicate )
{
    int fCheck = 1;
    ProgressBar * pProgress;
    Vec_Vec_t * vStorage;
    Abc_Obj_t * pNode, * pDriver;
    int i;

    // set the level of PIs of AIG according to the arrival times of the old network
    Abc_NtkSetNodeLevelsArrival( pNtk );
    // allocate temporary storage for supergates
    vStorage = Vec_VecStart( 10 );
    // perform balancing of POs
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // strash the driver node
        pDriver = Abc_ObjFanin0(pNode);
        Abc_NodeBalance_rec( pNtkAig, pDriver, vStorage, 0, fDuplicate );
    }
    Extra_ProgressBarStop( pProgress );
    Vec_VecFree( vStorage );
}

/**Function*************************************************************

  Synopsis    [Randomizes the node positions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeBalanceRandomize( Vec_Ptr_t * vSuper )
{
    Abc_Obj_t * pNode1, * pNode2;
    int i, Signature;
    if ( Vec_PtrSize(vSuper) < 3 )
        return;
    pNode1 = Vec_PtrEntry( vSuper, Vec_PtrSize(vSuper)-2 );
    pNode2 = Vec_PtrEntry( vSuper, Vec_PtrSize(vSuper)-3 );
    if ( Abc_ObjRegular(pNode1)->Level != Abc_ObjRegular(pNode2)->Level )
        return;
    // some reordering will be performed
    Signature = rand();
    for ( i = Vec_PtrSize(vSuper)-2; i > 0; i-- )
    {
        pNode1 = Vec_PtrEntry( vSuper, i );
        pNode2 = Vec_PtrEntry( vSuper, i-1 );
        if ( Abc_ObjRegular(pNode1)->Level != Abc_ObjRegular(pNode2)->Level )
            return;
        if ( Signature & (1 << (i % 10)) )
            continue;
        Vec_PtrWriteEntry( vSuper, i,   pNode2 );
        Vec_PtrWriteEntry( vSuper, i-1, pNode1 );
    }
}

/**Function*************************************************************

  Synopsis    [Rebalances the multi-input node rooted at pNodeOld.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeBalance_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNodeOld, Vec_Vec_t * vStorage, int Level, bool fDuplicate )
{
    Abc_Aig_t * pMan = pNtkNew->pManFunc;
    Abc_Obj_t * pNodeNew, * pNode1, * pNode2;
    Vec_Ptr_t * vSuper;
    int i;
    assert( !Abc_ObjIsComplement(pNodeOld) );
    // return if the result if known
    if ( pNodeOld->pCopy )
        return pNodeOld->pCopy;
    assert( Abc_ObjIsNode(pNodeOld) );
    // get the implication supergate
    vSuper = Abc_NodeBalanceCone( pNodeOld, vStorage, Level, fDuplicate );
    if ( vSuper->nSize == 0 )
    { // it means that the supergate contains two nodes in the opposite polarity
        pNodeOld->pCopy = Abc_ObjNot(Abc_NtkConst1(pNtkNew));
        return pNodeOld->pCopy;
    }
    // for each old node, derive the new well-balanced node
    for ( i = 0; i < vSuper->nSize; i++ )
    {
        pNodeNew = Abc_NodeBalance_rec( pNtkNew, Abc_ObjRegular(vSuper->pArray[i]), vStorage, Level + 1, fDuplicate );
        vSuper->pArray[i] = Abc_ObjNotCond( pNodeNew, Abc_ObjIsComplement(vSuper->pArray[i]) );
    }
    if ( vSuper->nSize < 2 )
        printf( "BUG!\n" );
    // sort the new nodes by level in the decreasing order
    Vec_PtrSort( vSuper, Abc_NodeCompareLevelsDecrease );
    // balance the nodes
    assert( vSuper->nSize > 1 );
    while ( vSuper->nSize > 1 )
    {
        // randomize the node positions
//        Abc_NodeBalanceRandomize( vSuper );
        // pull out the last two nodes
        pNode1 = Vec_PtrPop(vSuper);
        pNode2 = Vec_PtrPop(vSuper);
        Abc_VecObjPushUniqueOrderByLevel( vSuper, Abc_AigAnd(pMan, pNode1, pNode2) );
    }
    // make sure the balanced node is not assigned
    assert( pNodeOld->pCopy == NULL );
    // mark the old node with the new node
    pNodeOld->pCopy = vSuper->pArray[0];
    vSuper->nSize = 0;
    return pNodeOld->pCopy;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in the cone delimited by fMarkA==1.]

  Description [Returns -1 if the AND-cone has the same node in both polarities.
  Returns 1 if the AND-cone has the same node in the same polarity. Returns 0
  if the AND-cone has no repeated nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeBalanceCone( Abc_Obj_t * pNode, Vec_Vec_t * vStorage, int Level, int fDuplicate )
{
    Vec_Ptr_t * vNodes;
    int RetValue, i;
    assert( !Abc_ObjIsComplement(pNode) );
    // extend the storage
    if ( Vec_VecSize( vStorage ) <= Level )
        Vec_VecPush( vStorage, Level, 0 );
    // get the temporary array of nodes
    vNodes = Vec_VecEntry( vStorage, Level );
    Vec_PtrClear( vNodes );
    // collect the nodes in the implication supergate
    RetValue = Abc_NodeBalanceCone_rec( pNode, vNodes, 1, fDuplicate );
    assert( vNodes->nSize > 1 );
    // unmark the visited nodes
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjRegular((Abc_Obj_t *)vNodes->pArray[i])->fMarkB = 0;
    // if we found the node and its complement in the same implication supergate, 
    // return empty set of nodes (meaning that we should use constant-0 node)
    if ( RetValue == -1 )
        vNodes->nSize = 0;
    return vNodes;
}


/**Function*************************************************************

  Synopsis    [Collects the nodes in the cone delimited by fMarkA==1.]

  Description [Returns -1 if the AND-cone has the same node in both polarities.
  Returns 1 if the AND-cone has the same node in the same polarity. Returns 0
  if the AND-cone has no repeated nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeBalanceCone_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vSuper, bool fFirst, bool fDuplicate )
{
    int RetValue1, RetValue2, i;
    // check if the node is visited
    if ( Abc_ObjRegular(pNode)->fMarkB )
    {
        // check if the node occurs in the same polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == pNode )
                return 1;
        // check if the node is present in the opposite polarity
        for ( i = 0; i < vSuper->nSize; i++ )
            if ( vSuper->pArray[i] == Abc_ObjNot(pNode) )
                return -1;
        assert( 0 );
        return 0;
    }
    // if the new node is complemented or a PI, another gate begins
    if ( !fFirst && (Abc_ObjIsComplement(pNode) || !Abc_ObjIsNode(pNode) || !fDuplicate && (Abc_ObjFanoutNum(pNode) > 1)) )
    {
        Vec_PtrPush( vSuper, pNode );
        Abc_ObjRegular(pNode)->fMarkB = 1;
        return 0;
    }
    assert( !Abc_ObjIsComplement(pNode) );
    assert( Abc_ObjIsNode(pNode) );
    // go through the branches
    RetValue1 = Abc_NodeBalanceCone_rec( Abc_ObjChild0(pNode), vSuper, 0, fDuplicate );
    RetValue2 = Abc_NodeBalanceCone_rec( Abc_ObjChild1(pNode), vSuper, 0, fDuplicate );
    if ( RetValue1 == -1 || RetValue2 == -1 )
        return -1;
    // return 1 if at least one branch has a duplicate
    return RetValue1 || RetValue2;
}




/**Function*************************************************************

  Synopsis    [Collects the nodes in the implication supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeFindCone_rec( Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNodeC, * pNodeT, * pNodeE;
    int RetValue, i;
    assert( !Abc_ObjIsComplement(pNode) );
    if ( Abc_ObjIsCi(pNode) )
        return NULL;
    // start the new array
    vNodes = Vec_PtrAlloc( 4 );
    // if the node is the MUX collect its fanins
    if ( Abc_NodeIsMuxType(pNode) )
    {
        pNodeC = Abc_NodeRecognizeMux( pNode, &pNodeT, &pNodeE );
        Vec_PtrPush( vNodes, Abc_ObjRegular(pNodeC) );
        Vec_PtrPushUnique( vNodes, Abc_ObjRegular(pNodeT) );
        Vec_PtrPushUnique( vNodes, Abc_ObjRegular(pNodeE) );
    }
    else
    {
        // collect the nodes in the implication supergate
        RetValue = Abc_NodeBalanceCone_rec( pNode, vNodes, 1, 1 );
        assert( vNodes->nSize > 1 );
        // unmark the visited nodes
        Vec_PtrForEachEntry( vNodes, pNode, i )
            Abc_ObjRegular(pNode)->fMarkB = 0;
        // if we found the node and its complement in the same implication supergate, 
        // return empty set of nodes (meaning that we should use constant-0 node)
        if ( RetValue == -1 )
            vNodes->nSize = 0;
    }
    // call for the fanin
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        pNode = Abc_ObjRegular(pNode);
        if ( pNode->pCopy )
            continue;
        pNode->pCopy = (Abc_Obj_t *)Abc_NodeFindCone_rec( pNode );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Attaches the implication supergates to internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBalanceAttach( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        pNode = Abc_ObjFanin0(pNode);
        if ( pNode->pCopy )
            continue;
        pNode->pCopy = (Abc_Obj_t *)Abc_NodeFindCone_rec( pNode );
    }
}

/**Function*************************************************************

  Synopsis    [Attaches the implication supergates to internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBalanceDetach( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( pNode->pCopy )
        {
            Vec_PtrFree( (Vec_Ptr_t *)pNode->pCopy );
            pNode->pCopy = NULL;
        }
}

/**Function*************************************************************

  Synopsis    [Compute levels of implication supergates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkBalanceLevel_rec( Abc_Obj_t * pNode )
{
    Vec_Ptr_t * vSuper;
    Abc_Obj_t * pFanin;
    int i, LevelMax;
    assert( !Abc_ObjIsComplement(pNode) );
    if ( pNode->Level > 0 )
        return pNode->Level;
    if ( Abc_ObjIsCi(pNode) )
        return 0;
    vSuper = (Vec_Ptr_t *)pNode->pCopy;
    assert( vSuper != NULL );
    LevelMax = 0;
    Vec_PtrForEachEntry( vSuper, pFanin, i )
    {
        pFanin = Abc_ObjRegular(pFanin);
        Abc_NtkBalanceLevel_rec(pFanin);
        if ( LevelMax < (int)pFanin->Level )
            LevelMax = pFanin->Level;
    }
    pNode->Level = LevelMax + 1;
    return pNode->Level;
}


/**Function*************************************************************

  Synopsis    [Compute levels of implication supergates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBalanceLevel( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    int i;
    Abc_NtkForEachObj( pNtk, pNode, i )
        pNode->Level = 0;
    Abc_NtkForEachCo( pNtk, pNode, i )
        Abc_NtkBalanceLevel_rec( Abc_ObjFanin0(pNode) );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


