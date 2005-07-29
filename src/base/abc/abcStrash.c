/**CFile****************************************************************

  FileName    [aigStrash.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Strashing of the current network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigStrash.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "extra.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// static functions
static void        Abc_NtkStrashPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkAig );
static Abc_Obj_t * Abc_NodeStrash( Abc_Aig_t * pMan, Abc_Obj_t * pNode );
static Abc_Obj_t * Abc_NodeStrashSop( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Abc_Obj_t * Abc_NodeStrashFactor( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop );

static void        Abc_NtkBalancePerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkAig, bool fDuplicate );
static Abc_Obj_t * Abc_NodeBalance_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, bool fDuplicate );
static Vec_Ptr_t * Abc_NodeBalanceCone( Abc_Obj_t * pNode, int fDuplicate );

extern char *      Mio_GateReadSop( void * pGate );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the strashed AIG network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStrash( Abc_Ntk_t * pNtk )
{
    int fCheck = 1;
    Abc_Ntk_t * pNtkAig;
    assert( !Abc_NtkIsNetlist(pNtk) );
    if ( Abc_NtkIsLogicBdd(pNtk) )
    {
//        printf( "Converting node functions from BDD to SOP.\n" );
        Abc_NtkBddToSop(pNtk);
    }
    // print warning about choice nodes
    if ( Abc_NtkCountChoiceNodes( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );
    // perform strashing
    pNtkAig = Abc_NtkStartFrom( pNtk, ABC_NTK_AIG );
    Abc_NtkStrashPerform( pNtk, pNtkAig );
    Abc_NtkFinalize( pNtk, pNtkAig );
    // print warning about self-feed latches
    if ( Abc_NtkCountSelfFeedLatches(pNtkAig) )
        printf( "The network has %d self-feeding latches.\n", Abc_NtkCountSelfFeedLatches(pNtkAig) );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkStrash( pNtk->pExdc );
    // make sure everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkStrash: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Prepares the network for strashing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkStrashPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew )
{
    ProgressBar * pProgress;
    Abc_Aig_t * pMan = pNtkNew->pManFunc;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pNodeNew, * pObj;
    int i;

    // perform strashing
    vNodes = Abc_NtkDfs( pNtk );
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    for ( i = 0; i < vNodes->nSize; i++ )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // get the node
        pNode = vNodes->pArray[i];
        assert( Abc_ObjIsNode(pNode) );
         // strash the node
        pNodeNew = Abc_NodeStrash( pMan, pNode );
        // get the old object
        if ( Abc_NtkIsNetlist(pNtk) )
            pObj = Abc_ObjFanout0( pNode ); // the fanout net 
        else 
            pObj = vNodes->pArray[i]; // the node itself
        // make sure the node is not yet strashed
        assert( pObj->pCopy == NULL );
        // mark the old object with the new AIG node
        pObj->pCopy = pNodeNew;
    }
    Vec_PtrFree( vNodes );
    Extra_ProgressBarStop( pProgress );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrash( Abc_Aig_t * pMan, Abc_Obj_t * pNode )
{
    int fUseFactor = 1;
    char * pSop;

    assert( Abc_ObjIsNode(pNode) );

    // consider the case when the graph is an AIG
    if ( Abc_NtkIsAig(pNode->pNtk) )
    {
//        Abc_Obj_t * pChild0, * pChild1;
//        pChild0 = Abc_ObjFanin0(pNode);
//        pChild1 = Abc_ObjFanin1(pNode);
        if ( Abc_NodeIsConst(pNode) )
            return Abc_AigConst1(pMan);
        return Abc_AigAnd( pMan, 
            Abc_ObjNotCond( Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) ),
            Abc_ObjNotCond( Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) )  );
    }

    // get the SOP of the node
    if ( Abc_NtkIsLogicMap(pNode->pNtk) )
        pSop = Mio_GateReadSop(pNode->pData);
    else
        pSop = pNode->pData;

    // consider the cconstant node
    if ( Abc_NodeIsConst(pNode) )
    {
        // check if the SOP is constant
        if ( Abc_SopIsConst1(pSop) )
            return Abc_AigConst1(pMan);
        return Abc_ObjNot( Abc_AigConst1(pMan) );
    }

    // decide when to use factoring
    if ( fUseFactor && Abc_ObjFaninNum(pNode) > 2 && Abc_SopGetCubeNum(pSop) > 1 )
        return Abc_NodeStrashFactor( pMan, pNode, pSop );
    return Abc_NodeStrashSop( pMan, pNode, pSop );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrashSop( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin, * pAnd, * pSum;
    Abc_Obj_t * pConst1 = Abc_AigConst1(pMan);
    char * pCube;
    int i, nFanins;

    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Abc_ObjNot(pConst1);
    Abc_SopForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = pConst1;
        Abc_ObjForEachFanin( pNode, pFanin, i ) // pFanin can be a net
        {
            if ( pCube[i] == '1' )
                pAnd = Abc_AigAnd( pMan, pAnd, pFanin->pCopy );
            else if ( pCube[i] == '0' )
                pAnd = Abc_AigAnd( pMan, pAnd, Abc_ObjNot(pFanin->pCopy) );
        }
        // add to the sum of cubes
        pSum = Abc_AigOr( pMan, pSum, pAnd );
    }
    // decide whether to complement the result
    pCube = pSop;
    if ( pCube[nFanins + 1] == '0' )
        pSum = Abc_ObjNot(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeStrashFactor( Abc_Aig_t * pMan, Abc_Obj_t * pRoot, char * pSop )
{
    Vec_Int_t * vForm;
    Vec_Ptr_t * vAnds;
    Abc_Obj_t * pAnd, * pAnd0, * pAnd1, * pFanin;
    Ft_Node_t * pFtNode;
    int i, nVars;

    // derive the factored form
    vForm = Ft_Factor( pSop );

    // sanity checks
    nVars = Ft_FactorGetNumVars( vForm );
    assert( nVars >= 0 );
    assert( vForm->nSize > nVars );
    assert( nVars == Abc_ObjFaninNum(pRoot) );

    // check for constant Andtion
    pFtNode = Ft_NodeRead( vForm, 0 );
    if ( pFtNode->fConst )
    {
        Vec_IntFree( vForm );
        return Abc_ObjNotCond( Abc_AigConst1(pMan), pFtNode->fCompl );
    }

    // start the array of elementary variables
    vAnds = Vec_PtrAlloc( 20 );
    Abc_ObjForEachFanin( pRoot, pFanin, i )
        Vec_PtrPush( vAnds, pFanin->pCopy );

    // compute the Andtions of other nodes
    for ( i = nVars; i < vForm->nSize; i++ )
    {
        pFtNode = Ft_NodeRead( vForm, i );
        pAnd0   = Abc_ObjNotCond( vAnds->pArray[pFtNode->iFanin0], pFtNode->fCompl0 ); 
        pAnd1   = Abc_ObjNotCond( vAnds->pArray[pFtNode->iFanin1], pFtNode->fCompl1 ); 
        pAnd    = Abc_AigAnd( pMan, pAnd0, pAnd1 );
        Vec_PtrPush( vAnds, pAnd );
    }
    assert( vForm->nSize = vAnds->nSize );
    Vec_PtrFree( vAnds );

    // complement the result if necessary
    pFtNode = Ft_NodeReadLast( vForm );
    pAnd = Abc_ObjNotCond( pAnd, pFtNode->fCompl );
    Vec_IntFree( vForm );
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Appends the second network to the first.]

  Description [Modifies the first network by adding the logic of the second. 
  Does not add the COs of the second. Does not change the second network.
  Returns 0 if the appending failed, 1 otherise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    int fCheck = 1;
    Abc_Obj_t * pObj;
    int i;
    // the first network should be an AIG
    assert( Abc_NtkIsAig(pNtk1) );
    assert( Abc_NtkIsLogic(pNtk2) || Abc_NtkIsAig(pNtk2) ); 
    if ( Abc_NtkIsLogicBdd(pNtk2) )
    {
//        printf( "Converting node functions from BDD to SOP.\n" );
        Abc_NtkBddToSop(pNtk2);
    }
    // check that the networks have the same PIs
    // reorder PIs of pNtk2 according to pNtk1
    if ( !Abc_NtkCompareSignals( pNtk1, pNtk2, 1 ) )
        return 0;
    // perform strashing
    Abc_NtkCleanCopy( pNtk2 );
    Abc_NtkForEachCi( pNtk2, pObj, i )
        pObj->pCopy = Abc_NtkCi(pNtk1, i); 
    // add pNtk2 to pNtk1 while strashing
    Abc_NtkStrashPerform( pNtk2, pNtk1 );
    // make sure that everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtk1 ) )
    {
        printf( "Abc_NtkAppend: The network check has failed.\n" );
        return 0;
    }
    return 1;
}




/**Function*************************************************************

  Synopsis    [Balances the AIG network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkBalance( Abc_Ntk_t * pNtk, bool fDuplicate )
{
    int fCheck = 1;
    Abc_Ntk_t * pNtkAig;
    assert( Abc_NtkIsAig(pNtk) );
    // perform balancing
    pNtkAig = Abc_NtkStartFrom( pNtk, ABC_NTK_AIG );
    Abc_NtkBalancePerform( pNtk, pNtkAig, fDuplicate );
    Abc_NtkFinalize( pNtk, pNtkAig );
    // make sure everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtkAig ) )
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
    Abc_Obj_t * pNode, * pDriver;
    int i;

    // copy the constant node
    Abc_AigConst1(pNtk->pManFunc)->pCopy = Abc_AigConst1(pNtkAig->pManFunc);
    // set the level of PIs of AIG according to the arrival times of the old network
    Abc_NtkSetNodeLevelsArrival( pNtk );
    // perform balancing of POs
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // strash the driver node
        pDriver = Abc_ObjFanin0(pNode);
        Abc_NodeBalance_rec( pNtkAig, pDriver, fDuplicate );
    }
    Extra_ProgressBarStop( pProgress );
}

/**Function*************************************************************

  Synopsis    [Rebalances the multi-input node rooted at pNodeOld.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeBalance_rec( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNodeOld, bool fDuplicate )
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
    vSuper = Abc_NodeBalanceCone( pNodeOld, fDuplicate );
    if ( vSuper->nSize == 0 )
    { // it means that the supergate contains two nodes in the opposite polarity
        Vec_PtrFree( vSuper );
        pNodeOld->pCopy = Abc_ObjNot(Abc_AigConst1(pMan));
        return pNodeOld->pCopy;
    }
    // for each old node, derive the new well-balanced node
    for ( i = 0; i < vSuper->nSize; i++ )
    {
        pNodeNew = Abc_NodeBalance_rec( pNtkNew, Abc_ObjRegular(vSuper->pArray[i]), fDuplicate );
        vSuper->pArray[i] = Abc_ObjNotCond( pNodeNew, Abc_ObjIsComplement(vSuper->pArray[i]) );
    }
    // sort the new nodes by level in the decreasing order
    Vec_PtrSort( vSuper, Abc_NodeCompareLevelsDecrease );
    // balance the nodes
    assert( vSuper->nSize > 1 );
    while ( vSuper->nSize > 1 )
    {
        pNode1 = Vec_PtrPop(vSuper);
        pNode2 = Vec_PtrPop(vSuper);
        Abc_VecObjPushUniqueOrderByLevel( vSuper, Abc_AigAnd(pMan, pNode1, pNode2) );
    }
    // make sure the balanced node is not assigned
    assert( pNodeOld->pCopy == NULL );
    // mark the old node with the new node
    pNodeOld->pCopy = vSuper->pArray[0];
    Vec_PtrFree( vSuper );
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
int Abc_NodeBalanceCone_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vSuper, bool fFirst, bool fDuplicate )
{
    Abc_Obj_t * p0, * p1;
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
    // get the children
    p0 = Abc_ObjNotCond( Abc_ObjFanin0(pNode), Abc_ObjFaninC0(pNode) );
    p1 = Abc_ObjNotCond( Abc_ObjFanin1(pNode), Abc_ObjFaninC1(pNode) );
    // go through the branches
    RetValue1 = Abc_NodeBalanceCone_rec( p0, vSuper, 0, fDuplicate );
    RetValue2 = Abc_NodeBalanceCone_rec( p1, vSuper, 0, fDuplicate );
    if ( RetValue1 == -1 || RetValue2 == -1 )
        return -1;
    // return 1 if at least one branch has a duplicate
    return RetValue1 || RetValue2;
}

/**Function*************************************************************

  Synopsis    [Collects the nodes in the cone delimited by fMarkA==1.]

  Description [Returns -1 if the AND-cone has the same node in both polarities.
  Returns 1 if the AND-cone has the same node in the same polarity. Returns 0
  if the AND-cone has no repeated nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NodeBalanceCone( Abc_Obj_t * pNode, int fDuplicate )
{
    Vec_Ptr_t * vNodes;
    int RetValue, i;
    assert( !Abc_ObjIsComplement(pNode) );
    vNodes = Vec_PtrAlloc( 4 );
    RetValue = Abc_NodeBalanceCone_rec( pNode, vNodes, 1, fDuplicate );
    assert( vNodes->nSize > 0 );
    for ( i = 0; i < vNodes->nSize; i++ )
        Abc_ObjRegular((Abc_Obj_t *)vNodes->pArray[i])->fMarkB = 0;
    if ( RetValue == -1 )
        vNodes->nSize = 0;
    return vNodes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


