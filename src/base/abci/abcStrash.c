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
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// static functions
static void        Abc_NtkStrashPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkAig, bool fAllNodes );
static Abc_Obj_t * Abc_NodeStrashSop( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Abc_Obj_t * Abc_NodeStrashFactor( Abc_Aig_t * pMan, Abc_Obj_t * pNode, char * pSop );

extern char *      Mio_GateReadSop( void * pGate );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the strashed AIG network.]

  Description [Converts the logic network or the AIG into a 
  structurally hashed AIG.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkStrash( Abc_Ntk_t * pNtk, bool fAllNodes, bool fCleanup )
{
    Abc_Ntk_t * pNtkAig;
    int nNodes;

    assert( !Abc_NtkIsNetlist(pNtk) );
    if ( Abc_NtkIsBddLogic(pNtk) )
        Abc_NtkBddToSop(pNtk);
    // print warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );
    // perform strashing
    pNtkAig = Abc_NtkStartFrom( pNtk, ABC_TYPE_STRASH, ABC_FUNC_AIG );
    Abc_NtkStrashPerform( pNtk, pNtkAig, fAllNodes );
    Abc_NtkFinalize( pNtk, pNtkAig );
    // print warning about self-feed latches
    if ( Abc_NtkCountSelfFeedLatches(pNtkAig) )
        printf( "The network has %d self-feeding latches.\n", Abc_NtkCountSelfFeedLatches(pNtkAig) );
    if ( fCleanup && (nNodes = Abc_AigCleanup(pNtkAig->pManFunc)) )
        printf( "Cleanup has removed %d nodes.\n", nNodes );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkStrash( pNtk->pExdc, 0, 1 );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkAig ) )
    {
        printf( "Abc_NtkStrash: The network check has failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return NULL;
    }
    return pNtkAig;
}

/**Function*************************************************************

  Synopsis    [Appends the second network to the first.]

  Description [Modifies the first network by adding the logic of the second. 
  Performs structural hashing while appending the networks. Does not add 
  the COs of the second. Does not change the second network. Returns 0 
  if the appending failed, 1 otherise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 )
{
    Abc_Obj_t * pObj;
    int i;
    // the first network should be an AIG
    assert( Abc_NtkIsStrash(pNtk1) );
    assert( Abc_NtkIsLogic(pNtk2) || Abc_NtkIsStrash(pNtk2) ); 
    if ( Abc_NtkIsBddLogic(pNtk2) )
        Abc_NtkBddToSop(pNtk2);
    // check that the networks have the same PIs
    // reorder PIs of pNtk2 according to pNtk1
    if ( !Abc_NtkCompareSignals( pNtk1, pNtk2, 1 ) )
        return 0;
    // perform strashing
    Abc_NtkCleanCopy( pNtk2 );
    Abc_NtkForEachCi( pNtk2, pObj, i )
        pObj->pCopy = Abc_NtkCi(pNtk1, i); 
    // add pNtk2 to pNtk1 while strashing
    Abc_NtkStrashPerform( pNtk2, pNtk1, 1 );
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtk1 ) )
    {
        printf( "Abc_NtkAppend: The network check has failed.\n" );
        return 0;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Prepares the network for strashing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkStrashPerform( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew, bool fAllNodes )
{
    ProgressBar * pProgress;
    Abc_Aig_t * pMan = pNtkNew->pManFunc;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pNodeNew, * pObj;
    int i;

    // perform strashing
    vNodes = Abc_NtkDfs( pNtk, fAllNodes );
    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // get the node
        assert( Abc_ObjIsNode(pNode) );
         // strash the node
        pNodeNew = Abc_NodeStrash( pMan, pNode );
        // get the old object
        pObj = Abc_ObjFanout0Ntk( pNode );
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
    if ( Abc_NtkIsStrash(pNode->pNtk) )
    {
        if ( Abc_NodeIsConst(pNode) )
            return Abc_AigConst1(pMan);
        return Abc_AigAnd( pMan, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode) );
    }

    // get the SOP of the node
    if ( Abc_NtkHasMapping(pNode->pNtk) )
        pSop = Mio_GateReadSop(pNode->pData);
    else
        pSop = pNode->pData;

    // consider the constant node
    if ( Abc_NodeIsConst(pNode) )
        return Abc_ObjNotCond( Abc_AigConst1(pMan), Abc_SopIsConst0(pSop) );

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
    if ( Abc_SopIsComplement(pSop) )
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
    Dec_Graph_t * pFForm;
    Dec_Node_t * pNode;
    Abc_Obj_t * pAnd;
    int i;
    // perform factoring
    pFForm = Dec_Factor( pSop );
    // collect the fanins
    Dec_GraphForEachLeaf( pFForm, pNode, i )
        pNode->pFunc = Abc_ObjFanin(pRoot,i)->pCopy;
    // perform strashing
    pAnd = Dec_GraphToNetwork( pMan, pFForm );
    Dec_GraphFree( pFForm );
    return pAnd;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


