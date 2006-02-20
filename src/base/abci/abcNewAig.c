/**CFile****************************************************************

  FileName    [aigNewAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Strashing of the current network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigNewAig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "extra.h"
#include "dec.h"
#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t *  Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan );
static Aig_Man_t *  Abc_NtkToAig( Abc_Ntk_t * pNtkOld );

static void         Abc_NtkStrashPerformAig( Abc_Ntk_t * pNtk, Aig_Man_t * pMan );
static Aig_Node_t * Abc_NodeStrashAig( Aig_Man_t * pMan, Abc_Obj_t * pNode );
static Aig_Node_t * Abc_NodeStrashAigSopAig( Aig_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Aig_Node_t * Abc_NodeStrashAigExorAig( Aig_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Aig_Node_t * Abc_NodeStrashAigFactorAig( Aig_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
extern char *       Mio_GateReadSop( void * pGate );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Gives the current ABC network to AIG manager for processing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkNewAig( Abc_Ntk_t * pNtk )
{
    Aig_Man_t * pMan;
    Abc_Ntk_t * pNtkAig;
//    Aig_ProofType_t RetValue;
    int fCleanup = 1;
    int nNodes;
    extern void Aig_MffcTest( Aig_Man_t * pMan );


    assert( !Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkIsSeq(pNtk) );
    if ( Abc_NtkIsBddLogic(pNtk) )
        Abc_NtkBddToSop(pNtk);
    // print warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );

    // convert to the AIG manager
    pMan = Abc_NtkToAig( pNtk );

    Aig_MffcTest( pMan );

/*
    // execute a command in the AIG manager
    RetValue = Aig_FraigProve( pMan );
    if ( RetValue == AIG_PROOF_SAT )
        printf( "Satisfiable.\n" );
    else if ( RetValue == AIG_PROOF_UNSAT )
        printf( "Unsatisfiable.\n" );
    else if ( RetValue == AIG_PROOF_TIMEOUT )
        printf( "Undecided.\n" );
    else
        assert( 0 );
*/

    // convert from the AIG manager
    pNtkAig = Abc_NtkFromAig( pNtk, pMan );
    Aig_ManStop( pMan );

    // report the cleanup results
    if ( fCleanup && (nNodes = Abc_AigCleanup(pNtkAig->pManFunc)) )
        printf( "Warning: AIG cleanup removed %d nodes (this is not a bug).\n", nNodes );
    // duplicate EXDC 
    if ( pNtk->pExdc )
        pNtkAig->pExdc = Abc_NtkDup( pNtk->pExdc );
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

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan )
{
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj, * pObjNew, * pFaninNew, * pFaninNew0, * pFaninNew1;
    Aig_Node_t * pAnd;
    int i;
    // perform strashing
    pNtk = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Aig_ManConst1(pMan)->Data = Abc_NtkConst1(pNtk)->Id;
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        Aig_ManPi(pMan, i)->Data = pObj->pCopy->Id;
    // rebuild the AIG
    Aig_ManForEachAnd( pMan, pAnd, i )
    {
        // add the first fanins
        pFaninNew0 = Abc_NtkObj( pNtk, Aig_NodeFanin0(pAnd)->Data );
        pFaninNew0 = Abc_ObjNotCond( pFaninNew0, Aig_NodeFaninC0(pAnd) );
        // add the first second
        pFaninNew1 = Abc_NtkObj( pNtk, Aig_NodeFanin1(pAnd)->Data );
        pFaninNew1 = Abc_ObjNotCond( pFaninNew1, Aig_NodeFaninC1(pAnd) );
        // create the new node
        pObjNew = Abc_AigAnd( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        pAnd->Data = pObjNew->Id;
    }
    // connect the PO nodes
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        pAnd = Aig_ManPo( pMan, i );
        pFaninNew = Abc_NtkObj( pNtk, Aig_NodeFanin0(pAnd)->Data );
        pFaninNew = Abc_ObjNotCond( pFaninNew, Aig_NodeFaninC0(pAnd) );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToAig( Abc_Ntk_t * pNtkOld )
{
    Aig_Param_t Params;
    Aig_Man_t * pMan;
    Abc_Obj_t * pObj;
    Aig_Node_t * pFanin;
    int i;
    // create the manager
    Aig_ManSetDefaultParams( &Params );
    pMan = Aig_ManStart( &Params );
    // create the PIs
    Abc_NtkConst1(pNtkOld)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_NodeCreatePi(pMan);
    Abc_NtkForEachCo( pNtkOld, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Aig_NodeCreatePo(pMan);
    // perform the conversion of the internal nodes
    Abc_NtkStrashPerformAig( pNtkOld, pMan );
    // create the POs
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        pFanin = (Aig_Node_t *)Abc_ObjFanin0(pObj)->pCopy;
        pFanin = Aig_NotCond( pFanin, Abc_ObjFaninC0(pObj) );
        Aig_NodeConnectPo( pMan, (Aig_Node_t *)pObj->pCopy, pFanin );
    }
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Prepares the network for strashing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkStrashPerformAig( Abc_Ntk_t * pNtk, Aig_Man_t * pMan )
{
//    ProgressBar * pProgress;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i;
    vNodes = Abc_NtkDfs( pNtk, 0 );
//    pProgress = Extra_ProgressBarStart( stdout, vNodes->nSize );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
//        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNode->pCopy = (Abc_Obj_t *)Abc_NodeStrashAig( pMan, pNode );
    }
//    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Abc_NodeStrashAig( Aig_Man_t * pMan, Abc_Obj_t * pNode )
{
    int fUseFactor = 1;
    char * pSop;
    Aig_Node_t * pFanin0, * pFanin1;
    extern int Abc_SopIsExorType( char * pSop );

    assert( Abc_ObjIsNode(pNode) );

    // consider the case when the graph is an AIG
    if ( Abc_NtkIsStrash(pNode->pNtk) )
    {
        if ( Abc_NodeIsConst(pNode) )
            return Aig_ManConst1(pMan);
        pFanin0 = (Aig_Node_t *)Abc_ObjFanin0(pNode)->pCopy;
        pFanin0 = Aig_NotCond( pFanin0, Abc_ObjFaninC0(pNode) );
        pFanin1 = (Aig_Node_t *)Abc_ObjFanin1(pNode)->pCopy;
        pFanin1 = Aig_NotCond( pFanin1, Abc_ObjFaninC1(pNode) );
        return Aig_And( pMan, pFanin0, pFanin1 );
    }

    // get the SOP of the node
    if ( Abc_NtkHasMapping(pNode->pNtk) )
        pSop = Mio_GateReadSop(pNode->pData);
    else
        pSop = pNode->pData;

    // consider the constant node
    if ( Abc_NodeIsConst(pNode) )
        return Aig_NotCond( Aig_ManConst1(pMan), Abc_SopIsConst0(pSop) );

    // consider the special case of EXOR function
    if ( Abc_SopIsExorType(pSop) )
        return Abc_NodeStrashAigExorAig( pMan, pNode, pSop );

    // decide when to use factoring
    if ( fUseFactor && Abc_ObjFaninNum(pNode) > 2 && Abc_SopGetCubeNum(pSop) > 1 )
        return Abc_NodeStrashAigFactorAig( pMan, pNode, pSop );
    return Abc_NodeStrashAigSopAig( pMan, pNode, pSop );
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Abc_NodeStrashAigSopAig( Aig_Man_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin;
    Aig_Node_t * pAnd, * pSum;
    char * pCube;
    int i, nFanins;

    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Aig_Not( Aig_ManConst1(pMan) );
    Abc_SopForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = Aig_ManConst1(pMan);
        Abc_ObjForEachFanin( pNode, pFanin, i ) // pFanin can be a net
        {
            if ( pCube[i] == '1' )
                pAnd = Aig_And( pMan, pAnd, (Aig_Node_t *)pFanin->pCopy );
            else if ( pCube[i] == '0' )
                pAnd = Aig_And( pMan, pAnd, Aig_Not((Aig_Node_t *)pFanin->pCopy) );
        }
        // add to the sum of cubes
        pSum = Aig_Or( pMan, pSum, pAnd );
    }
    // decide whether to complement the result
    if ( Abc_SopIsComplement(pSop) )
        pSum = Aig_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashed n-input XOR function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Abc_NodeStrashAigExorAig( Aig_Man_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin;
    Aig_Node_t * pSum;
    int i, nFanins;
    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Aig_Not( Aig_ManConst1(pMan) );
    for ( i = 0; i < nFanins; i++ )
    {
        pFanin = Abc_ObjFanin( pNode, i );
        pSum = Aig_Xor( pMan, pSum, (Aig_Node_t *)pFanin->pCopy );
    }
    if ( Abc_SopIsComplement(pSop) )
        pSum = Aig_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Node_t * Abc_NodeStrashAigFactorAig( Aig_Man_t * pMan, Abc_Obj_t * pRoot, char * pSop )
{
    Dec_Graph_t * pFForm;
    Dec_Node_t * pNode;
    Aig_Node_t * pAnd;
    int i;
    extern Aig_Node_t * Dec_GraphToNetworkAig( Aig_Man_t * pMan, Dec_Graph_t * pGraph );

    // perform factoring
    pFForm = Dec_Factor( pSop );
    // collect the fanins
    Dec_GraphForEachLeaf( pFForm, pNode, i )
        pNode->pFunc = Abc_ObjFanin(pRoot,i)->pCopy;
    // perform strashing
    pAnd = Dec_GraphToNetworkAig( pMan, pFForm );
    Dec_GraphFree( pFForm );
    return pAnd;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


