/**CFile****************************************************************

  FileName    [abcIvy.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Strashing of the current network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcIvy.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "dec.h"
#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t *  Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan );
static Ivy_Man_t *  Abc_NtkToAig( Abc_Ntk_t * pNtkOld );

static void         Abc_NtkStrashPerformAig( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan );
static Ivy_Obj_t *  Abc_NodeStrashAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode );
static Ivy_Obj_t *  Abc_NodeStrashAigSopAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Ivy_Obj_t *  Abc_NodeStrashAigExorAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
static Ivy_Obj_t *  Abc_NodeStrashAigFactorAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop );
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
Abc_Ntk_t * Abc_NtkIvy( Abc_Ntk_t * pNtk )
{
    Ivy_Man_t * pMan;
    Abc_Ntk_t * pNtkAig;
    int fCleanup = 1;
    int nNodes;

    assert( !Abc_NtkIsNetlist(pNtk) );
    assert( !Abc_NtkIsSeq(pNtk) );
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        if ( !Abc_NtkBddToSop(pNtk, 0) )
        {
            printf( "Converting to SOPs has failed.\n" );
            return NULL;
        }
    }
    // print warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Warning: The choice nodes in the initial AIG are removed by strashing.\n" );

    // convert to the AIG manager
    pMan = Abc_NtkToAig( pNtk );

    if ( !Ivy_ManCheck( pMan ) )
    {
        printf( "AIG check has failed.\n" );
        Ivy_ManStop( pMan );
        return NULL;
    }


//    Ivy_MffcTest( pMan );
    Ivy_ManPrintStats( pMan );
    Ivy_ManSeqRewrite( pMan, 0, 0 );
    Ivy_ManPrintStats( pMan );

    // convert from the AIG manager
    pNtkAig = Abc_NtkFromAig( pNtk, pMan );
    Ivy_ManStop( pMan );

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
Abc_Ntk_t * Abc_NtkFromAig( Abc_Ntk_t * pNtkOld, Ivy_Man_t * pMan )
{
    Vec_Int_t * vNodes;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj, * pObjNew, * pFaninNew, * pFaninNew0, * pFaninNew1;
    Ivy_Obj_t * pNode;
    int i, Fanin;
    // perform strashing
    pNtk = Abc_NtkStartFrom( pNtkOld, ABC_NTK_STRASH, ABC_FUNC_AIG );
    // transfer the pointers to the basic nodes
    Ivy_ManConst1(pMan)->TravId = (Abc_NtkConst1(pNtk)->Id << 1);
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        Ivy_ManPi(pMan, i)->TravId = (pObj->pCopy->Id << 1);
    // rebuild the AIG
    vNodes = Ivy_ManDfs( pMan );
    Ivy_ManForEachNodeVec( pMan, vNodes, pNode, i )
    {
        // add the first fanins
        Fanin = Ivy_ObjFanin0(pNode)->TravId;
        pFaninNew0 = Abc_NtkObj( pNtk, Fanin >> 1 );
        pFaninNew0 = Abc_ObjNotCond( pFaninNew0, Ivy_ObjFaninC0(pNode) ^ (Fanin&1) );
        if ( Ivy_ObjIsBuf(pNode) )
        {
            pNode->TravId = (Abc_ObjRegular(pFaninNew0)->Id << 1) | Abc_ObjIsComplement(pFaninNew0);
            continue;
        }
        // add the first second
        Fanin = Ivy_ObjFanin1(pNode)->TravId;
        pFaninNew1 = Abc_NtkObj( pNtk, Fanin >> 1 );
        pFaninNew1 = Abc_ObjNotCond( pFaninNew1, Ivy_ObjFaninC1(pNode) ^ (Fanin&1) );
        // create the new node
        if ( Ivy_ObjIsExor(pNode) )
            pObjNew = Abc_AigXor( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        else
            pObjNew = Abc_AigAnd( pNtk->pManFunc, pFaninNew0, pFaninNew1 );
        pNode->TravId = (Abc_ObjRegular(pObjNew)->Id << 1) | Abc_ObjIsComplement(pObjNew);
    }
    Vec_IntFree( vNodes );
    // connect the PO nodes
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        pNode = Ivy_ManPo(pMan, i);
        Fanin = Ivy_ObjFanin0(pNode)->TravId;
        pFaninNew = Abc_NtkObj( pNtk, Fanin >> 1 );
        pFaninNew = Abc_ObjNotCond( pFaninNew, Ivy_ObjFaninC0(pNode) ^ (Fanin&1) );
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
Ivy_Man_t * Abc_NtkToAig( Abc_Ntk_t * pNtkOld )
{
    Ivy_Man_t * pMan;
    Abc_Obj_t * pObj;
    Ivy_Obj_t * pFanin;
    int i;
    // create the manager
    assert( Abc_NtkHasSop(pNtkOld) || Abc_NtkHasAig(pNtkOld) );
    if ( Abc_NtkHasSop(pNtkOld) )
        pMan = Ivy_ManStart( Abc_NtkCiNum(pNtkOld), Abc_NtkCoNum(pNtkOld), 3 * Abc_NtkGetLitNum(pNtkOld) + 10 );
    else
        pMan = Ivy_ManStart( Abc_NtkCiNum(pNtkOld), Abc_NtkCoNum(pNtkOld), 3 * Abc_NtkNodeNum(pNtkOld) + 10 );
    // create the PIs
    Abc_NtkConst1(pNtkOld)->pCopy = (Abc_Obj_t *)Ivy_ManConst1(pMan);
    Abc_NtkForEachCi( pNtkOld, pObj, i )
        pObj->pCopy = (Abc_Obj_t *)Ivy_ManPi(pMan, i);
    // perform the conversion of the internal nodes
    Abc_NtkStrashPerformAig( pNtkOld, pMan );
    // create the POs
    Abc_NtkForEachCo( pNtkOld, pObj, i )
    {
        pFanin = (Ivy_Obj_t *)Abc_ObjFanin0(pObj)->pCopy;
        pFanin = Ivy_NotCond( pFanin, Abc_ObjFaninC0(pObj) );
        Ivy_ObjConnect( Ivy_ManPo(pMan, i), pFanin );
    }
    Ivy_ManCleanup( pMan );
    return pMan;
}

/**Function*************************************************************

  Synopsis    [Prepares the network for strashing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkStrashPerformAig( Abc_Ntk_t * pNtk, Ivy_Man_t * pMan )
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
Ivy_Obj_t * Abc_NodeStrashAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode )
{
    int fUseFactor = 1;
    char * pSop;
    Ivy_Obj_t * pFanin0, * pFanin1;
    extern int Abc_SopIsExorType( char * pSop );

    assert( Abc_ObjIsNode(pNode) );

    // consider the case when the graph is an AIG
    if ( Abc_NtkIsStrash(pNode->pNtk) )
    {
        if ( Abc_NodeIsConst(pNode) )
            return Ivy_ManConst1(pMan);
        pFanin0 = (Ivy_Obj_t *)Abc_ObjFanin0(pNode)->pCopy;
        pFanin0 = Ivy_NotCond( pFanin0, Abc_ObjFaninC0(pNode) );
        pFanin1 = (Ivy_Obj_t *)Abc_ObjFanin1(pNode)->pCopy;
        pFanin1 = Ivy_NotCond( pFanin1, Abc_ObjFaninC1(pNode) );
        return Ivy_And( pFanin0, pFanin1 );
    }

    // get the SOP of the node
    if ( Abc_NtkHasMapping(pNode->pNtk) )
        pSop = Mio_GateReadSop(pNode->pData);
    else
        pSop = pNode->pData;

    // consider the constant node
    if ( Abc_NodeIsConst(pNode) )
        return Ivy_NotCond( Ivy_ManConst1(pMan), Abc_SopIsConst0(pSop) );

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
Ivy_Obj_t * Abc_NodeStrashAigSopAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin;
    Ivy_Obj_t * pAnd, * pSum;
    char * pCube;
    int i, nFanins;

    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Ivy_Not( Ivy_ManConst1(pMan) );
    Abc_SopForEachCube( pSop, nFanins, pCube )
    {
        // create the AND of literals
        pAnd = Ivy_ManConst1(pMan);
        Abc_ObjForEachFanin( pNode, pFanin, i ) // pFanin can be a net
        {
            if ( pCube[i] == '1' )
                pAnd = Ivy_And( pAnd, (Ivy_Obj_t *)pFanin->pCopy );
            else if ( pCube[i] == '0' )
                pAnd = Ivy_And( pAnd, Ivy_Not((Ivy_Obj_t *)pFanin->pCopy) );
        }
        // add to the sum of cubes
        pSum = Ivy_Or( pSum, pAnd );
    }
    // decide whether to complement the result
    if ( Abc_SopIsComplement(pSop) )
        pSum = Ivy_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashed n-input XOR function.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Abc_NodeStrashAigExorAig( Ivy_Man_t * pMan, Abc_Obj_t * pNode, char * pSop )
{
    Abc_Obj_t * pFanin;
    Ivy_Obj_t * pSum;
    int i, nFanins;
    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pNode );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    // go through the cubes of the node's SOP
    pSum = Ivy_Not( Ivy_ManConst1(pMan) );
    for ( i = 0; i < nFanins; i++ )
    {
        pFanin = Abc_ObjFanin( pNode, i );
        pSum = Ivy_Exor( pSum, (Ivy_Obj_t *)pFanin->pCopy );
    }
    if ( Abc_SopIsComplement(pSop) )
        pSum = Ivy_Not(pSum);
    return pSum;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ivy_Obj_t * Abc_NodeStrashAigFactorAig( Ivy_Man_t * pMan, Abc_Obj_t * pRoot, char * pSop )
{
    Dec_Graph_t * pFForm;
    Dec_Node_t * pNode;
    Ivy_Obj_t * pAnd;
    int i;

//    extern Ivy_Obj_t * Dec_GraphToNetworkAig( Ivy_Man_t * pMan, Dec_Graph_t * pGraph );
    extern Ivy_Obj_t * Dec_GraphToNetworkIvy( Ivy_Man_t * pMan, Dec_Graph_t * pGraph );

//    assert( 0 );

    // perform factoring
    pFForm = Dec_Factor( pSop );
    // collect the fanins
    Dec_GraphForEachLeaf( pFForm, pNode, i )
        pNode->pFunc = Abc_ObjFanin(pRoot,i)->pCopy;
    // perform strashing
//    pAnd = Dec_GraphToNetworkAig( pMan, pFForm );
    pAnd = Dec_GraphToNetworkIvy( pMan, pFForm );
//    pAnd = NULL;

    Dec_GraphFree( pFForm );
    return pAnd;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


