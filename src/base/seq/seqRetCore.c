/**CFile****************************************************************

  FileName    [seqRetCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    [The core of FPGA mapping/retiming package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqRetCore.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Seq_NtkRetimeDerive( Abc_Ntk_t * pNtk );
static Abc_Obj_t * Seq_NodeRetimeDerive( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, char * pSop );
static void        Seq_NodeAddEdges_rec( Abc_Obj_t * pGoal, Abc_Obj_t * pNode, Abc_InitType_t Init );
static Abc_Ntk_t * Seq_NtkRetimeReconstruct( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtk );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs FPGA mapping and retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkRetime( Abc_Ntk_t * pNtk, int nMaxIters, int fVerbose )
{
    Abc_Seq_t * p;
    Abc_Ntk_t * pNtkAig, * pNtkNew;
    int RetValue;
    assert( !Abc_NtkHasAig(pNtk) );
    // derive the isomorphic seq AIG
    pNtkAig = Seq_NtkRetimeDerive( pNtk );
    p = pNtkAig->pManFunc;
    p->nMaxIters = nMaxIters;
    // find the best mapping and retiming 
    Seq_NtkRetimeDelayLags( pNtk, pNtkAig, fVerbose );
    // implement the retiming
    RetValue = Seq_NtkImplementRetiming( pNtkAig, p->vLags, fVerbose );
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
    // create the final mapped network
    pNtkNew = Seq_NtkRetimeReconstruct( pNtk, pNtkAig );
    Abc_NtkDelete( pNtkAig );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives the isomorphic seq AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkRetimeDerive( Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pFanin, * pFanout;
    int i, k, RetValue;
    char * pSop;

    // make sure it is an AIG without self-feeding latches
    assert( !Abc_NtkHasAig(pNtk) );
    if ( RetValue = Abc_NtkRemoveSelfFeedLatches(pNtk) )
        printf( "Modified %d self-feeding latches. The result will not verify.\n", RetValue );
    assert( Abc_NtkCountSelfFeedLatches(pNtk) == 0 );

    if ( Abc_NtkIsBddLogic(pNtk) )
        Abc_NtkBddToSop(pNtk);

    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_SEQ, ABC_FUNC_AIG );

    // duplicate the name and the spec
    pNtkNew->pName = util_strsav(pNtk->pName);
    pNtkNew->pSpec = util_strsav(pNtk->pSpec);
    // map the constant nodes
    Abc_NtkCleanCopy( pNtk );
    // clone the PIs/POs/latches
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);

    // create one AND for each logic node
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pObj->pCopy = Abc_NtkCreateNode( pNtkNew );
        pObj->pCopy->pCopy = pObj;
    }
    Abc_NtkForEachLatch( pNtk, pObj, i )
        pObj->pCopy = Abc_ObjFanin0(pObj)->pCopy;

    // create internal AND nodes w/o strashing for each logic node (including constants)
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        // get the SOP of the node
        if ( Abc_NtkHasMapping(pNtk) )
            pSop = Mio_GateReadSop(pObj->pData);
        else
            pSop = pObj->pData;
        pFanin = Seq_NodeRetimeDerive( pNtkNew, pObj, pSop );
        Abc_ObjAddFanin( pObj->pCopy, pFanin );
        Abc_ObjAddFanin( pObj->pCopy, pFanin );
    }

    // connect the POs...

    
    // start the storage for initial states
    p = pNtkNew->pManFunc;
    Seq_Resize( p, Abc_NtkObjNumMax(pNtkNew) );

    // add the sequential edges
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjForEachFanout( pObj, pFanout, k )
            Seq_NodeAddEdges_rec( Abc_ObjFanin0(pObj)->pCopy, pFanout->pCopy, Abc_LatchInit(pObj) );

    // collect the nodes in the topological order
    p->vMapAnds   = Abc_NtkDfs( pNtk, 0 );
    p->vMapCuts   = Vec_VecStart( Vec_PtrSize(p->vMapAnds) );
    p->vMapDelays = Vec_VecStart( Vec_PtrSize(p->vMapAnds) );
    Vec_PtrForEachEntry( p->vMapAnds, pObj, i )
    {
        // change the node to be the new one
        Vec_PtrWriteEntry( p->vMapAnds, i, pObj->pCopy );
        // collect the new fanins of this node
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Vec_VecPush( p->vMapCuts, i, pFanin->pCopy );
        // collect the delay info
        if ( !Abc_NtkHasMapping(pNtk) )
        {
            Abc_ObjForEachFanin( pObj, pFanin, k )
                Vec_VecPush( p->vMapDelays, i, (void *)Abc_Float2Int(1.0) );
        }
        else
        {
            Mio_Pin_t * pPin = Mio_GateReadPins(pObj->pData);
            float Max, tDelayBlockRise, tDelayBlockFall;
            Abc_ObjForEachFanin( pObj, pFanin, k )
            {
                tDelayBlockRise = (float)Mio_PinReadDelayBlockRise( pPin );  
                tDelayBlockFall = (float)Mio_PinReadDelayBlockFall( pPin ); 
                Max = ABC_MAX( tDelayBlockRise, tDelayBlockFall );
                Vec_VecPush( p->vMapDelays, i, (void *)Abc_Float2Int(Max) );
                pPin = Mio_PinReadNext(pPin);
            }
        }
    }

    // set the cutset composed of latch drivers
//    Abc_NtkAigCutsetCopy( pNtk );
    Seq_NtkLatchGetEqualFaninNum( pNtkNew );

    // copy EXDC and check correctness
    if ( pNtkNew->pExdc )
        fprintf( stdout, "Warning: EXDC is not copied when converting to sequential AIG.\n" );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Seq_NtkRetimeDerive(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Add sequential edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_NodeAddEdges_rec( Abc_Obj_t * pGoal, Abc_Obj_t * pNode, Abc_InitType_t Init )
{
    Abc_Obj_t * pFanin;
    // consider the first fanin
    pFanin = Abc_ObjFanin0(pNode);
    if ( pFanin->pCopy == NULL ) // internal node
        Seq_NodeAddEdges_rec( pGoal, pFanin, Init );
    else if ( pFanin == pGoal )
        Seq_NodeInsertFirst( pNode, 0, Init );
    // consider the second fanin
    pFanin = Abc_ObjFanin1(pNode);
    if ( pFanin->pCopy == NULL ) // internal node
        Seq_NodeAddEdges_rec( pGoal, pFanin, Init );
    else if ( pFanin == pGoal )
        Seq_NodeInsertFirst( pNode, 1, Init );
}


/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Seq_NodeRetimeDerive( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pRoot, char * pSop )
{
    Dec_Graph_t * pFForm;
    Dec_Node_t * pNode;
    Abc_Obj_t * pAnd;
    int i, nFanins;

    // get the number of node's fanins
    nFanins = Abc_ObjFaninNum( pRoot );
    assert( nFanins == Abc_SopGetVarNum(pSop) );
    if ( nFanins < 2 )
    {
        if ( Abc_SopIsConst1(pSop) )
            return Abc_NtkConst1(pNtkNew);
        else if ( Abc_SopIsConst0(pSop) )
            return Abc_ObjNot( Abc_NtkConst1(pNtkNew) );
        else if ( Abc_SopIsBuf(pSop) )
            return Abc_ObjFanin0(pRoot)->pCopy;
        else if ( Abc_SopIsInv(pSop) )
            return Abc_ObjNot( Abc_ObjFanin0(pRoot)->pCopy );
        assert( 0 );
        return NULL;
    }

    // perform factoring
    pFForm = Dec_Factor( pSop );
    // collect the fanins
    Dec_GraphForEachLeaf( pFForm, pNode, i )
        pNode->pFunc = Abc_ObjFanin(pRoot,i)->pCopy;
    // perform strashing
    pAnd = Dec_GraphToNetworkNoStrash( pNtkNew, pFForm );
    Dec_GraphFree( pFForm );
    return pAnd;
}


/**Function*************************************************************

  Synopsis    [Reconstructs the network after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkRetimeReconstruct( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtk )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Seq_Lat_t * pRing;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pFaninNew, * pObjNew;
    int i;

    assert( !Abc_NtkIsSeq(pNtkOld) );
    assert( Abc_NtkIsSeq(pNtk) );

    // start the final network
    pNtkNew = Abc_NtkStartFrom( pNtk, pNtkOld->ntkType, pNtkOld->ntkFunc );

    // copy the internal nodes
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj );

    // share the latches
    Seq_NtkShareLatches( pNtkNew, pNtk );

    // connect the objects
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        if ( pRing = Seq_NodeGetRing(pObj,0) )
            pFaninNew = pRing->pLatch;
        else
            pFaninNew = Abc_ObjFanin0(pObj)->pCopy;
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );

        if ( pRing = Seq_NodeGetRing(pObj,1) )
            pFaninNew = pRing->pLatch;
        else
            pFaninNew = Abc_ObjFanin1(pObj)->pCopy;
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }
    // connect the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        if ( pRing = Seq_NodeGetRing(pObj,0) )
            pFaninNew = pRing->pLatch;
        else
            pFaninNew = Abc_ObjFanin0(pObj)->pCopy;
        pFaninNew = Abc_ObjNotCond( pFaninNew, Abc_ObjFaninC0(pObj) );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
    }

    // add the latches and their names
    Abc_NtkAddDummyLatchNames( pNtkNew );
    Abc_NtkForEachLatch( pNtkNew, pObjNew, i )
    {
        Vec_PtrPush( pNtkNew->vCis, pObjNew );
        Vec_PtrPush( pNtkNew->vCos, pObjNew );
    }
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkSeqToLogicSop(): Network check has failed.\n" );
    return pNtkNew;

}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


