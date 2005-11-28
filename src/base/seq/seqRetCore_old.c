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

static Abc_Ntk_t * Seq_NtkRetimeDerive( Abc_Ntk_t * pNtk, int fVerbose );
static Abc_Obj_t * Seq_NodeRetimeDerive( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, char * pSop );
static void        Seq_NodeAddEdges_rec( Abc_Obj_t * pGoal, Abc_Obj_t * pNode, Abc_InitType_t Init );
static Abc_Ntk_t * Seq_NtkRetimeReconstruct( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtkSeq );
static Abc_Obj_t * Seq_EdgeReconstruct_rec( Abc_Obj_t * pGoal, Abc_Obj_t * pNode );
static Abc_Obj_t * Seq_EdgeReconstructPO( Abc_Obj_t * pNode );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs FPGA mapping and retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkRetime( Abc_Ntk_t * pNtk, int nMaxIters, int fInitial, int fVerbose )
{
    Abc_Seq_t * p;
    Abc_Ntk_t * pNtkSeq, * pNtkNew;
    int RetValue;
    assert( !Abc_NtkHasAig(pNtk) );
    // derive the isomorphic seq AIG
    pNtkSeq = Seq_NtkRetimeDerive( pNtk, fVerbose );
    p = pNtkSeq->pManFunc;
    p->nMaxIters = nMaxIters;

    if ( !fInitial )
        Seq_NtkLatchSetValues( pNtkSeq, ABC_INIT_DC );
    // find the best mapping and retiming 
    Seq_NtkRetimeDelayLags( pNtk, pNtkSeq, fVerbose );
    // implement the retiming
    RetValue = Seq_NtkImplementRetiming( pNtkSeq, p->vLags, fVerbose );
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );

//return pNtkSeq;

    // create the final mapped network
    pNtkNew = Seq_NtkRetimeReconstruct( pNtk, pNtkSeq );
    Abc_NtkDelete( pNtkSeq );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives the isomorphic seq AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Seq_NtkRetimeDerive( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Seq_t * p;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pFanin, * pFanout;
    int i, k, RetValue, fHasBdds;
    char * pSop;

    // make sure it is an AIG without self-feeding latches
    assert( !Abc_NtkHasAig(pNtk) );
    if ( RetValue = Abc_NtkRemoveSelfFeedLatches(pNtk) )
        printf( "Modified %d self-feeding latches. The result will not verify.\n", RetValue );
    assert( Abc_NtkCountSelfFeedLatches(pNtk) == 0 );

    // remove the dangling nodes
    Abc_NtkCleanup( pNtk, fVerbose );

    // transform logic functions from BDD to SOP
    if ( fHasBdds = Abc_NtkIsBddLogic(pNtk) )
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
        Abc_NtkDupObj( pNtkNew, pObj );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj( pNtkNew, pObj );
    // copy the names
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj->pCopy, Abc_ObjName(pObj) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkLogicStoreName( pObj->pCopy, Abc_ObjName(pObj) );

    // create one AND for each logic node
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 && Abc_ObjFanoutNum(pObj) == 0 )
            continue;
        pObj->pCopy = Abc_NtkCreateNode( pNtkNew );
        pObj->pCopy->pCopy = pObj;
    }
    // make latches point to the latch fanins
    Abc_NtkForEachLatch( pNtk, pObj, i )
    {
        assert( !Abc_ObjIsLatch(Abc_ObjFanin0(pObj)) );
        pObj->pCopy = Abc_ObjFanin0(pObj)->pCopy;
    }

    // create internal AND nodes w/o strashing for each logic node (including constants)
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 && Abc_ObjFanoutNum(pObj) == 0 )
            continue;
        // get the SOP of the node
        if ( Abc_NtkHasMapping(pNtk) )
            pSop = Mio_GateReadSop(pObj->pData);
        else
            pSop = pObj->pData;
        pFanin = Seq_NodeRetimeDerive( pNtkNew, pObj, pSop );
        Abc_ObjAddFanin( pObj->pCopy, pFanin );
        Abc_ObjAddFanin( pObj->pCopy, pFanin );
    }
    // connect the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjFanin0(pObj)->pCopy );
    
    // start the storage for initial states
    p = pNtkNew->pManFunc;
    Seq_Resize( p, Abc_NtkObjNumMax(pNtkNew) );

    // add the sequential edges
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjForEachFanout( pObj, pFanout, k )
        {
            if ( pObj->pCopy == Abc_ObjFanin0(pFanout->pCopy) )
            {
                Seq_NodeInsertFirst( pFanout->pCopy, 0, Abc_LatchInit(pObj) );
                Seq_NodeInsertFirst( pFanout->pCopy, 1, Abc_LatchInit(pObj) );
                continue;
            }
            Seq_NodeAddEdges_rec( pObj->pCopy, Abc_ObjFanin0(pFanout->pCopy), Abc_LatchInit(pObj) );
        }

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
            Vec_VecPush( p->vMapCuts, i, (void *)( (pFanin->pCopy->Id << 8) | Abc_ObjIsLatch(pFanin) ) );
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
//    Seq_NtkLatchGetEqualFaninNum( pNtkNew );

    // convert the network back into BDDs if this is how it was
    if ( fHasBdds )
        Abc_NtkSopToBdd(pNtk);

    // copy EXDC and check correctness
    if ( pNtk->pExdc )
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
    assert( !Abc_ObjIsLatch(pNode) );
    if ( !Abc_NodeIsAigAnd(pNode) )
        return;
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
Abc_Ntk_t * Seq_NtkRetimeReconstruct( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtkSeq )
{
    Abc_Seq_t * p = pNtkSeq->pManFunc;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pObjNew, * pFanin, * pFaninNew;
    int i, k;

    assert( !Abc_NtkIsSeq(pNtkOld) );
    assert( Abc_NtkIsSeq(pNtkSeq) );

    // transfer the pointers pNtkOld->pNtkSeq from pCopy to pNext
    Abc_NtkForEachObj( pNtkOld, pObj, i )
        pObj->pNext = pObj->pCopy;

    // start the final network
    pNtkNew = Abc_NtkStartFrom( pNtkSeq, pNtkOld->ntkType, pNtkOld->ntkFunc );

    // copy the internal nodes of the old network into the new network
    // transfer the pointers pNktOld->pNtkNew to pNtkSeq->pNtkNew
    Abc_NtkForEachNode( pNtkOld, pObj, i )
    {
        if ( i == 0 ) continue;
        Abc_NtkDupObj( pNtkNew, pObj );
        pObj->pNext->pCopy = pObj->pCopy;
    }

    // share the latches
    Seq_NtkShareLatches( pNtkNew, pNtkSeq );

    // connect the objects
    Abc_NtkForEachNode( pNtkOld, pObj, i )
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            pFaninNew = Seq_EdgeReconstruct_rec( pFanin->pNext, pObj->pNext );
            assert( pFaninNew != NULL );
            Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        }

    // connect the POs
    Abc_NtkForEachPo( pNtkOld, pObj, i )
    {
        pFaninNew = Seq_EdgeReconstructPO( pObj->pNext );
        assert( pFaninNew != NULL );
        Abc_ObjAddFanin( pObj->pNext->pCopy, pFaninNew );
    }

    // clean the result of latch sharing
    Seq_NtkShareLatchesClean( pNtkSeq );

    // add the latches and their names
    Abc_NtkAddDummyLatchNames( pNtkNew );
    Abc_NtkForEachLatch( pNtkNew, pObjNew, i )
    {
        Vec_PtrPush( pNtkNew->vCis, pObjNew );
        Vec_PtrPush( pNtkNew->vCos, pObjNew );
    }
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 1 );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Seq_NtkRetimeReconstruct(): Network check has failed.\n" );
    return pNtkNew;

}

/**Function*************************************************************

  Synopsis    [Reconstructs the network after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Seq_EdgeReconstruct_rec( Abc_Obj_t * pGoal, Abc_Obj_t * pNode )
{
    Seq_Lat_t * pRing;
    Abc_Obj_t * pFanin, * pRes = NULL;

    if ( !Abc_NodeIsAigAnd(pNode) )
        return NULL;

    // consider the first fanin
    pFanin = Abc_ObjFanin0(pNode);
    if ( pFanin->pCopy == NULL ) // internal node
        pRes = Seq_EdgeReconstruct_rec( pGoal, pFanin );
    else if ( pFanin == pGoal )
    {
        if ( pRing = Seq_NodeGetRing( pNode, 0 ) )
            pRes = pRing->pLatch;
        else
            pRes = pFanin->pCopy;
    }
    if ( pRes != NULL )
        return pRes;

    // consider the second fanin
    pFanin = Abc_ObjFanin1(pNode);
    if ( pFanin->pCopy == NULL ) // internal node
        pRes = Seq_EdgeReconstruct_rec( pGoal, pFanin );
    else if ( pFanin == pGoal )
    {
        if ( pRing = Seq_NodeGetRing( pNode, 1 ) )
            pRes = pRing->pLatch;
        else
            pRes = pFanin->pCopy;
    }
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Reconstructs the network after retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Seq_EdgeReconstructPO( Abc_Obj_t * pNode )
{
    Seq_Lat_t * pRing;
    assert( Abc_ObjIsPo(pNode) );
    if ( pRing = Seq_NodeGetRing( pNode, 0 ) )
        return pRing->pLatch;
    else
        return Abc_ObjFanin0(pNode)->pCopy;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


