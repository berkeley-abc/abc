/**CFile****************************************************************

  FileName    [abcCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface to cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcCut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "cut.h"
#include "seqInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_NtkPrintCuts( void * p, Abc_Ntk_t * pNtk, int fSeq );
static void Abc_NtkPrintCuts_( void * p, Abc_Ntk_t * pNtk, int fSeq );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t * Abc_NtkCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams )
{
    Cut_Man_t *  p;
    Abc_Obj_t * pObj, * pNode;
    Vec_Ptr_t * vNodes;
    Vec_Int_t * vChoices;
    int i;
    int clk = clock();

    extern void Abc_NtkBalanceAttach( Abc_Ntk_t * pNtk );
    extern void Abc_NtkBalanceDetach( Abc_Ntk_t * pNtk );

    assert( Abc_NtkIsStrash(pNtk) );
/*
    if ( pParams->fMulti )
    {
        Abc_Obj_t * pNode, * pNodeA, * pNodeB, * pNodeC;
        int nFactors;
        // lebel the nodes, which will be the roots of factor-cuts
        // mark the multiple-fanout nodes
        Abc_AigForEachAnd( pNtk, pNode, i )
            if ( pNode->vFanouts.nSize > 1 )
                pNode->fMarkB = 1;
        // unmark the control inputs of MUXes and inputs of EXOR gates
        Abc_AigForEachAnd( pNtk, pNode, i )
        {
            if ( !Abc_NodeIsMuxType(pNode) )
                continue;

            pNodeC = Abc_NodeRecognizeMux( pNode, &pNodeA, &pNodeB );
            // if real children are used, skip
            if ( Abc_ObjFanin0(pNode)->vFanouts.nSize > 1 || Abc_ObjFanin1(pNode)->vFanouts.nSize > 1 )
                continue;

            if ( pNodeC->vFanouts.nSize == 2 )
                pNodeC->fMarkB = 0;
            if ( Abc_ObjRegular(pNodeA) == Abc_ObjRegular(pNodeB) && Abc_ObjRegular(pNodeA)->vFanouts.nSize == 2 )
                Abc_ObjRegular(pNodeA)->fMarkB = 0;
       }
        // mark the PO drivers
//        Abc_NtkForEachCo( pNtk, pNode, i )
//            Abc_ObjFanin0(pNode)->fMarkB = 1;
        nFactors = 0;
        Abc_AigForEachAnd( pNtk, pNode, i )
            nFactors += pNode->fMarkB;
        printf( "Total nodes = %6d.  Total factors = %6d.\n", Abc_NtkNodeNum(pNtk), nFactors );
    }
*/
    // start the manager
    pParams->nIdsMax = Abc_NtkObjNumMax( pNtk );
    p = Cut_ManStart( pParams );
    if ( pParams->fDrop )
        Cut_ManSetFanoutCounts( p, Abc_NtkFanoutCounts(pNtk) );
    // set cuts for PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_ObjFanoutNum(pObj) > 0 )
            Cut_NodeSetTriv( p, pObj->Id );
    // compute cuts for internal nodes
    vNodes = Abc_AigDfs( pNtk, 0, 1 ); // collects POs
    vChoices = Vec_IntAlloc( 100 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // when we reached a CO, it is time to deallocate the cuts
        if ( Abc_ObjIsCo(pObj) )
        {
            if ( pParams->fDrop )
                Cut_NodeTryDroppingCuts( p, Abc_ObjFaninId0(pObj) );
            continue;
        }
        // skip constant node, it has no cuts
        if ( Abc_NodeIsConst(pObj) )
            continue;
        // compute the cuts to the internal node
        Abc_NodeGetCuts( p, pObj, pParams->fMulti );  
        // consider dropping the fanins cuts
        if ( pParams->fDrop )
        {
            Cut_NodeTryDroppingCuts( p, Abc_ObjFaninId0(pObj) );
            Cut_NodeTryDroppingCuts( p, Abc_ObjFaninId1(pObj) );
        }
        // add cuts due to choices
        if ( Abc_NodeIsAigChoice(pObj) )
        {
            Vec_IntClear( vChoices );
            for ( pNode = pObj; pNode; pNode = pNode->pData )
                Vec_IntPush( vChoices, pNode->Id );
            Cut_NodeUnionCuts( p, vChoices );
        }
    }
    Vec_PtrFree( vNodes );
    Vec_IntFree( vChoices );
/*
    if ( pParams->fMulti )
    {
        Abc_NtkForEachObj( pNtk, pNode, i )
            pNode->fMarkB = 0;
    }
*/
PRT( "Total", clock() - clk );
//Abc_NtkPrintCuts_( p, pNtk, 0 );
//    Cut_ManPrintStatsToFile( p, pNtk->pSpec, clock() - clk );
    return p;
}

/**Function*************************************************************

  Synopsis    [Cut computation using the oracle.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCutsOracle( Abc_Ntk_t * pNtk, Cut_Oracle_t * p )
{
    Abc_Obj_t * pObj;
    Vec_Ptr_t * vNodes;
    int i, clk = clock();
    int fDrop = Cut_OracleReadDrop(p);

    assert( Abc_NtkIsStrash(pNtk) );

    // prepare cut droppping
    if ( fDrop )
        Cut_OracleSetFanoutCounts( p, Abc_NtkFanoutCounts(pNtk) );

    // set cuts for PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_ObjFanoutNum(pObj) > 0 )
            Cut_OracleNodeSetTriv( p, pObj->Id );

    // compute cuts for internal nodes
    vNodes = Abc_AigDfs( pNtk, 0, 1 ); // collects POs
    Vec_PtrForEachEntry( vNodes, pObj, i )
    {
        // when we reached a CO, it is time to deallocate the cuts
        if ( Abc_ObjIsCo(pObj) )
        {
            if ( fDrop )
                Cut_OracleTryDroppingCuts( p, Abc_ObjFaninId0(pObj) );
            continue;
        }
        // skip constant node, it has no cuts
        if ( Abc_NodeIsConst(pObj) )
            continue;
        // compute the cuts to the internal node
        Cut_OracleComputeCuts( p, pObj->Id, Abc_ObjFaninId0(pObj), Abc_ObjFaninId1(pObj),  
                Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
        // consider dropping the fanins cuts
        if ( fDrop )
        {
            Cut_OracleTryDroppingCuts( p, Abc_ObjFaninId0(pObj) );
            Cut_OracleTryDroppingCuts( p, Abc_ObjFaninId1(pObj) );
        }
    }
    Vec_PtrFree( vNodes );
//PRT( "Total", clock() - clk );
//Abc_NtkPrintCuts_( p, pNtk, 0 );
}


/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t * Abc_NtkSeqCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams )
{
    Cut_Man_t *  p;
    Abc_Obj_t * pObj, * pNode;
    int i, nIters, fStatus;
    Vec_Int_t * vChoices;
    int clk = clock();

    assert( Abc_NtkIsSeq(pNtk) );
    assert( pParams->fSeq );
//    assert( Abc_NtkIsDfsOrdered(pNtk) );

    // start the manager
    pParams->nIdsMax = Abc_NtkObjNumMax( pNtk );
    pParams->nCutSet = Abc_NtkCutSetNodeNum( pNtk );
    p = Cut_ManStart( pParams );

    // set cuts for the constant node and the PIs
    pObj = Abc_NtkConst1(pNtk);
    if ( Abc_ObjFanoutNum(pObj) > 0 )
        Cut_NodeSetTriv( p, pObj->Id );
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
//printf( "Setting trivial cut %d.\n", pObj->Id );
        Cut_NodeSetTriv( p, pObj->Id );
    }
    // label the cutset nodes and set their number in the array
    // assign the elementary cuts to the cutset nodes
    Abc_SeqForEachCutsetNode( pNtk, pObj, i )
    {
        assert( pObj->fMarkC == 0 );
        pObj->fMarkC = 1;
        pObj->pCopy = (Abc_Obj_t *)i;
        Cut_NodeSetTriv( p, pObj->Id );
//printf( "Setting trivial cut %d.\n", pObj->Id );
    }

    // process the nodes
    vChoices = Vec_IntAlloc( 100 );
    for ( nIters = 0; nIters < 10; nIters++ )
    {
//printf( "ITERATION %d:\n", nIters );
        // compute the cuts for the internal nodes
        Abc_AigForEachAnd( pNtk, pObj, i )
        {
            Abc_NodeGetCutsSeq( p, pObj, nIters==0 );
            // add cuts due to choices
            if ( Abc_NodeIsAigChoice(pObj) )
            {
                Vec_IntClear( vChoices );
                for ( pNode = pObj; pNode; pNode = pNode->pData )
                    Vec_IntPush( vChoices, pNode->Id );
                Cut_NodeUnionCutsSeq( p, vChoices, (pObj->fMarkC ? (int)pObj->pCopy : -1), nIters==0 );
            }
        }
        // merge the new cuts with the old cuts
        Abc_NtkForEachPi( pNtk, pObj, i )
            Cut_NodeNewMergeWithOld( p, pObj->Id );
        Abc_AigForEachAnd( pNtk, pObj, i )
            Cut_NodeNewMergeWithOld( p, pObj->Id );
        // for the cutset, transfer temp cuts to new cuts
        fStatus = 0;
        Abc_SeqForEachCutsetNode( pNtk, pObj, i )
            fStatus |= Cut_NodeTempTransferToNew( p, pObj->Id, i );
        if ( fStatus == 0 )
            break;
    }
    Vec_IntFree( vChoices );

    // if the status is not finished, transfer new to old for the cutset
    Abc_SeqForEachCutsetNode( pNtk, pObj, i )
        Cut_NodeNewMergeWithOld( p, pObj->Id );

    // transfer the old cuts to the new positions
    Abc_NtkForEachObj( pNtk, pObj, i )
        Cut_NodeOldTransferToNew( p, pObj->Id );

    // unlabel the cutset nodes
    Abc_SeqForEachCutsetNode( pNtk, pObj, i )
        pObj->fMarkC = 0;
if ( pParams->fVerbose )
{
PRT( "Total", clock() - clk );
printf( "Converged after %d iterations.\n", nIters );
}
//Abc_NtkPrintCuts( p, pNtk, 1 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NodeGetCutsRecursive( void * p, Abc_Obj_t * pObj, int fMulti )
{
    void * pList;
    if ( pList = Abc_NodeReadCuts( p, pObj ) )
        return pList;
    Abc_NodeGetCutsRecursive( p, Abc_ObjFanin0(pObj), fMulti );
    Abc_NodeGetCutsRecursive( p, Abc_ObjFanin1(pObj), fMulti );
    return Abc_NodeGetCuts( p, pObj, fMulti );
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NodeGetCuts( void * p, Abc_Obj_t * pObj, int fMulti )
{
//    int fTriv = (!fMulti) || pObj->fMarkB;
    int fTriv = (!fMulti) || (pObj->vFanouts.nSize > 1 && !Abc_NodeIsMuxControlType(pObj));
    assert( Abc_NtkIsStrash(pObj->pNtk) );
    assert( Abc_ObjFaninNum(pObj) == 2 );
    return Cut_NodeComputeCuts( p, pObj->Id, Abc_ObjFaninId0(pObj), Abc_ObjFaninId1(pObj),  
        Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj), fTriv );  
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeGetCutsSeq( void * p, Abc_Obj_t * pObj, int fTriv )
{
    int CutSetNum;
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    assert( Abc_ObjFaninNum(pObj) == 2 );
    fTriv     = pObj->fMarkC ? 0 : fTriv;
    CutSetNum = pObj->fMarkC ? (int)pObj->pCopy : -1;
    Cut_NodeComputeCutsSeq( p, pObj->Id, Abc_ObjFaninId0(pObj), Abc_ObjFaninId1(pObj),  
        Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj), Seq_ObjFaninL0(pObj), Seq_ObjFaninL1(pObj), fTriv, CutSetNum );  
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NodeReadCuts( void * p, Abc_Obj_t * pObj )
{
    return Cut_NodeReadCutsNew( p, pObj->Id );  
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeFreeCuts( void * p, Abc_Obj_t * pObj )
{
    Cut_NodeFreeCuts( p, pObj->Id );
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintCuts( void * p, Abc_Ntk_t * pNtk, int fSeq )
{
    Cut_Man_t * pMan = p;
    Cut_Cut_t * pList;
    Abc_Obj_t * pObj;
    int i;
    printf( "Cuts of the network:\n" );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        pList = Abc_NodeReadCuts( p, pObj );
        printf( "Node %s:\n", Abc_ObjName(pObj) );
        Cut_CutPrintList( pList, fSeq );
    }
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkPrintCuts_( void * p, Abc_Ntk_t * pNtk, int fSeq )
{
    Cut_Man_t * pMan = p;
    Cut_Cut_t * pList;
    Abc_Obj_t * pObj;
    pObj = Abc_NtkObj( pNtk, 2 * Abc_NtkObjNum(pNtk) / 3 );
    pList = Abc_NodeReadCuts( p, pObj );
    printf( "Node %s:\n", Abc_ObjName(pObj) );
    Cut_CutPrintList( pList, fSeq );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


