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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_NtkPrintCuts( void * p, Abc_Ntk_t * pNtk, int fSeq );
static void Abc_NtkPrintCuts_( void * p, Abc_Ntk_t * pNtk, int fSeq );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
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
    if ( pParams->fMulti )
        Abc_NtkBalanceAttach(pNtk);

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
    vNodes = Abc_AigDfs( pNtk, 0, 1 );
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
    if ( pParams->fMulti )
        Abc_NtkBalanceDetach(pNtk);
PRT( "Total", clock() - clk );
Abc_NtkPrintCuts_( p, pNtk, 0 );
//    Cut_ManPrintStatsToFile( p, pNtk->pSpec, clock() - clk );
    return p;
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
    Abc_Obj_t * pObj;
    int i, nIters, fStatus;
    int clk = clock();

    assert( Abc_NtkIsSeq(pNtk) );
    assert( pParams->fSeq );

    // start the manager
    pParams->nIdsMax = Abc_NtkObjNumMax( pNtk );
    pParams->nCutSet = pNtk->vLats->nSize;
    p = Cut_ManStart( pParams );

    // set cuts for PIs
    Abc_NtkForEachPi( pNtk, pObj, i )
        Cut_NodeSetTriv( p, pObj->Id );
    // label the cutset nodes and set their number in the array
    // assign the elementary cuts to the cutset nodes
    Abc_SeqForEachCutsetNode( pNtk, pObj, i )
    {
        assert( pObj->fMarkC == 0 );
        pObj->fMarkC = 1;
        pObj->pCopy = (Abc_Obj_t *)i;
        Cut_NodeSetTriv( p, pObj->Id );
    }

    // process the nodes
    for ( nIters = 0; nIters < 10; nIters++ )
    {
//printf( "ITERATION %d:\n", nIters );
        // compute the cuts for the internal nodes
        Abc_AigForEachAnd( pNtk, pObj, i )
            Abc_NodeGetCutsSeq( p, pObj, nIters==0 );
Abc_NtkPrintCuts( p, pNtk, 1 );
        // merge the new cuts with the old cuts
        Abc_NtkForEachPi( pNtk, pObj, i )
            Cut_NodeNewMergeWithOld( p, pObj->Id );
        Abc_AigForEachAnd( pNtk, pObj, i )
            Cut_NodeNewMergeWithOld( p, pObj->Id );
        // for the cutset, merge temp with new
        fStatus = 0;
        Abc_SeqForEachCutsetNode( pNtk, pObj, i )
            fStatus |= Cut_NodeTempTransferToNew( p, pObj->Id, i );
        if ( fStatus == 0 )
            break;
    }

    // if the status is not finished, transfer new to old for the cutset
    Abc_SeqForEachCutsetNode( pNtk, pObj, i )
        Cut_NodeNewMergeWithOld( p, pObj->Id );

    // transfer the old cuts to the new positions
    Abc_NtkForEachObj( pNtk, pObj, i )
        Cut_NodeOldTransferToNew( p, pObj->Id );

    // unlabel the cutset nodes
    Abc_SeqForEachCutsetNode( pNtk, pObj, i )
        pObj->fMarkC = 0;
PRT( "Total", clock() - clk );
printf( "Converged after %d iterations.\n", nIters );
Abc_NtkPrintCuts( p, pNtk, 1 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NodeGetCutsRecursive( void * p, Abc_Obj_t * pObj )
{
    void * pList;
    if ( pList = Abc_NodeReadCuts( p, pObj ) )
        return pList;
    Abc_NodeGetCutsRecursive( p, Abc_ObjFanin0(pObj) );
    Abc_NodeGetCutsRecursive( p, Abc_ObjFanin1(pObj) );
    return Abc_NodeGetCuts( p, pObj, 0 );
}

/**Function*************************************************************

  Synopsis    [Computes the cuts for the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void * Abc_NodeGetCuts( void * p, Abc_Obj_t * pObj, int fMulti )
{
    int fTriv = (!fMulti) || (pObj->pCopy != NULL);
    assert( Abc_NtkIsStrash(pObj->pNtk) );
    assert( Abc_ObjFaninNum(pObj) == 2 );
    return Cut_NodeComputeCuts( p, pObj->Id, Abc_ObjFaninId0(pObj), Abc_ObjFaninId1(pObj),  
        Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj), 1, 1, fTriv );  
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
//    fTriv     = pObj->fMarkC ? 0 : fTriv;
    CutSetNum = pObj->fMarkC ? (int)pObj->pCopy : -1;
    Cut_NodeComputeCutsSeq( p, pObj->Id, Abc_ObjFaninId0(pObj), Abc_ObjFaninId1(pObj),  
        Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj), Abc_ObjFaninL0(pObj), Abc_ObjFaninL1(pObj), fTriv, CutSetNum );  
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


