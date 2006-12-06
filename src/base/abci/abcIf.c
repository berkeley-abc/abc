/**CFile****************************************************************

  FileName    [abcIf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface with the FPGA mapping package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: abcIf.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "if.h"
#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static If_Man_t *  Abc_NtkToIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
static Abc_Ntk_t * Abc_NtkFromIf( If_Man_t * pIfMan, Abc_Ntk_t * pNtk );
static Abc_Obj_t * Abc_NodeFromIf_rec( Abc_Ntk_t * pNtkNew, If_Man_t * pIfMan, If_Obj_t * pIfObj );
static Hop_Obj_t * Abc_NodeIfToHop( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj );
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars )
{
    Abc_Ntk_t * pNtkNew;
    If_Man_t * pIfMan;

    assert( Abc_NtkIsStrash(pNtk) );

    // print a warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
//        printf( "Performing FPGA mapping with choices.\n" );
        printf( "Currently mapping with choices is not enabled.\n" );
        return NULL;
    }

    // get timing information
    pPars->pTimesArr = Abc_NtkGetCiArrivalFloats(pNtk);
    pPars->pTimesReq = NULL;

    // perform FPGA mapping
    pIfMan = Abc_NtkToIf( pNtk, pPars );    
    if ( pIfMan == NULL )
        return NULL;
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        If_ManStop( pIfMan );
        return NULL;
    }

    // transform the result of mapping into the new network
    pNtkNew = Abc_NtkFromIf( pIfMan, pNtk );
    if ( pNtkNew == NULL )
        return NULL;
    If_ManStop( pIfMan );

    // duplicate EXDC
    if ( pNtk->pExdc )
        pNtkNew->pExdc = Abc_NtkDup( pNtk->pExdc );

    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkIf: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Man_t * Abc_NtkToIf( Abc_Ntk_t * pNtk, If_Par_t * pPars )
{
    ProgressBar * pProgress;
    If_Man_t * pIfMan;
    Abc_Obj_t * pNode, * pFanin, * pPrev;
    int i;

    assert( Abc_NtkIsStrash(pNtk) );

    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );

    // create PIs and remember them in the old nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)If_ManConst1( pIfMan );
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)If_ManCreatePi( pIfMan );

    // load the AIG into the mapper
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
    Abc_AigForEachAnd( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // add the node to the mapper
        pNode->pCopy = (Abc_Obj_t *)If_ManCreateAnd( pIfMan, 
            (If_Obj_t *)Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode), 
            (If_Obj_t *)Abc_ObjFanin1(pNode)->pCopy, Abc_ObjFaninC1(pNode) );
        // set up the choice node
        if ( Abc_AigNodeIsChoice( pNode ) )
            for ( pPrev = pNode, pFanin = pNode->pData; pFanin; pPrev = pFanin, pFanin = pFanin->pData )
                If_ObjSetChoice( (If_Obj_t *)pPrev->pCopy, (If_Obj_t *)pFanin->pCopy );
    }
    Extra_ProgressBarStop( pProgress );

    // set the primary outputs without copying the phase
    Abc_NtkForEachCo( pNtk, pNode, i )
        If_ManCreatePo( pIfMan, (If_Obj_t *)Abc_ObjFanin0(pNode)->pCopy, Abc_ObjFaninC0(pNode) );
    return pIfMan;
}

/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description [Assuming the copy field of the mapped nodes are NULL.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromIf( If_Man_t * pIfMan, Abc_Ntk_t * pNtk )
{
    ProgressBar * pProgress;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pNodeNew;
    int i, nDupGates;
    // create the new network
    if ( pIfMan->pPars->fUseBdds )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_BDD );
    else if ( pIfMan->pPars->fUseSops )
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    else
        pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_AIG );
    // prepare the mapping manager
    If_ManCleanNodeCopy( pIfMan );
    If_ManCleanCutData( pIfMan );
    // make the mapper point to the new network
    If_ObjSetCopy( If_ManConst1(pIfMan), Abc_NtkCreateNodeConst1(pNtkNew) );
    Abc_NtkForEachCi( pNtk, pNode, i )
        If_ObjSetCopy( If_ManPi(pIfMan, i), pNode->pCopy );
    // process the nodes in topological order
    pProgress = Extra_ProgressBarStart( stdout, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        pNodeNew = Abc_NodeFromIf_rec( pNtkNew, pIfMan, If_ObjFanin0(If_ManPo(pIfMan, i)) );
        pNodeNew = Abc_ObjNotCond( pNodeNew, If_ObjFaninC0(If_ManPo(pIfMan, i)) );
        Abc_ObjAddFanin( pNode->pCopy, pNodeNew );
    }
    Extra_ProgressBarStop( pProgress );
    // remove the constant node if not used
    pNodeNew = (Abc_Obj_t *)If_ObjCopy( If_ManConst1(pIfMan) );
    if ( Abc_ObjFanoutNum(pNodeNew) == 0 )
        Abc_NtkDeleteObj( pNodeNew );
    // decouple the PO driver nodes to reduce the number of levels
    nDupGates = Abc_NtkLogicMakeSimpleCos( pNtkNew, 1 );
//    if ( nDupGates && If_ManReadVerbose(pIfMan) )
//        printf( "Duplicated %d gates to decouple the CO drivers.\n", nDupGates );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derive one node after FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeFromIf_rec( Abc_Ntk_t * pNtkNew, If_Man_t * pIfMan, If_Obj_t * pIfObj )
{
    Abc_Obj_t * pNodeNew;
    If_Cut_t * pCutBest;
    If_Obj_t * pIfLeaf;
    int i;
    // return if the result if known
    pNodeNew = (Abc_Obj_t *)If_ObjCopy( pIfObj );
    if ( pNodeNew )
        return pNodeNew;
    assert( pIfObj->Type == IF_AND );
    // get the parameters of the best cut
    // create a new node 
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    pCutBest = If_ObjCutBest( pIfObj );
    If_CutForEachLeaf( pIfMan, pCutBest, pIfLeaf, i )
        Abc_ObjAddFanin( pNodeNew, Abc_NodeFromIf_rec(pNtkNew, pIfMan, pIfLeaf) );
    // derive the function of this node
    if ( pIfMan->pPars->fTruth )
    {
        if ( pIfMan->pPars->fUseBdds )
        { 
            extern void Abc_NodeBddReorder( void * p, Abc_Obj_t * pNode );
            extern DdNode * Kit_TruthToBdd( DdManager * dd, unsigned * pTruth, int nVars );
            // transform truth table into the BDD 
            pNodeNew->pData = Kit_TruthToBdd( pNtkNew->pManFunc, If_CutTruth(pCutBest), pCutBest->nLimit );
            // reorder the fanins to minimize the BDD size
            Abc_NodeBddReorder( pIfMan->pPars->pReoMan, pNodeNew );
        }
        else if ( pIfMan->pPars->fUseSops ) 
        {
            Vec_Int_t * vCover = Vec_IntAlloc( 1 << 16 );
            // transform truth table into the SOP
            int RetValue = Kit_TruthIsop( If_CutTruth(pCutBest), pCutBest->nLimit, vCover, 0 );
            assert( RetValue == 0 );
            // derive the AIG for that tree
            pNodeNew->pData = Abc_SopCreateFromIsop( pNtkNew->pManFunc, pCutBest->nLimit, vCover );
            Vec_IntFree( vCover );
        }
        else 
        {
            extern Hop_Obj_t * Kit_GraphToHop( Hop_Man_t * pMan, Kit_Graph_t * pGraph );
            Vec_Int_t * vMemory = Vec_IntAlloc( 1 << 16 );
            // transform truth table into the decomposition tree
            Kit_Graph_t * pGraph = Kit_TruthToGraph( If_CutTruth(pCutBest), pCutBest->nLimit, vMemory );
            // derive the AIG for the decomposition tree
            pNodeNew->pData = Kit_GraphToHop( pNtkNew->pManFunc, pGraph );
            Kit_GraphFree( pGraph );
            Vec_IntFree( vMemory );
        }
    }
    else
        pNodeNew->pData = Abc_NodeIfToHop( pNtkNew->pManFunc, pIfMan, pIfObj );
    If_ObjSetCopy( pIfObj, pNodeNew );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfToHop_rec( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Ptr_t * vVisited )
{
    If_Cut_t * pCut;
    Hop_Obj_t * gFunc, * gFunc0, * gFunc1;
    // get the best cut
    pCut = If_ObjCutTriv(pIfObj);
    // if the cut is visited, return the result
    if ( If_CutData(pCut) )
        return If_CutData(pCut);
    // compute the functions of the children
    gFunc0 = Abc_NodeIfToHop_rec( pHopMan, pIfMan, pIfObj->pFanin0, vVisited );
    gFunc1 = Abc_NodeIfToHop_rec( pHopMan, pIfMan, pIfObj->pFanin1, vVisited );
    // get the function of the cut
    gFunc  = Hop_And( pHopMan, Hop_NotCond(gFunc0, pIfObj->fCompl0), Hop_NotCond(gFunc1, pIfObj->fCompl1) );  
    assert( If_CutData(pCut) == NULL );
    If_CutSetData( pCut, gFunc );
    // add this cut to the visited list
    Vec_PtrPush( vVisited, pCut );
    return gFunc;
}

/**Function*************************************************************

  Synopsis    [Derives the truth table for one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfToHop( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj )
{
    If_Cut_t * pCut;
    Hop_Obj_t * gFunc;
    If_Obj_t * pLeaf;
    int i;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    assert( pCut->nLeaves > 1 );
    // set the leaf variables
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetData( If_ObjCutTriv(pLeaf), Hop_IthVar(pHopMan, i) );
    // recursively compute the function while collecting visited cuts
    Vec_PtrClear( pIfMan->vTemp );
    gFunc = Abc_NodeIfToHop_rec( pHopMan, pIfMan, pIfObj, pIfMan->vTemp ); 
//    printf( "%d ", Vec_PtrSize(p->vTemp) );
    // clean the cuts
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetData( If_ObjCutTriv(pLeaf), NULL );
    Vec_PtrForEachEntry( pIfMan->vTemp, pCut, i )
        If_CutSetData( pCut, NULL );
    return gFunc;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


