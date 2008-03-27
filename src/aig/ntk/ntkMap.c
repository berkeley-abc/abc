/**CFile****************************************************************

  FileName    [ntkMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Interface to technology mapping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkMap.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"
#include "if.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManSetIfParsDefault( If_Par_t * pPars )
{
//    extern void * Abc_FrameReadLibLut();
    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
//    pPars->nLutSize    = -1;
    pPars->nLutSize    =  6;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  1;
    pPars->nAreaIters  =  2;
    pPars->DelayTarget = -1;
    pPars->Epsilon     =  (float)0.01;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0;
    pPars->fLatchPaths =  0;
    pPars->fEdge       =  1;
    pPars->fCutMin     =  1;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  1;
    // internal parameters
    pPars->fTruth      =  0;
    pPars->nLatches    =  0;
    pPars->fLiftLeaves =  0;
//    pPars->pLutLib     =  Abc_FrameReadLibLut();
    pPars->pLutLib     =  NULL;
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->pFuncCost   =  NULL;   
/*
    if ( pPars->nLutSize == -1 )
    {
        if ( pPars->pLutLib == NULL )
        {
            printf( "The LUT library is not given.\n" );
            return;
        }
        // get LUT size from the library
        pPars->nLutSize = pPars->pLutLib->LutMax;
    }
*/
}

/**Function*************************************************************

  Synopsis    [Load the network into FPGA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Man_t * Ntk_ManToIf( Aig_Man_t * p, If_Par_t * pPars )
{
    If_Man_t * pIfMan;
    Aig_Obj_t * pNode;//, * pFanin, * pPrev;
    int i;
    // start the mapping manager and set its parameters
    pIfMan = If_ManStart( pPars );
    // print warning about excessive memory usage
//    if ( 1.0 * Aig_ManObjNum(p) * pIfMan->nObjBytes / (1<<30) > 1.0 )
//        printf( "Warning: The mapper will allocate %.1f Gb for to represent the subject graph with %d AIG nodes.\n", 
//            1.0 * Aig_ManObjNum(p) * pIfMan->nObjBytes / (1<<30), Aig_ManObjNum(p) );
    // load the AIG into the mapper
    Aig_ManForEachObj( p, pNode, i )
    {
        if ( Aig_ObjIsAnd(pNode) )
            pNode->pData = (Aig_Obj_t *)If_ManCreateAnd( pIfMan, 
                If_NotCond( (If_Obj_t *)Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ), 
                If_NotCond( (If_Obj_t *)Aig_ObjFanin1(pNode)->pData, Aig_ObjFaninC1(pNode) ) );
        else if ( Aig_ObjIsPi(pNode) )
        {
            pNode->pData = If_ManCreateCi( pIfMan );
            ((If_Obj_t *)pNode->pData)->Level = pNode->Level;
            if ( pIfMan->nLevelMax < (int)pNode->Level )
                pIfMan->nLevelMax = (int)pNode->Level;
        }
        else if ( Aig_ObjIsPo(pNode) )
            pNode->pData = If_ManCreateCo( pIfMan, If_NotCond( Aig_ObjFanin0(pNode)->pData, Aig_ObjFaninC0(pNode) ) );
        else if ( Aig_ObjIsConst1(pNode) )
            Aig_ManConst1(p)->pData = If_ManConst1( pIfMan );
        else // add the node to the mapper
            assert( 0 );
        // set up the choice node
//        if ( Aig_AigNodeIsChoice( pNode ) )
//        {
//            pIfMan->nChoices++;
//            for ( pPrev = pNode, pFanin = pNode->pData; pFanin; pPrev = pFanin, pFanin = pFanin->pData )
//                If_ObjSetChoice( (If_Obj_t *)pPrev->pData, (If_Obj_t *)pFanin->pData );
//            If_ManCreateChoice( pIfMan, (If_Obj_t *)pNode->pData );
//        }
        {
            If_Obj_t * pIfObj = pNode->pData;
            assert( !If_IsComplement(pIfObj) );
            assert( pIfObj->Id == pNode->Id );
        }
    }
    return pIfMan;
}


/**Function*************************************************************

  Synopsis    [Recursively derives the truth table for the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Ntk_NodeIfToHop2_rec( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Ptr_t * vVisited )
{
    If_Cut_t * pCut;
    If_Obj_t * pTemp;
    Hop_Obj_t * gFunc, * gFunc0, * gFunc1;
    // get the best cut
    pCut = If_ObjCutBest(pIfObj);
    // if the cut is visited, return the result
    if ( If_CutData(pCut) )
        return If_CutData(pCut);
    // mark the node as visited
    Vec_PtrPush( vVisited, pCut );
    // insert the worst case
    If_CutSetData( pCut, (void *)1 );
    // skip in case of primary input
    if ( If_ObjIsCi(pIfObj) )
        return If_CutData(pCut);
    // compute the functions of the children
    for ( pTemp = pIfObj; pTemp; pTemp = pTemp->pEquiv )
    {
        gFunc0 = Ntk_NodeIfToHop2_rec( pHopMan, pIfMan, pTemp->pFanin0, vVisited );
        if ( gFunc0 == (void *)1 )
            continue;
        gFunc1 = Ntk_NodeIfToHop2_rec( pHopMan, pIfMan, pTemp->pFanin1, vVisited );
        if ( gFunc1 == (void *)1 )
            continue;
        // both branches are solved
        gFunc = Hop_And( pHopMan, Hop_NotCond(gFunc0, pTemp->fCompl0), Hop_NotCond(gFunc1, pTemp->fCompl1) ); 
        if ( pTemp->fPhase != pIfObj->fPhase )
            gFunc = Hop_Not(gFunc);
        If_CutSetData( pCut, gFunc );
        break;
    }
    return If_CutData(pCut);
}

/**Function*************************************************************

  Synopsis    [Derives the truth table for one cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Ntk_NodeIfToHop( Hop_Man_t * pHopMan, If_Man_t * pIfMan, If_Obj_t * pIfObj )
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
        If_CutSetData( If_ObjCutBest(pLeaf), Hop_IthVar(pHopMan, i) );
    // recursively compute the function while collecting visited cuts
    Vec_PtrClear( pIfMan->vTemp );
    gFunc = Ntk_NodeIfToHop2_rec( pHopMan, pIfMan, pIfObj, pIfMan->vTemp ); 
    if ( gFunc == (void *)1 )
    {
        printf( "Ntk_NodeIfToHop(): Computing local AIG has failed.\n" );
        return NULL;
    }
//    printf( "%d ", Vec_PtrSize(p->vTemp) );
    // clean the cuts
    If_CutForEachLeaf( pIfMan, pCut, pLeaf, i )
        If_CutSetData( If_ObjCutBest(pLeaf), NULL );
    Vec_PtrForEachEntry( pIfMan->vTemp, pCut, i )
        If_CutSetData( pCut, NULL );
    return gFunc;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Man_t * Ntk_ManFromIf( If_Man_t * pIfMan, Aig_Man_t * p )
{
    Ntk_Man_t * pNtk;
    Ntk_Obj_t * pObjNew;
    Aig_Obj_t * pObj;
    If_Obj_t * pIfObj;
    If_Cut_t * pCutBest;
    int i, k, nLeaves, * ppLeaves;
    assert( Aig_ManPiNum(p) == If_ManCiNum(pIfMan) );
    assert( Aig_ManPoNum(p) == If_ManCoNum(pIfMan) );
    assert( Aig_ManNodeNum(p) == If_ManAndNum(pIfMan) );
    If_ManCleanCutData( pIfMan );
    // construct the network
    pNtk = Ntk_ManAlloc();
    pNtk->pName = Aig_UtilStrsav( p->pName );
    pNtk->pSpec = Aig_UtilStrsav( p->pSpec );
    Aig_ManForEachObj( p, pObj, i )
    {
        pIfObj = If_ManObj( pIfMan, i );
        if ( pIfObj->nRefs == 0 && !If_ObjIsTerm(pIfObj) )
            continue;
        if ( Aig_ObjIsNode(pObj) )
        {
            pCutBest = If_ObjCutBest( pIfObj );
            nLeaves  = If_CutLeaveNum( pCutBest ); 
            ppLeaves = If_CutLeaves( pCutBest );
            // create node
            pObjNew = Ntk_ManCreateNode( pNtk, nLeaves, pIfObj->nRefs );
            for ( k = 0; k < nLeaves; k++ )
                Ntk_ObjAddFanin( pObjNew, Aig_ManObj(p, ppLeaves[k])->pData );
            // get the functionality
            pObjNew->pFunc = Ntk_NodeIfToHop( pNtk->pManHop, pIfMan, pIfObj );
        }
        else if ( Aig_ObjIsPi(pObj) )
            pObjNew = Ntk_ManCreateCi( pNtk, pIfObj->nRefs );
        else if ( Aig_ObjIsPo(pObj) )
        {
            pObjNew = Ntk_ManCreateCo( pNtk );
            pObjNew->fCompl = Aig_ObjFaninC0(pObj);
            Ntk_ObjAddFanin( pObjNew, Aig_ObjFanin0(pObj)->pData );
        }
        else if ( Aig_ObjIsConst1(pObj) )
        {
            pObjNew = Ntk_ManCreateNode( pNtk, 0, pIfObj->nRefs );
            pObjNew->pFunc = Hop_ManConst1( pNtk->pManHop );
        }
        else
            assert( 0 );
        pObj->pData = pObjNew;
    }
    pNtk->pManTime = Tim_ManDup( pIfMan->pManTim, 0 );
    return pNtk;
}

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntk_Man_t * Ntk_MappingIf( Aig_Man_t * p, Tim_Man_t * pManTime, If_Par_t * pPars )
{
    Ntk_Man_t * pNtk;
    If_Man_t * pIfMan;
    // perform FPGA mapping
    // set the arrival times
    pPars->pTimesArr = ALLOC( float, Aig_ManPiNum(p) );
    memset( pPars->pTimesArr, 0, sizeof(float) * Aig_ManPiNum(p) );
    // translate into the mapper
    pIfMan = Ntk_ManToIf( p, pPars );    
    if ( pIfMan == NULL )
        return NULL;
    pIfMan->pManTim = Tim_ManDup( pManTime, 0 );
    if ( !If_ManPerformMapping( pIfMan ) )
    {
        If_ManStop( pIfMan );
        return NULL;
    }
    // transform the result of mapping into the new network
    pNtk = Ntk_ManFromIf( pIfMan, p );
    If_ManStop( pIfMan );
    return pNtk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


