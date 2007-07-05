/**CFile****************************************************************

  FileName    [lpkMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast Boolean matching for LUT structures.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: lpkMap.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lpkInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern void Res_UpdateNetworkLevel( Abc_Obj_t * pObjNew, Vec_Vec_t * vLevels );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lpk_IfManStart( Lpk_Man_t * p )
{
    If_Par_t * pPars;
    assert( p->pIfMan == NULL );
    // set defaults
    pPars = ALLOC( If_Par_t, 1 );
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    =  p->pPars->nLutSize;
    pPars->nCutsMax    = 16;
    pPars->nFlowIters  =  0; // 1
    pPars->nAreaIters  =  0; // 1 
    pPars->DelayTarget = -1;
    pPars->fPreprocess =  0;
    pPars->fArea       =  1;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0; //
    pPars->fLatchPaths =  0;
    pPars->fSeqMap     =  0;
    pPars->fVerbose    =  0;
    // internal parameters
    pPars->fTruth      =  0;
    pPars->fUsePerm    =  0; 
    pPars->nLatches    =  0;
    pPars->pLutLib     =  NULL; // Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->fUseBdds    =  0;
    pPars->fUseSops    =  0;
    pPars->fUseCnfs    =  0;
    pPars->fUseMv      =  0;
    // start the mapping manager and set its parameters
    p->pIfMan = If_ManStart( pPars );
    If_ManSetupSetAll( p->pIfMan, 1000 );
    p->pIfMan->pPars->pTimesArr = ALLOC( float, 32 );
}

/**Function*************************************************************

  Synopsis    [Transforms the decomposition graph into the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Lpk_MapPrimeInternal( If_Man_t * pIfMan, Kit_Graph_t * pGraph )
{
    Kit_Node_t * pNode;
    If_Obj_t * pAnd0, * pAnd1;
    int i;
    // check for constant function
    if ( Kit_GraphIsConst(pGraph) )
        return If_ManConst1(pIfMan);
    // check for a literal
    if ( Kit_GraphIsVar(pGraph) )
        return Kit_GraphVar(pGraph)->pFunc;
    // build the AIG nodes corresponding to the AND gates of the graph
    Kit_GraphForEachNode( pGraph, pNode, i )
    {
        pAnd0 = Kit_GraphNode(pGraph, pNode->eEdge0.Node)->pFunc; 
        pAnd1 = Kit_GraphNode(pGraph, pNode->eEdge1.Node)->pFunc; 
        pNode->pFunc = If_ManCreateAnd( pIfMan, 
            If_NotCond( If_Regular(pAnd0), If_IsComplement(pAnd0) ^ pNode->eEdge0.fCompl ), 
            If_NotCond( If_Regular(pAnd1), If_IsComplement(pAnd1) ^ pNode->eEdge1.fCompl ) );
    }
    return pNode->pFunc;
}

/**Function*************************************************************

  Synopsis    [Strashes one logic node using its SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Lpk_MapPrime( Lpk_Man_t * p, unsigned * pTruth, int nVars, If_Obj_t ** ppLeaves )
{
    Kit_Graph_t * pGraph;
    Kit_Node_t * pNode;
    If_Obj_t * pRes;
    int i;
    // derive the factored form
    pGraph = Kit_TruthToGraph( pTruth, nVars, p->vCover );
    if ( pGraph == NULL )
        return NULL;
    // collect the fanins
    Kit_GraphForEachLeaf( pGraph, pNode, i )
        pNode->pFunc = ppLeaves[i];
    // perform strashing
    pRes = Lpk_MapPrimeInternal( p->pIfMan, pGraph );
    pRes = If_NotCond( pRes, Kit_GraphIsComplement(pGraph) );
    Kit_GraphFree( pGraph );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_CutExplore( Lpk_Man_t * p, Lpk_Cut_t * pCut, Kit_DsdNtk_t * pNtk )
{
    extern Abc_Obj_t * Abc_NodeFromIf_rec( Abc_Ntk_t * pNtkNew, If_Man_t * pIfMan, If_Obj_t * pIfObj, Vec_Int_t * vCover );
    Kit_DsdObj_t * pRoot;
    If_Obj_t * pDriver, * ppLeaves[16];
    Abc_Obj_t * pLeaf, * pObjNew;
    int nGain, i;
//    int nOldShared;

    // check special cases
    pRoot = Kit_DsdNtkRoot( pNtk );
    if ( pRoot->Type == KIT_DSD_CONST1 )
    {
        if ( Kit_DsdLitIsCompl(pNtk->Root) )
            pObjNew = Abc_NtkCreateNodeConst0( p->pNtk );
        else
            pObjNew = Abc_NtkCreateNodeConst1( p->pNtk );

        // perform replacement
        pObjNew->Level = p->pObj->Level;
        Abc_ObjReplace( p->pObj, pObjNew );
        Res_UpdateNetworkLevel( pObjNew, p->vLevels );
        p->nGainTotal += pCut->nNodes - pCut->nNodesDup;
        return 1;
    }
    if ( pRoot->Type == KIT_DSD_VAR )
    {
        pObjNew = Abc_NtkObj( p->pNtk, pCut->pLeaves[ Kit_DsdLit2Var(pRoot->pFans[0]) ] );
        if ( Kit_DsdLitIsCompl(pNtk->Root) ^ Kit_DsdLitIsCompl(pRoot->pFans[0]) )
            pObjNew = Abc_NtkCreateNodeInv( p->pNtk, pObjNew );

        // perform replacement
        pObjNew->Level = p->pObj->Level;
        Abc_ObjReplace( p->pObj, pObjNew );
        Res_UpdateNetworkLevel( pObjNew, p->vLevels );
        p->nGainTotal += pCut->nNodes - pCut->nNodesDup;
        return 1;
    }
    assert( pRoot->Type == KIT_DSD_AND || pRoot->Type == KIT_DSD_XOR || pRoot->Type == KIT_DSD_PRIME );

    // start the mapping manager
    if ( p->pIfMan == NULL )
        Lpk_IfManStart( p );

    // prepare the mapping manager
    If_ManRestart( p->pIfMan );
    // create the PI variables
    for ( i = 0; i < p->pPars->nVarsMax; i++ )
        ppLeaves[i] = If_ManCreateCi( p->pIfMan );
    // set the arrival times
    Lpk_CutForEachLeaf( p->pNtk, pCut, pLeaf, i )
        p->pIfMan->pPars->pTimesArr[i] = (float)pLeaf->Level;
    // prepare the PI cuts
    If_ManSetupCiCutSets( p->pIfMan );
    // create the internal nodes
    p->fCalledOnce = 0;
    pDriver = Lpk_MapTree_rec( p, pNtk, ppLeaves, pNtk->Root, NULL );
    if ( pDriver == NULL )
        return 0;
    // create the PO node
    If_ManCreateCo( p->pIfMan, If_Regular(pDriver) );

    // perform mapping
    p->pIfMan->pPars->fAreaOnly = 1;
    If_ManPerformMappingComb( p->pIfMan );

    // compute the gain in area
    nGain = pCut->nNodes - pCut->nNodesDup - (int)p->pIfMan->AreaGlo;
    if ( p->pPars->fVeryVerbose )
        printf( "       Mffc = %2d. Mapped = %2d. Gain = %3d. Depth increase = %d.\n", 
            pCut->nNodes - pCut->nNodesDup, (int)p->pIfMan->AreaGlo, nGain, (int)p->pIfMan->RequiredGlo - (int)p->pObj->Level );

    // quit if there is no gain
    if ( !(nGain > 0 || (p->pPars->fZeroCost && nGain == 0)) )
        return 0;

    // quit if depth increases too much
    if ( (int)p->pIfMan->RequiredGlo - (int)p->pObj->Level > p->pPars->nGrowthLevel )
        return 0;

    // perform replacement
    p->nGainTotal += nGain;
    p->nChanges++;

    // prepare the mapping manager
    If_ManCleanNodeCopy( p->pIfMan );
    If_ManCleanCutData( p->pIfMan );
    // set the PIs of the cut
    Lpk_CutForEachLeaf( p->pNtk, pCut, pLeaf, i )
        If_ObjSetCopy( If_ManCi(p->pIfMan, i), pLeaf );
    // get the area of mapping
    pObjNew = Abc_NodeFromIf_rec( p->pNtk, p->pIfMan, If_Regular(pDriver), p->vCover );
    pObjNew->pData = Hop_NotCond( pObjNew->pData, If_IsComplement(pDriver) );

    // perform replacement
    pObjNew->Level = p->pObj->Level;
    Abc_ObjReplace( p->pObj, pObjNew );
    Res_UpdateNetworkLevel( pObjNew, p->vLevels );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares the mapping manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_Obj_t * Lpk_MapTree_rec( Lpk_Man_t * p, Kit_DsdNtk_t * pNtk, If_Obj_t ** ppLeaves, int iLit, If_Obj_t * pResult )
{
    Kit_DsdObj_t * pObj;
    If_Obj_t * pObjNew, * pFansNew[16];
    unsigned i, iLitFanin;

    assert( iLit >= 0 );

    // consider the case of a gate
    pObj = Kit_DsdNtkObj( pNtk, Kit_DsdLit2Var(iLit) );
    if ( pObj == NULL )
    {
        pObjNew = ppLeaves[Kit_DsdLit2Var(iLit)];
        return If_NotCond( pObjNew, Kit_DsdLitIsCompl(iLit) );
    }
    if ( pObj->Type == KIT_DSD_CONST1 )
    {
        return If_NotCond( If_ManConst1(p->pIfMan), Kit_DsdLitIsCompl(iLit) );
    }
    if ( pObj->Type == KIT_DSD_VAR )
    {
        pObjNew = ppLeaves[Kit_DsdLit2Var(pObj->pFans[0])];
        return If_NotCond( pObjNew, Kit_DsdLitIsCompl(iLit) ^ Kit_DsdLitIsCompl(pObj->pFans[0]) );
    }
    if ( pObj->Type == KIT_DSD_AND )
    {
        assert( pObj->nFans == 2 );
        pFansNew[0] = Lpk_MapTree_rec( p, pNtk, ppLeaves, pObj->pFans[0], NULL );
        pFansNew[1] = pResult? pResult : Lpk_MapTree_rec( p, pNtk, ppLeaves, pObj->pFans[1], NULL );
        if ( pFansNew[0] == NULL || pFansNew[1] == NULL )
            return NULL;
        pObjNew = If_ManCreateAnd( p->pIfMan, pFansNew[0], pFansNew[1] ); 
        return If_NotCond( pObjNew, Kit_DsdLitIsCompl(iLit) );
    }
    if ( pObj->Type == KIT_DSD_XOR )
    {
        int fCompl = Kit_DsdLitIsCompl(iLit);
        assert( pObj->nFans == 2 );
        pFansNew[0] = Lpk_MapTree_rec( p, pNtk, ppLeaves, pObj->pFans[0], NULL );
        pFansNew[1] = pResult? pResult : Lpk_MapTree_rec( p, pNtk, ppLeaves, pObj->pFans[1], NULL );
        if ( pFansNew[0] == NULL || pFansNew[1] == NULL )
            return NULL;
        fCompl ^= If_IsComplement(pFansNew[0]) ^ If_IsComplement(pFansNew[1]);
        pObjNew = If_ManCreateXor( p->pIfMan, If_Regular(pFansNew[0]), If_Regular(pFansNew[1]) );
        return If_NotCond( pObjNew, fCompl );
    }
    assert( pObj->Type == KIT_DSD_PRIME );
    p->nBlocks[pObj->nFans]++;

    // solve for the inputs
    Kit_DsdObjForEachFanin( pNtk, pObj, iLitFanin, i )
    {
        if ( i == 0 )
            pFansNew[i] = pResult? pResult : Lpk_MapTree_rec( p, pNtk, ppLeaves, iLitFanin, NULL );
        else
            pFansNew[i] = Lpk_MapTree_rec( p, pNtk, ppLeaves, iLitFanin, NULL );
        if ( pFansNew[i] == NULL )
            return NULL;
    }
/*
    if ( !p->fCofactoring && p->pPars->nVarsShared > 0 && (int)pObj->nFans > p->pPars->nLutSize )
    {
        pObjNew = Lpk_MapTreeMulti( p, Kit_DsdObjTruth(pObj), pObj->nFans, pFansNew );
        return If_NotCond( pObjNew, Kit_DsdLitIsCompl(iLit) );
    }
*/

    // find best cofactoring variable
    if ( pObj->nFans > 3 && !p->fCalledOnce )
//        pObjNew = Lpk_MapTreeMux_rec( p, Kit_DsdObjTruth(pObj), pObj->nFans, pFansNew );
        pObjNew = Lpk_MapSuppRedDec_rec( p, Kit_DsdObjTruth(pObj), pObj->nFans, pFansNew );
    else
        pObjNew = Lpk_MapPrime( p, Kit_DsdObjTruth(pObj), pObj->nFans, pFansNew );
    return If_NotCond( pObjNew, Kit_DsdLitIsCompl(iLit) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


