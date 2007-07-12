/**CFile****************************************************************

  FileName    [darCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting.]

  Synopsis    [Core of the rewriting package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: darCore.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "darInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the structure with default assignment of parameters.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dar_ManDefaultParams( Dar_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Dar_Par_t) );
    pPars->nCutsMax     = 8;
    pPars->nSubgMax     = 4;
    pPars->fUpdateLevel = 0;
    pPars->fUseZeros    = 0;
    pPars->fVerbose     = 0;
    pPars->fVeryVerbose = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dar_ManRewrite( Aig_Man_t * pAig, Dar_Par_t * pPars )
{
    Dar_Man_t * p;
    ProgressBar * pProgress;
    Dar_Cut_t * pCut;
    Aig_Obj_t * pObj, * pObjNew;
    int i, k, nNodesOld, nNodeBefore, nNodeAfter, Required;
    int clk = 0, clkStart;
    // create rewriting manager
    p = Dar_ManStart( pAig, pPars );
    // remove dangling nodes
    Aig_ManCleanup( pAig );
    // set elementary cuts for the PIs
//    Dar_ManSetupPis( p );
    Aig_ManCleanData( pAig );
    Dar_ObjPrepareCuts( p, Aig_ManConst1(pAig) );
    Aig_ManForEachPi( pAig, pObj, i )
        Dar_ObjPrepareCuts( p, pObj );
//    if ( p->pPars->fUpdateLevel )
//        Aig_NtkStartReverseLevels( p );
    // resynthesize each node once
    clkStart = clock();
    p->nNodesInit = Aig_ManNodeNum(pAig);
    nNodesOld = Vec_PtrSize( pAig->vObjs );
    pProgress = Extra_ProgressBarStart( stdout, nNodesOld );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        if ( !Aig_ObjIsNode(pObj) )
            continue;
        if ( i > nNodesOld )
            break;
        // compute cuts for the node
clk = clock();
        Dar_ObjComputeCuts_rec( p, pObj );
p->timeCuts += clock() - clk;

        // check if there is a trivial cut
        Dar_ObjForEachCut( pObj, pCut, k )
            if ( pCut->nLeaves == 0 || (pCut->nLeaves == 1 && pCut->pLeaves[0] != pObj->Id) )
                break;
        if ( k < (int)pObj->nCuts )
        {
            assert( pCut->nLeaves < 2 );
            if ( pCut->nLeaves == 0 ) // replace by constant
            {
                assert( pCut->uTruth == 0 || pCut->uTruth == 0xFFFF );
                pObjNew = Aig_NotCond( Aig_ManConst1(p->pAig), pCut->uTruth==0 );
            }
            else
            {
                assert( pCut->uTruth == 0xAAAA || pCut->uTruth == 0x5555 );
                pObjNew = Aig_NotCond( Aig_ManObj(p->pAig, pCut->pLeaves[0]), pCut->uTruth==0x5555 );
            }
            // replace the node
            Aig_ObjReplace( pAig, pObj, pObjNew, 1 );
            // remove the old cuts
            Dar_ObjSetCuts( pObj, NULL );
            continue;
        }

        // evaluate the cuts
        p->GainBest = -1;
        Required = 1000000;
        Dar_ObjForEachCut( pObj, pCut, k )
            Dar_LibEval( p, pObj, pCut, Required );
        // check the best gain
        if ( !(p->GainBest > 0 || p->GainBest == 0 && p->pPars->fUseZeros) )
            continue;
        // if we end up here, a rewriting step is accepted
        nNodeBefore = Aig_ManNodeNum( pAig );
        pObjNew = Dar_LibBuildBest( p );
        pObjNew = Aig_NotCond( pObjNew, pObjNew->fPhase ^ pObj->fPhase );
        assert( (int)Aig_Regular(pObjNew)->Level <= Required );
        // replace the node
        Aig_ObjReplace( pAig, pObj, pObjNew, 1 );
        // remove the old cuts
        Dar_ObjSetCuts( pObj, NULL );
        // compare the gains
        nNodeAfter = Aig_ManNodeNum( pAig );
        assert( p->GainBest <= nNodeBefore - nNodeAfter );
        // count gains of this class
        p->ClassGains[p->ClassBest] += nNodeBefore - nNodeAfter;
    }
p->timeTotal = clock() - clkStart;
p->timeOther = p->timeTotal - p->timeCuts - p->timeEval;

    Extra_ProgressBarStop( pProgress );
    p->nCutMemUsed = Aig_MmFixedReadMemUsage(p->pMemCuts)/(1<<20);
    Dar_ManCutsFree( p );
    // stop the rewriting manager
    Dar_ManStop( p );
    // put the nodes into the DFS order and reassign their IDs
//    Aig_NtkReassignIds( p );
    // fix the levels
//    if ( p->pPars->fUpdateLevel )
//        Aig_NtkStopReverseLevels( p );
    // check
    if ( !Aig_ManCheck( pAig ) )
    {
        printf( "Aig_ManRewrite: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_MmFixed_t * Dar_ManComputeCuts( Aig_Man_t * pAig )
{
    Dar_Man_t * p;
    Aig_Obj_t * pObj;
    Aig_MmFixed_t * pMemCuts;
    int i, clk = 0, clkStart = clock();
    int nCutsMax = 0, nCutsTotal = 0;
    // create rewriting manager
    p = Dar_ManStart( pAig, NULL );
    // remove dangling nodes
    Aig_ManCleanup( pAig );
    // set elementary cuts for the PIs
//    Dar_ManSetupPis( p );
    Aig_ManForEachPi( pAig, pObj, i )
        Dar_ObjPrepareCuts( p, pObj );
    // compute cuts for each nodes in the topological order
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( !Aig_ObjIsNode(pObj) )
            continue;
        Dar_ObjComputeCuts( p, pObj );
        nCutsTotal += pObj->nCuts - 1;
        nCutsMax = AIG_MAX( nCutsMax, (int)pObj->nCuts - 1 );
    }
    // free the cuts
    pMemCuts = p->pMemCuts;
    p->pMemCuts = NULL;
//    Dar_ManCutsFree( p );
    // stop the rewriting manager
    Dar_ManStop( p );
    return pMemCuts;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


