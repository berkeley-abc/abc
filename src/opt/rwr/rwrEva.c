/**CFile****************************************************************

  FileName    [rwrDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Evaluation and decomposition procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrDec.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"
#include "dec.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Dec_Graph_t * Rwr_CutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Cut_Cut_t * pCut, Vec_Ptr_t * vFaninsCur, int nNodesSaved, int LevelMax, int * pGainBest );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs rewriting for one node.]

  Description [This procedure considers all the cuts computed for the node
  and tries to rewrite each of them using the "forest" of different AIG
  structures precomputed and stored in the RWR manager. 
  Determines the best rewriting and computes the gain in the number of AIG
  nodes in the final network. In the end, p->vFanins contains information 
  about the best cut that can be used for rewriting, while p->pGraph gives 
  the decomposition dag (represented using decomposition graph data structure).
  Returns gain in the number of nodes or -1 if node cannot be rewritten.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rwr_NodeRewrite( Rwr_Man_t * p, Cut_Man_t * pManCut, Abc_Obj_t * pNode, int fUpdateLevel, int fUseZeros )
{
    int fVeryVerbose = 0;
    Dec_Graph_t * pGraph;
    Cut_Cut_t * pCut;
    Abc_Obj_t * pFanin;
    unsigned uPhase, uTruthBest, uTruth;
    char * pPerm;
    int Required, nNodesSaved, nNodesSaveCur;
    int i, GainCur, GainBest = -1;
    int clk, clk2;

    p->nNodesConsidered++;
    // get the required times
    Required = fUpdateLevel? Abc_NodeReadRequiredLevel(pNode) : ABC_INFINITY;
    // get the node's cuts
clk = clock();
    pCut = (Cut_Cut_t *)Abc_NodeGetCutsRecursive( pManCut, pNode, 0, 0 );
    assert( pCut != NULL );
p->timeCut += clock() - clk;

    // go through the cuts
clk = clock();
    for ( pCut = pCut->pNext; pCut; pCut = pCut->pNext )
    {
        // consider only 4-input cuts
        if ( pCut->nLeaves < 4 )
            continue;
        // get the fanin permutation
        uTruth = 0xFFFF & *Cut_CutReadTruth(pCut);
        pPerm = p->pPerms4[ p->pPerms[uTruth] ];
        uPhase = p->pPhases[uTruth];
        // collect fanins with the corresponding permutation/phase
        Vec_PtrClear( p->vFaninsCur );
        Vec_PtrFill( p->vFaninsCur, (int)pCut->nLeaves, 0 );
        for ( i = 0; i < (int)pCut->nLeaves; i++ )
        {
            pFanin = Abc_NtkObj( pNode->pNtk, pCut->pLeaves[pPerm[i]] );
            if ( pFanin == NULL )
                break;
            pFanin = Abc_ObjNotCond(pFanin, ((uPhase & (1<<i)) > 0) );
            Vec_PtrWriteEntry( p->vFaninsCur, i, pFanin );
        }
        if ( i != (int)pCut->nLeaves )
        {
            p->nCutsBad++;
            continue;
        }
        p->nCutsGood++;

clk2 = clock();
        // mark the fanin boundary 
        Vec_PtrForEachEntry( p->vFaninsCur, pFanin, i )
            Abc_ObjRegular(pFanin)->vFanouts.nSize++;
        // label MFFC with current ID
        Abc_NtkIncrementTravId( pNode->pNtk );
        nNodesSaved = Abc_NodeMffcLabel( pNode );
        // unmark the fanin boundary
        Vec_PtrForEachEntry( p->vFaninsCur, pFanin, i )
            Abc_ObjRegular(pFanin)->vFanouts.nSize--;
p->timeMffc += clock() - clk2;

        // evaluate the cut
clk2 = clock();
        pGraph = Rwr_CutEvaluate( p, pNode, pCut, p->vFaninsCur, nNodesSaved, Required, &GainCur );
p->timeEval += clock() - clk2;

        // check if the cut is better than the current best one
        if ( pGraph != NULL && GainBest < GainCur )
        {
            // save this form
            nNodesSaveCur = nNodesSaved;
            GainBest  = GainCur;
            p->pGraph  = pGraph;
            p->fCompl = ((uPhase & (1<<4)) > 0);
            uTruthBest = 0xFFFF & *Cut_CutReadTruth(pCut);
            // collect fanins in the
            Vec_PtrClear( p->vFanins );
            Vec_PtrForEachEntry( p->vFaninsCur, pFanin, i )
                Vec_PtrPush( p->vFanins, pFanin );
        }
    }
p->timeRes += clock() - clk;

    if ( GainBest == -1 )
        return -1;

    // copy the leaves
    Vec_PtrForEachEntry( p->vFanins, pFanin, i )
        Dec_GraphNode(p->pGraph, i)->pFunc = pFanin;

    p->nScores[p->pMap[uTruthBest]]++;
    p->nNodesGained += GainBest;
    if ( fUseZeros || GainBest > 0 )
        p->nNodesRewritten++;

    // report the progress
    if ( fVeryVerbose && GainBest > 0 )
    {
        printf( "Node %6s :   ", Abc_ObjName(pNode) );
        printf( "Fanins = %d. ", p->vFanins->nSize );
        printf( "Save = %d.  ", nNodesSaveCur );
        printf( "Add = %d.  ",  nNodesSaveCur-GainBest );
        printf( "GAIN = %d.  ", GainBest );
        printf( "Cone = %d.  ", p->pGraph? Dec_GraphNodeNum(p->pGraph) : 0 );
        printf( "Class = %d.  ", p->pMap[uTruthBest] );
        printf( "\n" );
    }
    return GainBest;
}

/**Function*************************************************************

  Synopsis    [Evaluates the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dec_Graph_t * Rwr_CutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Cut_Cut_t * pCut, Vec_Ptr_t * vFaninsCur, int nNodesSaved, int LevelMax, int * pGainBest )
{
    Vec_Ptr_t * vSubgraphs;
    Dec_Graph_t * pGraphBest, * pGraphCur;
    Rwr_Node_t * pNode, * pFanin;
    int nNodesAdded, GainBest, i, k;
    unsigned uTruth;
    // find the matching class of subgraphs
    uTruth = 0xFFFF & *Cut_CutReadTruth(pCut);
    vSubgraphs = Vec_VecEntry( p->vClasses, p->pMap[uTruth] );
    p->nSubgraphs += vSubgraphs->nSize;
    // determine the best subgraph
    GainBest = -1;
    Vec_PtrForEachEntry( vSubgraphs, pNode, i )
    {
        // get the current graph
        pGraphCur = (Dec_Graph_t *)pNode->pNext;
        // copy the leaves
        Vec_PtrForEachEntry( vFaninsCur, pFanin, k )
            Dec_GraphNode(pGraphCur, k)->pFunc = pFanin;
        // detect how many unlabeled nodes will be reused
        nNodesAdded = Dec_GraphToNetworkCount( pRoot, pGraphCur, nNodesSaved, LevelMax );
        if ( nNodesAdded == -1 )
            continue;
        assert( nNodesSaved >= nNodesAdded );
        // count the gain at this node
        if ( GainBest < nNodesSaved - nNodesAdded )
        {
            GainBest   = nNodesSaved - nNodesAdded;
            pGraphBest = pGraphCur;

//            if ( GainBest > 0 )
//            printf( "%d %d  ", nNodesSaved, nNodesAdded );
        }
    }
    if ( GainBest == -1 )
        return NULL;
    *pGainBest = GainBest;
    return pGraphBest;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


