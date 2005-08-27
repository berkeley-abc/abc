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
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Vec_Int_t * Rwr_CutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Cut_Cut_t * pCut, Vec_Ptr_t * vFaninsCur, int nNodesSaved, int LevelMax, int * pGainBest );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs rewriting for one node.]

  Description [This procedure considers all the cuts computed for the node
  and tries to rewrite each of them using the "forest" of different AIG
  structures precomputed and stored in the RWR manager. 
  Determines the best rewriting and computes the gain in the number of AIG
  nodes in the final network. In the end, p->vFanins contains information 
  about the best cut that can be used for rewriting, while p->vForm gives 
  the decomposition tree (represented using factored form data structure).
  Returns gain in the number of nodes or -1 if node cannot be rewritten.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Rwr_NodeRewrite( Rwr_Man_t * p, Cut_Man_t * pManCut, Abc_Obj_t * pNode, int fUseZeros )
{
    int fVeryVerbose = 0;
    Vec_Int_t * vForm;
    Cut_Cut_t * pCut;
    Abc_Obj_t * pFanin;
    unsigned uPhase, uTruthBest;
    char * pPerm;
    int Required, nNodesSaved;
    int i, GainCur, GainBest = -1;
    int clk;

    p->nNodesConsidered++;
    // get the required times
    Required = Abc_NodeReadRequiredLevel( pNode );
    // get the node's cuts
clk = clock();
    pCut = (Cut_Cut_t *)Abc_NodeGetCutsRecursive( pManCut, pNode );
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
        pPerm = p->pPerms4[ p->pPerms[pCut->uTruth] ];
        uPhase = p->pPhases[pCut->uTruth];
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

        // mark the fanin boundary 
        Vec_PtrForEachEntry( p->vFaninsCur, pFanin, i )
            Abc_ObjRegular(pFanin)->vFanouts.nSize++;
        // label MFFC with current ID
        Abc_NtkIncrementTravId( pNode->pNtk );
        nNodesSaved = Abc_NodeMffcLabel( pNode );
        // unmark the fanin boundary
        Vec_PtrForEachEntry( p->vFaninsCur, pFanin, i )
            Abc_ObjRegular(pFanin)->vFanouts.nSize--;

        // evaluate the cut
        vForm = Rwr_CutEvaluate( p, pNode, pCut, p->vFaninsCur, nNodesSaved, Required, &GainCur );

        // check if the cut is better than the current best one
        if ( vForm != NULL && GainBest < GainCur )
        {
            // save this form
            GainBest  = GainCur;
            p->vForm  = vForm;
            p->fCompl = ((uPhase & (1<<4)) > 0);
            uTruthBest = pCut->uTruth;
            // collect fanins in the
            Vec_PtrClear( p->vFanins );
            Vec_PtrForEachEntry( p->vFaninsCur, pFanin, i )
                Vec_PtrPush( p->vFanins, pFanin );
        }
    }
p->timeRes += clock() - clk;

    if ( GainBest == -1 || GainBest == 0 && !fUseZeros )
        return GainBest;

    p->nScores[p->pMap[uTruthBest]]++;
    p->nNodesRewritten++;
    p->nNodesGained += GainBest;

    // report the progress
    if ( fVeryVerbose )
    {
        printf( "Node %6s :   ", Abc_ObjName(pNode) );
        printf( "Fanins = %d. ", p->vFanins->nSize );
        printf( "Cone = %2d.  ", p->vForm->nSize - 4 );
        printf( "GAIN = %2d.  ", GainBest );
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
Vec_Int_t * Rwr_CutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Cut_Cut_t * pCut, Vec_Ptr_t * vFaninsCur, int nNodesSaved, int LevelMax, int * pGainBest )
{
    Vec_Ptr_t * vSubgraphs;
    Vec_Int_t * vFormBest;
    Rwr_Node_t * pNode;
    int nNodesAdded, GainBest = -1, i;
    int clk = clock();
    // find the matching class of subgraphs
    vSubgraphs = Vec_VecEntry( p->vClasses, p->pMap[pCut->uTruth] );
    p->nSubgraphs += vSubgraphs->nSize;
    // determine the best subgraph
    Vec_PtrForEachEntry( vSubgraphs, pNode, i )
    {
        // detect how many unlabeled nodes will be reused
        nNodesAdded = Abc_NodeStrashDecCount( pRoot->pNtk->pManFunc, pRoot, vFaninsCur, 
            (Vec_Int_t *)pNode->pNext, p->vLevNums, nNodesSaved, LevelMax );
        if ( nNodesAdded == -1 )
            continue;
        assert( nNodesSaved >= nNodesAdded );
        // count the gain at this node
        if ( GainBest < nNodesSaved - nNodesAdded )
        {
            GainBest  = nNodesSaved - nNodesAdded;
            vFormBest = (Vec_Int_t *)pNode->pNext;
        }
    }
p->timeEval += clock() - clk;
    if ( GainBest == -1 )
        return NULL;
    *pGainBest = GainBest;
    return vFormBest;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


