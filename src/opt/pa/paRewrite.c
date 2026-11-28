/**CFile****************************************************************

  FileName    [paRewrite.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Placement-aware rewriting.]

  Author      [Anqi Lu, from abcRewrite.c and rwrEva.c by Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paRewrite.c,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"
#include <math.h>
#include "opt/rwr/rwr.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the rewriting library of a frame.]

  Description [The rewriting library of the current frame; its forest and
               class tables do not depend on the network.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void * Pa_RwrAlloc( void )
{
    return Rwr_ManStart( 0 );
}
/**Function*************************************************************

  Synopsis    [Stops the rewriting library of a frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_RwrFree( void * p )
{
    Rwr_ManStop( (Rwr_Man_t *)p );
}


static Cut_Man_t * Pa_NtkStartCutManForRewrite( Abc_Ntk_t * pNtk );

static Dec_Graph_t * Pa_RwrCutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Cut_Cut_t * pCut, Vec_Ptr_t * vFaninsCur,
                                        int nNodesSaved, int LevelMax, int * pGainBest, double * pScoreBest,
                                        int fRootComplement );

/**Function*************************************************************

  Synopsis    [Performs rewriting for one node.]

  Description [This procedure considers all the 4-input cuts computed for
  the node and tries to rewrite each of them using the "forest" of different
  AIG structures precomputed and stored in the RWR manager. The best
  rewriting is the one with the highest placement score (ties: higher node
  gain). In the end, p->vFanins contains information about the best cut,
  while p->pGraph gives the decomposition dag. Returns the node gain, or
  -ABC_INFINITY if no candidate has a positive score.]

***********************************************************************/
static int Pa_RwrNodeRewrite( Rwr_Man_t * p, Cut_Man_t * pManCut, Abc_Obj_t * pNode )
{
    Dec_Graph_t * pGraph;
    Cut_Cut_t * pCut;
    Abc_Obj_t * pFanin;
    unsigned uPhase;
    unsigned uTruth;
    char * pPerm;
    int Required, nNodesSaved;
    int i, GainCur = -1, GainBest = -1;
    double ScoreCur = -ABC_INFINITY, ScoreBest = -ABC_INFINITY;

    // get the required times
    Required = Abc_ObjRequiredLevel( pNode );

    // get the node's cuts
    pCut = (Cut_Cut_t *)Abc_NodeGetCutsRecursive( pManCut, pNode, 0, 0 );
    assert( pCut != NULL );

    // go through the cuts
    for ( pCut = pCut->pNext; pCut; pCut = pCut->pNext )
    {
        // consider only 4-input cuts
        if ( pCut->nLeaves < 4 )
            continue;

        // get the fanin permutation
        uTruth = 0xFFFF & *Cut_CutReadTruth( pCut );
        pPerm = p->pPerms4[(int)p->pPerms[uTruth]];
        uPhase = p->pPhases[uTruth];
        // collect fanins with the corresponding permutation/phase
        Vec_PtrClear( p->vFaninsCur );
        Vec_PtrFill( p->vFaninsCur, (int)pCut->nLeaves, 0 );
        for ( i = 0; i < (int)pCut->nLeaves; i++ )
        {
            pFanin = Abc_NtkObj( pNode->pNtk, pCut->pLeaves[(int)pPerm[i]] );
            if ( pFanin == NULL )
                break;
            pFanin = Abc_ObjNotCond( pFanin, ( ( uPhase & ( 1 << i ) ) > 0 ) );
            Vec_PtrWriteEntry( p->vFaninsCur, i, pFanin );
        }
        if ( i != (int)pCut->nLeaves )
            continue;

        {
            int Counter = 0;
            Vec_PtrForEachEntry( Abc_Obj_t *, p->vFaninsCur, pFanin,
                                 i ) if ( Abc_ObjFanoutNum( Abc_ObjRegular( pFanin ) ) == 1 ) Counter++;
            if ( Counter > 2 )
                continue;
        }

        // mark the fanin boundary
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vFaninsCur, pFanin, i ) Abc_ObjRegular( pFanin )->vFanouts.nSize++;
        // label MFFC with current ID
        Abc_NtkIncrementTravId( pNode->pNtk );
        nNodesSaved = Abc_NodeMffcLabelAig( pNode );
        // unmark the fanin boundary
        Vec_PtrForEachEntry( Abc_Obj_t *, p->vFaninsCur, pFanin, i ) Abc_ObjRegular( pFanin )->vFanouts.nSize--;

        // evaluate the cut
        pGraph = Pa_RwrCutEvaluate( p, pNode, pCut, p->vFaninsCur, nNodesSaved, Required, &GainCur, &ScoreCur,
                                    ( ( uPhase & ( 1 << 4 ) ) > 0 ) );

        // check if the cut is better than the current best one
        if ( pGraph != NULL &&
             ( ScoreBest + 1.0e-10 < ScoreCur || ( fabs( ScoreBest - ScoreCur ) <= 1.0e-10 && GainBest < GainCur ) ) )
        {
            // save this form
            GainBest = GainCur;
            ScoreBest = ScoreCur;
            p->pGraph = pGraph;
            p->fCompl = ( ( uPhase & ( 1 << 4 ) ) > 0 );
            Vec_PtrClear( p->vFanins );
            Vec_PtrForEachEntry( Abc_Obj_t *, p->vFaninsCur, pFanin, i ) Vec_PtrPush( p->vFanins, pFanin );
        }
    }
    if ( ScoreBest <= 1.0e-10 )
        return -ABC_INFINITY;

    // copy the leaves
    Vec_PtrForEachEntry( Abc_Obj_t *, p->vFanins, pFanin, i ) Dec_GraphNode( (Dec_Graph_t *)p->pGraph, i )->pFunc =
        pFanin;
    return GainBest;
}

/**Function*************************************************************

  Synopsis    [Evaluates the cut.]

  Description [Returns the subgraph of the cut's class with the highest
  positive placement score (ties: higher node gain, then first), or NULL.]

***********************************************************************/
static Dec_Graph_t * Pa_RwrCutEvaluate( Rwr_Man_t * p, Abc_Obj_t * pRoot, Cut_Cut_t * pCut, Vec_Ptr_t * vFaninsCur,
                                        int nNodesSaved, int LevelMax, int * pGainBest, double * pScoreBest,
                                        int fRootComplement )
{
    Vec_Ptr_t * vSubgraphs;
    Dec_Graph_t * pGraphBest = NULL;
    Dec_Graph_t * pGraphCur;
    Rwr_Node_t *pNode, *pFanin;
    int GainBest, i, k;
    unsigned uTruth;
    double ScoreBest = -ABC_INFINITY;
    // find the matching class of subgraphs
    uTruth = 0xFFFF & *Cut_CutReadTruth( pCut );
    vSubgraphs = Vec_VecEntry( p->vClasses, p->pMap[uTruth] );
    // determine the best subgraph
    GainBest = -1;
    Vec_PtrForEachEntry( Rwr_Node_t *, vSubgraphs, pNode, i )
    {
        double ScoreCur;
        int GainCur;
        // get the current graph
        pGraphCur = (Dec_Graph_t *)pNode->pNext;
        // copy the leaves
        Vec_PtrForEachEntry( Rwr_Node_t *, vFaninsCur, pFanin, k ) Dec_GraphNode( pGraphCur, k )->pFunc = pFanin;
        if ( !Pa_ManEvaluateCandidate( pRoot, pGraphCur, nNodesSaved, LevelMax, fRootComplement, &GainCur, &ScoreCur,
                                       NULL, NULL, NULL ) ||
             ScoreCur <= 1.0e-10 )
            continue;
        if ( ScoreBest + 1.0e-10 < ScoreCur || ( fabs( ScoreBest - ScoreCur ) <= 1.0e-10 && GainBest < GainCur ) ||
             ( fabs( ScoreBest - ScoreCur ) <= 1.0e-10 && GainBest == GainCur && pGraphBest == NULL ) )
        {
            GainBest = GainCur;
            ScoreBest = ScoreCur;
            pGraphBest = pGraphCur;
        }
    }
    if ( pGraphBest == NULL )
        return NULL;
    *pGainBest = GainBest;
    *pScoreBest = ScoreBest;
    return pGraphBest;
}

/**Function*************************************************************

  Synopsis    [Placement-aware rewriting.]

  Description [ABC's rewriting of 4-input cuts with level update and
               without zero-cost replacements. fReassignIds puts the nodes
               into DFS order at the end. Returns 1 on success, 0 if the
               network check fails and -1 if the placement could not be
               maintained.]

***********************************************************************/
int Pa_NtkRewrite( Abc_Ntk_t * pNtk, Pa_Filter_t * pFilter, int fReassignIds )
{
    Cut_Man_t * pManCut;
    Rwr_Man_t * pManRwr;
    Abc_Obj_t * pNode;
    Dec_Graph_t * pGraph;
    int i, nNodes, nGain, fCompl, RetValue = 1;

    assert( Abc_NtkIsStrash( pNtk ) );
    if ( !Pa_ManHasPlacement( pNtk ) )
        return -1;
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    if ( !Pa_ManBeginPass( pNtk ) )
        return -1;
    if ( !Pa_ManPrepareTimingPass( pNtk ) )
    {
        Pa_ManEndPass( pNtk );
        return -1;
    }
    pManRwr = (Rwr_Man_t *)Pa_FrameState( PA_STATE_RWR, Pa_RwrAlloc, Pa_RwrFree );
    if ( pManRwr == NULL )
    {
        Pa_ManEndPass( pNtk );
        return 0;
    }
    Abc_NtkStartReverseLevels( pNtk, 0 );
    pManCut = Pa_NtkStartCutManForRewrite( pNtk );
    pNtk->pManCut = pManCut;

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax( pNtk );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        if ( Abc_NodeIsPersistant( pNode ) || Abc_ObjFanoutNum( pNode ) > 1000 )
            continue;
        if ( pFilter && !pFilter->fVisit( pFilter->pData, pNode ) )
            continue;
        nGain = Pa_RwrNodeRewrite( pManRwr, pManCut, pNode );
        if ( pFilter && pFilter->fDone )
            pFilter->fDone( pFilter->pData, pNode, nGain != -ABC_INFINITY );
        if ( nGain == -ABC_INFINITY )
            continue;
        // a rewriting step is accepted
        pGraph = (Dec_Graph_t *)Rwr_ManReadDecs( pManRwr );
        fCompl = Rwr_ManReadCompl( pManRwr );
        if ( fCompl )
            Dec_GraphComplement( pGraph );
        if ( !Pa_ManCommitCandidate( pNode, pGraph, pManRwr->vFanins, 1, nGain ) )
        {
            // restore the library graph, which is reused by later calls
            if ( fCompl )
                Dec_GraphComplement( pGraph );
            RetValue = -1;
            break;
        }
        if ( fCompl )
            Dec_GraphComplement( pGraph );
    }
    Cut_ManStop( pManCut );
    pNtk->pManCut = NULL;

    if ( !Pa_ManBeginEdit( pNtk ) )
        RetValue = -1;
    if ( fReassignIds )
        Abc_NtkReassignIds( pNtk );
    if ( RetValue >= 0 && !Pa_ManFinishEdit( pNtk ) )
        RetValue = -1;
    if ( RetValue >= 0 && !Pa_ManEndPass( pNtk ) )
        RetValue = -1;
    if ( RetValue < 0 )
    {
        Pa_ManClearPlacement();
        return RetValue;
    }
    Abc_NtkStopReverseLevels( pNtk );
    if ( !Abc_NtkCheck( pNtk ) )
    {
        printf( "Pa_NtkRewrite: The network check has failed.\n" );
        return 0;
    }
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Starts the cut manager for rewriting.]

***********************************************************************/
static Cut_Man_t * Pa_NtkStartCutManForRewrite( Abc_Ntk_t * pNtk )
{
    static ABC_THREAD_LOCAL Cut_Params_t Params;
    Cut_Params_t * pParams = &Params;
    Cut_Man_t * pManCut;
    Abc_Obj_t * pObj;
    int i;
    // start the cut manager
    memset( pParams, 0, sizeof( Cut_Params_t ) );
    pParams->nVarsMax = 4;   // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax = 250; // the max number of cuts kept at a node
    pParams->fTruth = 1;     // compute truth tables
    pParams->fFilter = 1;    // filter dominated cuts
    pParams->fSeq = 0;       // compute sequential cuts
    pParams->fDrop = 0;      // drop cuts on the fly
    pParams->fVerbose = 0;   // the verbosiness flag
    pParams->nIdsMax = Abc_NtkObjNumMax( pNtk );
    pManCut = Cut_ManStart( pParams );
    // set cuts for PIs
    Abc_NtkForEachCi( pNtk, pObj, i ) if ( Abc_ObjFanoutNum( pObj ) > 0 ) Cut_NodeSetTriv( pManCut, pObj->Id );
    return pManCut;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
