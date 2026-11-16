#ifndef ABC__ext_pa__paRewrite_h
#define ABC__ext_pa__paRewrite_h

#include "base/abc/abc.h"
#include "bool/dec/dec.h"

ABC_NAMESPACE_HEADER_START

#ifdef __cplusplus
extern "C" {
#endif

/* Upstream decAbc.c functions are not declared by dec.h. */
int Dec_GraphToNetworkCount( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph,
    int NodeMax, int LevelMax );
Abc_Obj_t * Dec_GraphToNetwork( Abc_Ntk_t * pNtk, Dec_Graph_t * pGraph );

void Pa_ManSetClusterEvaluation( int Enable );
void Pa_ManSetTimingEvaluation( int Enable );
void Pa_ManSetTimingWeight( double Weight );
/* 0: original, 1: node-priority, 2: integrated slack criticality. */
void Pa_ManSetScoreMode( int Mode );
void Pa_ManSetBalancedRefactor( int Enable );
int Pa_ManBalancedRefactorEnabled();
Dec_Graph_t * Pa_ManBalanceGraph( Dec_Graph_t * pGraph );
int Pa_ManPrepareTimingPass( Abc_Ntk_t * pNtk );
/* Resubstitution admits divisors beyond the ID traversal frontier. */
void Pa_ManSetExactTiming( int Enable );
/* 0: bounded proxy; 1: bounded with lazy required times; 2: full incremental. */
void Pa_ManSetTimingEffort( int Mode );
int Pa_NtkResubstitute( Abc_Ntk_t * pNtk, int nCutMax, int nStepsMax,
    int nMinSaved, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose );

/*
 * Evaluates a decomposition graph against the MFFC marked by the current ABC
 * traversal ID.  Internal ANDs are simulated in graph order using ABC's
 * simplification and structural-hash rules; no ABC nodes are created here.
 */
int Pa_ManEvaluateCandidate( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph,
    int nNodesSaved, int LevelMax, int fRootComplement, int * pGain,
    double * pScore,
    double * pHpwlSaved, double * pHpwlAdded, double * pDensityDelta );

/*
 * Rebuilds the selected MFFC mark, recomputes its deterministic placement,
 * instantiates the graph once, and commits placement and AIG edits together.
 */
int Pa_ManCommitCandidate( Abc_Obj_t * pRoot, Dec_Graph_t * pGraph,
    Vec_Ptr_t * vLeaves, int fUpdateLevel, int nGain );

#ifdef __cplusplus
}
#endif

ABC_NAMESPACE_HEADER_END

#endif
