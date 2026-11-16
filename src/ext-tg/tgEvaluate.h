#ifndef ABC__ext_tg__tgEvaluate_h
#define ABC__ext_tg__tgEvaluate_h

#include "base/abc/abc.h"
#include "bool/dec/dec.h"

ABC_NAMESPACE_HEADER_START

#ifdef __cplusplus
extern "C"
{
#endif

    void TgEval_ManConfigure(int mode, int growth, double hpwl, double area);
    void TgEval_ManSetCandidateScoreFloor(double floor);
    int TgEval_ManGrowthEnabled();
    void TgEval_ManSetPhysicalAreaGuard(int enabled);

    void TgEval_ManPrintEffort();

    /* Upstream decAbc.c functions are not declared by dec.h. */
    int Dec_GraphToNetworkCount(Abc_Obj_t *pRoot, Dec_Graph_t *pGraph, int NodeMax, int LevelMax);
    Abc_Obj_t *Dec_GraphToNetwork(Abc_Ntk_t *pNtk, Dec_Graph_t *pGraph);

    void TgEval_ManSetClusterEvaluation(int Enable);
    void TgEval_ManSetTimingEvaluation(int Enable);
    void TgEval_ManSetTimingWeight(double Weight);
    /* 0: original, 1: node-priority, 2: integrated slack criticality. */
    void TgEval_ManSetScoreMode(int Mode);
    void TgEval_ManSetBalancedRefactor(int Enable);
    int TgEval_ManBalancedRefactorEnabled();
    Dec_Graph_t *TgEval_ManBalanceGraph(Dec_Graph_t *pGraph);
    int TgEval_ManPrepareTimingPass(Abc_Ntk_t *pNtk);
    /* Resubstitution admits divisors beyond the ID traversal frontier. */
    void TgEval_ManSetExactTiming(int Enable);
    /* 0: bounded proxy; 1: bounded with lazy required times; 2: full incremental. */
    void TgEval_ManSetTimingEffort(int Mode);
    int TgEval_NtkResubstitute(Abc_Ntk_t *pNtk, int nCutMax, int nStepsMax, int nMinSaved,
                               int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose);

    /*
     * Evaluates a decomposition graph against the MFFC marked by the current ABC
     * traversal ID.  Internal ANDs are simulated in graph order using ABC's
     * simplification and structural-hash rules; no ABC nodes are created here.
     */
    int TgEval_ManEvaluateCandidate(Abc_Obj_t *pRoot, Dec_Graph_t *pGraph, int nNodesSaved,
                                    int LevelMax, int fRootComplement, int *pGain, double *pScore,
                                    double *pHpwlSaved, double *pHpwlAdded, double *pDensityDelta);

    /*
     * Rebuilds the selected MFFC mark, recomputes its deterministic placement,
     * instantiates the graph once, and commits placement and AIG edits together.
     */
    int TgEval_ManCommitCandidate(Abc_Obj_t *pRoot, Dec_Graph_t *pGraph, Vec_Ptr_t *vLeaves,
                                  int fUpdateLevel, int nGain);

#ifdef __cplusplus
}
#endif

ABC_NAMESPACE_HEADER_END

#endif
