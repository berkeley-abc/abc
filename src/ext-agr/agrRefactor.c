#include "agrLog.h"
#include "agrOperators.h"
/**CFile****************************************************************

  FileName    [agrRefactor.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Placement-aware copy of ABC's refactoring pass.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRefactor.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "agrVisit.h"
#include "base/abc/abc.h"
#include "bool/dec/dec.h"
#include "bool/kit/kit.h"

#include "agrEvaluate.h"
#include <math.h>

#include "agrPlace.h"

ABC_NAMESPACE_IMPL_START;

static const unsigned char *coRfMask = 0;
static int coRfLimit = 0;
void Agr_RfSetMask(const unsigned char *mask, int limit)
{
    coRfMask = mask;
    coRfLimit = limit;
}

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Per-command, direct-mapped memoization of the pure truth-to-graph step.
// Keys contain the complete ordered truth table and variable count. At most
// 1024 entries of 16 KiB each; a collision/oversize entry only causes a miss.
#define ABC_REF_CACHE_SIZE 1024
#define ABC_REF_CACHE_ENTRY_BYTES 16384
typedef struct Abc_RefCacheEntry_t_
{
    word Hash;
    int nVars;
    unsigned *pTruth;
    Dec_Graph_t *pGraph;
} Abc_RefCacheEntry_t;

typedef struct Abc_ManRef_t_ Abc_ManRef_t;
struct Abc_ManRef_t_
{
    // user specified parameters
    int nNodeSizeMax; // the limit on the size of the supernode
    int nConeSizeMax; // the limit on the size of the containing cone
    int fVerbose;     // the verbosity flag
    // internal data structures
    Vec_Ptr_t *vVars;    // truth tables
    Vec_Ptr_t *vFuncs;   // functions
    Vec_Int_t *vMemory;  // memory
    Vec_Str_t *vCube;    // temporary
    Vec_Int_t *vForm;    // temporary
    Vec_Ptr_t *vVisited; // temporary
    Vec_Ptr_t *vLeaves;  // temporary
    Abc_RefCacheEntry_t *pFactorCache;
#ifdef ABC_AGR_ENABLE_AUDIT
    unsigned nFactorHitsAudited;
#endif
    // node statistics
    int nLastGain;
    int nNodesConsidered;
    int nNodesRefactored;
    int nNodesGained;
    int nNodesBeg;
    int nNodesEnd;
    // runtime statistics
    abctime timeCut;
    abctime timeTru;
    abctime timeDcs;
    abctime timeSop;
    abctime timeFact;
    abctime timeEval;
    abctime timeRes;
    abctime timeNtk;
    abctime timeTotal;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns function of the cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
word *AgrEval_NodeConeTruth(Vec_Ptr_t *vVars, Vec_Ptr_t *vFuncs, int nWordsMax, Abc_Obj_t *pRoot,
                           Vec_Ptr_t *vLeaves, Vec_Ptr_t *vVisited)
{
    Abc_Obj_t *pNode;
    word *pTruth0, *pTruth1, *pTruth = NULL;
    int i, k, nWords = Abc_Truth6WordNum(Vec_PtrSize(vLeaves));
    // get nodes in the cut without fanins in the DFS order
    Abc_NodeConeCollect(&pRoot, 1, vLeaves, vVisited, 0);
    // set elementary functions
    Vec_PtrForEachEntry(Abc_Obj_t *, vLeaves, pNode, i) pNode->pCopy =
        (Abc_Obj_t *)Vec_PtrEntry(vVars, i);
    // prepare functions
    for (i = Vec_PtrSize(vFuncs); i < Vec_PtrSize(vVisited); i++)
        Vec_PtrPush(vFuncs, ABC_ALLOC(word, nWordsMax));
    // compute functions for the collected nodes
    Vec_PtrForEachEntry(Abc_Obj_t *, vVisited, pNode, i)
    {
        assert(!Abc_ObjIsPi(pNode));
        pTruth0 = (word *)Abc_ObjFanin0(pNode)->pCopy;
        pTruth1 = (word *)Abc_ObjFanin1(pNode)->pCopy;
        pTruth = (word *)Vec_PtrEntry(vFuncs, i);
        if (Abc_ObjFaninC0(pNode))
        {
            if (Abc_ObjFaninC1(pNode))
                for (k = 0; k < nWords; k++)
                    pTruth[k] = ~pTruth0[k] & ~pTruth1[k];
            else
                for (k = 0; k < nWords; k++)
                    pTruth[k] = ~pTruth0[k] & pTruth1[k];
        }
        else
        {
            if (Abc_ObjFaninC1(pNode))
                for (k = 0; k < nWords; k++)
                    pTruth[k] = pTruth0[k] & ~pTruth1[k];
            else
                for (k = 0; k < nWords; k++)
                    pTruth[k] = pTruth0[k] & pTruth1[k];
        }
        pNode->pCopy = (Abc_Obj_t *)pTruth;
    }
    return pTruth;
}
int AgrEval_NodeConeIsConst0(word *pTruth, int nVars)
{
    int k, nWords = Abc_Truth6WordNum(nVars);
    for (k = 0; k < nWords; k++)
        if (pTruth[k])
            return 0;
    return 1;
}
int AgrEval_NodeConeIsConst1(word *pTruth, int nVars)
{
    int k, nWords = Abc_Truth6WordNum(nVars);
    for (k = 0; k < nWords; k++)
        if (~pTruth[k])
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resynthesizes the node using refactoring.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Dec_Graph_t *Abc_RefGraphCopy(const Dec_Graph_t *pGraph)
{
    Dec_Graph_t *pCopy;
    if (pGraph == NULL)
        return NULL;
    pCopy = ABC_ALLOC(Dec_Graph_t, 1);
    *pCopy = *pGraph;
    pCopy->nCap = pGraph->nSize;
    pCopy->pNodes = ABC_ALLOC(Dec_Node_t, pCopy->nCap);
    memcpy(pCopy->pNodes, pGraph->pNodes, sizeof(Dec_Node_t) * pCopy->nSize);
    return pCopy;
}

static Dec_Graph_t *Abc_RefFactorCached(Abc_ManRef_t *p, unsigned *pTruth, int nVars)
{
    int i, nWords = Kit_TruthWordNum(nVars);
    word Hash = (word)nVars + ABC_CONST(1469598103934665603);
    Abc_RefCacheEntry_t *pEntry;
    Dec_Graph_t *pGraph;
    for (i = 0; i < nWords; ++i)
        Hash = (Hash ^ pTruth[i]) * ABC_CONST(1099511628211);
    Hash ^= Hash >> 32;
    pEntry = p->pFactorCache + (Hash & (ABC_REF_CACHE_SIZE - 1));
    if (pEntry->pTruth && pEntry->Hash == Hash && pEntry->nVars == nVars &&
        !memcmp(pEntry->pTruth, pTruth, sizeof(unsigned) * nWords))
    {
#ifdef ABC_AGR_ENABLE_AUDIT
        if (((char *)0))
        {
            Dec_Graph_t *pFresh = (Dec_Graph_t *)Kit_TruthToGraph(pTruth, nVars, p->vMemory);
            int Equal = (pFresh == NULL) == (pEntry->pGraph == NULL);
            if (pFresh && pEntry->pGraph)
            {
                Equal = pFresh->fConst == pEntry->pGraph->fConst &&
                        pFresh->nLeaves == pEntry->pGraph->nLeaves &&
                        pFresh->nSize == pEntry->pGraph->nSize &&
                        Dec_EdgeToInt(pFresh->eRoot) == Dec_EdgeToInt(pEntry->pGraph->eRoot);
                for (i = pFresh->nLeaves; Equal && i < pFresh->nSize; ++i)
                    Equal = Dec_EdgeToInt(pFresh->pNodes[i].eEdge0) ==
                                Dec_EdgeToInt(pEntry->pGraph->pNodes[i].eEdge0) &&
                            Dec_EdgeToInt(pFresh->pNodes[i].eEdge1) ==
                                Dec_EdgeToInt(pEntry->pGraph->pNodes[i].eEdge1);
            }
            if (pFresh)
                Dec_GraphFree(pFresh);
            if (!Equal)
            {
                Abc_Print(-1, "refactor cache error: factored graph mismatch.\n");
                abort();
            }
            ++p->nFactorHitsAudited;
        }
#endif
        return Abc_RefGraphCopy(pEntry->pGraph);
    }
    pGraph = (Dec_Graph_t *)Kit_TruthToGraph(pTruth, nVars, p->vMemory);
    if (sizeof(unsigned) * nWords + (pGraph ? sizeof(Dec_Node_t) * pGraph->nSize : 0) <=
        ABC_REF_CACHE_ENTRY_BYTES)
    {
        ABC_FREE(pEntry->pTruth);
        if (pEntry->pGraph)
            Dec_GraphFree(pEntry->pGraph);
        pEntry->Hash = Hash;
        pEntry->nVars = nVars;
        pEntry->pTruth = ABC_ALLOC(unsigned, nWords);
        memcpy(pEntry->pTruth, pTruth, sizeof(unsigned) * nWords);
        // Store before leaves are bound or materialization writes pFunc.
        pEntry->pGraph = Abc_RefGraphCopy(pGraph);
    }
    return pGraph;
}

Dec_Graph_t *AgrEval_NodeRefactor(Abc_ManRef_t *p, Abc_Obj_t *pNode, Vec_Ptr_t *vFanins,
                                 int nMinSaved, int fUpdateLevel, int fUseZeros, int fUseDcs,
                                 int fVerbose, int fPhysical)
{
    extern int Dec_GraphToNetworkCount(Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int NodeMax,
                                       int LevelMax);
    int fVeryVerbose = 0;
    int nVars = Vec_PtrSize(vFanins);
    int nWordsMax = Abc_Truth6WordNum(p->nNodeSizeMax);
    Dec_Graph_t *pFForm;
    Abc_Obj_t *pFanin;
    word *pTruth;
    abctime clk;
    int i, nNodesSaved, nNodesAdded, Required;
    if (fUseZeros)
        nMinSaved = 0;

    p->nNodesConsidered++;

    Required = fUpdateLevel ? Abc_ObjRequiredLevel(pNode) : ABC_INFINITY;

    // get the function of the cut
    ABC_TIME_START(fVerbose, clk);
    pTruth = AgrEval_NodeConeTruth(p->vVars, p->vFuncs, nWordsMax, pNode, vFanins, p->vVisited);
    ABC_TIME_STOP(fVerbose, p->timeTru, clk);
    if (pTruth == NULL)
        return NULL;

    // always accept the case of constant node
    if (AgrEval_NodeConeIsConst0(pTruth, nVars) || AgrEval_NodeConeIsConst1(pTruth, nVars))
    {
        Dec_Graph_t *pConst = AgrEval_NodeConeIsConst0(pTruth, nVars) ? Dec_GraphCreateConst0()
                                                                     : Dec_GraphCreateConst1();
        if (fPhysical)
        {
            double Score;
            int Gain;
            Vec_PtrForEachEntry(Abc_Obj_t *, vFanins, pFanin, i) Abc_ObjRegular(pFanin)
                ->vFanouts.nSize++;
            Abc_NtkIncrementTravId(pNode->pNtk);
            nNodesSaved = Abc_NodeMffcLabelAig(pNode);
            Vec_PtrForEachEntry(Abc_Obj_t *, vFanins, pFanin, i) Abc_ObjRegular(pFanin)
                ->vFanouts.nSize--;
            if (!AgrEval_ManEvaluateCandidate(pNode, pConst, nNodesSaved, Required, 0, &Gain, &Score,
                                             NULL, NULL, NULL) ||
                (!AgrEval_ManGrowthEnabled() && Gain < nMinSaved) || Score <= 1.0e-10)
            {
                Dec_GraphFree(pConst);
                return NULL;
            }
            p->nLastGain = Gain;
        }
        else
            p->nLastGain = Abc_NodeMffcSize(pNode);
        p->nNodesGained += p->nLastGain;
        p->nNodesRefactored++;
        return pConst;
    }

    // get the factored form
    ABC_TIME_START(fVerbose, clk);
    // Keep ordinary refactor on the original, uncached factoring path.
    pFForm = fPhysical ? Abc_RefFactorCached(p, (unsigned *)pTruth, nVars)
                       : (Dec_Graph_t *)Kit_TruthToGraph((unsigned *)pTruth, nVars, p->vMemory);
    ABC_TIME_STOP(fVerbose, p->timeFact, clk);
    if (pFForm == NULL)
        return NULL;

    // mark the fanin boundary
    // (can mark only essential fanins, belonging to bNodeFunc!)
    Vec_PtrForEachEntry(Abc_Obj_t *, vFanins, pFanin, i) pFanin->vFanouts.nSize++;
    // label MFFC with current traversal ID
    Abc_NtkIncrementTravId(pNode->pNtk);
    nNodesSaved = Abc_NodeMffcLabelAig(pNode);
    // unmark the fanin boundary and set the fanins as leaves in the form
    Vec_PtrForEachEntry(Abc_Obj_t *, vFanins, pFanin, i)
    {
        pFanin->vFanouts.nSize--;
        Dec_GraphNode(pFForm, i)->pFunc = pFanin;
    }

    if (fPhysical)
    {
        double Score;
        int Gain;
        ABC_TIME_START(fVerbose, clk);
        int Valid = AgrEval_ManEvaluateCandidate(pNode, pFForm, nNodesSaved, Required, 0, &Gain,
                                                &Score, NULL, NULL, NULL);
        Valid = Valid && (AgrEval_ManGrowthEnabled() || Gain >= nMinSaved);
        if (AgrEval_ManBalancedRefactorEnabled())
        {
            Dec_Graph_t *pBalanced = AgrEval_ManBalanceGraph(pFForm);
            double BalancedScore;
            int BalancedGain;
            if (pBalanced &&
                AgrEval_ManEvaluateCandidate(pNode, pBalanced, nNodesSaved, Required, 0,
                                            &BalancedGain, &BalancedScore, NULL, NULL, NULL) &&
                (AgrEval_ManGrowthEnabled() || BalancedGain >= nMinSaved) &&
                (!Valid || BalancedScore > Score + 1.0e-10 ||
                 (fabs(BalancedScore - Score) <= 1.0e-10 && BalancedGain > Gain)))
            {
                Dec_GraphFree(pFForm);
                pFForm = pBalanced;
                pBalanced = NULL;
                Valid = 1;
                Gain = BalancedGain;
                Score = BalancedScore;
            }
            if (pBalanced)
                Dec_GraphFree(pBalanced);
        }
        ABC_TIME_STOP(fVerbose, p->timeEval, clk);
        if (!Valid || Score <= 1.0e-10)
        {
            Dec_GraphFree(pFForm);
            return NULL;
        }
        nNodesAdded = nNodesSaved - Gain;
    }
    else
    {
        // Default ABC flow retains its original count/level filter.
        ABC_TIME_START(fVerbose, clk);
        nNodesAdded = Dec_GraphToNetworkCount(pNode, pFForm, nNodesSaved, Required);
        ABC_TIME_STOP(fVerbose, p->timeEval, clk);
        if (nNodesAdded == -1 || nNodesSaved - nNodesAdded < nMinSaved)
        {
            Dec_GraphFree(pFForm);
            return NULL;
        }
    }

    // compute the total gain in the number of nodes
    p->nLastGain = nNodesSaved - nNodesAdded;
    p->nNodesGained += p->nLastGain;
    p->nNodesRefactored++;

    // report the progress
    if (fVeryVerbose)
    {
        printf("Node %6s : ", Abc_ObjName(pNode));
        printf("Cone = %2d. ", vFanins->nSize);
        printf("FF = %2d. ", 1 + Dec_GraphNodeNum(pFForm));
        printf("MFFC = %2d. ", nNodesSaved);
        printf("Add = %2d. ", nNodesAdded);
        printf("GAIN = %2d. ", p->nLastGain);
        printf("\n");
    }
    return pFForm;
}

/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManRef_t *AgrEval_NtkManRefStart(int nNodeSizeMax, int nConeSizeMax, int fUseDcs, int fVerbose)
{
    Abc_ManRef_t *p;
    p = ABC_ALLOC(Abc_ManRef_t, 1);
    memset(p, 0, sizeof(Abc_ManRef_t));
    p->vCube = Vec_StrAlloc(100);
    p->vVisited = Vec_PtrAlloc(100);
    p->nNodeSizeMax = nNodeSizeMax;
    p->nConeSizeMax = nConeSizeMax;
    p->fVerbose = fVerbose;
    p->vVars = Vec_PtrAllocTruthTables(Abc_MaxInt(nNodeSizeMax, 6));
    p->vFuncs = Vec_PtrAlloc(100);
    p->vMemory = Vec_IntAlloc(1 << 16);
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void AgrEval_NtkManRefStop(Abc_ManRef_t *p)
{
    int i;
#ifdef ABC_AGR_ENABLE_AUDIT
    if (p->nFactorHitsAudited)
        AGR_VERBOSE("refactor cache audit: %u hits matched fresh factored graphs.\n",
                   p->nFactorHitsAudited);
#endif
    if (p->pFactorCache)
    {
        for (i = 0; i < ABC_REF_CACHE_SIZE; ++i)
        {
            ABC_FREE(p->pFactorCache[i].pTruth);
            if (p->pFactorCache[i].pGraph)
                Dec_GraphFree(p->pFactorCache[i].pGraph);
        }
        ABC_FREE(p->pFactorCache);
    }
    Vec_PtrFreeFree(p->vFuncs);
    Vec_PtrFree(p->vVars);
    Vec_IntFree(p->vMemory);
    Vec_PtrFree(p->vVisited);
    Vec_StrFree(p->vCube);
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void AgrEval_NtkManRefPrintStats(Abc_ManRef_t *p)
{
    printf("Refactoring statistics:\n");
    printf("Nodes considered  = %8d.\n", p->nNodesConsidered);
    printf("Nodes refactored  = %8d.\n", p->nNodesRefactored);
    printf("Gain              = %8d. (%6.2f %%).\n", p->nNodesBeg - p->nNodesEnd,
           100.0 * (p->nNodesBeg - p->nNodesEnd) / p->nNodesBeg);
    ABC_PRT("Cuts       ", p->timeCut);
    ABC_PRT("Resynthesis", p->timeRes);
    ABC_PRT("    BDD    ", p->timeTru);
    ABC_PRT("    DCs    ", p->timeDcs);
    ABC_PRT("    SOP    ", p->timeSop);
    ABC_PRT("    FF     ", p->timeFact);
    ABC_PRT("    Eval   ", p->timeEval);
    ABC_PRT("AIG update ", p->timeNtk);
    ABC_PRT("TOTAL      ", p->timeTotal);
}

/**Function*************************************************************

  Synopsis    [Performs incremental resynthesis of the AIG.]

  Description [Starting from each node, computes a reconvergence-driven cut,
  derives BDD of the cut function, constructs ISOP, factors the ISOP,
  and replaces the current implementation of the MFFC of the node by the
  new factored form, if the number of AIG nodes is reduced and the total
  number of levels of the AIG network is not increated. Returns the
  number of AIG nodes saved.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_NtkRefactorInternal(Abc_Ntk_t *pNtk, int nNodeSizeMax, int nMinSaved,
                                   int nConeSizeMax, int fUpdateLevel, int fUseZeros, int fUseDcs,
                                   int fVerbose, int fPhysical)
{
    extern int Dec_GraphUpdateNetwork(Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int fUpdateLevel,
                                      int nGain);
    ProgressBar *pProgress;
    Abc_ManRef_t *pManRef;
    Abc_ManCut_t *pManCut;
    Dec_Graph_t *pFForm;
    Vec_Ptr_t *vFanins;
    Abc_Obj_t *pNode;
    abctime clk, clkStart;
    int i, nNodes, RetValue = 1;

    ABC_TIME_START(fVerbose, clkStart);
    assert(Abc_NtkIsStrash(pNtk));
    if (fPhysical && !Agr_ManHasPlacement(pNtk))
    {
        Abc_Print(-1, "pa_rf: run pa_place on the current AIG first.\n");
        return -1;
    }
    // cleanup the AIG
    Abc_AigCleanup((Abc_Aig_t *)pNtk->pManFunc);
    if (fPhysical && !Agr_ManBeginPass(pNtk))
    {
        Abc_Print(-1, "pa_rf: AIG cleanup changed the placed graph; rerun pa_place.\n");
        return -1;
    }
    if (fPhysical && !AgrEval_ManPrepareTimingPass(pNtk))
    {
        Abc_Print(-1, "pa_rf -t: could not initialize timing from placement.\n");
        Agr_ManEndPass(pNtk);
        return -1;
    }
    // start the managers
    pManCut = Abc_NtkManCutStart(nNodeSizeMax, nConeSizeMax, 2, 1000);
    pManRef = AgrEval_NtkManRefStart(nNodeSizeMax, nConeSizeMax, fUseDcs, fVerbose);
    // The memoization speedup belongs only to placement-aware refactor.
    if (fPhysical)
        pManRef->pFactorCache = ABC_CALLOC(Abc_RefCacheEntry_t, ABC_REF_CACHE_SIZE);
    pManRef->vLeaves = Abc_NtkManCutReadCutLarge(pManCut);
    // compute the reverse levels if level update is requested
    if (fUpdateLevel)
        Abc_NtkStartReverseLevels(pNtk, 0);

    // resynthesize each node once
    int coVisitCount = 0;
    const int *coVisitOrder = Agr_ReadVisitOrder(&coVisitCount);

    pManRef->nNodesBeg = Abc_NtkNodeNum(pNtk);
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart(stdout, nNodes);
    Agr_NtkForEachVisit(pNtk, pNode, i, coVisitOrder, coVisitCount)
    {
        Extra_ProgressBarUpdate(pProgress, i, NULL);
        if (coRfMask && (pNode->Id >= coRfLimit || !coRfMask[pNode->Id]))
            continue;
        // skip the constant node
        //        if ( Abc_NodeIsConst(pNode) )
        //            continue;
        // skip persistant nodes
        if (Abc_NodeIsPersistant(pNode))
            continue;
        // skip the nodes with many fanouts
        if (Abc_ObjFanoutNum(pNode) > 1000)
            continue;
        // stop if all nodes have been tried once
        if (i >= nNodes)
            break;

        // compute a reconvergence-driven cut
        ABC_TIME_START(fVerbose, clk);
        vFanins = Abc_NodeFindCut(pManCut, pNode, fUseDcs);
        ABC_TIME_STOP(fVerbose, pManRef->timeCut, clk);
        // evaluate this cut
        ABC_TIME_START(fVerbose, clk);
        pFForm = AgrEval_NodeRefactor(pManRef, pNode, vFanins, nMinSaved, fUpdateLevel, fUseZeros,
                                     fUseDcs, fVerbose, fPhysical);
        ABC_TIME_STOP(fVerbose, pManRef->timeRes, clk);
        if (pFForm == NULL)
            continue;
        // acceptable replacement found, update the graph
        ABC_TIME_START(fVerbose, clk);
        if (!(fPhysical ? AgrEval_ManCommitCandidate(pNode, pFForm, vFanins, fUpdateLevel,
                                                    pManRef->nLastGain)
                        : Dec_GraphUpdateNetwork(pNode, pFForm, fUpdateLevel, pManRef->nLastGain)))
        {
            Dec_GraphFree(pFForm);
            RetValue = -1;
            break;
        }
        ABC_TIME_STOP(fVerbose, pManRef->timeNtk, clk);
        Dec_GraphFree(pFForm);
    }
    Extra_ProgressBarStop(pProgress);
    ABC_TIME_STOP(fVerbose, pManRef->timeTotal, clkStart);
    pManRef->nNodesEnd = Abc_NtkNodeNum(pNtk);

    // print statistics of the manager
    if (fVerbose)
        AgrEval_NtkManRefPrintStats(pManRef);
    // delete the managers
    Abc_NtkManCutStop(pManCut);
    AgrEval_NtkManRefStop(pManRef);
    // put the nodes into the DFS order and reassign their IDs
    if (fPhysical && !Agr_ManBeginEdit(pNtk))
        RetValue = -1;
    if (!Agr_InFlight())
        Abc_NtkReassignIds(pNtk);
    if (fPhysical && RetValue >= 0 && !Agr_ManFinishEdit(pNtk))
        RetValue = -1;
    if (fPhysical && RetValue >= 0 && !Agr_ManEndPass(pNtk))
        RetValue = -1;
    if (fPhysical && RetValue < 0)
        Agr_ManClearPlacement();
    //    Abc_AigCheckFaninOrder( pNtk->pManFunc );
    if (RetValue != -1)
    {
        // fix the levels
        if (fUpdateLevel)
            Abc_NtkStopReverseLevels(pNtk);
        else
            Abc_NtkLevel(pNtk);
        // check
        if (!Abc_NtkCheck(pNtk))
        {
            printf("AgrEval_NtkRefactor: The network check has failed.\n");
            return 0;
        }
    }
    return RetValue;
}

int AgrEval_NtkRefactorPhysical(Abc_Ntk_t *pNtk, int nNodeSizeMax, int nMinSaved, int nConeSizeMax,
                               int fUpdateLevel, int fUseZeros, int fUseDcs, int fVerbose)
{
    return Abc_NtkRefactorInternal(pNtk, nNodeSizeMax, nMinSaved, nConeSizeMax, fUpdateLevel,
                                   fUseZeros, fUseDcs, fVerbose, 1);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
