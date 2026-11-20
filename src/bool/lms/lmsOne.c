/**CFile****************************************************************

  FileName    [lmsOne.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS iterative critical-path optimization.]

  Synopsis    [Cover the zero-slack graph with area-weighted resubstitutions.]

  Description [Find earlier implementations of zero-slack edges using
  local resubstitution and the receiving AND's observability don't-cares.
  Whole-node replacements remain available as shared alternatives. An
  area-weighted edge/vertex cut intersects every longest path. Simultaneous
  changes to both inputs of an AND must pass a compatibility proof; bounded
  branching excludes incompatible pairs. Rebuild the batch, check its depth,
  refine actual area, and run level-preserving resubstitution. The cut is
  optimal for its nonnegative local costs before compatibility constraints;
  bounded search and interacting sharing make total area heuristic. A search
  miss is not a depth lower bound. Flop terminals are independent PIs/POs.
  The LMS2 driver repeats this one-level search to saturation or a stopping
  bound, retaining the preceding graph if a recovered pass exceeds the
  per-pass node-growth budget. Graph-independent recipes and library data survive
  between iterations. Native XOR mode counts every AND/XOR as one gate.]

  Author      [Alan Mishchenko]

***********************************************************************/

#include "lmsInt.h"
#include "base/abc/abc.h"
#include "aig/gia/gia.h"
#include "misc/util/utilTruth.h"
#include "misc/mem/mem.h"
#include "misc/extra/extraUtilFlow.h"
#include <float.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

enum { LMO_LEAVES = 16, LMO_EARLY = 16, LMO_DIVS = 64, LMO_WINDOW = 256 };
enum { LMO_TIME_OTHER, LMO_TIME_BANK, LMO_TIME_WINDOW, LMO_TIME_RESUB,
    LMO_TIME_LIBRARY, LMO_TIME_REPLAY, LMO_TIME_COST, LMO_TIME_CUT,
    LMO_TIME_BUILD, LMO_TIME_RECOVER, LMO_TIME_MATCH,
    LMO_TIME_INSTANTIATE, LMO_TIME_NUM };
typedef struct Lmo_Cut_t_ { int n, Leaves[LMO_LEAVES]; } Lmo_Cut_t;
typedef struct Lmo_Best_t_ { int n, * Lits, * Costs; } Lmo_Best_t;
typedef struct Lmo_CutMemo_t_
{
    struct Lmo_CutMemo_t_ * pNext;
    word Resub, Library[2];
    int Root, nLeaves;
    unsigned char fBaseDone, fFailed;
    int Leaves[1]; // Variable-sized, aligned entries in the per-pass arena.
} Lmo_CutMemo_t;
typedef struct Lmo_Memo_t_
{
    word Hash;
    size_t Bytes;
    int nDivs, nWords, Nodes, Divs, Choices, fXor, Pass;
    word Data[1];
} Lmo_Memo_t;
typedef struct Lmo_Cache_t_
{
    Lmo_Memo_t ** pBins;
    int nBins, Clock, fLibrary, Pass;
    abctime Deadline;
    size_t Bytes, Limit;
    word Hits, CrossHits, Misses, Evictions;
    Vec_Int_t * vPrograms, * vOffsets;
} Lmo_Cache_t;
typedef struct Lmo_Man_t_
{
    Gia_Man_t * pGia, * pPool, * pSatGia;
    Lmo_Cache_t * pCache;
    Lmo_CutMemo_t ** pCutBins;
    Mem_Flex_t * pCutMem;
    int nCutOverflows;
    word * pVersions, Version;
    word * pCandidateBins, * pMergedVersions, * pReplayVersion;
    int nCandidateBins, nCandidateSkips, nReplaySkips, fSkipTarget;
    int fInMerged;
    unsigned nTimeChecks;
    word Builds[3], DuplicateOrigins[2];
    int nCutBins, nCutMemos, nWindowSkips, nResubSkips, nLibrarySkips;
    int * pLevels, * pReverse, * pSeen, * pSelected, * pNeeded, * pTruthIds;
    unsigned char * pFocus, * pBankCone;
    word * pTruths, * pValues, * pOff, * pOn;
    void ** pDivs;
    int * pLits, * pTimes;
    const word * pLibDelays;
    const unsigned char * pLibAreas;
    Lmo_Best_t * pBest, * pEdgeBest;
    int * pEdgeSelected, * pEdgeIndex;
    int * pFastLits, * pFastCosts, * pEarlyLits, * pEarlyCosts;
    unsigned char * pPairs;
    Cbs_Man_t * pSolver;
    Vec_Int_t * vPoolLevels, * vRefs, * vStack, * vWindow, * vCostUndo;
    Vec_Int_t * vPrograms, * vOffsets, * vSatMap, * vMerged;
    Vec_Wrd_t * vMergedTruths;
    Vec_Wec_t * vFanouts, * vRecipes;
    int Depth, InputDepth, Cuts, Nodes, Stamp, Root, fUncovered, fMapped, fOnePerProfile, fCompose, fTargetOnly, MappedRoot, Leaves[6];
    int CutSize, Divs, Choices, Alternatives, Window, nWords, nWordsMax, fXor, fMergedDirect, fFullHelpers;
    int DivIds[2][LMO_DIVS], nDivIds[2], DivLits[LMO_WINDOW], DivTimes[LMO_WINDOW];
    word DivHashes[LMO_WINDOW], ProblemHashes[LMO_DIVS+2];
    unsigned DivStamp, DivStamps[1024];
    int DivBins[1024];
    unsigned char DivSeen[LMO_WINDOW];
    int nCritical, nEdges, nRoots, nCuts, nResub, nLibrary, nCandidates;
    int nEdgeCandidates, nEdgeRoots, nCutTrials, nPairChecks, nPairRejects, nInfinitePaths;
    int nUncovered, nUncoveredCone;
    int CostRoot, CostLit, CostRemoved, CostAdded;
    word CostBounded, CostAborts;
    word CutCost;
    int CutCounts[LMO_LEAVES+1];
    // Exclusive times: nested work is charged to its own category. Enable
    // only with -v, so ordinary runs pay no per-candidate clock overhead.
    int fProfile, TimeActive;
    abctime TimeLast, Times[LMO_TIME_NUM];
} Lmo_Man_t;

/**Function*************************************************************

  Synopsis    [Checks the optional deadline shared by the LMS search passes.]

***********************************************************************/
static inline int Lmo_Expired( Lmo_Man_t * p )
{
    return p->pCache->Deadline && Abc_ClockHr() >= p->pCache->Deadline;
}

/**Function*************************************************************

  Synopsis    [Charge elapsed profiling time to the previous category.]

***********************************************************************/
static int Lmo_TimeSwitch( Lmo_Man_t * p, int Category )
{
    int Previous = p->TimeActive;
    if ( p->fProfile )
    {
        abctime Now = Abc_Clock();
        p->Times[Previous] += Now-p->TimeLast;
        p->TimeLast = Now; p->TimeActive = Category;
    }
    return Previous;
}

extern void Abc_ResubPrepareManager( int nWords );
extern int Abc_ResubComputeFunctions( void **, int, int, int, int, int, int,
    int, int, int, int, Vec_Wec_t *, int *, abctime *, abctime *, abctime *, int *, int * );

/**Function*************************************************************

  Synopsis    [Hash the active words of a divisor truth table.]

***********************************************************************/
static word Lmo_TruthHash( const word * pTruth, int nWords )
{
    word Hash = 0;
    int w;
    for ( w = 0; w < nWords; ++w ) Hash = (Hash ^ pTruth[w])*ABC_CONST(1099511628211);
    return Hash;
}

// Recipes depend on the complete ordered truth problem and search budgets,
// not graph IDs, arrivals, reference counts, or previous replacements. Cache
// successes and misses alike; always recheck timing, truth, and actual cost.
// A hash selects a slot, but full key comparison is required for every hit.
/**Function*************************************************************

  Synopsis    [Reuse or compute resubstitution recipes for the current problem.]

***********************************************************************/
static void Lmo_ResubRecipes( Lmo_Man_t * p, int nDivs )
{
    Lmo_Cache_t * c = p->pCache;
    Lmo_Memo_t * e;
    Vec_Int_t * v;
    word Hash = ABC_CONST(1469598103934665603), * pData;
    int i, w, Slot = 0, Same = 0, nCode = 1, * pCode;
    size_t Bytes;
    assert(p->nWordsMax >= p->nWords);
    if ( c->nBins )
    {
        Hash ^= (word)nDivs + ((word)p->nWords<<8) + ((word)p->Nodes<<24) + ((word)p->fXor<<40);
        for ( i = 0; i < nDivs; ++i )
            Hash = (Hash ^ p->ProblemHashes[i]) * ABC_CONST(1099511628211);
        Hash ^= Hash >> 32;
        Slot = (int)(Hash & (c->nBins-1));
        e = c->pBins[Slot];
        Same = e && e->Hash == Hash && e->nDivs == nDivs && e->nWords == p->nWords &&
            e->Nodes == p->Nodes && e->Divs == p->Divs && e->Choices == p->Choices && e->fXor == p->fXor;
        for ( i = 0; Same && i < nDivs; ++i )
            Same = !memcmp(e->Data+(size_t)i*p->nWords, p->pDivs[i], sizeof(word)*p->nWords);
        if ( Same )
        {
            ++c->Hits;
            c->CrossHits += e->Pass != c->Pass;
            Vec_WecClear(p->vRecipes);
            pCode = (int *)(e->Data+(size_t)nDivs*p->nWords);
            nCode = *pCode++;
            for ( i = 0; i < nCode; ++i )
            {
                int Size = *pCode++;
                v = Vec_WecPushLevel(p->vRecipes);
                for ( w = 0; w < Size; ++w ) Vec_IntPush(v, *pCode++);
            }
            return;
        }
        ++c->Misses;
    }
    // The manager owns maximum-width scratch; solve only this cut's actual
    // truth problem. Allocation capacity is not part of the recipe key.
    Abc_ResubComputeFunctions(p->pDivs, nDivs, p->nWords, p->Nodes, p->Divs, p->Choices, 0,
        1, p->fXor, 0, 0, p->vRecipes, NULL, NULL, NULL, NULL, NULL, NULL);
    if ( !c->nBins ) return;
    Vec_WecForEachLevel(p->vRecipes, v, i) nCode += 1+Vec_IntSize(v);
    Bytes = sizeof(Lmo_Memo_t)-sizeof(word)+(size_t)nDivs*p->nWords*sizeof(word)+(size_t)nCode*sizeof(int);
    if ( Bytes > c->Limit ) return;
    e = (Lmo_Memo_t *)ABC_ALLOC(char, Bytes);
    if ( !e ) return; // Optional memoization must not affect synthesis.
    e->Hash = Hash; e->Bytes = Bytes; e->nDivs = nDivs; e->nWords = p->nWords;
    e->Nodes = p->Nodes; e->Divs = p->Divs; e->Choices = p->Choices; e->fXor = p->fXor;
    e->Pass = c->Pass;
    pData = e->Data;
    for ( i = 0; i < nDivs; ++i, pData += p->nWords ) memcpy(pData, p->pDivs[i], sizeof(word)*p->nWords);
    pCode = (int *)pData;
    *pCode++ = Vec_WecSize(p->vRecipes);
    Vec_WecForEachLevel(p->vRecipes, v, i)
    {
        *pCode++ = Vec_IntSize(v);
        Vec_IntForEachEntry(v, w, nCode) *pCode++ = w;
    }
    if ( c->pBins[Slot] )
    { c->Bytes -= c->pBins[Slot]->Bytes; ABC_FREE(c->pBins[Slot]); ++c->Evictions; }
    while ( c->Bytes+Bytes > c->Limit )
    {
        i = c->Clock; c->Clock = (c->Clock+1) & (c->nBins-1);
        if ( !c->pBins[i] ) continue;
        c->Bytes -= c->pBins[i]->Bytes; ABC_FREE(c->pBins[i]); ++c->Evictions;
    }
    c->pBins[Slot] = e; c->Bytes += Bytes;
}

static const word s_LmoVars[6] = {
    ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
    ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
    ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000)
};

// Only nodes in the current bounded window need truth-table storage. This
// keeps large-cut memory proportional to the window rather than the AIG.
/**Function*************************************************************

  Synopsis    [Return the active truth table of a window node.]

***********************************************************************/
static word * Lmo_Truth( Lmo_Man_t * p, int Id )
{
    return p->pTruths + (size_t)p->nWords*p->pTruthIds[Id];
}

/**Function*************************************************************

  Synopsis    [Compute an AND truth table with complemented fanins.]

***********************************************************************/
static void Lmo_TruthAnd( word * pOut, word * pA, word * pB, int nWords, int cA, int cB )
{
    int w;
    for ( w = 0; w < nWords; ++w ) pOut[w] = (pA[w] ^ -(word)cA) & (pB[w] ^ -(word)cB);
}

/**Function*************************************************************

  Synopsis    [Compute an AND or XOR truth table with complemented fanins.]

***********************************************************************/
static void Lmo_TruthGate( word * pOut, word * pA, word * pB, int nWords, int cA, int cB, int fXor )
{
    int w;
    if ( !fXor ) { Lmo_TruthAnd(pOut, pA, pB, nWords, cA, cB); return; }
    for ( w = 0; w < nWords; ++w ) pOut[w] = pA[w] ^ pB[w] ^ -(word)(cA^cB);
}

/**Function*************************************************************

  Synopsis    [Find longest paths with one forward and one reverse traversal.]

  Description [All CIs arrive at zero. An edge u->v is critical exactly when
  level(u)+1+reverse(v) equals the maximum CO-driver level. Dangling logic
  has reverse level -1 and cannot enter the critical graph.]

***********************************************************************/
static void Lmo_Timing( Lmo_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, a, b, n = Gia_ManObjNum(p->pGia);
    p->pLevels = ABC_CALLOC(int, n);
    p->pReverse = ABC_ALLOC(int, n);
    for ( i = 0; i < n; ++i ) p->pReverse[i] = -1;
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        p->pLevels[i] = 1 + Abc_MaxInt(p->pLevels[Gia_ObjFaninId0p(p->pGia, pObj)],
                                      p->pLevels[Gia_ObjFaninId1p(p->pGia, pObj)]);
        p->InputDepth = Abc_MaxInt(p->InputDepth, p->pLevels[i]);
    }
    Gia_ManForEachCo(p->pGia, pObj, i)
    {
        a = Gia_ObjFaninId0p(p->pGia, pObj);
        p->Depth = Abc_MaxInt(p->Depth, p->pLevels[a]);
        p->pReverse[a] = 0;
    }
    for ( i = n-1; i > 0; --i )
    {
        pObj = Gia_ManObj(p->pGia, i);
        if ( !Gia_ObjIsAnd(pObj) || p->pReverse[i] < 0 ) continue;
        a = Gia_ObjFaninId0p(p->pGia, pObj);
        b = Gia_ObjFaninId1p(p->pGia, pObj);
        p->pReverse[a] = Abc_MaxInt(p->pReverse[a], p->pReverse[i]+1);
        p->pReverse[b] = Abc_MaxInt(p->pReverse[b], p->pReverse[i]+1);
    }
    Gia_ManForEachAnd(p->pGia, pObj, i)
        if ( p->pReverse[i] >= 0 && p->pLevels[i]+p->pReverse[i] == p->Depth )
        {
            ++p->nCritical;
            p->nEdges += p->pLevels[Gia_ObjFaninId0p(p->pGia, pObj)]+1 == p->pLevels[i];
            p->nEdges += p->pLevels[Gia_ObjFaninId1p(p->pGia, pObj)]+1 == p->pLevels[i];
        }
}

/**Function*************************************************************

  Synopsis    [Test whether a node lies on a current longest path.]

***********************************************************************/
static int Lmo_IsCritical( Lmo_Man_t * p, int Id )
{
    return p->pReverse[Id] >= 0 && p->pLevels[Id]+p->pReverse[Id] == p->Depth;
}

/**Function*************************************************************

  Synopsis    [Hash a candidate gate and maintain only its new level.]

  Description [The input graph is immutable during candidate generation.
  No speculative change propagates timing through its fanout cone.]

***********************************************************************/
static int Lmo_Gate( Lmo_Man_t * p, int a, int b, int fXor )
{
    int Lit = fXor ? Gia_ManHashXorReal(p->pPool, a, b) : Gia_ManHashAnd(p->pPool, a, b);
    int Id = Abc_Lit2Var(Lit);
    if ( Id >= Vec_IntSize(p->vPoolLevels) )
    {
        int Level = 1 + Abc_MaxInt(Vec_IntEntry(p->vPoolLevels, Abc_Lit2Var(a)),
                                   Vec_IntEntry(p->vPoolLevels, Abc_Lit2Var(b)));
        Vec_IntFillExtra(p->vPoolLevels, Gia_ManObjNum(p->pPool), 0);
        Vec_IntFillExtra(p->vRefs, Gia_ManObjNum(p->pPool), 0);
        Vec_IntWriteEntry(p->vPoolLevels, Id, Level);
    }
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Reference or dereference a cone without recursion.]

  Description [Force processes the old root even though its fanouts still
  reference it. Candidate gates can share both original and new interiors.]

***********************************************************************/
static int Lmo_Reference( Lmo_Man_t * p, int Id, int Add, int Force )
{
    int Count = 0, k, Fan, * pRefs = Vec_IntArray(p->vRefs);
    Gia_Obj_t * pObj;
    if ( !Force && (Add ? pRefs[Id]++ != 0 : --pRefs[Id] != 0) ) return 0;
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack, Id);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntPop(p->vStack);
        pObj = Gia_ManObj(p->pPool, Id);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        ++Count;
        for ( k = 0; k < 2; ++k )
        {
            Fan = k ? Gia_ObjFaninId1p(p->pPool, pObj) : Gia_ObjFaninId0p(p->pPool, pObj);
            assert(Add || pRefs[Fan] > 0);
            if ( Add ? pRefs[Fan]++ == 0 : --pRefs[Fan] == 0 ) Vec_IntPush(p->vStack, Fan);
        }
    }
    return Count;
}

// Bound only the newly referenced gates. The preceding candidate may still
// share gates with this one, so this count is a lower bound on its standalone
// area. On an abort, undo exactly the increments already performed, including
// fanins still on the traversal stack; an ordinary dereference would visit
// unfinished cones and corrupt their references.
/**Function*************************************************************

  Synopsis    [Reference a candidate cone, rolling back when its bound is exceeded.]

***********************************************************************/
static int Lmo_ReferenceLimit( Lmo_Man_t * p, int Root, int Limit )
{
    int Count = 0, Id, k, Fan, * pRefs = Vec_IntArray(p->vRefs);
    Gia_Obj_t * pObj;
    if ( pRefs[Root]++ ) return 0;
    if ( !p->vCostUndo ) p->vCostUndo = Vec_IntAlloc(256);
    Vec_IntClear(p->vCostUndo);
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack, Root);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntPop(p->vStack);
        pObj = Gia_ManObj(p->pPool, Id);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        if ( ++Count > Limit )
        {
            Vec_IntForEachEntry(p->vCostUndo, Id, k)
            {
                pObj = Gia_ManObj(p->pPool, Id);
                --pRefs[Gia_ObjFaninId0p(p->pPool, pObj)];
                --pRefs[Gia_ObjFaninId1p(p->pPool, pObj)];
            }
            --pRefs[Root];
            Vec_IntClear(p->vStack);
            ++p->CostAborts;
            return INT_MAX;
        }
        Vec_IntPush(p->vCostUndo, Id);
        for ( k = 0; k < 2; ++k )
        {
            Fan = k ? Gia_ObjFaninId1p(p->pPool, pObj) : Gia_ObjFaninId0p(p->pPool, pObj);
            if ( pRefs[Fan]++ == 0 ) Vec_IntPush(p->vStack, Fan);
        }
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Retain a candidate in the ordered alternatives for a root.]

***********************************************************************/
static int Lmo_Save( Lmo_Man_t * p, Lmo_Best_t * q, int Lit, int Delta )
{
    int i, j, First = !q->n;
    for ( i = 0; i < q->n; ++i ) if ( q->Lits[i] == Lit ) return 0;
    for ( i = 0; i < q->n; ++i )
        if ( Delta < q->Costs[i] || (Delta == q->Costs[i] && Lit < q->Lits[i]) ) break;
    if ( i == p->Alternatives ) return 0;
    if ( !q->n )
    {
        q->Lits = ABC_ALLOC(int, p->Alternatives);
        q->Costs = ABC_ALLOC(int, p->Alternatives);
    }
    if ( q->n < p->Alternatives ) ++q->n;
    for ( j = q->n-1; j > i; --j )
        q->Lits[j] = q->Lits[j-1], q->Costs[j] = q->Costs[j-1];
    q->Lits[i] = Lit;
    q->Costs[i] = Delta;
    return 1+First;
}

/**Function*************************************************************

  Synopsis    [Restore references after pricing candidates for one root.]

***********************************************************************/
static void Lmo_CostReset( Lmo_Man_t * p )
{
    if ( !p->CostRoot ) return;
    if ( p->CostLit >= 0 ) Lmo_Reference(p, p->CostLit>>1, 0, 0);
    Lmo_Reference(p, p->CostRoot, 1, 1);
    p->CostRoot = 0;
}

/**Function*************************************************************

  Synopsis    [Measure standalone area while retaining shared candidate interiors.]

***********************************************************************/
static int Lmo_Cost( Lmo_Man_t * p, int Root, int Lit, int Limit )
{
    int Result;
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_COST);
    int Added;
    // Keep this root removed and the previous candidate referenced. Add the
    // next candidate before removing the previous one: their shared cones
    // then stay live. The accumulated count is exactly the same standalone
    // area as restoring the input references between every pair of trials.
    if ( p->CostRoot != Root )
    {
        Lmo_CostReset(p);
        p->CostRoot = Root;
        p->CostRemoved = Lmo_Reference(p, Root, 0, 1);
        p->CostAdded = 0;
        p->CostLit = -1;
    }
    if ( Limit == INT_MAX ) Added = Lmo_Reference(p, Lit>>1, 1, 0);
    else
    {
        ++p->CostBounded;
        Added = Lmo_ReferenceLimit(p, Lit>>1, Limit+p->CostRemoved);
        if ( Added == INT_MAX ) { Result = INT_MAX; goto done; }
    }
    p->CostAdded += Added;
    if ( p->CostLit >= 0 ) p->CostAdded -= Lmo_Reference(p, p->CostLit>>1, 0, 0);
    p->CostLit = Lit;
    Result = p->CostAdded-p->CostRemoved;
done:
    Lmo_TimeSwitch(p, TimePrevious);
    return Result;
}

// A candidate must improve at least one retained slot. Leave ties to the
// existing literal-order rules; bounding by the largest eligible slot cost
// is conservative. A new arrival level or a faster candidate is unbounded.
/**Function*************************************************************

  Synopsis    [Find a conservative cost bound from eligible retention slots.]

***********************************************************************/
static int Lmo_CostLimit( Lmo_Man_t * p, int Root, int Lit )
{
    Lmo_Best_t * q = p->pBest+Root;
    int Level = Vec_IntEntry(p->vPoolLevels, Lit>>1);
    int FastLevel = Vec_IntEntry(p->vPoolLevels, p->pFastLits[Root]>>1);
    int Limit;
    if ( q->n < p->Alternatives || Level < FastLevel ) return INT_MAX;
    Limit = q->Costs[q->n-1];
    if ( p->pLevels[Root]-Level <= LMO_EARLY )
    {
        size_t Index = (size_t)Root*LMO_EARLY+p->pLevels[Root]-Level-1;
        if ( p->pEarlyLits[Index] < 0 ) return INT_MAX;
        Limit = Abc_MaxInt(Limit, p->pEarlyCosts[Index]);
    }
    if ( Level == FastLevel ) Limit = Abc_MaxInt(Limit, p->pFastCosts[Root]);
    return Limit;
}

// Meet this pin's deadline without unnecessarily accelerating its whole
// cone. Original signals are free to reuse. Otherwise take the cheapest
// retained implementation that is early enough, with the fastest as backup.
// Keep a cheapest representative for each of the first 16 levels saved as
// well as the area-ranked choices. Otherwise a slightly tighter deadline can
// force an unnecessarily large jump from the cheapest cone to the fastest.
/**Function*************************************************************

  Synopsis    [Choose a retained implementation meeting a fanin deadline.]

***********************************************************************/
static int Lmo_Leaf( Lmo_Man_t * p, int Id, int Required )
{
    Lmo_Best_t * q = p->pBest+Id;
    int k, Best = -1, Cost = INT_MAX;
    int * pLits = p->pEarlyLits+(size_t)Id*LMO_EARLY;
    int * pCosts = p->pEarlyCosts+(size_t)Id*LMO_EARLY;
    if ( p->pLevels[Id] <= Required ) return 2*Id;
    for ( k = 0; k < q->n; ++k )
        if ( Vec_IntEntry(p->vPoolLevels, q->Lits[k]>>1) <= Required )
        { Best = q->Lits[k]; Cost = q->Costs[k]; break; }
    for ( k = 0; k < LMO_EARLY; ++k )
        if ( pLits[k] >= 0 && p->pLevels[Id]-k-1 <= Required &&
             (pCosts[k] < Cost || (pCosts[k] == Cost && (Best < 0 || pLits[k] < Best))) )
        { Best = pLits[k]; Cost = pCosts[k]; }
    if ( Vec_IntEntry(p->vPoolLevels, p->pFastLits[Id]>>1) <= Required &&
         (Best < 0 || p->pFastCosts[Id] < Cost ||
         (p->pFastCosts[Id] == Cost && p->pFastLits[Id] < Best)) ) Best = p->pFastLits[Id];
    return Best;
}

// Standalone cost and timing of a root/literal pair never change within a
// pass. Retained alternatives only improve, so even an evicted or rejected
// candidate cannot become useful on a revisit. Collisions merely evict this
// optional cache entry; full key equality is required to suppress a trial.
/**Function*************************************************************

  Synopsis    [Remember root/literal pairs already submitted for costing.]

***********************************************************************/
static int Lmo_CandidateSeen( Lmo_Man_t * p, int Root, int Lit, int Kind )
{
    word Key = (((word)3*Root+Kind)<<32) | (unsigned)Lit;
    word Hash = (Key ^ (Key>>30))*ABC_CONST(0xbf58476d1ce4e5b9);
    int Slot;
    if ( !p->nCandidateBins ) return 0;
    Hash = (Hash ^ (Hash>>27))*ABC_CONST(0x94d049bb133111eb);
    Slot = (int)((Hash ^ (Hash>>31)) & (p->nCandidateBins-1));
    if ( p->pCandidateBins[Slot] == Key ) { ++p->nCandidateSkips; return 1; }
    p->pCandidateBins[Slot] = Key;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Price and retain a faster whole-node implementation.]

***********************************************************************/
static void Lmo_Consider( Lmo_Man_t * p, int Lit, int fResub )
{
    int Status, Cost, Limit, Level, FastLevel, k, Changed = 0;
    if ( Vec_IntEntry(p->vPoolLevels, Abc_Lit2Var(Lit)) >= p->pLevels[p->Root] ) return;
    if ( p->pFastLits[p->Root] == Lit ) return;
    for ( k = 0; k < p->pBest[p->Root].n; ++k )
        if ( p->pBest[p->Root].Lits[k] == Lit ) return;
    if ( Lmo_CandidateSeen(p, p->Root, Lit, 0) )
    { if ( p->fProfile ) ++p->DuplicateOrigins[fResub == 1 ? 0 : 1]; return; }
    Limit = Lmo_CostLimit(p, p->Root, Lit);
    Cost = Lmo_Cost(p, p->Root, Lit, Limit);
    if ( Cost > Limit ) return;
    Level = Vec_IntEntry(p->vPoolLevels, Lit>>1);
    FastLevel = Vec_IntEntry(p->vPoolLevels, p->pFastLits[p->Root]>>1);
    if ( p->pLevels[p->Root]-Level <= LMO_EARLY )
    {
        size_t Index = (size_t)p->Root*LMO_EARLY+p->pLevels[p->Root]-Level-1;
        if ( p->pEarlyLits[Index] < 0 || Cost < p->pEarlyCosts[Index] ||
             (Cost == p->pEarlyCosts[Index] && Lit < p->pEarlyLits[Index]) )
        { p->pEarlyLits[Index] = Lit; p->pEarlyCosts[Index] = Cost; Changed = 1; }
    }
    if ( Level < FastLevel || (Level == FastLevel && Cost < p->pFastCosts[p->Root]) )
    {
        p->pFastLits[p->Root] = Lit;
        p->pFastCosts[p->Root] = Cost;
        Changed = 1;
    }
    Status = Lmo_Save(p, p->pBest+p->Root, Lit, Cost);
    if ( p->pVersions && (Changed || Status) ) p->pVersions[p->Root] = ++p->Version;
    if ( !Status ) return;
    p->nRoots += Status == 2;
    ++p->nCandidates;
    if ( fResub == 1 ) ++p->nResub;
    else ++p->nLibrary;
}

/**Function*************************************************************

  Synopsis    [Price and retain a faster contextual edge implementation.]

***********************************************************************/
static void Lmo_ConsiderEdge( Lmo_Man_t * p, int Edge, int Lit )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Edge/2);
    int Driver = Edge&1 ? Gia_ObjFaninId1p(p->pGia, pObj) : Gia_ObjFaninId0p(p->pGia, pObj);
    int Other = Edge&1 ? Gia_ObjFaninLit0p(p->pGia, pObj) : Gia_ObjFaninLit1p(p->pGia, pObj);
    int Node, Status, Cost, Limit, k;
    if ( Vec_IntEntry(p->vPoolLevels, Lit>>1) >= p->pLevels[Driver] ) return;
    for ( k = 0; k < p->pEdgeBest[Edge].n; ++k )
        if ( p->pEdgeBest[Edge].Lits[k] == Lit ) return;
    if ( Lmo_CandidateSeen(p, Edge/2, Lit, 1+(Edge&1)) )
    { if ( p->fProfile ) ++p->DuplicateOrigins[0]; return; }
    Node = Lmo_Gate(p, Lit, Other, Gia_ObjIsXor(pObj));
    Limit = p->pEdgeBest[Edge].n < p->Alternatives ? INT_MAX : p->pEdgeBest[Edge].Costs[p->Alternatives-1];
    Cost = Lmo_Cost(p, Edge/2, Node, Limit);
    Status = Cost > Limit ? 0 : Lmo_Save(p, p->pEdgeBest+Edge, Lit, Cost);
    p->nEdgeRoots += Status == 2;
    p->nEdgeCandidates += Status != 0;
    // With only one late input this also supplies a globally equivalent,
    // earlier node implementation, which can share across all fanouts.
    Lmo_Consider(p, Node, 1);
}

/**Function*************************************************************

  Synopsis    [Check a candidate truth table against the required care sets.]

***********************************************************************/
static int Lmo_Matches( word * pValue, word * pOn, word * pOff, int nWords, int Compl )
{
    int w;
    for ( w = 0; w < nWords; ++w )
    {
        word Value = pValue[w] ^ -(word)Compl;
        if ( (Value & pOff[w]) || (~Value & pOn[w]) ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Simulate a bounded cut and collect available local divisors.]

  Description [Truth tables include every assignment of the cut leaves.
  Fanout expansion only adds earlier nodes whose two truths are known, so
  divisors neither introduce cycles nor depend on unmodeled inputs.]

***********************************************************************/
static int Lmo_Window( Lmo_Man_t * p, Lmo_Cut_t * c )
{
    int Result;
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_WINDOW);
    Gia_Obj_t * pObj;
    Vec_Int_t * vFans;
    int i, k, w, Id, a, b, Visits = 0;
    p->nWords = Abc_Truth6WordNum(c->n);
    if ( p->Stamp == INT_MAX )
    { memset(p->pSeen, 0, sizeof(int)*Gia_ManObjNum(p->pGia)); p->Stamp = 0; }
    ++p->Stamp;
    p->pSeen[0] = p->Stamp;
    p->pTruthIds[0] = 0;
    Abc_TtClear(Lmo_Truth(p, 0), p->nWords);
    Vec_IntClear(p->vWindow);
    for ( i = 0; i < c->n; ++i )
    {
        Id = c->Leaves[i];
        p->pSeen[Id] = p->Stamp;
        p->pTruthIds[Id] = Vec_IntSize(p->vWindow)+1;
        for ( w = 0; w < p->nWords; ++w )
            Lmo_Truth(p, Id)[w] = i < 6 ? s_LmoVars[i] : -(word)((w >> (i-6)) & 1);
        Vec_IntPush(p->vWindow, Id);
    }
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack, p->Root);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntEntryLast(p->vStack);
        if ( p->pSeen[Id] == p->Stamp ) { Vec_IntPop(p->vStack); continue; }
        pObj = Gia_ManObj(p->pGia, Id);
        if ( !Gia_ObjIsAnd(pObj) || ++Visits > 3*p->Window ) { Result = 0; goto done; }
        a = Gia_ObjFaninId0p(p->pGia, pObj);
        b = Gia_ObjFaninId1p(p->pGia, pObj);
        if ( p->pSeen[a] != p->Stamp ) { Vec_IntPush(p->vStack, a); continue; }
        if ( p->pSeen[b] != p->Stamp ) { Vec_IntPush(p->vStack, b); continue; }
        p->pTruthIds[Id] = Vec_IntSize(p->vWindow)+1;
        Lmo_TruthGate(Lmo_Truth(p, Id), Lmo_Truth(p, a), Lmo_Truth(p, b),
            p->nWords, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), Gia_ObjIsXor(pObj));
        p->pSeen[Id] = p->Stamp;
        Vec_IntPop(p->vStack);
        Vec_IntPush(p->vWindow, Id);
        if ( Vec_IntSize(p->vWindow) > p->Window ) { Result = 0; goto done; }
    }
    // This bounded closure also discovers already shared divisors outside
    // the root cone. Both fanins must be expressible in these cut coordinates.
    for ( i = 0; i < Vec_IntSize(p->vWindow) && Vec_IntSize(p->vWindow) < p->Window; ++i )
    {
        vFans = Vec_WecEntry(p->vFanouts, Vec_IntEntry(p->vWindow, i));
        Vec_IntForEachEntry(vFans, Id, k)
        {
            // Fanouts were inserted in increasing object order.
            if ( Id >= p->Root || Vec_IntSize(p->vWindow) == p->Window ) break;
            if ( p->pSeen[Id] == p->Stamp ) continue;
            pObj = Gia_ManObj(p->pGia, Id);
            a = Gia_ObjFaninId0p(p->pGia, pObj);
            b = Gia_ObjFaninId1p(p->pGia, pObj);
            if ( p->pSeen[a] != p->Stamp || p->pSeen[b] != p->Stamp ) continue;
            p->pTruthIds[Id] = Vec_IntSize(p->vWindow)+1;
            Lmo_TruthGate(Lmo_Truth(p, Id), Lmo_Truth(p, a), Lmo_Truth(p, b),
                p->nWords, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), Gia_ObjIsXor(pObj));
            p->pSeen[Id] = p->Stamp;
            Vec_IntPush(p->vWindow, Id);
        }
    }
    Result = 1;
done:
    Lmo_TimeSwitch(p, TimePrevious);
    return Result;
}

// Classify each window truth once. Preserve the original first-eligible
// divisor order separately for the root deadline and the earlier edge
// deadline; equality candidates still retain every physical implementation.
/**Function*************************************************************

  Synopsis    [Prepare and classify the divisors of the current window.]

***********************************************************************/
static void Lmo_PrepareDivisors( Lmo_Man_t * p )
{
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_RESUB);
    int i, Id, Slot, Class, k;
    if ( !++p->DivStamp )
    { memset(p->DivStamps, 0, sizeof(p->DivStamps)); ++p->DivStamp; }
    p->nDivIds[0] = p->nDivIds[1] = 0;
    Vec_IntForEachEntry(p->vWindow, Id, i)
    {
        word Hash;
        p->DivLits[i] = p->fMapped ? p->pFastLits[Id] : 2*Id;
        p->DivTimes[i] = Vec_IntEntry(p->vPoolLevels, p->DivLits[i]>>1);
        if ( Id == p->Root || p->DivTimes[i]+1 >= p->pLevels[p->Root] ) continue;
        Hash = p->DivHashes[i] = Lmo_TruthHash(Lmo_Truth(p, Id), p->nWords);
        Slot = (int)((Hash ^ (Hash>>32)) & 1023);
        while ( p->DivStamps[Slot] == p->DivStamp && !Abc_TtEqual(Lmo_Truth(p, Id),
                Lmo_Truth(p, Vec_IntEntry(p->vWindow, p->DivBins[Slot])), p->nWords) ) Slot = (Slot+1)&1023;
        if ( p->DivStamps[Slot] != p->DivStamp )
        { p->DivStamps[Slot] = p->DivStamp; p->DivBins[Slot] = i; p->DivSeen[i] = 0; }
        Class = p->DivBins[Slot];
        for ( k = 0; k < 2; ++k )
            if ( p->DivTimes[i]+1 < p->pLevels[p->Root]-k && !(p->DivSeen[Class] & (1<<k)) && p->nDivIds[k] < p->Divs )
            { p->DivSeen[Class] |= 1<<k; p->DivIds[k][p->nDivIds[k]++] = i; }
    }
    Lmo_TimeSwitch(p, TimePrevious);
}

/**Function*************************************************************

  Synopsis    [Generate and evaluate resubstitution candidates in a cut window.]

***********************************************************************/
static void Lmo_Resub( Lmo_Man_t * p, int Edge )
{
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_RESUB);
    word * Truth = p->pOn, * Off = p->pOff, * Values = p->pValues;
    void ** Divs = p->pDivs;
    int * Lits = p->pLits, * Levels = p->pTimes;
    int n = 2, Id, i, k, a, b, Root, Valid, Lit, Bound = p->pLevels[p->Root], nWords = p->nWords;
    Vec_Int_t * vRecipe;
    Abc_TtCopy(Truth, Lmo_Truth(p, p->Root), nWords, 0);
    if ( Edge < 0 ) Abc_TtCopy(Off, Truth, nWords, 1);
    else
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, p->Root);
        a = Edge&1 ? Gia_ObjFaninLit1p(p->pGia, pObj) : Gia_ObjFaninLit0p(p->pGia, pObj);
        b = Edge&1 ? Gia_ObjFaninLit0p(p->pGia, pObj) : Gia_ObjFaninLit1p(p->pGia, pObj);
        Bound = p->pLevels[a>>1];
        if ( !Bound || Bound+1 != p->pLevels[p->Root] ) goto done;
        if ( Gia_ObjIsXor(pObj) )
        {
            // Both inputs of XOR are always observable. Edge replacements
            // must preserve the complete signed input function.
            Abc_TtCopy(Truth, Lmo_Truth(p, a>>1), nWords, a&1);
            Abc_TtCopy(Off, Truth, nWords, 1);
        }
        else
            // An AND input is observable only while its other input is 1.
            Lmo_TruthAnd(Off, Lmo_Truth(p, a>>1), Lmo_Truth(p, b>>1), nWords, !(a&1), b&1);
    }
    Divs[0] = Off; Divs[1] = Truth;
    p->ProblemHashes[0] = Lmo_TruthHash(Off, nWords);
    p->ProblemHashes[1] = Lmo_TruthHash(Truth, nWords);
    Lits[0] = Lits[1] = Levels[0] = Levels[1] = 0;
    Abc_TtClear(Values, 2*nWords);
    if ( Abc_TtIsConst0(Truth, nWords) || Abc_TtIsConst0(Off, nWords) )
    {
        Lit = !Abc_TtIsConst0(Truth, nWords);
        if ( Edge < 0 ) Lmo_Consider(p, Lit, 1);
        else Lmo_ConsiderEdge(p, Edge, Lit);
    }
    Vec_IntForEachEntry(p->vWindow, Id, i)
    {
        int DivLit = p->DivLits[i], DivLevel = p->DivTimes[i];
        if ( Id == p->Root || DivLevel >= Bound ) continue;
        for ( k = 0; k < 2; ++k )
            if ( Lmo_Matches(Lmo_Truth(p, Id), Truth, Off, nWords, k) )
            {
                if ( Edge < 0 ) Lmo_Consider(p, DivLit^k, 1);
                else Lmo_ConsiderEdge(p, Edge, DivLit^k);
            }
    }
    // Any divisor of a nontrivial recipe needs one gate of slack. The
    // precomputed truth classes remove repeated pairwise truth comparisons.
    for ( i = 0; i < p->nDivIds[Edge >= 0]; ++i )
    {
        k = p->DivIds[Edge >= 0][i]; Id = Vec_IntEntry(p->vWindow, k);
        Lits[n] = p->DivLits[k];
        Levels[n] = p->DivTimes[k];
        Abc_TtCopy(Values+n*nWords, Lmo_Truth(p, Id), nWords, 0);
        Divs[n] = Lmo_Truth(p, Id);
        p->ProblemHashes[n] = p->DivHashes[k];
        ++n;
    }
    if ( n == 2 || !p->Nodes ) goto done;
    Lmo_ResubRecipes(p, n);
    Vec_WecForEachLevel(p->vRecipes, vRecipe, k)
    {
        Valid = Vec_IntSize(vRecipe) > 0 && (Vec_IntSize(vRecipe) & 1) && Vec_IntSize(vRecipe)/2 <= p->Nodes;
        for ( i = 0; Valid && i < Vec_IntSize(vRecipe)/2; ++i )
        {
            a = Vec_IntEntry(vRecipe, 2*i); b = Vec_IntEntry(vRecipe, 2*i+1);
            if ( a < 0 || b < 0 || (a>>1) >= n+i || (b>>1) >= n+i || (a>>1) == 1 || (b>>1) == 1 || (!p->fXor && (a>>1) > (b>>1)) )
            { Valid = 0; break; }
            Lmo_TruthGate(Values+(n+i)*nWords, Values+(a>>1)*nWords, Values+(b>>1)*nWords,
                nWords, a&1, b&1, p->fXor && a > b);
            Levels[n+i] = 1 + Abc_MaxInt(Levels[a>>1], Levels[b>>1]);
        }
        if ( !Valid ) continue;
        Root = Vec_IntEntryLast(vRecipe);
        if ( Root < 0 || (Root>>1) >= n+Vec_IntSize(vRecipe)/2 || (Root>>1) == 1 ||
             !Lmo_Matches(Values+(Root>>1)*nWords, Truth, Off, nWords, Root&1) ||
             Levels[Root>>1] >= Bound ) continue;
        for ( i = 0; i < Vec_IntSize(vRecipe)/2; ++i )
        {
            a = Vec_IntEntry(vRecipe, 2*i); b = Vec_IntEntry(vRecipe, 2*i+1);
            Lits[n+i] = Lmo_Gate(p, Lits[a>>1]^(a&1), Lits[b>>1]^(b&1), p->fXor && a > b);
        }
        if ( Edge < 0 ) Lmo_Consider(p, Lits[Root>>1]^(Root&1), 1);
        else Lmo_ConsiderEdge(p, Edge, Lits[Root>>1]^(Root&1));
    }
done:
    Lmo_TimeSwitch(p, TimePrevious);
}

/**Function*************************************************************

  Synopsis    [Try timing-feasible structures from the active six-input bank.]

  Description [Every instantiated structure is checked against the full
  local truth table before it can participate in the critical-path cut.]

***********************************************************************/
static int Lmo_Instantiate( Lmo_Man_t * p, const int * pCode, int Count, int * Lits )
{
    int i, a, b, Root, Lit, Origin = p->fInMerged ? 2 : p->fMapped ? 1 : 0;
    int Previous = Lmo_TimeSwitch(p, LMO_TIME_INSTANTIATE);
    if ( p->fProfile ) ++p->Builds[Origin];
    for ( i = 0; i < Count; ++i )
    {
        a = pCode[2*i]; b = pCode[2*i+1];
        Lits[6+i] = Lmo_Gate(p, Lits[a>>1]^(a&1), Lits[b>>1]^(b&1), p->fXor && a > b);
    }
    Root = pCode[2*Count];
    Lit = Lits[Root>>1]^(Root&1);
    Lmo_TimeSwitch(p, Previous);
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Match and instantiate eligible library structures for a cut.]

***********************************************************************/
static void Lmo_Library( Lmo_Man_t * p, word Truth, int n, int * pTimes )
{
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_LIBRARY);
    Lms_CutMatch_t Match;
    const int * pPos;
    int i, k, Po, nPos, Area, Delay, Arrival, Offset, Count, a, b, Root, Variant, Goal, Previous, Lit, * pCode;
    int Lits[70];
    word Values[70];
    if ( !p->pLibAreas || Lmo_Expired(p) ) goto done;
    Previous = Lmo_TimeSwitch(p, LMO_TIME_MATCH);
    Delay = Abc_RecTargetCost3(Truth, n, pTimes, &Area, &Match);
    Lmo_TimeSwitch(p, Previous);
    if ( Delay >= p->pLevels[p->Root] || Match.Class < 0 ) goto done;
    nPos = Abc_RecTargetProfiles3(Match.Class, &pPos);
    for ( k = 0; k < nPos; ++k )
    {
        Po = pPos[k];
        if ( p->pLibAreas[Po] > p->Nodes ) continue;
        Arrival = 0;
        for ( i = 0; i < n; ++i ) Arrival = Abc_MaxInt(Arrival,
            pTimes[(int)Match.Perm[i]] + (int)((p->pLibDelays[Po] >> (4*i)) & 15));
        if ( Arrival >= p->pLevels[p->Root] ) continue;
        for ( ; Po >= 0; Po = Abc_RecTargetNext3(Po) )
        {
            Vec_IntFillExtra(p->vOffsets, Po+1, -1);
            Offset = Vec_IntEntry(p->vOffsets, Po);
            if ( Offset < 0 )
            {
                Offset = Vec_IntSize(p->vPrograms);
                if ( p->fXor ) Abc_RecTargetRecipeXor3(Po, p->vPrograms);
                else Abc_RecTargetRecipe3(Po, p->vPrograms);
                Vec_IntWriteEntry(p->vOffsets, Po, Offset);
            }
            pCode = Vec_IntArray(p->vPrograms)+Offset;
            Count = *pCode++;
            if ( Count > p->Nodes ) continue;
            for ( i = 0; i < 6; ++i ) { Lits[i] = 0; Values[i] = 0; }
            for ( i = 0; i < n; ++i )
            {
                int Id = p->Leaves[(int)Match.Perm[i]], Phase = (Match.Phase >> i) & 1;
                Lits[i] = (p->fMapped ? p->pFastLits[Id] : 2*Id)^Phase;
                Values[i] = *Lmo_Truth(p, Id) ^ -(word)Phase;
            }
            for ( i = 0; i < Count; ++i )
            {
                word x, y;
                a = pCode[2*i]; b = pCode[2*i+1];
                assert((a>>1) < 6+i && (b>>1) < 6+i);
                x = Values[a>>1] ^ -(word)(a&1); y = Values[b>>1] ^ -(word)(b&1);
                Values[6+i] = p->fXor && a > b ? x ^ y : x & y;
            }
            Root = pCode[2*Count] ^ ((Match.Phase >> n) & 1);
            if ( (Values[Root>>1] ^ -(word)(Root&1)) != *Lmo_Truth(p, p->Root) ) continue;
            for ( Variant = p->fSkipTarget; Variant < 1+(p->fMapped && !p->fTargetOnly && Arrival < p->pLevels[p->Root]-1 &&
                  Arrival <= Vec_IntEntry(p->vPoolLevels, p->pFastLits[p->Root]>>1)); ++Variant )
            {
                Goal = Variant ? Arrival : p->pLevels[p->Root]-1;
                if ( p->fMapped )
                    for ( i = 0; i < n; ++i )
                    {
                        int Id = p->Leaves[(int)Match.Perm[i]], Pin = (int)((p->pLibDelays[Po] >> (4*i)) & 15);
                        int Lit = Lmo_Leaf(p, Id, Goal-Pin);
                        assert(Lit >= 0);
                        Lits[i] = Lit ^ ((Match.Phase >> i) & 1);
                    }
                Lit = Lmo_Instantiate(p, pCode, Count, Lits);
                Lmo_Consider(p, Lit^((Match.Phase >> n) & 1), 2);
            }
            // The composed bank visits every feasible delay/area profile,
            // retaining one structural representative per profile. The
            // fastest profile alone can needlessly accelerate expensive
            // pins even when a slower profile meets the one-level target.
            if ( p->fOnePerProfile ) break;
        }
    }
done:
    Lmo_TimeSwitch(p, TimePrevious);
}

// Full leaf-key comparisons make this an exact per-pass deduplication map.
// Mapping versions change whenever a retained helper changes; the greatest
// version in a window changes on every relevant update, even if an older
// helper is later rediscovered. Hash collisions never suppress a cut.
/**Function*************************************************************

  Synopsis    [Find or allocate the per-root memo entry for a cut.]

***********************************************************************/
static Lmo_CutMemo_t * Lmo_CutMemo( Lmo_Man_t * p, Lmo_Cut_t * c )
{
    Lmo_CutMemo_t * e;
    unsigned Hash = (unsigned)p->Root*12582917u;
    int i, Slot, Bytes;
    if ( !p->nCutBins ) return NULL;
    for ( i = 0; i < c->n; ++i ) Hash = (Hash ^ (unsigned)c->Leaves[i])*16777619u;
    Slot = (int)(Hash & (p->nCutBins-1));
    for ( e = p->pCutBins[Slot]; e; e = e->pNext )
        if ( e->Root == p->Root && e->nLeaves == c->n && !memcmp(e->Leaves, c->Leaves, sizeof(int)*c->n) ) return e;
    Bytes = (int)((sizeof(*e)+(size_t)Abc_MaxInt(0, c->n-1)*sizeof(int)+7) & ~(size_t)7);
    if ( !p->pCutMem ) p->pCutMem = Mem_FlexStart();
    // Bound stored entries; Mem_Flex also owns a small amount of chunk slack.
    if ( Mem_FlexReadMemUsage(p->pCutMem) > 64*1024*1024-Bytes )
    { ++p->nCutOverflows; return NULL; }
    e = (Lmo_CutMemo_t *)Mem_FlexEntryFetch(p->pCutMem, Bytes);
    memset(e, 0, Bytes);
    e->Root = p->Root; e->nLeaves = c->n; memcpy(e->Leaves, c->Leaves, sizeof(int)*c->n);
    e->Resub = e->Library[0] = e->Library[1] = ~(word)0;
    e->pNext = p->pCutBins[Slot]; p->pCutBins[Slot] = e; ++p->nCutMemos;
    return e;
}

/**Function*************************************************************

  Synopsis    [Evaluate a cut when its original or helper binding has changed.]

***********************************************************************/
static void Lmo_TryCut( Lmo_Man_t * p, Lmo_Cut_t * c, int fWindowReady )
{
    word Truth;
    word Version = 0, LibVersion = 0;
    Lmo_CutMemo_t * e = Lmo_CutMemo(p, c);
    int i, Id, Times[6], n, Mode;
    if ( e && (e->fFailed || (!p->fCompose && e->fBaseDone)) ) { ++p->nWindowSkips; return; }
    if ( !fWindowReady && !Lmo_Window(p, c) ) { if ( e ) e->fFailed = 1; return; }
    ++p->nCuts;
    ++p->CutCounts[c->n];
    if ( p->fCompose )
        Vec_IntForEachEntry(p->vWindow, Id, i)
            if ( Id != p->Root && Version < p->pVersions[Id] ) Version = p->pVersions[Id];
    p->fMapped = Version != 0;
    if ( !e || e->Resub != Version )
    {
        Lmo_PrepareDivisors(p);
        Lmo_Resub(p, -1);
        Lmo_Resub(p, 2*p->Root);
        Lmo_Resub(p, 2*p->Root+1);
        if ( e ) e->Resub = Version;
    }
    else ++p->nResubSkips;
    // Library matching remains a six-input engine;
    // larger cuts use the multiword resubstitution engine above.
    if ( !p->Nodes || c->n > 6 ) goto done;
    Truth = *Lmo_Truth(p, p->Root);
    memcpy(p->Leaves, c->Leaves, sizeof(int)*c->n);
    n = Abc_Tt6MinBase(&Truth, p->Leaves, c->n);
    if ( n < 2 ) goto done;
    if ( p->fCompose )
        for ( i = 0; i < n; ++i )
            if ( LibVersion < p->pVersions[p->Leaves[i]] ) LibVersion = p->pVersions[p->Leaves[i]];
    p->fMapped = LibVersion != 0;
    for ( i = 0; i < n; ++i )
    {
        Times[i] = Vec_IntEntry(p->vPoolLevels, (p->fMapped ? p->pFastLits[p->Leaves[i]] : 2*p->Leaves[i])>>1);
        if ( Times[i]+1 >= p->pLevels[p->Root] || Times[i] > 1000000 ) goto done;
    }
    Mode = p->fMapped && p->fTargetOnly;
    if ( !e || e->Library[Mode] != LibVersion )
    {
        p->fSkipTarget = e && p->fMapped && !p->fTargetOnly && e->Library[1] == LibVersion;
        Lmo_Library(p, Truth, n, Times);
        p->fSkipTarget = 0;
        if ( e ) e->Library[Mode] = LibVersion;
    }
    else ++p->nLibrarySkips;
done:
    if ( e && !p->fCompose ) e->fBaseDone = 1;
    p->fMapped = 0;
}

// Frontier expansion tends to spend its entire budget on shallow cuts.
// Also visit the delay-ranked cuts obtained by merging fanin cut banks.
// This is the same cut enumerator used by LMS, not a whole-network mapping.
/**Function*************************************************************

  Synopsis    [Evaluate a collected cut with original or composed fanins.]

***********************************************************************/
static int Lmo_MergedCut( void * pData, int Root, int nLeaves,
    const int * pLeaves, word Truth, const Lms_CutMatch_t * pMatch )
{
    Lmo_Man_t * p = (Lmo_Man_t *)pData;
    Lmo_Cut_t Cut;
    int i, w, Times[6], SkipTarget = 0;
    if ( p->pCache->Deadline && !(p->nTimeChecks++ & 63) && Lmo_Expired(p) ) return -1;
    (void)pMatch;
    if ( p->pFocus && !p->pFocus[Root] ) return 1;
    if ( nLeaves > p->CutSize || (!p->fCompose && !Lmo_IsCritical(p, Root)) ) return 1;
    p->Root = Root;
    if ( p->fCompose && p->MappedRoot != Root )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Root);
        int a = Gia_ObjFaninLit0p(p->pGia, pObj), b = Gia_ObjFaninLit1p(p->pGia, pObj);
        int x = Lmo_Leaf(p, a>>1, p->pLevels[Root]-2), y = Lmo_Leaf(p, b>>1, p->pLevels[Root]-2);
        p->MappedRoot = Root;
        if ( x >= 0 && y >= 0 ) Lmo_Consider(p, Lmo_Gate(p, x^(a&1), y^(b&1), Gia_ObjIsXor(pObj)), 1);
        Lmo_Consider(p, Lmo_Gate(p, p->pFastLits[a>>1]^(a&1), p->pFastLits[b>>1]^(b&1), Gia_ObjIsXor(pObj)), 1);
    }
    // Keep the gate replay above independent of cut support: its structural
    // fanins may have changed even when this minimized cut's leaves did not.
    if ( p->fCompose && p->pReplayVersion )
    {
        word Version = 0;
        for ( i = 0; i < nLeaves; ++i )
            if ( Version < p->pVersions[pLeaves[i]] ) Version = p->pVersions[pLeaves[i]];
        if ( p->pReplayVersion[p->fTargetOnly] == Version ||
             (!Version && p->pReplayVersion[1] == 0) )
        { ++p->nReplaySkips; return 1; }
        SkipTarget = !p->fTargetOnly && p->pReplayVersion[1] == Version;
        p->pReplayVersion[p->fTargetOnly] = Version;
    }
    if ( nLeaves < 2 )
    {
        Lmo_Consider(p, nLeaves ? (p->fCompose ? p->pFastLits[pLeaves[0]] : 2*pLeaves[0])^(int)(Truth&1) : (int)(Truth&1), 1);
        return 1;
    }
    Cut.n = nLeaves;
    memcpy(Cut.Leaves, pLeaves, sizeof(int)*nLeaves);
    if ( !p->fCompose && Lmo_Window(p, &Cut) )
    {
        Lmo_TryCut(p, &Cut, 1);
        return 1;
    }
    // Support minimization can remove structural leaves. The collector's
    // exact truth still defines a valid replacement, but the receiver's
    // individual input truths need not exist in these coordinates.
    ++p->nCuts; ++p->CutCounts[nLeaves];
    p->nWords = 1;
    Vec_IntClear(p->vWindow);
    p->pTruthIds[Root] = 0;
    for ( w = 0; w < p->nWords; ++w ) Lmo_Truth(p, Root)[w] = Truth;
    for ( i = 0; i < nLeaves; ++i )
    {
        p->Leaves[i] = pLeaves[i];
        p->pTruthIds[pLeaves[i]] = i+1;
        for ( w = 0; w < p->nWords; ++w ) Lmo_Truth(p, pLeaves[i])[w] = s_LmoVars[i];
        Vec_IntPush(p->vWindow, pLeaves[i]);
        Times[i] = p->pLevels[pLeaves[i]];
    }
    p->fMapped = p->fOnePerProfile = p->fCompose;
    if ( !p->fCompose ) { Lmo_PrepareDivisors(p); Lmo_Resub(p, -1); }
    if ( p->fCompose )
        for ( i = 0; i < nLeaves; ++i ) Times[i] = Vec_IntEntry(p->vPoolLevels, p->pFastLits[pLeaves[i]]>>1);
    p->fSkipTarget = SkipTarget;
    Lmo_Library(p, Truth, nLeaves, Times);
    p->fSkipTarget = 0;
    p->fMapped = p->fOnePerProfile = 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Retain a collected cut and its truth table for replay.]

***********************************************************************/
static int Lmo_RememberMerged( void * pData, int Root, int nLeaves,
    const int * pLeaves, word Truth, const Lms_CutMatch_t * pMatch )
{
    Lmo_Man_t * p = (Lmo_Man_t *)pData;
    int i;
    if ( p->pCache->Deadline && !(p->nTimeChecks++ & 63) && Lmo_Expired(p) ) return -1;
    (void)pMatch;
    if ( p->pFocus && !p->pFocus[Root] ) return 1;
    if ( p->pBankCone && !p->pBankCone[Root] ) return 1;
    if ( (size_t)(Vec_IntSize(p->vMerged)+8)*sizeof(int) +
         (size_t)(Vec_WrdSize(p->vMergedTruths)+1)*3*sizeof(word) > 64*1024*1024 )
    { p->fMergedDirect = 1; return -1; }
    Vec_IntPushTwo(p->vMerged, Root, nLeaves);
    for ( i = 0; i < nLeaves; ++i ) Vec_IntPush(p->vMerged, pLeaves[i]);
    Vec_WrdPush(p->vMergedTruths, Truth);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Replay the retained cut bank in topological order.]

***********************************************************************/
static int Lmo_EnumerateMerged( Lmo_Man_t * p, Gia_Man_t * pCuts, Lms_CutVisit_t pVisit )
{
    int * pLimits, i, Result, Cuts = Abc_MinInt(p->Cuts, 128);
    unsigned char * pCone = p->pFocus;
    // The focus includes the complete fanin cone of every requested root.
    // Full budgets there preserve its merged bank; cheap outside budgets
    // cannot affect these roots, including the delay/area ranking of cuts.
    pLimits = ABC_CALLOC(int, Gia_ManObjNum(pCuts));
    // Outside escalation, keep a smaller helper bank from the first pass.
    // This also changes downstream cut ranking and is an area/delay heuristic.
    for ( i = 0; i < Gia_ManObjNum(pCuts); ++i )
        pLimits[i] = pCone ? (pCone[i] ? Cuts : 1) : p->pBankCone && !p->pBankCone[i] ? 1 :
            (Lmo_IsCritical(p, i) || p->fFullHelpers ? Cuts : Abc_MinInt(Cuts, 8));
    Result = Lms_CutsCollectBudgetedTimed(pCuts, Cuts, pLimits, Abc_RecTargetCost3, pVisit, p, 0, p->pCache->Deadline);
    ABC_FREE(pLimits);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Release the retained cut bank and its replay versions.]

***********************************************************************/
static void Lmo_ClearMerged( Lmo_Man_t * p )
{
    Vec_IntFreeP(&p->vMerged); Vec_WrdFreeP(&p->vMergedTruths);
    ABC_FREE(p->pMergedVersions);
    p->pReplayVersion = NULL; p->fMergedDirect = 0;
}

// Keep normal budgets throughout every critical root's fanin cone, so its
// retained cuts are identical. Outside this cone, early rounds read no bank.
// Limit this mode to large, sparse-critical graphs to avoid routine recollection.
/**Function*************************************************************

  Synopsis    [Mark fanin cones needed by the focused cut collection.]

***********************************************************************/
static void Lmo_FocusBank( Lmo_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, Count = 0, n = Gia_ManAndNum(p->pGia);
    if ( n < 10000 || (size_t)p->nCritical*100 >= (size_t)n ) return;
    p->pBankCone = ABC_CALLOC(unsigned char, Gia_ManObjNum(p->pGia));
    Gia_ManForEachAnd(p->pGia, pObj, i)
        if ( Lmo_IsCritical(p, i) ) p->pBankCone[i] = 1;
    for ( i = Gia_ManObjNum(p->pGia)-1; i > 0; --i )
    {
        pObj = Gia_ManObj(p->pGia, i);
        if ( !p->pBankCone[i] || !Gia_ObjIsAnd(pObj) ) continue;
        ++Count;
        p->pBankCone[Gia_ObjFaninId0p(p->pGia, pObj)] = 1;
        p->pBankCone[Gia_ObjFaninId1p(p->pGia, pObj)] = 1;
    }
    if ( p->fProfile )
        Abc_Print(1, "LMS2 initial bank: %d/%d critical gates; %d gates in their fanin cones.\n", p->nCritical, n, Count);
}

/**Function*************************************************************

  Synopsis    [Collect merged cuts with role-based and focused budgets.]

***********************************************************************/
static void Lmo_CollectMerged( Lmo_Man_t * p )
{
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_REPLAY);
    int i, k, Root, nLeaves, Previous, InMerged = p->fInMerged;
    p->fInMerged = 1;
    if ( !p->pLibAreas || Lmo_Expired(p) ) goto done;
    if ( !p->vMerged && !p->fMergedDirect )
    {
        p->vMerged = Vec_IntAlloc(1000);
        p->vMergedTruths = Vec_WrdAlloc(1000);
        Previous = Lmo_TimeSwitch(p, LMO_TIME_BANK);
        if ( !Lmo_EnumerateMerged(p, p->pGia, Lmo_RememberMerged) )
        {
            if ( p->fMergedDirect ) Abc_Print(1, "LMS2: merged-cut cache reached 64 MiB; continuing with direct enumeration.\n");
            Lmo_ClearMerged(p);
            p->fMergedDirect = 1;
        }
        Lmo_TimeSwitch(p, Previous);
        if ( p->vMergedTruths && p->pCache->nBins )
        {
            p->pMergedVersions = ABC_ALLOC(word, 2*Vec_WrdSize(p->vMergedTruths));
            memset(p->pMergedVersions, 0xFF, sizeof(word)*2*Vec_WrdSize(p->vMergedTruths));
        }
    }
    if ( p->fMergedDirect )
    {
        if ( Lmo_Expired(p) ) goto done;
        Previous = Lmo_TimeSwitch(p, LMO_TIME_BANK);
        Lmo_EnumerateMerged(p, p->pGia, Lmo_MergedCut);
        Lmo_TimeSwitch(p, Previous);
        goto done;
    }
    // The original graph and collection timing are unchanged across the
    // original-divisor, modest-composition, and aggressive-composition rounds.
    for ( i = k = 0; i < Vec_IntSize(p->vMerged); ++k )
    {
        if ( !(k & 127) && Lmo_Expired(p) ) break;
        Root = Vec_IntEntry(p->vMerged, i++);
        nLeaves = Vec_IntEntry(p->vMerged, i++);
        p->pReplayVersion = p->pMergedVersions ? p->pMergedVersions+2*k : NULL;
        Lmo_MergedCut(p, Root, nLeaves, Vec_IntArray(p->vMerged)+i, Vec_WrdEntry(p->vMergedTruths, k), NULL);
        i += nLeaves;
    }
    p->pReplayVersion = NULL;
done:
    p->fInMerged = InMerged;
    Lmo_TimeSwitch(p, TimePrevious);
}

/**Function*************************************************************

  Synopsis    [Enumerate distinct cuts by expanding their frontier.]

  Description [Initially only zero-slack interior nodes can be expanded;
  side inputs remain boundary leaves. A second collection permits side-cone
  expansion within the same budget before selecting a critical-path cut.]

***********************************************************************/
static void Lmo_Collect( Lmo_Man_t * p, int fSideCones )
{
    Lmo_Cut_t * pCuts = ABC_ALLOC(Lmo_Cut_t, p->Cuts), Next;
    Gia_Obj_t * pObj;
    int Root, nCuts, i, k, j, v, a, b, Id, Found;
    Gia_ManForEachAnd(p->pGia, pObj, Root)
    {
        if ( !(Root & 15) && Lmo_Expired(p) ) break;
        if ( p->pFocus ? !p->pFocus[Root] :
             (!Lmo_IsCritical(p, Root) || (p->fUncovered && !p->pNeeded[Root])) ) continue;
        p->Root = Root;
        pCuts[0].n = 1; pCuts[0].Leaves[0] = Root;
        nCuts = 1;
        for ( i = 0; i < nCuts; ++i )
        {
            if ( i )
                Lmo_TryCut(p, pCuts+i, 0);
            for ( k = 0; k < pCuts[i].n && nCuts < p->Cuts; ++k )
            {
                Id = pCuts[i].Leaves[k];
                if ( !Gia_ObjIsAnd(Gia_ManObj(p->pGia, Id)) || (!fSideCones && !Lmo_IsCritical(p, Id)) ) continue;
                a = Gia_ObjFaninId0p(p->pGia, Gia_ManObj(p->pGia, Id));
                b = Gia_ObjFaninId1p(p->pGia, Gia_ManObj(p->pGia, Id));
                Next.n = 0;
                for ( j = 0; j < pCuts[i].n; ++j ) if ( j != k ) Next.Leaves[Next.n++] = pCuts[i].Leaves[j];
                for ( j = 0; j < 2; ++j )
                {
                    v = j ? b : a;
                    if ( !v ) continue;
                    for ( Found = 0; Found < Next.n; ++Found ) if ( Next.Leaves[Found] == v ) break;
                    if ( Found < Next.n ) continue;
                    if ( Next.n == p->CutSize ) break;
                    Next.Leaves[Next.n++] = v;
                }
                if ( j < 2 ) continue;
                for ( j = 1; j < Next.n; ++j )
                    for ( v = j; v && Next.Leaves[v] < Next.Leaves[v-1]; --v )
                        ABC_SWAP(int, Next.Leaves[v], Next.Leaves[v-1]);
                for ( j = 0; j < nCuts; ++j )
                    if ( Next.n == pCuts[j].n && !memcmp(Next.Leaves, pCuts[j].Leaves, sizeof(int)*Next.n) ) break;
                if ( j == nCuts ) pCuts[nCuts++] = Next;
            }
        }
    }
    ABC_FREE(pCuts);
}

// Restrict expensive synthesis to paths not covered by available whole-node
// replacements. Ignoring contextual edges makes this filter conservative.
// Nodes outside these paths cannot repair the vertex-only feasibility failure.
/**Function*************************************************************

  Synopsis    [Mark critical paths that still have no available replacement.]

***********************************************************************/
static void Lmo_Uncovered( Lmo_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, a, b, n = Gia_ManObjNum(p->pGia);
    int * pReach = ABC_CALLOC(int, n);
    memset(p->pNeeded, 0, sizeof(int)*n);
    Gia_ManForEachObj(p->pGia, pObj, i)
    {
        if ( Gia_ObjIsCo(pObj) || !Lmo_IsCritical(p, i) || p->pBest[i].n ) continue;
        if ( !Gia_ObjIsAnd(pObj) ) { pReach[i] = 1; continue; }
        a = Gia_ObjFaninId0p(p->pGia, pObj); b = Gia_ObjFaninId1p(p->pGia, pObj);
        pReach[i] = (pReach[a] && p->pLevels[a]+1 == p->pLevels[i]) ||
                    (pReach[b] && p->pLevels[b]+1 == p->pLevels[i]);
    }
    Gia_ManForEachCo(p->pGia, pObj, i)
    {
        a = Gia_ObjFaninId0p(p->pGia, pObj);
        if ( p->pLevels[a] == p->Depth && pReach[a] ) p->pNeeded[a] = 1;
    }
    for ( i = n-1; i > 0; --i )
    {
        pObj = Gia_ManObj(p->pGia, i);
        if ( !p->pNeeded[i] || !Gia_ObjIsAnd(pObj) ) continue;
        a = Gia_ObjFaninId0p(p->pGia, pObj); b = Gia_ObjFaninId1p(p->pGia, pObj);
        if ( pReach[a] && p->pLevels[a]+1 == p->pLevels[i] ) p->pNeeded[a] = 1;
        if ( pReach[b] && p->pLevels[b]+1 == p->pLevels[i] ) p->pNeeded[b] = 1;
    }
    p->nUncovered = p->nUncoveredCone = 0;
    memset(pReach, 0, sizeof(int)*n);
    for ( i = n-1; i > 0; --i )
    {
        pObj = Gia_ManObj(p->pGia, i);
        if ( !Gia_ObjIsAnd(pObj) || (!p->pNeeded[i] && !pReach[i]) ) continue;
        p->nUncovered += p->pNeeded[i] != 0;
        ++p->nUncoveredCone;
        pReach[Gia_ObjFaninId0p(p->pGia, pObj)] = 1;
        pReach[Gia_ObjFaninId1p(p->pGia, pObj)] = 1;
    }
    ABC_FREE(pReach);
}

// The initial infinite-capacity graph is acyclic, so one topological pass
// decides whether any input-to-output path cannot be cut by a candidate.
// This test includes the currently excluded edge alternatives in SAT search.
/**Function*************************************************************

  Synopsis    [Detect an uncuttable critical path before maximum flow.]

***********************************************************************/
static int Lmo_InfinitePath( Lmo_Man_t * p )
{
    unsigned char * pReach = ABC_CALLOC(unsigned char, Gia_ManObjNum(p->pGia));
    Gia_Obj_t * pObj;
    int Id, k, a, Found = 0;
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        if ( Gia_ObjIsCo(pObj) )
        {
            a = Gia_ObjFaninId0p(p->pGia, pObj);
            if ( p->pLevels[a] == p->Depth && pReach[a] ) { Found = 1; break; }
            continue;
        }
        if ( !Lmo_IsCritical(p, Id) || p->pBest[Id].n ) continue;
        if ( !Gia_ObjIsAnd(pObj) ) { pReach[Id] = 1; continue; }
        for ( k = 0; k < 2; ++k )
        {
            a = k ? Gia_ObjFaninId1p(p->pGia, pObj) : Gia_ObjFaninId0p(p->pGia, pObj);
            if ( p->pLevels[a]+1 != p->pLevels[Id] || !pReach[a] ) continue;
            if ( !p->pEdgeBest || p->pEdgeIndex[2*Id+k] >= p->pEdgeBest[2*Id+k].n ) pReach[Id] = 1;
        }
    }
    ABC_FREE(pReach);
    return Found;
}

/**Function*************************************************************

  Synopsis    [Find an area-weighted edge/vertex cut of every longest path.]

  Description [Split each node into input/output vertices. Its finite edge
  represents a verified replacement reducing its arrival by at least one.
  Zero-slack fanin edges carry their cheapest enabled contextual replacement.
  Unavailable transformations have infinite capacity. The integer objective
  first minimizes estimated added ANDs, then the number of replacements.
  Negative local costs are clamped to zero; real batch area is checked later.
  Breadth-first augmenting paths avoid recursion even on very deep AIGs.]

***********************************************************************/
static int Lmo_Select( Lmo_Man_t * p )
{
    Extra_Flow_t F, * f = &F;
    Gia_Obj_t * pObj;
    int Id, k, a, Source, Sink, Count = 0, n = Gia_ManObjNum(p->pGia);
    word Inf = ABC_CONST(0x4000000000000000), Flow = 0, Delta;
    word Scale = (word)n*(p->pEdgeBest ? 3 : 1)+1;
    int fInfinitePath = Lmo_InfinitePath(p);
    Source = 2*n; Sink = Source+1;
    if ( fInfinitePath || !Extra_FlowStart(f, Sink+1, (size_t)4*n+1) )
    {
        memset(p->pSelected, 0xFF, sizeof(int)*n);
        if ( p->pEdgeBest ) memset(p->pEdgeSelected, 0xFF, sizeof(int)*2*n);
        if ( fInfinitePath ) ++p->nInfinitePaths;
        else Abc_Print( -1, "LMS2: Cannot allocate the critical-cut graph.\n" );
        p->CutCost = Inf;
        return -1;
    }
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        if ( Gia_ObjIsCo(pObj) )
        {
            a = Gia_ObjFaninId0p(p->pGia, pObj);
            if ( p->pLevels[a] == p->Depth ) Extra_FlowAdd(f, 2*a+1, Sink, Inf);
            continue;
        }
        if ( !Lmo_IsCritical(p, Id) ) continue;
        Delta = p->pBest[Id].n ? Scale*Abc_MaxInt(0, p->pBest[Id].Costs[0])+1 : Inf;
        Extra_FlowAdd(f, 2*Id, 2*Id+1, Delta);
        if ( !Gia_ObjIsAnd(pObj) ) { Extra_FlowAdd(f, Source, 2*Id, Inf); continue; }
        for ( k = 0; k < 2; ++k )
        {
            a = k ? Gia_ObjFaninId1p(p->pGia, pObj) : Gia_ObjFaninId0p(p->pGia, pObj);
            if ( p->pLevels[a]+1 != p->pLevels[Id] ) continue;
            Delta = Inf;
            if ( p->pEdgeBest && p->pEdgeIndex[2*Id+k] < p->pEdgeBest[2*Id+k].n )
                Delta = Scale*Abc_MaxInt(0, p->pEdgeBest[2*Id+k].Costs[p->pEdgeIndex[2*Id+k]])+1;
            Extra_FlowAdd(f, 2*a+1, 2*Id, Delta);
        }
    }
    Flow = Extra_FlowSolveTimed(f, Source, Sink, Inf, p->pCache->Deadline);
    if ( Flow >= Inf ) Count = -1;
    for ( Id = 0; Id < n; ++Id )
    {
        p->pSelected[Id] = -1;
        if ( Count >= 0 && f->pParents[2*Id] != -1 && f->pParents[2*Id+1] == -1 )
        {
            assert(p->pBest[Id].n);
            p->pSelected[Id] = p->pBest[Id].Lits[0];
            ++Count;
        }
        if ( !p->pEdgeBest ) continue;
        for ( k = 0; k < 2; ++k )
        {
            p->pEdgeSelected[2*Id+k] = -1;
            if ( Count < 0 || !Gia_ObjIsAnd(Gia_ManObj(p->pGia, Id)) ||
                 f->pParents[2*Id] != -1 || !Lmo_IsCritical(p, Id) ) continue;
            pObj = Gia_ManObj(p->pGia, Id);
            a = k ? Gia_ObjFaninId1p(p->pGia, pObj) : Gia_ObjFaninId0p(p->pGia, pObj);
            if ( p->pLevels[a]+1 != p->pLevels[Id] || f->pParents[2*a+1] == -1 ) continue;
            assert(p->pEdgeIndex[2*Id+k] < p->pEdgeBest[2*Id+k].n);
            p->pEdgeSelected[2*Id+k] = p->pEdgeBest[2*Id+k].Lits[p->pEdgeIndex[2*Id+k]];
            ++Count;
        }
    }
    p->CutCost = Flow;
    Extra_FlowStop(f);
    return Count;
}

// Keep an append-only ordinary-AIG view for compatibility SAT. Optimizing
// XOR gates never changes the unit-gate timing model used by the search.
/**Function*************************************************************

  Synopsis    [Extend the ordinary-AIG SAT view for a pool literal.]

***********************************************************************/
static int Lmo_SatLit( Lmo_Man_t * p, int Lit )
{
    Gia_Obj_t * pObj;
    int i, a, b, Result;
    if ( !p->fXor ) return Lit;
    if ( !p->pSatGia )
    {
        p->pSatGia = Gia_ManStart(Gia_ManObjNum(p->pPool));
        Gia_ManHashAlloc(p->pSatGia);
        p->vSatMap = Vec_IntStart(1);
    }
    for ( i = Vec_IntSize(p->vSatMap); i < Gia_ManObjNum(p->pPool); ++i )
    {
        pObj = Gia_ManObj(p->pPool, i);
        if ( Gia_ObjIsCi(pObj) ) Result = Gia_ManAppendCi(p->pSatGia);
        else
        {
            a = Gia_ObjFaninLit0p(p->pPool, pObj);
            a = Vec_IntEntry(p->vSatMap, a>>1)^(a&1);
            if ( Gia_ObjIsCo(pObj) ) Result = a;
            else
            {
                b = Gia_ObjFaninLit1p(p->pPool, pObj);
                b = Vec_IntEntry(p->vSatMap, b>>1)^(b&1);
                Result = Gia_ObjIsXor(pObj) ? Gia_ManHashXor(p->pSatGia, a, b) : Gia_ManHashAnd(p->pSatGia, a, b);
            }
        }
        Vec_IntPush(p->vSatMap, Result);
    }
    return Vec_IntEntry(p->vSatMap, Lit>>1)^(Lit&1);
}

// Each edge alone preserves the AND's on-set. Their conjunction can only
// add spurious ones when both original inputs are zero. Prove that it does
// not; an undecided SAT call rejects the pair just like a counterexample.
/**Function*************************************************************

  Synopsis    [Check simultaneous contextual replacements of both AND inputs.]

***********************************************************************/
static int Lmo_Compatible( Lmo_Man_t * p, int Id, int a, int b )
{
    int Assumptions[3], Result;
    if ( Lmo_Expired(p) ) return 0;
    if ( Gia_ObjIsXor(Gia_ManObj(p->pGia, Id)) ) return 1;
    Assumptions[0] = Lmo_SatLit(p, 2*Id+1);
    Assumptions[1] = Lmo_SatLit(p, a);
    Assumptions[2] = Lmo_SatLit(p, b);
    if ( !p->pSolver )
    {
        p->pSolver = Cbs_ManAlloc(p->fXor ? p->pSatGia : p->pPool);
        Cbs_ManSetConflictNum(p->pSolver, 1000);
    }
    ++p->nPairChecks;
    // SolveLits synchronizes appended objects and allocates/grows pRefs
    // before making decisions, for both the pool and the native SAT view.
    Result = Cbs_ManSolveLitsNoModel(p->pSolver, Assumptions, 3) == 1;
    p->nPairRejects += !Result;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Find an incompatible pair in the selected replacement batch.]

***********************************************************************/
static int Lmo_Conflict( Lmo_Man_t * p )
{
    int Id, a, b;
    size_t Index;
    for ( Id = 1; Id < Gia_ManObjNum(p->pGia); ++Id )
    {
        a = p->pEdgeSelected[2*Id]; b = p->pEdgeSelected[2*Id+1];
        if ( a < 0 || b < 0 ) continue;
        Index = ((size_t)Id*p->Alternatives+p->pEdgeIndex[2*Id])*p->Alternatives+p->pEdgeIndex[2*Id+1];
        if ( !p->pPairs[Index] ) p->pPairs[Index] = Lmo_Compatible(p, Id, a, b) ? 1 : 2;
        if ( p->pPairs[Index] == 2 ) return Id;
    }
    return -1;
}

typedef struct Lmo_Search_t_
{
    int * pNodes, * pEdges;
    int Count, Trials;
    word Cost;
} Lmo_Search_t;

// Branch on an incompatible pair by advancing one or the other edge's
// candidate. Each branch excludes at least that pair and has a valid
// min-cut lower bound. A bounded search retains its best feasible cut.
/**Function*************************************************************

  Synopsis    [Branch on incompatible edge pairs within the search budget.]

***********************************************************************/
static void Lmo_SelectSearch( Lmo_Man_t * p, Lmo_Search_t * s )
{
    int Count, Conflict, k, n = Gia_ManObjNum(p->pGia);
    if ( Lmo_Expired(p) ) return;
    if ( !s->Trials-- ) { s->Trials = 0; return; }
    ++p->nCutTrials;
    Count = Lmo_Select(p);
    if ( Count < 0 || p->CutCost >= s->Cost ) return;
    Conflict = Lmo_Conflict(p);
    if ( Lmo_Expired(p) ) return;
    if ( Conflict < 0 )
    {
        s->Cost = p->CutCost; s->Count = Count;
        memcpy(s->pNodes, p->pSelected, sizeof(int)*n);
        memcpy(s->pEdges, p->pEdgeSelected, sizeof(int)*2*n);
        return;
    }
    for ( k = 0; k < 2 && s->Trials; ++k )
    {
        ++p->pEdgeIndex[2*Conflict+k];
        Lmo_SelectSearch(p, s);
        --p->pEdgeIndex[2*Conflict+k];
    }
}

/**Function*************************************************************

  Synopsis    [Select a compatible weighted critical-path cut.]

***********************************************************************/
static int Lmo_SelectEdges( Lmo_Man_t * p )
{
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_CUT);
    Lmo_Search_t Search, * s = &Search;
    int i, n = Gia_ManObjNum(p->pGia);
    memset(s, 0, sizeof(*s));
    s->pNodes = ABC_ALLOC(int, n); s->pEdges = ABC_ALLOC(int, 2*n);
    s->Cost = ABC_CONST(0x4000000000000000); s->Count = -1; s->Trials = 1;
    // Keep the ordinary vertex-only cut as a feasible fallback, even when
    // the bounded compatibility search cannot resolve all edge conflicts.
    for ( i = 0; i < 2*n; ++i ) p->pEdgeIndex[i] = p->pEdgeBest[i].n;
    Lmo_SelectSearch(p, s);
    memset(p->pEdgeIndex, 0, sizeof(int)*2*n);
    memset(p->pPairs, 0, (size_t)n*p->Alternatives*p->Alternatives);
    s->Trials = 64;
    Lmo_SelectSearch(p, s);
    if ( s->Count >= 0 )
    {
        memcpy(p->pSelected, s->pNodes, sizeof(int)*n);
        memcpy(p->pEdgeSelected, s->pEdges, sizeof(int)*2*n);
    }
    ABC_FREE(s->pNodes); ABC_FREE(s->pEdges);
    Lmo_TimeSwitch(p, TimePrevious);
    return s->Count;
}

/**Function*************************************************************

  Synopsis    [Rebuild the chosen batch with structural hashing.]

  Description [Replacement dependencies always have smaller input levels.
  A stack handles both pool edges and substitutions without recursion.
  The input is untouched, so a failed batch can be discarded atomically.]

***********************************************************************/
static Gia_Man_t * Lmo_Build( Lmo_Man_t * p )
{
    int TimePrevious = Lmo_TimeSwitch(p, LMO_TIME_BUILD);
    Gia_Man_t * pNew = Gia_ManStart(Gia_ManObjNum(p->pGia)), * pClean;
    Gia_Obj_t * pObj;
    int * pMap = ABC_ALLOC(int, Gia_ManObjNum(p->pPool));
    int n = Gia_ManObjNum(p->pGia), i, Id, a, b, Choice;
    for ( i = 0; i < Gia_ManObjNum(p->pPool); ++i ) pMap[i] = -1;
    pMap[0] = 0;
    if ( p->fXor ) pNew->pMuxes = ABC_CALLOC(unsigned, pNew->nObjsAlloc);
    Gia_ManHashAlloc(pNew);
    Gia_ManForEachCi(p->pGia, pObj, i) pMap[Gia_ObjId(p->pGia, pObj)] = Gia_ManAppendCi(pNew);
    Gia_ManForEachCo(p->pGia, pObj, i)
    {
        int Driver = Gia_ObjFaninId0p(p->pGia, pObj), Compl = Gia_ObjFaninC0(pObj);
        Vec_IntClear(p->vStack); Vec_IntPush(p->vStack, Driver);
        while ( Vec_IntSize(p->vStack) )
        {
            Id = Vec_IntEntryLast(p->vStack);
            if ( pMap[Id] >= 0 ) { Vec_IntPop(p->vStack); continue; }
            Choice = Id < n ? p->pSelected[Id] : -1;
            if ( Choice >= 0 )
            {
                a = Choice>>1;
                if ( pMap[a] < 0 ) { Vec_IntPush(p->vStack, a); continue; }
                pMap[Id] = pMap[a]^(Choice&1);
            }
            else
            {
                pObj = Gia_ManObj(p->pPool, Id);
                assert(Gia_ObjIsAnd(pObj));
                a = Gia_ObjFaninLit0p(p->pPool, pObj); b = Gia_ObjFaninLit1p(p->pPool, pObj);
                if ( Id < n && p->pEdgeSelected )
                {
                    if ( p->pEdgeSelected[2*Id] >= 0 ) a = p->pEdgeSelected[2*Id];
                    if ( p->pEdgeSelected[2*Id+1] >= 0 ) b = p->pEdgeSelected[2*Id+1];
                }
                if ( pMap[a>>1] < 0 ) { Vec_IntPush(p->vStack, a>>1); continue; }
                if ( pMap[b>>1] < 0 ) { Vec_IntPush(p->vStack, b>>1); continue; }
                pMap[Id] = Gia_ObjIsXor(pObj) ? Gia_ManHashXorReal(pNew, pMap[a>>1]^(a&1), pMap[b>>1]^(b&1))
                    : Gia_ManHashAnd(pNew, pMap[a>>1]^(a&1), pMap[b>>1]^(b&1));
            }
            Vec_IntPop(p->vStack);
        }
        Gia_ManAppendCo(pNew, pMap[Driver]^Compl);
    }
    Gia_ManHashStop(pNew);
    pClean = Gia_ManCleanup(pNew);
    Gia_ManStop(pNew);
    pClean->pName = Abc_UtilStrsav(p->pGia->pName);
    pClean->pSpec = Abc_UtilStrsav(p->pGia->pSpec);
    ABC_FREE(pMap);
    Lmo_TimeSwitch(p, TimePrevious);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Try retained alternatives to reduce the rebuilt batch area.]

***********************************************************************/
static Gia_Man_t * Lmo_Refine( Lmo_Man_t * p, Gia_Man_t * pBest, int Trials )
{
    Gia_Man_t * pTrial;
    int i, k, Saved, Count = 0, n = Gia_ManObjNum(p->pGia);
    // Try different structures at selected roots, then optional local area
    // reductions. Actual rebuilt AND count accounts for interacting MFFCs.
    for ( i = n-1; i > 0 && Count < Trials; --i )
    {
        if ( !p->pBest[i].n || (p->pSelected[i] < 0 && p->pBest[i].Costs[0] >= 0) ) continue;
        for ( k = 0; k < p->pBest[i].n && Count < Trials; ++k )
        {
            Saved = p->pSelected[i];
            if ( Saved == p->pBest[i].Lits[k] ) continue;
            if ( Lmo_Expired(p) ) return pBest;
            p->pSelected[i] = p->pBest[i].Lits[k];
            pTrial = Lmo_Build(p); ++Count;
            if ( Gia_ManAndNum(pTrial) < Gia_ManAndNum(pBest) && Lms_LevelNum(pTrial, p->fXor) < p->Depth )
            { Gia_ManStop(pBest); pBest = pTrial; }
            else { Gia_ManStop(pTrial); p->pSelected[i] = Saved; }
        }
    }
    for ( i = 2*n-1; i > 1 && Count < Trials; --i )
    {
        if ( p->pSelected[i/2] >= 0 || !p->pEdgeBest[i].n ||
             (p->pEdgeSelected[i] < 0 && p->pEdgeBest[i].Costs[0] >= 0) ) continue;
        for ( k = 0; k < p->pEdgeBest[i].n && Count < Trials; ++k )
        {
            int Lit = p->pEdgeBest[i].Lits[k], Other = p->pEdgeSelected[i^1];
            Saved = p->pEdgeSelected[i];
            if ( Lmo_Expired(p) ) return pBest;
            if ( Saved == Lit || (Other >= 0 && !Lmo_Compatible(p, i/2, Lit, Other)) ) continue;
            p->pEdgeSelected[i] = Lit;
            pTrial = Lmo_Build(p); ++Count;
            if ( Gia_ManAndNum(pTrial) < Gia_ManAndNum(pBest) && Lms_LevelNum(pTrial, p->fXor) < p->Depth )
            { Gia_ManStop(pBest); pBest = pTrial; }
            else { Gia_ManStop(pTrial); p->pEdgeSelected[i] = Saved; }
        }
    }
    return pBest;
}

// Use the same recovery before the first pass and after accepted batches.
// In native mode, check the reconstructed XAG's area and unit-gate depth.
/**Function*************************************************************

  Synopsis    [Run resubstitution without increasing gate count or depth.]

***********************************************************************/
static Gia_Man_t * Lmo_RecoverArea( Gia_Man_t * pResult, int CutSize, int Nodes, int fXor, abctime Deadline )
{
    Gia_Man_t * pRecovered, * pAig = NULL;
    if ( Deadline && Abc_ClockHr() >= Deadline ) return pResult;
    // Recover area outside the critical graph under the achieved depth.
    if ( fXor && (pResult->pMuxes || Gia_ManXorNum(pResult)) ) pAig = Gia_ManDupNoMuxes(pResult, 0);
    pRecovered = Rsub_ManPerformTimed(pAig ? pAig : pResult, CutSize, Abc_MinInt(Nodes, 3), 1, 1, 0, 0, Deadline);
    if ( pAig ) Gia_ManStop(pAig);
    if ( pRecovered && fXor )
    {
        pAig = pRecovered;
        pRecovered = Gia_ManDupMuxes(pAig, 0);
        Gia_ManStop(pAig);
    }
    if ( pRecovered && Gia_ManAndNum(pRecovered) <= Gia_ManAndNum(pResult) &&
         Lms_LevelNum(pRecovered, fXor) <= Lms_LevelNum(pResult, fXor) )
    { Gia_ManStop(pResult); pResult = pRecovered; }
    else if ( pRecovered ) Gia_ManStop(pRecovered);
    return pResult;
}

// Iterate only while area or depth strictly improves. Discard a no-gain
// sweep, including equal-cost restructuring, so repeating recovery cannot
// cycle and an unchanged graph can keep its existing candidate bank.
/**Function*************************************************************

  Synopsis    [Repeat level-preserving area recovery until no gain remains.]

***********************************************************************/
static Gia_Man_t * Lmo_RecoverFinal( Gia_Man_t * pResult, int CutSize, int Nodes, int fXor, int fVerbose, const char * pStage, abctime Deadline )
{
    int InitialNodes = Gia_ManAndNum(pResult);
    int InitialDepth = Lms_LevelNum(pResult, fXor);
    int Depth = InitialDepth, NextDepth, Sweeps = 0;
    abctime Start = Abc_Clock();
    for ( ;; )
    {
        Gia_Man_t * pTrial = Lmo_RecoverArea(Gia_ManDup(pResult), CutSize, Nodes, fXor, Deadline);
        ++Sweeps;
        NextDepth = Lms_LevelNum(pTrial, fXor);
        if ( Gia_ManAndNum(pTrial) >= Gia_ManAndNum(pResult) && NextDepth >= Depth )
        { Gia_ManStop(pTrial); break; }
        Gia_ManStop(pResult);
        pResult = pTrial;
        Depth = NextDepth;
    }
    if ( fVerbose )
        Abc_Print(1, "LMS2 %s recovery: %d -> %d gates; level %d -> %d; %d sweeps; time %.3f s.\n",
            pStage, InitialNodes, Gia_ManAndNum(pResult), InitialDepth, Depth, Sweeps, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Refine and recover area on a feasible replacement batch.]

***********************************************************************/
static Gia_Man_t * Lmo_ImproveBatch( Lmo_Man_t * p, Gia_Man_t * pResult, int Trials )
{
    int Previous;
    pResult = Lmo_Refine(p, pResult, Trials);
    Previous = Lmo_TimeSwitch(p, LMO_TIME_RECOVER);
    pResult = Lmo_RecoverArea(pResult, p->CutSize, p->Nodes, p->fXor, p->pCache->Deadline);
    Lmo_TimeSwitch(p, Previous);
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Include the fanin helper cones of the current focus.]

***********************************************************************/
static int Lmo_FocusClose( Lmo_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, Count = 0;
    for ( i = Gia_ManObjNum(p->pGia)-1; i > 0; --i )
    {
        pObj = Gia_ManObj(p->pGia, i);
        if ( !p->pFocus[i] || !Gia_ObjIsAnd(pObj) ) continue;
        ++Count;
        p->pFocus[Gia_ObjFaninId0p(p->pGia, pObj)] = 1;
        p->pFocus[Gia_ObjFaninId1p(p->pGia, pObj)] = 1;
    }
    return Count;
}

// Expand one zero-slack neighborhood of the selected cut, then include all
// fanin helpers. Seed separately so a forward scan cannot turn one hop into
// the entire transitive fanout. Edge replacements seed both endpoints.
/**Function*************************************************************

  Synopsis    [Expand the focus around the selected critical-path cut.]

***********************************************************************/
static int Lmo_FocusCut( Lmo_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, k, Fan, n = Gia_ManObjNum(p->pGia);
    unsigned char * pSeeds = ABC_CALLOC(unsigned char, n);
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        if ( !Lmo_IsCritical(p, i) ) continue;
        if ( p->pSelected[i] >= 0 ) pSeeds[i] = 1;
        for ( k = 0; k < 2; ++k )
            if ( p->pEdgeSelected[2*i+k] >= 0 )
            {
                pSeeds[i] = 1;
                pSeeds[k ? Gia_ObjFaninId1p(p->pGia, pObj) : Gia_ObjFaninId0p(p->pGia, pObj)] = 1;
            }
    }
    for ( i = 1; i < n; ++i )
    {
        if ( !pSeeds[i] ) continue;
        p->pFocus[i] = 1;
        pObj = Gia_ManObj(p->pGia, i);
        if ( Gia_ObjIsAnd(pObj) )
            for ( k = 0; k < 2; ++k )
            {
                Fan = k ? Gia_ObjFaninId1p(p->pGia, pObj) : Gia_ObjFaninId0p(p->pGia, pObj);
                if ( Lmo_IsCritical(p, Fan) && p->pLevels[Fan]+1 == p->pLevels[i] ) p->pFocus[Fan] = 1;
            }
        Vec_IntForEachEntry(Vec_WecEntry(p->vFanouts, i), Fan, k)
            if ( Lmo_IsCritical(p, Fan) && p->pLevels[i]+1 == p->pLevels[Fan] ) p->pFocus[Fan] = 1;
    }
    ABC_FREE(pSeeds);
    return Lmo_FocusClose(p);
}

// Retain the global bank and first widen uncovered paths. Once feasible,
// price alternatives around the selected cut while actual batch area falls.
/**Function*************************************************************

  Synopsis    [Widen uncovered roots and selected cut neighborhoods.]

***********************************************************************/
static Gia_Man_t * Lmo_Escalate( Lmo_Man_t * p, int Trials, int fVerbose, int * pnCount )
{
    Gia_Man_t * pBest = NULL, * pTrial;
    int i, Stage, Count, Focus, NextFocus, Round = 0, AreaBefore, * pSelection, n = Gia_ManObjNum(p->pGia);
    int CutSize = Abc_MaxInt(p->CutSize, 12), Cuts = Abc_MaxInt(p->Cuts, 128);
    abctime Start = Abc_Clock();
    if ( CutSize == p->CutSize && Cuts == p->Cuts ) return NULL;
    Lmo_Uncovered(p);
    if ( !p->nUncovered ) return NULL;
    p->pFocus = ABC_CALLOC(unsigned char, n);
    for ( i = 0; i < n; ++i ) p->pFocus[i] = p->pNeeded[i] != 0;
    Focus = Lmo_FocusClose(p);
    if ( fVerbose )
        Abc_Print(1, "LMS2 escalation: %d uncovered of %d critical gates, %d gates with fanin helpers; K %d -> %d, C %d -> %d.\n",
            p->nUncovered, p->nCritical, Focus, p->CutSize, CutSize, p->Cuts, Cuts);
    p->CutSize = CutSize; p->Cuts = Cuts;
    p->nWordsMax = Abc_Truth6WordNum(CutSize);
    p->pTruths = ABC_REALLOC(word, p->pTruths, (p->Window+2)*p->nWordsMax);
    p->pValues = ABC_REALLOC(word, p->pValues, (p->Divs+p->Nodes+2)*p->nWordsMax);
    p->pOff = ABC_REALLOC(word, p->pOff, p->nWordsMax);
    p->pOn = ABC_REALLOC(word, p->pOn, p->nWordsMax);
    pSelection = ABC_ALLOC(int, 3*n);
    p->fCompose = 1; p->fUncovered = 0;
    Abc_ResubPrepareManager(p->nWordsMax);
    for ( ;; )
    {
        AreaBefore = pBest ? Gia_ManAndNum(pBest) : INT_MAX;
        // Candidates and their graph IDs survive; recollect only the cut bank.
        Lmo_ClearMerged(p);
        for ( Stage = 0; Stage < 2; ++Stage )
        {
            p->fTargetOnly = !Stage;
            p->MappedRoot = 0;
            Lmo_CollectMerged(p);
            Lmo_Collect(p, 0);
            Lmo_Collect(p, 1);
            Lmo_CostReset(p);
            Count = Lmo_SelectEdges(p);
            if ( Count < 0 ) continue;
            pTrial = Lmo_Build(p);
            if ( Lms_LevelNum(pTrial, p->fXor) >= p->Depth ) { Gia_ManStop(pTrial); continue; }
            pTrial = Lmo_ImproveBatch(p, pTrial, Trials);
            if ( !pBest || Gia_ManAndNum(pTrial) < Gia_ManAndNum(pBest) ||
                 (Gia_ManAndNum(pTrial) == Gia_ManAndNum(pBest) && Lms_LevelNum(pTrial, p->fXor) < Lms_LevelNum(pBest, p->fXor)) )
            {
                if ( pBest ) Gia_ManStop(pBest);
                pBest = pTrial; *pnCount = Count;
                memcpy(pSelection, p->pSelected, sizeof(int)*n);
                memcpy(pSelection+n, p->pEdgeSelected, sizeof(int)*2*n);
            }
            else Gia_ManStop(pTrial);
            if ( Gia_ManAndNum(pBest) <= Gia_ManAndNum(p->pGia) ) break;
        }
        if ( fVerbose && Round && pBest )
            Abc_Print(1, "LMS2 escalation repricing %d: %d -> %d gates.\n", Round, AreaBefore, Gia_ManAndNum(pBest));
        if ( !pBest || Gia_ManAndNum(pBest) >= AreaBefore ) break;
        memcpy(p->pSelected, pSelection, sizeof(int)*n);
        memcpy(p->pEdgeSelected, pSelection+n, sizeof(int)*2*n);
        NextFocus = Lmo_FocusCut(p);
        if ( NextFocus == Focus ) break;
        ++Round;
        if ( fVerbose )
            Abc_Print(1, "LMS2 escalation neighborhood %d: %d -> %d focused gates.\n", Round, Focus, NextFocus);
        Focus = NextFocus;
    }
    ABC_FREE(pSelection);
    Abc_ResubPrepareManager(0);
    if ( fVerbose )
        Abc_Print(1, "LMS2 escalation result: %s; %d gates, level %d; time %.3f s.\n",
            pBest ? "improved" : "no improvement", Gia_ManAndNum(pBest ? pBest : p->pGia),
            pBest ? Lms_LevelNum(pBest, p->fXor) : p->Depth, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    return pBest;
}

// Compare actual recovered gates, with both native gate types counted once.
/**Function*************************************************************

  Synopsis    [Test the recovered per-pass percentage growth limit.]

***********************************************************************/
static int Lmo_OverBudget( Gia_Man_t * pGia, Gia_Man_t * pTrial, double Percent )
{
    return Percent >= 0.0 && 100.0*(Gia_ManAndNum(pTrial)-Gia_ManAndNum(pGia)) > Percent*Gia_ManAndNum(pGia);
}

/**Function*************************************************************

  Synopsis    [Search progressively stronger candidate banks for one lower level.]

***********************************************************************/
static Gia_Man_t * Lmo_OneSearch( Gia_Man_t * pGia, int CutSize, int Cuts, int Nodes, int Trials,
    double AreaGrowth, int fFullHelpers, int fXor, int fEscalate, int fVerbose, Lmo_Cache_t * pCache, int * pfRecovered )
{
    Lmo_Man_t Man, * p = &Man;
    Gia_Man_t * pResult = NULL;
    Gia_Obj_t * pObj;
    int i, n = Gia_ManObjNum(pGia), Count = -1, Round, BestCount = -1;
    abctime Start = Abc_Clock();
    assert(pCache && !pGia->nRegs && !pGia->pCexSeq && !pGia->vCiArrs);
    memset(p, 0, sizeof(*p));
    p->fProfile = fVerbose; p->TimeLast = Start;
    p->pGia = pGia; p->Cuts = Cuts; p->Nodes = Nodes;
    p->fXor = fXor; p->pCache = pCache; p->fFullHelpers = fFullHelpers;
    p->CutSize = CutSize; p->Divs = LMO_DIVS; p->Choices = 4; p->Alternatives = 4;
    p->Window = LMO_WINDOW; p->nWords = p->nWordsMax = Abc_Truth6WordNum(CutSize);
    Lmo_Timing(p);
    // &ps includes dangling gates in its maximum level. Removing such a
    // deepest dangling cone already meets this invocation's one-level goal.
    if ( p->InputDepth > p->Depth )
    {
        pResult = Gia_ManCleanup(pGia);
        goto cleanup;
    }
    if ( !p->Depth ) goto cleanup;
    p->pVersions = ABC_CALLOC(word, n);
    if ( pCache->nBins )
    {
        p->nCandidateBins = 32768;
        while ( p->nCandidateBins < (1<<20) && (size_t)p->nCandidateBins < (size_t)p->nCritical*Cuts*8 ) p->nCandidateBins <<= 1;
        p->pCandidateBins = ABC_CALLOC(word, p->nCandidateBins);
    }
    p->nCutBins = pCache->nBins ? 1024 : 0;
    while ( p->nCutBins && p->nCutBins < (1<<20) && (size_t)p->nCutBins < (size_t)p->nCritical*Cuts*2 ) p->nCutBins <<= 1;
    p->pCutBins = ABC_CALLOC(Lmo_CutMemo_t *, p->nCutBins);
    p->pPool = Gia_ManDup(pGia);
    if ( fXor && !p->pPool->pMuxes ) p->pPool->pMuxes = ABC_CALLOC(unsigned, p->pPool->nObjsAlloc);
    Gia_ManHashStart(p->pPool);
    p->pBest = ABC_CALLOC(Lmo_Best_t, n);
    p->pFastLits = ABC_ALLOC(int, n);
    p->pFastCosts = ABC_CALLOC(int, n);
    p->pEarlyLits = ABC_ALLOC(int, (size_t)n*LMO_EARLY);
    p->pEarlyCosts = ABC_ALLOC(int, (size_t)n*LMO_EARLY);
    memset(p->pEarlyLits, 0xFF, sizeof(int)*(size_t)n*LMO_EARLY);
    for ( i = 0; i < n; ++i ) p->pFastLits[i] = 2*i;
    p->pEdgeBest = ABC_CALLOC(Lmo_Best_t, 2*n);
    p->pEdgeSelected = ABC_ALLOC(int, 2*n);
    p->pEdgeIndex = ABC_CALLOC(int, 2*n);
    p->pPairs = ABC_CALLOC(unsigned char, (size_t)n*p->Alternatives*p->Alternatives);
    p->pSeen = ABC_CALLOC(int, n);
    p->pTruthIds = ABC_ALLOC(int, n);
    p->pTruths = ABC_ALLOC(word, (p->Window+2)*p->nWords);
    p->pValues = ABC_ALLOC(word, (p->Divs+Nodes+2)*p->nWords);
    p->pOff = ABC_ALLOC(word, p->nWords);
    p->pOn = ABC_ALLOC(word, p->nWords);
    p->pDivs = ABC_ALLOC(void *, p->Divs+2);
    p->pLits = ABC_ALLOC(int, p->Divs+Nodes+2);
    p->pTimes = ABC_ALLOC(int, p->Divs+Nodes+2);
    p->pSelected = ABC_ALLOC(int, n);
    p->pNeeded = ABC_CALLOC(int, n);
    p->vPoolLevels = Vec_IntStart(n);
    memcpy(Vec_IntArray(p->vPoolLevels), p->pLevels, sizeof(int)*n);
    p->vRefs = Vec_IntStart(n);
    p->vStack = Vec_IntAlloc(256);
    p->vWindow = Vec_IntAlloc(p->Window);
    p->vFanouts = Vec_WecStart(n);
    p->vRecipes = Vec_WecAlloc(4);
    p->vPrograms = pCache->vPrograms;
    p->vOffsets = pCache->vOffsets;
    Gia_ManForEachObj(pGia, pObj, i)
    {
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) ) Vec_IntAddToEntry(p->vRefs, Gia_ObjFaninId0p(pGia, pObj), 1);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        Vec_IntAddToEntry(p->vRefs, Gia_ObjFaninId1p(pGia, pObj), 1);
        Vec_WecPush(p->vFanouts, Gia_ObjFaninId0p(pGia, pObj), i);
        Vec_WecPush(p->vFanouts, Gia_ObjFaninId1p(pGia, pObj), i);
    }
    if ( p->Nodes && !Abc_NtkRecIsRunning3() ) Abc_NtkRecStartBuiltin3(stdout, stderr);
    if ( p->Nodes && (fXor ? Abc_RecTargetXorReady3() : Abc_RecTargetReady3()) )
    {
        if ( !pCache->fLibrary ) Abc_RecTargetCache3(1);
        Abc_RecTargetData3(&p->pLibAreas, &p->pLibDelays);
        pCache->fLibrary = 1;
        Lmo_FocusBank(p);
    }
    Abc_ResubPrepareManager(p->nWordsMax);
    Lmo_CollectMerged(p);
    // Keep the cheapest fully recovered feasible batch while adding alternatives.
    // A first feasible cut can be expensive even when it was cheap to find.
    for ( Round = 0; Round < 6 && !Lmo_Expired(p); ++Round )
    {
        Gia_Man_t * pTrial;
        if ( fVerbose && (Round == 2 || Round == 4) )
        {
            Lmo_Uncovered(p);
            Abc_Print(1, "LMS2 uncovered before %s composition: %d/%d critical gates, %d gates in their fanin cones.\n",
                Round == 2 ? "modest" : "aggressive", p->nUncovered, p->nCritical, p->nUncoveredCone);
        }
        if ( Round == 2 )
        {
            if ( p->pBankCone )
            {
                if ( fVerbose ) Abc_Print(1, "LMS2: collecting the full bank for composition.\n");
                ABC_FREE(p->pBankCone);
                Lmo_ClearMerged(p);
            }
            p->fCompose = 1;
            p->fTargetOnly = 1;
            Lmo_CollectMerged(p);
        }
        if ( Round == 4 )
        {
            p->fTargetOnly = 0;
            Lmo_CollectMerged(p);
        }
        // Feasibility needs only uncovered paths. Area alternatives can lie
        // anywhere on the cut, so visit every critical root once feasible.
        p->fUncovered = Round >= 4 && !pResult;
        if ( p->fUncovered ) Lmo_Uncovered(p);
        Lmo_Collect(p, Round & 1);
        if ( Lmo_Expired(p) ) break;
        if ( Round == 0 || Round == 2 ) continue;
        Lmo_CostReset(p);
        Count = Lmo_SelectEdges(p);
        if ( Count < 0 ) continue;
        pTrial = Lmo_Build(p);
        if ( Lms_LevelNum(pTrial, p->fXor) >= p->Depth )
        {
            if ( fVerbose ) Abc_Print(1, "LMS2: selected batch missed the depth target; trying remaining alternatives.\n");
            Gia_ManStop(pTrial);
            continue;
        }
        pTrial = Lmo_ImproveBatch(p, pTrial, Trials);
        if ( !pResult || Gia_ManAndNum(pTrial) < Gia_ManAndNum(pResult) ||
             (Gia_ManAndNum(pTrial) == Gia_ManAndNum(pResult) && Lms_LevelNum(pTrial, p->fXor) < Lms_LevelNum(pResult, p->fXor)) )
        {
            if ( pResult ) Gia_ManStop(pResult);
            pResult = pTrial; BestCount = Count;
        }
        else Gia_ManStop(pTrial);
        if ( fVerbose )
            Abc_Print(1, "LMS2 %s batch: best %d gates, level %d.\n",
                Round == 1 ? "original" : Round == 3 ? "modest" : "aggressive", Gia_ManAndNum(pResult), Lms_LevelNum(pResult, p->fXor));
        // Stop pricing once the best recovered batch grows by at most 1%
        // and fits -A. Over-budget batches still price the remaining banks.
        if ( !Lmo_OverBudget(pGia, pResult, 1.0) && !Lmo_OverBudget(pGia, pResult, AreaGrowth) ) break;
    }
    Abc_ResubPrepareManager(0);
    Count = BestCount;
    if ( !pResult && !Lmo_Expired(p) && fEscalate && pfRecovered )
    {
        int Previous = Lmo_TimeSwitch(p, LMO_TIME_RECOVER);
        Gia_Man_t * pRecovered = Lmo_RecoverFinal(Gia_ManDup(pGia), CutSize, Nodes, fXor, fVerbose, "before escalation", pCache->Deadline);
        Lmo_TimeSwitch(p, Previous);
        if ( Gia_ManAndNum(pRecovered) < Gia_ManAndNum(pGia) || Lms_LevelNum(pRecovered, p->fXor) < p->Depth )
        {
            // Graph-dependent windows and candidates refer to the old IDs.
            // Return the recovered graph and rebuild them before escalating.
            pResult = pRecovered;
            *pfRecovered = 1;
        }
        else Gia_ManStop(pRecovered);
    }
    if ( !pResult && !Lmo_Expired(p) && fEscalate ) pResult = Lmo_Escalate(p, Trials, fVerbose, &Count);
    if ( fVerbose )
    {
        Abc_Print(1, "LMS2 budgets: cut size %d (delay and recovery), %d cuts/root, %d divisors, %d resub choices, %d alternatives/root.\n",
            p->CutSize, p->Cuts, p->Divs, p->Choices, p->Alternatives);
        Abc_Print(1, "LMS2 search: %d critical gates, %d zero-slack edges; %d cuts; %d improving roots, %d resub and %d library candidates; %d cut replacements.\n",
            p->nCritical, p->nEdges, p->nCuts, p->nRoots, p->nResub, p->nLibrary, Abc_MaxInt(0, Count));
        Abc_Print(1, "LMS2 reuse: %d duplicate windows, %d unchanged resub problems, %d unchanged library lookups skipped.\n",
            p->nWindowSkips, p->nResubSkips, p->nLibrarySkips);
        Abc_Print(1, "LMS2 replay: %d unchanged bank entries, %d previously costed candidates skipped.\n",
            p->nReplaySkips, p->nCandidateSkips);
        Abc_Print(1, "LMS2 library builds: frontier %llu, mapped frontier %llu, bank %llu.\n",
            (unsigned long long)p->Builds[0], (unsigned long long)p->Builds[1], (unsigned long long)p->Builds[2]);
        Abc_Print(1, "LMS2 duplicate costs: resub %llu, library %llu.\n",
            (unsigned long long)p->DuplicateOrigins[0], (unsigned long long)p->DuplicateOrigins[1]);
        Abc_Print(1, "LMS2 bounded costing: %llu walks, %llu early rejections.\n",
            (unsigned long long)p->CostBounded, (unsigned long long)p->CostAborts);
        Abc_Print(1, "LMS2 pool: %d input gates, %d pool gates (%.2fx); %d objects allocated, %.2f MiB graph storage.\n",
            Gia_ManAndNum(pGia), Gia_ManAndNum(p->pPool),
            Gia_ManAndNum(p->pPool)/(double)Abc_MaxInt(1, Gia_ManAndNum(pGia)),
            p->pPool->nObjsAlloc, Gia_ManMemory(p->pPool)/(1024.0*1024.0));
        Abc_Print(1, "LMS2 cut memo: %d entries, %d chains, %.2f MiB entries; %d uncached overflow trials.\n",
            p->nCutMemos, p->nCutBins, p->pCutMem ? Mem_FlexReadMemUsage(p->pCutMem)/(1024.0*1024.0) : 0.0, p->nCutOverflows);
        Abc_Print(1, "LMS2 edges: %d improving edges, %d candidates; %d cut solves, %d compatibility checks (%d rejected/undecided).\n",
            p->nEdgeRoots, p->nEdgeCandidates, p->nCutTrials, p->nPairChecks, p->nPairRejects);
        Abc_Print(1, "LMS2 cut feasibility: %d solves rejected by an infinite-edge path.\n", p->nInfinitePaths);
        Abc_Print(1, "LMS2 cut sizes:");
        for ( i = 0; i <= p->CutSize; ++i ) if ( p->CutCounts[i] ) Abc_Print(1, " %d:%d", i, p->CutCounts[i]);
        Abc_Print(1, "\n");
    }
cleanup:
    if ( !pResult )
    {
        pResult = Gia_ManDup(pGia);
        Abc_Print(1, "LMS2: no one-level reduction found in the bounded search; logic unchanged.\n");
    }
    Abc_Print(1, "LMS2 step: %d -> %d %s; level %d -> %d (target %d); time %.3f s.\n",
        Gia_ManAndNum(pGia), Gia_ManAndNum(pResult), fXor ? "AND/XOR gates" : "ANDs", p->InputDepth, Lms_LevelNum(pResult, p->fXor),
        Abc_MaxInt(0, p->InputDepth-1), (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( p->pSolver ) Cbs_ManStop(p->pSolver);
    if ( p->pSatGia ) Gia_ManStop(p->pSatGia);
    if ( p->pPool ) Gia_ManStop(p->pPool);
    if ( p->pBest )
        for ( i = 0; i < n; ++i ) { ABC_FREE(p->pBest[i].Lits); ABC_FREE(p->pBest[i].Costs); }
    if ( p->pEdgeBest )
        for ( i = 0; i < 2*n; ++i ) { ABC_FREE(p->pEdgeBest[i].Lits); ABC_FREE(p->pEdgeBest[i].Costs); }
    ABC_FREE(p->pEdgeBest); ABC_FREE(p->pEdgeSelected); ABC_FREE(p->pEdgeIndex); ABC_FREE(p->pPairs);
    ABC_FREE(p->pFastLits); ABC_FREE(p->pFastCosts);
    ABC_FREE(p->pEarlyLits); ABC_FREE(p->pEarlyCosts);
    ABC_FREE(p->pLevels); ABC_FREE(p->pReverse); ABC_FREE(p->pBest);
    ABC_FREE(p->pSeen); ABC_FREE(p->pTruths); ABC_FREE(p->pSelected); ABC_FREE(p->pNeeded);
    ABC_FREE(p->pFocus); ABC_FREE(p->pBankCone);
    ABC_FREE(p->pTruthIds); ABC_FREE(p->pValues); ABC_FREE(p->pOff); ABC_FREE(p->pOn);
    ABC_FREE(p->pDivs); ABC_FREE(p->pLits); ABC_FREE(p->pTimes);
    Vec_IntFreeP(&p->vPoolLevels); Vec_IntFreeP(&p->vRefs);
    Vec_IntFreeP(&p->vStack); Vec_IntFreeP(&p->vWindow);
    Vec_IntFreeP(&p->vCostUndo);
    Mem_FlexStop(p->pCutMem, 0);
    ABC_FREE(p->pCutBins); ABC_FREE(p->pVersions);
    ABC_FREE(p->pCandidateBins); ABC_FREE(p->pMergedVersions);
    Vec_IntFreeP(&p->vSatMap); Vec_IntFreeP(&p->vMerged); Vec_WrdFreeP(&p->vMergedTruths);
    if ( p->vFanouts ) Vec_WecFree(p->vFanouts);
    if ( p->vRecipes ) Vec_WecFree(p->vRecipes);
    if ( fVerbose )
    {
        static const char * const Names[LMO_TIME_NUM] = {"other", "bank", "windows", "resub", "library_scan",
            "replay", "costing", "cut", "rebuild", "recovery", "library_match", "library_build"};
        Lmo_TimeSwitch(p, LMO_TIME_OTHER);
        Abc_Print(1, "LMS2 exclusive times:");
        for ( i = 0; i < LMO_TIME_NUM; ++i )
            Abc_Print(1, " %s=%.6f", Names[i], (double)p->Times[i]/CLOCKS_PER_SEC);
        Abc_Print(1, " s.\n");
    }
    return pResult;
}

// Reprice a feasible over-budget pass on the same incoming graph. A full
// helper bank changes retained cuts, so use a fresh candidate pool while
// reusing graph-independent resub recipes. A search miss ends the iteration.
/**Function*************************************************************

  Synopsis    [Retry a feasible over-budget pass with full helper budgets.]

***********************************************************************/
static Gia_Man_t * Lmo_OnePerform( Gia_Man_t * pGia, int CutSize, int Cuts, int Nodes, int Trials,
    double AreaGrowth, int fXor, int fEscalate, int fVerbose, Lmo_Cache_t * pCache, int * pfRecovered )
{
    Gia_Man_t * pBest = Lmo_OneSearch(pGia, CutSize, Cuts, Nodes, Trials, AreaGrowth, 0, fXor, fEscalate, fVerbose, pCache, pfRecovered);
    Gia_Man_t * pRetry;
    int Depth = Lms_LevelNum(pGia, fXor);
    int BestDepth = Lms_LevelNum(pBest, fXor), RetryDepth;
    if ( Cuts <= 8 || !pCache->fLibrary || BestDepth >= Depth || !Lmo_OverBudget(pGia, pBest, AreaGrowth) ) return pBest;
    Abc_Print(1, "LMS2: retrying level %d with %d helper cuts after exceeding the area limit.\n", Depth, Abc_MinInt(Cuts, 128));
    pRetry = Lmo_OneSearch(pGia, CutSize, Cuts, Nodes, Trials, AreaGrowth, 1, fXor, fEscalate, fVerbose, pCache, NULL);
    RetryDepth = Lms_LevelNum(pRetry, fXor);
    if ( RetryDepth < Depth && (Gia_ManAndNum(pRetry) < Gia_ManAndNum(pBest) ||
         (Gia_ManAndNum(pRetry) == Gia_ManAndNum(pBest) && RetryDepth < BestDepth)) )
    { Gia_ManStop(pBest); pBest = pRetry; }
    else Gia_ManStop(pRetry);
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Iterate weighted critical-path cuts with shared recipe caches.]

***********************************************************************/
Gia_Man_t * Lms_TwoPerformTraceTimed( Gia_Man_t * pGia, int StopLevel, int CutSize,
    int Cuts, int Nodes, int Trials, double AreaGrowth, int fXor, int fEscalate, int fVerbose,
    int nPassLimit, Lms_TwoVisit_t pVisit, void * pData, abctime Deadline )
{
    Lmo_Cache_t Cache, * c = &Cache;
    Gia_Man_t * pCurrent, * pNext;
    void * pSaved = NULL;
    int i, Depth, NextDepth, InitialDepth, InitialNodes, Passes = 0, fPrivate = 0, fAfterRecovery = 0, fFinalChanged = 0;
    abctime Start = Abc_Clock();
    if ( !pGia || pGia->pManTime || Gia_ManHasChoices(pGia) || Gia_ManBufNum(pGia) || Gia_ManConstrNum(pGia) ||
         (fXor ? Gia_ManMuxNum(pGia) : pGia->pMuxes != NULL || Gia_ManXorNum(pGia)) ||
         Gia_ManObjNum(pGia) > INT_MAX/8 || StopLevel < -1 || StopLevel >= ABC_INFINITY || nPassLimit < 0 ||
         !(AreaGrowth == -1.0 || (AreaGrowth >= 0.0 && AreaGrowth <= DBL_MAX)) ||
         CutSize < 4 || CutSize > 16 || Cuts < 2 || Cuts > 256 || Nodes < 0 || Nodes > 64 || Trials < 0 || Trials > 10000 )
    {
        Abc_Print(-1, "&lms2: invalid graph or search budgets; native XOR inputs require -x.\n");
        return NULL;
    }
    pCurrent = fXor && !pGia->pMuxes && !Gia_ManXorNum(pGia) ? Gia_ManDupMuxes(pGia, 0) : Gia_ManDup(pGia);
    if ( fXor )
    {
        // Unit-XAG depth is measured at outputs. Remove dangling gates now
        // so cleanup alone cannot look like a failed level-reduction pass.
        pNext = Gia_ManCleanup(pCurrent);
        Gia_ManStop(pCurrent); pCurrent = pNext;
    }
    pCurrent->nRegs = 0;
    Abc_CexFreeP(&pCurrent->pCexSeq);
    // This optimizer uses uniform unit-gate levels, with every CI at zero.
    Vec_IntFreeP(&pCurrent->vCiArrs); Vec_IntFreeP(&pCurrent->vCoReqs); Vec_IntFreeP(&pCurrent->vCoArrs);
    Depth = InitialDepth = Lms_LevelNum(pCurrent, fXor);
    InitialNodes = Gia_ManAndNum(pCurrent);
    // Honor an already-met -D without changing the graph. Otherwise remove
    // available redundancy before pricing the first level against its input.
    if ( Depth > Abc_MaxInt(0, StopLevel) )
    {
        abctime RecoverStart = Abc_Clock();
        pCurrent = Lmo_RecoverArea(pCurrent, CutSize, Nodes, fXor, Deadline);
        Depth = Lms_LevelNum(pCurrent, fXor);
        if ( fVerbose )
            Abc_Print(1, "LMS2 input recovery: %d -> %d gates; level %d -> %d; time %.3f s.\n",
                InitialNodes, Gia_ManAndNum(pCurrent), InitialDepth, Depth, (double)(Abc_Clock()-RecoverStart)/CLOCKS_PER_SEC);
    }
    if ( pVisit ) pVisit(pData, pCurrent, Depth);
    if ( fXor && Nodes && Depth > Abc_MaxInt(0, StopLevel) )
    {
        if ( !Abc_RecTargetXorStart3(&pSaved, fVerbose) ) { Gia_ManStop(pCurrent); return NULL; }
        fPrivate = 1;
    }
    memset(c, 0, sizeof(*c));
    c->Deadline = Deadline;
    // Scale slots with the problem count, rather than evicting on almost
    // every miss while most of the memory budget remains unused.
    c->nBins = 32768; c->Limit = 64*1024*1024;
    while ( c->nBins < (1<<20) && (size_t)c->nBins < (size_t)Gia_ManObjNum(pCurrent)*Cuts*8 ) c->nBins <<= 1;
    c->pBins = ABC_CALLOC(Lmo_Memo_t *, c->nBins);
    c->vPrograms = Vec_IntAlloc(1000); c->vOffsets = Vec_IntAlloc(1000);
    while ( Depth > Abc_MaxInt(0, StopLevel) && (!nPassLimit || Passes < nPassLimit) && (!Deadline || Abc_ClockHr() < Deadline) )
    {
        int fRecovered = 0;
        c->Pass = Passes+1;
        if ( fVerbose ) Abc_Print(1, "LMS2 iteration %d: %d gates, %d levels.\n", Passes+1, Gia_ManAndNum(pCurrent), Depth);
        pNext = Lmo_OnePerform(pCurrent, CutSize, Cuts, Nodes, Trials, AreaGrowth, fXor, fEscalate, fVerbose, c,
            fEscalate && !fAfterRecovery ? &fRecovered : NULL);
        if ( !pNext ) { Abc_Print(0, "LMS2: keeping the preceding feasible result after a failed pass.\n"); break; }
        ++Passes;
        NextDepth = Lms_LevelNum(pNext, fXor);
        if ( NextDepth > Depth || (NextDepth == Depth && Gia_ManAndNum(pNext) > Gia_ManAndNum(pCurrent)) )
        { Gia_ManStop(pNext); break; }
        // Charge the actual recovered graph, including all sharing, against
        // the graph entering this pass. In XOR mode both gate types count once.
        if ( Lmo_OverBudget(pCurrent, pNext, AreaGrowth) )
        {
            Abc_Print(1, "LMS2: area limit %g%% rejects %d -> %d gates at level %d -> %d; retaining %d gates / %d levels.\n",
                AreaGrowth, Gia_ManAndNum(pCurrent), Gia_ManAndNum(pNext), Depth, NextDepth, Gia_ManAndNum(pCurrent), Depth);
            Gia_ManStop(pNext);
            break;
        }
        Gia_ManStop(pCurrent);
        pCurrent = pNext;
        if ( pVisit ) pVisit(pData, pCurrent, NextDepth);
        if ( NextDepth == Depth && !fRecovered ) break;
        Depth = NextDepth;
        fAfterRecovery = fRecovered;
    }
    // Keep an already-met -D a no-op. Otherwise recover at the attained
    // depth without restarting the ordinary level search.
    if ( InitialDepth > Abc_MaxInt(0, StopLevel) && (!Deadline || Abc_ClockHr() < Deadline) )
    {
        int OldNodes = Gia_ManAndNum(pCurrent), OldDepth = Depth;
        pCurrent = Lmo_RecoverFinal(pCurrent, CutSize, Nodes, fXor, fVerbose, "final", Deadline);
        Depth = Lms_LevelNum(pCurrent, fXor);
        fFinalChanged = Depth != OldDepth || Gia_ManAndNum(pCurrent) != OldNodes;
    }
    if ( !pCurrent->vNamesIn && pGia->vNamesIn ) pCurrent->vNamesIn = Vec_PtrDupStr(pGia->vNamesIn);
    if ( !pCurrent->vNamesOut && pGia->vNamesOut ) pCurrent->vNamesOut = Vec_PtrDupStr(pGia->vNamesOut);
    if ( fXor )
    {
        Vec_IntFreeP(&pCurrent->vCoArrs);
        pCurrent->vCoArrs = Vec_IntAlloc(Gia_ManCoNum(pCurrent));
        Lms_XorLevels(pCurrent, pCurrent->vCoArrs);
    }
    if ( pVisit && fFinalChanged ) pVisit(pData, pCurrent, Depth);
    if ( fVerbose )
    {
        Abc_Print(1, "LMS2 resub cache: %llu hits (%llu across iterations), %llu misses, %llu evictions, %.2f MiB retained (%.0f MiB limit).\n",
            (unsigned long long)c->Hits, (unsigned long long)c->CrossHits, (unsigned long long)c->Misses,
            (unsigned long long)c->Evictions, c->Bytes/(1024.0*1024.0), c->Limit/(1024.0*1024.0));
    }
    for ( i = 0; i < c->nBins; ++i ) ABC_FREE(c->pBins[i]);
    ABC_FREE(c->pBins);
    Vec_IntFree(c->vPrograms); Vec_IntFree(c->vOffsets);
    if ( c->fLibrary ) Abc_RecTargetCache3(0);
    if ( fPrivate ) Abc_RecTargetXorStop3(pSaved);
    Abc_Print(1, "LMS2: %d -> %d %s; level %d -> %d; %d iterations; time %.3f s.\n",
        InitialNodes, Gia_ManAndNum(pCurrent), fXor ? "AND/XOR gates" : "ANDs", InitialDepth, Depth, Passes,
        (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( StopLevel >= 0 && Depth <= StopLevel && fVerbose ) Abc_Print(1, "LMS2: stopping bound %d reached.\n", StopLevel);
    return pCurrent;
}

Gia_Man_t * Lms_TwoPerformTrace( Gia_Man_t * pGia, int StopLevel, int CutSize,
    int Cuts, int Nodes, int Trials, double AreaGrowth, int fXor, int fEscalate, int fVerbose,
    int nPassLimit, Lms_TwoVisit_t pVisit, void * pData )
{
    return Lms_TwoPerformTraceTimed(pGia, StopLevel, CutSize, Cuts, Nodes, Trials, AreaGrowth, fXor, fEscalate,
                                    fVerbose, nPassLimit, pVisit, pData, 0);
}

/**Function*************************************************************

  Synopsis    [Runs the unrestricted-pass LMS2 search.]

***********************************************************************/
Gia_Man_t * Lms_TwoPerform( Gia_Man_t * pGia, int StopLevel, int CutSize,
    int Cuts, int Nodes, int Trials, double AreaGrowth, int fXor, int fEscalate, int fVerbose )
{
    return Lms_TwoPerformTrace(pGia, StopLevel, CutSize, Cuts, Nodes, Trials,
                               AreaGrowth, fXor, fEscalate, fVerbose, 0, NULL, NULL);
}

ABC_NAMESPACE_IMPL_END
