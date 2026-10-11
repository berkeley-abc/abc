/**CFile****************************************************************

  FileName    [lmsCuts.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS target-delay optimization.]

  Synopsis    [Six-input cut enumeration directly over a GIA.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 10, 2026.]

  Revision    [$Id: lmsCuts.c,v 1.00 2026/10/10 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lms.h"
#include "aig/gia/gia.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// The merge, containment, and truth operations follow giaCut.c's sorted
// six-input path. Truth tables fit in one word; no truth store is needed.
typedef struct Lmc_Cut_t_ Lmc_Cut_t;
struct Lmc_Cut_t_
{
    word Truth, Sign;
    int Leaves[6], nLeaves, Delay;
    float Flow, Edge;
};
// Matching data is needed only until this node's retained cuts are visited.
// Fanin cut sets keep the compact truth/leaf/ranking record above.
typedef struct Lmc_Work_t_ Lmc_Work_t;
struct Lmc_Work_t_
{
    Lmc_Cut_t Cut;
    Lms_CutMatch_t Match;
};
typedef struct Lmc_Set_t_ Lmc_Set_t;
struct Lmc_Set_t_
{
    Lmc_Set_t * pNext;
    int nCuts, Capacity;
    Lmc_Cut_t Cuts[1];
};
typedef struct Lmc_Obj_t_ Lmc_Obj_t;
struct Lmc_Obj_t_
{
    Lmc_Set_t * pSet;
    int Refs, Uses, Delay, fChanged;
    float Flow, Edge;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compute the leaf-set signature.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Lmc_Sign( Lmc_Cut_t * pCut )
{
    word Sign = 0;
    int i;
    for ( i = 0; i < pCut->nLeaves; ++i ) Sign |= (word)1 << (pCut->Leaves[i] & 63);
    return Sign;
}

/**Function*************************************************************

  Synopsis    [Merge two sorted leaf sets, stopping at six leaves.]

  Description [Specialized from Gia_CutMergeOrder.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmc_Merge( Lmc_Cut_t * a, Lmc_Cut_t * b, Lmc_Cut_t * c )
{
    int i = 0, k = 0, n = 0;
    if ( a->nLeaves + b->nLeaves > 6 && Gia_WordCountOnes(a->Sign | b->Sign) > 6 ) return 0;
    while ( i < a->nLeaves || k < b->nLeaves )
    {
        if ( n == 6 ) return 0;
        if ( k == b->nLeaves || (i < a->nLeaves && a->Leaves[i] < b->Leaves[k]) )
            c->Leaves[n++] = a->Leaves[i++];
        else if ( i == a->nLeaves || b->Leaves[k] < a->Leaves[i] )
            c->Leaves[n++] = b->Leaves[k++];
        else
        { c->Leaves[n++] = a->Leaves[i++]; ++k; }
    }
    c->nLeaves = n;
    c->Sign = a->Sign | b->Sign;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Check whether the smaller sorted cut is contained.]

  Description [Specialized from Gia_CutSetCutIsContainedOrder.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmc_Contains( Lmc_Cut_t * pBase, Lmc_Cut_t * pCut )
{
    int i, k = 0;
    if ( (pBase->Sign & pCut->Sign) != pCut->Sign ) return 0;
    for ( i = 0; i < pBase->nLeaves && k < pCut->nLeaves; ++i )
    {
        if ( pBase->Leaves[i] > pCut->Leaves[k] ) return 0;
        if ( pBase->Leaves[i] == pCut->Leaves[k] ) ++k;
    }
    return k == pCut->nLeaves;
}

/**Function*************************************************************

  Synopsis    [Compose fanin truths and remove unused input variables.]

  Description [Uses the word-sized expansion/minimization of giaCut.c.
  Truth includes output polarity, so no separate phase flag is needed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmc_Truth( Lmc_Cut_t * a, Lmc_Cut_t * b, Lmc_Cut_t * c, int fCompl0, int fCompl1 )
{
    int n = c->nLeaves;
    word t0 = fCompl0 ? ~a->Truth : a->Truth;
    word t1 = fCompl1 ? ~b->Truth : b->Truth;
    t0 = Abc_Tt6Expand(t0, a->Leaves, a->nLeaves, c->Leaves, n);
    t1 = Abc_Tt6Expand(t1, b->Leaves, b->nLeaves, c->Leaves, n);
    c->Truth = t0 & t1;
    c->nLeaves = Abc_Tt6MinBase(&c->Truth, c->Leaves, n);
    if ( c->nLeaves == n ) return 0;
    c->Sign = Lmc_Sign(c);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Compare cuts by delay, leaf count, area flow, and edge flow.]

  Description [Preserves the initial delay round's priority and stable ties.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmc_Compare( Lmc_Cut_t * a, Lmc_Cut_t * b )
{
    if ( a->Delay != b->Delay ) return a->Delay < b->Delay ? -1 : 1;
    if ( a->nLeaves != b->nLeaves ) return a->nLeaves < b->nLeaves ? -1 : 1;
    if ( a->Flow < b->Flow - 0.005f ) return -1;
    if ( a->Flow > b->Flow + 0.005f ) return 1;
    if ( a->Edge < b->Edge - 0.005f ) return -1;
    if ( a->Edge > b->Edge + 0.005f ) return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Evaluate a cut in the current leaf arrival and flow context.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmc_Evaluate( Lmc_Obj_t * pObjs, Lmc_Work_t * w, Lms_CutCost_t pCost )
{
    Lmc_Cut_t * c = &w->Cut;
    int v, Area, Times[6];
    for ( v = 0; v < c->nLeaves; ++v ) Times[v] = pObjs[c->Leaves[v]].Delay;
    c->Delay = pCost(c->Truth, c->nLeaves, Times, &Area, &w->Match);
    c->Flow = (float)Area;
    c->Edge = (float)c->nLeaves;
    for ( v = 0; v < c->nLeaves; ++v )
    {
        c->Flow = Abc_MinFloat(1.0e32f, c->Flow + pObjs[c->Leaves[v]].Flow);
        c->Edge = Abc_MinFloat(1.0e32f, c->Edge + pObjs[c->Leaves[v]].Edge);
    }
}

/**Function*************************************************************

  Synopsis    [Insert the next cut in stable priority order under the budget.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmc_Insert( Lmc_Work_t ** ppCuts, int nCuts, int nCutsMax )
{
    Lmc_Work_t * c = ppCuts[nCuts];
    int v;
    for ( v = nCuts; v > 0 && Lmc_Compare(&ppCuts[v-1]->Cut, &c->Cut) > 0; --v )
        ppCuts[v] = ppCuts[v-1];
    ppCuts[v] = c;
    return nCuts + (nCuts < nCutsMax);
}

/**Function*************************************************************

  Synopsis    [Filter containment by delay and rank under the cut budget.]

  Description [Each essential leaf of a multi-input function traverses at
  least one AND. The latest arrival plus one is therefore a lower bound.
  Constants and wires need no AND. Compute the bound after support reduction;
  a late leaf that cancels out must not block evaluation. Match lazily when
  containment needs an exact delay. A subset dominates only if it is at
  least as fast; protect cut 0 from removal even on equal-delay ties.]

  SideEffects [Updates the retained cut set under the shared budget.]

  SeeAlso     []

***********************************************************************/
static int Lmc_AddCut( Lmc_Obj_t * pObjs, Lmc_Work_t ** ppCuts, int nCuts, int nCutsMax, Lms_CutCost_t pCost )
{
    Lmc_Work_t * w = ppCuts[nCuts], * pOldWork;
    Lmc_Cut_t * c = &w->Cut, * pOld;
    int i, k, v, Bound = 0, fEvaluated = 0;
    for ( v = 0; v < c->nLeaves; ++v ) Bound = Abc_MaxInt(Bound, pObjs[c->Leaves[v]].Delay);
    Bound = Abc_MinInt(ABC_INFINITY-1, Bound + (c->nLeaves > 1));
    // A strictly later cut cannot displace any retained cut, or remove a
    // superset by delay dominance. Ties still need the remaining priorities.
    if ( nCuts == nCutsMax && Bound > ppCuts[nCuts-1]->Cut.Delay ) return nCuts;
    for ( i = 0; i < nCuts; ++i )
    {
        pOldWork = ppCuts[i];
        pOld = &pOldWork->Cut;
        if ( pOld->nLeaves <= c->nLeaves )
        {
            if ( !Lmc_Contains(c, pOld) ) continue;
            if ( pOld->Delay <= Bound ) return nCuts;
            if ( !fEvaluated ) { Lmc_Evaluate(pObjs, w, pCost); fEvaluated = 1; }
            if ( pOld->Delay <= c->Delay ) return nCuts;
            continue;
        }
        if ( i == 0 || Bound > pOld->Delay || !Lmc_Contains(pOld, c) ) continue;
        if ( !fEvaluated ) { Lmc_Evaluate(pObjs, w, pCost); fEvaluated = 1; }
        if ( c->Delay > pOld->Delay ) continue;
        for ( k = i; k < nCuts; ++k ) ppCuts[k] = ppCuts[k+1];
        ppCuts[nCuts--] = pOldWork;
        --i;
    }
    if ( !fEvaluated ) Lmc_Evaluate(pObjs, w, pCost);
    return Lmc_Insert(ppCuts, nCuts, nCutsMax);
}

/**Function*************************************************************

  Synopsis    [Release cut storage after its last AND or choice consumer.]

  Description [Cut sets are recycled; CIs and constants use local unit cuts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmc_Release( Lmc_Obj_t * pObj, Lmc_Set_t ** ppFree )
{
    assert(pObj->Uses > 0);
    if ( --pObj->Uses || !pObj->pSet ) return;
    pObj->pSet->pNext = ppFree[pObj->pSet->Capacity];
    ppFree[pObj->pSet->Capacity] = pObj->pSet;
    pObj->pSet = NULL;
}

/**Function*************************************************************

  Synopsis    [Enumerate retained six-input cuts in one topological pass.]

  Description [No mapping cover, required times, or reconstruction is built.
  The cost callback returns a library delay and area for supplied arrivals;
  ABC_INFINITY denotes a missing function. The visit callback receives each
  retained nontrivial cut, and may return zero to stop. Only cut sets needed
  by unvisited AND or choice consumers remain live. Choice links point to
  earlier ANDs, as in the GIA mappers. Import sibling cuts with the relative
  output phase, excluding the sibling unit cut, under the same cut budget.
  The caller initializes zero-input phases before collecting choices.
  Members with no ordinary fanouts only supply cuts to the next member;
  they need no candidate bank of their own. Optional object-indexed pLimits
  supplies each node's budget. Recycle sets by capacity, so a few large
  budgets do not enlarge every set. During recollection, visit only changed
  budgets and their transitive AND/choice consumers. Other cuts are identical
  to the first uniform-budget pass. All arrays are local to this call.]

  SideEffects [Calls the client's cost and visit procedures.]

  SeeAlso     []

***********************************************************************/
static int Lmc_Collect( Gia_Man_t * pGia, int nCutsMax, const int * pLimits,
    Lms_CutCost_t pCost, Lms_CutVisit_t pVisit, void * pData, int fRecollect, int fVerbose )
{
    Lmc_Obj_t * pObjs = NULL, * pThis;
    Lmc_Set_t * pFree[129] = {0}, * pSet;
    Lmc_Work_t * pCuts = NULL, ** ppCuts = NULL;
    Lmc_Cut_t * a, * b, * c, Units[2];
    Gia_Obj_t * pObj;
    int Id, i, k, v, nCuts, n0, n1, i0, i1, Sibl, Result = 0;
    int nObjs = Gia_ManObjNum(pGia), nSets = 0, nChoices = 0;
    double nPairs = 0, nTruths = 0, nKept = 0, nVisited = 0;
    size_t SetBytes, AllocBytes = 0;
    int DefaultMax = nCutsMax, NodeMax;
    abctime Start = Abc_Clock();
    assert(nCutsMax >= 1 && nCutsMax <= 128);
    assert(!Gia_ManRegNum(pGia) && !pGia->pMuxes);
    assert(!Gia_ManXorNum(pGia) && !Gia_ManBufNum(pGia));
    if ( pLimits )
        for ( Id = 0; Id < nObjs; ++Id )
        {
            if ( pLimits[Id] < 1 || pLimits[Id] > 128 )
            { Abc_Print(-1, "LMS cuts: node budgets must be in [1, 128].\n"); goto cleanup; }
            nCutsMax = Abc_MaxInt(nCutsMax, pLimits[Id]);
        }
    pObjs = ABC_CALLOC(Lmc_Obj_t, nObjs);
    pCuts = ABC_ALLOC(Lmc_Work_t, nCutsMax+1);
    ppCuts = ABC_ALLOC(Lmc_Work_t *, nCutsMax+1);
    if ( !pObjs || !pCuts || !ppCuts ) goto cleanup;
    if ( pGia->vCiArrs )
    {
        if ( Vec_IntSize(pGia->vCiArrs) != Gia_ManCiNum(pGia) ) goto cleanup;
        Gia_ManForEachCi(pGia, pObj, i)
        {
            int Arrival = Vec_IntEntry(pGia->vCiArrs, i);
            if ( Arrival < 0 || Arrival >= ABC_INFINITY ) goto cleanup;
            pObjs[Gia_ObjId(pGia, pObj)].Delay = Arrival;
        }
    }
    Gia_ManForEachObj(pGia, pObj, Id)
    {
        Sibl = Gia_ObjSibl(pGia, Id);
        if ( Sibl )
        {
            if ( !Gia_ObjIsAnd(pObj) || Sibl < 0 || Sibl >= Id || !Gia_ObjIsAnd(Gia_ManObj(pGia, Sibl)) )
            { Abc_Print(-1, "LMS cuts: choice links must point to earlier AND nodes.\n"); goto cleanup; }
            ++pObjs[Sibl].Uses;
            ++nChoices;
        }
        if ( !Gia_ObjIsAnd(pObj) && !Gia_ObjIsCo(pObj) ) continue;
        i0 = Gia_ObjFaninId0p(pGia, pObj);
        ++pObjs[i0].Refs;
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        i1 = Gia_ObjFaninId1p(pGia, pObj);
        ++pObjs[i1].Refs;
        ++pObjs[i0].Uses;
        ++pObjs[i1].Uses;
    }
    Gia_ManForEachAnd(pGia, pObj, Id)
    {
        Lmc_Cut_t * pFans[2];
        i0 = Gia_ObjFaninId0p(pGia, pObj);
        i1 = Gia_ObjFaninId1p(pGia, pObj);
        for ( v = 0; v < 2; ++v )
        {
            int Fan = v ? i1 : i0;
            if ( pObjs[Fan].pSet ) pFans[v] = pObjs[Fan].pSet->Cuts;
            else
            {
                assert(!Gia_ObjIsAnd(Gia_ManObj(pGia, Fan)));
                memset(Units+v, 0, sizeof(Lmc_Cut_t));
                Units[v].nLeaves = Fan != 0;
                Units[v].Leaves[0] = Fan;
                Units[v].Truth = Fan ? ABC_CONST(0xAAAAAAAAAAAAAAAA) : 0;
                Units[v].Sign = Lmc_Sign(Units+v);
                pFans[v] = Units+v;
            }
        }
        n0 = pObjs[i0].pSet ? pObjs[i0].pSet->nCuts : 1;
        n1 = pObjs[i1].pSet ? pObjs[i1].pSet->nCuts : 1;
        nPairs += n0*n1;
        nCuts = 0;
        NodeMax = pLimits ? pLimits[Id] : DefaultMax;
        for ( i = 0; i <= NodeMax; ++i ) ppCuts[i] = pCuts+i;
        Sibl = Gia_ObjSibl(pGia, Id);
        if ( Sibl )
        {
            int Compl = Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(pGia, Sibl));
            pSet = pObjs[Sibl].pSet;
            assert(pSet != NULL);
            for ( i = 0; i < pSet->nCuts; ++i )
            {
                a = pSet->Cuts+i;
                if ( a->nLeaves == 1 && a->Leaves[0] == Sibl ) continue;
                c = &ppCuts[nCuts]->Cut;
                *c = *a;
                if ( Compl ) c->Truth = ~c->Truth;
                nCuts = Lmc_AddCut(pObjs, ppCuts, nCuts, NodeMax, pCost);
            }
        }
        for ( i = 0; i < n0; ++i )
        for ( k = 0; k < n1; ++k )
        {
            a = pFans[0]+i;
            b = pFans[1]+k;
            c = &ppCuts[nCuts]->Cut;
            if ( !Lmc_Merge(a, b, c) ) continue;
            ++nTruths;
            Lmc_Truth(a, b, c, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj));
            nCuts = Lmc_AddCut(pObjs, ppCuts, nCuts, NodeMax, pCost);
        }
        assert(nCuts > 0);
        pThis = pObjs+Id;
        pThis->fChanged = NodeMax != DefaultMax || pObjs[i0].fChanged || pObjs[i1].fChanged ||
            (Sibl && pObjs[Sibl].fChanged);
        c = &ppCuts[0]->Cut;
        pThis->Delay = c->Delay;
        pThis->Flow = c->Flow;
        pThis->Edge = c->Edge;
        if ( c->Delay == ABC_INFINITY )
        {
            // The selector always has the original gate as a fallback,
            // even when a custom library omits all functions at this node.
            pThis->Delay = Abc_MinInt(ABC_INFINITY-1, Abc_MaxInt(pObjs[i0].Delay, pObjs[i1].Delay)) + 1;
            pThis->Flow = Abc_MinFloat(1.0e32f, 1 + pObjs[i0].Flow + pObjs[i1].Flow);
            pThis->Edge = Abc_MinFloat(1.0e32f, 2 + pObjs[i0].Edge + pObjs[i1].Edge);
        }
        pThis->Flow /= Abc_MaxInt(1, pThis->Refs);
        pThis->Edge /= Abc_MaxInt(1, pThis->Refs);
        nKept += nCuts;
        for ( i = 0; i < nCuts && (!nChoices || pThis->Refs) && (!fRecollect || pThis->fChanged); ++i )
        {
            c = &ppCuts[i]->Cut;
            if ( !pVisit(pData, Id, c->nLeaves, c->Leaves, c->Truth, &ppCuts[i]->Match) ) goto cleanup;
            ++nVisited;
        }
        Lmc_Release(pObjs+i0, pFree);
        Lmc_Release(pObjs+i1, pFree);
        if ( Sibl ) Lmc_Release(pObjs+Sibl, pFree);
        if ( !pThis->Uses ) continue;
        pSet = pFree[NodeMax];
        if ( pSet ) pFree[NodeMax] = pSet->pNext;
        else
        {
            SetBytes = sizeof(Lmc_Set_t) + (size_t)NodeMax*sizeof(Lmc_Cut_t);
            pSet = (Lmc_Set_t *)ABC_ALLOC(char, SetBytes);
            if ( !pSet ) goto cleanup;
            ++nSets;
            AllocBytes += SetBytes;
            pSet->Capacity = NodeMax;
        }
        pThis->pSet = pSet;
        pSet->nCuts = nCuts;
        for ( i = 0; i < nCuts; ++i ) pSet->Cuts[i] = ppCuts[i]->Cut;
        if ( ppCuts[0]->Cut.nLeaves > 1 )
        {
            c = pSet->Cuts + pSet->nCuts++;
            memset(c, 0, sizeof(*c));
            c->nLeaves = 1;
            c->Leaves[0] = Id;
            c->Sign = (word)1 << (Id & 63);
            c->Truth = ABC_CONST(0xAAAAAAAAAAAAAAAA);
        }
    }
    Result = 1;
    if ( fVerbose && nChoices ) Abc_Print(1, "LMS cuts: merged %d choice links under the shared cut budget.\n", nChoices);
    if ( fVerbose ) Abc_Print(1, "LMS cuts: %.0f pairs, %.0f truths, %.0f retained; %d live cut sets, %.2f MiB; %.3f s.\n",
        nPairs, nTruths, nKept, nSets,
        ((double)AllocBytes + (double)nObjs*sizeof(Lmc_Obj_t))/(1024*1024),
        (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( fVerbose && fRecollect )
        Abc_Print(1, "LMS cuts: revisited %.0f / %.0f retained cuts after budget changes.\n", nVisited, nKept);
cleanup:
    if ( !Result ) Abc_Print(-1, "LMS cuts: collection failed; input unchanged.\n");
    if ( pObjs )
        for ( Id = 0; Id < nObjs; ++Id ) ABC_FREE(pObjs[Id].pSet);
    for ( i = 0; i <= 128; ++i )
        while ( pFree[i] )
        { pSet = pFree[i]->pNext; ABC_FREE(pFree[i]); pFree[i] = pSet; }
    ABC_FREE(pObjs);
    ABC_FREE(pCuts);
    ABC_FREE(ppCuts);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Enumerate cuts with optional per-node budgets.]

  Description []

  SideEffects []

  SeeAlso     [Lms_CutsCollect]

***********************************************************************/
int Lms_CutsCollectBudgeted( Gia_Man_t * pGia, int nCutsMax, const int * pLimits,
    Lms_CutCost_t pCost, Lms_CutVisit_t pVisit, void * pData, int fVerbose )
{
    return Lmc_Collect(pGia, nCutsMax, pLimits, pCost, pVisit, pData, 0, fVerbose);
}

/**Function*************************************************************

  Synopsis    [Visit only cuts affected by changes to a uniform cut budget.]

  Description [The caller retains the first bank. Recompute fanin sets but
  skip visits outside the transitive fanout of changed budgets, including
  choice imports. The GIA, timing, library and cost callback are unchanged.]

  SideEffects []

  SeeAlso     [Lms_CutsCollectBudgeted]

***********************************************************************/
int Lms_CutsRecollect( Gia_Man_t * pGia, int nCutsMax, const int * pLimits,
    Lms_CutCost_t pCost, Lms_CutVisit_t pVisit, void * pData, int fVerbose )
{
    return Lmc_Collect(pGia, nCutsMax, pLimits, pCost, pVisit, pData, 1, fVerbose);
}

/**Function*************************************************************

  Synopsis    [Enumerate cuts with a uniform budget.]

  Description []

  SideEffects []

  SeeAlso     [Lms_CutsCollectBudgeted]

***********************************************************************/
int Lms_CutsCollect( Gia_Man_t * pGia, int nCutsMax, Lms_CutCost_t pCost,
    Lms_CutVisit_t pVisit, void * pData, int fVerbose )
{
    return Lms_CutsCollectBudgeted(pGia, nCutsMax, NULL, pCost, pVisit, pData, fVerbose);
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
