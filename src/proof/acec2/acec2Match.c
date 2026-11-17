/**CFile****************************************************************

  FileName    [acec2Match.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Finds and proves internal arithmetic word correspondences.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 12, 2026.]

  Revision    [$Id$]

  Description [Partial-product ranks propose operand buses. Independent
  operand patterns locate candidate result bits inside each design. Only
  exact proofs on extracted cones authorize replacement; neither the bus
  inference nor simulation is trusted as an equivalence proof.]

***********************************************************************/

#include "acec2Int.h"
#include "misc/vec/vecHsh.h"
#include "proof/cec/cec.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef struct Acec2_Edge_t_ Acec2_Edge_t;
struct Acec2_Edge_t_ { int a, b, rank; };
typedef enum {
    ACEC2_PRODUCT_TEMPLATE,
    ACEC2_PRODUCT_SHIFTED,
    ACEC2_PRODUCT_CERTIFICATE,
    ACEC2_PRODUCT_BOUNDARY
} Acec2_ProductStage_t;
enum { ACEC2_CACHE_LINEAR_WORD = 2, ACEC2_CACHE_BDD = 3 };
static int Acec2_BoundaryCache( Acec2_Man_t * m, Gia_Man_t ** g, Vec_Int_t ** vRoots, Vec_Int_t ** vOps,
                                 int Width, int fModel, int Choice );


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Orders repeated partial products by endpoints and weight.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_EdgeCompare( const void * x, const void * y )
{
    const Acec2_Edge_t * a = (const Acec2_Edge_t *)x, * b = (const Acec2_Edge_t *)y;
    if ( a->a != b->a ) return a->a < b->a ? -1 : 1;
    if ( a->b != b->b ) return a->b < b->b ? -1 : 1;
    return a->rank == b->rank ? 0 : a->rank < b->rank ? -1 : 1;
}

/**Function*************************************************************

  Synopsis    [Marks original logic still exposed beyond proved shared cuts.]

  Description [A shared function can be a common free input to context CEC.
  Arithmetic entirely behind such boundaries needs no further proposals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Bit_t * Acec2_ProductLive( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vColors, int fStopAtShared )
{
    Gia_Obj_t * o;
    Vec_Bit_t * vLive = Vec_BitStart(Gia_ManObjNum(m->pGia));
    int i, k, id;
    Gia_ManForEachCo(m->pGia, o, i)
    {
        id = Gia_ObjFaninId0p(m->pGia, o);
        if ( Vec_IntEntry(vColors, Vec_IntEntry(vMap, id) >> 1) != 3 ) Acec2_BitWrite(vLive, id, 1);
    }
    for ( i = Gia_ManObjNum(m->pGia)-1; i > 0; i-- )
    {
        o = Gia_ManObj(m->pGia, i);
        if ( !Vec_BitEntry(vLive, i) || !Gia_ObjIsAnd(o) ) continue;
        for ( k = 0; k < (Gia_ObjIsMux(m->pGia, o) ? 3 : 2); k++ )
        {
            id = k == 2 ? Gia_ObjFaninId2(m->pGia, i) : k ? Gia_ObjFaninId1(o, i) : Gia_ObjFaninId0(o, i);
            if ( !fStopAtShared || Vec_IntEntry(vColors, Vec_IntEntry(vMap, id) >> 1) != 3 ) Acec2_BitWrite(vLive, id, 1);
        }
    }
    return vLive;
}
/**Function*************************************************************

  Synopsis    [Tests whether a region contains an exposed cell output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ProductTreeLive( Acec2_Man_t * m, Vec_Bit_t * vLive, int Tree )
{
    Vec_Int_t * v = Vec_WecEntry(m->vTrees, Tree);
    Acec2_Cell_t * c;
    int i, id;
    Vec_IntForEachEntry(v, id, i)
    {
        c = Acec2_Cell(m, id);
        if ( Vec_BitEntry(vLive, c->Out[0] >> 1) || Vec_BitEntry(vLive, c->Out[1] >> 1) ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Prioritizes regions with substantial unresolved arithmetic.]

  Description [Mostly shared words can retain a few unrelated taps. They
  should not consume the complete component budget ahead of an exposed
  multiplier. Ordering affects proposals only, never their certification.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wrd_t * Acec2_ProductOrder( Acec2_Man_t * m, Vec_Bit_t * vLive )
{
    Vec_Wrd_t * vOrder = Vec_WrdAlloc(Vec_WecSize(m->vTrees));
    Vec_Int_t * v;
    Acec2_Cell_t * c;
    int tree, i, id, count;
    Vec_WecForEachLevel(m->vTrees, v, tree)
    {
        count = 0;
        Vec_IntForEachEntry(v, id, i)
        {
            c = Acec2_Cell(m, id);
            count += Vec_BitEntry(vLive, c->Out[0] >> 1) || Vec_BitEntry(vLive, c->Out[1] >> 1);
        }
        if ( count ) Vec_WrdPush(vOrder, ((word)(unsigned)count << 32) | (0xFFFFFFFFu-(unsigned)tree));
    }
    if ( Vec_WrdSize(vOrder) > 1 ) Vec_WrdSort(vOrder, 1);
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Collects weighted product graphs over already shared signals.]

  Description [Repeated products are summed before taking their low weight.
  This accounts for the doubled off-diagonal terms of a square, including
  cases where only some duplicates have already collapsed in the AIG.
  Degree and rank consistency only filter proposals; every accepted output
  correspondence is proved separately over independent cut variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wec_t * Acec2_ProductGraph( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vColors,
                                      int Tree, Hsh_Int1Man_t * h, Vec_Int_t ** pvEdges )
{
    Vec_Int_t * vLeaves = Acec2_ProductLeaves(m, Tree), * vEdges = Vec_IntAlloc(Vec_IntSize(vLeaves));
    Vec_Int_t * vDegree;
    Vec_Wec_t * vAdj;
    Gia_Obj_t * o;
    Acec2_Edge_t * e;
    int i, j, k, id, a, b, rank, carry, n = 0, count;
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        id = Abc_Lit2Var(Vec_IntEntry(vLeaves, i)); o = Gia_ManObj(m->pGia, id);
        if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
        a = Vec_IntEntry(vMap, Gia_ObjFaninId0(o, id)) ^ Gia_ObjFaninC0(o);
        b = Vec_IntEntry(vMap, Gia_ObjFaninId1(o, id)) ^ Gia_ObjFaninC1(o);
        if ( a < 2 || b < 2 || Vec_IntEntry(vColors, a >> 1) != 3 || Vec_IntEntry(vColors, b >> 1) != 3 ) continue;
        a = Acec2_IndexAdd(h, a); b = Acec2_IndexAdd(h, b);
        if ( a > b ) ABC_SWAP(int, a, b);
        Vec_IntPushThree(vEdges, a, b, Abc_Var2Lit(Vec_IntEntry(vLeaves, i+1), Vec_IntEntry(vLeaves, i)&1));
    }
    count = Vec_IntSize(vEdges)/3; e = (Acec2_Edge_t *)Vec_IntArray(vEdges);
    if ( count > 1 ) qsort(e, count, sizeof(Acec2_Edge_t), Acec2_EdgeCompare);
    for ( i = 0; i < count; i = j )
    {
        for ( j = i+1; j < count && e[i].a == e[j].a && e[i].b == e[j].b; j++ ) {}
        rank = e[i].rank >> 1; carry = 0; k = i;
        while ( k < j || carry )
        {
            while ( k < j && (e[k].rank >> 1) == rank ) carry += (e[k++].rank & 1) ? -1 : 1;
            if ( carry & 1 ) break;
            carry /= 2; rank++;
            if ( !carry && k < j ) rank = e[k].rank >> 1;
        }
        if ( carry ) { e[n] = e[i]; e[n++].rank = rank; }
    }
    Vec_IntShrink(vEdges, 3*n);
    vDegree = Vec_IntStart(Hsh_Int1ManEntryNum(h)); vAdj = Vec_WecStart(Hsh_Int1ManEntryNum(h));
    for ( i = 0; i < n; i++ ) { Vec_IntAddToEntry(vDegree, e[i].a, 1); Vec_IntAddToEntry(vDegree, e[i].b, 1); }
    for ( i = 0; i < n; i++ )
        if ( Vec_IntEntry(vDegree, e[i].a) >= 3 || Vec_IntEntry(vDegree, e[i].b) >= 3 )
        { Vec_WecPush(vAdj, e[i].a, i); Vec_WecPush(vAdj, e[i].b, i); }
    Vec_IntFree(vDegree); Vec_IntFree(vLeaves); *pvEdges = vEdges;
    return vAdj;
}

/**Function*************************************************************

  Synopsis    [Refines boundary candidates with component counterexamples.]

  Description [Small active supports are exhausted, which is an exact proof.
  Larger supports receive 65536 fresh patterns on the extracted cones. A
  discrepancy refines all candidates on that operand assignment; agreeing
  random patterns never authorize a replacement. Unused CIs cost no rounds.
  With a work limit, this is an exact-only query; a larger support or effort
  estimate returns unknown before enumeration.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RefineProductLimit( Gia_Man_t ** g, Acec2_WordSim_t ** s, Vec_Int_t ** vOps,
                               Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected,
                               int Width, Acec2_Par_t * pPars, abctime Deadline, Gia_Man_t * pModel,
                               int nExactInputs, int nWordLimit )
{
    static const word Truths[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    Vec_Int_t * vActive = Vec_IntAlloc(100), * vMark = Vec_IntAlloc(Gia_ManCiNum(g[0]));
    Vec_Int_t * vEval[2] = {Vec_IntAlloc(1000), Vec_IntAlloc(1000)};
    Vec_Wrd_t * vSim[2] = {Vec_WrdStart(Gia_ManObjNum(g[0])), Vec_WrdStart(Gia_ManObjNum(g[1]))};
    Gia_Obj_t * o, * f;
    int side, i, j, id, nRounds, fExact, result = 0;
    word state = ABC_CONST(0xA274891FE69DB035), a, b, value;
    if ( nExactInputs < 0 || nExactInputs > 20 || nWordLimit < 0 ) { result = -1; goto finish; }
    Vec_IntFill(vMark, Gia_ManCiNum(g[0]), 0);
    for ( side = 0; side < 2; side++ )
    {
        Gia_ManForEachAnd(g[side], o, i)
        {
            Vec_IntPush(vEval[side], i);
            for ( j = 0; j < (Gia_ObjIsMux(g[side], o) ? 3 : 2); j++ )
            {
                f = j == 2 ? Gia_ManObj(g[side], Gia_ObjFaninId2(g[side], i)) : j ? Gia_ObjFanin1(o) : Gia_ObjFanin0(o);
                if ( Gia_ObjIsCi(f) ) Vec_IntWriteEntry(vMark, Gia_ObjCioId(f), 1);
            }
        }
        Gia_ManForEachCo(g[side], o, i)
        { f = Gia_ObjFanin0(o); if ( Gia_ObjIsCi(f) ) Vec_IntWriteEntry(vMark, Gia_ObjCioId(f), 1); }
    }
    Vec_IntForEachEntry(vMark, id, i) if ( id ) Vec_IntPush(vActive, i);
    fExact = Vec_IntSize(vActive) <= nExactInputs;
    nRounds = fExact ? Abc_MaxInt(1, (1 << Vec_IntSize(vActive))/64) : 1024;
    if ( nWordLimit && (!fExact || ((ABC_INT64_T)Vec_IntSize(vEval[0])+Vec_IntSize(vEval[1])+
         Vec_IntSize(vActive)+2*Gia_ManCoNum(g[0]))*nRounds > nWordLimit) )
    { result = -1; goto finish; }
    Vec_WrdFill(vValues, Vec_WrdSize(vValues), 0);
    for ( i = 0; i < nRounds; i++ )
    {
        if ( (i & 15) == 0 && Acec2_Stop(pPars, Deadline) ) { result = -1; break; }
        Vec_IntForEachEntry(vActive, id, j)
        {
            if ( fExact )
            {
                value = j < 6 ? Truths[j] : ((i >> (j-6)) & 1) ? ~(word)0 : 0;
            }
            else { Acec2_Random(&state); value = state; }
            Vec_WrdWriteEntry(vValues, id, value);
            for ( side = 0; side < 2; side++ ) Vec_WrdWriteEntry(vSim[side], Gia_ObjId(g[side], Gia_ManCi(g[side], id)), value);
        }
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(vEval[side], id, j)
            {
                Vec_WrdWriteEntry(vSim[side], id, Acec2_SimGate(g[side], id, vSim[side], 1, 0));
            }
        for ( j = 0; j < Gia_ManCoNum(g[0]); j++ )
        {
            o = Gia_ManCo(g[0], j); a = Vec_WrdEntry(vSim[0], Gia_ObjFaninId0p(g[0], o)); if ( Gia_ObjFaninC0(o) ) a = ~a;
            o = Gia_ManCo(g[1], j); b = Vec_WrdEntry(vSim[1], Gia_ObjFaninId0p(g[1], o)); if ( Gia_ObjFaninC0(o) ) b = ~b;
            if ( a != b ) break;
        }
        if ( j == Gia_ManCoNum(g[0]) ) continue;
        if ( s )
        {
            Acec2_ModelPatterns(vOps, hCuts, vValues, vExpected, Width, pModel);
            for ( side = 0; side < 2; side++ ) Acec2_WordSimulate(s[side], vValues, vExpected, 1);
        }
        result = 2; break;
    }
    if ( i == nRounds && fExact )
    {
        result = 1;
        if ( s && pPars->fVerbose ) Abc_Print(1, "Exhaustive component proof: inputs = %d, output bits = %d.\n", Vec_IntSize(vActive), Gia_ManCoNum(g[0]));
    }
finish:
    Vec_IntFree(vActive); Vec_IntFree(vMark);
    for ( side = 0; side < 2; side++ ) { Vec_IntFree(vEval[side]); Vec_WrdFree(vSim[side]); }
    return result;
}

/**Function*************************************************************

  Synopsis    [Retains the ordinary component-refinement policy.]

  Description [Up to sixteen active inputs are exhausted. Larger supports
  use fresh simulation only to reject or refine candidates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RefineProduct( Gia_Man_t ** g, Acec2_WordSim_t ** s, Vec_Int_t ** vOps,
                               Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected,
                               int Width, Acec2_Par_t * pPars, abctime Deadline, Gia_Man_t * pModel )
{
    return Acec2_RefineProductLimit(g, s, vOps, hCuts, vValues, vExpected, Width, pPars, Deadline, pModel, 16, 0);
}

/**Function*************************************************************

  Synopsis    [Exhausts a small private dual-output weighted miter.]

  Description [All active input assignments must be checked. Twenty active
  inputs and four million packed gate/input/output evaluations bound this
  optional proof. Larger queries return unknown for the ordinary CEC
  fallback. Iterative copies preserve native gate functions and avoid a
  recursion-depth restriction.]

  SideEffects [Updates exact-check statistics.]

  SeeAlso     []

***********************************************************************/
static int Acec2_WeightedTruth( Acec2_Man_t * m, Gia_Man_t * q )
{
    Gia_Man_t * pair[2] = {NULL, NULL}, * clean; Gia_Obj_t * o;
    Vec_Int_t * map; Vec_Wrd_t * values;
    int side, i, lit, width, status, result = -1;
    if ( !m || !q || !Gia_ManCoNum(q) || (Gia_ManCoNum(q) & 1) ||
         Gia_ManRegNum(q) || Acec2_Stopped(m) ) return -1;
    m->nWeightedTruthChecks++; width = Gia_ManCoNum(q)/2;
    map = Vec_IntStart(Gia_ManObjNum(q)); values = Vec_WrdAlloc(Gia_ManCiNum(q));
    Vec_WrdFill(values, Gia_ManCiNum(q), 0);
    for ( side = 0; side < 2; side++ )
    {
        pair[side] = Gia_ManStart(Gia_ManObjNum(q)); Gia_ManHashAlloc(pair[side]);
        Gia_ManForEachCi(q, o, i) Vec_IntWriteEntry(map, Gia_ObjId(q, o), Gia_ManAppendCi(pair[side]));
        Gia_ManForEachAnd(q, o, i)
        {
            if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
            Vec_IntWriteEntry(map, i, Acec2_MapNode(q, pair[side], map, o, i));
        }
        for ( i = 0; i < width; i++ )
        {
            lit = Gia_ObjFaninLit0p(q, Gia_ManCo(q, 2*i+side));
            Gia_ManAppendCo(pair[side], Vec_IntEntry(map, lit >> 1) ^ (lit & 1));
        }
        Gia_ManHashStop(pair[side]); clean = Gia_ManCleanup(pair[side]); Gia_ManStop(pair[side]); pair[side] = clean;
    }
    status = Acec2_RefineProductLimit(pair, NULL, NULL, NULL, values, NULL,
        width, &m->Pars, m->Deadline, NULL, 20, 4000000);
    result = status == 1 ? 1 : status == 2 ? 0 : -1;
finish:
    for ( side = 0; side < 2; side++ ) if ( pair[side] ) Gia_ManStop(pair[side]);
    Vec_IntFree(map); Vec_WrdFree(values);
    if ( Acec2_Stopped(m) ) result = -1;
    m->nWeightedTruthProved += result == 1; m->nWeightedTruthDisproved += result == 0;
    m->nWeightedTruthLimits += result < 0;
    return result;
}

/**Function*************************************************************

  Synopsis    [Proves observed bits through completed arithmetic words.]

  Description [Only previously unobserved positions may change. A complete polynomial
  proof of the resulting words establishes every retained output equality.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CompletedProof( Acec2_Man_t ** a, Vec_Int_t ** vObserved, Acec2_Par_t * pPars, abctime Deadline )
{
    Gia_Man_t * g[2] = {NULL, NULL};
    Vec_Int_t * vRules[2] = {NULL, NULL};
    Acec2_Man_t * b[2] = {NULL, NULL};
    Acec2_Par_t Pars = *pPars;
    int side, i, lit, missing = 0, result = -1;
    for ( side = 0; side < 2; side++ )
    {
        if ( a[side]->fStopped ) goto finish;
        Vec_IntForEachEntry(vObserved[side], lit, i) missing += lit < 0;
    }
    if ( !missing ) goto finish;
    for ( side = 0; side < 2; side++ ) g[side] = Acec2_CompleteWord(a[side], vObserved[side], Deadline, &vRules[side]);
    if ( (!g[0] && !g[1]) || Acec2_Stop(pPars, Deadline) ) goto finish;
    Pars.fVerbose = 0;
    for ( side = 0; side < 2; side++ )
    {
        if ( !g[side] ) continue;
        b[side] = Acec2_AnalyzeCells(g[side], &Pars, Deadline);
        if ( !b[side] || Acec2_Stop(pPars, Deadline) ) goto finish;
        b[side]->vExtraRules = vRules[side]; vRules[side] = NULL;
        b[side]->Pars.fVerbose = pPars->fVerbose;
        b[side]->nPolyTermLimit = a[side]->nPolyTermLimit;
    }
    result = Acec2_PolyCompareQuiet(b[0] ? b[0] : a[0], b[1] ? b[1] : a[1], Deadline);
    if ( pPars->fVerbose ) Abc_Print(1, "Completed arithmetic word: unobserved positions = %d, proof = %d.\n", missing, result);
finish:
    for ( side = 0; side < 2; side++ ) { Acec2_Free(b[side]); if ( g[side] ) Gia_ManStop(g[side]); Vec_IntFreeP(&vRules[side]); }
    return result == 1 ? 1 : -1;
}

/**Function*************************************************************

  Synopsis    [Refines candidates with a validated component counterexample.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_BoundaryRefine( Gia_Man_t ** g, Acec2_WordSim_t ** s, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts,
                                Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Width, Gia_Man_t * pModel,
                                Acec2_Par_t * pPars, abctime Deadline, Abc_Cex_t * pCex )
{
    int i, side;
    if ( !pCex || pCex->nRegs || pCex->iFrame || pCex->nPis != Gia_ManCiNum(g[0]) ||
         pCex->nPis != Gia_ManCiNum(g[1]) || pCex->nPis != Vec_WrdSize(vValues) ||
         pCex->nBits < pCex->nPis || pCex->iPo < 0 || pCex->iPo >= Gia_ManCoNum(g[0]) ||
         pCex->iPo >= Gia_ManCoNum(g[1]) || Acec2_Stop(pPars, Deadline) ) return -1;
    if ( Acec2_CexOutput(g[0], pCex, pCex->iPo) == Acec2_CexOutput(g[1], pCex, pCex->iPo) ) return -1;
    for ( i = 0; i < Vec_WrdSize(vValues); i++ )
        Vec_WrdWriteEntry(vValues, i, Abc_InfoHasBit(pCex->pData, i) ? ~(word)0 : 0);
    Acec2_ModelPatterns(vOps, hCuts, vValues, vExpected, Width, pModel);
    for ( side = 0; side < 2; side++ ) Acec2_WordSimulate(s[side], vValues, vExpected, 1);
    return 2;
}

/**Function*************************************************************

  Synopsis    [Uses operand ordering for a bounded BDD proof and refinement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_BddCached( Acec2_Man_t * m, Gia_Man_t ** g, Vec_Int_t * order, Acec2_Par_t * pars,
                           abctime Deadline, Abc_Cex_t ** ppCex, int Limit )
{
    Vec_Int_t empty = {0}, * roots[2] = { order ? order : &empty, &empty };
    Acec2_Par_t keyPars = *pars;
    int cache, result, limited = 0;
    if ( ppCex ) *ppCex = NULL;
    if ( Acec2_Stop(pars, Deadline) ) return -1;
    // Only the exact extracted gates and variable order determine this
    // attempt. Source proposal choices and polynomial tiers do not.
    keyPars.nCecPolyLimit = 0;
    cache = Acec2_BoundaryCache(m, g, roots, NULL, Gia_ManCoNum(g[0]), ACEC2_CACHE_BDD, 0);
    if ( Acec2_ProofCacheRead(m->vFailedProofs, cache, Limit, &keyPars) )
    { m->nBddHits++; return -1; }
    m->nBddAttempts++;
    result = Acec2_ProveBddLimit(g, order, pars, Deadline, ppCex, Limit, &limited);
    if ( limited && !Acec2_Stop(pars, Deadline) )
    {
        m->nBddLimits++;
        Acec2_ProofCacheWrite(m->vFailedProofs, cache, Limit, &keyPars, -1, 1);
    }
    return result;
}

/**Function*************************************************************

  Synopsis    [Uses operand order for a cached BDD attempt and refinement.]

  Description [Only deterministic exhaustion is retained; a deadline or
  caller cancellation never becomes a permanent failure.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_BoundaryBdd( Acec2_Man_t * m, Gia_Man_t ** g, Acec2_WordSim_t ** s, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts,
                             Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Width, Gia_Man_t * pModel,
                             Acec2_Par_t * pPars, abctime Deadline )
{
    Vec_Int_t * vOrder = Vec_IntAlloc(Hsh_Int1ManEntryNum(hCuts));
    Abc_Cex_t * pCex = NULL;
    int i, side, lit, result;
    for ( i = 0; i < Abc_MaxInt(Vec_IntSize(vOps[0]), Vec_IntSize(vOps[1])); i++ )
        for ( side = 0; side < 2; side++ )
            if ( i < Vec_IntSize(vOps[side]) && (lit = Vec_IntEntry(vOps[side], i)) >= 2 )
                Vec_IntPush(vOrder, Acec2_IndexLookup(hCuts, lit >> 1));
    Vec_IntReverseOrder(vOrder);
    result = Acec2_BddCached(m, g, vOrder, pPars, Deadline, &pCex, 1000000);
    Vec_IntFree(vOrder);
    if ( result == 0 ) result = Acec2_BoundaryRefine(g, s, vOps, hCuts, vValues, vExpected, Width, pModel, pPars, Deadline, pCex);
    if ( pCex ) Abc_CexFree(pCex);
    return result;
}

/**Function*************************************************************

  Synopsis    [Indexes an exact extracted proof problem and its effort budget.]

  Description [Completed results and deterministic effort limits are cached. Source
  bindings, phases and every output are represented by the extracted gates;
  a changed cut or root therefore has a different key. Storage is bounded.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_BoundaryCache( Acec2_Man_t * m, Gia_Man_t ** g, Vec_Int_t ** vRoots, Vec_Int_t ** vOps,
                                  int Width, int fModel, int Choice )
{
    Vec_Int_t * v; Gia_Obj_t * o; int side, i, id, before;
    if ( (ABC_INT64_T)Gia_ManObjNum(g[0])+Gia_ManObjNum(g[1]) > 100000 || m->nFailedProofWords >= 1000000 ) return -1;
    if ( !m->hFailedProofs )
    { m->hFailedProofs = Hsh_VecManStart(100); m->vFailedProofs = Vec_IntAlloc(100); }
    v = Vec_IntAlloc(100);
    Vec_IntPushThree(v, Choice, Width, fModel);
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntPush(v, Vec_IntSize(vRoots[side])); Vec_IntAppend(v, vRoots[side]);
        Vec_IntPush(v, vOps ? Vec_IntSize(vOps[side]) : -1);
        if ( vOps ) Vec_IntAppend(v, vOps[side]);
    }
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntPushThree(v, Gia_ManObjNum(g[side]), Gia_ManCiNum(g[side]), Gia_ManCoNum(g[side]));
        Gia_ManForEachAnd(g[side], o, i)
        {
            Vec_IntPush(v, i); Vec_IntPushTwo(v, Gia_ObjFaninLit0p(g[side], o), Gia_ObjFaninLit1p(g[side], o));
            Vec_IntPush(v, Gia_ObjIsXor(o));
            if ( Gia_ObjIsMux(g[side], o) ) { Vec_IntFree(v); return -1; }
        }
        Gia_ManForEachCo(g[side], o, i) Vec_IntPush(v, Gia_ObjFaninLit0p(g[side], o));
    }
    before = Hsh_VecSize(m->hFailedProofs); id = Hsh_VecManAdd(m->hFailedProofs, v);
    if ( id == before ) { Vec_IntPushFour(m->vFailedProofs, 0, 0, 0, 0); m->nFailedProofWords += Vec_IntSize(v); }
    Vec_IntFree(v); return id;
}

/**Function*************************************************************

  Synopsis    [Proves simulated word correspondences and commits exact aliases.]

  Description [Only exhaustive simulation, BDD, SAT, or polynomial proofs
  authorize a replacement. Counterexamples refine candidate boundaries.]

  SideEffects [Updates caller-owned replacement maps.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveBoundaryMode( Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                               Acec2_WordSim_t ** s, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts,
                               Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Width,
                               Acec2_Par_t * pPars, abctime Deadline, int * pnWords, Gia_Man_t * pModel, int Mode )
{
    Gia_Man_t * g[2] = {NULL, NULL}; Acec2_Man_t * a[2] = {NULL, NULL};
    Vec_Int_t * vRoots[2] = {NULL, NULL};
    Acec2_Par_t Pars = *pPars;
    int cache, i, j, k, l, side, lit, choice, nRefines = 0, prefix = 0, best = Mode, nProof, nCommit, nShared, part, testWidth, x, y, result, pairs, merged = 0, rejected, effort;
    Vec_Int_t * v0, * v1;
    Abc_Cex_t * pCex = NULL;
    abctime stop;
    for ( i = 0; i < Width; i++ )
        prefix += Vec_IntSize(Vec_WecEntry(s[0]->vCandidates, Mode*Width+i)) && Vec_IntSize(Vec_WecEntry(s[1]->vCandidates, Mode*Width+i));
    if ( pModel && pPars->fVerbose ) Abc_Print(1, "Weighted region proposal: inputs = %d, width = %d, candidate bits = %d.\n", Hsh_Int1ManEntryNum(hCuts), Width, prefix);
    if ( prefix < 4 || Acec2_Stop(pPars, Deadline) ) goto finish;
    for ( i = 0; i < Width; i++ )
        if ( !Vec_IntSize(Vec_WecEntry(s[0]->vCandidates, best*Width+i)) || !Vec_IntSize(Vec_WecEntry(s[1]->vCandidates, best*Width+i)) )
            for ( side = 0; side < 2; side++ ) Vec_IntClear(Vec_WecEntry(s[side]->vCandidates, best*Width+i));
    // Keep the complete observed word for the first proof attempts. If a
    // shared low word belongs to a different implementation over these
    // operands, the last attempt can leave it open for sum completion.
    for ( i = 0; i < Width; i++ )
    {
        v0 = Vec_WecEntry(s[0]->vCandidates, best*Width+i);
        v1 = Vec_WecEntry(s[1]->vCandidates, best*Width+i); pairs = 0;
        Vec_IntForEachEntry(v0, x, k)
        {
            j = Vec_IntEntry(vReplaces[0], x >> 1); if ( j < 0 ) j = Vec_IntEntry(vMaps[0], x >> 1);
            Vec_IntForEachEntry(v1, y, l)
            {
                lit = Vec_IntEntry(vReplaces[1], y >> 1); if ( lit < 0 ) lit = Vec_IntEntry(vMaps[1], y >> 1);
                if ( (j ^ (x & 1)) == (lit ^ (y & 1)) ) { pairs = 1; break; }
            }
            if ( pairs ) break;
        }
        if ( !pairs ) break;
    }
    nShared = i >= 4 ? i : 0;
    for ( nProof = Width; nProof > 0; nProof-- )
        if ( Vec_IntSize(Vec_WecEntry(s[0]->vCandidates, best*Width+nProof-1)) ) break;
    for ( choice = 0; choice < 3 && !Acec2_Stop(pPars, Deadline); choice++ )
    {
        rejected = effort = 0;
        if ( choice == 2 )
            for ( j = 0; j < nShared; j++ )
                for ( side = 0; side < 2; side++ ) Vec_IntClear(Vec_WecEntry(s[side]->vCandidates, best*Width+j));
        nCommit = nProof;
        for ( side = 0; side < 2; side++ ) g[side] = Acec2_ExtractWord(s[side], best, Width, nProof, Hsh_Int1ManEntryNum(hCuts), &vRoots[side], vOps, hCuts, choice, pModel);
        if ( !g[0] || !g[1] ) goto next_choice;
        pairs = 0;
        for ( i = 0; i < nProof; i++ )
        {
            x = Vec_IntEntry(vRoots[0], i); y = Vec_IntEntry(vRoots[1], i);
            if ( x < 0 || y < 0 ) continue;
            j = Vec_IntEntry(vReplaces[0], x >> 1); if ( j < 0 ) j = Vec_IntEntry(vMaps[0], x >> 1);
            lit = Vec_IntEntry(vReplaces[1], y >> 1); if ( lit < 0 ) lit = Vec_IntEntry(vMaps[1], y >> 1);
            pairs += (j ^ (x & 1)) != (lit ^ (y & 1));
        }
        if ( !pairs ) goto next_choice;
        cache = Acec2_BoundaryCache(m[0], g, vRoots, vOps, Width, pModel != NULL, choice);
        if ( Acec2_ProofCacheRead(m[0]->vFailedProofs, cache, pPars->nBTLimit, pPars) )
        { m[0]->nFailedProofHits++; goto next_choice; }
        result = Acec2_RefineProduct(g, s, vOps, hCuts, vValues, vExpected, Width, pPars, Deadline, pModel);
        if ( result < 0 ) goto finish;
        if ( result == 2 )
        {
            if ( pModel && pPars->fVerbose ) Abc_Print(1, "Weighted region boundary refinement %d.\n", nRefines+1);
            if ( ++nRefines > 8 ) goto finish;
            choice--; goto next_choice;
        }
        if ( result == 1 ) goto proved;
        if ( vOps && pModel )
        {
            result = Acec2_BoundaryBdd(m[0], g, s, vOps, hCuts, vValues, vExpected, Width, pModel, pPars, Deadline);
            if ( result == 1 ) goto proved;
            if ( result == 2 ) { if ( ++nRefines > 8 ) goto finish; choice--; goto next_choice; }
            if ( Acec2_Stop(pPars, Deadline) ) goto finish;
        }
        if ( pModel && !vOps )
        {
            Gia_Man_t * pMiter = Gia_ManMiter(g[0], g[1], 0, 1, 0, 0, 0);
            result = Acec2_ProveBounded(pMiter, pPars, Deadline, 4);
            if ( pPars->fVerbose ) Abc_Print(1, "Component CEC: inputs = %d, bits = %d, result = %d.\n", Hsh_Int1ManEntryNum(hCuts), prefix, result);
            Gia_ManStop(pMiter);
            if ( result == 1 ) goto proved;
            if ( Acec2_Stop(pPars, Deadline) ) goto finish;
        }
        stop = Deadline;
        Pars.fVerbose = 0;
        for ( side = 0; side < 2; side++ )
        {
            a[side] = Acec2_AnalyzeCells(g[side], &Pars, Deadline);
            if ( !a[side] || Acec2_Stop(pPars, stop) )
            {
                if ( Acec2_Stop(pPars, Deadline) ) goto finish;
                goto next_choice;
            }
            a[side]->Pars.fVerbose = pPars->fVerbose;
            a[side]->nPolyTermLimit = Abc_MaxInt(20000, (int)Abc_MinInt(500000, 8*Abc_MinInt(Width, 250)*Abc_MinInt(Width, 250)));
        }
        result = Acec2_PolyCompareCex(a[0], a[1], stop, &pCex);
        effort |= a[0]->fPolyEffortLimit || a[1]->fPolyEffortLimit;
        rejected = result == 0;
        if ( pPars->fVerbose ) Abc_Print(1, "%s boundary: inputs = %d, bits = %d, proof = %s.\n",
            pModel ? "Weighted region" : "Product", Hsh_Int1ManEntryNum(hCuts), prefix,
            result == 1 ? "equivalent" : result == 0 ? "proposal rejected" : "limit");
        if ( result == 0 && Acec2_BoundaryRefine(g, s, vOps, hCuts, vValues, vExpected, Width, pModel, pPars, Deadline, pCex) == 2 )
        {
            Abc_CexFree(pCex); pCex = NULL;
            if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic boundary refined by an exact polynomial counterexample.\n");
            if ( ++nRefines > 8 ) goto finish;
            choice--; goto next_choice;
        }
        if ( pCex ) { Abc_CexFree(pCex); pCex = NULL; }
        if ( result != 1 && !Acec2_Stop(pPars, Deadline) )
            for ( part = 0; part < 2; part++ )
            {
                testWidth = part ? nProof/2 : nProof-1; pairs = 0;
                if ( testWidth < 4 ) continue;
                for ( i = 0; i < testWidth; i++ )
                {
                    x = Vec_IntEntry(vRoots[0], i); y = Vec_IntEntry(vRoots[1], i);
                    if ( x < 0 || y < 0 ) continue;
                    j = Vec_IntEntry(vReplaces[0], x >> 1); if ( j < 0 ) j = Vec_IntEntry(vMaps[0], x >> 1);
                    lit = Vec_IntEntry(vReplaces[1], y >> 1); if ( lit < 0 ) lit = Vec_IntEntry(vMaps[1], y >> 1);
                    pairs += (j ^ (x & 1)) != (lit ^ (y & 1));
                }
                if ( !pairs ) continue;
                stop = Deadline;
                i = Acec2_PolyComparePrefix(a[0], a[1], testWidth, stop);
                effort |= a[0]->fPolyEffortLimit || a[1]->fPolyEffortLimit;
                if ( i != 1 ) continue;
                nCommit = testWidth;
                if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic boundary prefix: proved %d / %d low bits.\n", nCommit, nProof);
                goto proved;
            }
        if ( result != 1 && !Acec2_Stop(pPars, Deadline) && Acec2_CompletedProof(a, vRoots, pPars, Deadline) == 1 ) result = 1;
        effort |= a[0]->fPolyEffortLimit || a[1]->fPolyEffortLimit;
        if ( result != 1 && vOps && !pModel && !Acec2_Stop(pPars, Deadline) )
        {
            result = Acec2_BoundaryBdd(m[0], g, s, vOps, hCuts, vValues, vExpected, Width, pModel, pPars, Deadline);
            if ( result == 2 ) { if ( ++nRefines > 8 ) goto finish; choice--; goto next_choice; }
        }
        if ( result != 1 )
        {
            if ( Acec2_Stop(pPars, Deadline) ) goto finish;
            Acec2_ProofCacheWrite(m[0]->vFailedProofs, cache, pPars->nBTLimit, pPars, rejected && !effort ? 0 : -1, effort);
            goto next_choice;
        }
proved:
        for ( i = 0; i < nCommit; i++ )
        {
            x = Vec_IntEntry(vRoots[0], i); y = Vec_IntEntry(vRoots[1], i);
            if ( x < 0 || y < 0 ) continue;
            j = Vec_IntEntry(vReplaces[0], x >> 1); if ( j < 0 ) j = Vec_IntEntry(vMaps[0], x >> 1);
            lit = Vec_IntEntry(vReplaces[1], y >> 1); if ( lit < 0 ) lit = Vec_IntEntry(vMaps[1], y >> 1);
            j ^= x & 1; lit ^= y & 1;
            if ( j == lit ) continue;
            lit = Abc_MinInt(j, lit);
            if ( x >= 2 ) Vec_IntWriteEntry(vReplaces[0], x >> 1, lit ^ (x & 1));
            if ( y >= 2 ) Vec_IntWriteEntry(vReplaces[1], y >> 1, lit ^ (y & 1));
            merged++;
        }
        (*pnWords)++;
        goto finish;
next_choice:
        for ( side = 0; side < 2; side++ )
        { Acec2_Free(a[side]); a[side] = NULL; if ( g[side] ) Gia_ManStop(g[side]); g[side] = NULL; Vec_IntFreeP(&vRoots[side]); }
    }
finish:
    for ( side = 0; side < 2; side++ )
    { Acec2_Free(a[side]); if ( g[side] ) Gia_ManStop(g[side]); Vec_IntFreeP(&vRoots[side]); }
    return merged;
}

/**Function*************************************************************

  Synopsis    [Checks every proposed arithmetic interpretation of a shared cut.]

  Description [Signed and unsigned products can coexist over the same bits.
  Proving one interpretation must not hide the remaining words. Candidate
  coverage determines the order; every committed equality has its own proof.]

  SideEffects [Updates caller-owned replacement maps after exact proofs.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveBoundary( Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                               Acec2_WordSim_t ** s, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts,
                               Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Width,
                               Acec2_Par_t * pPars, abctime Deadline, int * pnWords, Gia_Man_t * pModel )
{
    int counts[4] = {0, 0, 0, 0}, order[4] = {0, 1, 2, 3};
    int i, j, mode, merged = 0;
    for ( mode = 0; mode < 4; mode++ )
        for ( i = 0; i < Width; i++ )
            counts[mode] += Vec_IntSize(Vec_WecEntry(s[0]->vCandidates, mode*Width+i)) && Vec_IntSize(Vec_WecEntry(s[1]->vCandidates, mode*Width+i));
    for ( i = 1; i < 4; i++ )
        for ( j = i; j > 0 && counts[order[j]] > counts[order[j-1]]; j-- ) ABC_SWAP(int, order[j], order[j-1]);
    for ( i = 0; i < 4 && !Acec2_Stop(pPars, Deadline); i++ )
    {
        mode = order[i];
        if ( counts[mode] < 4 ) continue;
        merged += Acec2_ProveBoundaryMode(m, vMaps, vReplaces, s, vOps, hCuts, vValues, vExpected, Width, pPars, Deadline, pnWords, pModel, mode);
    }
    return merged;
}

/**Function*************************************************************

  Synopsis    [Proves a proposed component pair before installing root aliases.]

  Description [The proof is universal over the shared operand cut. Failure
  only rejects this proposal; it is never an inequivalence result for the
  original designs.]

  SideEffects [Updates only caller-owned replacement maps.]

  SeeAlso     []

***********************************************************************/
static int Acec2_TryProduct( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                            Vec_Int_t ** vOps, int Width, Acec2_Par_t * pPars, abctime Deadline, int * pnWords, int Stage, Hsh_VecMan_t * hTried, int * pnAttempts, Acec2_Templ_t * pTemplates, int * pPrefix )
{
    Hsh_Int1Man_t * hCuts = Hsh_Int1ManStart(100);
    Acec2_WordSim_t * s[2] = {NULL, NULL};
    Vec_Wrd_t * vValues = NULL, * vExpected = NULL;
    Gia_Obj_t * o;
    Acec2_WordSim_t * temp;
    int i, j, side, lit, round, mode, pass, prefix, nRounds, merged = 0;
    Vec_Int_t * vKey = Vec_IntAlloc(Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1])+3);
    int first = 0, oldSize = Hsh_VecSize(hTried), keyId;
    word state = ABC_CONST(0x19C69D74E8237A5B);
    if ( pPrefix ) *pPrefix = 0;
    if ( Vec_IntSize(vOps[0]) > Vec_IntSize(vOps[1]) ) first = 1;
    else if ( Vec_IntSize(vOps[0]) == Vec_IntSize(vOps[1]) )
        for ( i = 0; i < Vec_IntSize(vOps[0]); i++ )
            if ( Vec_IntEntry(vOps[0], i) != Vec_IntEntry(vOps[1], i) )
            { first = Vec_IntEntry(vOps[0], i) > Vec_IntEntry(vOps[1], i); break; }
    Vec_IntPush(vKey, Width);
    for ( side = 0; side < 2; side++ )
    { Vec_IntPush(vKey, Vec_IntSize(vOps[side ^ first])); Vec_IntAppend(vKey, vOps[side ^ first]); }
    keyId = Hsh_VecManAdd(hTried, vKey); Vec_IntFree(vKey);
    if ( keyId < oldSize ) goto finish;
    (*pnAttempts)++;
    if ( pPars->fVerbose ) Abc_Print(1, "Product proposal: operands = %d x %d, width = %d.\n", Vec_IntSize(vOps[0]), Vec_IntSize(vOps[1]), Width);
    if ( Stage == ACEC2_PRODUCT_TEMPLATE ) merged = Acec2_TemplateMatch(pNew, vMaps, vOriginals, vReplaces, vOps, Width, pPars, Deadline, pnWords, pTemplates);
    if ( Stage == ACEC2_PRODUCT_SHIFTED ) merged = Acec2_TemplateShifted(pNew, vMaps, vOriginals, vReplaces, vOps, Width, pPars, Deadline, pnWords, pTemplates);
    if ( Stage < ACEC2_PRODUCT_CERTIFICATE || Acec2_Stop(pPars, Deadline) ) goto finish;
    if ( Stage == ACEC2_PRODUCT_CERTIFICATE )
    {
        merged = Acec2_CertifyProducts(pNew, m, vMaps, vReplaces, vOps, Width, pPars, Deadline, pnWords, pPrefix);
        goto finish;
    }
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vOps[side], lit, i) Acec2_IndexAdd(hCuts, lit >> 1);
    vValues = Vec_WrdStart(Hsh_Int1ManEntryNum(hCuts)); vExpected = Vec_WrdStart(4*Width);
    for ( side = 0; side < 2; side++ )
    { s[side] = Acec2_WordSimCached(m[side], vMaps[side], hCuts, Width); Acec2_WordPrioritize(s[side], m[side]); }
    nRounds = (256+25+10*(Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1]))+63)/64;
    for ( pass = 0; pass < 2; pass++ )
    {
        if ( pass )
        {
            // Some unused high operand bits cancel only algebraically. Admit
            // other CIs as independent variables and prove their cancellation
            // on the extracted cones; preserve the operand-domain boundary.
            for ( side = 0; side < 2; side++ )
                Gia_ManForEachCi(m[side]->pGia, o, i)
                    Acec2_IndexAdd(hCuts, Vec_IntEntry(vMaps[side], Gia_ObjId(m[side]->pGia, o)) >> 1);
            Vec_WrdFill(vValues, Hsh_Int1ManEntryNum(hCuts), 0);
            for ( side = 0; side < 2; side++ )
            {
                temp = Acec2_WordSimCached(m[side], vMaps[side], hCuts, Width);
                Vec_IntFree(temp->vBoundary); temp->vBoundary = Vec_IntDup(s[side]->vBoundary); temp->pMan = s[side]->pMan;
                Acec2_WordSimStop(s[side]); s[side] = temp;
            }
        }
        for ( round = 0; round < nRounds; round++ )
        {
            if ( Acec2_Stop(pPars, Deadline) ) goto finish;
            if ( pass )
                for ( i = 0; i < Vec_WrdSize(vValues); i++ )
                { Acec2_Random(&state); Vec_WrdWriteEntry(vValues, i, state); }
            Acec2_OperandPatterns(vOps, hCuts, vValues, round, &state);
            Acec2_ProductPatterns(vOps, hCuts, vValues, vExpected, Width);
            for ( side = 0; side < 2; side++ ) Acec2_WordSimulate(s[side], vValues, vExpected, round);
        }
        prefix = 0;
        for ( mode = 0; mode < 4; mode++ )
        {
            j = 0;
            for ( i = 0; i < Width; i++ )
                j += Vec_IntSize(Vec_WecEntry(s[0]->vCandidates, mode*Width+i)) && Vec_IntSize(Vec_WecEntry(s[1]->vCandidates, mode*Width+i));
            if ( j > prefix ) prefix = j;
        }
        if ( prefix == Width ) break;
    }
    merged = Acec2_ProveBoundary(m, vMaps, vReplaces, s, vOps, hCuts, vValues, vExpected, Width, pPars, Deadline, pnWords, NULL);
finish:
    for ( side = 0; side < 2; side++ )
        Acec2_WordSimStop(s[side]);
    Vec_WrdFreeP(&vValues); Vec_WrdFreeP(&vExpected); Hsh_Int1ManStop(hCuts);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Proposes fixed low operand bits from linear partial products.]

  Description [An operand bit equal to one contributes the other operand's
  bits directly to the compressor tree. Their ranks can reveal fixed low
  positions missing from the graph of two-input bit products. This is only
  proposal evidence; component certification remains mandatory.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_OperandPrefix( Acec2_Man_t * m, Vec_Int_t * vMap, int Tree,
                               Vec_Int_t * vOther, int Offset, int * pMask )
{
    unsigned char seen[4][256] = {{0}};
    int counts[4] = {0, 0, 0, 0};
    Vec_Int_t * vLeaves = Vec_WecEntry(m->vLeaves, Tree);
    int i, j, lit, other, delta, shift = 0;
    *pMask = 0;
    if ( Vec_IntSize(vOther) > 256 ) return 0;
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        lit = Vec_IntEntry(vLeaves, i); lit = Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1);
        if ( lit < 2 ) continue;
        Vec_IntForEachEntry(vOther, other, j)
        {
            if ( (lit >> 1) != (other >> 1) ) continue;
            delta = Offset+j-Vec_IntEntry(vLeaves, i+1);
            if ( delta < 1 || delta > 4 || seen[delta-1][j] ) continue;
            seen[delta-1][j] = 1; counts[delta-1]++;
        }
    }
    for ( i = 0; i < 4; i++ ) if ( counts[i] >= 2 ) shift = i+1;
    for ( i = 0; i < shift; i++ ) if ( counts[i] >= 2 ) *pMask |= 1 << (shift-i-1);
    return shift;
}

/**Function*************************************************************

  Synopsis    [Proposes a missing high operand bit from surviving bit products.]

  Description [A top sum without a carry cell may hide its last partial
  product from the selected region. Partners of known low operand bits,
  ordered by proximity to the existing bus, provide bounded candidates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_OperandTop( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vColors, Vec_Int_t * vOwn, Vec_Int_t * vOther )
{
    Vec_Int_t * v = Vec_IntAlloc(4);
    Gia_Obj_t * o;
    int refs[3], nRefs = 0, last = Vec_IntEntryLast(vOwn) >> 1, i, j, k, a, b, lit, candidate, score, oldScore;
    Vec_IntForEachEntry(vOther, lit, i)
        if ( lit >= 2 && nRefs < 3 ) refs[nRefs++] = lit;
    Gia_ManForEachAnd(m->pGia, o, i)
    {
        if ( Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
        a = Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o);
        b = Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o);
        candidate = -1;
        for ( j = 0; j < nRefs; j++ )
            if ( a == refs[j] ) candidate = b;
            else if ( b == refs[j] ) candidate = a;
        if ( candidate < 2 || Vec_IntEntry(vColors, candidate >> 1) != 3 || Vec_IntFind(v, candidate) >= 0 ) continue;
        Vec_IntForEachEntry(vOwn, lit, j) if ( (lit >> 1) == (candidate >> 1) ) break;
        if ( j < Vec_IntSize(vOwn) ) continue;
        score = abs((candidate >> 1)-last);
        for ( j = 0; j < Vec_IntSize(v); j++ )
        {
            oldScore = abs((Vec_IntEntry(v, j) >> 1)-last);
            if ( score < oldScore || (score == oldScore && candidate < Vec_IntEntry(v, j)) ) break;
        }
        if ( j == 4 ) continue;
        if ( Vec_IntSize(v) < 4 ) Vec_IntPush(v, candidate);
        for ( k = Vec_IntSize(v)-1; k > j; k-- ) Vec_IntWriteEntry(v, k, Vec_IntEntry(v, k-1));
        Vec_IntWriteEntry(v, j, candidate);
    }
    return v;
}

/**Function*************************************************************

  Synopsis    [Checks the variable product and evidence for fixed operand bits.]

  Description [Independent fixed prefixes are also tried together. The
  operand cut is still derived solely from the gate-level arithmetic cover.]

  SideEffects [Installs only certified aliases.]

  SeeAlso     []

***********************************************************************/
static int Acec2_TryProducts( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                             Vec_Int_t ** vOps, int Width, Acec2_Par_t * pPars, abctime Deadline, int * pnWords,
                             int Stage, Hsh_VecMan_t * hTried, int * pnAttempts, Acec2_Templ_t * pTemplates,
                             int Side, int Tree, int Offset, Vec_Int_t * vColors )
{
    Vec_Int_t * vArgs[2], * vTop[2];
    int shift[2], mask[2], side, i, choice, extra, fill, width, merged = 0, candidate, prefix, extended;
    merged += Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vOps, Width, pPars, Deadline, pnWords, Stage, hTried, pnAttempts, pTemplates, &prefix);
    // A low-half certificate can hide a missing high operand bit. Propose
    // surviving bit-product partners before shrinking either operand. These
    // extensions require fresh exact certificates, including signedness.
    if ( Stage == ACEC2_PRODUCT_CERTIFICATE && prefix == Vec_IntSize(vOps[0]) && prefix == Vec_IntSize(vOps[1]) &&
         prefix < Width && Width+2 <= pPars->nMaxWidth && !Acec2_Stop(pPars, Deadline) )
    {
        for ( side = 0; side < 2; side++ ) vTop[side] = Acec2_OperandTop(m[Side], vMaps[Side], vColors, vOps[side], vOps[!side]);
        for ( choice = 3; choice > 0 && !Acec2_Stop(pPars, Deadline); choice-- )
            for ( i = 0; i < 4 && !Acec2_Stop(pPars, Deadline); i++ )
            {
                if ( ((choice & 1) && i >= Vec_IntSize(vTop[0])) || ((choice & 2) && i >= Vec_IntSize(vTop[1])) ) break;
                width = Width;
                for ( side = 0; side < 2; side++ )
                {
                    vArgs[side] = Vec_IntDup(vOps[side]);
                    if ( choice & (1 << side) ) { Vec_IntPush(vArgs[side], Vec_IntEntry(vTop[side], i)); width++; }
                }
                merged += Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vArgs, width, pPars, Deadline, pnWords, Stage, hTried, pnAttempts, pTemplates, &extended);
                Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]);
                if ( extended > prefix ) goto extended_operand;
            }
extended_operand:
        Vec_IntFree(vTop[0]); Vec_IntFree(vTop[1]);
    }
    // Rebuild after a completed certificate before proposing narrower buses.
    // The next pass can try them if unresolved bits remain.
    if ( Stage == ACEC2_PRODUCT_CERTIFICATE && merged ) return merged;
    if ( Stage == ACEC2_PRODUCT_SHIFTED ) return merged;
    // Overlapping regions can add an unrelated high bit to a plausible bus.
    // Check bounded prefixes as separate proposals, with their own proofs.
    if ( Stage == ACEC2_PRODUCT_CERTIFICATE )
        for ( choice = 1; choice < 4 && !Acec2_Stop(pPars, Deadline); choice++ )
        {
            if ( Vec_IntSize(vOps[0]) < 4 || Vec_IntSize(vOps[1]) < 4 ) break;
            for ( side = 0; side < 2; side++ )
            {
                vArgs[side] = Vec_IntDup(vOps[side]);
                if ( choice & (1 << side) ) Vec_IntPop(vArgs[side]);
            }
            width = Vec_IntSize(vArgs[0])+Vec_IntSize(vArgs[1]);
            merged += Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vArgs, width, pPars, Deadline, pnWords, Stage, hTried, pnAttempts, pTemplates, NULL);
            Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]);
        }
    for ( side = 0; side < 2; side++ ) shift[side] = Acec2_OperandPrefix(m[Side], vMaps[Side], Tree, vOps[!side], Offset, &mask[side]);
    for ( choice = 1; choice < 4 && !Acec2_Stop(pPars, Deadline); choice++ )
    {
        if ( ((choice & 1) && !shift[0]) || ((choice & 2) && !shift[1]) ) continue;
        for ( extra = 0; extra < (choice == 3 ? 1 : 2) && !Acec2_Stop(pPars, Deadline); extra++ )
        for ( fill = 0; fill < (extra ? 2 : 1) && !Acec2_Stop(pPars, Deadline); fill++ )
        {
            width = Width;
            for ( side = 0; side < 2; side++ )
            {
                vArgs[side] = Vec_IntAlloc(Vec_IntSize(vOps[side])+5);
                if ( choice & (1 << side) )
                {
                    for ( i = 0; i < shift[side]; i++ ) Vec_IntPush(vArgs[side], (mask[side] >> i) & 1);
                    if ( extra ) Vec_IntPush(vArgs[side], fill);
                    width += shift[side]+extra;
                }
                Vec_IntAppend(vArgs[side], vOps[side]);
            }
            if ( width <= pPars->nMaxWidth )
            {
                if ( pPars->fVerbose ) Abc_Print(1, "Fixed operand prefix: widths = %d / %d, constants = %d / %d.\n", (choice & 1) ? shift[0] : 0, (choice & 2) ? shift[1] : 0, mask[0], mask[1]);
                merged += Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vArgs, width, pPars, Deadline, pnWords, Stage, hTried, pnAttempts, pTemplates, NULL);
            }
            Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]);
        }
    }
    if ( Stage == ACEC2_PRODUCT_TEMPLATE && !merged && Width < pPars->nMaxWidth && !Acec2_Stop(pPars, Deadline) &&
         Vec_IntEntry(m[Side]->vWidths, Tree)-Offset <= Abc_MaxInt(Vec_IntSize(vOps[0]), Vec_IntSize(vOps[1]))+1 )
    {
        for ( side = 0; side < 2; side++ ) vTop[side] = Acec2_OperandTop(m[Side], vMaps[Side], vColors, vOps[side], vOps[!side]);
        for ( side = 0; side < 2 && !Acec2_Stop(pPars, Deadline); side++ )
            Vec_IntForEachEntry(vTop[side], candidate, i)
            {
                if ( Acec2_Stop(pPars, Deadline) ) break;
                vArgs[side] = Vec_IntDup(vOps[side]); vArgs[!side] = Vec_IntDup(vOps[!side]);
                Vec_IntPush(vArgs[side], candidate);
                merged += Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vArgs, Width+1, pPars, Deadline, pnWords, Stage, hTried, pnAttempts, pTemplates, NULL);
                Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]);
                if ( merged ) break;
            }
        Vec_IntFree(vTop[0]); Vec_IntFree(vTop[1]);
    }
    return merged;
}

/**Function*************************************************************

  Synopsis    [Builds weighted-leaf and observed-root word proposals.]

  Description [Both orientations are simulated over independent cut inputs. In
  shared or truncated regions, individual observed roots also propose a
  result word; every resulting correspondence still requires an exact proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_RegionModel( Acec2_WordSim_t * s, Acec2_Man_t * m, int Tree, int nInputs, int Width )
{
    Gia_Man_t * g = Gia_ManStart(1000), * clean;
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(s->g)), * vBits = Vec_IntStart(4*Width);
    Vec_Int_t * vChosen = Vec_IntStartFull(Width);
    Vec_Int_t * vConst = Vec_IntStart(Width), * vLeaves = Vec_WecEntry(m->vLeaves, Tree);
    Vec_Int_t * vRoots = Vec_WecEntry(m->vRoots, Tree), * v;
    Vec_Wec_t * vCols = Vec_WecStart(Width);
    int i, j, id, lit, a, b, c, rank, carry, sum;
    Gia_ManHashAlloc(g);
    for ( i = 0; i < nInputs; i++ ) Gia_ManAppendCi(g);
    Vec_IntForEachEntry(s->vStop, lit, i) if ( lit >= 0 ) Vec_IntWriteEntry(vMap, i, lit+2);
    Vec_IntForEachEntry(s->vEval, id, i)
        Vec_IntWriteEntry(vMap, id, Acec2_CopyGate(s->g, g, vMap, id));
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        lit = Vec_IntEntry(vLeaves, i); rank = Vec_IntEntry(vLeaves, i+1);
        if ( rank < Width ) Vec_WecPush(vCols, rank, Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
    }
    Vec_IntForEachEntry(Vec_WecEntry(m->vBias, Tree), rank, i)
        if ( rank < Width ) Vec_WecPush(vCols, rank, 1);
    for ( i = 0; i < Width; i++ )
    {
        v = Vec_WecEntry(vCols, i);
        while ( Vec_IntSize(v) > 1 )
        {
            a = Vec_IntPop(v); b = Vec_IntPop(v); c = Vec_IntSize(v) ? Vec_IntPop(v) : 0;
            sum = Gia_ManHashXor(g, Gia_ManHashXor(g, a, b), c);
            carry = Gia_ManHashMaj(g, a, b, c); Vec_IntPush(v, sum);
            if ( i+1 < Width ) Vec_WecPush(vCols, i+1, carry);
        }
        Vec_IntWriteEntry(vBits, i, Vec_IntSize(v) ? Vec_IntEntry(v, 0) : 0);
    }
    // Reversing every root gives K - value, where K is the sum of root weights.
    for ( i = 1; i < Vec_IntSize(vRoots); i += 2 )
    {
        rank = Vec_IntEntry(vRoots, i);
        for ( j = rank; j < Width; j++ )
        { a = Vec_IntEntry(vConst, j); Vec_IntWriteEntry(vConst, j, a ^ 1); if ( !a ) break; }
    }
    carry = 1;
    for ( i = 0; i < Width; i++ )
    {
        a = Vec_IntEntry(vBits, i) ^ 1; b = Vec_IntEntry(vConst, i);
        Vec_IntWriteEntry(vBits, Width+i, Gia_ManHashXor(g, a, carry) ^ b);
        carry = b ? Gia_ManHashOr(g, a, carry) : Gia_ManHashAnd(g, a, carry);
    }
    // Shared or truncated low columns can leave additional boundary roots.
    // Also propose one observed root per column, preferring the later final
    // adder. This is a proposal only, checked on the extracted gate cones.
    for ( i = 0; i < Vec_IntSize(vRoots); i += 2 )
    {
        lit = Vec_IntEntry(vRoots, i); rank = Vec_IntEntry(vRoots, i+1);
        if ( rank < Width && lit > Vec_IntEntry(vChosen, rank) ) Vec_IntWriteEntry(vChosen, rank, lit);
    }
    for ( i = 0; i < Width; i++ )
    {
        lit = Vec_IntEntry(vChosen, i);
        lit = lit < 0 ? Vec_IntEntry(vBits, i) : Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1);
        Vec_IntWriteEntry(vBits, 2*Width+i, lit); Vec_IntWriteEntry(vBits, 3*Width+i, lit ^ 1);
    }
    for ( i = 0; i < 4*Width; i++ ) Gia_ManAppendCo(g, Vec_IntEntry(vBits, i));
    Gia_ManHashStop(g); clean = Gia_ManCleanup(g); Gia_ManStop(g);
    Vec_IntFree(vMap); Vec_IntFree(vBits); Vec_IntFree(vConst); Vec_IntFree(vChosen); Vec_WecFree(vCols);
    return clean;
}

/**Function*************************************************************

  Synopsis    [Proposes a constant multiplier from repeated leaf coefficients.]

  Description [Coefficient patterns suggest the constant and operand order. Simulation
  filters these hypotheses; extracted-cone proofs authorize replacements.]

  SideEffects [Updates private replacement maps with proved equalities.]

  SeeAlso     []

***********************************************************************/
static int Acec2_TryConstantProduct( Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                                    int Side, int Tree, Hsh_Int1Man_t * h, Acec2_Par_t * pPars, abctime Deadline, int * pnWords )
{
    int n = Hsh_Int1ManEntryNum(h), Width = Vec_IntEntry(m[Side]->vWidths, Tree);
    ABC_INT64_T * pCoefs = ABC_CALLOC(ABC_INT64_T, n);
    word * pOdd = ABC_CALLOC(word, n);
    Vec_Int_t * vMax = Vec_IntStartFull(n), * vOrder = Vec_IntStartNatural(n);
    Vec_Int_t * vLeaves = Vec_WecEntry(m[Side]->vLeaves, Tree), * vOps[2] = {NULL, NULL}, * vBits, * vOuts = NULL;
    Vec_Wrd_t * vValues = NULL, * vExpected = NULL;
    Acec2_WordSim_t * s[2] = {NULL, NULL};
    Gia_Man_t * pModel = NULL, * pClean;
    int i, j, lit, rank, cut, best = -1, count, most = 0, nConst = 0, mode, side, round, merged = 0;
    word constant, code, state = ABC_CONST(0xB81726F1D49CA305);
    if ( n < 4 || n > 64 || Width > 48 ) goto finish;
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        lit = Vec_IntEntry(vLeaves, i); rank = Vec_IntEntry(vLeaves, i+1);
        lit = Vec_IntEntry(vMaps[Side], lit >> 1) ^ (lit & 1); cut = Acec2_IndexLookup(h, lit >> 1);
        if ( cut < 0 ) continue;
        pCoefs[cut] += (lit & 1) ? -(((ABC_INT64_T)1) << rank) : (((ABC_INT64_T)1) << rank);
        Vec_IntWriteEntry(vMax, cut, Abc_MaxInt(Vec_IntEntry(vMax, cut), rank));
    }
    for ( i = 0; i < n; i++ )
    {
        if ( !pCoefs[i] || Vec_IntEntry(vMax, i) < 0 ) goto finish;
        pOdd[i] = (word)(pCoefs[i] < 0 ? -pCoefs[i] : pCoefs[i]);
        while ( !(pOdd[i] & 1) ) pOdd[i] >>= 1;
    }
    for ( i = 0; i < n; i++ )
    {
        count = 0;
        for ( j = 0; j < n; j++ ) count += pOdd[j] == pOdd[i];
        if ( count > most ) { most = count; best = i; }
    }
    if ( most < Abc_MaxInt(3, n/2) || pOdd[best] <= 1 ) goto finish;
    constant = pOdd[best];
    for ( code = constant; code; code >>= 1 ) nConst++;
    if ( nConst > 32 ) goto finish;
    for ( i = 1; i < n; i++ )
    {
        cut = Vec_IntEntry(vOrder, i); j = i;
        while ( j && Vec_IntEntry(vMax, Vec_IntEntry(vOrder, j-1)) > Vec_IntEntry(vMax, cut) )
        { Vec_IntWriteEntry(vOrder, j, Vec_IntEntry(vOrder, j-1)); j--; }
        Vec_IntWriteEntry(vOrder, j, cut);
    }
    for ( i = 1; i < n-1; i++ )
        if ( Vec_IntEntry(vMax, Vec_IntEntry(vOrder, i)) != Vec_IntEntry(vMax, Vec_IntEntry(vOrder, 0))+i ) goto finish;
    Width = n+nConst+1;
    if ( Width > pPars->nMaxWidth || Acec2_Stop(pPars, Deadline) ) goto finish;
    vOps[0] = Vec_IntAlloc(n); vOps[1] = Vec_IntStart(nConst+1);
    Vec_IntForEachEntry(vOrder, cut, i)
        Vec_IntPush(vOps[0], Abc_Var2Lit(Vec_IntEntry(h->vData, cut), (pCoefs[cut] < 0) != (pCoefs[best] < 0)));
    pModel = Gia_ManStart(1000); Gia_ManHashAlloc(pModel); vOuts = Vec_IntAlloc(4*Width);
    for ( i = 0; i < n; i++ ) Gia_ManAppendCi(pModel);
    for ( mode = 0; mode < 4; mode++ )
    {
        code = mode & 2 ? (word)0-constant : constant;
        for ( i = 0; i <= nConst; i++ ) Vec_IntWriteEntry(vOps[1], i, (int)((code >> i) & 1));
        vBits = Acec2_ProductReference(pModel, vOps, h, mode, Width);
        Vec_IntAppend(vOuts, vBits); Vec_IntFree(vBits);
    }
    Vec_IntForEachEntry(vOuts, lit, i) Gia_ManAppendCo(pModel, lit);
    Gia_ManHashStop(pModel); pClean = Gia_ManCleanup(pModel); Gia_ManStop(pModel); pModel = pClean;
    for ( side = 0; side < 2; side++ )
    { s[side] = Acec2_WordSimCached(m[side], vMaps[side], h, Width); Acec2_WordPrioritize(s[side], m[side]); }
    vValues = Vec_WrdStart(n); vExpected = Vec_WrdStart(4*Width);
    for ( round = 0; round < 16; round++ )
    {
        if ( Acec2_Stop(pPars, Deadline) ) goto finish;
        for ( i = 0; i < n; i++ )
        {
            Acec2_Random(&state);
            Vec_WrdWriteEntry(vValues, i, round == 4 ? ABC_CONST(0xAAAAAAAAAAAAAAAA) : state);
        }
        Acec2_ModelPatterns(vOps, h, vValues, vExpected, Width, pModel);
        for ( side = 0; side < 2; side++ ) Acec2_WordSimulate(s[side], vValues, vExpected, round);
    }
    if ( pPars->fVerbose ) Abc_Print(1, "Constant-product proposal: operand bits = %d, constant bits = %d.\n", n, nConst);
    merged = Acec2_ProveBoundary(m, vMaps, vReplaces, s, vOps, h, vValues, vExpected, Width, pPars, Deadline, pnWords, pModel);
finish:
    ABC_FREE(pCoefs); ABC_FREE(pOdd); Vec_IntFree(vMax); Vec_IntFree(vOrder); Vec_IntFreeP(&vOps[0]); Vec_IntFreeP(&vOps[1]); Vec_IntFreeP(&vOuts);
    Vec_WrdFreeP(&vValues); Vec_WrdFreeP(&vExpected);
    for ( side = 0; side < 2; side++ ) Acec2_WordSimStop(s[side]);
    if ( pModel ) Gia_ManStop(pModel);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Matches a region over a shared cut preceding its cell interior.]

  Description [Retains dependencies between cut signals where available.]

  SideEffects [Updates private replacement maps after exact proofs.]

  SeeAlso     []

***********************************************************************/
static int Acec2_TryRegion( Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces, Vec_Int_t * vColors,
                           int Side, int Tree, Acec2_Par_t * pPars, abctime Deadline, int * pnWords )
{
    Hsh_Int1Man_t * h = Hsh_Int1ManStart(100), * hMinimal;
    Vec_Int_t * vStack = Vec_IntAlloc(100), * vSeen = Vec_IntStart(Gia_ManObjNum(m[Side]->pGia));
    Vec_Int_t * vInside = Vec_IntStart(Vec_IntSize(vColors));
    Vec_Int_t * vLeaves = Vec_WecEntry(m[Side]->vLeaves, Tree);
    Acec2_WordSim_t * s[2] = {NULL, NULL};
    Gia_Man_t * pModel = NULL;
    Gia_Obj_t * o;
    Vec_Wrd_t * vValues = NULL, * vExpected = NULL;
    word state = ABC_CONST(0xE47F68AA9B316205), value;
    int Width = Vec_IntEntry(m[Side]->vWidths, Tree), i, k, gate, id, lit, side, round, legal, count = 0, merged = 0;
    if ( Width < 4 || Width > 256 || Width > pPars->nMaxWidth || Vec_IntSize(vLeaves) > 20000 ) goto finish;
    // A shared signal used by several cells can be both a reported leaf and
    // an internal result. Cutting it would destroy the region identity under
    // independent assignments. Move those cut points behind the cell interior.
    Vec_IntForEachEntry(Vec_WecEntry(m[Side]->vTrees, Tree), id, i)
        Vec_IntForEachEntry(Vec_WecEntry(m[Side]->vCellGates, id), gate, k)
        {
            if ( (k & 255) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
            lit = Vec_IntEntry(vMaps[Side], gate);
            if ( (lit >> 1) > Gia_ManCiNum(m[Side]->pGia) ) Vec_IntWriteEntry(vInside, lit >> 1, 1);
        }
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 ) Vec_IntPush(vStack, Vec_IntEntry(vLeaves, i) >> 1);
    while ( Vec_IntSize(vStack) )
    {
        id = Vec_IntPop(vStack);
        if ( !id || Vec_IntEntry(vSeen, id) ) continue;
        Vec_IntWriteEntry(vSeen, id, 1);
        if ( ++count > 20000 || ((count & 255) == 0 && Acec2_Stop(pPars, Deadline)) ) goto finish;
        lit = Vec_IntEntry(vMaps[Side], id);
        if ( lit >= 2 && Vec_IntEntry(vColors, lit >> 1) == 3 && !Vec_IntEntry(vInside, lit >> 1) )
        { Acec2_IndexAdd(h, lit >> 1); if ( Hsh_Int1ManEntryNum(h) > 512 ) goto finish; continue; }
        o = Gia_ManObj(m[Side]->pGia, id);
        if ( !Gia_ObjIsAnd(o) ) goto finish;
        Vec_IntPushTwo(vStack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
        if ( Gia_ObjIsMux(m[Side]->pGia, o) ) Vec_IntPush(vStack, Gia_ObjFaninId2(m[Side]->pGia, id));
    }
    if ( !Hsh_Int1ManEntryNum(h) ) goto finish;
    // Keep dependencies between low carry inputs and operand bits. A cut
    // signal already computable from earlier cut signals is not independent.
    hMinimal = Hsh_Int1ManStart(100); Vec_IntFill(vSeen, Vec_IntSize(vSeen), 0); Vec_IntWriteEntry(vSeen, 0, 1);
    Gia_ManForEachObj1(m[Side]->pGia, o, i)
    {
        if ( Gia_ObjIsCo(o) ) continue;
        legal = Gia_ObjIsAnd(o) && Vec_IntEntry(vSeen, Gia_ObjFaninId0(o, i)) && Vec_IntEntry(vSeen, Gia_ObjFaninId1(o, i));
        if ( legal && Gia_ObjIsMux(m[Side]->pGia, o) ) legal = Vec_IntEntry(vSeen, Gia_ObjFaninId2(m[Side]->pGia, i));
        lit = Vec_IntEntry(vMaps[Side], i);
        if ( !legal && Acec2_IndexLookup(h, lit >> 1) >= 0 )
        { Acec2_IndexAdd(hMinimal, lit >> 1); legal = 1; }
        Vec_IntWriteEntry(vSeen, i, legal);
    }
    Hsh_Int1ManStop(h); h = hMinimal;
    merged = Acec2_TryConstantProduct(m, vMaps, vReplaces, Side, Tree, h, pPars, Deadline, pnWords);
    if ( merged || Acec2_Stop(pPars, Deadline) ) goto finish;
    for ( side = 0; side < 2; side++ )
    { s[side] = Acec2_WordSimCached(m[side], vMaps[side], h, Width); Acec2_WordPrioritize(s[side], m[side]); }
    pModel = Acec2_RegionModel(s[Side], m[Side], Tree, Hsh_Int1ManEntryNum(h), Width);
    vValues = Vec_WrdStart(Hsh_Int1ManEntryNum(h)); vExpected = Vec_WrdStart(4*Width);
    for ( round = 0; round < 16; round++ )
    {
        if ( Acec2_Stop(pPars, Deadline) ) goto finish;
        for ( i = 0; i < Vec_WrdSize(vValues); i++ )
        {
            Acec2_Random(&state); value = state;
            if ( round == 4 ) value = ABC_CONST(0xAAAAAAAAAAAAAAAA);
            Vec_WrdWriteEntry(vValues, i, value);
        }
        Acec2_ModelPatterns(NULL, h, vValues, vExpected, Width, pModel);
        for ( side = 0; side < 2; side++ ) Acec2_WordSimulate(s[side], vValues, vExpected, round);
    }
    merged = Acec2_ProveBoundary(m, vMaps, vReplaces, s, NULL, h, vValues, vExpected, Width, pPars, Deadline, pnWords, pModel);
finish:
    if ( pModel ) Gia_ManStop(pModel);
    for ( side = 0; side < 2; side++ ) Acec2_WordSimStop(s[side]);
    Vec_WrdFreeP(&vValues); Vec_WrdFreeP(&vExpected);
    Vec_IntFree(vStack); Vec_IntFree(vSeen); Vec_IntFree(vInside); Hsh_Int1ManStop(h);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Separates operand buses that share some of their bits.]

  Description [Only proposes a cut; component proofs remain mandatory.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_OverlapOperands( Vec_Int_t * vNodes, Vec_Int_t * vRank, Vec_Wec_t * vAdj, Acec2_Edge_t * e,
                                  Hsh_Int1Man_t * h, int Min, int Max, Vec_Int_t ** vOps )
{
    Vec_Wec_t * vRanks = Vec_WecStart((Max-Min)/2+1);
    Vec_Int_t * vSide = Vec_IntStartFull(Vec_WecSize(vAdj)), * vQueue = Vec_IntAlloc(100), * v, * vPair;
    int i, j, k, x, y, rank, color, mask, ok = 0, last[2] = {-1, -1};
    vOps[0] = vOps[1] = NULL;
    Vec_IntForEachEntry(vNodes, x, i)
    {
        rank = Vec_IntEntry(vRank, x)-Min;
        if ( rank & 1 ) goto finish;
        Vec_WecPush(vRanks, rank/2, x);
        if ( Vec_IntSize(Vec_WecEntry(vRanks, rank/2)) > 2 ) goto finish;
    }
    Vec_WecForEachLevel(vRanks, vPair, rank)
    {
        if ( Vec_IntSize(vPair) != 2 ) continue;
        x = Vec_IntEntry(vPair, 0);
        if ( Vec_IntEntry(vSide, x) >= 0 ) continue;
        Vec_IntClear(vQueue); Vec_IntPush(vQueue, x); Vec_IntWriteEntry(vSide, x, 0);
        for ( i = 0; i < Vec_IntSize(vQueue); i++ )
        {
            x = Vec_IntEntry(vQueue, i); color = Vec_IntEntry(vSide, x);
            v = Vec_WecEntry(vRanks, (Vec_IntEntry(vRank, x)-Min)/2);
            y = Vec_IntEntry(v, 0) ^ Vec_IntEntry(v, 1) ^ x;
            if ( Vec_IntEntry(vSide, y) < 0 ) { Vec_IntWriteEntry(vSide, y, color ^ 1); Vec_IntPush(vQueue, y); }
            else if ( Vec_IntEntry(vSide, y) == color ) goto finish;
            v = Vec_WecEntry(vAdj, x);
            Vec_IntForEachEntry(v, j, k)
            {
                y = e[j].a ^ e[j].b ^ x;
                if ( Vec_IntSize(Vec_WecEntry(vRanks, (Vec_IntEntry(vRank, y)-Min)/2)) != 2 ) continue;
                if ( Vec_IntEntry(vSide, y) < 0 ) { Vec_IntWriteEntry(vSide, y, color ^ 1); Vec_IntPush(vQueue, y); }
                else if ( Vec_IntEntry(vSide, y) == color ) goto finish;
            }
        }
    }
    vOps[0] = Vec_IntStartFull(Vec_WecSize(vRanks)); vOps[1] = Vec_IntStartFull(Vec_WecSize(vRanks));
    Vec_IntForEachEntry(vNodes, x, i)
    {
        rank = (Vec_IntEntry(vRank, x)-Min)/2; color = Vec_IntEntry(vSide, x);
        if ( color >= 0 ) mask = 1 << color;
        else
        {
            mask = 0; v = Vec_WecEntry(vAdj, x);
            Vec_IntForEachEntry(v, j, k)
            { y = e[j].a ^ e[j].b ^ x; color = Vec_IntEntry(vSide, y); if ( color >= 0 ) mask |= 1 << (color ^ 1); }
            if ( !mask ) goto finish;
        }
        for ( color = 0; color < 2; color++ )
            if ( (mask >> color) & 1 )
            { Vec_IntWriteEntry(vOps[color], rank, Vec_IntEntry(h->vData, x)); last[color] = Abc_MaxInt(last[color], rank); }
    }
    for ( color = 0; color < 2; color++ )
    {
        if ( last[color] < 2 ) goto finish;
        Vec_IntShrink(vOps[color], last[color]+1);
        Vec_IntForEachEntry(vOps[color], x, i) if ( x < 0 ) goto finish;
    }
    ok = 1;
finish:
    if ( !ok ) { Vec_IntFreeP(&vOps[0]); Vec_IntFreeP(&vOps[1]); }
    Vec_WecFree(vRanks); Vec_IntFree(vSide); Vec_IntFree(vQueue); return ok;
}

/**Function*************************************************************

  Synopsis    [Recovers sparse or repeated-bit operands from product weights.]

  Description [Coefficient columns of a consecutive bus suggest the other operand.
  Voting tolerates missing low products and modular coefficients retain
  repeated sign bits. A unit matrix entry supplies an additional proposal.
  The resulting buses still require exact proofs over independent cut inputs.]

  SideEffects [Allocates two proposed operand vectors on success.]

  SeeAlso     []

***********************************************************************/
static int Acec2_WeightedOperands( Acec2_Man_t * m, Vec_Int_t * vMap, int Tree,
                                  Hsh_Int1Man_t * h, Vec_Int_t * vNodes, Vec_Int_t * vColor, Vec_Int_t * vRank,
                                  Vec_Int_t ** vOps, int * pOffset )
{
    Vec_Int_t * vLeaves = Vec_WecEntry(m->vLeaves, Tree), * vIndex;
    Gia_Obj_t * o;
    word * matrix, * weights[2], mask, coef, mag, anchor = 0;
    int n = Vec_IntSize(vNodes), width = Vec_IntEntry(m->vWidths, Tree);
    int i, j, k, id, a, b, x, y, row = -1, col = -1, rank, minRow = 64, minCol = 64, sign = 0;
    int side, bits[2] = {0, 0}, ok = 0, known, count, lo, hi, pos, neg, shift, other, otherWidth, seen, bestCount, votes;
    word candidates[64], otherMask;
    vOps[0] = vOps[1] = NULL;
    if ( n < 6 || n > 512 || width < 4 || width > 64 ) return 0;
    vIndex = Vec_IntStartFull(Hsh_Int1ManEntryNum(h));
    Vec_IntForEachEntry(vNodes, x, i) Vec_IntWriteEntry(vIndex, x, i);
    matrix = ABC_CALLOC(word, n*n); weights[0] = ABC_CALLOC(word, n); weights[1] = ABC_CALLOC(word, n);
    mask = width == 64 ? ~(word)0 : (((word)1 << width)-1);
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        id = Vec_IntEntry(vLeaves, i) >> 1; rank = Vec_IntEntry(vLeaves, i+1);
        o = Gia_ManObj(m->pGia, id);
        if ( rank >= width || !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
        a = Vec_IntEntry(vMap, Gia_ObjFaninId0(o, id)) ^ Gia_ObjFaninC0(o);
        b = Vec_IntEntry(vMap, Gia_ObjFaninId1(o, id)) ^ Gia_ObjFaninC1(o);
        x = Acec2_IndexLookup(h, a); y = Acec2_IndexLookup(h, b);
        if ( x < 0 || y < 0 || Vec_IntEntry(vColor, x) == Vec_IntEntry(vColor, y) ) continue;
        a = Vec_IntEntry(vIndex, x); b = Vec_IntEntry(vIndex, y);
        if ( a < 0 || b < 0 ) continue;
        if ( Vec_IntEntry(vColor, x) ) ABC_SWAP(int, a, b);
        coef = (word)1 << rank;
        matrix[a*n+b] = (matrix[a*n+b] + ((Vec_IntEntry(vLeaves, i) & 1) ? -coef : coef)) & mask;
    }
    // A consecutive operand bus fixes the shifts of every coefficient
    // column. Combining those columns recovers repeated positions even when
    // discarded low sums removed some partial products from the region.
    for ( known = 0; known < 2; known++ )
    {
        lo = ABC_INT_MAX; hi = -ABC_INT_MAX; count = 0;
        Vec_IntForEachEntry(vNodes, x, i)
            if ( Vec_IntEntry(vColor, x) == known )
            { rank = Vec_IntEntry(vRank, x); lo = Abc_MinInt(lo, rank); hi = Abc_MaxInt(hi, rank); count++; }
        if ( count < 3 || count > 64 || hi-lo+1 != count ) continue;
        for ( i = 0; i < n; i++ ) for ( j = i+1; j < n; j++ )
            if ( Vec_IntEntry(vColor, Vec_IntEntry(vNodes, i)) == known &&
                 Vec_IntEntry(vColor, Vec_IntEntry(vNodes, j)) == known &&
                 Vec_IntEntry(vRank, Vec_IntEntry(vNodes, i)) == Vec_IntEntry(vRank, Vec_IntEntry(vNodes, j)) ) goto next_known;
        pos = neg = 0; *pOffset = ABC_INT_MAX;
        for ( i = 0; i < n; i++ ) for ( j = 0; j < n; j++ )
        {
            coef = matrix[i*n+j]; if ( !coef ) continue;
            x = Vec_IntEntry(vNodes, known ? j : i); rank = Vec_IntEntry(vRank, x)-lo;
            for ( k = 0; k < width && !((coef >> k) & 1); k++ ) {}
            *pOffset = Abc_MinInt(*pOffset, k-rank);
            if ( (coef >> (width-1)) & 1 ) neg++; else pos++;
        }
        if ( *pOffset == ABC_INT_MAX ) continue;
        sign = neg > pos;
        for ( i = 0; i < n; i++ ) weights[0][i] = weights[1][i] = 0;
        Vec_IntForEachEntry(vNodes, x, i)
            if ( Vec_IntEntry(vColor, x) == known ) weights[known][i] = (word)1 << (Vec_IntEntry(vRank, x)-lo);
        otherWidth = width-*pOffset-count;
        // A truncated product need not contain the full width of either
        // operand. Subtracting the known bus width can leave no room for
        // repeated bits in the other bus. Retain the observable coefficient
        // range in this case; simulation and exact proofs check the proposal.
        if ( otherWidth < 3 ) otherWidth = width-*pOffset;
        if ( otherWidth < 3 || otherWidth > 64 ) continue;
        otherMask = otherWidth == 64 ? ~(word)0 : (((word)1 << otherWidth)-1);
        for ( other = 0; other < n; other++ )
        {
            if ( Vec_IntEntry(vColor, Vec_IntEntry(vNodes, other)) == known ) continue;
            seen = 0;
            for ( j = 0; j < n; j++ )
            {
                coef = known ? matrix[other*n+j] : matrix[j*n+other];
                if ( !coef ) continue;
                x = Vec_IntEntry(vNodes, j); shift = Vec_IntEntry(vRank, x)-lo+*pOffset;
                if ( shift <= -64 || shift >= 64 ) continue;
                // Keep the coefficient modulo the inferred operand width.
                // In particular, a repeated sign bit must not be replaced
                // by the absolute value of its signed coefficient.
                mag = shift < 0 ? coef << -shift : coef >> shift;
                assert(seen < 64); candidates[seen++] = mag & otherMask;
            }
            bestCount = 0;
            for ( j = 0; j < seen; j++ )
            {
                votes = 0;
                for ( k = 0; k < seen; k++ ) votes += candidates[k] == candidates[j];
                if ( votes > bestCount ) { bestCount = votes; weights[known ^ 1][other] = candidates[j]; }
            }
        }
        goto build_buses;
next_known:;
    }
    // Prefer the lowest nonzero unit entry. Its row and column expose the
    // two coefficient vectors without dividing by a non-unit odd factor.
    for ( i = 0; i < n; i++ ) for ( j = 0; j < n; j++ )
    {
        coef = matrix[i*n+j]; mag = coef;
        if ( (coef >> (width-1)) & 1 ) mag = (-coef) & mask;
        if ( !mag || (mag & (mag-1)) || (anchor && mag >= anchor) ) continue;
        anchor = mag; row = i; col = j; sign = mag != coef;
    }
    if ( row < 0 ) goto finish;
    for ( i = 0; i < n; i++ )
    {
        coef = matrix[row*n+i];
        if ( coef ) { for ( k = 0; k < width && !((coef >> k) & 1); k++ ) {} minRow = Abc_MinInt(minRow, k); }
        coef = matrix[i*n+col];
        if ( coef ) { for ( k = 0; k < width && !((coef >> k) & 1); k++ ) {} minCol = Abc_MinInt(minCol, k); }
    }
    for ( k = 0; k < width && !((anchor >> k) & 1); k++ ) {}
    *pOffset = minRow+minCol-k;
    if ( minRow == 64 || minCol == 64 || *pOffset < 0 ) goto finish;
    for ( i = 0; i < n; i++ )
    {
        weights[0][i] = (sign ? -matrix[i*n+col] & mask : matrix[i*n+col]) >> minCol;
        weights[1][i] = (sign ? -matrix[row*n+i] & mask : matrix[row*n+i]) >> minRow;
    }
build_buses:
    for ( side = 0; side < 2; side++ )
    {
        vOps[side] = Vec_IntStart(64);
        for ( i = 0; i < n; i++ )
        {
            x = Vec_IntEntry(h->vData, Vec_IntEntry(vNodes, i));
            for ( k = 0; k < 64; k++ )
                if ( (weights[side][i] >> k) & 1 )
                {
                    if ( Vec_IntEntry(vOps[side], k) && Vec_IntEntry(vOps[side], k) != x ) goto finish;
                    Vec_IntWriteEntry(vOps[side], k, x); bits[side] = Abc_MaxInt(bits[side], k+1);
                }
        }
        if ( bits[side] < 3 || bits[side] > width ) goto finish;
        Vec_IntShrink(vOps[side], bits[side]);
    }
    ok = 1;
finish:
    if ( !ok ) { Vec_IntFreeP(&vOps[0]); Vec_IntFreeP(&vOps[1]); }
    ABC_FREE(matrix); ABC_FREE(weights[0]); ABC_FREE(weights[1]); Vec_IntFree(vIndex);
    return ok;
}

/**Function*************************************************************

  Synopsis    [Recovers square operands despite incomplete top-column products.]

  Description [Triangles independently vote for twice each bit rank. A few
  missing duplicate products at a truncated boundary need not invalidate the
  entire bus. These ranks only propose templates; every merged result still
  requires an exact component certificate.]

  SideEffects [Allocates two operand vectors on success.]

  SeeAlso     []

***********************************************************************/
static int Acec2_SquareOperands( Vec_Int_t * vNodes, Vec_Wec_t * vAdj, Acec2_Edge_t * e,
                                Hsh_Int1Man_t * h, int Width, Vec_Int_t ** vOps, int * pOffset )
{
    int n = Vec_IntSize(vNodes), i, j, k, x, y, z, a, b, c, rank, votes, best, count, agree = 0, total = 0, min = ABC_INT_MAX, max = -ABC_INT_MAX, ok = 0;
    Vec_Int_t * vIndex, * vMatrix, * vRanks, * vVotes;
    if ( n < 4 || n > 128 || Width < 4 || Width > 256 ) return 0;
    vIndex = Vec_IntStartFull(Hsh_Int1ManEntryNum(h)); vMatrix = Vec_IntStartFull(n*n);
    vRanks = Vec_IntStart(n); vVotes = Vec_IntStart(3*Width+1);
    Vec_IntForEachEntry(vNodes, x, i) Vec_IntWriteEntry(vIndex, x, i);
    Vec_IntForEachEntry(vNodes, x, i)
        Vec_IntForEachEntry(Vec_WecEntry(vAdj, x), k, j)
        {
            y = e[k].a ^ e[k].b ^ x; z = Vec_IntEntry(vIndex, y);
            if ( z >= 0 && e[k].rank < Width ) Vec_IntWriteEntry(vMatrix, i*n+z, e[k].rank);
        }
    for ( i = 0; i < n; i++ )
    {
        Vec_IntFill(vVotes, Vec_IntSize(vVotes), 0); count = votes = 0; best = 0;
        for ( j = 0; j < n; j++ ) for ( k = j+1; k < n; k++ )
        {
            a = Vec_IntEntry(vMatrix, i*n+j); b = Vec_IntEntry(vMatrix, i*n+k); c = Vec_IntEntry(vMatrix, j*n+k);
            if ( a < 0 || b < 0 || c < 0 ) continue;
            rank = a+b-c+Width; Vec_IntAddToEntry(vVotes, rank, 1); count++;
            if ( Vec_IntEntry(vVotes, rank) > votes ) { votes = Vec_IntEntry(vVotes, rank); best = rank-Width; }
        }
        if ( votes < 2 || 2*votes < count ) goto finish;
        Vec_IntWriteEntry(vRanks, i, best); min = Abc_MinInt(min, best); max = Abc_MaxInt(max, best);
    }
    if ( max-min != 2*(n-1) ) goto finish;
    for ( i = 0; i < n; i++ ) for ( j = i+1; j < n; j++ )
    {
        rank = Vec_IntEntry(vMatrix, i*n+j); if ( rank < 0 ) continue;
        total++; agree += Vec_IntEntry(vRanks, i)+Vec_IntEntry(vRanks, j) == 2*rank;
    }
    if ( total < 2*n || 4*agree < 3*total ) goto finish;
    vOps[0] = Vec_IntStartFull(n);
    Vec_IntForEachEntry(vNodes, x, i)
    {
        rank = Vec_IntEntry(vRanks, i)-min;
        if ( (rank & 1) || Vec_IntEntry(vOps[0], rank/2) >= 0 ) { Vec_IntFree(vOps[0]); goto finish; }
        Vec_IntWriteEntry(vOps[0], rank/2, Vec_IntEntry(h->vData, x));
    }
    vOps[1] = Vec_IntDup(vOps[0]); *pOffset = min; ok = 1;
finish:
    Vec_IntFree(vIndex); Vec_IntFree(vMatrix); Vec_IntFree(vRanks); Vec_IntFree(vVotes);
    return ok;
}

/**Function*************************************************************

  Synopsis    [Uses repeated leaf coefficients and a preceding adder as a bus proposal.]

  Description [Truncated constant products can lose low leaf occurrences.
  The repeated odd coefficient proposes the constant; a preceding adder
  supplies the complete operand order. Neither observation constitutes a
  proof. Only certified templates may install aliases.]

  SideEffects [Updates private replacement maps after exact proofs.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ConstantTemplates( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps,
                                   Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces, Vec_Int_t * vColors,
                                   int Side, int Tree, Acec2_Par_t * pPars, abctime Deadline, int * pnWords,
                                   Acec2_Templ_t * pTemplates )
{
    Acec2_Man_t * p = m[Side];
    Hsh_Int1Man_t * h = Hsh_Int1ManStart(100);
    Vec_Wrd_t * vCoefs = Vec_WrdAlloc(100), * vOdd = NULL;
    Vec_Int_t * vLeaves = Vec_WecEntry(p->vLeaves, Tree), * vSource = Vec_IntAlloc(100), * vVotes = NULL;
    Vec_Int_t * vWord = NULL, * vOps[2] = {NULL, NULL}, * vRoots, * vTop = Vec_IntAlloc(4);
    int width = Vec_IntEntry(p->vWidths, Tree), i, j, k, id, lit, rank, cut, owner, producer = -1;
    int n, best = -1, most = 0, count, busWidth, nConst = 0, flip, top, merged = 0;
    word coef, odd, constant;
    if ( width < 8 || width > 63 ) goto finish;
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        id = Vec_IntEntry(vLeaves, i) >> 1; rank = Vec_IntEntry(vLeaves, i+1);
        lit = Vec_IntEntry(vMaps[Side], id) ^ (Vec_IntEntry(vLeaves, i) & 1);
        if ( rank >= 63 || lit < 2 || Vec_IntEntry(vColors, lit >> 1) != 3 ) continue;
        n = Hsh_Int1ManEntryNum(h); cut = Acec2_IndexAdd(h, lit >> 1);
        if ( cut == n ) { Vec_WrdPush(vCoefs, 0); Vec_IntPush(vSource, id); }
        coef = (word)1 << rank;
        Vec_WrdWriteEntry(vCoefs, cut, Vec_WrdEntry(vCoefs, cut) + ((lit & 1) ? (word)0-coef : coef));
    }
    n = Hsh_Int1ManEntryNum(h); if ( n < 8 || n > 512 ) goto finish;
    vOdd = Vec_WrdStart(n);
    Vec_WrdForEachEntry(vCoefs, coef, i)
    {
        if ( coef >> 63 ) coef = (word)0-coef;
        if ( !coef ) continue;
        while ( !(coef & 1) ) coef >>= 1;
        Vec_WrdWriteEntry(vOdd, i, coef);
    }
    Vec_WrdForEachEntry(vOdd, odd, i)
    {
        if ( odd <= 1 ) continue;
        count = 0; for ( j = 0; j < n; j++ ) count += Vec_WrdEntry(vOdd, j) == odd;
        if ( count > most ) { best = i; most = count; }
    }
    if ( most < 4 ) goto finish;
    constant = Vec_WrdEntry(vOdd, best); for ( coef = constant; coef; coef >>= 1 ) nConst++;
    if ( nConst > 32 ) goto finish;
    vVotes = Vec_IntStart(Vec_WecSize(p->vTrees)); most = 0;
    Vec_WrdForEachEntry(vOdd, odd, i)
    {
        if ( odd != constant ) continue;
        owner = Vec_IntEntry(p->vOwner, Vec_IntEntry(vSource, i));
        if ( owner < 0 || (owner & 1) ) continue;
        j = Acec2_Cell(p, owner >> 1)->Tree; if ( j == Tree ) continue;
        Vec_IntAddToEntry(vVotes, j, 1);
        if ( Vec_IntEntry(vVotes, j) > most ) { most = Vec_IntEntry(vVotes, j); producer = j; }
    }
    if ( most < 4 ) goto finish;
    busWidth = Vec_IntEntry(p->vWidths, producer);
    if ( busWidth < 4 || busWidth > 128 || busWidth+nConst > pPars->nMaxWidth ) goto finish;
    vWord = Vec_IntStartFull(busWidth); vRoots = Vec_WecEntry(p->vRoots, producer);
    for ( i = 0; i < Vec_IntSize(vRoots); i += 2 )
    {
        lit = Vec_IntEntry(vRoots, i); rank = Vec_IntEntry(vRoots, i+1);
        if ( lit > Vec_IntEntry(vWord, rank) ) Vec_IntWriteEntry(vWord, rank, lit);
    }
    Vec_IntForEachEntry(vWord, lit, i) if ( lit < 0 ) goto finish;
    // A truncated final sum may have no carry cell. Its XOR and phase are
    // alternative proposals, never assumed arithmetic boundaries.
    id = Vec_IntEntryLast(vWord) >> 1;
    for ( i = 0; i < Vec_IntSize(p->vXors) && Vec_IntSize(vTop) < 4; i += 5 )
    {
        if ( Vec_IntEntry(p->vXors, i) != 2 ) continue;
        if ( Vec_IntEntry(p->vXors, i+1) != id && Vec_IntEntry(p->vXors, i+2) != id ) continue;
        lit = Vec_IntEntry(p->vXors, i+4);
        if ( Vec_IntFind(vTop, lit) < 0 ) Vec_IntPush(vTop, lit);
    }
    Vec_IntPushUnique(vTop, Vec_IntEntryLast(vWord));
    vOps[0] = Vec_IntStart(busWidth); vOps[1] = Vec_IntStart(nConst);
    for ( i = 0; i < nConst; i++ ) Vec_IntWriteEntry(vOps[1], i, (int)((constant >> i) & 1));
    for ( top = 0; top < Vec_IntSize(vTop) && !Acec2_Stop(pPars, Deadline); top++ )
        for ( flip = 0; flip < 4 && !Acec2_Stop(pPars, Deadline); flip++ )
        {
            Vec_IntForEachEntry(vWord, lit, i)
            {
                if ( i == busWidth-1 ) lit = Vec_IntEntry(vTop, top) ^ (flip >> 1);
                lit = Vec_IntEntry(vMaps[Side], lit >> 1) ^ (lit & 1) ^ ((flip ^ 1) & 1);
                if ( lit >= 2 && Vec_IntEntry(vColors, lit >> 1) != 3 ) break;
                Vec_IntWriteEntry(vOps[0], i, lit);
            }
            if ( i < busWidth ) continue;
            k = Acec2_TemplateMatch(pNew, vMaps, vOriginals, vReplaces, vOps, busWidth+nConst, pPars, Deadline, pnWords, pTemplates);
            merged += k;
            if ( k )
            {
                if ( pPars->fVerbose ) Abc_Print(1, "Certified constant product: operand bits = %d, constant = %llu, new root aliases = %d.\n", busWidth, (unsigned long long)constant, k);
                goto finish;
            }
        }
finish:
    Hsh_Int1ManStop(h); Vec_WrdFree(vCoefs); Vec_WrdFreeP(&vOdd);
    Vec_IntFree(vSource); Vec_IntFreeP(&vVotes); Vec_IntFreeP(&vWord); Vec_IntFree(vTop);
    Vec_IntFreeP(&vOps[0]); Vec_IntFreeP(&vOps[1]);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Collects coefficients of common signals at a weighted boundary.]

  Description [These coefficients propose constant factors. A boundary may
  include other arithmetic, so neither the factor nor the inferred bus is
  trusted without an independent product certificate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ChainCoefficients( Acec2_Man_t * p, Vec_Int_t * vMap, Vec_Int_t * vColors,
                                   int Tree, Vec_Int_t * vIds, Vec_Wrd_t * vCoefs,
                                   Acec2_Par_t * pPars, abctime Deadline )
{
    Hsh_Int1Man_t * h = Hsh_Int1ManStart(100);
    Vec_Int_t * vLeaves = Vec_IntAlloc(100), * vCells = Vec_WecEntry(p->vTrees, Tree);
    Acec2_Cell_t * c;
    int i, j, lit, id, rank, index, valid = 0;
    word coef;
    if ( Vec_IntEntry(p->vWidths, Tree) > 63 || Vec_IntSize(vCells) > 33333 ) goto finish;
    // A shared operand can now belong to the same region as its consumers.
    // Restore the frontier at those proved common sums when proposing a
    // constant coefficient; cancelling one shared use would reduce it by one.
    Vec_IntForEachEntry(vCells, id, i)
    {
        c = Acec2_Cell(p, id);
        if ( Vec_IntEntry(vColors, Vec_IntEntry(vMap, c->Out[0] >> 1) >> 1) == 3 ) continue;
        for ( j = 0; j < c->nIns; j++ ) Vec_IntPushTwo(vLeaves, c->In[j] ^ c->Phase, c->Rank);
    }
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
        lit = Vec_IntEntry(vLeaves, i); rank = Vec_IntEntry(vLeaves, i+1); id = lit >> 1;
        if ( rank < 0 || rank >= 63 || !id || Vec_IntEntry(vColors, Vec_IntEntry(vMap, id) >> 1) != 3 ) continue;
        index = Acec2_IndexAdd(h, id);
        if ( index == Vec_IntSize(vIds) )
        {
            if ( index == 512 ) goto finish;
            Vec_IntPush(vIds, id); Vec_WrdPush(vCoefs, 0);
        }
        coef = (word)1 << rank;
        Vec_WrdWriteEntry(vCoefs, index, Vec_WrdEntry(vCoefs, index) + ((lit & 1) ? (word)0-coef : coef));
    }
    valid = Vec_IntSize(vIds) >= 2;
finish:
    Hsh_Int1ManStop(h); Vec_IntFree(vLeaves);
    return valid;
}

/**Function*************************************************************

  Synopsis    [Links common sum bits through unambiguous carry connections.]

  Description [A producer may share a region with its constant multiplier.
  Following carries preserves the operand order even in that case.]

  SideEffects [Writes private predecessor and successor vectors.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ChainLinks( Acec2_Man_t * p, Vec_Int_t * vMap, Vec_Int_t * vColors,
                            Vec_Int_t * vPrev, Vec_Int_t * vNext, Acec2_Par_t * pPars, abctime Deadline )
{
    Acec2_Cell_t * c, * b;
    int i, j, owner, parent;
    Vec_PtrForEachEntry(Acec2_Cell_t *, p->vCells, c, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) return 0;
        if ( Vec_IntEntry(vColors, Vec_IntEntry(vMap, c->Out[0] >> 1) >> 1) != 3 ) continue;
        parent = -1;
        for ( j = 0; j < c->nIns; j++ )
        {
            owner = Vec_IntEntry(p->vOwner, c->In[j] >> 1);
            if ( owner < 0 || !(owner & 1) ) continue;
            b = Acec2_Cell(p, owner >> 1);
            if ( Vec_IntEntry(vColors, Vec_IntEntry(vMap, b->Out[0] >> 1) >> 1) != 3 ||
                 b->Tree != c->Tree || b->Rank+1 != c->Rank ) continue;
            if ( parent >= 0 ) { parent = -2; break; }
            parent = owner >> 1;
        }
        if ( parent < 0 ) continue;
        Vec_IntWriteEntry(vPrev, i, parent);
        Vec_IntWriteEntry(vNext, parent, Vec_IntEntry(vNext, parent) == -1 ? i : -2);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects a bounded carry chain containing a proposed operand bit.]

  Description [Only the chain through the seed is retained at a branch.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ChainWord( Acec2_Man_t * p, int Seed, Vec_Int_t * vPrev, Vec_Int_t * vNext,
                           Vec_Int_t * vBus, int * pFirst, int * pLast )
{
    Acec2_Cell_t * c;
    int first = Seed, last = Seed, i, j, cur, lit;
    for ( i = 0; i < 128 && Vec_IntEntry(vPrev, first) >= 0; i++ ) first = Vec_IntEntry(vPrev, first);
    if ( Vec_IntEntry(vPrev, first) >= 0 ) return 0;
    Vec_IntClear(vBus);
    for ( cur = Seed; cur >= 0 && Vec_IntSize(vBus) < 128; cur = Vec_IntEntry(vPrev, cur) )
    {
        c = Acec2_Cell(p, cur); Vec_IntPush(vBus, c->Out[0] ^ c->Phase);
        if ( cur == first ) break;
    }
    if ( cur != first ) return 0;
    for ( i = 0, j = Vec_IntSize(vBus)-1; i < j; i++, j-- )
    {
        lit = Vec_IntEntry(vBus, i); Vec_IntWriteEntry(vBus, i, Vec_IntEntry(vBus, j)); Vec_IntWriteEntry(vBus, j, lit);
    }
    for ( i = 0; i < 128 && Vec_IntEntry(vNext, last) >= 0; i++ )
    {
        last = Vec_IntEntry(vNext, last); c = Acec2_Cell(p, last); Vec_IntPush(vBus, c->Out[0] ^ c->Phase);
    }
    if ( Vec_IntEntry(vNext, last) >= 0 || Vec_IntSize(vBus) < 4 || Vec_IntSize(vBus) > 128 ) return 0;
    *pFirst = first; *pLast = last;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Proposes low operand bits preceding the first carry-chain cell.]

  Description [Exact coefficient occurrences take priority. Otherwise the
  weighted column supplies at most four choices. At most sixteen complete
  low-bit combinations are attempted; all remain unproved proposals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ChainLowBits( Acec2_Man_t * p, Vec_Int_t * vMap, Vec_Int_t * vColors,
                              int Tree, int Offset, word Constant, Vec_Int_t * vIds,
                              Vec_Wrd_t * vCoefs, Vec_Wec_t * vLow )
{
    Vec_Int_t * v, * vLeaves = Vec_WecEntry(p->vLeaves, Tree);
    int i, j, id, lit, variants = 1;
    word coef;
    for ( j = 0; j < Offset; j++ )
    {
        v = Vec_WecEntry(vLow, j); Vec_IntClear(v);
        Vec_IntForEachEntry(vIds, id, i)
        {
            coef = Vec_WrdEntry(vCoefs, i); if ( coef >> 63 ) coef = (word)0-coef;
            if ( coef == (Constant << j) )
                Vec_IntPushUnique(v, Abc_Var2Lit(id, (int)(Vec_WrdEntry(vCoefs, i) >> 63)));
        }
        if ( !Vec_IntSize(v) )
            for ( i = 0; i < Vec_IntSize(vLeaves) && Vec_IntSize(v) < 4; i += 2 )
            {
                if ( Vec_IntEntry(vLeaves, i+1) != j ) continue;
                lit = Vec_IntEntry(vLeaves, i);
                if ( lit >= 2 && Vec_IntEntry(vColors, Vec_IntEntry(vMap, lit >> 1) >> 1) == 3 ) Vec_IntPushUnique(v, lit);
            }
        if ( !Vec_IntSize(v) || variants*Vec_IntSize(v) > 16 ) return 0;
        variants *= Vec_IntSize(v);
    }
    return variants;
}

/**Function*************************************************************

  Synopsis    [Proposes a final sum without requiring a carry output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ChainTopBits( Acec2_Man_t * p, Vec_Int_t * vMap, Vec_Int_t * vColors,
                               int Last, int Top, Vec_Int_t * vTops, Acec2_Par_t * pPars, abctime Deadline )
{
    int i, j, n, lit, id = Acec2_Cell(p, Last)->Out[1] >> 1;
    Vec_IntClear(vTops);
    for ( i = 0; i < Vec_IntSize(p->vXors) && Vec_IntSize(vTops) < 8; i += 5 )
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) break;
        n = Vec_IntEntry(p->vXors, i);
        for ( j = 0; j < n; j++ ) if ( Vec_IntEntry(p->vXors, i+1+j) == id ) break;
        if ( j == n ) continue;
        lit = Vec_IntEntry(p->vXors, i+4);
        if ( Vec_IntEntry(vColors, Vec_IntEntry(vMap, lit >> 1) >> 1) != 3 || (lit >> 1) <= (Top >> 1) ) continue;
        Vec_IntPushUnique(vTops, lit);
    }
    Vec_IntPush(vTops, -1);
}

/**Function*************************************************************

  Synopsis    [Proposes constant products from weighted leaves and carry chains.]

  Description [No generator structure is required. A repeated odd coefficient
  suggests a constant; shared sums, low columns, and a possible final XOR
  suggest the operand bus. Only a completed exact product proof installs
  aliases. Other constant-product and Boolean proof paths remain available.]

  SideEffects [Installs completed certificates in private replacement maps.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ConstantProducts( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps,
                                  Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces, Vec_Int_t * vColors,
                                  int Side, int Tree, Acec2_Par_t * pPars, abctime Deadline, int * pnWords,
                                  Hsh_VecMan_t * hTried, int * pnAttempts, Acec2_Templ_t * pTemplates )
{
    Acec2_Man_t * p = m[Side];
    Vec_Int_t * vIds = Vec_IntAlloc(64), * vPrev = NULL, * vNext = NULL;
    Vec_Int_t * vBus = Vec_IntAlloc(64), * vTops = Vec_IntAlloc(8), * vOps[2], * v;
    Vec_Wrd_t * vCoefs = Vec_WrdAlloc(64);
    Vec_Wec_t * vLow = Vec_WecStart(4);
    int i, j, seed, owner, first, last, n, offset, variants, variant, choice, top, flip, nConst, lit, k, merged = 0;
    word coef, constant;
    if ( !Acec2_ChainCoefficients(p, vMaps[Side], vColors, Tree, vIds, vCoefs, pPars, Deadline) ) goto finish;
    vPrev = Vec_IntStartFull(Vec_PtrSize(p->vCells)); vNext = Vec_IntStartFull(Vec_PtrSize(p->vCells));
    if ( !Acec2_ChainLinks(p, vMaps[Side], vColors, vPrev, vNext, pPars, Deadline) ) goto finish;
    for ( seed = 0; seed < Vec_IntSize(vIds) && *pnAttempts < 256 && !Acec2_Stop(pPars, Deadline); seed++ )
    {
        coef = Vec_WrdEntry(vCoefs, seed); if ( coef >> 63 ) coef = (word)0-coef;
        if ( !coef ) continue;
        while ( !(coef & 1) ) coef >>= 1;
        constant = coef; if ( constant <= 1 || constant > 65535 ) continue;
        n = 0;
        Vec_WrdForEachEntry(vCoefs, coef, i)
        {
            owner = Vec_IntEntry(p->vOwner, Vec_IntEntry(vIds, i));
            if ( owner < 0 || (owner & 1) ) continue;
            if ( coef >> 63 ) coef = (word)0-coef;
            if ( !coef ) continue;
            while ( !(coef & 1) ) coef >>= 1;
            n += coef == constant;
        }
        if ( n < 2 ) continue;
        owner = Vec_IntEntry(p->vOwner, Vec_IntEntry(vIds, seed));
        if ( owner < 0 || (owner & 1) || !Acec2_ChainWord(p, owner >> 1, vPrev, vNext, vBus, &first, &last) ) continue;
        coef = Vec_WrdEntry(vCoefs, seed); if ( coef >> 63 ) coef = (word)0-coef;
        offset = 0; while ( !(coef & 1) ) { offset++; coef >>= 1; }
        offset -= Acec2_Cell(p, owner >> 1)->Rank-Acec2_Cell(p, first)->Rank;
        // Within one region, the coefficient and the carry chain must agree
        // on the first column. Partial coefficients can suggest wrong shifts.
        if ( Acec2_Cell(p, first)->Tree == Tree && offset != Acec2_Cell(p, first)->Rank ) continue;
        if ( offset < 0 || offset > 4 ) continue;
        variants = Acec2_ChainLowBits(p, vMaps[Side], vColors, Tree, offset, constant, vIds, vCoefs, vLow);
        if ( !variants ) continue;
        Acec2_ChainTopBits(p, vMaps[Side], vColors, last, Vec_IntEntryLast(vBus), vTops, pPars, Deadline);
        nConst = 0; for ( coef = constant; coef; coef >>= 1 ) nConst++;
        for ( variant = 0; variant < variants && *pnAttempts < 256 && !Acec2_Stop(pPars, Deadline); variant++ )
            for ( top = 0; top < Vec_IntSize(vTops) && *pnAttempts < 256 && !Acec2_Stop(pPars, Deadline); top++ )
                for ( flip = 0; flip < 4 && *pnAttempts < 256 && !Acec2_Stop(pPars, Deadline); flip++ )
                {
                    if ( Vec_IntEntry(vTops, top) < 0 && flip >= 2 ) continue;
                    vOps[0] = Vec_IntAlloc(Vec_IntSize(vBus)+offset+1); vOps[1] = Vec_IntAlloc(nConst);
                    choice = variant;
                    for ( j = 0; j < offset; j++ )
                    {
                        v = Vec_WecEntry(vLow, j); lit = Vec_IntEntry(v, choice % Vec_IntSize(v)) ^ (flip & 1); choice /= Vec_IntSize(v);
                        Vec_IntPush(vOps[0], Vec_IntEntry(vMaps[Side], lit >> 1) ^ (lit & 1));
                    }
                    Vec_IntForEachEntry(vBus, lit, i)
                    {
                        lit ^= flip & 1;
                        Vec_IntPush(vOps[0], Vec_IntEntry(vMaps[Side], lit >> 1) ^ (lit & 1));
                    }
                    lit = Vec_IntEntry(vTops, top);
                    if ( lit >= 0 )
                    { lit ^= flip >> 1; Vec_IntPush(vOps[0], Vec_IntEntry(vMaps[Side], lit >> 1) ^ (lit & 1)); }
                    for ( i = 0; i < nConst; i++ ) Vec_IntPush(vOps[1], (int)((constant >> i) & 1));
                    k = 0;
                    if ( Vec_IntSize(vOps[0])+nConst <= pPars->nMaxWidth )
                        k = Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vOps, Vec_IntSize(vOps[0])+nConst,
                                            pPars, Deadline, pnWords, ACEC2_PRODUCT_CERTIFICATE, hTried, pnAttempts, pTemplates, NULL);
                    Vec_IntFree(vOps[0]); Vec_IntFree(vOps[1]); merged += k;
                    if ( k > 1 ) goto finish;
                }
    }
finish:
    Vec_IntFree(vIds); Vec_IntFreeP(&vPrev); Vec_IntFreeP(&vNext); Vec_IntFree(vBus); Vec_IntFree(vTops);
    Vec_WrdFree(vCoefs); Vec_WecFree(vLow);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Reuses independently detected product operands as proof proposals.]

  Description [Expression records contain original source literals. Map each
  operand to a proved common signal before asking for source-to-reference
  certificates. Profiling and verification therefore use the same bus evidence.]

  SideEffects [Installs only independently certified result bits.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ExpressionProducts( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps,
                                    Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces, Vec_Int_t * vColors,
                                    int Side, int Tree, Acec2_Par_t * pPars, abctime Deadline, int * pnWords,
                                    Hsh_VecMan_t * hTried, int * pnAttempts, Acec2_Templ_t * pTemplates )
{
    Acec2_Expr_t * e = Acec2_Expression(m[Side], Tree);
    Acec2_Product_t * p;
    Vec_Int_t * vOps[2];
    int k, port, i, lit, ok, width, merged = 0;
    if ( !e ) return 0;
    Vec_PtrForEachEntry(Acec2_Product_t *, e->vProducts, p, k)
    {
        if ( *pnAttempts >= 256 || Acec2_Stop(pPars, Deadline) ) break;
        vOps[0] = Vec_IntAlloc(256); vOps[1] = Vec_IntAlloc(256); ok = 1;
        for ( port = 0; port < 2; port++ )
            Vec_IntForEachEntry(p->vOperands[port], lit, i)
            {
                lit = Vec_IntEntry(vMaps[Side], lit >> 1) ^ (lit & 1);
                if ( lit >= 2 && Vec_IntEntry(vColors, lit >> 1) != 3 ) ok = 0;
                Vec_IntPush(vOps[port], lit);
            }
        width = Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1]);
        if ( ok && width >= 4 && width <= pPars->nMaxWidth )
            merged += Acec2_TryProduct(pNew, m, vMaps, vOriginals, vReplaces, vOps, width,
                                      pPars, Deadline, pnWords, ACEC2_PRODUCT_CERTIFICATE, hTried, pnAttempts, pTemplates, NULL);
        Vec_IntFree(vOps[0]); Vec_IntFree(vOps[1]);
    }
    return merged;
}

/**Function*************************************************************

  Synopsis    [Infers product buses and proves internal word correspondences.]

  Description [Both designs may contribute operand proposals. The graph
  search is bounded and ignores inconsistent or ambiguous rank assignments.]

  SideEffects [Writes proved aliases to private replacement maps.]

  SeeAlso     []

***********************************************************************/
int Acec2_MatchProducts( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                        Acec2_Par_t * pPars, abctime Deadline, Acec2_MatchMode_t Mode, int * pnWords, Acec2_Templ_t * pTemplates )
{
    static const Acec2_ProductStage_t Stages[4] = {
        ACEC2_PRODUCT_CERTIFICATE, ACEC2_PRODUCT_TEMPLATE, ACEC2_PRODUCT_BOUNDARY, ACEC2_PRODUCT_SHIFTED
    };
    Vec_Int_t * vColors = Vec_IntStart(Gia_ManObjNum(pNew)), * vEdges, * vColor, * vRank, * vQueue, * v, * vOps[2];
    Hsh_Int1Man_t * h;
    Hsh_VecMan_t * hTried;
    Vec_Wec_t * vAdj;
    Vec_Bit_t * vLive[2];
    Vec_Wrd_t * vOrder[2];
    Acec2_Edge_t * e;
    int side, tree, i, j, k, start, x, y, lit, ok, color, min[2], max[2], count[2], offset, width, shift, shift2;
    int attempts = 0, merged = 0, regionAttempts = 0, stage, order, step, sourceQueries, sourceWords, visited, level;
    int request, slot, unit, scan;
    int nBatch = (pPars->nCecOptions & ACEC2_CEC_DEFER) ? 32 : ABC_INT_MAX;
    int fRecordsOnly = (pPars->nCecOptions & ACEC2_CEC_RECORDS_ONLY) != 0;
    abctime FullDeadline = Deadline, clk = Abc_Clock();
    // Cheap certificate tiers can cover independent words together before
    // rebuilding the surrounding logic. Later, more expensive tiers return
    // to CEC after a smaller batch.
    if ( (pPars->nCecOptions & ACEC2_CEC_DEFER) && pPars->nCecPolyLimit > 0 && pPars->nCecPolyLimit <= 4096 ) nBatch = 128;
    *pnWords = 0;
    if ( pTemplates && !fRecordsOnly ) Acec2_TemplatePending(pTemplates, 1);
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vMaps[side], lit, i) Vec_IntWriteEntry(vColors, lit >> 1, Vec_IntEntry(vColors, lit >> 1) | (1 << side));
    for ( side = 0; side < 2; side++ )
    {
        vLive[side] = Acec2_ProductLive(m[side], vMaps[side], vColors, 1);
        vOrder[side] = Acec2_ProductOrder(m[side], vLive[side]);
    }
    for ( step = fRecordsOnly ? 2 : Mode == ACEC2_MATCH_PENDING ? 3 : Mode == ACEC2_MATCH_BOUNDARY ? 2 : 0;
          step < (fRecordsOnly ? 3 : Mode == ACEC2_MATCH_INITIAL ? 1 : Mode == ACEC2_MATCH_CHEAP ? 2 : 4) && !Acec2_Stop(pPars, FullDeadline); step++ )
    {
        // Independent certificates precede the existing matching paths.
        // A boundary proof can admit extra cut signals and prove that they
        // cancel. Keep that fallback before the shifted-template search.
        stage = Stages[step];
        Deadline = FullDeadline;
        if ( step > 0 )
        {
            Vec_IntFree(vColors); vColors = Vec_IntStart(Gia_ManObjNum(pNew));
            for ( side = 0; side < 2; side++ )
                Vec_IntForEachEntry(vMaps[side], lit, i) Vec_IntWriteEntry(vColors, lit >> 1, Vec_IntEntry(vColors, lit >> 1) | (1 << side));
            for ( side = 0; side < 2; side++ )
            {
                Vec_BitFree(vLive[side]); Vec_WrdFree(vOrder[side]);
                vLive[side] = Acec2_ProductLive(m[side], vMaps[side], vColors, 1);
                vOrder[side] = Acec2_ProductOrder(m[side], vLive[side]);
            }
        }
        // Let cheap structural/certificate matches expose common interfaces
        // first. Remaining regions then request the same source records as
        // standalone profiling, with a bounded and fair proposal queue.
        // BOUNDARY resumes pairwise obligations immediately after source
        // profiling; do not repeat global enrichment on the other cover.
        // The regular and records-only paths retain the shared source queue.
        if ( stage == ACEC2_PRODUCT_BOUNDARY && (Mode != ACEC2_MATCH_BOUNDARY || fRecordsOnly) &&
             pPars->nAnalysisLevel > 0 )
            for ( side = 0; side < 2 && !Acec2_Stop(pPars, Deadline); side++ )
            {
                abctime savedDeadline = m[side]->Deadline;
                Vec_Bit_t * sourceLive;
                if ( Deadline && (!savedDeadline || Deadline < savedDeadline) ) m[side]->Deadline = Deadline;
                sourceQueries = 2; sourceWords = 0; visited = 0;
                level = Abc_MinInt(pPars->nAnalysisLevel, pPars->nCecPolyLimit > 4096 ? 3 : 2);
                // A shared low sum can still identify unshared carry bits.
                // Counter requests keep its source cone below shared cuts.
                sourceLive = Acec2_ProductLive(m[side], vMaps[side], vColors, 0);
                // One queue cannot spend both units before a region is
                // visited. Empty queues cost no unit, and the cursor persists
                // across rounds, including rounds without a new equality.
                for ( request = 0; request < 2*ACEC2_SOURCE_QUEUES && sourceQueries && !Acec2_Stop(pPars, Deadline); request++ )
                {
                    slot = m[side]->iSourceRequest; m[side]->iSourceRequest = (slot+1)%ACEC2_SOURCE_QUEUES; unit = 1;
                    if ( slot == 1 ) sourceWords += Acec2_EnrichMasked(m[side], sourceLive, &unit);
                    else if ( slot == 2 ) sourceWords += Acec2_EnrichCounters(m[side], sourceLive, &unit);
                    else if ( slot == 3 ) sourceWords += Acec2_EnrichCarries(m[side], sourceLive, &unit);
                    else if ( slot == 4 ) sourceWords += Acec2_EnrichPolynomial(m[side], &unit);
                    else for ( scan = 0; scan < Vec_WrdSize(vOrder[side]) && scan < 8 && unit && !Acec2_Stop(pPars, Deadline); scan++ )
                    {
                        order = m[side]->iRegionRequest % Vec_WrdSize(vOrder[side]);
                        m[side]->iRegionRequest = order+1; visited++;
                        tree = (int)(0xFFFFFFFFu-(unsigned)Vec_WrdEntry(vOrder[side], order));
                        if ( Acec2_ProductTreeLive(m[side], vLive[side], tree) )
                            sourceWords += Acec2_EnrichRegion(m[side], tree, level, &unit);
                    }
                    sourceQueries -= 1-unit; m[side]->nSourceWork[slot] += 1-unit;
                }
                Vec_BitFree(sourceLive);
                m[side]->Deadline = savedDeadline;
                if ( pPars->fVerbose ) Abc_Print(1, "On-demand source records: side = %d, level = %d, visited regions = %d, work units = %d, new records = %d.\n",
                    side, level, visited, 2-sourceQueries, sourceWords);
            }
        // New source records may describe a boundary that does not yet
        // correspond across designs. Retain them for the next record pass,
        // while allowing the remaining cheap matching paths to run now.
        // Record creation alone must not repeatedly restart this schedule.
        if ( fRecordsOnly ) goto finish;
        attempts = 0; hTried = Hsh_VecManStart(100);
        if ( stage == ACEC2_PRODUCT_CERTIFICATE )
            for ( side = 0; side < 2 && *pnWords < nBatch && !Acec2_Stop(pPars, Deadline); side++ )
                for ( order = 0; order < Vec_WrdSize(vOrder[side]) && *pnWords < nBatch && attempts < 256 && !Acec2_Stop(pPars, Deadline); order++ )
                {
                    tree = (int)(0xFFFFFFFFu-(unsigned)Vec_WrdEntry(vOrder[side], order));
                    if ( !Acec2_ProductTreeLive(m[side], vLive[side], tree) ) continue;
                    merged += Acec2_ExpressionProducts(pNew, m, vMaps, vOriginals, vReplaces, vColors, side, tree,
                                                       pPars, Deadline, pnWords, hTried, &attempts, pTemplates);
                    merged += Acec2_ConstantProducts(pNew, m, vMaps, vOriginals, vReplaces, vColors, side, tree,
                                                     pPars, Deadline, pnWords, hTried, &attempts, pTemplates);
                }
        for ( side = 0; side < 2 && *pnWords < nBatch && attempts < 256 && !Acec2_Stop(pPars, Deadline); side++ )
            for ( order = 0; order < Vec_WrdSize(vOrder[side]) && *pnWords < nBatch && attempts < 256 && !Acec2_Stop(pPars, Deadline); order++ )
            {
                tree = (int)(0xFFFFFFFFu-(unsigned)Vec_WrdEntry(vOrder[side], order));
                if ( !Acec2_ProductTreeLive(m[side], vLive[side], tree) ) continue;
                if ( Vec_IntSize(Vec_WecEntry(m[side]->vTrees, tree)) < 8 || Vec_IntSize(Vec_WecEntry(m[side]->vLeaves, tree)) > 200000 ) continue;
                if ( stage == ACEC2_PRODUCT_TEMPLATE ) merged += Acec2_ConstantTemplates(pNew, m, vMaps, vOriginals, vReplaces, vColors, side, tree, pPars, Deadline, pnWords, pTemplates);
                h = Hsh_Int1ManStart(100); vAdj = Acec2_ProductGraph(m[side], vMaps[side], vColors, tree, h, &vEdges);
                e = (Acec2_Edge_t *)Vec_IntArray(vEdges); vColor = Vec_IntStartFull(Vec_WecSize(vAdj));
                vRank = Vec_IntStart(Vec_WecSize(vAdj)); vQueue = Vec_IntAlloc(100);
                for ( start = 0; start < Vec_WecSize(vAdj) && *pnWords < nBatch && attempts < 256 && !Acec2_Stop(pPars, Deadline); start++ )
                {
                    if ( Vec_IntEntry(vColor, start) >= 0 || !Vec_IntSize(Vec_WecEntry(vAdj, start)) ) continue;
                    Vec_IntClear(vQueue); Vec_IntPush(vQueue, start); Vec_IntWriteEntry(vColor, start, 0); ok = 1; shift2 = ABC_INT_MAX;
                    min[0] = min[1] = ABC_INT_MAX; max[0] = max[1] = -ABC_INT_MAX; count[0] = count[1] = 0;
                    for ( i = 0; i < Vec_IntSize(vQueue); i++ )
                    {
                        x = Vec_IntEntry(vQueue, i); color = Vec_IntEntry(vColor, x); lit = Vec_IntEntry(vRank, x);
                        min[color] = Abc_MinInt(min[color], lit); max[color] = Abc_MaxInt(max[color], lit); count[color]++;
                        v = Vec_WecEntry(vAdj, x);
                        Vec_IntForEachEntry(v, j, k)
                        {
                            y = e[j].a ^ e[j].b ^ x;
                            if ( Vec_IntEntry(vColor, y) < 0 )
                            { Vec_IntWriteEntry(vColor, y, color ^ 1); Vec_IntWriteEntry(vRank, y, e[j].rank-lit); Vec_IntPush(vQueue, y); }
                            else if ( Vec_IntEntry(vColor, y) == color )
                            {
                                // An odd cycle identifies a square: both operands
                                // use the same bus. Solve its absolute rank offset.
                                shift = (e[j].rank-lit-Vec_IntEntry(vRank, y)) * (color ? -1 : 1);
                                if ( shift2 != ABC_INT_MAX && shift2 != shift ) ok = 0;
                                shift2 = shift;
                            }
                            else if ( Vec_IntEntry(vRank, y) != e[j].rank-lit ) ok = 0;
                        }
                    }
                    if ( stage == ACEC2_PRODUCT_TEMPLATE && !ok && shift2 != ABC_INT_MAX &&
                         Acec2_SquareOperands(vQueue, vAdj, e, h, Vec_IntEntry(m[side]->vWidths, tree), vOps, &offset) )
                    {
                        width = 2*Vec_IntSize(vOps[0]);
                        if ( width <= pPars->nMaxWidth )
                            merged += Acec2_TryProducts(pNew, m, vMaps, vOriginals, vReplaces, vOps, width, pPars, Deadline, pnWords, stage, hTried, &attempts, pTemplates, side, tree, offset, vColors);
                        Vec_IntFree(vOps[0]); Vec_IntFree(vOps[1]); continue;
                    }
                    if ( ok && shift2 != ABC_INT_MAX )
                    {
                        min[0] = ABC_INT_MAX; max[0] = -ABC_INT_MAX;
                        Vec_IntForEachEntry(vQueue, x, i)
                        {
                            lit = 2*Vec_IntEntry(vRank, x)+(Vec_IntEntry(vColor, x) ? -shift2 : shift2);
                            Vec_IntWriteEntry(vRank, x, lit); min[0] = Abc_MinInt(min[0], lit); max[0] = Abc_MaxInt(max[0], lit);
                        }
                        offset = min[0]; count[0] = Vec_IntSize(vQueue);
                        if ( count[0] < 3 || max[0]-min[0] > 510 ) continue;
                        if ( max[0]-min[0]+2 == 2*count[0] )
                        {
                            vOps[0] = Vec_IntStartFull(count[0]);
                            Vec_IntForEachEntry(vQueue, x, i)
                            {
                                lit = Vec_IntEntry(vRank, x)-min[0];
                                if ( (lit & 1) || Vec_IntEntry(vOps[0], lit/2) >= 0 ) { ok = 0; break; }
                                Vec_IntWriteEntry(vOps[0], lit/2, Vec_IntEntry(h->vData, x));
                            }
                            vOps[1] = Vec_IntDup(vOps[0]);
                        }
                        else if ( !Acec2_OverlapOperands(vQueue, vRank, vAdj, e, h, min[0], max[0], vOps) ) continue;
                        width = Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1]);
                        if ( stage == ACEC2_PRODUCT_BOUNDARY ) width = Abc_MinInt(width, Vec_IntEntry(m[side]->vWidths, tree)-offset);
                        if ( ok && width >= 4 && width <= pPars->nMaxWidth )
                        { merged += Acec2_TryProducts(pNew, m, vMaps, vOriginals, vReplaces, vOps, width, pPars, Deadline, pnWords, stage, hTried, &attempts, pTemplates, side, tree, offset, vColors); }
                        Vec_IntFree(vOps[0]); Vec_IntFree(vOps[1]);
                        continue;
                    }
                    if ( !ok || count[0] < 2 || count[1] < 2 || count[0] > 256 || count[1] > 256 ||
                         max[0]-min[0]+1 != count[0] || max[1]-min[1]+1 != count[1] )
                    {
                        if ( shift2 != ABC_INT_MAX || !Acec2_WeightedOperands(m[side], vMaps[side], tree, h, vQueue, vColor, vRank, vOps, &offset) ) continue;
                        width = Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1]);
                        if ( stage == ACEC2_PRODUCT_BOUNDARY ) width = Abc_MinInt(width, Vec_IntEntry(m[side]->vWidths, tree)-offset);
                        if ( width >= 4 && width <= pPars->nMaxWidth )
                        { merged += Acec2_TryProducts(pNew, m, vMaps, vOriginals, vReplaces, vOps, width, pPars, Deadline, pnWords, stage, hTried, &attempts, pTemplates, side, tree, offset, vColors); }
                        Vec_IntFree(vOps[0]); Vec_IntFree(vOps[1]); continue;
                    }
                    vOps[0] = Vec_IntStartFull(count[0]); vOps[1] = Vec_IntStartFull(count[1]);
                    Vec_IntForEachEntry(vQueue, x, i)
                    {
                        color = Vec_IntEntry(vColor, x); lit = Vec_IntEntry(vRank, x)-min[color];
                        if ( Vec_IntEntry(vOps[color], lit) >= 0 ) { ok = 0; break; }
                        Vec_IntWriteEntry(vOps[color], lit, Vec_IntEntry(h->vData, x));
                    }
                    offset = min[0]+min[1]; width = count[0]+count[1];
                    if ( stage == ACEC2_PRODUCT_BOUNDARY ) width = Abc_MinInt(width, Vec_IntEntry(m[side]->vWidths, tree)-offset);
                    if ( ok && width >= 4 && width <= pPars->nMaxWidth )
                    { merged += Acec2_TryProducts(pNew, m, vMaps, vOriginals, vReplaces, vOps, width, pPars, Deadline, pnWords, stage, hTried, &attempts, pTemplates, side, tree, offset, vColors); }
                    Vec_IntFree(vOps[0]); Vec_IntFree(vOps[1]);
                }
                Vec_IntFree(vQueue); Vec_IntFree(vColor); Vec_IntFree(vRank); Vec_IntFree(vEdges); Vec_WecFree(vAdj); Hsh_Int1ManStop(h);
            }
        Hsh_VecManStop(hTried);
        // Batch independent certificates over the same frontier, then return
        // to concrete CEC before starting another recognition stage. This
        // avoids rebuilding the full miter after every component.
        if ( stage == ACEC2_PRODUCT_CERTIFICATE && merged && !Acec2_Stop(pPars, FullDeadline) )
        {
            int update = Acec2_AliasUpdate(pNew, vMaps, vReplaces, pPars, FullDeadline);
            if ( update == -2 ) { merged = -2; goto finish; }
            if ( update == 0 ) merged = 0;
        }
        if ( merged ) break;
    }
    Deadline = FullDeadline;
    if ( !merged && Mode != ACEC2_MATCH_INITIAL && Mode != ACEC2_MATCH_CHEAP )
        for ( side = 0; side < 2 && regionAttempts < 16 && !Acec2_Stop(pPars, Deadline); side++ )
            for ( order = 0; order < Vec_WrdSize(vOrder[side]) && regionAttempts < 16 && !Acec2_Stop(pPars, Deadline); order++ )
            {
                tree = (int)(0xFFFFFFFFu-(unsigned)Vec_WrdEntry(vOrder[side], order));
                if ( !Acec2_ProductTreeLive(m[side], vLive[side], tree) ) continue;
                if ( Vec_IntSize(Vec_WecEntry(m[side]->vTrees, tree)) < 16 ) continue;
                v = Vec_WecEntry(m[side]->vRoots, tree); count[0] = 0;
                for ( i = 0; i < Vec_IntSize(v); i += 2 )
                {
                    lit = Vec_IntEntry(vMaps[side], Vec_IntEntry(v, i) >> 1);
                    count[0] += Vec_IntEntry(vColors, lit >> 1) != 3;
                }
                if ( count[0] < 4 ) continue;
                regionAttempts++;
                merged += Acec2_TryRegion(m, vMaps, vReplaces, vColors, side, tree, pPars, Deadline, pnWords);
            }
    // The caller deadline can interrupt an unvisited part of the traversal.
    // Preserve pending template work without treating interruption as failure.
    if ( Mode != ACEC2_MATCH_INITIAL && pTemplates && Acec2_Stop(pPars, FullDeadline) ) Acec2_TemplateSetPending(pTemplates);
finish:
    if ( pPars->fVerbose ) Abc_Print(1, "Component matching: products = %d, regions = %d, proved words = %d, new root aliases = %d, time = %.3f sec.\n", attempts, regionAttempts, *pnWords, merged, (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    Vec_IntFree(vColors); Vec_BitFree(vLive[0]); Vec_BitFree(vLive[1]);
    Vec_WrdFree(vOrder[0]); Vec_WrdFree(vOrder[1]);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Finds one occurrence of a weighted boundary literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordTerm( Vec_Int_t * v, int Lit, int Rank )
{
    int i;
    for ( i = 0; i < Vec_IntSize(v); i += 2 )
        if ( Vec_IntEntry(v, i) == Lit && Vec_IntEntry(v, i+1) == Rank ) return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Moves a word boundary before partially recognized final adders.]

  Description [A half adder's sum and carry are related. Cutting both as free
  inputs can destroy a prefix carry recurrence. Undo terminal half adders
  and their cell descendants using the checked identities. This proposes
  an independent interface; an exact proof must still certify its result.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Word_t * Acec2_WordBoundary( Acec2_Man_t * m, int Tree )
{
    Acec2_Word_t * w = ABC_CALLOC(Acec2_Word_t, 1);
    Vec_Int_t * v = Vec_WecEntry(m->vTrees, Tree);
    Vec_Wrd_t * vOrder = Vec_WrdAlloc(Vec_IntSize(v));
    Vec_Bit_t * vFinal = Vec_BitStart(Vec_PtrSize(m->vCells));
    Acec2_Cell_t * c;
    word key;
    int i, j, id, owner, a, b, kept = 0;
    w->Tree = Tree; w->Record = -1; w->Width = Acec2_WeightedWidth(Vec_WecEntry(m->vRoots, Tree), m->Pars.nMaxWidth);
    w->vTerms = Vec_IntDup(Vec_WecEntry(m->vRoots, Tree)); w->vConstants = Vec_IntAlloc(16);
    Vec_IntForEachEntry(v, id, i)
    {
        c = Acec2_Cell(m, id);
        Vec_WrdPush(vOrder, ((word)(unsigned)Abc_MinInt(c->Out[0], c->Out[1]) << 32) | (unsigned)id);
    }
    if ( Vec_WrdSize(vOrder) > 1 ) Vec_WrdSort(vOrder, 0);
    Vec_WrdForEachEntry(vOrder, key, i)
    {
        id = (int)(unsigned)key; c = Acec2_Cell(m, id);
        // Functional carry stages also need their original operand interface:
        // cutting their related outputs independently destroys the recurrence.
        // Earlier ordinary compressor stages remain outside this rollback.
        if ( (c->nIns == 2 || c->Proof) &&
             (Acec2_WordTerm(w->vTerms, c->Out[0] ^ c->Phase, c->Rank) >= 0 ||
              Acec2_WordTerm(w->vTerms, c->Out[1] ^ c->Phase, c->Rank+1) >= 0) ) Acec2_BitWrite(vFinal, id, 1);
        for ( j = 0; j < c->nIns; j++ )
        {
            owner = Vec_IntEntry(m->vOwner, c->In[j] >> 1);
            if ( owner >= 0 && Acec2_Cell(m, owner/2)->Tree == Tree && Vec_BitEntry(vFinal, owner/2) )
                Acec2_BitWrite(vFinal, id, 1);
        }
    }
    for ( i = Vec_WrdSize(vOrder)-1; i >= 0; i-- )
    {
        id = (int)(unsigned)Vec_WrdEntry(vOrder, i); c = Acec2_Cell(m, id);
        if ( !Vec_BitEntry(vFinal, id) ) continue;
        a = Acec2_WordTerm(w->vTerms, c->Out[0] ^ c->Phase, c->Rank);
        b = Acec2_WordTerm(w->vTerms, c->Out[1] ^ c->Phase, c->Rank+1);
        if ( a < 0 || b < 0 ) continue;
        Vec_IntWriteEntry(w->vTerms, a, -1); Vec_IntWriteEntry(w->vTerms, b, -1);
        for ( j = 0; j < c->nIns; j++ ) Vec_IntPushTwo(w->vTerms, c->In[j] ^ c->Phase, c->Rank);
        if ( c->nIns == 2 && c->Phase ) Vec_IntPush(w->vConstants, c->Rank);
        w->nRolled++;
    }
    for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 )
        if ( Vec_IntEntry(w->vTerms, i) >= 0 && Vec_IntEntry(w->vTerms, i+1) < w->Width )
        {
            Vec_IntWriteEntry(w->vTerms, kept++, Vec_IntEntry(w->vTerms, i));
            Vec_IntWriteEntry(w->vTerms, kept++, Vec_IntEntry(w->vTerms, i+1));
        }
    Vec_IntShrink(w->vTerms, kept); Vec_WrdFree(vOrder); Vec_BitFree(vFinal);
    return w;
}

/**Function*************************************************************

  Synopsis    [Compresses weighted literals modulo their column width.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_WordCompress( Acec2_Man_t * m, Gia_Man_t * g, Vec_Wec_t * cols )
{
    Vec_Int_t * bits = Vec_IntAlloc(Vec_WecSize(cols)), * v;
    int rank, a, b, c;
    Vec_WecForEachLevel(cols, v, rank)
    {
        while ( Vec_IntSize(v) > 1 )
        {
            if ( Gia_ManObjNum(g) >= 50000 || Acec2_Stopped(m) ) { Vec_IntFree(bits); return NULL; }
            a = Vec_IntPop(v); b = Vec_IntPop(v); c = Vec_IntSize(v) ? Vec_IntPop(v) : 0;
            Vec_IntPush(v, Gia_ManHashXor(g, Gia_ManHashXor(g, a, b), c));
            if ( rank+1 < Vec_WecSize(cols) ) Vec_WecPush(cols, rank+1, Gia_ManHashMaj(g, a, b, c));
        }
        Vec_IntPush(bits, Vec_IntSize(v) ? Vec_IntEntry(v, 0) : 0);
    }
    return bits;
}

/**Function*************************************************************

  Synopsis    [Proves a weighted identity while preserving source correlations.]

  Description [Both sums retain their original fanin cones. No boundary
  signal is made independent. Only the complete modular equality is accepted;
  a counterexample, resource limit or cancellation stores no certificate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveWeightedCut( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, Vec_Int_t * vProducts, Vec_Int_t * vCut, int Width )
{
    Gia_Man_t * g, * q = NULL, * clean; Gia_Obj_t * o;
    Vec_Bit_t * needed = NULL, * boundary = NULL; Vec_Int_t * map = NULL, * sums[2] = {NULL, NULL}, * terms;
    Vec_Wec_t * cols = NULL; Acec2_Par_t pars;
    Vec_Wrd_t * inputs, * outputs; word state = ABC_CONST(0x7951AD8C632EBF07);
    int side, i, j, lit, rank, a, b, count = 0, result = -1;
    if ( !m || !vOutputs || !vTerms || !vConstants || Width < 1 ||
         (Vec_IntSize(vOutputs) & 1) || (Vec_IntSize(vTerms) & 1) || (vProducts && Vec_IntSize(vProducts) % 4) || Acec2_Stopped(m) ) return -1;
    m->fWeightedTruth = 0;
    if ( Width > 512 || Width > m->Pars.nMaxWidth || Vec_IntSize(vOutputs) > 2048 || Vec_IntSize(vTerms) > 2048 || Vec_IntSize(vConstants) > 2048 || (vProducts && Vec_IntSize(vProducts) > 4096) )
    { m->nWeightedLimits++; return -1; }
    g = m->pGia; needed = Vec_BitStart(Gia_ManObjNum(g));
    boundary = Vec_BitStart(Gia_ManObjNum(g));
    if ( vCut ) Vec_IntForEachEntry(vCut, lit, i)
    {
        if ( lit < 2 || (lit >> 1) >= Gia_ManObjNum(g) || Gia_ObjIsCo(Gia_ManObj(g, lit >> 1)) ) goto finish;
        Acec2_BitWrite(boundary, lit >> 1, 1);
    }
    for ( side = 0; side < 2; side++ )
    {
        terms = side ? vTerms : vOutputs;
        for ( i = 0; i < Vec_IntSize(terms); i += 2 )
        {
            lit = Vec_IntEntry(terms, i); rank = Vec_IntEntry(terms, i+1);
            if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(g) || rank < 0 || rank >= Width || Gia_ObjIsCo(Gia_ManObj(g, lit >> 1)) ) goto finish;
            Acec2_BitWrite(needed, lit >> 1, 1);
        }
    }
    if ( vProducts ) for ( i = 0; i < Vec_IntSize(vProducts); i += 4 )
    {
        rank = Vec_IntEntry(vProducts, i+2);
        if ( rank < 0 || rank >= Width || (Vec_IntEntry(vProducts, i+3) & ~1) ) goto finish;
        for ( j = 0; j < 2; j++ )
        {
            lit = Vec_IntEntry(vProducts, i+j);
            if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(g) || Gia_ObjIsCo(Gia_ManObj(g, lit >> 1)) ) goto finish;
            Acec2_BitWrite(needed, lit >> 1, 1);
        }
    }
    Vec_IntForEachEntry(vConstants, rank, i) if ( rank < 0 || rank >= Width ) goto finish;
    m->nWeightedAttempts++;
    for ( i = Gia_ManObjNum(g)-1; i > 0; i-- )
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( !Vec_BitEntry(needed, i) ) continue;
        if ( ++count > 40000 ) goto finish;
        o = Gia_ManObj(g, i); if ( Gia_ObjIsCi(o) || Vec_BitEntry(boundary, i) ) continue;
        if ( !Gia_ObjIsAnd(o) ) goto finish;
        Acec2_BitWrite(needed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(needed, Gia_ObjFaninId1(o, i), 1);
        if ( Gia_ObjIsMux(g, o) ) Acec2_BitWrite(needed, Gia_ObjFaninId2(g, i), 1);
    }
    q = Gia_ManStart(1000); Gia_ManHashAlloc(q); map = Vec_IntStart(Gia_ManObjNum(g));
    for ( i = 1; i < Gia_ManObjNum(g); i++ )
        if ( Vec_BitEntry(needed, i) && (Gia_ObjIsCi(Gia_ManObj(g, i)) || Vec_BitEntry(boundary, i)) )
            Vec_IntWriteEntry(map, i, Gia_ManAppendCi(q));
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( Vec_BitEntry(needed, i) && !Vec_BitEntry(boundary, i) ) Vec_IntWriteEntry(map, i, Acec2_MapNode(g, q, map, o, i));
        if ( Gia_ManObjNum(q) >= 50000 ) goto finish;
    }
    for ( side = 0; side < 2; side++ )
    {
        terms = side ? vTerms : vOutputs; cols = Vec_WecStart(Width);
        for ( i = 0; i < Vec_IntSize(terms); i += 2 )
        {
            lit = Vec_IntEntry(terms, i); rank = Vec_IntEntry(terms, i+1);
            Vec_WecPush(cols, rank, Vec_IntEntry(map, lit >> 1) ^ (lit & 1));
        }
        if ( side ) Vec_IntForEachEntry(vConstants, rank, i) Vec_WecPush(cols, rank, 1);
        if ( side && vProducts ) for ( i = 0; i < Vec_IntSize(vProducts); i += 4 )
        {
            a = Vec_IntEntry(vProducts, i); b = Vec_IntEntry(vProducts, i+1);
            a = Vec_IntEntry(map, a >> 1) ^ (a & 1); b = Vec_IntEntry(map, b >> 1) ^ (b & 1);
            lit = Gia_ManHashAnd(q, a, b) ^ Vec_IntEntry(vProducts, i+3);
            Vec_WecPush(cols, Vec_IntEntry(vProducts, i+2), lit);
        }
        sums[side] = Acec2_WordCompress(m, q, cols); Vec_WecFreeP(&cols);
        if ( !sums[side] ) goto finish;
    }
    for ( i = 0; i < Width; i++ )
    { Gia_ManAppendCo(q, Vec_IntEntry(sums[0], i)); Gia_ManAppendCo(q, Vec_IntEntry(sums[1], i)); }
    Gia_ManHashStop(q); clean = Gia_ManCleanup(q); Gia_ManStop(q); q = clean;
    if ( Gia_ManCiNum(q) )
    {
        inputs = Vec_WrdStart(Gia_ManCiNum(q));
        for ( i = 0; i < Vec_WrdSize(inputs); i++ ) Vec_WrdWriteEntry(inputs, i, (Acec2_Random(&state) & ~(word)3) | 2);
        outputs = Gia_ManSimPatSimOut(q, inputs, 1);
        for ( i = 0; i < 2*Width; i += 2 )
            if ( Vec_WrdEntry(outputs, i) != Vec_WrdEntry(outputs, i+1) ) { result = 0; break; }
        Vec_WrdFree(inputs); Vec_WrdFree(outputs);
        if ( result == 0 ) goto finish;
    }
    result = Acec2_WeightedTruth(m, q);
    if ( result >= 0 ) { m->fWeightedTruth = result == 1; goto finish; }
    if ( Acec2_Stopped(m) ) goto finish;
    pars = m->Pars; pars.fVerbose = 0;
    result = Acec2_ProveBounded(q, &pars, m->Deadline, 16);
finish:
    if ( result >= 0 && Acec2_Stopped(m) ) result = -1;
    m->nWeightedLimits += result < 0; m->nWeightedProved += result == 1;
    if ( q ) Gia_ManStop(q);
    Vec_BitFreeP(&needed); Vec_BitFreeP(&boundary); Vec_IntFreeP(&map); Vec_IntFreeP(&sums[0]); Vec_IntFreeP(&sums[1]); Vec_WecFreeP(&cols);
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks the linear special case of a weighted source identity.]

  Description [Explicit product terms, when present in the general checker,
  are literal-pair, rank and output-phase tuples. Their ANDs are constructed
  only in the private proof graph; source node identities remain unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveWeightedProducts( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width )
{
    return Acec2_ProveWeightedCut(m, vOutputs, vTerms, vConstants, vProducts, NULL, Width);
}

/**Function*************************************************************

  Synopsis    [Checks weighted literals on their complete source cones.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveWeighted( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, int Width )
{
    return Acec2_ProveWeightedProducts(m, vOutputs, vTerms, vConstants, NULL, Width);
}

/**Function*************************************************************

  Synopsis    [Copies only the reference cones above an explicit independent cut.]

  Description [Product bits need not be a structural separator of the final
  adder. A lower cut preserves their shared carry and extension logic in
  both sides of the exact comparison. No correspondence is assumed.]

  SideEffects [Appends source logic to the reference graph.]

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_WordSourceMap( Acec2_Man_t * m, Acec2_Word_t * w, Hsh_Int1Man_t * h, Gia_Man_t * g )
{
    Gia_Man_t * source = m->pGia; Gia_Obj_t * o;
    Vec_Bit_t * needed = Vec_BitStart(Gia_ManObjNum(source));
    Vec_Int_t * map = Vec_IntStartFull(Gia_ManObjNum(source));
    int i, id, lit, count = 0, valid = 0;
    Vec_IntWriteEntry(map, 0, 0);
    Vec_IntForEachEntry(h->vData, id, i) Vec_IntWriteEntry(map, id, 2*(i+1));
    for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 ) Acec2_BitWrite(needed, Vec_IntEntry(w->vTerms, i) >> 1, 1);
    for ( i = Gia_ManObjNum(source)-1; i > 0; i-- )
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( !Vec_BitEntry(needed, i) || Vec_IntEntry(map, i) >= 0 ) continue;
        o = Gia_ManObj(source, i);
        if ( !Gia_ObjIsAnd(o) ) goto finish;
        if ( ++count >= 40000 ) { m->nWordLimits++; goto finish; }
        Acec2_BitWrite(needed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(needed, Gia_ObjFaninId1(o, i), 1);
        if ( Gia_ObjIsMux(source, o) ) Acec2_BitWrite(needed, Gia_ObjFaninId2(source, i), 1);
    }
    Gia_ManForEachAnd(source, o, i)
    {
        if ( !Vec_BitEntry(needed, i) || Vec_IntEntry(map, i) >= 0 ) continue;
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) goto finish;
        lit = Acec2_MapNode(source, g, map, o, i); Vec_IntWriteEntry(map, i, lit);
        if ( Gia_ManObjNum(g) >= 50000 ) { m->nWordLimits++; goto finish; }
    }
    valid = !Acec2_Stopped(m);
finish:
    Vec_BitFree(needed); if ( !valid ) Vec_IntFreeP(&map); return map;
}

/**Function*************************************************************

  Synopsis    [Builds the weighted boundary sum over free cut variables.]

  Description [The reference is explicitly modulo 2^Width.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_WordReference( Acec2_Man_t * m, Acec2_Word_t * w, Hsh_Int1Man_t * h )
{
    Gia_Man_t * g = Gia_ManStart(1000), * clean;
    Vec_Wec_t * vCols = Vec_WecStart(w->Width);
    Vec_Int_t * vBits = NULL, * sourceMap = NULL;
    int i, lit, rank;
    Gia_ManHashAlloc(g);
    for ( i = 0; i < Hsh_Int1ManEntryNum(h); i++ ) Gia_ManAppendCi(g);
    if ( w->vSourceCut ) { sourceMap = Acec2_WordSourceMap(m, w, h, g); if ( !sourceMap ) goto fail; }
    if ( w->fPolynomial )
    {
        Acec2_Record_t * r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, w->Record);
        Vec_Int_t * map = Vec_IntStart(Gia_ManObjNum(m->pGia)), * constants = Vec_IntStart(w->Width);
        int valid;
        Vec_IntForEachEntry(r->vCut, lit, i)
            Vec_IntWriteEntry(map, lit >> 1, 2*(Acec2_IndexLookup(h, lit >> 1)+1));
        valid = Acec2_RecordColumns(r, g, map, NULL, vCols, constants, &m->Pars, m->Deadline, 50000);
        Vec_IntForEachEntry(constants, lit, i) if ( lit ) Vec_WecPush(vCols, i, 1);
        Vec_IntFree(map); Vec_IntFree(constants);
        if ( !valid ) goto fail;
    }
    for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 )
    {
        lit = Vec_IntEntry(w->vTerms, i); rank = Vec_IntEntry(w->vTerms, i+1);
        if ( rank >= w->Width ) continue;
        if ( lit >= 2 ) lit = sourceMap ? Vec_IntEntry(sourceMap, lit >> 1) ^ (lit & 1) : Abc_Var2Lit(Acec2_IndexLookup(h, lit >> 1)+1, lit & 1);
        Vec_WecPush(vCols, rank, lit);
    }
    Vec_IntForEachEntry(w->vConstants, rank, i) if ( rank < w->Width ) Vec_WecPush(vCols, rank, 1);
    vBits = Acec2_WordCompress(m, g, vCols); if ( !vBits ) goto fail;
    Vec_IntForEachEntry(vBits, lit, i) Gia_ManAppendCo(g, lit);
    Gia_ManHashStop(g); clean = Gia_ManCleanup(g); Gia_ManStop(g);
    Vec_WecFree(vCols); Vec_IntFree(vBits); Vec_IntFreeP(&sourceMap);
    return clean;
fail:
    Gia_ManStop(g); Vec_WecFree(vCols); Vec_IntFreeP(&vBits); Vec_IntFreeP(&sourceMap); return NULL;
}

/**Function*************************************************************

  Synopsis    [Checks remaining boundary logic with ordinary correspondence.]

  Description [The proposed word and the weighted record roots share their
  original source cones. The comparison preserves dependencies that would
  be lost by cutting the roots independently. Only a completed Boolean
  proof promotes the binary boundary; the record already certifies its sum.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordBoundaryProve( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vBits )
{
    Gia_Man_t * g = m->pGia, * q = NULL, * clean;
    Gia_Obj_t * o;
    Vec_Bit_t * needed = NULL;
    Vec_Int_t * map = NULL, * sum = NULL;
    Vec_Wec_t * cols = NULL;
    Acec2_Par_t pars = m->Pars;
    int width = Vec_IntSize(vBits), i, lit, rank, count = 0, result = 0;
    if ( r->vOutputMasks || width < 1 || width > r->Width || Acec2_Stopped(m) || !Acec2_RecordCheck(m, r) ) return 0;
    needed = Vec_BitStart(Gia_ManObjNum(g));
    Vec_IntForEachEntry(vBits, lit, i) Acec2_BitWrite(needed, lit >> 1, 1);
    for ( i = 0; i < Vec_IntSize(r->vOutputs); i += 2 )
        if ( Vec_IntEntry(r->vOutputs, i+1) < width ) Acec2_BitWrite(needed, Vec_IntEntry(r->vOutputs, i) >> 1, 1);
    for ( i = Gia_ManObjNum(g)-1; i > 0; i-- )
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( !Vec_BitEntry(needed, i) ) continue;
        if ( ++count >= 40000 ) { m->nWordLimits++; goto finish; }
        o = Gia_ManObj(g, i); if ( !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(needed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(needed, Gia_ObjFaninId1(o, i), 1);
        if ( Gia_ObjIsMux(g, o) ) Acec2_BitWrite(needed, Gia_ObjFaninId2(g, i), 1);
    }
    q = Gia_ManStart(1000); Gia_ManHashAlloc(q); map = Vec_IntStart(Gia_ManObjNum(g)); cols = Vec_WecStart(width);
    Gia_ManForEachCi(g, o, i) if ( Vec_BitEntry(needed, Gia_ObjId(g, o)) ) Vec_IntWriteEntry(map, Gia_ObjId(g, o), Gia_ManAppendCi(q));
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( Vec_BitEntry(needed, i) ) Vec_IntWriteEntry(map, i, Acec2_MapNode(g, q, map, o, i));
        if ( Gia_ManObjNum(q) >= 50000 ) { m->nWordLimits++; goto finish; }
    }
    for ( i = 0; i < Vec_IntSize(r->vOutputs); i += 2 )
    {
        lit = Vec_IntEntry(r->vOutputs, i); rank = Vec_IntEntry(r->vOutputs, i+1);
        if ( rank < width ) Vec_WecPush(cols, rank, Vec_IntEntry(map, lit >> 1) ^ (lit & 1));
    }
    sum = Acec2_WordCompress(m, q, cols); if ( !sum ) { m->nWordLimits++; goto finish; }
    Vec_IntForEachEntry(vBits, lit, i)
    {
        Gia_ManAppendCo(q, Vec_IntEntry(map, lit >> 1) ^ (lit & 1));
        Gia_ManAppendCo(q, Vec_IntEntry(sum, i));
    }
    Gia_ManHashStop(q); clean = Gia_ManCleanup(q); Gia_ManStop(q); q = clean;
    pars.fVerbose = 0; m->nWordCecAttempts++;
    // The sweep can spend two iterations leaving its color-restricted
    // modes when the source cones are already shared. Allow the subsequent
    // unrestricted correspondence round to check the boundary itself.
    result = Acec2_ProveBounded(q, &pars, m->Deadline, 4) == 1 && !Acec2_Stopped(m);
    m->nWordCecProved += result;
finish:
    if ( q ) Gia_ManStop(q);
    Vec_BitFreeP(&needed); Vec_IntFreeP(&map); Vec_IntFreeP(&sum); Vec_WecFreeP(&cols); return result;
}

/**Function*************************************************************

  Synopsis    [Checks an unresolved linear word with exact cut polynomials.]

  Description [Both extracted graphs already use independent cut inputs.
  Completed equality certifies all bits. Rejections and deterministic effort
  limits are reusable, while interrupted checks remain retryable. This path
  does not invoke word closure recursively during component analysis.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordPolyProve( Acec2_Man_t * m, Gia_Man_t * a, Gia_Man_t * b )
{
    Gia_Man_t * g[2] = {a, b};
    Acec2_Man_t * analyses[2] = {NULL, NULL};
    Acec2_Par_t pars = m->Pars;
    Vec_Int_t * empty = NULL, * roots[2];
    int side, cache, saved, result = -1, effort = 0, cancelled = 0, limit;
    if ( !a || !b || !pars.fAlgebra || Acec2_Stopped(m) ||
         (ABC_INT64_T)Gia_ManObjNum(a)+Gia_ManObjNum(b) > 50000 ) return -1;
    // A linear cut may contain a full carry-save array of independent bit
    // products. Its intermediate carry substitutions need more terms than
    // the final linear polynomial, but the allowance still scales with the
    // cut rather than a wall-clock slice.
    limit = Abc_MaxInt(1024, 32*Gia_ManCiNum(a)+1024);
    if ( !pars.pCancelled ) pars.pCancelled = &cancelled;
    empty = Vec_IntAlloc(0); roots[0] = roots[1] = empty;
    cache = Acec2_BoundaryCache(m, g, roots, NULL, Gia_ManCoNum(a), ACEC2_CACHE_LINEAR_WORD, 0);
    Vec_IntFree(empty);
    saved = Acec2_ProofCacheRead(m->vFailedProofs, cache, limit, &pars);
    if ( saved ) { m->nWordPolyHits++; return saved == 1 ? 1 : -1; }
    m->nWordPolyAttempts++; pars.fVerbose = 0;
    for ( side = 0; side < 2 && !cancelled && !Acec2_Stopped(m); side++ )
    {
        analyses[side] = Acec2_AnalyzeCells(g[side], &pars, m->Deadline);
        if ( !analyses[side] ) goto finish;
        analyses[side]->nPolyTermLimit = limit;
    }
    if ( !cancelled && !Acec2_Stopped(m) && analyses[0] && analyses[1] )
        result = Acec2_PolyCompareQuiet(analyses[0], analyses[1], m->Deadline);
    for ( side = 0; side < 2; side++ ) effort |= analyses[side] && analyses[side]->fPolyEffortLimit;
    if ( cache >= 0 && !cancelled && !Acec2_Stopped(m) && (result >= 0 || effort) )
        Acec2_ProofCacheWrite(m->vFailedProofs, cache, limit, &pars, result, effort);
finish:
    if ( cancelled ) m->fStopped = m->fCancelled = 1;
    if ( Acec2_Stopped(m) ) result = -1;
    m->nWordPolyProved += result == 1; m->nWordPolyLimits += result < 0;
    Acec2_Free(analyses[0]); Acec2_Free(analyses[1]);
    return result == 1 ? 1 : -1;
}

/**Function*************************************************************

  Synopsis    [Sweeps a proposed word while retaining shared source logic.]

  Description [An operand cut may leave product carries on both sides.
  Ordinary correspondence can merge these before the final-adder queries.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordCecProve( Acec2_Man_t * m, Gia_Man_t * a, Gia_Man_t * b, Vec_Wrd_t * values )
{
    Gia_Man_t * g, * reduced;
    Cec_ParFra_t pars; Cec_ParLimit_t limits; Cec_ParEffort_t effort;
    int i, result = -1;
    if ( !a || !b || Acec2_Stopped(m) ) return -1;
    if ( (ABC_INT64_T)Gia_ManObjNum(a)+Gia_ManObjNum(b) > 50000 ) { m->nWordLimits++; return -1; }
    g = Gia_ManMiter(a, b, 0, 1, 0, 0, 0); if ( !g ) return -1;
    Gia_ManEquivFixOutputPairs(g);
    reduced = Gia_ManCleanup(g); Gia_ManStop(g); g = reduced;
    Cec_ManFraSetDefaultParams(&pars);
    // A productive correspondence round may expose only one adder stage.
    // Total queries/conflicts bound the work; eight rounds can stop a cheap
    // proof well before its ripple or compressor dependency chain closes.
    pars.nItersMax = 128; pars.nBTLimit = 1000; pars.nWords = 4; pars.nRounds = 8;
    pars.fCheckMiter = pars.fDualOut = 1;
    limits.TimeToStop = m->Deadline; limits.RunId = m->Pars.RunId;
    limits.pFuncStop = m->Pars.pFuncStop; limits.pCancelled = m->Pars.pCancelled; pars.pLimits = &limits;
    memset(&effort, 0, sizeof(effort)); effort.nCallsMax = 2048; effort.nConflictsMax = 16000; pars.pEffort = &effort;
    m->nWordCecAttempts++;
    reduced = Cec_ManSatSweeping(g, &pars, 1);
    if ( reduced )
    {
        result = 1;
        for ( i = 0; i < Gia_ManCoNum(reduced); i += 2 )
            if ( Gia_ObjFaninLit0p(reduced, Gia_ManCo(reduced, i)) != Gia_ObjFaninLit0p(reduced, Gia_ManCo(reduced, i+1)) ) result = -1;
    }
    else if ( g->pCexComb && g->pCexComb->nPis == Vec_WrdSize(values) && Gia_ManVerifyCex(g, g->pCexComb, 1) )
    {
        // A rare high-bit mismatch must refine discovery even when a flat
        // SAT query cannot get through the shared arithmetic cones.
        for ( i = 0; i < Vec_WrdSize(values); i++ )
            Vec_WrdWriteEntry(values, i, Abc_InfoHasBit(g->pCexComb->pData, g->pCexComb->nRegs+i) ? ~(word)0 : 0);
        result = 0;
    }
    if ( Acec2_Stopped(m) ) result = -1;
    if ( m->Pars.fVerbose ) Abc_Print(1, "Word CEC: result = %d, queries = %d, conflicts = %lld.\n",
        result, effort.nCalls, (long long)effort.nConflicts);
    m->nWordLimits += result < 0;
    m->nWordCecProved += result == 1;
    if ( reduced ) Gia_ManStop(reduced);
    Gia_ManStop(g); return result;
}

/**Function*************************************************************

  Synopsis    [Certifies every word bit with bounded SAT or exact algebra.]

  Description [Successful SAT queries certify individual bits. Up to 64
  counterexamples refine all result positions together. A limited SAT check
  can use an independently checked polynomial equality over the same free
  cut. Caller cancellation and the overall deadline remain active.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordProve( Acec2_Man_t * m, Gia_Man_t * a, Gia_Man_t * b, Vec_Wrd_t * vValues, int * pnProved )
{
    Gia_Man_t * g = NULL;
    Gia_Obj_t * o, * ci;
    sat_solver * sat = NULL;
    int i, j, lit = 1, status, result = -1, start, limit, nCex = 0, unknown = 0;
    *pnProved = 0;
    if ( !a || !b || Acec2_Stopped(m) ) goto finish;
    g = Gia_ManMiter(a, b, 0, 0, 0, 0, 0);
    if ( !g || Gia_ManXorNum(g) || Gia_ManMuxNum(g) || Acec2_Stopped(m) ) goto finish;
    if ( Gia_ManObjNum(g) > 50000 ) { m->nWordLimits++; goto finish; }
    sat = sat_solver_new(); sat_solver_setnvars(sat, Gia_ManObjNum(g));
    sat_solver_set_runtime_limit(sat, m->Deadline); sat_solver_set_runid(sat, m->Pars.RunId);
    sat_solver_set_stop_func(sat, m->Pars.pFuncStop); sat_solver_set_stop_flag(sat, m->Pars.pCancelled);
    if ( !sat_solver_addclause(sat, &lit, &lit+1) ) goto finish;
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( !sat_solver_add_and(sat, i, Gia_ObjFaninId0(o, i), Gia_ObjFaninId1(o, i), Gia_ObjFaninC0(o), Gia_ObjFaninC1(o), 0) ) goto finish;
    }
    Gia_ManForEachCo(g, o, i)
    {
        if ( Acec2_Stopped(m) ) goto finish;
        limit = Abc_MinInt(1000, 20000-(m->nWordConflicts-m->nWordConflictStart));
        if ( limit <= 0 ) { m->nWordLimits++; unknown = 1; break; }
        lit = Gia_ObjFaninLit0p(g, o); start = sat_solver_nconflicts(sat);
        status = sat_solver_solve(sat, &lit, &lit+1, limit, 0, 0, 0);
        m->nWordConflicts += sat_solver_nconflicts(sat)-start;
        // A difficult low bit must not hide an easy counterexample in a
        // later proposal bit. Refine those candidates within the same total
        // conflict budget before attempting a whole-word arithmetic proof.
        if ( status == l_Undef ) { m->nWordLimits++; unknown = 1; continue; }
        if ( status == l_True )
        {
            if ( !nCex ) Vec_WrdFill(vValues, Gia_ManCiNum(g), 0);
            Gia_ManForEachCi(g, ci, j)
                if ( sat_solver_var_value(sat, Gia_ObjId(g, ci)) )
                    Vec_WrdWriteEntry(vValues, j, Vec_WrdEntry(vValues, j) | ((word)1 << nCex));
            if ( ++nCex == 64 ) break;
            continue;
        }
        if ( *pnProved == i ) *pnProved = i+1;
        lit ^= 1;
        if ( !sat_solver_addclause(sat, &lit, &lit+1) ) goto finish;
    }
    result = nCex ? 0 : unknown ? -1 : 1;
finish:
    if ( Acec2_Stopped(m) ) result = -1;
    if ( sat ) sat_solver_delete(sat);
    if ( g ) Gia_ManStop(g);
    if ( result < 0 && !Acec2_Stopped(m) && Acec2_WordPolyProve(m, a, b) == 1 )
    { result = 1; *pnProved = Gia_ManCoNum(a); }
    return result;
}

/**Function*************************************************************

  Synopsis    [Locates and certifies a result word inside one design.]

  Description [Independent simulation proposes existing result signals.
  The original extracted cones are then compared with the weighted sum.
  A missing high result bit can leave a useful lower prefix; its reduced
  modulus is explicit. Every retained bit still needs an exact proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordDiscover( Acec2_Man_t * m, Acec2_Word_t * w, Vec_Int_t * vMap, int minimum )
{
    Hsh_Int1Man_t * h = Hsh_Int1ManStart(100);
    Acec2_WordSim_t * s = NULL;
    Gia_Man_t * model = NULL, * extracted = NULL;
    Vec_Wrd_t * vValues = NULL, * vExpected = NULL;
    Vec_Int_t * vBits = NULL, * vBest = NULL;
    word state = ABC_CONST(0x7163F49A53B281ED);
    int i, round, lit, proof, proved, prefix, refinement, boundaryPrefix, sourceProof, result = 0;
    if ( w->Width < minimum ) goto finish;
    if ( w->vSourceCut )
    {
        Vec_IntForEachEntry(w->vSourceCut, lit, i)
            if ( lit < 2 || (lit & 1) || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ) goto finish;
            else Acec2_IndexAdd(h, lit >> 1);
    }
    else for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 )
    { lit = Vec_IntEntry(w->vTerms, i); if ( lit >= 2 ) Acec2_IndexAdd(h, lit >> 1); }
    if ( w->fPolynomial )
    {
        Acec2_Record_t * r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, w->Record);
        Vec_IntForEachEntry(r->vCut, lit, i) Acec2_IndexAdd(h, lit >> 1);
    }
    if ( !Hsh_Int1ManEntryNum(h) || Hsh_Int1ManEntryNum(h) > 1024 || Acec2_Stopped(m) ) goto finish;
    s = Acec2_WordSimCached(m, vMap, h, w->Width); Vec_WecShrink(s->vCandidates, w->Width);
    Acec2_WordPrioritize(s, m); model = Acec2_WordReference(m, w, h);
    if ( !model ) { m->nWordLimits++; goto finish; }
    vValues = Vec_WrdStart(Hsh_Int1ManEntryNum(h)); vExpected = Vec_WrdStart(w->Width);
    for ( round = 0; round < 4 && !Acec2_Stopped(m); round++ )
    {
        // Uniform and directed carry patterns complement random filtering.
        for ( i = 0; i < Vec_WrdSize(vValues); i++ )
            Vec_WrdWriteEntry(vValues, i, (Acec2_Random(&state) & ~(word)3) | 2);
        Acec2_WordCarryPatterns(w, h, vValues, round);
        Acec2_WordOperandPatterns(m, w, h, vValues, round);
        Acec2_ModelPatterns(NULL, h, vValues, vExpected, w->Width, model);
        Acec2_WordSimulate(s, vValues, vExpected, round);
        for ( i = 0; i < minimum; i++ ) if ( !Vec_IntSize(Vec_WecEntry(s->vCandidates, i)) ) goto finish;
    }
    if ( Acec2_Stopped(m) ) goto finish;
    for ( round = 0; round < 16 && !Acec2_Stopped(m); round++ )
    {
        for ( prefix = 0; prefix < w->Width; prefix++ ) if ( !Vec_IntSize(Vec_WecEntry(s->vCandidates, prefix)) ) break;
        if ( prefix < minimum ) goto finish;
        if ( prefix < w->Width )
        {
            w->Width = prefix; Vec_WecShrink(s->vCandidates, prefix); Vec_WrdShrink(vExpected, prefix);
            Gia_ManStop(model); model = Acec2_WordReference(m, w, h);
            if ( !model ) { m->nWordLimits++; goto finish; }
        }
        extracted = Acec2_ExtractWord(s, 0, w->Width, w->Width, Hsh_Int1ManEntryNum(h), &vBits, NULL, h, 1, model);
        refinement = boundaryPrefix = 0;
        if ( extracted )
        {
            Gia_Man_t * pair[2] = {model, extracted};
            refinement = Acec2_RefineProduct(pair, NULL, NULL, h, vValues, vExpected, w->Width, &m->Pars, m->Deadline, model);
            if ( refinement < 0 ) { m->fStopped = 1; goto finish; }
        }
        if ( refinement == 2 ) { proof = 0; proved = 0; }
        else if ( refinement == 1 ) { proof = 1; proved = w->Width; }
        else if ( w->vSourceCut && (sourceProof = Acec2_WordCecProve(m, model, extracted, vValues)) >= 0 )
        { proof = sourceProof; proved = proof ? w->Width : 0; }
        else if ( w->vSourceCut && vBits &&
                  (boundaryPrefix = Acec2_PolyLinearPrefix(m, w, vBits)) == w->Width )
        { proof = 1; proved = w->Width; w->fSource = 1; }
        else if ( Hsh_Int1ManEntryNum(h) >= 32 && Acec2_WordPolyProve(m, model, extracted) == 1 )
        { proof = 1; proved = w->Width; }
        else if ( w->fPolynomial && vBits &&
             (Acec2_WordBoundaryProve(m, (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, w->Record), vBits) ||
              (boundaryPrefix = Acec2_PolyWordBoundaryPrefix(m, (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, w->Record), vBits)) == w->Width) )
        { proof = 1; proved = w->Width; }
        else
        {
            proof = Acec2_WordProve(m, model, extracted, vValues, &proved);
            proved = Abc_MaxInt(proved, boundaryPrefix);
            if ( w->vSourceCut && boundaryPrefix ) w->fSource = 1;
        }
        if ( m->Pars.fVerbose && proof != 1 )
            Abc_Print(1, "Word closure region %d: refinement %d, proved prefix %d/%d, %s.\n",
                w->Tree, round+1, proved, w->Width, proof == 0 ? "counterexample" : "proof limit");
        if ( proof == 1 ) { w->vBits = vBits; vBits = NULL; result = 1; break; }
        if ( proved >= minimum && (!vBest || proved > Vec_IntSize(vBest)) )
        {
            Vec_IntFreeP(&vBest); vBest = Vec_IntDup(vBits); Vec_IntShrink(vBest, proved);
        }
        if ( proof < 0 ) goto finish;
        // Real mismatches refine every candidate on the failing assignments.
        // Random agreement alone can mistake a rare carry for a result bit.
        Acec2_ModelPatterns(NULL, h, vValues, vExpected, w->Width, model);
        Acec2_WordSimulate(s, vValues, vExpected, 1);
        Gia_ManStop(extracted); extracted = NULL; Vec_IntFreeP(&vBits);
    }
    if ( round == 16 ) m->nWordLimits++;
finish:
    if ( !result && vBest && !Acec2_Stopped(m) )
    { w->Width = Vec_IntSize(vBest); w->vBits = vBest; vBest = NULL; result = 1; }
    if ( result )
    {
        int kept = 0;
        for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 )
            if ( Vec_IntEntry(w->vTerms, i+1) < w->Width )
            {
                Vec_IntWriteEntry(w->vTerms, kept++, Vec_IntEntry(w->vTerms, i));
                Vec_IntWriteEntry(w->vTerms, kept++, Vec_IntEntry(w->vTerms, i+1));
            }
        Vec_IntShrink(w->vTerms, kept); kept = 0;
        Vec_IntForEachEntry(w->vConstants, lit, i)
            if ( lit < w->Width ) Vec_IntWriteEntry(w->vConstants, kept++, lit);
        Vec_IntShrink(w->vConstants, kept);
    }
    Vec_IntFreeP(&vBest);
    Vec_IntFreeP(&vBits); Vec_WrdFreeP(&vValues); Vec_WrdFreeP(&vExpected);
    if ( model ) Gia_ManStop(model);
    if ( extracted ) Gia_ManStop(extracted);
    Acec2_WordSimStop(s); Hsh_Int1ManStop(h);
    return result;
}

/**Function*************************************************************

  Synopsis    [Certifies a proposed linear word over an independent source cut.]

  Description [A proposal can extend an earlier arithmetic prefix, but its
  retained bits all require a new exact proof. The caller owns the proposal
  and supplies explicit sign extension through its weighted literals.]

  SideEffects [Stores only proved bits and may narrow the word.]

  SeeAlso     []

***********************************************************************/
int Acec2_CertifyLinearWord( Acec2_Man_t * m, Acec2_Word_t * w, int Minimum )
{
    Vec_Int_t * map; int i, lit, result;
    if ( !w || w->Tree != -1 || w->Record != -1 || !w->fIndependent || w->fPolynomial ||
         w->pProduct || w->vBits || w->Width < Minimum || Minimum < 1 || w->Width > m->Pars.nMaxWidth ||
         w->Width > 512 || (Vec_IntSize(w->vTerms) & 1) || Acec2_Stopped(m) ) return 0;
    for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 )
    {
        lit = Vec_IntEntry(w->vTerms, i);
        if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ||
             Vec_IntEntry(w->vTerms, i+1) < 0 || Vec_IntEntry(w->vTerms, i+1) >= w->Width ) return 0;
    }
    Vec_IntForEachEntry(w->vConstants, lit, i) if ( lit < 0 || lit >= w->Width ) return 0;
    map = Vec_IntStart(Gia_ManObjNum(m->pGia));
    for ( i = 0; i < Vec_IntSize(map); i++ ) Vec_IntWriteEntry(map, i, 2*i);
    m->nWordConflictStart = m->nWordConflicts; m->nWordAttempts++;
    result = Acec2_WordDiscover(m, w, map, Minimum);
    Vec_IntFree(map); return result;
}

/**Function*************************************************************

  Synopsis    [Closes bounded carry-save regions through their final adders.]

  Description [Records are independent of any second design. Region order,
  traversal counts, word width and SAT conflicts bound this optional recovery;
  an unresolved region retains its original checked cell boundaries.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_CloseWords( Acec2_Man_t * m )
{
    Vec_Wrd_t * vOrder = Vec_WrdAlloc(Vec_WecSize(m->vTrees));
    Vec_Int_t * v, * vMap = NULL;
    Acec2_Word_t * w;
    word key;
    int i, tree, width;
    Vec_IntFill(m->vTreeWord, Vec_WecSize(m->vTrees), -1);
    Vec_WecForEachLevel(m->vTrees, v, tree)
    {
        width = Vec_IntEntry(m->vWidths, tree);
        if ( Vec_IntEntry(m->vNormal, tree) || Vec_IntSize(v) < 4 || width < 4 || width > 512 ||
             Abc_MinInt(width, m->Pars.nMaxWidth) <= Vec_IntEntry(m->vPrefix, tree) ) continue;
        Vec_WrdPush(vOrder, ((word)(unsigned)Vec_IntSize(v) << 32) | (0xFFFFFFFFu-(unsigned)tree));
    }
    if ( Vec_WrdSize(vOrder) > 1 ) Vec_WrdSort(vOrder, 1);
    Vec_WrdForEachEntry(vOrder, key, i)
    {
        if ( Acec2_Stopped(m) ) break;
        tree = (int)(0xFFFFFFFFu-(unsigned)key); w = Acec2_WordBoundary(m, tree);
        if ( w->nRolled && Vec_IntSize(w->vTerms) <= 2048 )
        {
            if ( !vMap )
            {
                int id;
                vMap = Vec_IntStart(Gia_ManObjNum(m->pGia));
                for ( id = 0; id < Vec_IntSize(vMap); id++ ) Vec_IntWriteEntry(vMap, id, 2*id);
            }
            m->nWordAttempts++; m->nWordConflictStart = m->nWordConflicts;
            if ( Acec2_WordDiscover(m, w, vMap, Abc_MaxInt(4, Vec_IntEntry(m->vPrefix, tree)+1)) )
            {
                Vec_IntWriteEntry(m->vTreeWord, tree, Vec_PtrSize(m->vWords)); Vec_PtrPush(m->vWords, w);
                Acec2_RecordTreeWord(m, tree); continue;
            }
        }
        Vec_IntFree(w->vTerms); Vec_IntFree(w->vConstants); ABC_FREE(w);
    }
    Vec_IntFreeP(&vMap); Vec_WrdFree(vOrder);
}

/**Function*************************************************************

  Synopsis    [Moves a weighted boundary before terminal propagate/generate pairs.]

  Description [Retained half-adder alternatives can expose the two inputs
  of a final parallel adder even when they were not chosen by the main cover.
  Checked nonlocal carry stages are also moved out of the boundary. Only
  complete output pairs are replaced. A decreasing maximum gate ID ensures
  progress; the common checker replays the
  recorded identities before accepting any completed word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WordRollback( Acec2_Man_t * m, Acec2_Word_t * w )
{
    Vec_Wrd_t * order = Vec_WrdAlloc(100);
    Vec_Ptr_t * cells;
    Acec2_Cell_t * c;
    word key;
    int kind, id, i, j, k, phase, rank, carry, latest, rolled = 0;
    for ( kind = 0; kind < 2; kind++ )
    {
        cells = kind ? m->vAlternatives : m->vCells;
        Vec_PtrForEachEntry(Acec2_Cell_t *, cells, c, id)
        {
            if ( c->nIns != 2 && !c->Proof ) continue;
            latest = Abc_MaxInt(c->Out[0], c->Out[1]) >> 1;
            for ( k = 0; k < c->nIns; k++ ) if ( (c->In[k] >> 1) >= latest ) break;
            if ( k < c->nIns ) continue;
            Vec_WrdPush(order, ((word)(unsigned)latest << 32) | (unsigned)(2*id+kind));
        }
    }
    Vec_WrdSort(order, 1); w->vRollback = Vec_IntAlloc(16);
    Vec_WrdForEachEntry(order, key, i)
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) break;
        if ( Vec_IntSize(w->vTerms) > 4096 ) { m->nWordLimits++; break; }
        id = (int)((unsigned)key >> 1); kind = (unsigned)key & 1;
        c = (Acec2_Cell_t *)Vec_PtrEntry(kind ? m->vAlternatives : m->vCells, id);
        for ( j = 0; j < Vec_IntSize(w->vTerms); j += 2 )
        {
            phase = Vec_IntEntry(w->vTerms, j) ^ c->Out[0]; if ( phase > 1 ) continue;
            rank = Vec_IntEntry(w->vTerms, j+1);
            carry = Acec2_WordTerm(w->vTerms, c->Out[1] ^ phase, rank+1); if ( carry < 0 ) continue;
            Vec_IntWriteEntry(w->vTerms, j, c->In[0] ^ phase);
            Vec_IntWriteEntry(w->vTerms, carry, c->In[1] ^ phase); Vec_IntWriteEntry(w->vTerms, carry+1, rank);
            if ( c->nIns == 3 ) Vec_IntPushTwo(w->vTerms, c->In[2] ^ phase, rank);
            else if ( phase ) Vec_IntPush(w->vConstants, rank);
            Vec_IntPushTwo(w->vRollback, kind, id); Vec_IntPushTwo(w->vRollback, rank, phase); rolled++;
        }
    }
    Vec_WrdFree(order); w->nRolled = rolled; return rolled;
}

/**Function*************************************************************

  Synopsis    [Closes composed counter boundaries through existing final adders.]

  Description [The weighted root boundary is tried as an independent cut.
  If its signals have hidden dependencies, the checked input boundary is
  tried instead. A polynomial reference can move the independent cut behind
  related partial products and carries. Every discovered bit requires an
  exact proof; an intermediate prefix does not suppress the remaining cuts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CloseRecordWordInt( Acec2_Man_t * m, int Record, int * pnQueries, Vec_Int_t ** pvMap )
{
    Acec2_Record_t * r, * result; Acec2_Word_t * w;
    int id, mode, minimum, added = 0, tier, offset;
    if ( !pnQueries || *pnQueries <= 0 || Record < 0 || Record >= Vec_PtrSize(m->vRecords) || Acec2_Stopped(m) ) return 0;
    r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Record);
    if ( r->vOutputMasks || (!r->vParts && r->Tree < 0) || r->Word >= 0 || r->Width < 4 || r->Width > 512 || r->Prefix == r->Width ) return 0;
    if ( Record >= ABC_INT_MAX/4-1 ) { m->nWordLimits++; return 0; }
    if ( !m->vWordProgress ) m->vWordProgress = Vec_IntAlloc(100);
    Vec_IntFillExtra(m->vWordProgress, 4*(Record+1), 0); offset = 4*Record;
    tier = m->Pars.nCecPolyLimit > 0 ? m->Pars.nCecPolyLimit : ABC_INT_MAX;
    // Escalation must not restart a partially visited boundary queue.
    if ( Vec_IntEntry(m->vWordProgress, offset) != tier &&
         (!Vec_IntEntry(m->vWordProgress, offset+1) || Vec_IntEntry(m->vWordProgress, offset+1) >= 4) )
    {
        Vec_IntWriteEntry(m->vWordProgress, offset, tier);
        Vec_IntWriteEntry(m->vWordProgress, offset+1, 0);
        Vec_IntWriteEntry(m->vWordProgress, offset+3, 0);
    }
    minimum = Abc_MaxInt(Abc_MaxInt(4, r->Prefix+1), Vec_IntEntry(m->vWordProgress, offset+2));
    if ( minimum > r->Width ) return 0;
    m->nWordConflictStart = m->nWordConflicts-Vec_IntEntry(m->vWordProgress, offset+3);
    for ( mode = Vec_IntEntry(m->vWordProgress, offset+1); mode < 4 && *pnQueries > 0 && !Acec2_Stopped(m); mode++ )
    {
        if ( mode == 3 && (!m->Pars.fAlgebra || !Vec_WecSize(r->vMonomials)) ) continue;
        if ( mode == 3 ? Vec_WecSize(r->vMonomials) > 32768 : Vec_IntSize(mode == 2 ? r->vTerms : r->vOutputs) > 2048 )
        { m->nWordLimits++; continue; }
        w = ABC_CALLOC(Acec2_Word_t, 1); w->Tree = -1; w->Record = Record; w->Width = r->Width;
        w->fPolynomial = mode == 3;
        w->vTerms = mode == 3 ? Vec_IntAlloc(0) : Vec_IntDup(mode == 2 ? r->vTerms : r->vOutputs);
        w->vConstants = mode == 2 ? Vec_IntDup(r->vConstants) : Vec_IntAlloc(0);
        if ( mode == 1 && !Acec2_WordRollback(m, w) ) { Acec2_WordFree(w); continue; }
        if ( !*pvMap )
        {
            *pvMap = Vec_IntStart(Gia_ManObjNum(m->pGia));
            for ( id = 0; id < Vec_IntSize(*pvMap); id++ ) Vec_IntWriteEntry(*pvMap, id, 2*id);
        }
        (*pnQueries)--; m->nWordAttempts++;
        if ( Acec2_WordDiscover(m, w, *pvMap, minimum) )
        {
            id = Vec_PtrSize(m->vWords); Vec_PtrPush(m->vWords, w);
            result = Acec2_RecordWord(m, id, Record);
            if ( result )
            {
                Vec_PtrPush(m->vRecords, result); minimum = w->Width+1; added++;
                if ( w->Width == r->Width ) { mode = 4; break; }
                continue;
            }
            Vec_PtrPop(m->vWords);
        }
        Acec2_WordFree(w);
        if ( Acec2_Stopped(m) ) break;
    }
    Vec_IntWriteEntry(m->vWordProgress, offset+1, mode);
    Vec_IntWriteEntry(m->vWordProgress, offset+2, minimum);
    Vec_IntWriteEntry(m->vWordProgress, offset+3, m->nWordConflicts-m->nWordConflictStart);
    return added;
}

/**Function*************************************************************

  Synopsis    [Requests bounded word closure for one persistent record.]

  Description [The same source proof is used by profiling and CEC. A
  completed prefix and the next proposal survive subsequent requests.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CloseRecordWord( Acec2_Man_t * m, int Record, int * pnQueries )
{
    Vec_Int_t * vMap = NULL;
    int added = Acec2_CloseRecordWordInt(m, Record, pnQueries, &vMap);
    Vec_IntFreeP(&vMap); return added;
}

/**Function*************************************************************

  Synopsis    [Requests word closure for every current region record.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_CloseRecordWords( Acec2_Man_t * m )
{
    Vec_Int_t * vMap = NULL;
    int i, queries, count = Vec_PtrSize(m->vRecords);
    for ( i = 0; i < count && !Acec2_Stopped(m); i++ )
    {
        queries = 4;
        Acec2_CloseRecordWordInt(m, i, &queries, &vMap);
    }
    Vec_IntFreeP(&vMap);
}

/**Function*************************************************************

  Synopsis    [Proposes linear words before related downstream boundary terms.]

  Description [Parallel carry implementations can leave their related
  intermediate signals on a region's input boundary. Keep the earliest
  independent cut and propose its weighted sum. Removing terms is only a
  discovery heuristic: SAT must prove every retained result bit over the
  free cut before an independent word or component record is stored.]

  SideEffects [Adds completed independent word certificates.]

  SeeAlso     []

***********************************************************************/
int Acec2_DiscoverLinearRegion( Acec2_Man_t * m, int Tree, int * pnQueries )
{
    Gia_Man_t * g; Gia_Obj_t * o;
    Vec_Int_t * leaves, * map, * terms;
    Vec_Bit_t * boundary, * known, * removed;
    Acec2_Word_t * w, * previous; Acec2_Record_t * record;
    int i, lit, id, dropped, minimum, word, a, b, c, width, tier, added = 0;
    if ( !m || !pnQueries || *pnQueries <= 0 || Tree < 0 || Tree >= Vec_WecSize(m->vTrees) || Acec2_Stopped(m) ) return 0;
    g = m->pGia;
    if ( Vec_IntEntry(m->vNormal, Tree) || Vec_IntSize(Vec_WecEntry(m->vTrees, Tree)) < 4 ) return 0;
    width = Abc_MinInt(Vec_IntEntry(m->vWidths, Tree), m->Pars.nMaxWidth);
    if ( width < 4 || width > 512 ) return 0;
    if ( !m->vLinearProgress ) m->vLinearProgress = Vec_IntStart(3*Vec_WecSize(m->vTrees));
    tier = m->Pars.nCecPolyLimit > 0 ? m->Pars.nCecPolyLimit : ABC_INT_MAX;
    if ( Vec_IntEntry(m->vLinearProgress, 3*Tree) == tier || Vec_IntEntry(m->vLinearProgress, 3*Tree+2) ) return 0;
    previous = Acec2_Word(m, Tree);
    minimum = Abc_MaxInt(4, Abc_MaxInt(previous ? previous->Width : Vec_IntEntry(m->vPrefix, Tree),
                                    Vec_IntEntry(m->vLinearProgress, 3*Tree+1))+1);
    if ( minimum > width ) return 0;
    leaves = Vec_WecEntry(m->vLeaves, Tree);
    if ( Vec_IntSize(leaves) < 8 || Vec_IntSize(leaves) > 2048 ) return 0;
    for ( i = 0; i < Vec_IntSize(leaves); i += 2 )
        if ( Gia_ObjIsAnd(Gia_ManObj(g, Vec_IntEntry(leaves, i) >> 1)) ) break;
    if ( i == Vec_IntSize(leaves) ) return 0;
    (*pnQueries)--;
    boundary = Vec_BitStart(Gia_ManObjNum(g)); known = Vec_BitStart(Gia_ManObjNum(g)); removed = Vec_BitStart(Gia_ManObjNum(g));
    for ( i = 0; i < Vec_IntSize(leaves); i += 2 ) Acec2_BitWrite(boundary, Vec_IntEntry(leaves, i) >> 1, 1);
    Acec2_BitWrite(known, 0, 1); dropped = 0;
    Gia_ManForEachObj1(g, o, id)
    {
        if ( (id & 1023) == 0 && Acec2_Stopped(m) ) break;
        if ( Gia_ObjIsCo(o) ) continue;
        if ( Gia_ObjIsAnd(o) )
        {
            a = Vec_BitEntry(known, Gia_ObjFaninId0(o, id)); b = Vec_BitEntry(known, Gia_ObjFaninId1(o, id));
            c = !Gia_ObjIsMux(g, o) || Vec_BitEntry(known, Gia_ObjFaninId2(g, id));
            if ( a && b && c ) Acec2_BitWrite(known, id, 1);
        }
        if ( !Vec_BitEntry(boundary, id) ) continue;
        if ( Vec_BitEntry(known, id) ) { Acec2_BitWrite(removed, id, 1); dropped++; }
        else Acec2_BitWrite(known, id, 1);
    }
    terms = Vec_IntAlloc(Vec_IntSize(leaves));
    for ( i = 0; i < Vec_IntSize(leaves); i += 2 )
    {
        lit = Vec_IntEntry(leaves, i);
        if ( !Vec_BitEntry(removed, lit >> 1) ) Vec_IntPushTwo(terms, lit, Vec_IntEntry(leaves, i+1));
    }
    Vec_BitFree(boundary); Vec_BitFree(known); Vec_BitFree(removed);
    if ( Acec2_Stopped(m) ) { Vec_IntFree(terms); return 0; }
    if ( !dropped || Vec_IntSize(terms) < 8 )
    { Vec_IntWriteEntry(m->vLinearProgress, 3*Tree+2, 1); Vec_IntFree(terms); return 0; }
    w = ABC_CALLOC(Acec2_Word_t, 1); w->Tree = w->Record = -1;
    w->Width = width; w->vTerms = terms; w->vConstants = Vec_IntAlloc(0);
    map = Vec_IntStart(Gia_ManObjNum(g));
    for ( i = 0; i < Vec_IntSize(map); i++ ) Vec_IntWriteEntry(map, i, 2*i);
    m->nWordAttempts++; m->nWordConflictStart = m->nWordConflicts;
    if ( Acec2_WordDiscover(m, w, map, minimum) )
    {
        w->fIndependent = 1; word = Vec_PtrSize(m->vWords); Vec_PtrPush(m->vWords, w);
        record = Acec2_RecordWord(m, word, -1);
        if ( record )
        {
            record->Discovery = Tree+1; Vec_PtrPush(m->vRecords, record); added = 1;
            Vec_IntWriteEntry(m->vLinearProgress, 3*Tree+1, w->Width);
            if ( m->Pars.fVerbose ) Abc_Print(1, "Independent linear word: width = %d, source region = %d, removed dependent terms = %d.\n", w->Width, Tree, dropped);
        }
        else Vec_PtrPop(m->vWords);
    }
    if ( !Acec2_Stopped(m) ) Vec_IntWriteEntry(m->vLinearProgress, 3*Tree, tier);
    if ( !added ) Acec2_WordFree(w);
    Vec_IntFree(map); return added;
}

/**Function*************************************************************

  Synopsis    [Requests bounded independent linear words for standalone profiling.]

  Description [The same per-region action is available to CEC on demand.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_DiscoverLinearWords( Acec2_Man_t * m )
{
    int tree, queries = 32;
    for ( tree = 0; tree < Vec_WecSize(m->vTrees) && queries > 0 && !Acec2_Stopped(m); tree++ )
        Acec2_DiscoverLinearRegion(m, tree, &queries);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
