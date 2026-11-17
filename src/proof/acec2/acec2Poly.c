/**CFile****************************************************************

  FileName    [acec2Poly.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Bounded, exact weighted polynomial extraction.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id$]

  Description [Backward substitution, as in acecPolyn.c, with checked
  adder cuts, SAT-proved carry recurrences, and coefficients modulo 2^W.
  All W ordered output bits form one word. Equality of these words proves
  every output pair, without relying on port names or multiplier hints.]

***********************************************************************/

#include "acec2Int.h"
#include "misc/vec/vecHsh.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef struct Acec2_Rule_t_ Acec2_Rule_t;
struct Acec2_Rule_t_
{
    int n, In[6], Type;       // uncomplemented node as a function of uncomplemented inputs
    word Truth;
    int Sum, Phase;           // optional checked linear carry identity
    int Counter, CounterOut;  // optional general integer counter, index plus one
    int Region, RegionOut;    // optional checked integer region, index plus one
};
struct Acec2_CarryCtx_t_
{
    Acec2_Man_t * pMan;
    Acec2_Rule_t * pRules;       // borrowed for a full pass, owned by an on-demand analysis
    Vec_Wrd_t * vSim;
    Vec_Int_t * vHead, * vNext, * vStack, * vVars, * vRecovered;
    Vec_Bit_t * vLoaded, * vFeeds;
    sat_solver * pSat;
    Hsh_VecMan_t * hTried;       // completed truth queries or deterministic conflict limits
    int fDetect, Pass, iCut, Phase, Node, nProbes, nProved, fDone, iImported;
    int fOwnRules;
};
typedef struct Acec2_Poly_t_ Acec2_Poly_t;
struct Acec2_Poly_t_
{
    Acec2_Man_t * pMan;
    Hsh_VecMan_t * pHash;
    Vec_Wrd_t * vCoefs;
    Vec_Int_t * vHeads, * vNext, * vMono, * vBase, * vDeps;
    Vec_Wec_t * vZeros;        // checked phased HA-output pairs by larger variable
    Vec_Wec_t * vOccurs;       // optional incidence lists for dynamic substitution
    Vec_Int_t * vUndo, * vTrialSeen;
    Vec_Wrd_t * vUndoCoefs;
    word * pCoef;
    int fTrial, nTrial, fTrialOrder, nTrialLimit, fBorrowZeros;
    int nWords, nWidth, nUsed, nPeak, nLimit, fFailed, fEffortLimit, iLastVar, nReduceDepth;
    ABC_INT64_T nSteps, nWork, nWorkLimit, nZeroProducts, nCounterRules, nRegionRules;
};
typedef struct Acec2_PolyMemo_t_ Acec2_PolyMemo_t;
struct Acec2_PolyMemo_t_
{
    Vec_Int_t * vRoots, * vDeps, * vConst;
    Vec_Wec_t * vCols;
    int Width, Flip, Result, Limit, nSize;
};
struct Acec2_PolyCtx_t_
{
    Acec2_Man_t * pMan;
    Acec2_Rule_t * pRules;
    Vec_Int_t * vMap, * vAbs, * vOrder;
    Vec_Ptr_t * vMemos;
    Vec_Wec_t * vZeros;         // owned rules shared by local queries on this cut
    Gia_Man_t * pDestination;
    int nVars, nShared, nLimit, nMemoSize, nCacheHits, nCacheLimits;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks the overall and local algebraic resource budgets.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyStop( Acec2_Man_t * p, abctime Deadline )
{
    return Acec2_Stopped(p) || (Deadline && Abc_Clock() >= Deadline);
}

/**Function*************************************************************

  Synopsis    [Initializes exact local truth functions, including native gates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Rule_t * Acec2_PolyRulesInt( Acec2_Man_t * p, Vec_Int_t * cover )
{
    Gia_Man_t * g = p->pGia; Gia_Obj_t * o;
    Acec2_Rule_t * r = ABC_CALLOC(Acec2_Rule_t, Gia_ManObjNum(g)), * q;
    Acec2_Cell_t * c;
    int i, j, k, a, b, ctrl, n, value, lit;
    Gia_ManForEachAnd(g, o, i)
    {
        q = r+i; q->n = Gia_ObjIsMux(g, o) ? 3 : 2;
        q->In[0] = Gia_ObjFaninId0(o, i); q->In[1] = Gia_ObjFaninId1(o, i);
        if ( q->n == 3 ) q->In[2] = Gia_ObjFaninId2(g, i);
        for ( k = 0; k < (1 << q->n); k++ )
        {
            a = (k & 1) ^ Gia_ObjFaninC0(o); b = ((k >> 1) & 1) ^ Gia_ObjFaninC1(o);
            ctrl = q->n == 3 ? ((k >> 2) & 1) ^ Gia_ObjFaninC2(g, o) : 0;
            value = q->n == 3 ? (ctrl ? b : a) : Gia_ObjIsXor(o) ? a ^ b : a & b;
            q->Truth |= value << k;
        }
    }
    for ( i = 0; i < Vec_IntSize(p->vXors); i += 5 )
    {
        lit = Vec_IntEntry(p->vXors, i+4); n = Vec_IntEntry(p->vXors, i);
        q = r+Abc_Lit2Var(lit);
        if ( q->Type && q->n <= n ) continue;
        q->n = n; q->Type = 1; q->Truth = 0;
        for ( j = 0; j < n; j++ ) q->In[j] = Vec_IntEntry(p->vXors, i+1+j);
        for ( k = 0; k < (1 << n); k++ )
        {
            value = (k & 1) ^ ((k >> 1) & 1) ^ (k >> 2) ^ Abc_LitIsCompl(lit);
            q->Truth |= value << k;
        }
    }
    for ( i = 0; i < (cover ? Vec_IntSize(cover)/2 : Vec_PtrSize(p->vCells)); i++ )
    {
        c = cover ? (Acec2_Cell_t *)Vec_PtrEntry(Vec_IntEntry(cover, 2*i) ? p->vAlternatives : p->vCells,
                                               Vec_IntEntry(cover, 2*i+1)) : Acec2_Cell(p, i);
        for ( j = 0; j < 2; j++ )
        {
            // Source-constrained identities can refer to later gate nodes.
            // Retain them in the detector, but keep a forward Boolean rule
            // here so an optional identity cannot make every proof cyclic.
            for ( k = 0; k < c->nIns; k++ )
                if ( (c->In[k] >> 1) >= (c->Out[j] >> 1) ) break;
            if ( k < c->nIns ) continue;
            q = r+Abc_Lit2Var(c->Out[j]); q->n = c->nIns; q->Type = 2; q->Truth = 0;
            for ( k = 0; k < q->n; k++ ) q->In[k] = Abc_Lit2Var(c->In[k]);
            for ( k = 0; k < (1 << q->n); k++ )
            {
                value = ((k & 1) ^ (c->In[0] & 1)) + (((k >> 1) & 1) ^ (c->In[1] & 1));
                if ( q->n == 3 ) value += (k >> 2) ^ (c->In[2] & 1);
                value = ((value >> j) & 1) ^ Abc_LitIsCompl(c->Out[j]);
                q->Truth |= value << k;
            }
        }
    }
    if ( p->vExtraRules && Vec_IntSize(p->vExtraRules) )
    {
        Vec_Int_t * vTruth = Vec_IntStartFull(Gia_ManObjNum(g));
        Vec_Int_t * vStack = Vec_IntAlloc(100), * vTouched = Vec_IntAlloc(100);
        Vec_IntWriteEntry(vTruth, 0, 0);
        for ( i = 0; i+6 <= Vec_IntSize(p->vExtraRules); i += 6 )
        {
            if ( Acec2_Stopped(p) ) break;
            if ( !Acec2_CheckCut(p, Vec_IntEntryP(p->vExtraRules, i), vTruth, vStack, vTouched) ) continue;
            q = r+Vec_IntEntry(p->vExtraRules, i+4); q->n = Vec_IntEntry(p->vExtraRules, i);
            for ( j = 0; j < q->n; j++ ) q->In[j] = Vec_IntEntry(p->vExtraRules, i+1+j);
            q->Truth = Vec_IntEntry(p->vExtraRules, i+5); q->Type = 4;
        }
        Vec_IntFree(vTruth); Vec_IntFree(vStack); Vec_IntFree(vTouched);
    }
    return r;
}

/**Function*************************************************************

  Synopsis    [Uses the primary selected cells for the existing proof passes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Rule_t * Acec2_PolyRules( Acec2_Man_t * p )
{
    return Acec2_PolyRulesInt(p, NULL);
}

/**Function*************************************************************

  Synopsis    [Shares exactly equal parity expressions before substitution.]

  Description [Different truncated or signed products can share their low
  sums while exposing different XOR decompositions. Expanding these sums
  independently can create large polynomials before their terms cancel.
  Flatten only truth-table-checked parity rules, cancel repeated variables,
  and alias identical supports with their exact phases. Representatives
  precede their users. Bounded supports and storage leave other rules intact.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyParityRules( Acec2_Man_t * m, Acec2_Rule_t * r, abctime Deadline )
{
    Gia_Man_t * g = m->pGia;
    Vec_Wec_t * vKeys = Vec_WecStart(Gia_ManObjNum(g));
    Vec_Int_t * vPhase = Vec_IntStartFull(Gia_ManObjNum(g)), * vReps = Vec_IntAlloc(100), * vKey;
    Hsh_VecMan_t * h = Hsh_VecManStart(1000);
    Gia_Obj_t * o;
    int i, j, k, n, id, phase, parity, lit, match, nAliases = 0, nStored = 0;
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 255) == 0 && Acec2_PolyStop(m, Deadline) ) break;
        n = r[i].n;
        if ( n < 2 || n > 3 ) continue;
        phase = r[i].Truth & 1;
        for ( k = 0; k < (1 << n); k++ )
        {
            parity = phase;
            for ( j = 0; j < n; j++ ) parity ^= (k >> j) & 1;
            if ( parity != ((r[i].Truth >> k) & 1) ) break;
        }
        if ( k != (1 << n) ) continue;
        for ( j = 0; j < n; j++ ) if ( r[i].In[j] < 0 || r[i].In[j] >= i ) break;
        if ( j != n ) continue;
        vKey = Vec_WecEntry(vKeys, i);
        for ( j = 0; j < n; j++ )
        {
            id = r[i].In[j];
            if ( Vec_IntEntry(vPhase, id) >= 0 )
            { phase ^= Vec_IntEntry(vPhase, id); Vec_IntAppend(vKey, Vec_WecEntry(vKeys, id)); }
            else if ( id ) Vec_IntPush(vKey, id);
        }
        Vec_IntSort(vKey, 0); n = 0;
        for ( j = 0; j < Vec_IntSize(vKey); j = k )
        {
            for ( k = j+1; k < Vec_IntSize(vKey) && Vec_IntEntry(vKey, k) == Vec_IntEntry(vKey, j); k++ ) {}
            if ( (k-j) & 1 ) Vec_IntWriteEntry(vKey, n++, Vec_IntEntry(vKey, j));
        }
        Vec_IntShrink(vKey, n);
        if ( n > 64 ) { Vec_IntErase(vKey); continue; }
        if ( nStored > 1000000-Vec_IntCap(vKey) ) break;
        nStored += Vec_IntCap(vKey); Vec_IntWriteEntry(vPhase, i, phase);
        if ( n < 2 ) lit = (n ? 2*Vec_IntEntry(vKey, 0) : 0) ^ phase;
        else
        {
            match = Hsh_VecManAdd(h, vKey);
            if ( match == Vec_IntSize(vReps) ) { Vec_IntPush(vReps, (2*i) ^ phase); continue; }
            lit = Vec_IntEntry(vReps, match) ^ phase;
        }
        r[i].n = lit < 2 ? 0 : 1; r[i].In[0] = lit >> 1;
        r[i].Truth = lit < 2 ? lit : (lit & 1) ? 1 : 2;
        r[i].Type = 5; r[i].Sum = r[i].Phase = 0; nAliases++;
    }
    Hsh_VecManStop(h); Vec_WecFree(vKeys); Vec_IntFree(vPhase); Vec_IntFree(vReps);
    return nAliases;
}

/**Function*************************************************************

  Synopsis    [Enables linear carry elimination in a complete word proof.]

  Description [When its coefficient is even, replace a carry using the exact
  identity 2*carry = inputs - sum. The effective order includes the sum, so
  this substitution cannot reintroduce an already eliminated variable.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyLinearRules( Acec2_Man_t * p, Acec2_Rule_t * r )
{
    Acec2_Cell_t * c;
    Acec2_Rule_t * q;
    int i, k;
    for ( i = 0; i < Vec_PtrSize(p->vCells); i++ )
    {
        c = Acec2_Cell(p, i); q = r+Abc_Lit2Var(c->Out[1]);
        if ( q->Type == 4 || q->Type == 5 ) continue;
        if ( q->n != c->nIns ) continue;
        for ( k = 0; k < q->n; k++ ) if ( q->In[k] != (c->In[k] >> 1) ) break;
        if ( k < q->n ) continue;
        q->Sum = c->Out[0]; q->Phase = (c->Out[1] & 1) << 3;
        for ( k = 0; k < q->n; k++ ) q->Phase |= (c->In[k] & 1) << k;
    }
}

/**Function*************************************************************

  Synopsis    [Adds exact counter rewrites for otherwise missing carries.]

  Description [The highest-weight output uses an integer identity. Other
  outputs use their complete cut truth tables, so the linear rewrite cannot
  introduce a cycle through their gate implementations. Outputs have unique
  ownership within this optional rewrite set. Modular-only counters are not lifted.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyCounterRules( Acec2_Man_t * m, Acec2_Rule_t * rules )
{
    Acec2_Part_t b; Acec2_Counter_t * c; Acec2_Rule_t * q;
    Vec_Bit_t * used = Vec_BitStart(Gia_ManObjNum(m->pGia)); word truths[4];
    int i, j, k, latest, selected, id, valid;
    Vec_PtrForEachEntry(Acec2_Counter_t *, m->vCounters, c, i)
    {
        if ( Acec2_Stopped(m) ) break;
        if ( !Acec2_GetPart(m, 2, i, &b) ) continue;
        latest = selected = -1; valid = 1;
        for ( j = 0; j < b.nIns; j++ ) latest = Abc_MaxInt(latest, b.In[2*j] >> 1);
        for ( j = 0; j < b.nOuts; j++ )
        {
            id = b.Out[2*j] >> 1;
            if ( id <= latest || Vec_BitEntry(used, id) ) { valid = 0; break; }
            if ( selected < 0 || b.Out[2*j+1] > b.Out[2*selected+1] ) selected = j;
        }
        if ( !valid || selected < 0 || !b.Out[2*selected+1] || !Acec2_CounterTruth(m, c, truths) ) continue;
        for ( j = 0; j < b.nOuts; j++ )
        {
            id = b.Out[2*j] >> 1; q = rules+id; Acec2_BitWrite(used, id, 1);
            q->Type = 6; q->Truth = truths[j]; q->n = b.nIns; q->Sum = q->Phase = q->Counter = 0;
            for ( k = 0; k < b.nIns; k++ ) q->In[k] = b.In[2*k] >> 1;
        }
        q = rules+(b.Out[2*selected] >> 1); q->Counter = i+1; q->CounterOut = selected;
    }
    Vec_BitFree(used);
}

/**Function*************************************************************

  Synopsis    [Lists all dependencies of a Boolean or arithmetic rewrite.]

  Description [Keeping both dependency sets permits the Boolean fallback
  when the current coefficient is not divisible by the output weight.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyDependencyNum( Acec2_Man_t * m, Acec2_Rule_t * r )
{
    int count = r->n+(r->Sum != 0); Acec2_Counter_t * c;
    if ( r->Counter )
    {
        c = (Acec2_Counter_t *)Vec_PtrEntry(m->vCounters, r->Counter-1);
        count += (Vec_IntSize(c->vInputs)+Vec_IntSize(c->vOutputs))/2-1;
    }
    if ( r->Region ) count += (Vec_IntSize(Vec_WecEntry(m->vLeaves, r->Region-1))+
                              Vec_IntSize(Vec_WecEntry(m->vRoots, r->Region-1)))/2-1;
    return count;
}

/**Function*************************************************************

  Synopsis    [Returns one effective dependency without a fixed cut-size bound.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyDependency( Acec2_Man_t * m, Acec2_Rule_t * r, int i )
{
    Acec2_Counter_t * c; Vec_Int_t * inputs, * outputs; int selected;
    if ( i < r->n ) return r->In[i];
    i -= r->n;
    if ( r->Sum ) { if ( !i ) return r->Sum >> 1; i--; }
    if ( r->Counter )
    {
        c = (Acec2_Counter_t *)Vec_PtrEntry(m->vCounters, r->Counter-1);
        if ( i < Vec_IntSize(c->vInputs)/2 ) return Vec_IntEntry(c->vInputs, 2*i) >> 1;
        i -= Vec_IntSize(c->vInputs)/2;
        if ( i < Vec_IntSize(c->vOutputs)/2-1 ) return Vec_IntEntry(c->vOutputs, 2*(i+(i >= r->CounterOut))) >> 1;
        i -= Vec_IntSize(c->vOutputs)/2-1;
    }
    assert(r->Region);
    inputs = Vec_WecEntry(m->vLeaves, r->Region-1); outputs = Vec_WecEntry(m->vRoots, r->Region-1); selected = r->RegionOut;
    if ( i < Vec_IntSize(inputs)/2 ) return Vec_IntEntry(inputs, 2*i) >> 1;
    i -= Vec_IntSize(inputs)/2;
    return Vec_IntEntry(outputs, 2*(i+(i >= selected))) >> 1;
}

/**Function*************************************************************

  Synopsis    [Installs checked weighted-region boundary substitutions.]

  Description [Eliminate the last boundary node in the effective rewrite
  order, after all inputs and other roots. A linear carry rule can depend on
  a sum with a larger gate ID, so gate IDs alone do not give this order.
  New dependencies preserve the existing topological order. The independent
  composition checker validates the identity at the proof modulus.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyRegionRules( Acec2_Man_t * m, Acec2_Rule_t * rules, int Width, Vec_Int_t * vOrder )
{
    Vec_Int_t * roots, * leaves, * positions = Vec_IntStart(Gia_ManObjNum(m->pGia));
    Acec2_Rule_t * r; int tree, i, selected, latest, id;
    Vec_IntForEachEntry(vOrder, id, i) Vec_IntWriteEntry(positions, id, i+1);
    Vec_WecForEachLevel(m->vRoots, roots, tree)
    {
        if ( Acec2_Stopped(m) ) break;
        if ( Vec_IntSize(Vec_WecEntry(m->vTrees, tree)) < 8 ) continue;
        selected = -1; latest = 0;
        for ( i = 0; i < Vec_IntSize(roots); i += 2 )
            if ( (id = Vec_IntEntry(positions, Vec_IntEntry(roots, i) >> 1)) > latest )
                { latest = id; selected = i/2; }
        if ( selected < 0 || Vec_IntEntry(roots, 2*selected+1) >= Width ) continue;
        for ( i = 0; i < Vec_IntSize(roots); i += 2 )
            if ( i/2 != selected && Vec_IntEntry(positions, Vec_IntEntry(roots, i) >> 1) >= latest ) break;
        if ( i < Vec_IntSize(roots) ) continue;
        leaves = Vec_WecEntry(m->vLeaves, tree);
        for ( i = 0; i < Vec_IntSize(leaves); i += 2 )
            if ( Vec_IntEntry(positions, Vec_IntEntry(leaves, i) >> 1) >= latest ) break;
        if ( i < Vec_IntSize(leaves) || !Acec2_CheckRegion(m, tree, Width) ) continue;
        r = rules+(Vec_IntEntry(roots, 2*selected) >> 1); r->Region = tree+1; r->RegionOut = selected;
    }
    Vec_IntFree(positions);
}

/**Function*************************************************************

  Synopsis    [Allocates a solver variable only for a queried source node.]

  Description [Variable zero is the fixed constant. Sparse source IDs never
  create unrelated decision variables in the incremental local solver.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolySatVar( sat_solver * sat, Vec_Int_t * vVars, int Id )
{
    int var = Vec_IntEntry(vVars, Id);
    if ( var >= 0 ) return var;
    var = sat_solver_nvars(sat); sat_solver_setnvars(sat, var+1);
    Vec_IntWriteEntry(vVars, Id, var); return var;
}

/**Function*************************************************************

  Synopsis    [Loads only queried original cones into the carry-proof solver.]

  Description [Loaded clauses are retained across candidates. Rule proposals
  never enter this CNF; every accepted recurrence is proved on original gates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyLoadCone( Acec2_Man_t * p, sat_solver * sat, int Id,
                              Vec_Bit_t * vLoaded, Vec_Int_t * vStack, Vec_Int_t * vVars, abctime Deadline )
{
    Gia_Man_t * g = p->pGia; Gia_Obj_t * o;
    int id, var, a, b, c, count = 0;
    Vec_IntClear(vStack); Vec_IntPush(vStack, Id);
    while ( Vec_IntSize(vStack) )
    {
        if ( (++count & 1023) == 0 && Acec2_PolyStop(p, Deadline) ) return 0;
        id = Vec_IntPop(vStack);
        if ( Vec_BitEntry(vLoaded, id) ) continue;
        Acec2_BitWrite(vLoaded, id, 1); o = Gia_ManObj(g, id);
        var = Acec2_PolySatVar(sat, vVars, id);
        if ( !Gia_ObjIsAnd(o) ) continue;
        Vec_IntPushTwo(vStack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
        a = Acec2_PolySatVar(sat, vVars, Gia_ObjFaninId0(o, id));
        b = Acec2_PolySatVar(sat, vVars, Gia_ObjFaninId1(o, id));
        if ( Gia_ObjIsMux(g, o) )
        {
            Vec_IntPush(vStack, Gia_ObjFaninId2(g, id));
            c = Acec2_PolySatVar(sat, vVars, Gia_ObjFaninId2(g, id));
            sat_solver_add_mux(sat, var, c, b, a, Gia_ObjFaninC2(g, o), Gia_ObjFaninC1(o), Gia_ObjFaninC0(o), 0);
        }
        else if ( Gia_ObjIsXor(o) ) sat_solver_add_xor(sat, var, a, b, Gia_ObjFaninC0(o) ^ Gia_ObjFaninC1(o));
        else sat_solver_add_and(sat, var, a, b, Gia_ObjFaninC0(o), Gia_ObjFaninC1(o), 0);
    }
    return !Acec2_PolyStop(p, Deadline);
}

/**Function*************************************************************

  Synopsis    [Caches simulation and source clauses for bounded carry recovery.]

  Description [The source graph is immutable. Proposal signatures and loaded
  clauses persist across requests; rules never enter the proof solver.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_CarryCtx_t * Acec2_CarryStart( Acec2_Man_t * p, Acec2_Rule_t * r, int fDetect )
{
    Acec2_CarryCtx_t * q = ABC_CALLOC(Acec2_CarryCtx_t, 1);
    Gia_Man_t * g = p->pGia; Gia_Obj_t * o;
    word state = ABC_CONST(0x345679ABCDEF0123), key, value;
    int i, j, slot, lit = 1, status;
    q->pMan = p; q->pRules = r; q->fDetect = fDetect; q->Node = -2;
    q->vSim = Vec_WrdStart(Gia_ManObjNum(g));
    q->vHead = Vec_IntStartFull(Abc_PrimeCudd(Gia_ManObjNum(g))); q->vNext = Vec_IntStartFull(Gia_ManObjNum(g));
    q->vLoaded = Vec_BitStart(Gia_ManObjNum(g)); q->vFeeds = Vec_BitStart(Gia_ManObjNum(g));
    q->vStack = Vec_IntAlloc(100); q->vVars = Vec_IntStartFull(Gia_ManObjNum(g)); q->vRecovered = Vec_IntAlloc(100);
    q->hTried = Hsh_VecManStart(100);
    q->hTried->vValue = Vec_IntAlloc(100);
    if ( fDetect )
    {
        for ( i = 0; i < Vec_WecSize(p->vXorLeaves); i++ )
            for ( j = 0; j < Vec_IntSize(Vec_WecEntry(p->vXorLeaves, i)); j++ )
                Acec2_BitWrite(q->vFeeds, Vec_IntEntry(Vec_WecEntry(p->vXorLeaves, i), j), 1);
        Gia_ManForEachCo(g, o, i) Acec2_BitWrite(q->vFeeds, Gia_ObjFaninId0p(g, o), 1);
    }
    Gia_ManForEachCi(g, o, i)
    { Acec2_Random(&state); Vec_WrdWriteEntry(q->vSim, Gia_ObjId(g, o), state); }
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(p) ) break;
        value = Acec2_SimGate(g, i, q->vSim, 1, 0);
        Vec_WrdWriteEntry(q->vSim, i, value);
        if ( fDetect && !Vec_IntEntry(p->vRefs, i) ) continue;
        if ( !value || !~value ) continue;
        if ( !fDetect && (r[i].Type == 2 || r[i].Type == 1 || r[i].Type == 4 || r[i].Type == 5) ) continue;
        key = (value & 1) ? ~value : value; slot = (int)(key % (unsigned)Vec_IntSize(q->vHead));
        Vec_IntWriteEntry(q->vNext, i, Vec_IntEntry(q->vHead, slot)); Vec_IntWriteEntry(q->vHead, slot, i);
    }
    q->pSat = sat_solver_new(); sat_solver_setnvars(q->pSat, 1); Vec_IntWriteEntry(q->vVars, 0, 0);
    status = sat_solver_addclause(q->pSat, &lit, &lit+1); assert(status);
    sat_solver_set_runid(q->pSat, p->Pars.RunId); sat_solver_set_stop_func(q->pSat, p->Pars.pFuncStop);
    sat_solver_set_stop_flag(q->pSat, p->Pars.pCancelled);
    return q;
}

/**Function*************************************************************

  Synopsis    [Releases a private carry search and its optional owned rules.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CarryFree( Acec2_CarryCtx_t * q )
{
    if ( !q ) return;
    sat_solver_delete(q->pSat); Hsh_VecManStop(q->hTried);
    Vec_WrdFree(q->vSim); Vec_IntFree(q->vHead); Vec_IntFree(q->vNext);
    Vec_BitFree(q->vLoaded); Vec_BitFree(q->vFeeds); Vec_IntFree(q->vStack); Vec_IntFree(q->vVars);
    Vec_IntFree(q->vRecovered); if ( q->fOwnRules ) ABC_FREE(q->pRules); ABC_FREE(q);
}

/**Function*************************************************************

  Synopsis    [Proves every violating carry row on the original source cones.]

  Description [Returns one for a complete proof, zero for a counterexample,
  and minus one for a limit. Proven rows become retained clauses.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CarryProve( Acec2_CarryCtx_t * q, int * ins, int n, int id, int truth, abctime Deadline )
{
    Acec2_Man_t * p = q->pMan; sat_solver * sat = q->pSat;
    int j, k, status, lits[4], limit;
    sat_solver_set_runtime_limit(sat, Deadline);
    sat_solver_set_runid(sat, p->Pars.RunId); sat_solver_set_stop_func(sat, p->Pars.pFuncStop);
    sat_solver_set_stop_flag(sat, p->Pars.pCancelled);
    if ( !Acec2_PolyLoadCone(p, sat, id, q->vLoaded, q->vStack, q->vVars, Deadline) ) return -1;
    for ( j = 0; j < n; j++ )
        if ( !Acec2_PolyLoadCone(p, sat, ins[j], q->vLoaded, q->vStack, q->vVars, Deadline) ) return -1;
    for ( k = 0; k < (1 << n); k++ )
    {
        if ( Acec2_PolyStop(p, Deadline) ) return -1;
        limit = q->fDetect ? Abc_MinInt(1000, p->nCarryConflictLimit-sat_solver_nconflicts(sat)) : 1000;
        if ( limit <= 0 ) return -1;
        for ( j = 0; j < n; j++ ) lits[j] = Abc_Var2Lit(Vec_IntEntry(q->vVars, ins[j]), !((k >> j) & 1));
        lits[n] = Abc_Var2Lit(Vec_IntEntry(q->vVars, id), (truth >> k) & 1);
        status = sat_solver_solve(sat, lits, lits+n+1, limit, 0, 0, 0);
        if ( status == l_True ) return 0;
        if ( status == l_Undef )
        { if ( q->fDetect && !Acec2_PolyStop(p, Deadline) ) p->nFunctionalLimits++; return -1; }
        for ( j = 0; j <= n; j++ ) lits[j] ^= 1;
        if ( !sat_solver_addclause(sat, lits, lits+n+1) )
        {
            Abc_Print(-1, "Arithmetic carry proofs contradict the original circuit.\n");
            p->fStopped = 1; return -1;
        }
    }
    return !Acec2_PolyStop(p, Deadline) ? 1 : -1;
}

/**Function*************************************************************

  Synopsis    [Resumes deterministic proposal and SAT work on source carries.]

  Description [The cursor names an exact cut, phase and signature chain.
  A work limit keeps that cursor for the next request. Only complete truth
  proofs update rules; simulated coincidences cannot create identities.]

  SideEffects [Consumes bounded steps and probes, retains completed clauses.]

  SeeAlso     []

***********************************************************************/
static int Acec2_CarryAdvance( Acec2_CarryCtx_t * q, abctime Deadline, Vec_Bit_t * vLive, int nSteps, int nProbes )
{
    Acec2_Man_t * p = q->pMan; Acec2_Rule_t * r = q->pRules;
    Vec_Int_t keyVec; int data[6];
    word a, b, c, value, key;
    int i, j, k, n, sum, ins[3], id, phase, truth, fCompl, slot, status, index, steps = 0, probes = 0;
    while ( q->Pass < (q->fDetect ? 2 : 1) && !q->fDone )
    {
        if ( (steps & 255) == 0 && Acec2_PolyStop(p, Deadline) ) break;
        if ( q->nProbes >= (q->fDetect ? p->nCarryProbeLimit : 4096) || (q->fDetect && sat_solver_nconflicts(q->pSat) >= p->nCarryConflictLimit) )
        { q->fDone = 1; if ( q->fDetect ) p->nFunctionalLimits++; break; }
        if ( steps >= nSteps || probes >= nProbes ) break;
        if ( q->iCut >= Vec_IntSize(p->vXors) ) { q->Pass++; q->iCut = q->Phase = 0; q->Node = -2; continue; }
        i = q->iCut; n = Vec_IntEntry(p->vXors, i); sum = Vec_IntEntry(p->vXors, i+4) >> 1;
        if ( q->Phase >= 4 || (n != 3 && (!q->fDetect || n != 2)) ||
             (!q->fDetect && ((r[sum].Type == 2 && r[sum].n == n) || r[sum].Type == 4 || r[sum].Type == 5)) )
        { q->iCut += 5; q->Phase = 0; q->Node = -2; steps++; continue; }
        phase = q->Phase;
        for ( j = 0; j < n; j++ ) ins[j] = Vec_IntEntry(p->vXors, i+1+j);
        a = Vec_WrdEntry(q->vSim, ins[0]); if ( phase & 1 ) a = ~a;
        b = Vec_WrdEntry(q->vSim, ins[1]); if ( phase & 2 ) b = ~b;
        c = n == 3 ? Vec_WrdEntry(q->vSim, ins[2]) : 0; value = (a & b) | (a & c) | (b & c);
        if ( q->Node == -2 )
        {
            key = (value & 1) ? ~value : value; slot = (int)(key % (unsigned)Vec_IntSize(q->vHead));
            q->Node = !value || !~value ? -1 : Vec_IntEntry(q->vHead, slot);
            steps++; continue;
        }
        if ( q->Node < 0 ) { q->Phase++; q->Node = -2; continue; }
        id = q->Node; q->Node = Vec_IntEntry(q->vNext, id); steps++;
        if ( q->fDetect && ((Vec_BitEntry(q->vFeeds, id) == 0) != q->Pass) ) continue;
        if ( vLive && !Vec_BitEntry(vLive, sum) && !Vec_BitEntry(vLive, id) ) continue;
        if ( id == sum || id == ins[0] || id == ins[1] || (n == 3 && id == ins[2]) || (!q->fDetect && r[id].Type == 3) ) continue;
        a = Vec_WrdEntry(q->vSim, id); if ( a != value && a != ~value ) continue;
        truth = 0; fCompl = a != value;
        for ( k = 0; k < (1 << n); k++ )
            truth |= (((((k & 1) ^ (phase & 1)) + (((k >> 1) & 1) ^ (phase >> 1)) + (k >> 2)) >= 2) ^ fCompl) << k;
        if ( q->fDetect && r[id].n == n && (r[id].Truth & ((1 << (1 << n))-1)) == (word)truth )
        {
            for ( j = 0; j < n; j++ ) if ( r[id].In[j] != ins[j] ) break;
            if ( j == n ) continue;
        }
        data[0] = n; data[1] = ins[0]; data[2] = ins[1]; data[3] = n == 3 ? ins[2] : -1; data[4] = id; data[5] = truth;
        keyVec.nSize = keyVec.nCap = 6; keyVec.pArray = data;
        index = Hsh_VecManAdd(q->hTried, &keyVec);
        Vec_IntFillExtra(q->hTried->vValue, index+1, 0);
        if ( Vec_IntEntry(q->hTried->vValue, index) ) continue;
        probes++; q->nProbes++;
        status = Acec2_CarryProve(q, ins, n, id, truth, Deadline);
        // Cancellation and deadlines stop this context. They are never
        // interpreted as a completed rejection that another request can use.
        if ( Acec2_PolyStop(p, Deadline) ) { q->Node = id; break; }
        Vec_IntWriteEntry(q->hTried->vValue, index, status+2);
        if ( status != 1 ) continue;
        if ( q->fDetect ) Vec_IntAppend(q->vRecovered, &keyVec);
        r[id].n = n; r[id].Truth = truth; r[id].Type = 3;
        r[id].Sum = Vec_IntEntry(p->vXors, i+4) ^ ((phase ^ (phase >> 1)) & 1);
        r[id].Phase = phase | (fCompl << 3);
        for ( j = 0; j < n; j++ ) r[id].In[j] = ins[j];
        r[sum].n = n; r[sum].Type = 1; r[sum].Sum = r[sum].Phase = 0;
        r[sum].Truth = (n == 3 ? 0x96 : 0x6) ^ ((Vec_IntEntry(p->vXors, i+4) & 1) ? 0xFF : 0);
        for ( j = 0; j < n; j++ ) r[sum].In[j] = ins[j];
        q->nProved++;
    }
    if ( q->Pass >= (q->fDetect ? 2 : 1) ) q->fDone = 1;
    return steps;
}

/**Function*************************************************************

  Synopsis    [Runs the shared carry proof engine for a complete bounded pass.]

  Description [Standalone detection and polynomial fallback use the same
  query checker as incremental source recognition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyCarries( Acec2_Man_t * p, Acec2_Rule_t * r, abctime Deadline, Vec_Int_t * vRecovered )
{
    Acec2_CarryCtx_t * q = Acec2_CarryStart(p, r, vRecovered != NULL);
    Acec2_CarryAdvance(q, Deadline, NULL, ABC_INT_MAX, ABC_INT_MAX);
    if ( vRecovered ) Vec_IntAppend(vRecovered, q->vRecovered);
    p->nPolyCarries += q->nProved; p->nPolyProbes = q->nProbes;
    Acec2_CarryFree(q);
}

/**Function*************************************************************

  Synopsis    [Promotes checked nonlocal carries into standalone detection.]

  Description [Persistent parity networks supply column boundaries and
  prioritize carry proposals. Terminal carries may feed surrounding logic.
  Every proposal passes all truth rows on the original gate cones, and the
  usual external-fanout filter rejects private XOR interiors. The proof
  records source-constrained support rather
  than claiming that the arithmetic inputs form an independent gate cut.]

  SideEffects [Appends owned candidates and exact proof records.]

  SeeAlso     []

***********************************************************************/
static void Acec2_CarryCells( Acec2_Man_t * m, Vec_Int_t * vRecovered, Vec_Ptr_t * vCandidates, int Start )
{
    Acec2_Cell_t * c; Acec2_Proof_t * proof;
    int i, j, k, sum[6], carry[6];
    for ( i = Start; i < Vec_IntSize(vRecovered) && !Acec2_Stopped(m); i += 6 )
    {
        memcpy(carry, Vec_IntEntryP(vRecovered, i), 6*sizeof(int));
        if ( carry[0] == 2 ) carry[5] = (carry[5] & 15)*17;
        for ( j = 0; j < Vec_IntSize(m->vXors); j += 5 )
        {
            if ( Vec_IntEntry(m->vXors, j) != carry[0] ) continue;
            for ( k = 0; k < carry[0]; k++ )
                if ( Vec_IntEntry(m->vXors, j+k+1) != carry[k+1] ) break;
            if ( k < carry[0] ) continue;
            memcpy(sum, carry, 4*sizeof(int));
            sum[4] = Vec_IntEntry(m->vXors, j+4) >> 1;
            sum[5] = (carry[0] == 2 ? 0x66 : 0x96) ^ ((Vec_IntEntry(m->vXors, j+4) & 1) ? 255 : 0);
            if ( sum[4] == carry[4] ) continue;
            c = Acec2_MatchCut(sum, carry);
            if ( !c ) continue;
            proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = proof->Domain = 1;
            proof->vIdentity = Vec_IntAlloc(6); Vec_IntPush(proof->vIdentity, c->nIns);
            for ( k = 0; k < 3; k++ ) Vec_IntPush(proof->vIdentity, c->In[k]);
            Vec_IntPushTwo(proof->vIdentity, c->Out[0], c->Out[1]);
            proof->vRoots = Vec_IntAlloc(5);
            for ( k = 0; k < c->nIns; k++ ) Vec_IntPushUnique(proof->vRoots, c->In[k] >> 1);
            Vec_IntPushUnique(proof->vRoots, c->Out[0] >> 1); Vec_IntPushUnique(proof->vRoots, c->Out[1] >> 1);
            Vec_PtrPush(m->vProofs, proof); c->Proof = Vec_PtrSize(m->vProofs);
            Vec_PtrPush(vCandidates, c); m->nFunctionalCells++;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Recovers all bounded source carry candidates before cover selection.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RecoverCarries( Acec2_Man_t * m, Vec_Ptr_t * vCandidates )
{
    Acec2_Rule_t * r;
    Vec_Ptr_t * vSaved = m->vCells;
    Vec_Int_t * vRecovered = Vec_IntAlloc(100);
    int oldCarries = m->nPolyCarries, oldProbes = m->nPolyProbes, first = Vec_PtrSize(vCandidates);
    m->vCells = vCandidates; r = Acec2_PolyRules(m); m->vCells = vSaved;
    Acec2_PolyCarries(m, r, m->Deadline, vRecovered);
    m->nFunctionalProbes = m->nPolyProbes;
    m->nPolyCarries = oldCarries; m->nPolyProbes = oldProbes;
    Acec2_CarryCells(m, vRecovered, vCandidates, 0);
    Acec2_PairRecovered(m, vCandidates, first);
    Vec_IntFree(vRecovered); ABC_FREE(r);
}

/**Function*************************************************************

  Synopsis    [Advances source carry recovery without changing the primary cover.]

  Description [One work unit scans at most 4096 signature steps and proves
  at most eight proposals. Per-design proposal and conflict limits scale
  with source size. Simulation, clauses, rejection keys and cursors persist.]

  SideEffects [Appends only checked, externally used alternative cells.]

  SeeAlso     []

***********************************************************************/
int Acec2_AdvanceCarries( Acec2_Man_t * m, Vec_Bit_t * vLive, int * pnWork )
{
    Acec2_CarryCtx_t * q; Acec2_Rule_t * r;
    Vec_Ptr_t * candidates, * saved;
    int added = 0, probes, work, first, i;
    if ( !m || !pnWork || *pnWork <= 0 || m->fCarryComplete || Acec2_Stopped(m) ) return 0;
    if ( !m->fFast || !Vec_IntSize(m->vXors) ) { m->fCarryComplete = 1; return 0; }
    if ( !m->pCarry )
    {
        candidates = Vec_PtrAlloc(Vec_PtrSize(m->vCells)+Vec_PtrSize(m->vAlternatives));
        Vec_PtrAppend(candidates, m->vCells); Vec_PtrAppend(candidates, m->vAlternatives);
        saved = m->vCells; m->vCells = candidates; r = Acec2_PolyRules(m); m->vCells = saved;
        Vec_PtrFree(candidates); m->pCarry = Acec2_CarryStart(m, r, 1); m->pCarry->fOwnRules = 1;
    }
    q = m->pCarry;
    while ( *pnWork > 0 && !q->fDone && !Acec2_Stopped(m) )
    {
        probes = q->nProbes; work = Acec2_CarryAdvance(q, m->Deadline, vLive, 4096, 8);
        m->nFunctionalProbes += q->nProbes-probes;
        if ( work || probes != q->nProbes ) { (*pnWork)--; m->nCarryWork++; }
        candidates = Vec_PtrAlloc(16);
        Vec_PtrAppend(candidates, m->vCells); Vec_PtrAppend(candidates, m->vAlternatives);
        first = Vec_PtrSize(candidates);
        Acec2_CarryCells(m, q->vRecovered, candidates, q->iImported); q->iImported = Vec_IntSize(q->vRecovered);
        Acec2_PairRecovered(m, candidates, first);
        for ( i = first; i < Vec_PtrSize(candidates); i++ ) Vec_PtrWriteEntry(candidates, i-first, Vec_PtrEntry(candidates, i));
        Vec_PtrShrink(candidates, Vec_PtrSize(candidates)-first);
        added += Acec2_ImportCells(m, candidates); Vec_PtrFree(candidates);
        if ( !work && probes == q->nProbes ) break;
    }
    m->fCarryComplete = q->fDone;
    return added;
}

/**Function*************************************************************

  Synopsis    [Releases an analysis instance's incremental carry proof cache.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_CarryStop( Acec2_Man_t * m )
{
    Acec2_CarryFree(m->pCarry); m->pCarry = NULL;
}

/**Function*************************************************************

  Synopsis    [Proves a complete adder relation on the original source cones.]

  Description [Every violating row for each output must be UNSAT. The cut
  signals may have dependencies in the source design; no independent-cut
  assertion is inferred from this source context.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveSourceCell( Acec2_Man_t * m, sat_solver * sat, Acec2_Cell_t * c,
                                  Vec_Bit_t * loaded, Vec_Int_t * stack, Vec_Int_t * vars )
{
    int i, k, out, count, value, lits[4], status;
    for ( i = 0; i < 5; i++ )
        if ( !Acec2_PolyLoadCone(m, sat, (i < 3 ? c->In[i] : c->Out[i-3]) >> 1, loaded, stack, vars, m->Deadline) ) return 0;
    for ( k = 0; k < 8; k++ )
    {
        count = 0;
        for ( i = 0; i < 3; i++ )
        {
            value = (k >> i) & 1; count += value ^ (c->In[i] & 1);
            lits[i] = Abc_Var2Lit(Vec_IntEntry(vars, c->In[i] >> 1), !value);
        }
        for ( out = 0; out < 2; out++ )
        {
            if ( Acec2_Stopped(m) ) return 0;
            if ( sat_solver_nconflicts(sat) >= 20000 ) { m->nParityLimits++; return 0; }
            value = ((count >> out) & 1) ^ (c->Out[out] & 1);
            lits[3] = Abc_Var2Lit(Vec_IntEntry(vars, c->Out[out] >> 1), value);
            status = sat_solver_solve(sat, lits, lits+4, Abc_MinInt(1000, 20000-sat_solver_nconflicts(sat)), 0, 0, 0);
            if ( status == l_Undef && !Acec2_Stopped(m) ) m->nParityLimits++;
            if ( status != l_False ) return 0;
        }
    }
    return !Acec2_Stopped(m);
}

/**Function*************************************************************

  Synopsis    [Recovers locally restructured parity stages with exact source proofs.]

  Description [Expand one input of an observed XOR2 into a pair of nearby
  signals. Simulation proposes the missing XOR3 and an observed carry feeding
  another parity network or an output. A completed source SAT proof validates
  both endpoints before the candidate can enter arithmetic analysis.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RecoverParityCells( Acec2_Man_t * m, Vec_Ptr_t * candidates )
{
    Gia_Man_t * g = m->pGia; Gia_Obj_t * o;
    Vec_Wrd_t * sim = Vec_WrdStart(Gia_ManObjNum(g)), * order = Vec_WrdAlloc(16);
    Vec_Bit_t * known = Vec_BitStart(Gia_ManObjNum(g)), * feeds = Vec_BitStart(Gia_ManObjNum(g)), * loaded = Vec_BitStart(Gia_ManObjNum(g));
    Vec_Bit_t * consumed = Vec_BitStart(Gia_ManObjNum(g));
    Vec_Int_t * heads = Vec_IntStartFull(Abc_PrimeCudd(Gia_ManObjNum(g))), * next = Vec_IntStartFull(Gia_ManObjNum(g));
    Vec_Int_t * priority = Vec_IntStart(Gia_ManObjNum(g)), * vars = Vec_IntStartFull(Gia_ManObjNum(g));
    Vec_Int_t * nodes = Vec_IntAlloc(32), * depths = Vec_IntAlloc(32), * stack = Vec_IntAlloc(100), * key = Vec_IntAlloc(5);
    Hsh_VecMan_t * tried = Hsh_VecManStart(100);
    Acec2_Cell_t proposal, * c; Acec2_Proof_t * proof; sat_solver * sat = NULL;
    word state = ABC_CONST(0x9A6E732B4185CD0F), a, b, ctrl, value, signature, parity;
    int i, j, k, root, other, sum, id, slot, pass, phase, ins[3], first, second, sumPhase, old, score;
    ABC_INT64_T work = 0, budget = Gia_ManAndNum(g) > 245904 ? 4000000 : 16*Gia_ManAndNum(g)+65536;
    Vec_PtrForEachEntry(Acec2_Cell_t *, m->vCells, c, i)
    {
        Acec2_BitWrite(known, c->Out[0] >> 1, 1);
        for ( k = 0; k < c->nIns; k++ )
        {
            Acec2_BitWrite(consumed, c->In[k] >> 1, 1);
            if ( Vec_IntEntry(priority, c->In[k] >> 1) < 2 ) Vec_IntWriteEntry(priority, c->In[k] >> 1, 2);
        }
        for ( k = 0; k < 2; k++ ) Vec_IntWriteEntry(priority, c->Out[k] >> 1, 4);
    }
    Vec_PtrForEachEntry(Acec2_Cell_t *, m->vAlternatives, c, i)
        Acec2_BitWrite(known, c->Out[0] >> 1, 1);
    for ( i = 0; i < Vec_WecSize(m->vXorLeaves); i++ )
        Vec_IntForEachEntry(Vec_WecEntry(m->vXorLeaves, i), id, j) Acec2_BitWrite(feeds, id, 1);
    Gia_ManForEachCo(g, o, i) Acec2_BitWrite(feeds, Gia_ObjFaninId0p(g, o), 1);
    Gia_ManForEachCi(g, o, i) Vec_WrdWriteEntry(sim, Gia_ObjId(g, o), Acec2_Random(&state));
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
        value = Acec2_SimGate(g, i, sim, 1, 0);
        Vec_WrdWriteEntry(sim, i, value);
        if ( !Vec_BitEntry(feeds, i) || !value || !~value ) continue;
        signature = (value & 1) ? ~value : value; slot = (int)(signature % (unsigned)Vec_IntSize(heads));
        Vec_IntWriteEntry(next, i, Vec_IntEntry(heads, slot)); Vec_IntWriteEntry(heads, slot, i);
    }
    for ( i = Vec_IntSize(m->vXors)-5; i >= 0; i -= 5 )
    {
        if ( Vec_IntEntry(m->vXors, i) != 2 ) continue;
        sum = Vec_IntEntry(m->vXors, i+4) >> 1; if ( Vec_BitEntry(known, sum) ) continue;
        for ( pass = 0; pass < 2; pass++ )
        {
            root = Vec_IntEntry(m->vXors, i+1+pass); other = Vec_IntEntry(m->vXors, i+2-pass);
            Vec_IntClear(nodes); Vec_IntClear(depths); Vec_IntPush(nodes, root); Vec_IntPush(depths, 0);
            for ( j = 0; j < Vec_IntSize(nodes); j++ )
            {
                o = Gia_ManObj(g, Vec_IntEntry(nodes, j));
                if ( Vec_IntEntry(depths, j) >= 3 || !Gia_ObjIsAnd(o) || Gia_ObjIsMux(g, o) ) continue;
                for ( k = 0; k < 2; k++ )
                {
                    id = k ? Gia_ObjFaninId1p(g, o) : Gia_ObjFaninId0p(g, o);
                    if ( !id || Vec_IntFind(nodes, id) >= 0 ) continue;
                    Vec_IntPush(nodes, id); Vec_IntPush(depths, Vec_IntEntry(depths, j)+1);
                }
            }
            // Prefer a recovered relation that reconnects existing columns
            // over an equally valid decomposition inside the XOR itself.
            Vec_WrdClear(order);
            for ( j = 1; j < Vec_IntSize(nodes); j++ )
            {
                id = Vec_IntEntry(nodes, j); o = Gia_ManObj(g, id); score = Vec_IntEntry(priority, id);
                if ( Gia_ObjIsAnd(o) && Gia_ObjIsCi(Gia_ObjFanin0(o)) && Gia_ObjIsCi(Gia_ObjFanin1(o)) ) score = Abc_MaxInt(score, 3);
                Vec_WrdPush(order, ((word)(unsigned)score << 32) | (unsigned)id);
            }
            Vec_WrdSort(order, 1); Vec_IntShrink(nodes, 1);
            for ( j = 0; j < Vec_WrdSize(order); j++ ) Vec_IntPush(nodes, (int)(unsigned)Vec_WrdEntry(order, j));
            for ( first = 1; first < Vec_IntSize(nodes); first++ )
            for ( second = first+1; second < Vec_IntSize(nodes); second++ )
            {
                if ( ++work > budget || m->nParityProbes >= 128 || (sat && sat_solver_nconflicts(sat) >= 20000) )
                { m->nParityLimits++; goto finish; }
                if ( (work & 1023) == 0 && Acec2_Stopped(m) ) goto finish;
                ins[0] = Vec_IntEntry(nodes, first); ins[1] = Vec_IntEntry(nodes, second); ins[2] = other;
                if ( ins[0] == other || ins[1] == other ) continue;
                parity = Vec_WrdEntry(sim, ins[0]) ^ Vec_WrdEntry(sim, ins[1]) ^ Vec_WrdEntry(sim, other);
                value = Vec_WrdEntry(sim, sum); if ( value != parity && value != ~parity ) continue;
                sumPhase = value != parity;
                for ( phase = 0; phase < 4; phase++ )
                {
                    a = Vec_WrdEntry(sim, ins[0]); if ( phase & 1 ) a = ~a;
                    b = Vec_WrdEntry(sim, ins[1]); if ( phase & 2 ) b = ~b;
                    ctrl = Vec_WrdEntry(sim, ins[2]); value = (a & b) | (a & ctrl) | (b & ctrl);
                    if ( !value || !~value ) continue;
                    signature = (value & 1) ? ~value : value; slot = (int)(signature % (unsigned)Vec_IntSize(heads));
                    for ( id = Vec_IntEntry(heads, slot); id >= 0; id = Vec_IntEntry(next, id) )
                    {
                        if ( id == sum || id <= ins[0] || id <= ins[1] || id <= ins[2] ) continue;
                        a = Vec_WrdEntry(sim, id); if ( a != value && a != ~value ) continue;
                        memset(&proposal, 0, sizeof(proposal)); proposal.nIns = 3; proposal.Tree = -1;
                        for ( k = 0; k < 3; k++ ) proposal.In[k] = 2*ins[k]^((phase >> k)&1);
                        proposal.Out[0] = 2*sum ^ sumPhase ^ ((phase ^ (phase >> 1))&1); proposal.Out[1] = 2*id ^ (a != value);
                        Vec_IntClear(key); for ( k = 0; k < 3; k++ ) Vec_IntPush(key, proposal.In[k]); Vec_IntSort(key, 0);
                        Vec_IntPushTwo(key, proposal.Out[0], proposal.Out[1]); old = Hsh_VecSize(tried);
                        if ( Hsh_VecManAdd(tried, key) < old ) continue;
                        if ( m->nParityProbes >= 128 ) { m->nParityLimits++; goto finish; }
                        m->nParityProbes++;
                        if ( !sat )
                        {
                            int constant = 1;
                            sat = sat_solver_new(); sat_solver_setnvars(sat, 1); Vec_IntWriteEntry(vars, 0, 0);
                            if ( !sat_solver_addclause(sat, &constant, &constant+1) ) goto finish;
                            sat_solver_set_runtime_limit(sat, m->Deadline); sat_solver_set_runid(sat, m->Pars.RunId);
                            sat_solver_set_stop_func(sat, m->Pars.pFuncStop); sat_solver_set_stop_flag(sat, m->Pars.pCancelled);
                        }
                        if ( !Acec2_ProveSourceCell(m, sat, &proposal, loaded, stack, vars) ) continue;
                        c = ABC_ALLOC(Acec2_Cell_t, 1); *c = proposal;
                        proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 2; proof->Domain = 1; proof->vRoots = Vec_IntAlloc(5);
                        proof->fBoundary = 1;
                        for ( k = 0; k < 3; k++ )
                        {
                            Vec_IntPush(proof->vRoots, ins[k]); o = Gia_ManObj(g, ins[k]);
                            score = Vec_IntEntry(priority, ins[k]);
                            if ( Gia_ObjIsCi(o) || (Gia_ObjIsAnd(o) && Gia_ObjIsCi(Gia_ObjFanin0(o)) && Gia_ObjIsCi(Gia_ObjFanin1(o))) ) score = Abc_MaxInt(score, 3);
                            if ( score < 3 || Vec_BitEntry(consumed, ins[k]) ) proof->fBoundary = 0;
                        }
                        Vec_IntPushTwo(proof->vRoots, sum, id);
                        Vec_PtrPush(m->vProofs, proof); c->Proof = Vec_PtrSize(m->vProofs); Vec_PtrPush(candidates, c);
                        m->nParityCells++; Acec2_BitWrite(known, sum, 1); goto next_sum;
                    }
                }
            }
        }
next_sum: ;
    }
finish:
    if ( sat ) sat_solver_delete(sat);
    Vec_WrdFree(sim); Vec_WrdFree(order); Vec_IntFree(priority); Vec_IntFree(vars); Vec_BitFree(known); Vec_BitFree(feeds); Vec_BitFree(loaded); Vec_BitFree(consumed);
    Vec_IntFree(heads); Vec_IntFree(next); Vec_IntFree(nodes); Vec_IntFree(depths); Vec_IntFree(stack); Vec_IntFree(key); Hsh_VecManStop(tried);
}

/**Function*************************************************************

  Synopsis    [Topologically orders effective rules and rejects cyclic sets.]

  Description [An explicit DFS stack avoids any recursion depth bound.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_PolyOrder( Acec2_Man_t * p, Acec2_Rule_t * r, abctime Deadline )
{
    Gia_Man_t * g = p->pGia; Gia_Obj_t * o;
    Vec_Int_t * vOrder = Vec_IntAlloc(Gia_ManObjNum(g)), * vColor = Vec_IntStart(Gia_ManObjNum(g));
    Vec_Int_t * vStack = Vec_IntAlloc(100), * vChild = Vec_IntStart(Gia_ManObjNum(g));
    int i, id, next, failed = 0, steps = 0, nDeps;
    Vec_IntWriteEntry(vColor, 0, 2);
    Gia_ManForEachCi(g, o, i)
    { id = Gia_ObjId(g, o); Vec_IntWriteEntry(vColor, id, 2); Vec_IntPush(vOrder, id); }
    Gia_ManForEachAnd(g, o, i)
    {
        if ( Vec_IntEntry(vColor, i) == 2 ) continue;
        Vec_IntPush(vStack, i);
        while ( Vec_IntSize(vStack) )
        {
            if ( (++steps & 1023) == 0 && Acec2_PolyStop(p, Deadline) ) { failed = 1; break; }
            id = Vec_IntEntryLast(vStack); Vec_IntWriteEntry(vColor, id, 1);
            nDeps = Acec2_PolyDependencyNum(p, r+id);
            if ( Vec_IntEntry(vChild, id) == nDeps )
            {
                Vec_IntPop(vStack); Vec_IntWriteEntry(vColor, id, 2); Vec_IntPush(vOrder, id); continue;
            }
            next = Acec2_PolyDependency(p, r+id, Vec_IntEntry(vChild, id)); Vec_IntAddToEntry(vChild, id, 1);
            if ( Vec_IntEntry(vColor, next) == 1 ) { failed = 1; break; }
            if ( Vec_IntEntry(vColor, next) == 0 ) Vec_IntPush(vStack, next);
        }
        if ( failed ) break;
    }
    Vec_IntFree(vColor); Vec_IntFree(vStack); Vec_IntFree(vChild);
    if ( failed ) Vec_IntFreeP(&vOrder);
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Releases private polynomial storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyFree( Acec2_Poly_t * p )
{
    if ( !p ) return;
    Hsh_VecManStop(p->pHash); Vec_WrdFree(p->vCoefs);
    Vec_IntFree(p->vHeads); Vec_IntFree(p->vNext); Vec_IntFree(p->vMono); Vec_IntFree(p->vBase);
    Vec_IntFreeP(&p->vDeps);
    if ( !p->fBorrowZeros ) Vec_WecFreeP(&p->vZeros);
    Vec_WecFreeP(&p->vOccurs);
    Vec_IntFreeP(&p->vUndo); Vec_IntFreeP(&p->vTrialSeen); Vec_WrdFreeP(&p->vUndoCoefs);
    ABC_FREE(p->pCoef); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Journals a coefficient before a reversible size trial.]

  Description [Each coefficient is saved once, including newly inserted
  monomials. Restoring zero leaves only harmless dead hash entries, which
  the ordinary compaction pass later reclaims.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyRemember( Acec2_Poly_t * p, int Id )
{
    int i;
    if ( !p->fTrial ) return;
    while ( Vec_IntSize(p->vTrialSeen) <= Id ) Vec_IntPush(p->vTrialSeen, 0);
    if ( Vec_IntEntry(p->vTrialSeen, Id) == p->nTrial ) return;
    Vec_IntWriteEntry(p->vTrialSeen, Id, p->nTrial); Vec_IntPush(p->vUndo, Id);
    for ( i = 0; i < p->nWords; i++ ) Vec_WrdPush(p->vUndoCoefs, Vec_WrdEntry(p->vCoefs, Id*p->nWords+i));
}

/**Function*************************************************************

  Synopsis    [Adds a coefficient times a square-free monomial modulo 2^W.]

  Description [Bounded storage and unsigned arithmetic also cover bit 63.
  Monomials are sorted variable sets; x*x=x for every Boolean variable.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyAdd( Acec2_Poly_t * p, Vec_Int_t * vMono, word * pCoef, int mult )
{
    int i, j, k, id, top, a, b, phase, was = 0, now = 0;
    Vec_Int_t * vPairs, * vReduced;
    word carry, old, sum, borrow;
    if ( p->fFailed ) return;
    if ( ++p->nWork > p->nWorkLimit ) { p->fFailed = p->fEffortLimit = 1; return; }
    // The two outputs of an exact HA cannot both be one. Apply this relation
    // with its recorded phases before expanding gates further. Each recursive
    // term loses at least one factor; the depth guard keeps stack use bounded.
    if ( p->vZeros && p->nReduceDepth < 64 )
        Vec_IntForEachEntry(vMono, a, i)
        {
            vPairs = Vec_WecEntry(p->vZeros, a);
            for ( j = 0; j < Vec_IntSize(vPairs); j += 2 )
            {
                b = Vec_IntEntry(vPairs, j); phase = Vec_IntEntry(vPairs, j+1);
                for ( k = 0; k < i && Vec_IntEntry(vMono, k) < b; k++ ) {}
                if ( k == i || Vec_IntEntry(vMono, k) != b ) continue;
                p->nZeroProducts++;
                if ( !phase ) return;
                vReduced = Vec_IntDup(vMono); p->nReduceDepth++;
                if ( phase != 3 )
                {
                    Vec_IntRemove(vReduced, (phase & 1) ? a : b);
                    Acec2_PolyAdd(p, vReduced, pCoef, mult);
                }
                else
                {
                    // (1-a)(1-b)=0 implies a*b=a+b-1.
                    Vec_IntRemove(vReduced, a); Acec2_PolyAdd(p, vReduced, pCoef, mult);
                    Vec_IntRemove(vReduced, b); Acec2_PolyAdd(p, vReduced, pCoef, -mult);
                    Vec_IntPushUniqueOrder(vReduced, a); Acec2_PolyAdd(p, vReduced, pCoef, mult);
                }
                p->nReduceDepth--; Vec_IntFree(vReduced); return;
            }
        }
    if ( Hsh_VecSize(p->pHash) >= 4*p->nLimit || Vec_IntSize(p->pHash->vData) > 16000000 || Vec_WrdSize(p->vCoefs) > 16000000-p->nWords ) { p->fFailed = p->fEffortLimit = 1; return; }
    id = Hsh_VecManAdd(p->pHash, vMono);
    if ( id == Vec_IntSize(p->vNext) )
    {
        top = Vec_IntSize(vMono) ? Vec_IntEntryLast(vMono) : 0;
        Vec_IntPush(p->vNext, Vec_IntEntry(p->vHeads, top)); Vec_IntWriteEntry(p->vHeads, top, id);
        for ( i = 0; i < p->nWords; i++ ) Vec_WrdPush(p->vCoefs, 0);
        if ( p->vOccurs ) Vec_IntForEachEntry(vMono, a, i) Vec_WecPush(p->vOccurs, a, id);
    }
    Acec2_PolyRemember(p, id);
    for ( i = 0; i < p->nWords; i++ ) was |= Vec_WrdEntry(p->vCoefs, id*p->nWords+i) != 0;
    for ( j = 0; j < Abc_AbsInt(mult); j++ )
    {
        carry = 0;
        for ( i = 0; i < p->nWords; i++ )
        {
            old = Vec_WrdEntry(p->vCoefs, id*p->nWords+i);
            if ( mult > 0 )
            {
                sum = old + pCoef[i]; borrow = sum < old;
                old = sum + carry; carry = borrow | (old < sum);
            }
            else
            {
                sum = old - pCoef[i]; borrow = old < pCoef[i];
                old = sum - carry; carry = borrow | (sum < carry);
            }
            if ( i == p->nWords-1 && (p->nWidth & 63) ) old &= (((word)1) << (p->nWidth & 63))-1;
            Vec_WrdWriteEntry(p->vCoefs, id*p->nWords+i, old);
        }
    }
    for ( i = 0; i < p->nWords; i++ ) now |= Vec_WrdEntry(p->vCoefs, id*p->nWords+i) != 0;
    p->nUsed += now-was; p->nPeak = Abc_MaxInt(p->nPeak, p->nUsed);
    if ( p->fTrial && p->nUsed > p->nTrialLimit ) p->fFailed = 1;
    if ( p->nUsed > p->nLimit ) p->fFailed = p->fEffortLimit = 1;
}

/**Function*************************************************************

  Synopsis    [Allocates bounded sparse polynomial storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Poly_t * Acec2_PolyAlloc( Acec2_Man_t * m, int Width, int nVars, int nLimit )
{
    Acec2_Poly_t * p = ABC_CALLOC(Acec2_Poly_t, 1);
    p->pMan = m; p->nWidth = Width; p->nWords = (Width+63)/64;
    p->nLimit = Abc_MinInt(nLimit, 16000000/p->nWords);
    p->nWorkLimit = 64*(ABC_INT64_T)p->nLimit+16*(ABC_INT64_T)nVars+1024;
    p->pHash = Hsh_VecManStart(1000); p->vCoefs = Vec_WrdAlloc(1000);
    p->vHeads = Vec_IntStartFull(nVars+1); p->vNext = Vec_IntAlloc(1000);
    p->vMono = Vec_IntAlloc(100); p->vBase = Vec_IntAlloc(100);
    p->pCoef = ABC_CALLOC(word, p->nWords);
    return p;
}

/**Function*************************************************************

  Synopsis    [Adds a weighted literal to the polynomial being extracted.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolySeedSigned( Acec2_Poly_t * p, int Var, int Compl, int Rank, int Sign )
{
    if ( Rank >= p->nWidth ) return;
    memset(p->pCoef, 0, sizeof(word)*p->nWords); p->pCoef[Rank >> 6] = ((word)1) << (Rank & 63);
    Vec_IntClear(p->vMono);
    if ( Compl ) Acec2_PolyAdd(p, p->vMono, p->pCoef, Sign);
    if ( Var )
    {
        Vec_IntPush(p->vMono, Var);
        Acec2_PolyAdd(p, p->vMono, p->pCoef, Compl ? -Sign : Sign);
    }
}
/**Function*************************************************************

  Synopsis    [Adds a literal with a positive power-of-two coefficient.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolySeed( Acec2_Poly_t * p, int Var, int Compl, int Rank )
{
    Acec2_PolySeedSigned(p, Var, Compl, Rank, 1);
}

/**Function*************************************************************

  Synopsis    [Reclaims dead monomials between variable-elimination steps.]

  Description [The live-term limit is separate from hard storage limits.
  No iterator or coefficient pointer may survive this compaction.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyCompact( Acec2_Poly_t * p )
{
    Hsh_VecMan_t * pHash = Hsh_VecManStart(Abc_MaxInt(1000, p->nUsed));
    Vec_Wrd_t * vCoefs = Vec_WrdAlloc(Abc_MaxInt(1000, p->nUsed*p->nWords));
    Vec_Int_t * vNext = Vec_IntAlloc(Abc_MaxInt(1000, p->nUsed)), * v;
    int i, j, id, top, alive;
    Vec_IntFill(p->vHeads, Vec_IntSize(p->vHeads), -1);
    if ( p->vOccurs ) Vec_WecClearLevels(p->vOccurs);
    for ( i = 0; i < Hsh_VecSize(p->pHash); i++ )
    {
        alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(p->pHash, i); id = Hsh_VecManAdd(pHash, v);
        assert(id == Vec_IntSize(vNext));
        top = Vec_IntSize(v) ? Vec_IntEntryLast(v) : 0;
        Vec_IntPush(vNext, Vec_IntEntry(p->vHeads, top)); Vec_IntWriteEntry(p->vHeads, top, id);
        for ( j = 0; j < p->nWords; j++ ) Vec_WrdPush(vCoefs, Vec_WrdEntry(p->vCoefs, i*p->nWords+j));
        if ( p->vOccurs )
            for ( j = 0; j < Vec_IntSize(v); j++ ) Vec_WecPush(p->vOccurs, Vec_IntEntry(v, j), id);
    }
    Hsh_VecManStop(p->pHash); Vec_WrdFree(p->vCoefs); Vec_IntFree(p->vNext);
    p->pHash = pHash; p->vCoefs = vCoefs; p->vNext = vNext;
}

/**Function*************************************************************

  Synopsis    [Eliminates internal variables using exact small truth tables.]

  Description [Mobius inversion supplies the multilinear coefficients.
  An optional abstraction maps selected original nodes to shared literals;
  these nodes become independent variables in both compared regions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyNext( Acec2_Poly_t * p, Acec2_Rule_t * r, Vec_Int_t * vMap, Vec_Int_t * vReady )
{
    ABC_INT64_T best = ((ABC_INT64_T)1 << 60), cost;
    Vec_Int_t * v;
    int slot = -1, i, j, k, id, term, alive, nTerms, coeff[64];
    for ( i = Vec_IntSize(vReady)-1; i >= 0 && i >= Vec_IntSize(vReady)-16; i-- )
    {
        id = Vec_IntEntry(vReady, i); cost = 0; nTerms = 0;
        for ( k = 0; k < (1 << r[id].n); k++ ) coeff[k] = (r[id].Truth >> k) & 1;
        for ( j = 0; j < r[id].n; j++ )
            for ( k = 0; k < (1 << r[id].n); k++ )
                if ( k & (1 << j) ) coeff[k] -= coeff[k ^ (1 << j)];
        for ( k = 0; k < (1 << r[id].n); k++ ) nTerms += coeff[k] != 0;
        v = Vec_WecEntry(p->vOccurs, Vec_IntEntry(vMap, id));
        Vec_IntForEachEntry(v, term, j)
        {
            if ( ++p->nWork > p->nWorkLimit ) { p->fFailed = p->fEffortLimit = 1; return -1; }
            alive = 0;
            for ( k = 0; k < p->nWords; k++ ) alive |= Vec_WrdEntry(p->vCoefs, term*p->nWords+k) != 0;
            if ( alive ) cost += r[id].Sum && !(Vec_WrdEntry(p->vCoefs, term*p->nWords) & 1) ? r[id].n : nTerms-1;
        }
        if ( slot < 0 || cost < best || (cost == best && id > Vec_IntEntry(vReady, slot)) ) { best = cost; slot = i; }
    }
    if ( slot < 0 ) return -1;
    id = Vec_IntEntry(vReady, slot);
    Vec_IntWriteEntry(vReady, slot, Vec_IntEntryLast(vReady)); Vec_IntPop(vReady);
    return id;
}

/**Function*************************************************************

  Synopsis    [Eliminates a counter output using its weighted integer identity.]

  Description [Division is used only for coefficients divisible by the
  chosen output weight. Complement corrections and all remaining weighted
  outputs are retained exactly modulo the current polynomial width.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyCounterExpand( Acec2_Poly_t * p, Acec2_Rule_t * r, Vec_Int_t * vMap )
{
    Acec2_Counter_t * c;
    Vec_Int_t * terms;
    int i, j, shift, phase, side, lit, mult, var;
    if ( !r->Counter ) return 0;
    c = (Acec2_Counter_t *)Vec_PtrEntry(p->pMan->vCounters, r->Counter-1);
    shift = Vec_IntEntry(c->vOutputs, 2*r->CounterOut+1);
    if ( p->pCoef[0] & (((word)1 << shift)-1) ) return 0;
    phase = Vec_IntEntry(c->vOutputs, 2*r->CounterOut) & 1;
    if ( phase ) Acec2_PolyAdd(p, p->vBase, p->pCoef, 1);
    for ( i = 0; i < p->nWords; i++ )
        p->pCoef[i] = (p->pCoef[i] >> shift) | (i+1 < p->nWords ? p->pCoef[i+1] << (64-shift) : 0);
    for ( side = 0; side < 2; side++ )
    {
        terms = side ? c->vOutputs : c->vInputs;
        for ( i = 0; i < Vec_IntSize(terms); i += 2 )
        {
            if ( side && i/2 == r->CounterOut ) continue;
            lit = Vec_IntEntry(terms, i); j = Vec_IntEntry(terms, i+1);
            mult = (side ^ phase ? -1 : 1)*(1 << j);
            if ( lit & 1 ) { Acec2_PolyAdd(p, p->vBase, p->pCoef, mult); mult = -mult; }
            var = Vec_IntEntry(vMap, lit >> 1); if ( !var ) continue;
            Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, p->vBase); Vec_IntPushUniqueOrder(p->vMono, var);
            Acec2_PolyAdd(p, p->vMono, p->pCoef, mult);
        }
    }
    p->nCounterRules++; return 1;
}

/**Function*************************************************************

  Synopsis    [Substitutes a checked region without expanding its interior.]

  Description [If c is divisible by the selected root weight, multiply
  the checked boundary equation by c/weight. All other roots, phases and
  constant corrections remain in the identity modulo the requested width.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyRegionExpand( Acec2_Poly_t * p, Acec2_Rule_t * r, Vec_Int_t * vMap )
{
    Vec_Int_t * roots, * terms; word * quotient;
    int i, j, side, shift, offset, bits, rank, lit, sign, phase, var, slot;
    if ( !r->Region ) return 0;
    roots = Vec_WecEntry(p->pMan->vRoots, r->Region-1);
    shift = Vec_IntEntry(roots, 2*r->RegionOut+1); offset = shift >> 6; bits = shift & 63;
    if ( shift >= p->nWidth ) return 0;
    for ( i = 0; i < offset; i++ ) if ( p->pCoef[i] ) return 0;
    if ( bits && (p->pCoef[offset] & (((word)1 << bits)-1)) ) return 0;
    phase = Vec_IntEntry(roots, 2*r->RegionOut) & 1;
    if ( phase ) Acec2_PolyAdd(p, p->vBase, p->pCoef, 1);
    quotient = ABC_CALLOC(word, p->nWords);
    for ( i = 0; i+offset < p->nWords; i++ )
    {
        quotient[i] = p->pCoef[i+offset] >> bits;
        if ( bits && i+offset+1 < p->nWords ) quotient[i] |= p->pCoef[i+offset+1] << (64-bits);
    }
    for ( side = 0; side < 3 && !p->fFailed; side++ )
    {
        terms = side == 0 ? Vec_WecEntry(p->pMan->vLeaves, r->Region-1) :
                side == 1 ? roots : Vec_WecEntry(p->pMan->vBias, r->Region-1);
        for ( i = 0; i < Vec_IntSize(terms) && !p->fFailed; i += side == 2 ? 1 : 2 )
        {
            if ( side == 1 && i/2 == r->RegionOut ) continue;
            rank = Vec_IntEntry(terms, i+(side != 2)); if ( rank >= p->nWidth ) continue;
            lit = side == 2 ? 1 : Vec_IntEntry(terms, i);
            offset = rank >> 6; bits = rank & 63;
            memset(p->pCoef, 0, sizeof(word)*p->nWords);
            for ( j = offset; j < p->nWords; j++ )
            {
                slot = j-offset; p->pCoef[j] = quotient[slot] << bits;
                if ( bits && slot ) p->pCoef[j] |= quotient[slot-1] >> (64-bits);
            }
            if ( p->nWidth & 63 ) p->pCoef[p->nWords-1] &= ((word)1 << (p->nWidth & 63))-1;
            sign = (phase ^ (side == 1)) ? -1 : 1;
            if ( lit & 1 ) { Acec2_PolyAdd(p, p->vBase, p->pCoef, sign); sign = -sign; }
            var = Vec_IntEntry(vMap, lit >> 1); if ( !var ) continue;
            Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, p->vBase); Vec_IntPushUniqueOrder(p->vMono, var);
            Acec2_PolyAdd(p, p->vMono, p->pCoef, sign);
        }
    }
    ABC_FREE(quotient); p->nRegionRules++; return 1;
}

/**Function*************************************************************

  Synopsis    [Substitutes one exact node rule throughout the live polynomial.]

  Description [The same operation is used for committed elimination and
  reversible size trials. Rewrites introduce only declared dependencies.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyRewrite( Acec2_Poly_t * p, Acec2_Rule_t * r, int id,
                               Vec_Int_t * vMap, Vec_Int_t * vAbs, abctime Deadline )
{
    Acec2_Man_t * m = p->pMan;
    Acec2_Rule_t * q, alias;
    Vec_Int_t * vEntry, * vOccurs;
    int j, k, term, coeff[64], ins[6], alive, sign, bias, var, cursor;
    q = r+id;
    if ( !p->vOccurs && Vec_IntEntry(p->vHeads, Vec_IntEntry(vMap, id)) < 0 ) return;
    p->iLastVar = id;
    if ( p->vDeps ) Vec_IntPushTwo(p->vDeps, id, Vec_IntEntry(vAbs, id));
    if ( vAbs && Vec_IntEntry(vAbs, id) >= 0 )
    {
        alias.n = 1; alias.Sum = alias.Counter = alias.Region = 0; alias.Truth = (Vec_IntEntry(vAbs, id) & 1) ? 1 : 2;
        q = &alias; ins[0] = Abc_Lit2Var(Vec_IntEntry(vAbs, id));
    }
    else for ( j = 0; j < q->n; j++ ) ins[j] = Vec_IntEntry(vMap, q->In[j]);
    for ( k = 0; k < (1 << q->n); k++ ) coeff[k] = (q->Truth >> k) & 1;
    for ( j = 0; j < q->n; j++ )
        for ( k = 0; k < (1 << q->n); k++ )
            if ( k & (1 << j) ) coeff[k] -= coeff[k ^ (1 << j)];
    vOccurs = p->vOccurs ? Vec_WecEntry(p->vOccurs, Vec_IntEntry(vMap, id)) : NULL; cursor = 0;
    for ( term = vOccurs ? (Vec_IntSize(vOccurs) ? Vec_IntEntry(vOccurs, 0) : -1) : Vec_IntEntry(p->vHeads, Vec_IntEntry(vMap, id));
          term >= 0 && !p->fFailed;
          term = vOccurs ? (++cursor < Vec_IntSize(vOccurs) ? Vec_IntEntry(vOccurs, cursor) : -1) : Vec_IntEntry(p->vNext, term) )
    {
        if ( (++p->nSteps & 1023) == 0 && Acec2_PolyStop(m, Deadline) ) { p->fFailed = 1; break; }
        if ( ++p->nWork > p->nWorkLimit ) { p->fFailed = p->fEffortLimit = 1; break; }
        alive = 0; Acec2_PolyRemember(p, term);
        for ( j = 0; j < p->nWords; j++ )
        {
            p->pCoef[j] = Vec_WrdEntry(p->vCoefs, term*p->nWords+j); alive |= p->pCoef[j] != 0;
            Vec_WrdWriteEntry(p->vCoefs, term*p->nWords+j, 0);
        }
        if ( !alive ) continue;
        p->nUsed--;
        vEntry = Hsh_VecReadEntry(p->pHash, term); Vec_IntClear(p->vBase); Vec_IntAppend(p->vBase, vEntry);
        if ( vOccurs ) Vec_IntRemove(p->vBase, Vec_IntEntry(vMap, id));
        else Vec_IntPop(p->vBase);
        if ( Acec2_PolyRegionExpand(p, q, vMap) || Acec2_PolyCounterExpand(p, q, vMap) ) continue;
        if ( q->Sum && !(p->pCoef[0] & 1) )
        {
            // For an even coefficient use 2*carry = inputs - sum.
            // This exact linear rewrite avoids expanding a majority
            // into products which only cancel after its sum is visited.
            for ( j = 0; j < p->nWords; j++ )
                p->pCoef[j] = (p->pCoef[j] >> 1) | (j+1 < p->nWords ? p->pCoef[j+1] << 63 : 0);
            sign = (q->Phase & 8) ? -1 : 1;
            bias = (q->Phase & 8) ? 2 : 0;
            for ( j = 0; j < q->n; j++ ) bias += sign*((q->Phase >> j) & 1);
            bias -= sign*Abc_LitIsCompl(q->Sum);
            if ( bias ) Acec2_PolyAdd(p, p->vBase, p->pCoef, bias);
            for ( j = 0; j <= q->n; j++ )
            {
                var = j == q->n ? Vec_IntEntry(vMap, Abc_Lit2Var(q->Sum)) : ins[j];
                if ( !var ) continue;
                Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, p->vBase); Vec_IntPushUniqueOrder(p->vMono, var);
                k = j == q->n ? (Abc_LitIsCompl(q->Sum) ? 1 : -1) : ((q->Phase >> j) & 1) ? -1 : 1;
                Acec2_PolyAdd(p, p->vMono, p->pCoef, sign*k);
            }
            continue;
        }
        for ( k = 0; k < (1 << q->n); k++ )
        {
            if ( !coeff[k] ) continue;
            Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, p->vBase);
            for ( j = 0; j < q->n; j++ )
                if ( k & (1 << j) ) { if ( !ins[j] ) break; Vec_IntPushUniqueOrder(p->vMono, ins[j]); }
            if ( j == q->n ) Acec2_PolyAdd(p, p->vMono, p->pCoef, coeff[k]);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Chooses a ready substitution by its measured polynomial size.]

  Description [Trial coefficients are always restored, including on a limit
  or cancellation. The work counter includes rejected trials. Only nodes
  whose users are eliminated are considered, preserving a terminating order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyTrialNext( Acec2_Poly_t * p, Acec2_Rule_t * r, Vec_Int_t * vMap,
                                 Vec_Int_t * vReady, abctime Deadline )
{
    int slot = -1, best = ABC_INT_MAX, i, j, k, id, used = p->nUsed, cost;
    if ( !p->vUndo )
    {
        p->vUndo = Vec_IntAlloc(100); p->vTrialSeen = Vec_IntAlloc(100);
        p->vUndoCoefs = Vec_WrdAlloc(100);
    }
    for ( i = Vec_IntSize(vReady)-1; i >= 0 && i >= Vec_IntSize(vReady)-16; i-- )
    {
        if ( Acec2_PolyStop(p->pMan, Deadline) ) { p->fFailed = 1; return -1; }
        id = Vec_IntEntry(vReady, i);
        if ( p->nTrial == ABC_INT_MAX ) { Vec_IntFill(p->vTrialSeen, Vec_IntSize(p->vTrialSeen), 0); p->nTrial = 0; }
        p->nTrial++; p->fTrial = 1; p->nTrialLimit = Abc_MinInt(p->nLimit, 2*used+64);
        Vec_IntClear(p->vUndo); Vec_WrdClear(p->vUndoCoefs);
        Acec2_PolyRewrite(p, r, id, vMap, NULL, Deadline);
        cost = p->fFailed ? ABC_INT_MAX : p->nUsed;
        Vec_IntForEachEntry(p->vUndo, j, k)
        {
            int w;
            for ( w = 0; w < p->nWords; w++ )
                Vec_WrdWriteEntry(p->vCoefs, j*p->nWords+w, Vec_WrdEntry(p->vUndoCoefs, k*p->nWords+w));
        }
        p->fTrial = p->fFailed = p->fEffortLimit = 0; p->nUsed = used;
        if ( p->nWork > p->nWorkLimit ) { p->fFailed = p->fEffortLimit = 1; return -1; }
        if ( Acec2_PolyStop(p->pMan, Deadline) ) { p->fFailed = 1; return -1; }
        if ( cost < best || (cost == best && cost < ABC_INT_MAX && id > Vec_IntEntry(vReady, slot)) )
        { best = cost; slot = i; }
    }
    if ( Hsh_VecSize(p->pHash) > p->nLimit/2 && Hsh_VecSize(p->pHash) > 2*p->nUsed ) Acec2_PolyCompact(p);
    if ( slot < 0 ) return Acec2_PolyNext(p, r, vMap, vReady);
    id = Vec_IntEntry(vReady, slot);
    Vec_IntWriteEntry(vReady, slot, Vec_IntEntryLast(vReady)); Vec_IntPop(vReady);
    return id;
}

/**Function*************************************************************

  Synopsis    [Substitutes exact rules in a fixed or size-aware order.]

  Description [Dynamic scheduling considers only nodes whose rule users
  have already been eliminated. Incidence lists let it remove a variable
  from every live monomial even when that variable is not the largest ID.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyExpand( Acec2_Poly_t * p, Acec2_Rule_t * r, Vec_Int_t * vOrder,
                              Vec_Int_t * vMap, Vec_Int_t * vAbs, abctime Deadline )
{
    Acec2_Man_t * m = p->pMan; Gia_Man_t * g = m->pGia;
    Acec2_Rule_t * q;
    Vec_Int_t * vReady = NULL, * vUsers = NULL;
    int i, j, id, var, nDeps;
    if ( p->vOccurs )
    {
        assert(!vAbs);
        vReady = Vec_IntAlloc(100); vUsers = Vec_IntStart(Gia_ManObjNum(g));
        Vec_IntForEachEntryStart(vOrder, id, i, Gia_ManCiNum(g))
        {
            nDeps = Acec2_PolyDependencyNum(m, r+id);
            for ( j = 0; j < nDeps; j++ ) Vec_IntAddToEntry(vUsers, Acec2_PolyDependency(m, r+id, j), 1);
        }
        Vec_IntForEachEntryStart(vOrder, id, i, Gia_ManCiNum(g))
            if ( !Vec_IntEntry(vUsers, id) ) Vec_IntPush(vReady, id);
    }
    for ( i = Vec_IntSize(vOrder); i > Gia_ManCiNum(g) && !p->fFailed; i-- )
    {
        if ( (i & 1023) == 0 && Acec2_PolyStop(m, Deadline) ) { p->fFailed = 1; break; }
        id = p->fTrialOrder ? Acec2_PolyTrialNext(p, r, vMap, vReady, Deadline) :
             p->vOccurs ? Acec2_PolyNext(p, r, vMap, vReady) : Vec_IntEntry(vOrder, i-1);
        if ( id < 0 ) { p->fFailed = 1; break; }
        Acec2_PolyRewrite(p, r, id, vMap, vAbs, Deadline);
        q = r+id;
        if ( !p->fFailed && Hsh_VecSize(p->pHash) > p->nLimit/2 && Hsh_VecSize(p->pHash) > 2*p->nUsed )
            Acec2_PolyCompact(p);
        if ( p->vOccurs )
        {
            nDeps = Acec2_PolyDependencyNum(m, q);
            for ( j = 0; j < nDeps; j++ )
            {
                var = Acec2_PolyDependency(m, q, j);
                Vec_IntAddToEntry(vUsers, var, -1);
                if ( var && !Gia_ObjIsCi(Gia_ManObj(g, var)) && !Vec_IntEntry(vUsers, var) ) Vec_IntPush(vReady, var);
            }
        }
    }
    Vec_IntFreeP(&vReady); Vec_IntFreeP(&vUsers);
}

/**Function*************************************************************

  Synopsis    [Proves a binary prefix against an existing weighted boundary.]

  Description [Subtracting the checked boundary first cancels shared roots
  before gate substitution. The first policies stop at the checked roots;
  subsequent policies may expand their source logic. A completed remainder
  divisible by 2^k proves the low k bits. An interrupted substitution never
  supplies a remainder. The claim holds on the source design, including
  dependencies among cut signals; no independent-cut claim is made.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyBoundaryPrefix( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * constants, Vec_Int_t * vBits )
{
    Acec2_Rule_t * rules;
    Acec2_Poly_t * p;
    Vec_Int_t * order, * map, * cut;
    int width = Vec_IntSize(vBits), pass, i, j, bit, id, lit, nCut, prefix, result = 0;
    word coefficient;
    if ( !m->Pars.fAlgebra || width < 1 || width > m->Pars.nMaxWidth || (Vec_IntSize(outputs) & 1) || Acec2_Stopped(m) ) return 0;
    for ( i = 0; i < Vec_IntSize(outputs); i += 2 )
        if ( Vec_IntEntry(outputs, i) < 0 || (Vec_IntEntry(outputs, i) >> 1) >= Gia_ManObjNum(m->pGia) ||
             Gia_ObjIsCo(Gia_ManObj(m->pGia, Vec_IntEntry(outputs, i) >> 1)) ||
             Vec_IntEntry(outputs, i+1) < 0 || Vec_IntEntry(outputs, i+1) >= m->Pars.nMaxWidth ) return 0;
    if ( constants ) Vec_IntForEachEntry(constants, bit, i) if ( bit < 0 || bit >= m->Pars.nMaxWidth ) return 0;
    Vec_IntForEachEntry(vBits, lit, i)
        if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ) return 0;
    m->nWordBoundaryAttempts++;
    for ( pass = 0; pass < 4 && !Acec2_Stopped(m); pass++ )
    {
        rules = Acec2_PolyRules(m);
        Acec2_PolyParityRules(m, rules, m->Deadline);
        if ( pass & 1 ) Acec2_PolyLinearRules(m, rules);
        order = Acec2_PolyOrder(m, rules, m->Deadline);
        if ( !order ) { ABC_FREE(rules); continue; }
        if ( pass & 1 ) Acec2_PolyRegionRules(m, rules, width, order);
        nCut = 0; cut = NULL;
        if ( pass < 2 )
        {
            cut = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
            for ( i = 0; i < Vec_IntSize(outputs); i += 2 )
            {
                id = Vec_IntEntry(outputs, i) >> 1;
                if ( Vec_IntEntry(outputs, i+1) >= width || !Gia_ObjIsAnd(Gia_ManObj(m->pGia, id)) || Vec_IntEntry(cut, id) >= 0 ) continue;
                Vec_IntWriteEntry(cut, id, 2*(++nCut));
            }
        }
        if ( (ABC_INT64_T)Vec_IntSize(order)+nCut >= 0x3FFFFFFF )
        { Vec_IntFreeP(&cut); Vec_IntFree(order); ABC_FREE(rules); m->nWordLimits++; break; }
        map = Vec_IntStart(Gia_ManObjNum(m->pGia));
        Vec_IntForEachEntry(order, id, i) Vec_IntWriteEntry(map, id, nCut+i+1);
        p = Acec2_PolyAlloc(m, width, nCut+Vec_IntSize(order), 2048); p->nWorkLimit = 65536;
        Vec_IntForEachEntry(vBits, lit, i)
            Acec2_PolySeed(p, Vec_IntEntry(map, lit >> 1), lit & 1, i);
        for ( i = 0; i < Vec_IntSize(outputs); i += 2 )
        {
            lit = Vec_IntEntry(outputs, i);
            Acec2_PolySeedSigned(p, Vec_IntEntry(map, lit >> 1), lit & 1, Vec_IntEntry(outputs, i+1), -1);
        }
        if ( constants ) Vec_IntForEachEntry(constants, bit, i) Acec2_PolySeedSigned(p, 0, 1, bit, -1);
        Acec2_PolyExpand(p, rules, order, map, cut, m->Deadline);
        prefix = 0;
        if ( !p->fFailed && !Acec2_Stopped(m) )
        {
            prefix = width;
            for ( i = 0; i < Hsh_VecSize(p->pHash) && prefix; i++ )
                for ( j = 0; j < p->nWords && 64*j < prefix; j++ )
                {
                    coefficient = Vec_WrdEntry(p->vCoefs, i*p->nWords+j);
                    if ( !coefficient ) continue;
                    for ( bit = 0; !(coefficient & 1); bit++ ) coefficient >>= 1;
                    prefix = Abc_MinInt(prefix, 64*j+bit); break;
                }
            result = Abc_MaxInt(result, prefix);
        }
        if ( m->Pars.fVerbose && prefix != width )
            Abc_Print(1, "Word boundary pass %d: %s, checked prefix = %d/%d, terms = %d, peak = %d, work = %lld.\n",
                pass, p->fFailed ? (p->fEffortLimit ? "effort limit" : "interrupted") : "different polynomial",
                prefix, width, p->nUsed, p->nPeak, (long long)p->nWork);
        Acec2_PolyFree(p); Vec_IntFreeP(&cut); Vec_IntFree(map); Vec_IntFree(order); ABC_FREE(rules);
        if ( result == width ) break;
    }
    if ( Acec2_Stopped(m) ) return 0;
    m->nWordBoundaryProved += result == width;
    m->nWordBoundaryPrefixes += result > 0 && result < width;
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks a proposed word against a persistent weighted record.]

  Description [The original record is re-checked before its boundary is used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyWordBoundaryPrefix( Acec2_Man_t * m, Acec2_Record_t * record, Vec_Int_t * vBits )
{
    if ( record->vOutputMasks || Vec_IntSize(vBits) > record->Width || !Acec2_RecordCheck(m, record) ) return 0;
    return Acec2_PolyBoundaryPrefix(m, record->vOutputs, NULL, vBits);
}

/**Function*************************************************************

  Synopsis    [Checks a proposed linear word on its original source cones.]

  Description [Subtract the weighted reference before substitution. Source
  dependencies are preserved; success does not claim an independent cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyLinearPrefix( Acec2_Man_t * m, Acec2_Word_t * w, Vec_Int_t * vBits )
{
    if ( Vec_IntSize(vBits) > w->Width || w->fPolynomial || w->pProduct ) return 0;
    return Acec2_PolyBoundaryPrefix(m, w->vTerms, w->vConstants, vBits);
}

/**Function*************************************************************

  Synopsis    [Indexes checked pairs whose product vanishes on the source.]

  Description [The same identities support whole-word and local proofs.
  A local context retains this index across its region queries. Expanding
  two complemented factors is optional because it can increase term count.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wec_t * Acec2_PolyZeroRules( Acec2_Man_t * m, Vec_Int_t * vMap, int nVars, int fExpand )
{
    Vec_Wec_t * zeros = Vec_WecStart(nVars+1);
    Acec2_Cell_t * c;
    int i, pass, a, b, phase;
    for ( pass = 0; pass < 2; pass++ )
        Vec_PtrForEachEntry(Acec2_Cell_t *, pass ? m->vAlternatives : m->vCells, c, i)
        {
            if ( c->nIns != 2 ) continue;
            a = 2*Vec_IntEntry(vMap, c->Out[0] >> 1) ^ (c->Out[0] & 1);
            b = 2*Vec_IntEntry(vMap, c->Out[1] >> 1) ^ (c->Out[1] & 1);
            if ( a < 2 || b < 2 || (a >> 1) == (b >> 1) ) continue;
            if ( a < b ) ABC_SWAP(int, a, b);
            phase = (a & 1) | ((b & 1) << 1);
            // Expanding (1-x)(1-y)=0 can increase the term count. Reserve
            // that rule for the size-aware pass; the other phases only
            // remove terms or factors.
            if ( phase == 3 && !fExpand ) continue;
            Vec_IntPushTwo(Vec_WecEntry(zeros, a >> 1), b >> 1, phase);
        }
    for ( i = 0; i < Vec_IntSize(m->vVanish); i += 5 )
    {
        a = Vec_IntEntry(m->vVanish, i+2); b = Vec_IntEntry(m->vVanish, i+3);
        a = 2*Vec_IntEntry(vMap, a >> 1) ^ (a & 1); b = 2*Vec_IntEntry(vMap, b >> 1) ^ (b & 1);
        if ( a < 2 || b < 2 || (a >> 1) == (b >> 1) ) continue;
        if ( a < b ) ABC_SWAP(int, a, b);
        phase = (a & 1) | ((b & 1) << 1);
        if ( phase == 3 && !fExpand ) continue;
        Vec_IntPushTwo(Vec_WecEntry(zeros, a >> 1), b >> 1, phase);
    }
    return zeros;
}

/**Function*************************************************************

  Synopsis    [Extracts the ordered output word or returns no result on limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Poly_t * Acec2_PolyBuildPass( Acec2_Man_t * m, abctime Deadline, int fCarries, int fLinear, int Width, int nTermLimit )
{
    Gia_Man_t * g = m->pGia; Gia_Obj_t * o;
    Acec2_Rule_t * r;
    Acec2_Poly_t * p;
    Vec_Int_t * vOrder, * vMap, * cover;
    int i, id, lit, nAliases;
    m->nPolyStatus = -1; m->fPolyEffortLimit = 0;
    if ( Acec2_PolyStop(m, Deadline) ) return NULL;
    if ( !Width || Width > 65536 || Width > m->Pars.nMaxWidth ) return NULL;
    cover = fLinear == 6 ? Acec2_RecordCover(m) : NULL;
    r = Acec2_PolyRulesInt(m, cover); Vec_IntFreeP(&cover);
    nAliases = Acec2_PolyParityRules(m, r, Deadline);
    if ( Acec2_PolyStop(m, Deadline) ) { ABC_FREE(r); return NULL; }
    if ( nAliases && m->Pars.fVerbose ) Abc_Print(1, "Polynomial parity: exact aliases = %d.\n", nAliases);
    if ( fLinear && fLinear != 6 ) Acec2_PolyLinearRules(m, r);
    if ( fCarries ) Acec2_PolyCarries(m, r, Deadline, NULL);
    if ( fLinear == 3 )
    {
        if ( !m->nCounterCuts && !Vec_PtrSize(m->vCounters) ) Acec2_FindCounters(m);
        Acec2_RefreshCounterRecords(m);
        Acec2_PolyCounterRules(m, r);
    }
    vOrder = Acec2_PolyOrder(m, r, Deadline);
    if ( !vOrder )
    {
        if ( m->Pars.fVerbose && !Acec2_PolyStop(m, Deadline) )
            Abc_Print(1, "Polynomial pass %d/%d: cyclic rewrite dependencies.\n", fCarries, fLinear);
        ABC_FREE(r); return NULL;
    }
    if ( fLinear == 4 ) Acec2_PolyRegionRules(m, r, Width, vOrder);
    p = Acec2_PolyAlloc(m, Width, Vec_IntSize(vOrder), nTermLimit);
    if ( fLinear == 2 || fLinear == 3 || fLinear == 5 ) p->vOccurs = Vec_WecStart(Vec_IntSize(vOrder)+1);
    p->fTrialOrder = fLinear == 5;
    if ( p->fTrialOrder && p->nWorkLimit > 2000000 ) p->nWorkLimit = 2000000;
    vMap = Vec_IntStart(Gia_ManObjNum(g));
    Vec_IntForEachEntry(vOrder, id, i) Vec_IntWriteEntry(vMap, id, i+1);
    p->vZeros = Acec2_PolyZeroRules(m, vMap, Vec_IntSize(vOrder), fLinear >= 2);
    Gia_ManForEachCo(g, o, i)
    {
        if ( i == Width ) break;
        lit = Gia_ObjFaninLit0p(g, o);
        Acec2_PolySeed(p, Vec_IntEntry(vMap, Abc_Lit2Var(lit)), Abc_LitIsCompl(lit), i);
    }
    Acec2_PolyExpand(p, r, vOrder, vMap, NULL, Deadline);
    m->nPolyTerms = p->nUsed; m->nPolyPeak = p->nPeak;
    m->nPolyStatus = p->fFailed ? -1 : 1;
    m->fPolyEffortLimit = p->fEffortLimit;
    if ( m->Pars.fVerbose && p->nZeroProducts )
        Abc_Print(1, "Polynomial reductions: checked vanishing products = %lld, work = %lld.\n", (long long)p->nZeroProducts, (long long)p->nWork);
    if ( m->Pars.fVerbose && p->nCounterRules ) Abc_Print(1, "Polynomial reductions: checked counter rewrites = %lld.\n", (long long)p->nCounterRules);
    if ( m->Pars.fVerbose && p->nRegionRules ) Abc_Print(1, "Polynomial reductions: checked region rewrites = %lld.\n", (long long)p->nRegionRules);
    if ( m->Pars.fVerbose && p->fFailed )
        Abc_Print(1, "Polynomial pass %d/%d: %s, live terms = %d, last node = %d, work = %lld.\n",
            fCarries, fLinear, p->fEffortLimit ? "effort limit" : "interrupted", p->nUsed, p->iLastVar, (long long)p->nWork);
    Vec_IntFree(vMap); Vec_IntFree(vOrder); ABC_FREE(r);
    if ( p->fFailed ) { Acec2_PolyFree(p); return NULL; }
    return p;
}

/**Function*************************************************************

  Synopsis    [Reduces a proposed weighted source equality directly to zero.]

  Description [The two boundaries enter one polynomial before substitution.
  Explicit product terms require no physical source node. Only a completed
  zero remainder proves the identity; nonzero and limited remainders leave
  the obligation to other checkers. No functional discovery runs here.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyWeightedInt( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms,
                        Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width, int fQuick )
{
    Acec2_Rule_t * rules; Acec2_Poly_t * p; Vec_Int_t * order, * map, * v;
    int pass, side, i, j, id, lit, rank, sign, a, b, vars[2], phases[2], choice, valid, mult, result = -1;
    if ( !m || !vOutputs || !vTerms || !vConstants || !vProducts || Width < 1 || Width > 512 || Width > m->Pars.nMaxWidth ||
         (Vec_IntSize(vOutputs) & 1) || (Vec_IntSize(vTerms) & 1) || Vec_IntSize(vProducts) % 4 || Acec2_Stopped(m) ) return -1;
    for ( side = 0; side < 3; side++ )
    {
        v = side == 2 ? vProducts : side ? vTerms : vOutputs;
        for ( i = 0; i < Vec_IntSize(v); i += side == 2 ? 4 : 2 )
        {
            rank = Vec_IntEntry(v, i+(side == 2 ? 2 : 1));
            if ( rank < 0 || rank >= Width || (side == 2 && (Vec_IntEntry(v, i+3) & ~1)) ) return -1;
            for ( j = 0; j < 1+(side == 2); j++ )
            {
                lit = Vec_IntEntry(v, i+j);
                if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ) return -1;
            }
        }
    }
    Vec_IntForEachEntry(vConstants, rank, i) if ( rank < 0 || rank >= Width ) return -1;
    for ( pass = 0; pass < (fQuick ? 1 : 3) && !Acec2_Stopped(m); pass++ )
    {
        rules = Acec2_PolyRules(m); Acec2_PolyParityRules(m, rules, m->Deadline);
        if ( pass < 2 ) Acec2_PolyLinearRules(m, rules);
        order = Acec2_PolyOrder(m, rules, m->Deadline);
        if ( !order ) { ABC_FREE(rules); continue; }
        map = Vec_IntStart(Gia_ManObjNum(m->pGia));
        Vec_IntForEachEntry(order, id, i) Vec_IntWriteEntry(map, id, i+1);
        p = Acec2_PolyAlloc(m, Width, Vec_IntSize(order), fQuick ? 2048 : 20000);
        p->nWorkLimit = fQuick ? 65536 : pass == 1 ? 2000000 : 500000;
        p->vOccurs = Vec_WecStart(Vec_IntSize(order)+1);
        p->vZeros = Acec2_PolyZeroRules(m, map, Vec_IntSize(order), 0);
        for ( side = 0; side < 2; side++ )
        {
            v = side ? vTerms : vOutputs; sign = side ? -1 : 1;
            for ( i = 0; i < Vec_IntSize(v); i += 2 )
            {
                lit = Vec_IntEntry(v, i); rank = Vec_IntEntry(v, i+1);
                Acec2_PolySeedSigned(p, Vec_IntEntry(map, lit >> 1), lit & 1, rank, sign);
            }
        }
        Vec_IntForEachEntry(vConstants, rank, i) Acec2_PolySeedSigned(p, 0, 1, rank, -1);
        for ( i = 0; i < Vec_IntSize(vProducts); i += 4 )
        {
            a = Vec_IntEntry(vProducts, i); b = Vec_IntEntry(vProducts, i+1); rank = Vec_IntEntry(vProducts, i+2);
            sign = Vec_IntEntry(vProducts, i+3) ? 1 : -1;
            if ( sign == 1 ) Acec2_PolySeedSigned(p, 0, 1, rank, -1);
            vars[0] = Vec_IntEntry(map, a >> 1); vars[1] = Vec_IntEntry(map, b >> 1); phases[0] = a & 1; phases[1] = b & 1;
            memset(p->pCoef, 0, sizeof(word)*p->nWords); p->pCoef[rank >> 6] = (word)1 << (rank & 63);
            for ( choice = 0; choice < 4; choice++ )
            {
                Vec_IntClear(p->vMono); valid = 1; mult = sign;
                for ( j = 0; j < 2; j++ )
                    if ( (choice >> j) & 1 )
                    {
                        if ( !vars[j] ) { valid = 0; break; }
                        Vec_IntPushUniqueOrder(p->vMono, vars[j]); if ( phases[j] ) mult = -mult;
                    }
                    else if ( !phases[j] ) { valid = 0; break; }
                if ( valid ) Acec2_PolyAdd(p, p->vMono, p->pCoef, mult);
            }
        }
        Acec2_PolyExpand(p, rules, order, map, NULL, m->Deadline);
        if ( !p->fFailed && !Acec2_Stopped(m) && !p->nUsed ) result = 1;
        if ( m->Pars.fVerbose ) Abc_Print(1, "Weighted polynomial: pass = %d, remainder terms = %d, peak = %d, work = %lld, result = %d.\n",
            pass, p->nUsed, p->nPeak, (long long)p->nWork, result);
        Acec2_PolyFree(p); Vec_IntFree(map); Vec_IntFree(order); ABC_FREE(rules);
        if ( result == 1 ) break;
    }
    return result;
}

/**Function*************************************************************

  Synopsis    [Runs the complete fixed recipe for a weighted source identity.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyWeighted( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms,
                        Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width )
{
    return Acec2_PolyWeightedInt(m, vOutputs, vTerms, vConstants, vProducts, Width, 0);
}

/**Function*************************************************************

  Synopsis    [Tries a small polynomial reduction before a prefix Boolean check.]

  Description [One pass, 2048 live terms and 65536 work units. A completed
  zero remainder has the same exact meaning as in the full recipe. Neither
  the caller's parameters nor the complete-word effort limits are changed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyWeightedQuick( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms,
                             Vec_Int_t * vConstants, Vec_Int_t * vProducts, int Width )
{
    return Acec2_PolyWeightedInt(m, vOutputs, vTerms, vConstants, vProducts, Width, 1);
}

/**Function*************************************************************

  Synopsis    [Runs an ordered polynomial recipe with one shared stop policy.]

  Description [Each code selects linear rules in its low bits and optional
  SAT carry recovery in bit three. Caller-supplied order and effort bounds
  preserve the distinct whole-output and product-certificate search policies.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Poly_t * Acec2_PolyRecipe( Acec2_Man_t * m, abctime Deadline, int Width,
                                       int Limit, const int * Recipe, int nPasses )
{
    Acec2_Poly_t * p = NULL; int i;
    for ( i = 0; i < nPasses; i++ )
    {
        if ( i && Acec2_PolyStop(m, Deadline) ) break;
        p = Acec2_PolyBuildPass(m, Deadline, Recipe[i] >> 3, Recipe[i] & 7, Width, Limit);
        if ( p ) break;
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Tries cut identities first, then proved nonlocal carry rules.]

  Description [Preserving the original cell pairing is crucial for early
  cancellation. Extra valid substitutions can otherwise increase term size.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Poly_t * Acec2_PolyBuild( Acec2_Man_t * m, abctime Deadline, int Width )
{
    static const int Recipe[] = {4, 0, 5, 8, 1, 10, 3}, Cheap[] = {4, 0, 1};
    Acec2_Poly_t * p;
    int nLimit = m->nPolyTermLimit > 0 ? m->nPolyTermLimit : 500000;
    ABC_INT64_T nInputs = Gia_ManCiNum(m->pGia);
    int nFirst, cheap = (m->Pars.nCecOptions & ACEC2_CEC_DEFER) &&
        m->Pars.nCecPolyLimit > 0 && m->Pars.nCecPolyLimit <= 4096;
    if ( m->Pars.nCecPolyLimit > 0 ) nLimit = Abc_MinInt(nLimit, m->Pars.nCecPolyLimit);
    nFirst = (int)Abc_MinInt(nLimit, Abc_MinInt(16384,
        nInputs > 256 || Width > 4096 ? 16384 : Abc_MaxInt(1024, (int)(nInputs*nInputs/4)+4*Width)));
    m->nPolyCarries = m->nPolyProbes = 0;
    // A valid region substitution can still be a poor elimination order.
    // Give both inexpensive policies a bounded first attempt before either
    // receives the full workspace. This is an effort tier, not a product
    // size limit; larger complete identities retain the full-budget passes.
    if ( nFirst < nLimit )
    {
        p = Acec2_PolyRecipe(m, Deadline, Width, nFirst, Recipe, 2);
        if ( p || Acec2_PolyStop(m, Deadline) ) return p;
    }
    p = Acec2_PolyRecipe(m, Deadline, Width, nLimit, cheap ? Cheap : Recipe, cheap ? 3 : 7);
    if ( !p && cheap && !Acec2_PolyStop(m, Deadline) ) m->fPolyEffortLimit = 1;
    return p;
}

/**Function*************************************************************

  Synopsis    [Certifies one result word against an explicit product formula.]

  Description [Operand literals use CI ordinal plus one as their variable;
  literals zero and one are constants. Each port can have repeated, phased
  or fixed bits. Mode bits select signed ports. Subtract the exact product
  polynomial modulo 2^Width; a zero remainder proves every result bit.
  The effort limit applies only to this check. Other polynomial searches
  retain their existing limits and fallback rules. Returns -1 on a limit,
  zero for a completed unequal polynomial, and one for a certificate.]

  SideEffects [Updates the analysis manager's polynomial statistics.]

  SeeAlso     []

***********************************************************************/
int Acec2_PolyCheckProduct( Acec2_Man_t * m, Vec_Int_t ** vOps, int Mode,
                           int Width, int nTermLimit, abctime Deadline )
{
    static const int Recipe[] = {4, 0, 1, 8, 10, 5}, Cheap[] = {0, 4, 1};
    Acec2_Poly_t * p;
    int i, j, side, a, b, sign, mask, termSign, valid, result, cheap, steps = 0;
    int var[2], phase[2], size[2];
    if ( !m || !m->pGia || !m->Pars.fAlgebra || !vOps || !vOps[0] || !vOps[1] ||
         Mode < 0 || Mode > 3 || Width < 1 || Width > Gia_ManCoNum(m->pGia) || nTermLimit < 1 ) return -1;
    for ( side = 0; side < 2; side++ )
    {
        size[side] = Vec_IntSize(vOps[side]);
        Vec_IntForEachEntry(vOps[side], a, i)
            if ( a < 0 || (a >> 1) > Gia_ManCiNum(m->pGia) ) return -1;
    }
    if ( m->Pars.nCecPolyLimit > 0 ) nTermLimit = Abc_MinInt(nTermLimit, m->Pars.nCecPolyLimit);
    // The first effort tiers use existing exact rules only. A term cap alone
    // does not bound repeated SAT carry recovery over many boundary choices.
    // Keep that recovery for a later tier after other operands were tried.
    cheap = (m->Pars.nCecOptions & ACEC2_CEC_DEFER) && m->Pars.nCecPolyLimit > 0 && m->Pars.nCecPolyLimit <= 4096;
    p = Acec2_PolyRecipe(m, Deadline, Width, nTermLimit, cheap ? Cheap : Recipe, cheap ? 3 : 6);
    if ( !p && cheap && !Acec2_PolyStop(m, Deadline) ) m->fPolyEffortLimit = 1;
    if ( !p ) return -1;
    for ( i = 0; i < size[0] && i < Width && !p->fFailed; i++ )
        for ( j = 0; j < size[1] && i+j < Width && !p->fFailed; j++ )
        {
            if ( (++steps & 255) == 0 && Acec2_PolyStop(m, Deadline) ) { p->fFailed = 1; break; }
            a = Vec_IntEntry(vOps[0], i); b = Vec_IntEntry(vOps[1], j);
            if ( !a || !b ) continue;
            var[0] = a >> 1; var[1] = b >> 1; phase[0] = a & 1; phase[1] = b & 1;
            sign = (((Mode & 1) && i == size[0]-1) ^ ((Mode & 2) && j == size[1]-1)) ? 1 : -1;
            memset(p->pCoef, 0, sizeof(word)*p->nWords);
            p->pCoef[(i+j) >> 6] = (word)1 << ((i+j) & 63);
            // Expand phased factors as x or (1-x). Equal variables occur
            // only once in a Boolean monomial, including square products.
            for ( mask = 0; mask < 4 && !p->fFailed; mask++ )
            {
                valid = 1; termSign = sign; Vec_IntClear(p->vMono);
                for ( side = 0; side < 2; side++ )
                    if ( mask & (1 << side) )
                    {
                        if ( !var[side] ) { valid = 0; break; }
                        Vec_IntPushUnique(p->vMono, var[side]);
                        if ( phase[side] ) termSign = -termSign;
                    }
                    else if ( !phase[side] ) { valid = 0; break; }
                if ( !valid ) continue;
                if ( Vec_IntSize(p->vMono) == 2 && Vec_IntEntry(p->vMono, 0) > Vec_IntEntry(p->vMono, 1) )
                    ABC_SWAP(int, Vec_IntArray(p->vMono)[0], Vec_IntArray(p->vMono)[1]);
                Acec2_PolyAdd(p, p->vMono, p->pCoef, termSign);
            }
        }
    result = p->fFailed || Acec2_PolyStop(m, Deadline) ? -1 : p->nUsed == 0;
    Acec2_PolyFree(p);
    return result;
}

/**Function*************************************************************

  Synopsis    [Releases a saved extraction and its exact dependencies.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyMemoFree( Acec2_PolyMemo_t * p )
{
    if ( !p ) return;
    Vec_IntFree(p->vRoots); Vec_IntFree(p->vDeps); Vec_IntFreeP(&p->vConst);
    Vec_WecFreeP(&p->vCols); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Discards all entries when destination bindings are invalidated.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyMemoClear( Acec2_PolyCtx_t * p )
{
    Acec2_PolyMemo_t * q;
    int i;
    Vec_PtrForEachEntry(Acec2_PolyMemo_t *, p->vMemos, q, i)
        { Acec2_PolyMemoFree(q); Vec_PtrWriteEntry(p->vMemos, i, NULL); }
    p->nMemoSize = 0;
}

/**Function*************************************************************

  Synopsis    [Updates the cut while retaining rules and dependency caches.]

  Description [Destination nodes may only be appended between updates.
  A reindexing or compaction requires a new context. Changed CI bindings
  invalidate every entry; AND bindings are compared only where used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyRegionUpdate( Acec2_PolyCtx_t * p, Vec_Int_t * vMap, Vec_Int_t * vFrontier )
{
    Acec2_Man_t * m = p->pMan;
    Gia_Obj_t * o;
    int i, id, lit, fChanged = 0;
    if ( (ABC_INT64_T)Gia_ManObjNum(m->pGia)+Vec_IntSize(vFrontier) >= 0x3FFFFFFF ) return 0;
    p->nLimit = m->Pars.nCecPolyLimit > 0 ?
        Abc_MinInt(20000, m->Pars.nCecPolyLimit) : 20000;
    p->nShared = Vec_IntSize(vFrontier); p->nVars = p->nShared+Gia_ManObjNum(m->pGia);
    Gia_ManForEachCi(m->pGia, o, i)
    {
        id = Gia_ObjId(m->pGia, o); lit = Abc_Lit2Var(Vec_IntEntry(vMap, id));
        fChanged |= Vec_IntEntry(p->vMap, id) != lit;
        Vec_IntWriteEntry(p->vMap, id, lit);
    }
    if ( fChanged ) Acec2_PolyMemoClear(p);
    Vec_IntForEachEntryStart(p->vOrder, id, i, Gia_ManCiNum(m->pGia))
    {
        Vec_IntWriteEntry(p->vMap, id, p->nShared+i+1);
        lit = Vec_IntEntry(vMap, id);
        Vec_IntWriteEntry(p->vAbs, id, Vec_IntEntry(vFrontier, Abc_Lit2Var(lit)) ? lit : -1);
    }
    Vec_WecFreeP(&p->vZeros);
    p->vZeros = Acec2_PolyZeroRules(m, p->vMap, p->nVars, 0);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Starts a persistent context for one immutable source analysis.]

  Description [Internal variables are larger than every shared variable,
  so backward substitution eliminates them before reaching the cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_PolyCtx_t * Acec2_PolyRegionStart( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vFrontier )
{
    Acec2_PolyCtx_t * p;
    if ( (ABC_INT64_T)Gia_ManObjNum(m->pGia)+Vec_IntSize(vFrontier) >= 0x3FFFFFFF ) return NULL;
    p = ABC_CALLOC(Acec2_PolyCtx_t, 1); p->pMan = m; p->nLimit = 20000;
    p->pRules = Acec2_PolyRules(m);
    Acec2_PolyParityRules(m, p->pRules, m->Deadline);
    Acec2_PolyLinearRules(m, p->pRules);
    p->vOrder = Acec2_PolyOrder(m, p->pRules, m->Deadline);
    if ( !p->vOrder && !Acec2_Stopped(m) )
    {
        // Optional carry equations can introduce a dependency cycle through
        // another decomposition. The forward Boolean rules remain usable.
        ABC_FREE(p->pRules); p->pRules = Acec2_PolyRules(m);
        Acec2_PolyParityRules(m, p->pRules, m->Deadline);
        p->vOrder = Acec2_PolyOrder(m, p->pRules, m->Deadline);
    }
    if ( !p->vOrder ) { ABC_FREE(p->pRules); ABC_FREE(p); return NULL; }
    p->vMap = Vec_IntStart(Gia_ManObjNum(m->pGia)); p->vAbs = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
    p->vMemos = Vec_PtrStart(Abc_MaxInt(1, 2*Vec_WecSize(m->vTrees)));
    Acec2_PolyRegionUpdate(p, vMap, vFrontier);
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the per-design local polynomial context.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_PolyRegionStop( Acec2_PolyCtx_t * p )
{
    if ( !p ) return;
    Acec2_PolyMemoClear(p); Vec_PtrFree(p->vMemos); Vec_WecFreeP(&p->vZeros);
    ABC_FREE(p->pRules); Vec_IntFree(p->vMap); Vec_IntFree(p->vAbs); Vec_IntFree(p->vOrder); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Reads reuse counts without exposing polynomial internals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_PolyRegionReuse( Acec2_PolyCtx_t * p, int * pHits, int * pLimits )
{
    if ( !p ) return;
    *pHits += p->nCacheHits; *pLimits += p->nCacheLimits;
}

/**Function*************************************************************

  Synopsis    [Reuses extraction only when every consulted binding agrees.]

  Description [The source rules, tree and substitution order are immutable.
  Dependencies include absence from the cut, not just its selected leaves.
  Thus inserting a new cut above a previously expanded cone invalidates it.
  A cached effort limit remains unknown; it is never an arithmetic proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyMemoLookup( Acec2_PolyCtx_t * c, int Tree, Vec_Int_t * vRoots,
                               Vec_Wec_t * vCols, Vec_Int_t * vConst, int * pFlip, abctime Deadline )
{
    Acec2_PolyMemo_t * p;
    Vec_Int_t * v;
    int slot, i;
    for ( slot = 2*Tree; slot < 2*Tree+2; slot++ )
    {
        p = (Acec2_PolyMemo_t *)Vec_PtrEntry(c->vMemos, slot);
        if ( !p || p->Width != Vec_IntSize(vConst) || (!p->Result && p->Limit != c->nLimit) || !Vec_IntEqual(p->vRoots, vRoots) ) continue;
        for ( i = 0; i < Vec_IntSize(p->vDeps); i += 2 )
        {
            if ( (i & 4095) == 0 && Acec2_PolyStop(c->pMan, Deadline) ) return -1;
            if ( Vec_IntEntry(c->vAbs, Vec_IntEntry(p->vDeps, i)) != Vec_IntEntry(p->vDeps, i+1) ) break;
        }
        if ( i < Vec_IntSize(p->vDeps) ) continue;
        c->nCacheHits++; c->nCacheLimits += !p->Result;
        if ( !p->Result ) return 0;
        Vec_WecForEachLevel(p->vCols, v, i) Vec_IntAppend(Vec_WecEntry(vCols, i), v);
        for ( i = 0; i < p->Width; i++ ) Vec_IntWriteEntry(vConst, i, Vec_IntEntry(p->vConst, i));
        *pFlip = p->Flip;
        return 1;
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Stores completed extraction or a reproducible effort limit.]

  Description [Two widths per region cover the word and its low prefix.
  Total stored integers are bounded. Clock and cancellation failures are
  deliberately not memoized. The cache owns copies of every saved vector.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyMemoSave( Acec2_PolyCtx_t * c, int Tree, Vec_Int_t * vRoots, Vec_Int_t * vDeps,
                              Vec_Wec_t * vCols, Vec_Int_t * vConst, int Flip, int Result )
{
    Acec2_PolyMemo_t * p;
    int slot;
    ABC_INT64_T nSize = (ABC_INT64_T)Vec_IntSize(vRoots)+Vec_IntSize(vDeps);
    if ( Result ) nSize += 5*(ABC_INT64_T)Vec_IntSize(vConst)+Vec_WecSizeSize(vCols);
    for ( slot = 2*Tree; slot < 2*Tree+1; slot++ )
    {
        p = (Acec2_PolyMemo_t *)Vec_PtrEntry(c->vMemos, slot);
        if ( !p || p->Width == Vec_IntSize(vConst) ) break;
    }
    p = (Acec2_PolyMemo_t *)Vec_PtrEntry(c->vMemos, slot);
    if ( p ) { c->nMemoSize -= p->nSize; Acec2_PolyMemoFree(p); Vec_PtrWriteEntry(c->vMemos, slot, NULL); }
    if ( nSize > 4000000-c->nMemoSize ) return;
    p = ABC_CALLOC(Acec2_PolyMemo_t, 1);
    p->vRoots = Vec_IntDup(vRoots); p->vDeps = Vec_IntDup(vDeps);
    p->Width = Vec_IntSize(vConst); p->Flip = Flip; p->Result = Result; p->Limit = c->nLimit; p->nSize = (int)nSize;
    if ( Result ) { p->vCols = Vec_WecDup(vCols); p->vConst = Vec_IntDup(vConst); }
    c->nMemoSize += (int)nSize; Vec_PtrWriteEntry(c->vMemos, slot, p);
}

/**Function*************************************************************

  Synopsis    [Copies or negates a modular coefficient into scratch storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyCoefficient( Acec2_Poly_t * p, int Id, int fNeg )
{
    int j;
    word carry = 1, value;
    for ( j = 0; j < p->nWords; j++ )
    {
        value = Vec_WrdEntry(p->vCoefs, Id*p->nWords+j);
        if ( !fNeg ) p->pCoef[j] = value;
        else { value = ~value; p->pCoef[j] = value+carry; carry = p->pCoef[j] < value; }
    }
    if ( p->nWidth & 63 ) p->pCoef[p->nWords-1] &= (((word)1) << (p->nWidth & 63))-1;
}

/**Function*************************************************************

  Synopsis    [Adds or subtracts a power of two modulo the column width.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyConstant( Vec_Int_t * vConst, int Rank, int fSub )
{
    int bit;
    for ( ; Rank < Vec_IntSize(vConst); Rank++ )
    {
        bit = Vec_IntEntry(vConst, Rank); Vec_IntWriteEntry(vConst, Rank, bit ^ 1);
        if ( bit == fSub ) break;
    }
}

/**Function*************************************************************

  Synopsis    [Expands selected arithmetic bits to canonical product columns.]

  Description [At most one selected bit per column forms an internal word.
  Exact substitution proves this word even when selection is incomplete or
  crosses region boundaries. It stops at shared operand nodes, not at the
  different partial-product encodings. A globally complemented root word
  is oriented by its first nonconstant coefficient. A negative coefficient
  -k*x becomes k*~x-k, keeping the compressor inputs sparse. Limits leave the
  caller free to use its original literal-based normalization instead.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyRegion( Acec2_PolyCtx_t * c, int Tree, Vec_Int_t * vRoots, Gia_Man_t * pNew,
                     Vec_Wec_t * vCols, Vec_Int_t * vConst, abctime Deadline,
                     int nMaxObjs, int * pFlip )
{
    Acec2_Man_t * m = c->pMan;
    Acec2_Poly_t * p;
    Vec_Int_t * v;
    int width = Vec_IntSize(vConst), i, j, k, lit, rank, first = -1, sign, alive, unequal, result = 0, cached;
    if ( Acec2_PolyStop(m, Deadline) ) return 0;
    if ( c->pDestination != pNew ) { Acec2_PolyMemoClear(c); c->pDestination = pNew; }
    cached = Acec2_PolyMemoLookup(c, Tree, vRoots, vCols, vConst, pFlip, Deadline);
    if ( cached >= 0 ) return cached;
    if ( Acec2_PolyStop(m, Deadline) ) return 0;
    p = Acec2_PolyAlloc(m, width, c->nVars, c->nLimit); p->vDeps = Vec_IntAlloc(100);
    p->vZeros = c->vZeros; p->fBorrowZeros = 1;
    p->nWorkLimit = (ABC_INT64_T)16*c->nLimit+1024;
    for ( i = 0; i < Vec_IntSize(vRoots); i += 2 )
    {
        lit = Vec_IntEntry(vRoots, i); rank = Vec_IntEntry(vRoots, i+1);
        Acec2_PolySeed(p, Vec_IntEntry(c->vMap, Abc_Lit2Var(lit)), Abc_LitIsCompl(lit), rank);
    }
    // The checked region identity is roots = leaves + bias. Add its zero
    // polynomial before substitution. Selected roots cancel immediately;
    // unselected roots are subtracted, so arbitrary word proposals remain
    // exact, including multi-root columns and a sum-only truncated top bit.
    v = Vec_WecEntry(m->vRoots, Tree);
    for ( i = 0; i < Vec_IntSize(v); i += 2 )
    {
        lit = Vec_IntEntry(v, i); rank = Vec_IntEntry(v, i+1);
        Acec2_PolySeedSigned(p, Vec_IntEntry(c->vMap, Abc_Lit2Var(lit)), Abc_LitIsCompl(lit), rank, -1);
    }
    v = Vec_WecEntry(m->vLeaves, Tree);
    for ( i = 0; i < Vec_IntSize(v); i += 2 )
    {
        lit = Vec_IntEntry(v, i); rank = Vec_IntEntry(v, i+1);
        Acec2_PolySeed(p, Vec_IntEntry(c->vMap, Abc_Lit2Var(lit)), Abc_LitIsCompl(lit), rank);
    }
    Vec_IntForEachEntry(Vec_WecEntry(m->vBias, Tree), rank, i) Acec2_PolySeed(p, 0, 1, rank);
    Acec2_PolyExpand(p, c->pRules, c->vOrder, c->vMap, c->vAbs, Deadline);
    if ( m->Pars.fVerbose && p->fFailed )
        Abc_Print(1, "  Local polynomial limit: first root = %d, width = %d, live = %d, peak = %d, steps = %lld, node = %d, rule = %d.\n",
            Vec_IntSize(vRoots) ? Vec_IntEntry(vRoots, 0) : -1, width, p->nUsed, p->nPeak, (long long)p->nSteps,
            p->iLastVar, c->pRules[p->iLastVar].Type);
    if ( p->fFailed ) goto finish;
    // Pick the lexicographically first coefficient that changes under negation.
    for ( i = 0; i < Hsh_VecSize(p->pHash); i++ )
    {
        unequal = 0;
        for ( j = 0; j < p->nWords; j++ )
            unequal |= (Vec_WrdEntry(p->vCoefs, i*p->nWords+j) &
                (j == p->nWords-1 ? ~(((word)1) << ((width-1) & 63)) : ~(word)0)) != 0;
        if ( !unequal ) continue;
        v = Hsh_VecReadEntry(p->pHash, i); if ( !Vec_IntSize(v) ) continue;
        k = 0;
        if ( first >= 0 )
        {
            for ( j = 0; j < Abc_MinInt(Vec_IntSize(v), Vec_IntSize(p->vMono)); j++ )
                if ( Vec_IntEntry(v, j) != Vec_IntEntry(p->vMono, j) )
                { k = Vec_IntEntry(v, j) < Vec_IntEntry(p->vMono, j) ? -1 : 1; break; }
            if ( !k ) k = Vec_IntSize(v)-Vec_IntSize(p->vMono);
        }
        if ( first < 0 || k < 0 )
        { first = i; Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v); }
    }
    *pFlip = first >= 0 && ((Vec_WrdEntry(p->vCoefs, first*p->nWords+p->nWords-1) >> ((width-1) & 63)) & 1);
    if ( *pFlip )
        for ( i = 1; i < Vec_IntSize(vRoots); i += 2 ) Acec2_PolyConstant(vConst, Vec_IntEntry(vRoots, i), 0);
    for ( i = 0; i < Hsh_VecSize(p->pHash); i++ )
    {
        if ( Acec2_PolyStop(m, Deadline) || Gia_ManObjNum(pNew) >= nMaxObjs ) goto finish;
        Acec2_PolyCoefficient(p, i, *pFlip);
        alive = 0; for ( j = 0; j < p->nWords; j++ ) alive |= p->pCoef[j] != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(p->pHash, i);
        if ( !Vec_IntSize(v) )
        {
            for ( rank = 0; rank < width; rank++ )
                if ( (p->pCoef[rank >> 6] >> (rank & 63)) & 1 ) Acec2_PolyConstant(vConst, rank, 0);
            continue;
        }
        lit = 1;
        Vec_IntForEachEntry(v, k, j)
        {
            if ( k <= 0 || k >= c->nShared ) goto finish;
            lit = Gia_ManHashAnd(pNew, lit, Abc_Var2Lit(k, 0));
            if ( Gia_ManObjNum(pNew) >= nMaxObjs ) goto finish;
        }
        sign = (p->pCoef[p->nWords-1] >> ((width-1) & 63)) & 1;
        if ( sign ) Acec2_PolyCoefficient(p, i, *pFlip ^ 1);
        for ( rank = 0; rank < width; rank++ )
            if ( (p->pCoef[rank >> 6] >> (rank & 63)) & 1 )
            {
                Vec_WecPush(vCols, rank, lit ^ sign);
                if ( sign ) Acec2_PolyConstant(vConst, rank, 1);
            }
    }
    result = 1;
finish:
    if ( (result || p->fEffortLimit) && !Acec2_PolyStop(m, Deadline) )
        Acec2_PolyMemoSave(c, Tree, vRoots, p->vDeps, vCols, vConst, result ? *pFlip : 0, result);
    Acec2_PolyFree(p);
    return result;
}

/**Function*************************************************************

  Synopsis    [Finds a single set bit in a modular coefficient.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyPower( word * pWords, int nWords )
{
    int i, j, bit = -1;
    for ( i = 0; i < nWords; i++ )
    {
        word w = pWords[i];
        if ( !w ) continue;
        if ( bit >= 0 || (w & (w-1)) ) return -1;
        for ( j = 0; !(w & 1); j++ ) w >>= 1;
        bit = 64*i+j;
    }
    return bit;
}

/**Function*************************************************************

  Synopsis    [Recognizes a full product from its exact bilinear polynomial.]

  Description [Discovers operand groups and bit order from the complete
  bipartite coefficient graph. No port names, input grouping, or signedness
  hints are used. Truncated products and one-bit operands are not labeled.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyProduct( Acec2_Poly_t * p )
{
    Acec2_Man_t * m = p->pMan;
    Vec_Wec_t * vAdj = Vec_WecStart(Gia_ManCiNum(m->pGia)+1);
    Vec_Int_t * vEdges = Vec_IntAlloc(100), * vRanks = NULL, * vSigns = NULL, * vColors = NULL;
    Vec_Int_t * vIns[2] = {NULL, NULL}, * v, * vRow;
    int i, j, a, b, bit, sign, first = -1, n[2], side, index, ok = 0, signedness[2] = {0, 0};
    word carry, val;
    for ( i = 0; i < Hsh_VecSize(p->pHash); i++ )
    {
        int alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(p->pHash, i);
        if ( Vec_IntSize(v) != 2 ) goto finish;
        a = Vec_IntEntry(v, 0); b = Vec_IntEntry(v, 1);
        if ( a < 1 || b > Gia_ManCiNum(m->pGia) ) goto finish;
        sign = 0; bit = Acec2_PolyPower(Vec_WrdEntryP(p->vCoefs, i*p->nWords), p->nWords);
        if ( bit < 0 )
        {
            carry = 1;
            for ( j = 0; j < p->nWords; j++ )
            {
                val = ~Vec_WrdEntry(p->vCoefs, i*p->nWords+j);
                p->pCoef[j] = val+carry; carry = p->pCoef[j] < val;
            }
            if ( p->nWidth & 63 ) p->pCoef[p->nWords-1] &= (((word)1) << (p->nWidth & 63))-1;
            sign = 1; bit = Acec2_PolyPower(p->pCoef, p->nWords);
            if ( bit < 0 ) goto finish;
        }
        index = Vec_IntSize(vEdges);
        if ( bit == 0 && !sign ) first = index;
        Vec_WecPush(vAdj, a, index); Vec_WecPush(vAdj, b, index);
        Vec_IntPushTwo(vEdges, a, b); Vec_IntPushTwo(vEdges, bit, sign);
    }
    if ( first < 0 ) goto finish;
    a = Vec_IntEntry(vEdges, first); b = Vec_IntEntry(vEdges, first+1);
    n[0] = Vec_IntSize(Vec_WecEntry(vAdj, b)); n[1] = Vec_IntSize(Vec_WecEntry(vAdj, a));
    if ( n[0] < 2 || n[1] < 2 || n[0]+n[1] > p->nWidth || (ABC_INT64_T)n[0]*n[1] != p->nUsed ) goto finish;
    vRanks = Vec_IntStartFull(Vec_WecSize(vAdj)); vSigns = Vec_IntStart(Vec_WecSize(vAdj)); vColors = Vec_IntStartFull(Vec_WecSize(vAdj));
    for ( side = 0; side < 2; side++ )
    {
        vIns[side] = Vec_IntStartFull(n[side]);
        vRow = Vec_WecEntry(vAdj, side ? a : b);
        Vec_IntForEachEntry(vRow, index, j)
        {
            i = Vec_IntEntry(vEdges, index) ^ Vec_IntEntry(vEdges, index+1) ^ (side ? a : b);
            bit = Vec_IntEntry(vEdges, index+2); sign = Vec_IntEntry(vEdges, index+3);
            if ( bit >= n[side] || Vec_IntEntry(vIns[side], bit) >= 0 || Vec_IntEntry(vColors, i) >= 0 || (sign && bit != n[side]-1) ) goto finish;
            Vec_IntWriteEntry(vIns[side], bit, i-1); signedness[side] |= sign;
            Vec_IntWriteEntry(vRanks, i, bit); Vec_IntWriteEntry(vSigns, i, sign); Vec_IntWriteEntry(vColors, i, side);
        }
    }
    for ( i = 0; i < Vec_IntSize(vEdges); i += 4 )
    {
        a = Vec_IntEntry(vEdges, i); b = Vec_IntEntry(vEdges, i+1);
        if ( Vec_IntEntry(vColors, a) < 0 || Vec_IntEntry(vColors, b) < 0 || Vec_IntEntry(vColors, a) == Vec_IntEntry(vColors, b) ||
            Vec_IntEntry(vRanks, a)+Vec_IntEntry(vRanks, b) != Vec_IntEntry(vEdges, i+2) ||
            (Vec_IntEntry(vSigns, a)^Vec_IntEntry(vSigns, b)) != Vec_IntEntry(vEdges, i+3) ) goto finish;
    }
    ok = 1;
finish:
    for ( side = 0; side < 2; side++ )
        if ( ok ) { Vec_IntFreeP(&m->vOperands[side]); m->vOperands[side] = vIns[side]; m->fPolySigned[side] = signedness[side]; }
        else Vec_IntFreeP(&vIns[side]);
    Vec_WecFree(vAdj); Vec_IntFree(vEdges); Vec_IntFreeP(&vRanks); Vec_IntFreeP(&vSigns); Vec_IntFreeP(&vColors);
    if ( ok ) m->nPolyWidth = p->nWidth;
    return ok;
}

/**Function*************************************************************

  Synopsis    [Retains a completed output-product proof as a source record.]

  Description [The exact bilinear polynomial has just certified these
  operands. Use its actual modulus, which may omit common trailing output
  aliases. CI ordinals are translated to source literals. All primary
  inputs remain in the proof cut, including inputs that cancelled out.
  A failure to prove the other design does not discard this certificate.]

  SideEffects [Appends an independently checked product word at most once.]

  SeeAlso     []

***********************************************************************/
static void Acec2_PolyRecordProduct( Acec2_Poly_t * p )
{
    Acec2_Man_t * m = p->pMan;
    Acec2_Word_t * w;
    Gia_Obj_t * o;
    int side, i, input;
    if ( p->fFailed || !m->vOperands[0] || !m->vOperands[1] || m->nPolyWidth != p->nWidth ||
         p->nWidth > Gia_ManCoNum(m->pGia) || Acec2_Stopped(m) ) return;
    w = ABC_CALLOC(Acec2_Word_t, 1); w->Tree = w->Record = -1; w->Width = p->nWidth;
    w->vTerms = Vec_IntAlloc(0); w->vConstants = Vec_IntAlloc(0);
    w->vBits = Vec_IntAlloc(w->Width); w->vSourceCut = Vec_IntAlloc(Gia_ManCiNum(m->pGia));
    w->pProduct = ABC_CALLOC(Acec2_Product_t, 1);
    for ( side = 0; side < 2; side++ )
    {
        w->pProduct->fSigned[side] = m->fPolySigned[side];
        w->pProduct->vOperands[side] = Vec_IntAlloc(Vec_IntSize(m->vOperands[side]));
        Vec_IntForEachEntry(m->vOperands[side], input, i)
            Vec_IntPush(w->pProduct->vOperands[side], 2*Gia_ObjId(m->pGia, Gia_ManCi(m->pGia, input)));
    }
    for ( i = 0; i < w->Width; i++ )
        Vec_IntPush(w->vBits, Gia_ObjFaninLit0p(m->pGia, Gia_ManCo(m->pGia, i)));
    Gia_ManForEachCi(m->pGia, o, i) Vec_IntPush(w->vSourceCut, 2*Gia_ObjId(m->pGia, o));
    m->nPolyRecords += Acec2_RecordAddProductWord(m, w, -1);
}

/**Function*************************************************************

  Synopsis    [Checks whether an existing binary record already covers the outputs.]

  Description [This is a discovery shortcut, not a new certificate. Only
  the already checked low prefix is compared; no missing high bit is inferred.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyWordKnown( Acec2_Man_t * m, int Width )
{
    Acec2_Record_t * r; Vec_Int_t * bits = Vec_IntAlloc(Width);
    int i, j, rank, found = 0;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        if ( r->Prefix < Width || r->vOutputMasks ) continue;
        Vec_IntFill(bits, Width, 0);
        for ( j = 0; j < Vec_IntSize(r->vOutputs); j += 2 )
        {
            rank = Vec_IntEntry(r->vOutputs, j+1);
            if ( rank < Width ) Vec_IntWriteEntry(bits, rank, Vec_IntEntry(r->vOutputs, j));
        }
        for ( j = 0; j < Width; j++ )
            if ( Vec_IntEntry(bits, j) != Gia_ObjFaninLit0p(m->pGia, Gia_ManCo(m->pGia, j)) ) break;
        if ( j == Width ) { found = 1; break; }
    }
    Vec_IntFree(bits); return found;
}

/**Function*************************************************************

  Synopsis    [Requests one bounded source-output certificate on demand.]

  Description [An arithmetic-dense, modest-width output interface can be
  certified without decoding its surrounding Boolean context. Each request
  uses existing exact source rules and one substitution policy. No SAT carry
  search runs here. Completed effort failures are reused until the rule
  database changes or a larger deterministic tier is requested. A stopped
  attempt never becomes a cached rejection. Profiling can request the same
  independently checked records as CEC.]

  SideEffects [Consumes one work unit only when a new proof is attempted.]

  SeeAlso     []

***********************************************************************/
int Acec2_EnrichPolynomial( Acec2_Man_t * m, int * pnWork )
{
    static const int policies[ACEC2_OUTPUT_POLICIES] = {4, 0, 1, 6, 2};
    Acec2_Poly_t * p; int generation[5], i, candidate, choice = -1, limit, before, width;
    abctime clk;
    if ( !m || !pnWork || *pnWork < 1 || !m->Pars.fAlgebra || m->Pars.nAnalysisLevel < 3 ||
         m->nPolyRecords || m->fOutputPolyComplete || Acec2_Stopped(m) ) return 0;
    width = Gia_ManCoNum(m->pGia);
    if ( width < 2 || width > 512 || width > m->Pars.nMaxWidth || Gia_ManAndNum(m->pGia) > 200000 ||
         ((Gia_ManCiNum(m->pGia) > 12 || Gia_ManAndNum(m->pGia) > 2048) &&
          (Vec_PtrSize(m->vCells) < 8 || (ABC_INT64_T)m->nCovered*4 < Gia_ManAndNum(m->pGia))) )
    { m->nOutputPolySkipped = 1; return 0; }
    if ( Acec2_PolyWordKnown(m, width) ) { m->fOutputPolyComplete = 1; return 0; }
    generation[0] = Vec_PtrSize(m->vCells); generation[1] = Vec_PtrSize(m->vAlternatives);
    generation[2] = m->vExtraRules ? Vec_IntSize(m->vExtraRules) : 0;
    generation[3] = Vec_IntSize(m->vVanish); generation[4] = Vec_IntSize(m->vXors);
    for ( i = 0; i < 5; i++ ) if ( generation[i] != m->nOutputPolyGeneration[i] ) break;
    if ( i < 5 )
    {
        memcpy(m->nOutputPolyGeneration, generation, sizeof(generation));
        memset(m->nOutputPolyTried, 0, sizeof(m->nOutputPolyTried));
    }
    limit = m->Pars.nCecPolyLimit > 0 ? Abc_MinInt(4096, m->Pars.nCecPolyLimit) : 4096;
    if ( m->nPolyTermLimit > 0 ) limit = Abc_MinInt(limit, m->nPolyTermLimit);
    // Enrichment invalidates effort failures, but must not send every
    // request back to the first policy and starve the other exact orders.
    for ( i = 0; i < ACEC2_OUTPUT_POLICIES; i++ )
    {
        candidate = (m->iOutputPolyPolicy+i)%ACEC2_OUTPUT_POLICIES;
        if ( m->nOutputPolyTried[candidate] < limit ) { choice = candidate; break; }
    }
    if ( choice < 0 ) return 0;
    (*pnWork)--; m->nOutputPolyAttempts++; before = Vec_PtrSize(m->vRecords); clk = Abc_Clock();
    p = Acec2_PolyBuildPass(m, m->Deadline, 0, policies[choice], width, limit);
    if ( !Acec2_Stopped(m) )
    {
        m->nOutputPolyTried[choice] = limit;
        m->iOutputPolyPolicy = (choice+1)%ACEC2_OUTPUT_POLICIES;
        if ( p )
        {
            if ( Acec2_PolyProduct(p) ) Acec2_PolyRecordProduct(p);
            else m->nPolyRecords += Acec2_RecordOutputPolynomial(m, width, p->pHash, p->vCoefs);
            if ( !Acec2_Stopped(m) ) m->fOutputPolyComplete = 1;
        }
        else m->nOutputPolyLimits++;
    }
    Acec2_PolyFree(p);
    if ( m->Pars.fVerbose ) Abc_Print(1, "Source output polynomial: policy = %d, term budget = %d, status = %s, new records = %d, time = %.3f sec.\n",
        policies[choice], limit, m->nPolyStatus == 1 ? "complete" : "limited", Vec_PtrSize(m->vRecords)-before, (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    m->TimeRecords += Abc_Clock()-clk; m->Time += Abc_Clock()-clk;
    return Vec_PtrSize(m->vRecords)-before;
}

/**Function*************************************************************

  Synopsis    [Profiles the ordered output word with a bounded exact proof.]

  Description [The existing cut-analysis deadline also bounds this stage.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_ProfilePolynomial( Acec2_Man_t * m )
{
    Acec2_Poly_t * p;
    abctime start = Abc_Clock(), stop = m->Deadline;
    if ( m->fPolyProfiled || (m->nPolyStatus == 1 && m->nPolyRecords) ) return;
    m->fPolyProfiled = 1;
    p = Acec2_PolyBuild(m, stop, Gia_ManCoNum(m->pGia));
    if ( p )
    {
        if ( Acec2_PolyProduct(p) ) Acec2_PolyRecordProduct(p);
        else m->nPolyRecords += Acec2_RecordOutputPolynomial(m, p->nWidth, p->pHash, p->vCoefs);
    }
    Acec2_PolyFree(p); m->Time += Abc_Clock()-start;
}

/**Function*************************************************************

  Synopsis    [Compares exact output polynomials; failure is inconclusive.]

  Description [Equal completed polynomials prove equivalence. A smallest
  differing monomial supplies a counterexample, independently validated by
  the caller. Time or storage limits leave ordinary CEC available.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PolyCompareInt( Acec2_Man_t * m0, Acec2_Man_t * m1, abctime Deadline, Abc_Cex_t ** ppCex, int fReport, int nPrefix )
{
    Acec2_Poly_t * p[2] = {NULL, NULL};
    Vec_Int_t * v, * vDiff = Vec_IntAlloc(100);
    int side, i, j, id, alive, size, bit = -1, first, result = -1, width, a, b, x, y, steps = 0;
    word diff;
    abctime start = Abc_Clock(), stop = Deadline;
    if ( ppCex ) *ppCex = NULL;
    if ( !m0 || !m1 || !m0->Pars.fAlgebra || Gia_ManCiNum(m0->pGia) != Gia_ManCiNum(m1->pGia) || Gia_ManCoNum(m0->pGia) != Gia_ManCoNum(m1->pGia) ) goto finish;
    if ( nPrefix > Gia_ManCoNum(m0->pGia) || nPrefix < -1 ) goto finish;
    if ( Acec2_PolyStop(m0, stop) || Acec2_PolyStop(m1, stop) ) goto finish;
    // A common constant or a common duplicate of a lower bit is already
    // determined by that lower bit. Avoid expanding sign extension into an
    // unsigned word polynomial: it can introduce exponentially many terms.
    for ( width = nPrefix < 0 ? Gia_ManCoNum(m0->pGia) : nPrefix; width > 0; width-- )
    {
        if ( (width & 1023) == 0 && Acec2_PolyStop(m0, stop) ) goto finish;
        a = Gia_ObjFaninLit0p(m0->pGia, Gia_ManCo(m0->pGia, width-1));
        b = Gia_ObjFaninLit0p(m1->pGia, Gia_ManCo(m1->pGia, width-1));
        if ( a < 2 && a == b ) continue;
        for ( i = 0; i < width-1; i++ )
        {
            if ( (++steps & 1023) == 0 && Acec2_PolyStop(m0, stop) ) goto finish;
            x = Gia_ObjFaninLit0p(m0->pGia, Gia_ManCo(m0->pGia, i));
            y = Gia_ObjFaninLit0p(m1->pGia, Gia_ManCo(m1->pGia, i));
            if ( (a ^ x) <= 1 && (a ^ x) == (b ^ y) ) break;
        }
        if ( i == width-1 ) break;
    }
    if ( !width ) { result = 1; goto finish; }
    p[0] = Acec2_PolyBuild(m0, stop, width);
    if ( p[0] )
    {
        if ( Acec2_PolyProduct(p[0]) ) { if ( fReport ) Acec2_PolyRecordProduct(p[0]); }
        else if ( fReport ) m0->nPolyRecords += Acec2_RecordOutputPolynomial(m0, width, p[0]->pHash, p[0]->vCoefs);
        p[1] = Acec2_PolyBuild(m1, stop, width);
    }
    if ( p[1] )
    {
        if ( Acec2_PolyProduct(p[1]) ) { if ( fReport ) Acec2_PolyRecordProduct(p[1]); }
        else if ( fReport ) m1->nPolyRecords += Acec2_RecordOutputPolynomial(m1, width, p[1]->pHash, p[1]->vCoefs);
    }
    if ( !p[0] || !p[1] ) goto finish;
    size = ABC_INT_MAX;
    for ( side = 0; side < 2; side++ )
        for ( i = 0; i < Vec_IntSize(p[side]->vNext); i++ )
        {
            if ( (i & 1023) == 0 && Acec2_PolyStop(m0, stop) ) goto finish;
            alive = 0;
            for ( j = 0; j < p[side]->nWords; j++ ) alive |= Vec_WrdEntry(p[side]->vCoefs, i*p[side]->nWords+j) != 0;
            if ( !alive ) continue;
            v = Hsh_VecReadEntry(p[side]->pHash, i);
            if ( Vec_IntSize(v) >= size ) continue;
            id = Hsh_VecManAdd(p[!side]->pHash, v); first = -1;
            for ( j = 0; j < p[side]->nWords; j++ )
            {
                diff = Vec_WrdEntry(p[side]->vCoefs, i*p[side]->nWords+j) -
                    (id < Vec_IntSize(p[!side]->vNext) ? Vec_WrdEntry(p[!side]->vCoefs, id*p[side]->nWords+j) : 0);
                if ( !diff ) continue;
                for ( first = 64*j; !(diff & 1); first++ ) diff >>= 1;
                break;
            }
            if ( first < 0 ) continue;
            size = Vec_IntSize(v); bit = first; Vec_IntClear(vDiff); Vec_IntAppend(vDiff, v);
        }
    result = bit < 0 ? 1 : 0;
    if ( result == 0 && ppCex )
    {
        // All proper submonomials have zero difference by minimal cardinality.
        // Setting precisely this monomial's variables to one evaluates its
        // nonzero difference coefficient; its low set bit is the failing CO.
        *ppCex = Abc_CexAlloc(0, Gia_ManCiNum(m0->pGia), 1); (*ppCex)->iPo = bit;
        Vec_IntForEachEntry(vDiff, id, i) Abc_InfoSetBit((*ppCex)->pData, id-1);
    }
finish:
    if ( m0 && m1 && m0->Pars.fVerbose )
        Abc_Print(1, "Polynomial: status = %d / %d, terms = %d / %d, peak = %d / %d, proved carries = %d / %d, probes = %d / %d, time = %.3f sec.\n",
            m0->nPolyStatus, m1->nPolyStatus, m0->nPolyTerms, m1->nPolyTerms, m0->nPolyPeak, m1->nPolyPeak,
            m0->nPolyCarries, m1->nPolyCarries, m0->nPolyProbes, m1->nPolyProbes, (double)(Abc_Clock()-start)/CLOCKS_PER_SEC);
    if ( fReport && result == 1 ) Abc_Print(1, "Exact arithmetic proof: all %d output bits agree modulo 2^%d.\n", Gia_ManCoNum(m0->pGia), Gia_ManCoNum(m0->pGia));
    if ( fReport && result == 0 ) Abc_Print(1, "Exact arithmetic counterexample: output bit %d differs.\n", bit);
    Vec_IntFree(vDiff); Acec2_PolyFree(p[0]); Acec2_PolyFree(p[1]); return result;
}

/**Function*************************************************************

  Synopsis    [Checks an ordered output word and reports its proof result.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyCompare( Acec2_Man_t * m0, Acec2_Man_t * m1, abctime Deadline, Abc_Cex_t ** ppCex )
{
    return Acec2_PolyCompareInt(m0, m1, Deadline, ppCex, 1, -1);
}

/**Function*************************************************************

  Synopsis    [Checks a component proposal without reporting a design verdict.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyCompareQuiet( Acec2_Man_t * m0, Acec2_Man_t * m1, abctime Deadline )
{
    return Acec2_PolyCompareInt(m0, m1, Deadline, NULL, 0, -1);
}

/**Function*************************************************************

  Synopsis    [Returns a component counterexample for boundary refinement.]

  Description [A rejected component proposal is not a design verdict. The
  caller owns the returned assignment and checks it on the extracted cones.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyCompareCex( Acec2_Man_t * m0, Acec2_Man_t * m1, abctime Deadline, Abc_Cex_t ** ppCex )
{
    return Acec2_PolyCompareInt(m0, m1, Deadline, ppCex, 0, -1);
}

/**Function*************************************************************

  Synopsis    [Proves only the specified low output prefix.]

  Description [Callers may merge only these bits after a successful proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_PolyComparePrefix( Acec2_Man_t * m0, Acec2_Man_t * m1, int Width, abctime Deadline )
{
    return Acec2_PolyCompareInt(m0, m1, Deadline, NULL, 0, Width);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
