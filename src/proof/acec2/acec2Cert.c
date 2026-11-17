/**CFile****************************************************************

  FileName    [acec2Cert.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Certifies proposed product words within each source design.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 13, 2026.]

  Revision    [$Id$]

  Description [Independent operand patterns propose result bits. Sum/carry
  connections select coherent words among repeated implementations. Only
  an exact polynomial identity over the independent cut authorizes a source
  word to use the common reference product. Unobserved high bits are omitted;
  missing low sums may be recovered and then checked by the same exact proof.]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef enum { ACEC2_ROOT_CARRY, ACEC2_ROOT_BOUNDARY } Acec2_RootMode_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Scales the certificate budget with the explicit product.]

  Description [Even an ideal extraction retains one term per bit product.
  Allow cancellation workspace without an operand-width-dependent cutoff.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CertTermLimit( Vec_Int_t ** vOps )
{
    ABC_INT64_T n = 8*(ABC_INT64_T)Vec_IntSize(vOps[0])*Vec_IntSize(vOps[1])+1024;
    return n > 0x3FFFFFFF ? 0x3FFFFFFF : Abc_MaxInt(8000, (int)n);
}

/**Function*************************************************************

  Synopsis    [Keys a product-certificate problem independently of its effort.]

  Description [Exact gate data, roots, phased operands and signedness are
  retained. A hash collision cannot authorize reuse. Only a finished proof,
  a completed rejection or deterministic exhaustion is cached by the caller.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CertCache( Acec2_Man_t * m, Gia_Man_t * g, Vec_Int_t * vRoots,
                           Vec_Int_t ** vOps, int Mode, int Width )
{
    Vec_Int_t * key; Gia_Obj_t * o; int i, side, before, id;
    if ( !g || Gia_ManObjNum(g) > 100000 || m->nCertificateWords >= 1000000 ) return -1;
    key = Vec_IntAlloc(100);
    Vec_IntPushTwo(key, Mode, Width);
    Vec_IntPush(key, Vec_IntSize(vRoots)); Vec_IntAppend(key, vRoots);
    for ( side = 0; side < 2; side++ )
    { Vec_IntPush(key, Vec_IntSize(vOps[side])); Vec_IntAppend(key, vOps[side]); }
    Vec_IntPushThree(key, Gia_ManObjNum(g), Gia_ManCiNum(g), Gia_ManCoNum(g));
    Gia_ManForEachAnd(g, o, i)
    {
        Vec_IntPush(key, i); Vec_IntPushTwo(key, Gia_ObjFaninLit0p(g, o), Gia_ObjFaninLit1p(g, o));
        Vec_IntPushTwo(key, Gia_ObjIsXor(o), Gia_ObjIsMux(g, o) ? Gia_ObjFaninLit2p(g, o) : -1);
    }
    Gia_ManForEachCo(g, o, i) Vec_IntPush(key, Gia_ObjFaninLit0p(g, o));
    if ( Vec_IntSize(key) > 1000000-m->nCertificateWords ) { Vec_IntFree(key); return -1; }
    if ( !m->hCertificates )
    { m->hCertificates = Hsh_VecManStart(100); m->vCertificates = Vec_IntAlloc(100); }
    before = Hsh_VecSize(m->hCertificates); id = Hsh_VecManAdd(m->hCertificates, key);
    if ( id == before ) { Vec_IntPushFour(m->vCertificates, 0, 0, 0, 0); m->nCertificateWords += Vec_IntSize(key); }
    Vec_IntFree(key); return id;
}

/**Function*************************************************************

  Synopsis    [Indexes checked carry siblings of selected and alternative sums.]

  Description [Existing cells are immutable; on-demand recovery appends
  alternatives. Extend the private index when those cells arrive so later
  word proposals can use them. The index guides discovery, not proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wec_t * Acec2_CertSiblings( Acec2_Man_t * m )
{
    Vec_Wec_t * v;
    Vec_Ptr_t * cells;
    Acec2_Cell_t * c;
    int pass, i;
    if ( !m->vWordSiblings ) m->vWordSiblings = Vec_WecStart(Gia_ManObjNum(m->pGia));
    v = m->vWordSiblings;
    for ( pass = 0; pass < 2; pass++ )
    {
        cells = pass ? m->vAlternatives : m->vCells;
        assert(m->nWordSiblingCells[pass] <= Vec_PtrSize(cells));
        for ( i = m->nWordSiblingCells[pass]; i < Vec_PtrSize(cells); i++ )
        {
            c = (Acec2_Cell_t *)Vec_PtrEntry(cells, i);
            if ( c->Ext[1] ) Vec_IntPushUnique(Vec_WecEntry(v, c->Out[0] >> 1), c->Out[1] >> 1);
        }
        m->nWordSiblingCells[pass] = Vec_PtrSize(cells);
    }
    return v;
}

/**Function*************************************************************

  Synopsis    [Counts or marks a candidate cone not already used by this word.]

  Description [Traversal stops at independent operands and has a fixed work
  bound. A failed bound rejects only this root-selection strategy.]

  SideEffects [Updates private traversal marks.]

  SeeAlso     []

***********************************************************************/
static int Acec2_CertCone( Acec2_WordSim_t * p, int Root, Vec_Int_t * vUsed,
                          Vec_Int_t * vSeen, Vec_Int_t * vStack, int Stamp,
                          int Limit, int * pWork, int fMark )
{
    Gia_Obj_t * o;
    int id, count = 0;
    Vec_IntClear(vStack); Vec_IntPush(vStack, Root >> 1);
    while ( Vec_IntSize(vStack) )
    {
        id = Vec_IntPop(vStack);
        if ( !id || Vec_IntEntry(vUsed, id) || Vec_IntEntry(vSeen, id) == Stamp || Vec_IntEntry(p->vStop, id) >= 0 ) continue;
        if ( ++*pWork > 500000 ) return -1;
        Vec_IntWriteEntry(vSeen, id, Stamp);
        if ( fMark ) Vec_IntWriteEntry(vUsed, id, 1);
        o = Gia_ManObj(p->g, id);
        if ( !Gia_ObjIsAnd(o) ) return -1;
        if ( ++count > Limit ) return count;
        Vec_IntPushTwo(vStack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
        if ( Gia_ObjIsMux(p->g, o) ) Vec_IntPush(vStack, Gia_ObjFaninId2(p->g, id));
    }
    return count;
}

/**Function*************************************************************

  Synopsis    [Follows carry connections backward from a proposed high result.]

  Description [A lower sum whose carry feeds the chosen higher cone usually
  belongs to the same implementation. Prefer an actual output or a tap into
  logic outside the operand domain before using carry connectivity and cone
  size as tie breakers. All selected signals still require the independent
  arithmetic certificate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_CertRoots( Acec2_WordSim_t * p, Vec_Wec_t * vSiblings,
                                   int Mode, int Width, int Prefix, Acec2_RootMode_t RootMode )
{
    Vec_Int_t * vUsed = Vec_IntStart(Gia_ManObjNum(p->g)), * vSeen = Vec_IntStart(Gia_ManObjNum(p->g));
    Vec_Int_t * vStack = Vec_IntAlloc(100), * vRoots = Vec_IntStartFull(Prefix), * v, * vLinks;
    int i, j, k, id, lit, best, cost, bestCost, score, bestScore, stamp = 1, work = 0, failed = 0;
    for ( i = Prefix-1; i >= 0; i-- )
    {
        v = Vec_WecEntry(p->vCandidates, Mode*Width+i); best = -1; bestCost = ABC_INT_MAX; bestScore = -1;
        Vec_IntForEachEntry(v, lit, j)
        {
            if ( j >= 128 ) break;
            // Carry-first selection follows one coherent implementation.
            // A boundary preference is a separate alternative; mixing it
            // into this score can select lower bits from another word.
            score = RootMode == ACEC2_ROOT_BOUNDARY && (Vec_IntEntry(p->vBoundary, lit >> 1) & 1) ? 4 : 0;
            vLinks = Vec_WecEntry(vSiblings, lit >> 1);
            Vec_IntForEachEntry(vLinks, id, k)
                if ( Vec_IntEntry(vUsed, id) ) { score |= 2; break; }
            if ( score < bestScore ) continue;
            cost = Acec2_CertCone(p, lit, vUsed, vSeen, vStack, stamp++, score > bestScore ? ABC_INT_MAX : bestCost, &work, 0);
            if ( cost < 0 ) { failed = 1; break; }
            if ( score > bestScore || cost < bestCost || (cost == bestCost && (best < 0 || lit < best)) )
            { bestScore = score; bestCost = cost; best = lit; }
        }
        if ( failed ) break;
        Vec_IntWriteEntry(vRoots, i, best);
        if ( best >= 0 && Acec2_CertCone(p, best, vUsed, vSeen, vStack, stamp++, ABC_INT_MAX, &work, 1) < 0 )
        { failed = 1; break; }
    }
    if ( failed ) Vec_IntFreeP(&vRoots);
    Vec_IntFree(vUsed); Vec_IntFree(vSeen); Vec_IntFree(vStack);
    return vRoots;
}

/**Function*************************************************************

  Synopsis    [Extracts one coherent proposal without changing the candidates.]

  Description [A separate candidate vector preserves every alternative for
  later anchors. The ordinary extractor handles missing bits identically.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_CertExtract( Acec2_WordSim_t * p, Vec_Wec_t * vSiblings,
                                     Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts,
                                     int Mode, int Width, int Prefix, Acec2_RootMode_t RootMode, Vec_Int_t ** pvRoots )
{
    Vec_Int_t * vChosen = Acec2_CertRoots(p, vSiblings, Mode, Width, Prefix, RootMode);
    Vec_Wec_t * vSaved = p->vCandidates, * vSingle;
    Gia_Man_t * g;
    int i, lit;
    if ( !vChosen ) return Acec2_ExtractWord(p, Mode, Width, Prefix, Hsh_Int1ManEntryNum(hCuts), pvRoots, vOps, hCuts, 1, NULL);
    vSingle = Vec_WecStart(4*Width);
    Vec_IntForEachEntry(vChosen, lit, i) if ( lit >= 0 ) Vec_WecPush(vSingle, Mode*Width+i, lit);
    p->vCandidates = vSingle;
    g = Acec2_ExtractWord(p, Mode, Width, Prefix, Hsh_Int1ManEntryNum(hCuts), pvRoots, vOps, hCuts, 0, NULL);
    p->vCandidates = vSaved;
    Vec_WecFree(vSingle); Vec_IntFree(vChosen);
    return g;
}

/**Function*************************************************************

  Synopsis    [Checks whether a proposed word contains any unresolved signal.]

  Description [Already shared words need no new certificate. Previously
  certified bits of this reference also need no repeated proof. A bit
  certified earlier in this call is retained when later sign modes or anchors
  propose the same low result bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CertUseful( Vec_Int_t * vRoots, Vec_Int_t * vMap, Vec_Int_t * vReplaces,
                            Vec_Int_t * vColors, Vec_Int_t * vReference, Vec_Bit_t * vDone )
{
    int i, lit, current;
    Vec_IntForEachEntry(vRoots, lit, i)
    {
        if ( lit < 2 || Vec_BitEntry(vDone, lit >> 1) ) continue;
        current = Vec_IntEntry(vReplaces, lit >> 1);
        if ( current < 0 ) current = Vec_IntEntry(vMap, lit >> 1);
        if ( vReference && (current ^ (lit & 1)) == Vec_IntEntry(vReference, i) ) continue;
        if ( (current >> 1) >= Vec_IntSize(vColors) || Vec_IntEntry(vColors, current >> 1) != 3 ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Records exactly proved original-to-reference bit equalities.]

  Description []

  SideEffects [Updates the private replacement vector.]

  SeeAlso     []

***********************************************************************/
static int Acec2_CertCommit( Vec_Int_t * vRoots, Vec_Int_t * vReference,
                            Vec_Int_t * vMap, Vec_Int_t * vReplaces, Vec_Bit_t * vDone )
{
    int i, lit, current, changed = 0;
    Vec_IntForEachEntry(vRoots, lit, i)
    {
        if ( lit < 2 || Vec_BitEntry(vDone, lit >> 1) ) continue;
        current = Vec_IntEntry(vReplaces, lit >> 1);
        if ( current < 0 ) current = Vec_IntEntry(vMap, lit >> 1);
        Acec2_BitWrite(vDone, lit >> 1, 1);
        if ( (current ^ (lit & 1)) == Vec_IntEntry(vReference, i) ) continue;
        Vec_IntWriteEntry(vReplaces, lit >> 1, Vec_IntEntry(vReference, i) ^ (lit & 1)); changed++;
    }
    return changed;
}

/**Function*************************************************************

  Synopsis    [Certifies a product after recovering absent low result bits.]

  Description [The completion adds checked sum/carry equations, then proves
  the entire resulting word against the explicit product formula. It never
  installs an alias by itself. Only the observed source roots are committed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CertComplete( Acec2_Man_t * m, Vec_Int_t * vRoots, Vec_Int_t ** vOps,
                               int Mode, int Width, abctime Deadline )
{
    Gia_Man_t * g;
    Acec2_Man_t * a;
    Vec_Int_t * vRules = NULL;
    int i, lit, missing = 0, result = -1;
    if ( !m || !vRoots || Acec2_Stop(&m->Pars, Deadline) ) return -1;
    Vec_IntForEachEntry(vRoots, lit, i) missing += lit < 0;
    if ( !missing ) return -1;
    g = Acec2_CompleteWord(m, vRoots, Deadline, &vRules);
    if ( !g ) return -1;
    a = Acec2_AnalyzeCells(g, &m->Pars, Deadline);
    if ( a )
    {
        a->vExtraRules = vRules; vRules = NULL;
        result = Acec2_PolyCheckProduct(a, vOps, Mode, Width, Acec2_CertTermLimit(vOps), Deadline);
        m->fPolyEffortLimit |= a->fPolyEffortLimit;
    }
    Acec2_Free(a); Vec_IntFreeP(&vRules); Gia_ManStop(g);
    return result;
}

/**Function*************************************************************

  Synopsis    [Transfers a completed extracted proof to unique source cut signals.]

  Description [The caller has already proved the extracted word. Every
  used formal variable must have one source representative in the observed
  cones. Otherwise the proof depends on alias equalities and cannot be
  relabelled as an independent source word. Missing result bits also prevent
  this transfer. Stop literals are zero-based; formal GIA inputs start at one.]

  SideEffects [Returns an owned word, or NULL without changing the source.]

  SeeAlso     []

***********************************************************************/
static Acec2_Word_t * Acec2_CertSourceWord( Acec2_Man_t * m, Acec2_WordSim_t * s,
                                          Vec_Int_t * roots, Vec_Int_t ** formal,
                                          int Mode, int nInputs, Acec2_Par_t * pPars, abctime Deadline )
{
    Acec2_Word_t * w = NULL;
    Vec_Int_t * representatives = Vec_IntStartFull(nInputs), * stack = Vec_IntAlloc(100);
    Vec_Int_t * cut = Vec_IntAlloc(32);
    Vec_Bit_t * seen = Vec_BitStart(Gia_ManObjNum(s->g));
    Gia_Obj_t * o;
    int i, id, lit, stop, old, side, steps = 0;
    Vec_IntForEachEntry(roots, lit, i)
    {
        if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(s->g) ) goto finish;
        Vec_IntPush(stack, lit >> 1);
    }
    Acec2_BitWrite(seen, 0, 1);
    while ( Vec_IntSize(stack) )
    {
        id = Vec_IntPop(stack);
        if ( Vec_BitEntry(seen, id) ) continue;
        Acec2_BitWrite(seen, id, 1);
        if ( ++steps > 50000 ) { m->nRecordLimits++; goto finish; }
        if ( (steps & 255) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
        stop = Vec_IntEntry(s->vStop, id);
        if ( stop >= 0 )
        {
            if ( (stop >> 1) >= nInputs ) goto finish;
            lit = 2*id ^ (stop & 1); old = Vec_IntEntry(representatives, stop >> 1);
            // The extracted proof identifies all sources of one formal
            // variable. That proof is independent of aliases only if this
            // source cone uses a single original signal for the variable.
            if ( old >= 0 && old != lit ) goto finish;
            Vec_IntWriteEntry(representatives, stop >> 1, lit);
            Vec_IntPush(cut, 2*id); continue;
        }
        o = Gia_ManObj(s->g, id);
        if ( !Gia_ObjIsAnd(o) ) goto finish;
        Vec_IntPushTwo(stack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
        if ( Gia_ObjIsMux(s->g, o) ) Vec_IntPush(stack, Gia_ObjFaninId2(s->g, id));
    }
    // A formal operand may cancel out of this truncated output cone.
    // It still needs an actual source signal; use an existing cut entry.
    Vec_IntForEachEntry(s->vStop, stop, id)
    {
        if ( (id & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
        if ( id && stop >= 0 && (stop >> 1) < nInputs && Vec_IntEntry(representatives, stop >> 1) < 0 )
            Vec_IntWriteEntry(representatives, stop >> 1, 2*id ^ (stop & 1));
    }
    w = ABC_CALLOC(Acec2_Word_t, 1); w->Tree = w->Record = -1; w->Width = Vec_IntSize(roots);
    w->vTerms = Vec_IntAlloc(0); w->vConstants = Vec_IntAlloc(0); w->vBits = Vec_IntDup(roots);
    w->vSourceCut = Vec_IntDup(cut); Vec_IntUniqify(w->vSourceCut);
    w->pProduct = ABC_CALLOC(Acec2_Product_t, 1);
    w->pProduct->vOperands[0] = Vec_IntAlloc(Vec_IntSize(formal[0]));
    w->pProduct->vOperands[1] = Vec_IntAlloc(Vec_IntSize(formal[1]));
    for ( side = 0; side < 2; side++ )
    {
        w->pProduct->fSigned[side] = ((Mode >> side) & 1) && Vec_IntSize(formal[side]) <= w->Width;
        Vec_IntForEachEntry(formal[side], lit, i)
        {
            if ( i == w->Width ) break;
            if ( lit >= 2 )
            {
                id = (lit >> 1)-1;
                if ( id >= nInputs || Vec_IntEntry(representatives, id) < 0 )
                { Acec2_WordFree(w); w = NULL; goto finish; }
                lit = Vec_IntEntry(representatives, id) ^ (lit & 1);
            }
            Vec_IntPush(w->pProduct->vOperands[side], lit);
        }
    }
finish:
    Vec_IntFree(representatives); Vec_IntFree(stack); Vec_IntFree(cut); Vec_BitFree(seen);
    if ( Acec2_Stop(pPars, Deadline) ) { Acec2_WordFree(w); w = NULL; }
    return w;
}

/**Function*************************************************************

  Synopsis    [Checks and caches one extracted product certificate.]

  Description [Both source discovery and paired matching use the same cache
  and polynomial checker. Missing-bit completion is requested only by paired
  matching. The caller owns the lazily created cell analysis and may reuse it
  when increasing a deterministic term limit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CertCheck( Acec2_Man_t * m, Gia_Man_t * g, Vec_Int_t * roots,
                           Vec_Int_t ** formal, int Mode, int Width, int Limit,
                           Acec2_Par_t * pPars, abctime Deadline, int fComplete,
                           Acec2_Man_t ** ppAnalysis )
{
    Acec2_Par_t pars = *pPars;
    int cache = Acec2_CertCache(m, g, roots, formal, Mode, Width);
    int saved = Acec2_ProofCacheRead(m->vCertificates, cache, Limit, &m->Pars), result;
    if ( saved ) { m->nCertificateHits++; return saved == 2 ? 0 : saved; }
    if ( !fComplete ) m->nCertificateAttempts++;
    pars.fVerbose = 0;
    if ( !*ppAnalysis ) *ppAnalysis = Acec2_AnalyzeCells(g, &pars, Deadline);
    result = *ppAnalysis ? Acec2_PolyCheckProduct(*ppAnalysis, formal, Mode, Width, Limit, Deadline) : -1;
    if ( result < 0 && fComplete ) result = Acec2_CertComplete(*ppAnalysis, roots, formal, Mode, Width, Deadline);
    if ( cache >= 0 && !Acec2_Stop(pPars, Deadline) &&
         (result >= 0 || (*ppAnalysis && (*ppAnalysis)->fPolyEffortLimit)) )
        Acec2_ProofCacheWrite(m->vCertificates, cache, Limit, &m->Pars, result,
            *ppAnalysis && (*ppAnalysis)->fPolyEffortLimit);
    if ( result < 0 && !fComplete ) m->nProductLimits++;
    return result;
}

/**Function*************************************************************

  Synopsis    [Certifies product words on both sources over shared operand cuts.]

  Description [A completed certificate can justify a private replacement.
  When its cut also has an independent source interpretation, store that
  interpretation through the common component record checker.]

  SideEffects [Installs completed proofs and retains independent source records.]

  SeeAlso     []

***********************************************************************/
int Acec2_CertifyProducts( Gia_Man_t * pNew, Acec2_Man_t ** m, Vec_Int_t ** vMaps,
                           Vec_Int_t ** vReplaces, Vec_Int_t ** vOps, int Width,
                           Acec2_Par_t * pPars, abctime Deadline, int * pnWords, int * pPrefix )
{
    Acec2_Par_t LocalPars;
    Acec2_WordSim_t * s[2] = {NULL, NULL};
    Vec_Wec_t * vSiblings[2] = {NULL, NULL};
    Vec_Bit_t * vDone[2] = {NULL, NULL};
    Hsh_Int1Man_t * hCuts = NULL;
    Vec_Wrd_t * vValues = NULL, * vExpected = NULL;
    Vec_Int_t * vFormal[2] = {NULL, NULL}, * vColors = NULL, * vRoots = NULL, * vReference = NULL, * vAnchors = NULL, * v;
    Acec2_Man_t * a = NULL;
    Gia_Man_t * g = NULL;
    ABC_INT64_T nMaxObjs;
    word state = ABC_CONST(0x19C69D74E8237A5B);
    int side, i, lit, mode, round, anchor, top, result, changed, merged = 0, cancelled = 0, nRounds, strategy;
    if ( pPrefix ) *pPrefix = 0;
    if ( !pNew || !m || !m[0] || !m[1] || !pPars || !pnWords || !vMaps || !vReplaces ||
         !vOps || !vOps[0] || !vOps[1] || !Vec_IntSize(&pNew->vHTable) ||
         Width < 1 || Width > pPars->nMaxWidth || Width > 512 ) return 0;
    for ( side = 0; side < 2; side++ )
    {
        if ( !m[side]->pGia || !vMaps[side] || !vReplaces[side] ||
             Vec_IntSize(vMaps[side]) != Gia_ManObjNum(m[side]->pGia) ||
             Vec_IntSize(vReplaces[side]) != Gia_ManObjNum(m[side]->pGia) ) return 0;
        Vec_IntForEachEntry(vMaps[side], lit, i)
            if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(pNew) ) return 0;
        Vec_IntForEachEntry(vReplaces[side], lit, i)
            if ( lit < -1 || (lit >= 0 && (lit >> 1) >= Gia_ManObjNum(pNew)) ) return 0;
        if ( !Vec_IntSize(vOps[side]) || Vec_IntSize(vOps[side]) > 256 ) return 0;
        Vec_IntForEachEntry(vOps[side], lit, i) if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(pNew) ) return 0;
    }
    LocalPars = *pPars;
    if ( !LocalPars.pCancelled ) LocalPars.pCancelled = &cancelled;
    pPars = &LocalPars;
    if ( Acec2_Stop(pPars, Deadline) ) return 0;
    nMaxObjs = 8*((ABC_INT64_T)Vec_IntSize(vMaps[0])+Vec_IntSize(vMaps[1]))+1000;
    hCuts = Hsh_Int1ManStart(100); vColors = Vec_IntStart(Gia_ManObjNum(pNew));
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntForEachEntry(vMaps[side], lit, i) Vec_IntWriteEntry(vColors, lit >> 1, Vec_IntEntry(vColors, lit >> 1) | (1 << side));
        // Certificates can share a reference before the next full source
        // rebuild. Treat those already proved replacements as common too,
        // avoiding another proof of the same bits under a smaller operand
        // proposal. Unproved simulation candidates never enter this map.
        Vec_IntForEachEntry(vReplaces[side], lit, i)
            if ( lit >= 0 ) Vec_IntWriteEntry(vColors, lit >> 1, Vec_IntEntry(vColors, lit >> 1) | (1 << side));
        Vec_IntForEachEntry(vOps[side], lit, i) Acec2_IndexAdd(hCuts, lit >> 1);
    }
    for ( side = 0; side < 2; side++ )
    {
        vFormal[side] = Vec_IntAlloc(Vec_IntSize(vOps[side]));
        Vec_IntForEachEntry(vOps[side], lit, i)
            Vec_IntPush(vFormal[side], lit < 2 ? lit : Abc_Var2Lit(Acec2_IndexLookup(hCuts, lit >> 1)+1, lit & 1));
        s[side] = Acec2_WordSimCached(m[side], vMaps[side], hCuts, Width);
        Acec2_WordPrioritize(s[side], m[side]); vSiblings[side] = Acec2_CertSiblings(m[side]);
        vDone[side] = Vec_BitStart(Gia_ManObjNum(m[side]->pGia));
    }
    vValues = Vec_WrdStart(Hsh_Int1ManEntryNum(hCuts)); vExpected = Vec_WrdStart(4*Width);
    nRounds = (256+25+10*(Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1]))+63)/64;
    for ( round = 0; round < nRounds; round++ )
    {
        if ( Acec2_Stop(pPars, Deadline) ) goto finish;
        Acec2_OperandPatterns(vOps, hCuts, vValues, round, &state);
        Acec2_ProductPatterns(vOps, hCuts, vValues, vExpected, Width);
        for ( side = 0; side < 2; side++ ) Acec2_WordSimulate(s[side], vValues, vExpected, round);
    }
    for ( mode = 0; mode < 4 && !Acec2_Stop(pPars, Deadline); mode++ )
    {
        for ( side = 0; side < 2; side++ )
        {
            top = Width-1;
            while ( top >= 0 && !Vec_IntSize(Vec_WecEntry(s[side]->vCandidates, mode*Width+top)) ) top--;
            if ( top < 3 ) continue;
            v = Vec_WecEntry(s[side]->vCandidates, mode*Width+top); vAnchors = Vec_IntDup(v);
            for ( anchor = 0; anchor < Vec_IntSize(vAnchors) && anchor < 16 && !Acec2_Stop(pPars, Deadline); anchor++ )
            {
                Vec_IntClear(v); Vec_IntPush(v, Vec_IntEntry(vAnchors, anchor));
                for ( strategy = ACEC2_ROOT_CARRY; strategy <= ACEC2_ROOT_BOUNDARY && !Acec2_Stop(pPars, Deadline); strategy++ )
                {
                    result = -1;
                    g = Acec2_CertExtract(s[side], vSiblings[side], vOps, hCuts, mode, Width, top+1, (Acec2_RootMode_t)strategy, &vRoots);
                    if ( !g || !vRoots || !Acec2_CertUseful(vRoots, vMaps[side], vReplaces[side], vColors, vReference, vDone[side]) ) goto next_anchor;
                    result = Acec2_CertCheck(m[side], g, vRoots, vFormal, mode, top+1,
                        Acec2_CertTermLimit(vFormal), pPars, Deadline, 1, &a);
                    if ( result == 1 && !Acec2_Stop(pPars, Deadline) && (ABC_INT64_T)Gia_ManObjNum(pNew) <= nMaxObjs )
                    {
                        if ( pPrefix ) *pPrefix = Abc_MaxInt(*pPrefix, top+1);
                        if ( !vReference ) vReference = Acec2_ProductBits(pNew, vOps, mode, Width);
                        changed = Acec2_CertCommit(vRoots, vReference, vMaps[side], vReplaces[side], vDone[side]);
                        if ( changed )
                        {
                            Acec2_Word_t * word = Acec2_CertSourceWord(m[side], s[side], vRoots, vFormal, mode,
                                Hsh_Int1ManEntryNum(hCuts), pPars, Deadline);
                            if ( word ) m[side]->nCertificateRecords += Acec2_RecordAddProductWord(m[side], word, -1);
                            else if ( !Acec2_Stop(pPars, Deadline) ) m[side]->nCertificateContext++;
                        }
                        merged += changed;
                        if ( changed ) (*pnWords)++;
                        if ( changed && pPars->fVerbose )
                            Abc_Print(1, "Certified product word: side = %d, mode = %d, bits = %d, new aliases = %d.\n", side, mode, top+1, changed);
                    }
next_anchor:
                    Acec2_Free(a); a = NULL; if ( g ) Gia_ManStop(g); g = NULL; Vec_IntFreeP(&vRoots);
                    if ( result == 1 ) break;
                }
            }
            Vec_IntClear(v); Vec_IntAppend(v, vAnchors); Vec_IntFreeP(&vAnchors);
        }
        Vec_IntFreeP(&vReference);
    }
finish:
    Acec2_Free(a);
    if ( g ) Gia_ManStop(g);
    Vec_IntFreeP(&vRoots); Vec_IntFreeP(&vReference); Vec_IntFreeP(&vAnchors); Vec_IntFreeP(&vColors);
    for ( side = 0; side < 2; side++ )
    {
        Acec2_WordSimStop(s[side]); Vec_IntFreeP(&vFormal[side]);
        if ( vDone[side] ) Vec_BitFree(vDone[side]);
    }
    Vec_WrdFreeP(&vValues); Vec_WrdFreeP(&vExpected);
    if ( hCuts ) Hsh_Int1ManStop(hCuts);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Certifies an observed product word within one immutable design.]

  Description [Operand cuts are discovered independently of any second
  circuit. Simulation locates contiguous result bits, and exact polynomial
  comparison certifies their original cones over free cut variables. Only
  observed, completely proved bits enter the persistent analysis database.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Word_t * Acec2_CertifyProductWord( Acec2_Man_t * m, Acec2_Product_t * product, int Prefix )
{
    Acec2_Word_t * w = NULL;
    Acec2_WordSim_t * sim = NULL; Acec2_Man_t * extracted = NULL;
    Hsh_Int1Man_t * cuts = NULL; Vec_Wec_t * siblings = NULL;
    Vec_Int_t * map = NULL, * formal[2] = {NULL, NULL}, * roots = NULL, * anchors = NULL, * top = NULL;
    Vec_Wrd_t * values = NULL, * expected = NULL;
    Gia_Man_t * g = NULL;
    word state = ABC_CONST(0x719F3C52D64A8BE0);
    int side, i, lit, width, mode, round, nRounds, prefix, result = -1, limit, pass, expanded, anchor, strategy;
    if ( !m->Pars.fAlgebra || product->fNeg || Acec2_Stopped(m) ) return NULL;
    for ( side = 0; side < 2; side++ )
        if ( Vec_IntSize(product->vOperands[side]) < 2 || Vec_IntSize(product->vOperands[side]) > 256 ) return NULL;
    width = Abc_MinInt(m->Pars.nMaxWidth, Vec_IntSize(product->vOperands[0])+Vec_IntSize(product->vOperands[1]));
    if ( width <= Prefix || width > 512 ) return NULL;
    mode = product->fSigned[0]+2*product->fSigned[1]; m->nProductAttempts++;
    cuts = Hsh_Int1ManStart(100); map = Vec_IntStart(Gia_ManObjNum(m->pGia));
    for ( i = 0; i < Vec_IntSize(map); i++ ) Vec_IntWriteEntry(map, i, 2*i);
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(product->vOperands[side], lit, i)
            if ( lit >= 2 ) Acec2_IndexAdd(cuts, lit >> 1);
    if ( !Hsh_Int1ManEntryNum(cuts) ) goto finish;
    for ( side = 0; side < 2; side++ )
    {
        formal[side] = Vec_IntAlloc(Vec_IntSize(product->vOperands[side]));
        Vec_IntForEachEntry(product->vOperands[side], lit, i)
            Vec_IntPush(formal[side], lit < 2 ? lit : 2*(Acec2_IndexLookup(cuts, lit >> 1)+1)+(lit & 1));
    }
    sim = Acec2_WordSimCached(m, map, cuts, width); Acec2_WordPrioritize(sim, m);
    values = Vec_WrdStart(Hsh_Int1ManEntryNum(cuts)); expected = Vec_WrdStart(4*width);
    nRounds = (281+10*(Vec_IntSize(formal[0])+Vec_IntSize(formal[1]))+63)/64;
    for ( round = 0; round < nRounds && !Acec2_Stopped(m); round++ )
    {
        Acec2_OperandPatterns(product->vOperands, cuts, values, round, &state);
        Acec2_ProductPatterns(product->vOperands, cuts, values, expected, width);
        Acec2_WordSimulate(sim, values, expected, round);
    }
    if ( Acec2_Stopped(m) ) goto finish;
    for ( prefix = 0; prefix < width; prefix++ )
        if ( !Vec_IntSize(Vec_WecEntry(sim->vCandidates, mode*width+prefix)) ) break;
    if ( prefix <= Prefix || prefix < 4 ) goto finish;
    siblings = Acec2_CertSiblings(m);
    top = Vec_WecEntry(sim->vCandidates, mode*width+prefix-1); anchors = Vec_IntDup(top);
    // Equivalent high bits can expose very different carry dependencies.
    // Retain a few observed anchors rather than committing to the smallest
    // cone before the arithmetic proof has succeeded.
    for ( anchor = 0; anchor < 1+Abc_MinInt(3, Vec_IntSize(anchors)) && !Acec2_Stopped(m); anchor++ )
    {
        if ( anchor ) { Vec_IntClear(top); Vec_IntPush(top, Vec_IntEntry(anchors, Vec_IntSize(anchors)-anchor)); }
        for ( strategy = ACEC2_ROOT_BOUNDARY; strategy >= ACEC2_ROOT_CARRY && !Acec2_Stopped(m); strategy-- )
        {
            result = -1;
            g = Acec2_CertExtract(sim, siblings, product->vOperands, cuts, mode, width, prefix, (Acec2_RootMode_t)strategy, &roots);
            if ( !g || !roots || Vec_IntSize(roots) != prefix ) goto next_word_anchor;
            Vec_IntForEachEntry(roots, lit, i) if ( lit < 0 ) break;
            if ( i < Vec_IntSize(roots) ) goto next_word_anchor;
            limit = Acec2_CertTermLimit(formal);
            // A complete observed word permits a larger deterministic cancellation
            // workspace. Keep the inexpensive first attempt for ordinary products.
            expanded = Abc_MaxInt(limit, Abc_MinInt(500000, 1024*Vec_IntSize(formal[0])*Vec_IntSize(formal[1])+1024));
            for ( pass = 0; pass < 1+(expanded > limit) && !Acec2_Stopped(m); pass++ )
            {
                if ( pass ) limit = expanded;
                result = Acec2_CertCheck(m, g, roots, formal, mode, prefix, limit,
                    &m->Pars, m->Deadline, 0, &extracted);
                if ( result >= 0 ) break;
            }
            if ( result == 1 ) break;
next_word_anchor:
            Acec2_Free(extracted); extracted = NULL;
            if ( g ) Gia_ManStop(g);
            g = NULL; Vec_IntFreeP(&roots);
        }
        if ( result == 1 ) break;
    }
    Vec_IntClear(top); Vec_IntAppend(top, anchors);
    if ( result != 1 || Acec2_Stopped(m) ) goto finish;
    w = ABC_CALLOC(Acec2_Word_t, 1); w->Tree = w->Record = -1; w->Width = prefix;
    w->vTerms = Vec_IntAlloc(0); w->vConstants = Vec_IntAlloc(0); w->vBits = roots; roots = NULL;
    w->pProduct = ABC_CALLOC(Acec2_Product_t, 1);
    for ( side = 0; side < 2; side++ )
    {
        w->pProduct->vOperands[side] = Vec_IntDup(product->vOperands[side]);
        if ( Vec_IntSize(w->pProduct->vOperands[side]) > prefix ) Vec_IntShrink(w->pProduct->vOperands[side], prefix);
        w->pProduct->fSigned[side] = product->fSigned[side] && Vec_IntSize(product->vOperands[side]) <= prefix;
    }
finish:
    Acec2_Free(extracted); if ( g ) Gia_ManStop(g); Acec2_WordSimStop(sim);
    if ( cuts ) Hsh_Int1ManStop(cuts);
    Vec_IntFreeP(&map); Vec_IntFreeP(&roots); Vec_IntFreeP(&anchors); Vec_IntFreeP(&formal[0]); Vec_IntFreeP(&formal[1]);
    Vec_WrdFreeP(&values); Vec_WrdFreeP(&expected);
    return w;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
