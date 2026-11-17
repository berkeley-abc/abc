/**CFile****************************************************************

  FileName    [acec2Masked.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Checked arithmetic words with explicit source XOR masks.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 14, 2026.]

  Revision    [$Id$]

  Description [Shared leaves of several parity networks propose decoding
  masks. A private gate copy exposes these expressions to the same arithmetic
  detector and record checker. Only completed identities are transferred;
  the original GIA is never modified and inferred operand names are unused.]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Orders shared boundary leaves as possible XOR masks.]

  Description [Counts distinct parity networks, not occurrences within a
  network. The proposal count is bounded independently of proof outcomes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_MaskedCandidates( Acec2_Man_t * m )
{
    Vec_Int_t * counts, * leaves; Vec_Wrd_t * order;
    Gia_Obj_t * o; int i, j, id, first = -1, mixed = 0, n = Gia_ManObjNum(m->pGia); word key;
    if ( m->vMaskCandidates ) return;
    m->vMaskCandidates = Vec_IntAlloc(16); counts = Vec_IntStart(n); order = Vec_WrdAlloc(32);
    Vec_WecForEachLevel(m->vXorLeaves, leaves, i)
        Vec_IntForEachEntry(leaves, id, j) if ( id ) Vec_IntAddToEntry(counts, id, 1);
    Vec_IntForEachEntry(counts, j, id)
        if ( j >= 3 && Vec_IntEntry(m->vRefs, id) >= 3 )
            Vec_WrdPush(order, ((word)(unsigned)j << 32) | (0xFFFFFFFFu-(unsigned)id));
    if ( Vec_WrdSize(order) > 1 ) Vec_WrdSort(order, 1);
    Vec_WrdForEachEntry(order, key, i)
    {
        if ( i == 16 ) { m->nMaskLimits++; break; }
        Vec_IntPush(m->vMaskCandidates, (int)(0xFFFFFFFFu-(unsigned)key));
    }
    // A word may use different control leaves for different bits. Queue
    // this proposal only when its observed output parities need more than
    // one of the individually ranked candidates.
    if ( Gia_ManCoNum(m->pGia) <= 512 ) Gia_ManForEachCo(m->pGia, o, i)
    {
        if ( Vec_IntEntry(m->vXorBest, Gia_ObjFaninId0p(m->pGia, o)) < 0 ) continue;
        Vec_IntForEachEntry(m->vMaskCandidates, id, j)
            if ( Acec2_ParityHasLeaf(m, Gia_ObjFaninLit0p(m->pGia, o), id) ) break;
        if ( j == Vec_IntSize(m->vMaskCandidates) ) continue;
        if ( first < 0 ) first = id; else mixed |= first != id;
    }
    if ( mixed ) Vec_IntPushFirst(m->vMaskCandidates, -1);
    Vec_IntFree(counts); Vec_WrdFree(order);
}

/**Function*************************************************************

  Synopsis    [Drops unused copied logic while retaining source expressions.]

  Description [The private copy contains plain ANDs. A reverse topological
  mark avoids recursion and leaves the original analysis entirely untouched.]

  SideEffects [Consumes the supplied private copy and mapping vectors.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_MaskedClean( Gia_Man_t * g, Vec_Int_t ** pBack, Vec_Int_t ** pMasks )
{
    Gia_Man_t * q = Gia_ManStart(Gia_ManObjNum(g)); Gia_Obj_t * o;
    Vec_Bit_t * live = Vec_BitStart(Gia_ManObjNum(g)); Vec_Int_t * map = Vec_IntStart(Gia_ManObjNum(g));
    Vec_Int_t * back = Vec_IntStart(1), * masks = Vec_IntStart(1); int i, lit;
    Gia_ManForEachCo(g, o, i) Acec2_BitWrite(live, Gia_ObjFaninId0p(g, o), 1);
    for ( i = Gia_ManObjNum(g)-1; i > 0; i-- )
    {
        o = Gia_ManObj(g, i);
        if ( !Vec_BitEntry(live, i) || !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(live, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(live, Gia_ObjFaninId1(o, i), 1);
    }
    Gia_ManForEachObj1(g, o, i)
    {
        if ( Gia_ObjIsCo(o) || (!Gia_ObjIsCi(o) && !Vec_BitEntry(live, i)) ) continue;
        lit = Gia_ObjIsCi(o) ? Gia_ManAppendCi(q) : Gia_ManAppendAnd(q,
            Vec_IntEntry(map, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
            Vec_IntEntry(map, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o));
        Vec_IntWriteEntry(map, i, lit); Vec_IntPush(back, Vec_IntEntry(*pBack, i)); Vec_IntPush(masks, Vec_IntEntry(*pMasks, i));
    }
    Gia_ManForEachCo(g, o, i) Gia_ManAppendCo(q, Vec_IntEntry(map, Gia_ObjFaninId0p(g, o)) ^ Gia_ObjFaninC0(o));
    Vec_IntFillExtra(back, Gia_ManObjNum(q), -1); Vec_IntFillExtra(masks, Gia_ManObjNum(q), 0);
    Vec_IntFree(*pBack); Vec_IntFree(*pMasks); *pBack = back; *pMasks = masks;
    Vec_BitFree(live); Vec_IntFree(map); Gia_ManStop(g); return q;
}

/**Function*************************************************************

  Synopsis    [Copies source gates and appends explicitly decoded parity sinks.]

  Description [Back-mapping entries describe the exact source expression
  of copied and decoded roots. Intermediate decoder gates are unmapped and
  cannot be imported as source boundaries. Hashing performs only ordinary
  Boolean construction; it supplies no arithmetic proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_MaskedCopy( Acec2_Man_t * m, int Mask, Vec_Bit_t * live,
                                   Vec_Int_t ** pBack, Vec_Int_t ** pMasks )
{
    Gia_Man_t * g = m->pGia, * copy = NULL;
    Gia_Obj_t * o; Vec_Int_t * selected = Vec_IntAlloc(32), * ordered = Vec_IntAlloc(32), * map = NULL, * sinks, * leaves;
    Vec_Int_t * back = NULL, * masks = NULL, * decoders = Vec_IntStartFull(Gia_ManObjNum(g));
    int i, j, k, id, lit, decoded, chosen, n = Gia_ManObjNum(g);
    Vec_WecForEachLevel(m->vXorLeaves, leaves, i)
    {
        if ( Mask >= 0 && Vec_IntFind(leaves, Mask) < 0 ) continue;
        sinks = Vec_WecEntry(m->vXorSinks, i);
        Vec_IntForEachEntry(sinks, id, j)
            if ( !live || Vec_BitEntry(live, id) )
            {
                chosen = Mask;
                if ( Mask < 0 && m->vMaskCandidates )
                    Vec_IntForEachEntry(m->vMaskCandidates, chosen, k)
                        if ( chosen >= 0 && Acec2_ParityHasLeaf(m, 2*id, chosen) ) break;
                if ( chosen < 0 || !Acec2_ParityHasLeaf(m, 2*id, chosen) ) continue;
                Vec_IntPushUnique(selected, id); Vec_IntWriteEntry(decoders, id, chosen);
            }
    }
    if ( Vec_IntSize(selected) < 3 ) goto finish;
    if ( n > 50000 || Vec_IntSize(selected) > 512 ) { m->nMaskLimits++; goto finish; }
    Gia_ManForEachCo(g, o, i)
    {
        id = Gia_ObjFaninId0p(g, o); j = Vec_IntFind(selected, id);
        if ( j < 0 ) continue;
        Vec_IntPush(ordered, Gia_ObjFaninLit0p(g, o)); Vec_IntWriteEntry(selected, j, -1);
    }
    Vec_IntForEachEntry(selected, id, i) if ( id >= 0 ) Vec_IntPush(ordered, 2*id);
    copy = Gia_ManStart(n+8*Vec_IntSize(selected)); Gia_ManHashAlloc(copy);
    map = Vec_IntStartFull(n); Vec_IntWriteEntry(map, 0, 0);
    back = Vec_IntStart(1); masks = Vec_IntStart(1);
    Gia_ManForEachObj1(g, o, id)
    {
        if ( !(id & 255) && Acec2_Stopped(m) ) goto fail;
        if ( Gia_ObjIsCo(o) ) continue;
        if ( Gia_ObjIsCi(o) ) lit = Gia_ManAppendCi(copy);
        else if ( Gia_ObjIsBuf(o) ) lit = Vec_IntEntry(map, Gia_ObjFaninId0(o, id)) ^ Gia_ObjFaninC0(o);
        else lit = Acec2_CopyGate(g, copy, map, id);
        Vec_IntWriteEntry(map, id, lit);
        Vec_IntFillExtra(back, Gia_ManObjNum(copy), -1); Vec_IntFillExtra(masks, Gia_ManObjNum(copy), 0);
        if ( Vec_IntEntry(back, lit >> 1) < 0 ) Vec_IntWriteEntry(back, lit >> 1, 2*id ^ (lit & 1));
    }
    Vec_IntForEachEntry(ordered, lit, i)
    {
        chosen = Vec_IntEntry(decoders, lit >> 1);
        decoded = Acec2_ParityBuild(m, copy, map, lit, 2*chosen);
        if ( decoded < 0 ) goto fail;
        Vec_IntFillExtra(back, Gia_ManObjNum(copy), -1); Vec_IntFillExtra(masks, Gia_ManObjNum(copy), 0);
        if ( Vec_IntEntry(back, decoded >> 1) < 0 )
        {
            Vec_IntWriteEntry(back, decoded >> 1, lit ^ (decoded & 1));
            Vec_IntWriteEntry(masks, decoded >> 1, 2*chosen);
        }
        Gia_ManAppendCo(copy, decoded);
    }
    Vec_IntFillExtra(back, Gia_ManObjNum(copy), -1); Vec_IntFillExtra(masks, Gia_ManObjNum(copy), 0);
    Gia_ManHashStop(copy); copy = Acec2_MaskedClean(copy, &back, &masks);
    *pBack = back; *pMasks = masks; back = masks = NULL;
    goto finish;
fail:
    Gia_ManStop(copy); copy = NULL;
finish:
    Vec_IntFree(selected); Vec_IntFree(ordered); Vec_IntFree(decoders); Vec_IntFreeP(&map); Vec_IntFreeP(&back); Vec_IntFreeP(&masks); return copy;
}

/**Function*************************************************************

  Synopsis    [Simulates one packed batch in a private decoded AIG.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_MaskedSimulate( Gia_Man_t * g, Vec_Wrd_t * values )
{
    Gia_Obj_t * o; int id;
    Gia_ManForEachAnd(g, o, id)
    {
        Vec_WrdWriteEntry(values, id, Acec2_SimGate(g, id, values, 1, 0));
    }
}

/**Function*************************************************************

  Synopsis    [Proposes an affine word from one-hot observations, then proves it.]

  Description [Output order is only a proposal. Each coefficient is the
  observed change caused by one source input. Random batches reject wrong
  proposals cheaply; only ordinary exact CEC can create the source record.
  Thus nonlinear logic or an incorrect order cannot become an arithmetic
  identity through simulation agreement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_MaskedLinear( Acec2_Man_t * m )
{
    Gia_Man_t * g = m->pGia; Gia_Obj_t * o;
    Vec_Wrd_t * values = NULL, * samples = NULL, * bits = NULL;
    Vec_Int_t * terms = NULL, * constants = NULL, * outputs = NULL;
    int ni = Gia_ManCiNum(g), width = Gia_ManCoNum(g), limbs = (width+63)/64;
    int batch, i, j, k, pattern, id, rank, lit, result = -1;
    word value, carry, old, sub, borrow, state = ABC_CONST(0xB912CD37A6015E4F);
    if ( ni > 512 || width < 3 || width > 512 || width > m->Pars.nMaxWidth ) return -1;
    values = Vec_WrdStart(Gia_ManObjNum(g)); samples = Vec_WrdStart((ni+1)*limbs);
    bits = Vec_WrdStart(width); terms = Vec_IntAlloc(100); constants = Vec_IntAlloc(32); outputs = Vec_IntAlloc(2*width);
    for ( batch = 0; batch*64 <= ni && !Acec2_Stopped(m); batch++ )
    {
        Gia_ManForEachCi(g, o, i)
        { pattern = i+1-64*batch; Vec_WrdWriteEntry(values, Gia_ObjId(g, o), pattern >= 0 && pattern < 64 ? (word)1 << pattern : 0); }
        Acec2_MaskedSimulate(g, values);
        Gia_ManForEachCo(g, o, rank)
        {
            value = Vec_WrdEntry(values, Gia_ObjFaninId0p(g, o)); if ( Gia_ObjFaninC0(o) ) value = ~value;
            for ( k = 0; k < 64 && 64*batch+k <= ni; k++ )
                if ( (value >> k) & 1 )
                { id = (64*batch+k)*limbs+rank/64; Vec_WrdWriteEntry(samples, id, Vec_WrdEntry(samples, id) | ((word)1 << (rank & 63))); }
        }
    }
    if ( Acec2_Stopped(m) ) goto finish;
    for ( rank = 0; rank < width; rank++ )
        if ( (Vec_WrdEntry(samples, rank/64) >> (rank & 63)) & 1 ) Vec_IntPush(constants, rank);
    Gia_ManForEachCi(g, o, i)
    {
        borrow = 0;
        for ( j = 0; j < limbs; j++ )
        {
            id = (i+1)*limbs+j; old = Vec_WrdEntry(samples, id); sub = Vec_WrdEntry(samples, j);
            value = old-sub; carry = old < sub; old = value; value -= borrow; borrow = carry | (old < borrow);
            Vec_WrdWriteEntry(samples, id, value);
        }
        for ( rank = 0; rank < width; rank++ )
            if ( (Vec_WrdEntry(samples, (i+1)*limbs+rank/64) >> (rank & 63)) & 1 )
                Vec_IntPushTwo(terms, 2*Gia_ObjId(g, o), rank);
        if ( Vec_IntSize(terms) > 2048 ) goto finish;
    }
    for ( batch = 0; batch < 2 && !Acec2_Stopped(m); batch++ )
    {
        Gia_ManForEachCi(g, o, i) Vec_WrdWriteEntry(values, Gia_ObjId(g, o), Acec2_Random(&state));
        Acec2_MaskedSimulate(g, values); Vec_WrdFill(bits, width, 0);
        Vec_IntForEachEntry(constants, rank, i) Vec_WrdWriteEntry(bits, rank, ~(word)0);
        for ( i = 0; i < Vec_IntSize(terms); i += 2 )
        {
            lit = Vec_IntEntry(terms, i); carry = Vec_WrdEntry(values, lit >> 1);
            for ( rank = Vec_IntEntry(terms, i+1); rank < width && carry; rank++ )
            { old = Vec_WrdEntry(bits, rank); Vec_WrdWriteEntry(bits, rank, old ^ carry); carry &= old; }
        }
        Gia_ManForEachCo(g, o, rank)
        {
            value = Vec_WrdEntry(values, Gia_ObjFaninId0p(g, o)); if ( Gia_ObjFaninC0(o) ) value = ~value;
            if ( value != Vec_WrdEntry(bits, rank) ) goto finish;
        }
    }
    Gia_ManForEachCo(g, o, rank) Vec_IntPushTwo(outputs, Gia_ObjFaninLit0p(g, o), rank);
    result = Acec2_RecordWeighted(m, outputs, terms, constants, width);
finish:
    Vec_WrdFreeP(&values); Vec_WrdFreeP(&samples); Vec_WrdFreeP(&bits);
    Vec_IntFreeP(&terms); Vec_IntFreeP(&constants); Vec_IntFreeP(&outputs); return result;
}

/**Function*************************************************************

  Synopsis    [Requests bounded mask decoding through the common detector.]

  Description [Profiling and CEC use the same queue. A completed attempt
  consumes one work unit. Deadline or cancellation never records a completed
  attempt. Derived analyses do not recursively request mask decoding.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_EnrichMasked( Acec2_Man_t * m, Vec_Bit_t * live, int * pnQueries )
{
    Acec2_Par_t pars; Acec2_Man_t * child; Gia_Man_t * g;
    Vec_Int_t * back = NULL, * masks = NULL;
    Acec2_Record_t * r; int i, added = 0, before;
    if ( !pnQueries || *pnQueries < 1 || Acec2_Stopped(m) ) return 0;
    Acec2_MaskedCandidates(m);
    while ( m->iMaskCandidate < Vec_IntSize(m->vMaskCandidates) && *pnQueries && !Acec2_Stopped(m) )
    {
        g = Acec2_MaskedCopy(m, Vec_IntEntry(m->vMaskCandidates, m->iMaskCandidate), live, &back, &masks);
        if ( !g ) { if ( !Acec2_Stopped(m) ) m->iMaskCandidate++; continue; }
        (*pnQueries)--; m->nMaskAttempts++; pars = m->Pars;
        pars.fVerbose = 0; pars.nAnalysisLevel = Abc_MaxInt(1, m->Pars.nAnalysisLevel); pars.nCecOptions = ACEC2_CEC_DEFER;
        child = Acec2_AnalyzeCells(g, &pars, m->Deadline); before = added;
        if ( child && !child->fStopped )
        {
            if ( Acec2_MaskedLinear(child) < 0 && !Acec2_Stopped(m) )
            {
                // A failed affine proposal may still contain a product or a
                // compressor tree. Reuse the full source detector, including
                // functional carries and counters, without recursive masks.
                Acec2_Free(child); pars.nCecOptions = 0;
                child = Acec2_AnalyzeSourceCells(g, &pars, m->Deadline);
                if ( child && !child->fStopped )
                { Acec2_CloseWords(child); if ( pars.nAnalysisLevel >= 2 ) Acec2_FindExpressions(child); Acec2_BuildRecords(child); }
            }
        }
        if ( child && !child->fStopped )
        {
            Vec_PtrForEachEntry(Acec2_Record_t *, child->vRecords, r, i)
                if ( !Acec2_Stopped(m) ) added += Acec2_RecordImportMasked(m, child, r, back, masks);
        }
        if ( child && !child->fStopped && !Acec2_Stopped(m) ) m->iMaskCandidate++;
        else if ( !Acec2_Stopped(m) ) { m->nMaskLimits++; m->iMaskCandidate++; }
        if ( m->Pars.fVerbose ) Abc_Print(1, "Decoded parity word: mask candidate %d, new source records = %d.\n", m->iMaskCandidate, added-before);
        Acec2_Free(child); Gia_ManStop(g); Vec_IntFree(back); Vec_IntFree(masks); back = masks = NULL;
    }
    m->nMaskRecords += added; return added;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
