/**CFile****************************************************************

  FileName    [acec2Word.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Simulates and extracts arithmetic words over independent cuts.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 13, 2026.]

  Revision    [$Id$]

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

  Synopsis    [Looks up an exact key in a private integer index.]

  Description [Traverse the collision chain and return the matching entry,
  never the bucket head. Allocation uses the common hash container.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_IndexLookup( Hsh_Int1Man_t * h, int Key )
{
    int i = Vec_IntEntry(h->vTable, Hsh_Int1ManHash(Key, Vec_IntSize(h->vTable)));
    for ( ; i >= 0; i = Vec_IntEntry(h->vNext, i) )
        if ( Vec_IntEntry(h->vData, i) == Key ) return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Inserts an exact key, retaining all colliding entries.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_IndexAdd( Hsh_Int1Man_t * h, int Key )
{
    int i = Acec2_IndexLookup(h, Key), slot, value;
    if ( i >= 0 ) return i;
    if ( Vec_IntSize(h->vData) > Vec_IntSize(h->vTable) )
    {
        Vec_IntFill(h->vTable, Abc_PrimeCudd(2*Vec_IntSize(h->vTable)), -1);
        Vec_IntForEachEntry(h->vData, value, i)
        {
            slot = Hsh_Int1ManHash(value, Vec_IntSize(h->vTable));
            Vec_IntWriteEntry(h->vNext, i, Vec_IntEntry(h->vTable, slot)); Vec_IntWriteEntry(h->vTable, slot, i);
        }
    }
    i = Vec_IntSize(h->vData); slot = Hsh_Int1ManHash(Key, Vec_IntSize(h->vTable));
    Vec_IntPush(h->vData, Key); Vec_IntPush(h->vNext, Vec_IntEntry(h->vTable, slot)); Vec_IntWriteEntry(h->vTable, slot, i);
    return i;
}

/**Function*************************************************************

  Synopsis    [Adds carry-generate and carry-propagate simulation patterns.]

  Description [One true term per column propagates an incoming carry;
  a second term in a selected column generates it. Both term orders are
  exercised. Repeated or complemented cut signals must receive consistent
  assignments. These patterns only filter candidates; proofs remain exact.
  The uniform patterns and at least half the random patterns are retained.]

  SideEffects [Updates at most thirty packed assignments.]

  SeeAlso     []

***********************************************************************/
int Acec2_WordCarryPatterns( Acec2_Word_t * w, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, int Round )
{
    Vec_Wec_t * cols;
    Vec_Int_t * assignments, * col;
    int i, rank, lit, bit, seed, count, value, index, old, good, added = 0;
    word mask, values;
    if ( w->fPolynomial || w->vSourceCut || w->Width < 2 || w->Width > 512 || Round < 0 || Round > 3 ||
         Vec_WrdSize(vValues) != Hsh_Int1ManEntryNum(hCuts) || (Vec_IntSize(w->vTerms) & 1) || Vec_IntSize(w->vTerms) > 4096 ) return 0;
    cols = Vec_WecStart(w->Width); assignments = Vec_IntStartFull(Vec_WrdSize(vValues));
    for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 )
    {
        rank = Vec_IntEntry(w->vTerms, i+1);
        if ( rank >= 0 && rank < w->Width ) Vec_WecPush(cols, rank, Vec_IntEntry(w->vTerms, i));
    }
    for ( bit = 2; bit < 32; bit++ )
    {
        seed = (30*(Round/2)+bit-2) % w->Width-1; good = 1;
        Vec_IntFill(assignments, Vec_IntSize(assignments), -1);
        Vec_WecForEachLevel(cols, col, rank)
        {
            count = Abc_MinInt(Vec_IntSize(col), rank < seed ? 0 : rank == seed ? 2 : 1);
            Vec_IntForEachEntry(col, lit, i)
            {
                value = (Round & 1) ? i >= Vec_IntSize(col)-count : i < count;
                value ^= lit & 1;
                if ( lit < 2 ) { if ( value ) good = 0; continue; }
                index = Acec2_IndexLookup(hCuts, lit >> 1);
                if ( index < 0 ) { good = 0; break; }
                old = Vec_IntEntry(assignments, index);
                if ( old >= 0 && old != value ) { good = 0; break; }
                Vec_IntWriteEntry(assignments, index, value);
            }
            if ( !good ) break;
        }
        if ( !good ) continue;
        mask = (word)1 << bit;
        Vec_IntForEachEntry(assignments, value, i)
            if ( value >= 0 )
            {
                values = Vec_WrdEntry(vValues, i) & ~mask;
                Vec_WrdWriteEntry(vValues, i, values | (value ? mask : 0));
            }
        added++;
    }
    Vec_IntFree(assignments); Vec_WecFree(cols); return added;
}
/**Function*************************************************************

  Synopsis    [Exercises simultaneous operand extremes in product sums.]

  Description [Signed minimum values can distinguish adjacent high sum
  bits only on very rare assignments. Uniform bus extremes and mixed
  extremes supplement random patterns. Repeated and phased literals must
  receive consistent assignments; these patterns never certify an identity.]

  SideEffects [Updates at most thirty packed assignments.]

  SeeAlso     []

***********************************************************************/
int Acec2_WordOperandPatterns( Acec2_Man_t * m, Acec2_Word_t * w, Hsh_Int1Man_t * h, Vec_Wrd_t * values, int Round )
{
    Vec_Int_t * assignment;
    Acec2_Record_t * r; Acec2_Product_t * product;
    int bit, pattern, i, j, side, id, code, port, lit, value, index, old, good, added = 0;
    word mask;
    if ( !w->vSourceCut || !w->vSumProducts || Vec_IntSize(w->vSumProducts) % 3 ||
         Round < 0 || Round > 3 || Vec_WrdSize(values) != Hsh_Int1ManEntryNum(h) ) return 0;
    assignment = Vec_IntStartFull(Vec_WrdSize(values));
    for ( bit = 2; bit < 32; bit++ )
    {
        pattern = 30*Round+bit-2; good = 1; port = 0;
        Vec_IntFill(assignment, Vec_IntSize(assignment), -1);
        for ( i = 0; i < Vec_IntSize(w->vSumProducts) && good; i += 3 )
        {
            id = Vec_IntEntry(w->vSumProducts, i);
            if ( id < 0 || id >= Vec_PtrSize(m->vRecords) ) { good = 0; break; }
            r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, id);
            product = Acec2_RecordProduct(m, r);
            if ( !product ) { good = 0; break; }
            for ( side = 0; side < 2 && good; side++, port++ )
            {
                code = pattern < 4 ? pattern : ((pattern-4) >> (2*(port & 3))) & 3;
                Vec_IntForEachEntry(product->vOperands[side], lit, j)
                {
                    value = code == 0 ? 0 : code == 1 ? 1 : code == 2 ? j == Vec_IntSize(product->vOperands[side])-1 : j < Vec_IntSize(product->vOperands[side])-1;
                    value ^= lit & 1;
                    if ( lit < 2 ) { if ( value ) good = 0; continue; }
                    index = Acec2_IndexLookup(h, lit >> 1);
                    if ( index < 0 ) { good = 0; break; }
                    old = Vec_IntEntry(assignment, index);
                    if ( old >= 0 && old != value ) { good = 0; break; }
                    Vec_IntWriteEntry(assignment, index, value);
                }
            }
        }
        if ( !good ) continue;
        mask = (word)1 << bit;
        Vec_IntForEachEntry(assignment, value, i)
            if ( value >= 0 ) Vec_WrdWriteEntry(values, i, (Vec_WrdEntry(values, i) & ~mask) | (value ? mask : 0));
        added++;
    }
    Vec_IntFree(assignment); return added;
}

/**Function*************************************************************

  Synopsis    [Builds a simulation domain closed over independent operands.]

  Description [Signals depending on any other input are excluded. Output
  bits with fanout outside this domain are preferred over internal carries
  that can agree with them on many random patterns.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_WordSim_t * Acec2_WordSimStart( Gia_Man_t * g, Vec_Int_t * vStop, int Width )
{
    Acec2_WordSim_t * p = ABC_CALLOC(Acec2_WordSim_t, 1);
    Vec_Int_t * vLegal = Vec_IntStart(Gia_ManObjNum(g));
    Gia_Obj_t * o;
    int i, id, a, b, c;
    p->g = g; p->vStop = vStop; p->vEval = Vec_IntAlloc(1000);
    p->vBoundary = Vec_IntStart(Gia_ManObjNum(g)); p->vSim = Vec_WrdStart(Gia_ManObjNum(g));
    p->vCandidates = Vec_WecStart(4*Width); Vec_IntWriteEntry(vLegal, 0, 1);
    Gia_ManForEachObj1(g, o, i)
    {
        if ( Gia_ObjIsCo(o) ) continue;
        if ( Vec_IntEntry(vStop, i) >= 0 )
        { Vec_IntWriteEntry(vLegal, i, 1); continue; }
        if ( !Gia_ObjIsAnd(o) ) continue;
        a = Gia_ObjFaninId0(o, i); b = Gia_ObjFaninId1(o, i); c = Gia_ObjIsMux(g, o) ? Gia_ObjFaninId2(g, i) : 0;
        if ( Vec_IntEntry(vLegal, a) && Vec_IntEntry(vLegal, b) && Vec_IntEntry(vLegal, c) )
        { Vec_IntWriteEntry(vLegal, i, 1); Vec_IntPush(p->vEval, i); }
        else
        { Vec_IntWriteEntry(p->vBoundary, a, 1); Vec_IntWriteEntry(p->vBoundary, b, 1); Vec_IntWriteEntry(p->vBoundary, c, 1); }
    }
    Gia_ManForEachCo(g, o, i)
    { id = Gia_ObjFaninId0p(g, o); Vec_IntWriteEntry(p->vBoundary, id, 33); }
    Vec_IntFree(vLegal);
    return p;
}

/**Function*************************************************************

  Synopsis    [Maps an operand cut to phased independent source variables.]

  Description [The complete stop vector is the cache key. It includes every
  source alias, the independent variable order, and its phase.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_WordStops( Gia_Man_t * g, Vec_Int_t * vMap, Hsh_Int1Man_t * hCuts )
{
    Vec_Int_t * stops = Vec_IntStartFull(Gia_ManObjNum(g));
    Gia_Obj_t * o; int i, lit, cut;
    Gia_ManForEachObj1(g, o, i)
    {
        if ( Gia_ObjIsCo(o) ) continue;
        lit = Vec_IntEntry(vMap, i); cut = Acec2_IndexLookup(hCuts, lit >> 1);
        if ( cut >= 0 ) Vec_IntWriteEntry(stops, i, 2*cut+(lit & 1));
    }
    return stops;
}

/**Function*************************************************************

  Synopsis    [Reuses the inverse source map for successive operand proposals.]

  Description [Exact comparison with a private snapshot detects in-place
  map changes, including phases and constants. Each operand then visits only
  its aliases. Large maps retain the uncached implementation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_WordStopsCached( Acec2_Man_t * m, Vec_Int_t * vMap, Hsh_Int1Man_t * hCuts )
{
    Gia_Obj_t * o;
    Vec_Int_t * stops;
    int i, lit, index, node, cut;
    if ( Gia_ManObjNum(m->pGia) > 2000000 ) return Acec2_WordStops(m->pGia, vMap, hCuts);
    if ( !m->vWordMap || !Vec_IntEqual(m->vWordMap, vMap) )
    {
        if ( m->hWordMap ) Hsh_Int1ManStop(m->hWordMap);
        Vec_IntFreeP(&m->vWordMap); Vec_IntFreeP(&m->vWordHeads); Vec_IntFreeP(&m->vWordNext);
        m->hWordMap = Hsh_Int1ManStart(Abc_MaxInt(100, Gia_ManObjNum(m->pGia)));
        m->vWordMap = Vec_IntDup(vMap); m->vWordHeads = Vec_IntAlloc(Gia_ManObjNum(m->pGia));
        m->vWordNext = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
        Gia_ManForEachObj1(m->pGia, o, i)
        {
            if ( Gia_ObjIsCo(o) ) continue;
            lit = Vec_IntEntry(vMap, i); index = Acec2_IndexAdd(m->hWordMap, lit >> 1);
            if ( index == Vec_IntSize(m->vWordHeads) ) Vec_IntPush(m->vWordHeads, -1);
            Vec_IntWriteEntry(m->vWordNext, i, Vec_IntEntry(m->vWordHeads, index));
            Vec_IntWriteEntry(m->vWordHeads, index, i);
        }
    }
    stops = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
    Vec_IntForEachEntry(hCuts->vData, node, cut)
    {
        index = Acec2_IndexLookup(m->hWordMap, node);
        if ( index < 0 ) continue;
        for ( i = Vec_IntEntry(m->vWordHeads, index); i >= 0; i = Vec_IntEntry(m->vWordNext, i) )
            Vec_IntWriteEntry(stops, i, 2*cut+(Vec_IntEntry(vMap, i) & 1));
    }
    return stops;
}

/**Function*************************************************************

  Synopsis    [Reuses an exact source simulation domain within one analysis.]

  Description [Mutable patterns, candidates and boundary priorities are
  private to each borrower. Four retained domains use at most two million
  source-object slots. Active borrowers prevent eviction.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_WordSim_t * Acec2_WordSimCached( Acec2_Man_t * m, Vec_Int_t * vMap, Hsh_Int1Man_t * hCuts, int Width )
{
    Acec2_WordSim_t * domain = NULL, * p, * old;
    Vec_Int_t * stops = Acec2_WordStopsCached(m, vMap, hCuts);
    int i, index = -1, nObjects = Gia_ManObjNum(m->pGia), capacity = 0;
    if ( nObjects > 0 && nObjects <= 2000000 ) capacity = Abc_MinInt(4, 2000000/nObjects);
    if ( !capacity ) return Acec2_WordSimStart(m->pGia, stops, Width);
    if ( !m->vWordDomains ) m->vWordDomains = Vec_PtrAlloc(capacity);
    Vec_PtrForEachEntry(Acec2_WordSim_t *, m->vWordDomains, old, i)
        if ( Vec_IntEqual(stops, old->vStop) ) { domain = old; m->nWordDomainHits++; break; }
    if ( domain ) Vec_IntFree(stops);
    else
    {
        if ( Vec_PtrSize(m->vWordDomains) < capacity ) index = Vec_PtrSize(m->vWordDomains);
        else for ( i = 0; i < capacity; i++ )
        {
            index = (m->iWordDomain+i)%capacity; old = (Acec2_WordSim_t *)Vec_PtrEntry(m->vWordDomains, index);
            if ( !old->nUsers ) break;
            index = -1;
        }
        if ( index < 0 ) return Acec2_WordSimStart(m->pGia, stops, Width);
        domain = Acec2_WordSimStart(m->pGia, stops, 0);
        Vec_WrdFree(domain->vSim); domain->vSim = NULL;
        if ( index == Vec_PtrSize(m->vWordDomains) ) Vec_PtrPush(m->vWordDomains, domain);
        else { Acec2_WordSimStop((Acec2_WordSim_t *)Vec_PtrEntry(m->vWordDomains, index)); Vec_PtrWriteEntry(m->vWordDomains, index, domain); }
        m->iWordDomain = (index+1)%capacity;
    }
    p = ABC_CALLOC(Acec2_WordSim_t, 1); p->g = m->pGia; p->pDomain = domain; domain->nUsers++;
    p->vStop = domain->vStop; p->vEval = domain->vEval; p->vBoundary = Vec_IntDup(domain->vBoundary);
    p->vSim = Vec_WrdStart(Gia_ManObjNum(m->pGia)); p->vCandidates = Vec_WecStart(4*Width);
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases a private candidate simulation domain.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_WordSimStop( Acec2_WordSim_t * p )
{
    if ( !p ) return;
    if ( p->pDomain ) { assert(p->pDomain->nUsers > 0); p->pDomain->nUsers--; }
    else { assert(!p->nUsers); Vec_IntFree(p->vStop); Vec_IntFree(p->vEval); }
    Vec_IntFree(p->vBoundary); Vec_WrdFreeP(&p->vSim); Vec_WecFree(p->vCandidates); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Prefers observed arithmetic sums over nearly equal carry gates.]

  Description [This affects proposals only. Every retained pair still needs
  an exact proof; a parity annotation never establishes equality by itself.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_WordPrioritize( Acec2_WordSim_t * s, Acec2_Man_t * m )
{
    Vec_Int_t * v;
    int i, j, id;
    s->pMan = m;
    Vec_WecForEachLevel(m->vRoots, v, i)
        for ( j = 0; j < Vec_IntSize(v); j += 2 )
        { id = Vec_IntEntry(v, j) >> 1; Vec_IntWriteEntry(s->vBoundary, id, Vec_IntEntry(s->vBoundary, id) | 2); }
    for ( i = 0; i < Vec_IntSize(m->vXors); i += 5 )
    { id = Vec_IntEntry(m->vXors, i+4) >> 1; Vec_IntWriteEntry(s->vBoundary, id, Vec_IntEntry(s->vBoundary, id) | 4); }
    Vec_IntForEachEntry(s->vStop, id, i)
        if ( id >= 0 ) Vec_IntWriteEntry(s->vBoundary, i, Vec_IntEntry(s->vBoundary, i) | 8);
}

/**Function*************************************************************

  Synopsis    [Returns one bit of a directed operand pattern.]

  Description [Directed patterns include signed extrema and walking ones
  and zeros. They are candidate filters; the subsequent exact proof remains
  mandatory even when every pattern agrees.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PatternBit( int Kind, int Bit, int Width )
{
    return Kind == 0 ? 0 : Kind == 1 ? Bit == 0 : Kind == 2 ? Bit != Width-1 : Kind == 3 ? Bit == Width-1 : 1;
}
/**Function*************************************************************

  Synopsis    [Creates deterministic random and directed operand patterns.]

  Description [Writes phased cut values for random, extremal and walking-bit
  patterns. Simulation proposes matches; exact proofs authorize replacements.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_OperandPatterns( Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, int Round, word * pState )
{
    int side, i, k, index, pattern, walk, which, other, bit, lit, n[2];
    word value;
    n[0] = Vec_IntSize(vOps[0]); n[1] = Vec_IntSize(vOps[1]);
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vOps[side], lit, i)
        {
            if ( lit < 2 ) continue;
            index = Acec2_IndexLookup(hCuts, Abc_Lit2Var(lit)); value = 0;
            if ( Round < 4 )
            { value = Acec2_Random(pState); }
            else for ( k = 0; k < 64; k++ )
            {
                pattern = 64*Round+k-256;
                if ( pattern < 25 ) bit = Acec2_PatternBit(side ? pattern%5 : pattern/5, i, n[side]);
                else
                {
                    pattern -= 25; which = pattern >= 10*n[0];
                    if ( which ) pattern -= 10*n[0];
                    walk = pattern/10; other = pattern%5;
                    bit = side == which ? ((i == walk) ^ ((pattern/5)&1)) : Acec2_PatternBit(other, i, n[side]);
                }
                value |= (word)bit << k;
            }
            Vec_WrdWriteEntry(vValues, index, Abc_LitIsCompl(lit) ? ~value : value);
        }
}

/**Function*************************************************************

  Synopsis    [Simulates a signed or unsigned product modulo a fixed width.]

  Description [Bit-parallel additions avoid native word-width restrictions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_ProductPatterns( Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Width )
{
    int mode, i, j, k, a, b, neg;
    word x, y, carry, old;
    Vec_WrdFill(vExpected, 4*Width, 0);
    for ( mode = 0; mode < 4; mode++ )
        Vec_IntForEachEntry(vOps[0], a, i)
            Vec_IntForEachEntry(vOps[1], b, j)
            {
                x = a < 2 ? 0 : Vec_WrdEntry(vValues, Acec2_IndexLookup(hCuts, a >> 1)); if ( a & 1 ) x = ~x;
                y = b < 2 ? 0 : Vec_WrdEntry(vValues, Acec2_IndexLookup(hCuts, b >> 1)); if ( b & 1 ) y = ~y;
                carry = x & y;
                neg = ((mode & 1) && i == Vec_IntSize(vOps[0])-1) ^ ((mode & 2) && j == Vec_IntSize(vOps[1])-1);
                for ( k = i+j; k < Width && carry; k++ )
                {
                    old = Vec_WrdEntry(vExpected, mode*Width+k);
                    Vec_WrdWriteEntry(vExpected, mode*Width+k, old ^ carry);
                    carry &= neg ? ~old : old;
                }
            }
}

/**Function*************************************************************

  Synopsis    [Evaluates proposed product or weighted-region words on cut patterns.]

  Description [This produces expected signatures only; component proofs establish equality.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_ModelPatterns( Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, Vec_Wrd_t * vValues,
                                 Vec_Wrd_t * vExpected, int Width, Gia_Man_t * pModel )
{
    Vec_Wrd_t * vSim;
    Gia_Obj_t * o;
    int i;
    word a;
    if ( !pModel ) { Acec2_ProductPatterns(vOps, hCuts, vValues, vExpected, Width); return; }
    vSim = Vec_WrdStart(Gia_ManObjNum(pModel));
    Gia_ManForEachCi(pModel, o, i) Vec_WrdWriteEntry(vSim, Gia_ObjId(pModel, o), Vec_WrdEntry(vValues, i));
    Gia_ManForEachAnd(pModel, o, i)
        Vec_WrdWriteEntry(vSim, i, Acec2_SimGate(pModel, i, vSim, 1, 0));
    Gia_ManForEachCo(pModel, o, i)
    {
        a = Vec_WrdEntry(vSim, Gia_ObjFaninId0p(pModel, o));
        Vec_WrdWriteEntry(vExpected, i, Gia_ObjFaninC0(o) ? ~a : a);
    }
    Vec_WrdFree(vSim);
}

/**Function*************************************************************

  Synopsis    [Filters result candidates using one batch of cut patterns.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_WordSimulate( Acec2_WordSim_t * p, Vec_Wrd_t * vValues, Vec_Wrd_t * vExpected, int Round )
{
    Vec_Int_t * v, * vHeads = NULL, * vNext = NULL;
    int i, j, id, lit, slot, keep, nSlots;
    word a, value, key;
    Vec_IntForEachEntry(p->vStop, lit, i)
        if ( lit >= 0 )
        { value = Vec_WrdEntry(vValues, lit >> 1); Vec_WrdWriteEntry(p->vSim, i, (lit & 1) ? ~value : value); }
    Vec_IntForEachEntry(p->vEval, id, i)
    {
        Vec_WrdWriteEntry(p->vSim, id, Acec2_SimGate(p->g, id, p->vSim, 1, 0));
    }
    if ( !Round )
    {
        nSlots = Abc_PrimeCudd(Abc_MaxInt(100, Vec_IntSize(p->vEval)));
        vHeads = Vec_IntStartFull(nSlots); vNext = Vec_IntStartFull(Gia_ManObjNum(p->g));
        Vec_IntForEachEntry(p->vEval, id, i)
        {
            value = Vec_WrdEntry(p->vSim, id); key = (value & 1) ? ~value : value;
            if ( !key ) continue;
            slot = (int)(key % (unsigned)nSlots); Vec_IntWriteEntry(vNext, id, Vec_IntEntry(vHeads, slot)); Vec_IntWriteEntry(vHeads, slot, id);
        }
        Vec_IntForEachEntry(p->vStop, lit, id)
        {
            if ( lit < 0 ) continue;
            value = Vec_WrdEntry(p->vSim, id); key = (value & 1) ? ~value : value;
            if ( !key ) continue;
            slot = (int)(key % (unsigned)nSlots); Vec_IntWriteEntry(vNext, id, Vec_IntEntry(vHeads, slot)); Vec_IntWriteEntry(vHeads, slot, id);
        }
        Vec_WecForEachLevel(p->vCandidates, v, i)
        {
            value = Vec_WrdEntry(vExpected, i); key = (value & 1) ? ~value : value;
            if ( !key ) { Vec_IntPush(v, value ? 1 : 0); continue; }
            slot = (int)(key % (unsigned)nSlots);
            for ( id = Vec_IntEntry(vHeads, slot); id >= 0; id = Vec_IntEntry(vNext, id) )
            {
                a = Vec_WrdEntry(p->vSim, id);
                if ( a == value || a == ~value ) Vec_IntPush(v, Abc_Var2Lit(id, a != value));
            }
        }
    }
    else Vec_WecForEachLevel(p->vCandidates, v, i)
    {
        keep = 0; value = Vec_WrdEntry(vExpected, i);
        Vec_IntForEachEntry(v, lit, j)
        {
            a = Vec_WrdEntry(p->vSim, lit >> 1); if ( lit & 1 ) a = ~a;
            if ( a == value ) Vec_IntWriteEntry(v, keep++, lit);
        }
        Vec_IntShrink(v, keep);
    }
    Vec_IntFreeP(&vHeads); Vec_IntFreeP(&vNext);
}

/**Function*************************************************************

  Synopsis    [Builds a reference product to fill unobserved result bits.]

  Description [A sliced product need not contain its discarded low bits.
  The same reference fills these holes on both sides of the component proof;
  only existing result signals are eligible for replacement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acec2_ProductReference( Gia_Man_t * g, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, int Mode, int Width )
{
    Vec_Int_t * vArgs[2], * vBits;
    int side, i, lit;
    for ( side = 0; side < 2; side++ )
    {
        vArgs[side] = Vec_IntAlloc(Vec_IntSize(vOps[side]));
        Vec_IntForEachEntry(vOps[side], lit, i)
            Vec_IntPush(vArgs[side], lit < 2 ? lit : Abc_Var2Lit(Acec2_IndexLookup(hCuts, lit >> 1)+1, lit & 1));
    }
    vBits = Acec2_ProductBits(g, vArgs, Mode, Width);
    Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]);
    return vBits;
}

/**Function*************************************************************

  Synopsis    [Copies a proposed reference word onto an existing cut interface.]

  Description [Returns the requested low prefix in the selected orientation.]

  SideEffects [Appends gates to the private destination GIA.]

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_ModelAppend( Gia_Man_t * g, Gia_Man_t * pModel, int Mode, int Width, int Prefix )
{
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(pModel)), * vBits = Vec_IntAlloc(Prefix);
    Gia_Obj_t * o;
    int i;
    Gia_ManForEachCi(pModel, o, i) Vec_IntWriteEntry(vMap, Gia_ObjId(pModel, o), Abc_Var2Lit(Gia_ObjId(g, Gia_ManCi(g, i)), 0));
    Gia_ManForEachAnd(pModel, o, i)
        Vec_IntWriteEntry(vMap, i, Gia_ManHashAnd(g,
            Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
            Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o)));
    for ( i = 0; i < Prefix; i++ )
    {
        o = Gia_ManCo(pModel, Mode*Width+i);
        Vec_IntPush(vBits, Vec_IntEntry(vMap, Gia_ObjFaninId0p(pModel, o)) ^ Gia_ObjFaninC0(o));
    }
    Vec_IntFree(vMap); return vBits;
}

/**Function*************************************************************

  Synopsis    [Prefers result candidates belonging to one weighted cell region.]

  Description [Independent per-bit selection can mix a truncated product's
  low sums with another implementation's upper sums. A common region and
  rank offset proposes a coherent word. The final component proof remains
  the only authority for any replacement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_BoundaryRegion( Acec2_WordSim_t * p, int Mode, int Width, int Prefix, int * pOffset )
{
    Acec2_Man_t * m = p->pMan;
    Acec2_Cell_t * c, * q;
    Vec_Int_t * v, * w, * vTried = Vec_IntAlloc(100);
    int i, j, k, l, lit, owner, id, off, score, best = -1, bestScore = 3, attempts = 0;
    *pOffset = 0;
    if ( !m ) { Vec_IntFree(vTried); return -1; }
    for ( i = Prefix-1; i >= 0 && attempts < 32; i-- )
    {
        v = Vec_WecEntry(p->vCandidates, Mode*Width+i);
        for ( j = 0; j < Vec_IntSize(v) && j < 128 && attempts < 32; j++ )
        {
            lit = Vec_IntEntry(v, j); owner = Vec_IntEntry(m->vOwner, lit >> 1);
            if ( owner < 0 ) continue;
            c = Acec2_Cell(m, owner/2); off = i-c->Rank-(owner & 1);
            for ( k = 0; k < Vec_IntSize(vTried); k += 2 )
                if ( Vec_IntEntry(vTried, k) == c->Tree && Vec_IntEntry(vTried, k+1) == off ) break;
            if ( k < Vec_IntSize(vTried) ) continue;
            Vec_IntPushTwo(vTried, c->Tree, off); attempts++; score = 0;
            for ( k = 0; k < Prefix; k++ )
            {
                w = Vec_WecEntry(p->vCandidates, Mode*Width+k);
                for ( l = 0; l < Vec_IntSize(w) && l < 128; l++ )
                {
                    id = Vec_IntEntry(m->vOwner, Vec_IntEntry(w, l) >> 1); if ( id < 0 ) continue;
                    q = Acec2_Cell(m, id/2);
                    if ( q->Tree == c->Tree && q->Rank+(id & 1)+off == k ) { score++; break; }
                }
            }
            if ( score > bestScore ) { bestScore = score; best = c->Tree; *pOffset = off; }
        }
    }
    Vec_IntFree(vTried); return best;
}

/**Function*************************************************************

  Synopsis    [Extracts proposed result bits over independent cut inputs.]

  Description [Unobserved positions use an identical reference on both sides.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Acec2_ExtractWord( Acec2_WordSim_t * p, int Mode, int Width, int Prefix, int nInputs, Vec_Int_t ** pvRoots, Vec_Int_t ** vOps, Hsh_Int1Man_t * hCuts, int Strategy, Gia_Man_t * pModel )
{
    Gia_Man_t * g = Gia_ManStart(1000), * clean;
    Vec_Int_t * vMap = Vec_IntStartFull(Gia_ManObjNum(p->g)), * vRoots = Vec_IntAlloc(Prefix), * v, * vReference = NULL;
    int i, j, lit, best, score, cur, tree, offset, owner;
    Acec2_Cell_t * cell;
    tree = Acec2_BoundaryRegion(p, Mode, Width, Prefix, &offset);
    for ( i = 0; i < Prefix; i++ )
    {
        v = Vec_WecEntry(p->vCandidates, Mode*Width+i); best = -1; score = -1;
        Vec_IntForEachEntry(v, lit, j)
        {
            cur = Vec_IntEntry(p->vBoundary, lit >> 1);
            // The earliest implementation often exposes the product before
            // rounding or other arithmetic. Such later sums can agree on
            // many patterns, so also try a proposal without boundary bias.
            if ( !Strategy )
            {
                cur &= 8;
                owner = p->pMan ? Vec_IntEntry(p->pMan->vOwner, lit >> 1) : -1;
                if ( tree >= 0 && owner >= 0 )
                {
                    cell = Acec2_Cell(p->pMan, owner/2);
                    if ( cell->Tree == tree && cell->Rank+(owner & 1)+offset == i ) cur |= 16;
                }
            }
            if ( cur > score || (cur == score && (best < 0 || (Strategy == 2 ? lit > best : lit < best))) ) { best = lit; score = cur; }
        }
        Vec_IntPush(vRoots, best);
    }
    Gia_ManHashAlloc(g);
    for ( i = 0; i < nInputs; i++ ) Gia_ManAppendCi(g);
    Vec_IntWriteEntry(vMap, 0, 0);
    Vec_IntForEachEntry(p->vStop, lit, i) if ( lit >= 0 ) Vec_IntWriteEntry(vMap, i, lit+2);
    if ( !Acec2_CopyCone(p->g, g, vMap, vRoots, p->vEval, NULL, 0) )
    {
        Vec_IntFree(vMap); Vec_IntFree(vRoots); Gia_ManStop(g); *pvRoots = NULL; return NULL;
    }
    for ( i = 0; i < Prefix; i++ )
        if ( !Vec_IntSize(Vec_WecEntry(p->vCandidates, Mode*Width+i)) )
        { vReference = pModel ? Acec2_ModelAppend(g, pModel, Mode, Width, Prefix) : Acec2_ProductReference(g, vOps, hCuts, Mode, Prefix); break; }
    Vec_IntForEachEntry(vRoots, lit, i)
        Gia_ManAppendCo(g, lit < 0 ? Vec_IntEntry(vReference, i) : Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
    Gia_ManHashStop(g); clean = Gia_ManCleanup(g); Gia_ManStop(g); Vec_IntFree(vMap); Vec_IntFreeP(&vReference);
    *pvRoots = vRoots;
    return clean;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
