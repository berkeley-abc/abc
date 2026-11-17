/**CFile****************************************************************

  FileName    [acec2Gap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Checked weighted identities across source region boundaries.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 14, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef struct Acec2_GapQueue_t_ Acec2_GapQueue_t;
struct Acec2_GapQueue_t_
{
    Vec_Wec_t * vCandidates;
    Vec_Ptr_t * vProducts;      // unproved operand grids, owned by this queue
    Vec_Int_t * vCoverage;      // observed, total and absent source products per grid
    int Next, Result, NextProduct, fProductNext, NextExpression;
};

static int Acec2_GridPartition( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                               Vec_Int_t * constants, Vec_Int_t * products, int Width );
static int Acec2_GridChains( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                            Vec_Int_t * constants, Vec_Int_t * products, int Width );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Simulates source signals once to filter weighted proposals.]

  Description [These signatures never establish an arithmetic identity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GapSimulate( Acec2_Man_t * m )
{
    Gia_Obj_t * o; Vec_Wrd_t * values; int i;
    word state = ABC_CONST(0xA395BE7D6182C04F);
    if ( m->vGapSim ) return 1;
    values = Vec_WrdStart(Gia_ManObjNum(m->pGia));
    Gia_ManForEachCi(m->pGia, o, i) Vec_WrdWriteEntry(values, Gia_ObjId(m->pGia, o), (Acec2_Random(&state) & ~(word)3) | 2);
    Gia_ManForEachAnd(m->pGia, o, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stopped(m) ) { Vec_WrdFree(values); return 0; }
        Vec_WrdWriteEntry(values, i, Acec2_SimGate(m->pGia, i, values, 1, 0));
    }
    m->vGapSim = values; return 1;
}

/**Function*************************************************************

  Synopsis    [Finds ranked source boundaries behind later region inputs.]

  Description [The basis contains both region roots and ranked input terms.
  Traversal stops at either boundary, retaining multiplicity and phase.
  Interior gates are recorded separately to group connected breaks.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wec_t * Acec2_GapDependencies( Acec2_Man_t * m, Acec2_Record_t * r,
                                         Vec_Int_t * basis, Vec_Wec_t * cones, int * pnWork )
{
    Gia_Obj_t * o; int nRoots = Vec_IntSize(r->vOutputs)/2, nTerms = Vec_IntSize(r->vTerms)/2;
    Vec_Int_t * heads = Vec_IntStartFull(Gia_ManObjNum(m->pGia)), * next = Vec_IntStartFull(Vec_IntSize(basis)/2);
    Vec_Int_t * seen = Vec_IntStart(Gia_ManObjNum(m->pGia)), * stack = Vec_IntAlloc(100), * found;
    Vec_Wec_t * deps = Vec_WecStart(nTerms); int i, j, origin, id, steps, root;
    // Put roots first in each occurrence list. When a signal is on both
    // boundaries, its earlier output occurrences define the dependency.
    for ( i = Vec_IntSize(basis)/2-1; i >= 0; i-- )
    {
        id = Vec_IntEntry(basis, 2*i) >> 1;
        if ( !id || Vec_IntEntry(basis, 2*i+1) >= r->Width ) continue;
        Vec_IntWriteEntry(next, i, Vec_IntEntry(heads, id)); Vec_IntWriteEntry(heads, id, i);
    }
    for ( i = 0; i < nTerms && !Acec2_Stopped(m); i++ )
    {
        origin = Vec_IntEntry(r->vTerms, 2*i) >> 1;
        if ( Vec_IntEntry(r->vTerms, 2*i+1) >= r->Width || !origin ) continue;
        root = Vec_IntEntry(heads, origin);
        if ( root >= 0 && root < nRoots ) continue;
        Vec_IntClear(stack); Vec_IntPush(stack, origin); steps = 0; found = Vec_WecEntry(deps, i);
        while ( Vec_IntSize(stack) )
        {
            id = Vec_IntPop(stack); if ( !id || Vec_IntEntry(seen, id) == i+1 ) continue;
            Vec_IntWriteEntry(seen, id, i+1);
            if ( ++steps > 4096 || ++*pnWork > 262144 )
            { m->nGapLimits++; Vec_IntClear(found); Vec_IntClear(Vec_WecEntry(cones, i)); break; }
            if ( (steps & 255) == 0 && Acec2_Stopped(m) ) break;
            if ( id != origin && Vec_IntEntry(heads, id) >= 0 )
            {
                root = Vec_IntEntry(heads, id) < nRoots;
                for ( j = Vec_IntEntry(heads, id); j >= 0 && (!root || j < nRoots); j = Vec_IntEntry(next, j) ) Vec_IntPush(found, j);
                continue;
            }
            o = Gia_ManObj(m->pGia, id); if ( !Gia_ObjIsAnd(o) ) continue;
            Vec_WecPush(cones, i, id);
            Vec_IntPushTwo(stack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
            if ( Gia_ObjIsMux(m->pGia, o) ) Vec_IntPush(stack, Gia_ObjFaninId2(m->pGia, id));
        }
        if ( Vec_IntSize(found) > 1 ) Vec_IntSort(found, 0);
        if ( *pnWork > 262144 ) break;
    }
    Vec_IntFree(heads); Vec_IntFree(next); Vec_IntFree(seen); Vec_IntFree(stack);
    return deps;
}

/**Function*************************************************************

  Synopsis    [Tests whether two boundary groups share a predecessor.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GapNeighbors( Vec_Int_t * a, Vec_Int_t * b )
{
    int i = 0, j = 0;
    while ( i < Vec_IntSize(a) && j < Vec_IntSize(b) )
    {
        if ( Vec_IntEntry(a, i) == Vec_IntEntry(b, j) ) return 1;
        if ( Vec_IntEntry(a, i) < Vec_IntEntry(b, j) ) i++; else j++;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Retains an observed weighted relation for subsequent proof.]

  Description [For earlier roots S and later leaves L, test S-L=c.
  Store the proposed identity L=S-c at the parent's full modulus. A small
  relative rank span makes the simulation arithmetic exact in 64 bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_GapCandidate( Acec2_Man_t * m, Acec2_Record_t * r, Acec2_GapQueue_t * q,
                                Vec_Int_t * basis, Vec_Wec_t * deps, int * selected, int size )
{
    Vec_Int_t * roots = Vec_IntAlloc(16), * terms, * key, * old, * constants;
    int i, j, k, lit, rank, low = r->Width, high = 0, bit;
    ABC_INT64_T value, difference = 0; word pattern, correction;
    m->nGapGroups++;
    for ( i = 0; i < size; i++ ) Vec_IntAppend(roots, Vec_WecEntry(deps, selected[i]));
    Vec_IntUniqify(roots);
    if ( !size || !Vec_IntSize(roots) ) { Vec_IntFree(roots); return; }
    if ( size > 128 || Vec_IntSize(roots) > 256 ) { m->nGapLimits++; Vec_IntFree(roots); return; }
    for ( k = 0; k < 2; k++ )
    {
        terms = k ? r->vTerms : basis;
        for ( i = 0; i < (k ? size : Vec_IntSize(roots)); i++ )
        {
            j = k ? selected[i] : Vec_IntEntry(roots, i); rank = Vec_IntEntry(terms, 2*j+1);
            low = Abc_MinInt(low, rank); high = Abc_MaxInt(high, rank);
        }
    }
    if ( high-low > 48 ) { m->nGapLimits++; Vec_IntFree(roots); return; }
    if ( !Acec2_GapSimulate(m) ) { Vec_IntFree(roots); return; }
    for ( bit = 0; bit < 64; bit++ )
    {
        value = 0;
        for ( k = 0; k < 2; k++ )
        {
            terms = k ? r->vTerms : basis;
            for ( i = 0; i < (k ? size : Vec_IntSize(roots)); i++ )
            {
                j = k ? selected[i] : Vec_IntEntry(roots, i); lit = Vec_IntEntry(terms, 2*j); rank = Vec_IntEntry(terms, 2*j+1)-low;
                pattern = Vec_WrdEntry(m->vGapSim, lit >> 1); if ( lit & 1 ) pattern = ~pattern;
                if ( (pattern >> bit) & 1 ) value += (k ? -1 : 1)*((ABC_INT64_T)1 << rank);
            }
        }
        if ( !bit ) difference = value;
        else if ( value != difference ) { Vec_IntFree(roots); return; }
    }
    correction = (word)(-difference); constants = Vec_IntAlloc(16);
    for ( rank = low; rank < r->Width; rank++ )
        if ( rank-low < 64 ? (correction >> (rank-low)) & 1 : difference > 0 ) Vec_IntPush(constants, rank);
    key = Vec_IntAlloc(32); Vec_IntPushTwo(key, r->Width, 2*size); Vec_IntPushTwo(key, 2*Vec_IntSize(roots), Vec_IntSize(constants));
    for ( i = 0; i < size; i++ ) { j = selected[i]; Vec_IntPushTwo(key, Vec_IntEntry(r->vTerms, 2*j), Vec_IntEntry(r->vTerms, 2*j+1)); }
    Vec_IntForEachEntry(roots, j, i) Vec_IntPushTwo(key, Vec_IntEntry(basis, 2*j), Vec_IntEntry(basis, 2*j+1));
    Vec_IntAppend(key, constants); Vec_IntFree(constants); Vec_IntFree(roots);
    Vec_WecForEachLevel(q->vCandidates, old, i) if ( Vec_IntEqual(old, key) ) break;
    if ( i == Vec_WecSize(q->vCandidates) )
    { Vec_IntAppend(Vec_WecPushLevel(q->vCandidates), key); m->nGapProposals++; }
    Vec_IntFree(key);
}

/**Function*************************************************************

  Synopsis    [Groups breaks through shared gates, then shared cut signals.]

  Description [Only discovery uses connectivity. Every resulting weighted
  relation still needs a completed exact source proof. Large connected
  components leave the smaller local proposals available.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_GapConnected( Acec2_Man_t * m, Acec2_Record_t * r, Acec2_GapQueue_t * q,
                              Vec_Int_t * basis, Vec_Wec_t * deps, Vec_Wec_t * cones, int * pnWork )
{
    Vec_Int_t * parent = Vec_IntStartNatural(Vec_WecSize(deps)), * owners, * v;
    Vec_Wec_t * groups, * index; int phase, i, j, id, first, a, b;
    for ( phase = 0; phase < 2 && !Acec2_Stopped(m); phase++ )
    {
        index = phase ? deps : cones;
        owners = Vec_IntStartFull(phase ? Vec_IntSize(basis)/2 : Gia_ManObjNum(m->pGia));
        Vec_WecForEachLevel(index, v, i)
        {
            if ( !Vec_IntSize(Vec_WecEntry(deps, i)) ) continue;
            Vec_IntForEachEntry(v, id, j)
            {
                if ( ++*pnWork > 262144 || (!(*pnWork & 255) && Acec2_Stopped(m)) ) break;
                first = Vec_IntEntry(owners, id);
                if ( first < 0 ) { Vec_IntWriteEntry(owners, id, i); continue; }
                a = Acec2_WeightFind(Vec_IntArray(parent), NULL, NULL, first); b = Acec2_WeightFind(Vec_IntArray(parent), NULL, NULL, i);
                if ( a != b ) Vec_IntWriteEntry(parent, Abc_MaxInt(a, b), Abc_MinInt(a, b));
            }
            if ( *pnWork > 262144 || Acec2_Stopped(m) ) break;
        }
        Vec_IntFree(owners);
        if ( *pnWork > 262144 || Acec2_Stopped(m) ) break;
        groups = Vec_WecStart(Vec_WecSize(deps));
        Vec_WecForEachLevel(deps, v, i)
            if ( Vec_IntSize(v) ) Vec_WecPush(groups, Acec2_WeightFind(Vec_IntArray(parent), NULL, NULL, i), i);
        Vec_WecForEachLevel(groups, v, i)
        {
            if ( Vec_WecSize(q->vCandidates) >= 32 || Acec2_Stopped(m) ) break;
            if ( Vec_IntSize(v) > 128 ) { m->nGapLimits++; continue; }
            if ( Vec_IntSize(v) >= 2 ) Acec2_GapCandidate(m, r, q, basis, deps, Vec_IntArray(v), Vec_IntSize(v));
        }
        Vec_WecFree(groups);
    }
    Vec_IntFree(parent);
}

/**Function*************************************************************

  Synopsis    [Tests primary outputs as a possible ordered boundary word.]

  Description [Port order proposes ranks only. Simulation filters the
  candidate and the same exact source checker must prove the identity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_GapOutputs( Acec2_Man_t * m, Acec2_Record_t * r, Acec2_GapQueue_t * q,
                            Vec_Int_t * basis, int * pnWork )
{
    Acec2_Record_t word = *r; Gia_Obj_t * o; Vec_Wec_t * deps, * cones;
    Vec_Int_t * selected; int i, j, id, first, width = Gia_ManCoNum(m->pGia);
    if ( width < 4 || width != r->Width || width > 128 || *pnWork > 262144 ) return;
    word.vTerms = Vec_IntAlloc(2*width); cones = Vec_WecStart(width); selected = Vec_IntStartNatural(width);
    Gia_ManForEachCo(m->pGia, o, i) Vec_IntPushTwo(word.vTerms, Gia_ObjFaninLit0p(m->pGia, o), i);
    deps = Acec2_GapDependencies(m, &word, basis, cones, pnWork);
    for ( i = 0; i < width; i++ )
    {
        id = Vec_IntEntry(word.vTerms, 2*i) >> 1;
        for ( first = 0; first < Vec_IntSize(basis)/2; first++ )
            if ( (Vec_IntEntry(basis, 2*first) >> 1) == id ) break;
        if ( first == Vec_IntSize(basis)/2 ) continue;
        Vec_IntClear(Vec_WecEntry(deps, i));
        for ( j = first; j < Vec_IntSize(basis)/2; j++ )
            if ( (first < Vec_IntSize(r->vOutputs)/2) == (j < Vec_IntSize(r->vOutputs)/2) &&
                 (Vec_IntEntry(basis, 2*j) >> 1) == id ) Vec_WecPush(deps, i, j);
    }
    if ( *pnWork <= 262144 && !Acec2_Stopped(m) ) Acec2_GapCandidate(m, &word, q, basis, deps, Vec_IntArray(selected), width);
    Vec_IntFree(word.vTerms); Vec_IntFree(selected); Vec_WecFree(deps); Vec_WecFree(cones);
}

/**Function*************************************************************

  Synopsis    [Finds a physical source gate for a proposed operand bit product.]

  Description [The exact literal-pair index is built once per source design.
  Missing gates are cached as absent and are never treated as proved terms.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GapProductNode( Acec2_Man_t * m, int a, int b, Vec_Int_t * key )
{
    Gia_Obj_t * o; int i, id, x, y;
    if ( !m->hGapProducts )
    {
        if ( Gia_ManAndNum(m->pGia) > 4000000 ) { m->nGapLimits++; return -1; }
        m->hGapProducts = Hsh_VecManStart(100); m->vGapProducts = Vec_IntAlloc(100);
        Gia_ManForEachAnd(m->pGia, o, i)
        {
            if ( !(i & 1023) && Acec2_Stopped(m) ) return -1;
            if ( Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
            x = Gia_ObjFaninLit0(o, i); y = Gia_ObjFaninLit1(o, i); if ( x > y ) ABC_SWAP(int, x, y);
            Vec_IntClear(key); Vec_IntPushTwo(key, x, y); id = Hsh_VecManAdd(m->hGapProducts, key);
            if ( id == Vec_IntSize(m->vGapProducts) ) Vec_IntPush(m->vGapProducts, 2*i);
        }
    }
    if ( a > b ) ABC_SWAP(int, a, b);
    Vec_IntClear(key); Vec_IntPushTwo(key, a, b); id = Hsh_VecManAdd(m->hGapProducts, key);
    if ( id == Vec_IntSize(m->vGapProducts) ) Vec_IntPush(m->vGapProducts, -1);
    return Vec_IntEntry(m->vGapProducts, id);
}

/**Function*************************************************************

  Synopsis    [Orders explicit products without changing their multiplicity.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GridTupleCompare( const void * p0, const void * p1 )
{
    const int * a = (const int *)p0, * b = (const int *)p1; int i;
    for ( i = 0; i < 4; i++ ) if ( a[i] != b[i] ) return a[i] < b[i] ? -1 : 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Keys one modular source obligation without its proposing region.]

  Description [Order is immaterial, but phases, ranks, multiplicities,
  constants, explicit products and the optional proof cut are retained.
  Source gates are immutable throughout an analysis. Exact keys, rather
  than fingerprints, authorize reuse. Cache storage has a separate bound.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GridProofKey( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                                Vec_Int_t * constants, Vec_Int_t * products, Vec_Int_t * cut, int Width )
{
    Vec_Int_t * key, * v, * tuples; Vec_Wrd_t * pairs; word pair;
    ABC_INT64_T size = (ABC_INT64_T)Vec_IntSize(outputs)+Vec_IntSize(terms)+Vec_IntSize(constants)+Vec_IntSize(products)+Vec_IntSize(cut)+6;
    int side, i, a, b, id, before;
    if ( size > 1000000-m->nGridProofWords ) { m->nGridProofCacheLimits++; return -1; }
    key = Vec_IntAlloc((int)size); pairs = Vec_WrdAlloc(32); tuples = Vec_IntDup(products);
    Vec_IntPush(key, Width);
    for ( side = 0; side < 2; side++ )
    {
        v = side ? terms : outputs; Vec_WrdClear(pairs);
        for ( i = 0; i < Vec_IntSize(v); i += 2 )
            Vec_WrdPush(pairs, ((word)(unsigned)Vec_IntEntry(v, i) << 32) | (unsigned)Vec_IntEntry(v, i+1));
        if ( Vec_WrdSize(pairs) > 1 ) Vec_WrdSort(pairs, 0);
        Vec_IntPush(key, Vec_IntSize(v));
        Vec_WrdForEachEntry(pairs, pair, i) Vec_IntPushTwo(key, (int)(pair >> 32), (int)(unsigned)pair);
    }
    v = Vec_IntDup(constants); if ( Vec_IntSize(v) > 1 ) Vec_IntSort(v, 0);
    Vec_IntPush(key, Vec_IntSize(v)); Vec_IntAppend(key, v); Vec_IntFree(v);
    for ( i = 0; i < Vec_IntSize(tuples); i += 4 )
    {
        a = Vec_IntEntry(tuples, i); b = Vec_IntEntry(tuples, i+1);
        Vec_IntWriteEntry(tuples, i, Abc_MinInt(a, b)); Vec_IntWriteEntry(tuples, i+1, Abc_MaxInt(a, b));
    }
    if ( Vec_IntSize(tuples) > 4 ) qsort(Vec_IntArray(tuples), Vec_IntSize(tuples)/4, 4*sizeof(int), Acec2_GridTupleCompare);
    Vec_IntPush(key, Vec_IntSize(tuples)); Vec_IntAppend(key, tuples);
    v = Vec_IntDup(cut); Vec_IntUniqify(v); Vec_IntPush(key, Vec_IntSize(v)); Vec_IntAppend(key, v); Vec_IntFree(v);
    if ( !m->hGridProofs ) { m->hGridProofs = Hsh_VecManStart(100); m->vGridProofs = Vec_IntAlloc(100); }
    before = Hsh_VecSize(m->hGridProofs); id = Hsh_VecManAdd(m->hGridProofs, key);
    if ( id == before )
    {
        for ( i = 0; i < 8; i++ ) Vec_IntPush(m->vGridProofs, 0);
        m->nGridProofWords += Vec_IntSize(key);
    }
    Vec_IntFree(key); Vec_IntFree(tuples); Vec_WrdFree(pairs); return id;
}

/**Function*************************************************************

  Synopsis    [Checks bounded source cones before expanding a complete gap.]

  Description [Frontiers at depths 2, 4, 8, 16 and 32 preserve nearby carry
  relationships while exposing the remaining signals as independent inputs.
  Each cone has at most 4096 nodes. Only a completed proof over this larger
  free domain establishes a source identity. Abstract counterexamples are
  inconclusive; the caller may still check the complete source cones.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GridLocalCuts( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                               Vec_Int_t * constants, Vec_Int_t * products, int Width )
{
    Vec_Int_t * depths = NULL, * cut = NULL, * v; Gia_Obj_t * o;
    int bound, side, i, j, id, lit, step, size, value, fanin, status, result = -1;
    if ( !m || !outputs || !terms || !constants || !products || Width < 1 || Width > 512 ||
         Width > m->Pars.nMaxWidth || Vec_IntSize(outputs) > 2048 || Vec_IntSize(terms) > 2048 ||
         Vec_IntSize(products) > 4096 || (Vec_IntSize(outputs) & 1) || (Vec_IntSize(terms) & 1) ||
         Vec_IntSize(products) % 4 || Acec2_Stopped(m) ) return -1;
    for ( side = 0; side < 3; side++ )
    {
        v = side == 2 ? products : side ? terms : outputs; step = side == 2 ? 4 : 2;
        for ( i = 0; i < Vec_IntSize(v); i += step )
            for ( j = 0; j < 1+(side == 2); j++ )
            {
                lit = Vec_IntEntry(v, i+j);
                if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ) return -1;
            }
    }
    depths = Vec_IntStartFull(Gia_ManObjNum(m->pGia)); cut = Vec_IntAlloc(100);
    for ( bound = 2; bound <= 32 && !Acec2_Stopped(m); bound *= 2 )
    {
        Vec_IntFill(depths, Gia_ManObjNum(m->pGia), -1); Vec_IntClear(cut); size = 0;
        for ( side = 0; side < 3; side++ )
        {
            v = side == 2 ? products : side ? terms : outputs; step = side == 2 ? 4 : 2;
            for ( i = 0; i < Vec_IntSize(v); i += step )
                for ( j = 0; j < 1+(side == 2); j++ ) Vec_IntWriteEntry(depths, Vec_IntEntry(v, i+j) >> 1, bound);
        }
        for ( id = Gia_ManObjNum(m->pGia)-1; id > 0; id-- )
        {
            if ( !(id & 255) && Acec2_Stopped(m) ) goto finish;
            value = Vec_IntEntry(depths, id); if ( value < 0 ) continue;
            if ( ++size > 4096 ) { m->nGridLocalLimits++; goto finish; }
            o = Gia_ManObj(m->pGia, id);
            if ( !value || Gia_ObjIsCi(o) ) { Vec_IntPush(cut, 2*id); continue; }
            if ( !Gia_ObjIsAnd(o) ) goto finish;
            for ( j = 0; j < 2+Gia_ObjIsMux(m->pGia, o); j++ )
            {
                fanin = j == 2 ? Gia_ObjFaninId2(m->pGia, id) : j ? Gia_ObjFaninId1(o, id) : Gia_ObjFaninId0(o, id);
                if ( Vec_IntEntry(depths, fanin) < value-1 ) Vec_IntWriteEntry(depths, fanin, value-1);
            }
        }
        m->nGridLocalChecks++;
        status = Acec2_ProveWeightedCut(m, outputs, terms, constants, products, cut, Width);
        m->nGridLocalLimits += status < 0;
        if ( m->Pars.fVerbose ) Abc_Print(1, "Product-grid local cut: depth = %d, cone = %d, inputs = %d, proof = %d.\n",
            bound, size, Vec_IntSize(cut), status);
        if ( status == 1 ) { m->nGridLocalProved++; result = 1; break; }
    }
finish:
    Vec_IntFreeP(&depths); Vec_IntFreeP(&cut); return Acec2_Stopped(m) ? -1 : result;
}

/**Function*************************************************************

  Synopsis    [Reuses completed grid-gap proofs and exhausted fixed recipes.]

  Description [Only a concrete counterexample rejects the source identity.
  Unknown results depend on the recipe and append-only rule generation.
  A deadline or cancellation never installs a cache result.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveGridRunBase( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                                 Vec_Int_t * constants, Vec_Int_t * products, Vec_Int_t * cut, int Width, int fQuick, int fPartition )
{
    int id, status, i, same = 1, generation[6];
    if ( Acec2_Stopped(m) ) return -1;
    id = Acec2_GridProofKey(m, outputs, terms, constants, products, cut, Width);
    generation[0] = Vec_PtrSize(m->vCells); generation[1] = Vec_PtrSize(m->vAlternatives);
    generation[2] = Vec_IntSize(m->vXors); generation[3] = Vec_IntSize(m->vVanish);
    generation[4] = m->vExtraRules ? Vec_IntSize(m->vExtraRules) : 0; generation[5] = Vec_PtrSize(m->vCounters);
    if ( id >= 0 )
    {
        status = Vec_IntEntry(m->vGridProofs, 8*id);
        for ( i = 0; i < 6; i++ ) same &= generation[i] == Vec_IntEntry(m->vGridProofs, 8*id+i+1);
        if ( status == 1 || status == 2 || (status == 3+fQuick+2*fPartition && same) )
        {
            m->nGridProofHits++; m->fWeightedTruth = Vec_IntEntry(m->vGridProofs, 8*id+7);
            return status == 2 ? 0 : status >= 3 ? -1 : 1;
        }
    }
    m->fWeightedTruth = 0;
    status = fPartition ? Acec2_GridChains(m, outputs, terms, constants, products, Width) : -1;
    if ( fPartition && status != 1 && !Acec2_Stopped(m) )
        status = Acec2_GridPartition(m, outputs, terms, constants, products, Width);
    if ( status != 1 && !Acec2_Stopped(m) )
    {
        m->fWeightedTruth = 0;
        status = fQuick ? Acec2_PolyWeightedQuick(m, outputs, terms, constants, products, Width) :
                         Acec2_PolyWeighted(m, outputs, terms, constants, products, Width);
    }
    if ( status != 1 && !Acec2_Stopped(m) ) status = Acec2_ProveWeightedCut(m, outputs, terms, constants, products, cut, Width);
    if ( !fQuick && status != 1 && !Acec2_Stopped(m) ) status = Acec2_GridLocalCuts(m, outputs, terms, constants, products, Width);
    // A free-cut counterexample can violate a source correlation.
    if ( status != 1 && !Acec2_Stopped(m) ) status = Acec2_ProveWeightedProducts(m, outputs, terms, constants, products, Width);
    if ( Acec2_Stopped(m) ) return -1;
    if ( id >= 0 )
    {
        Vec_IntWriteEntry(m->vGridProofs, 8*id, status == 1 ? 1 : status == 0 ? 2 : 3+fQuick+2*fPartition);
        for ( i = 0; i < 6; i++ ) Vec_IntWriteEntry(m->vGridProofs, 8*id+i+1, generation[i]);
        Vec_IntWriteEntry(m->vGridProofs, 8*id+7, m->fWeightedTruth);
    }
    return status;
}

/**Function*************************************************************

  Synopsis    [Checks one obligation without recursively splitting it.]

  Description [Completed certificates are shared across proof recipes.
  Deterministic failures distinguish split, ordinary and quick attempts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveGridRunInt( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                                Vec_Int_t * constants, Vec_Int_t * products, Vec_Int_t * cut, int Width, int fQuick )
{
    return Acec2_ProveGridRunBase(m, outputs, terms, constants, products, cut, Width, fQuick, 0);
}

/**Function*************************************************************

  Synopsis    [Proposes one parity step with an optional implicit carry.]

  Description [Only discovery uses signatures. A shared work counter bounds
  all combinations, and occurrence IDs preserve repeated weighted terms.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ChainStep( Vec_Int_t * column, Vec_Wrd_t * values, Vec_Bit_t * used,
                           word Target, int fCarry, word Carry, int * chosen, word * next, int * work )
{
    int i, j, k, a, b, c; word x, y, z, want = Target ^ (fCarry ? Carry : 0);
    for ( i = 0; i < Vec_IntSize(column); i++ )
    {
        a = Vec_IntEntry(column, i); if ( Vec_BitEntry(used, a) ) continue;
        x = Vec_WrdEntry(values, a);
        if ( ++*work > 262144 ) return 0;
        if ( fCarry && x == want ) { chosen[0] = a; *next = x & Carry; return 1; }
        for ( j = i+1; j < Vec_IntSize(column); j++ )
        {
            b = Vec_IntEntry(column, j); if ( Vec_BitEntry(used, b) ) continue;
            y = Vec_WrdEntry(values, b); if ( ++*work > 262144 ) return 0;
            if ( (x ^ y) == want )
            { chosen[0] = a; chosen[1] = b; *next = (x & y) | (fCarry ? Carry & (x | y) : 0); return 2; }
            if ( fCarry ) continue;
            for ( k = j+1; k < Vec_IntSize(column); k++ )
            {
                c = Vec_IntEntry(column, k); if ( Vec_BitEntry(used, c) ) continue;
                z = Vec_WrdEntry(values, c); if ( ++*work > 262144 ) return 0;
                if ( (x ^ y ^ z) != want ) continue;
                chosen[0] = a; chosen[1] = b; chosen[2] = c; *next = (x & y) | (x & z) | (y & z); return 3;
            }
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Appends exact term occurrences selected for a chain proof.]

  Description [Private product expressions remain literal pairs, never
  fabricated source nodes. Constants retain their individual multiplicity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ChainTerms( Vec_Int_t * entries, Vec_Int_t * ids, Vec_Int_t ** parts )
{
    int i, id, kind, a, b, rank, phase;
    Vec_IntForEachEntry(ids, id, i)
    {
        kind = Vec_IntEntry(entries, 5*id); a = Vec_IntEntry(entries, 5*id+1);
        b = Vec_IntEntry(entries, 5*id+2); rank = Vec_IntEntry(entries, 5*id+3); phase = Vec_IntEntry(entries, 5*id+4);
        if ( kind == 0 ) Vec_IntPushTwo(parts[1], a, rank);
        else if ( kind == 1 ) Vec_IntPush(parts[2], rank);
        else { Vec_IntPushTwo(parts[3], a, b); Vec_IntPushTwo(parts[3], rank, phase); }
        if ( kind != 1 && a > 1 ) Vec_IntPush(parts[4], a & ~1);
        if ( kind == 2 && b > 1 ) Vec_IntPush(parts[4], b & ~1);
    }
    Vec_IntUniqify(parts[4]);
}

/**Function*************************************************************

  Synopsis    [Closes carry chains without requiring intermediate carry nodes.]

  Description [A parity step proposes an implicit AND/majority carry. The
  chain continues through adjacent columns until it reaches a source output
  or the modular top column. The entire weighted boundary is then checked
  exactly; no simulated carry is admitted as a source equality. Successful
  chains and the remaining occurrences form a disjoint partition, and every
  part must be proved before this routine returns success.]

  SideEffects [Counts bounded discovery and completed chain certificates.]

  SeeAlso     []

***********************************************************************/
static int Acec2_GridChains( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                            Vec_Int_t * constants, Vec_Int_t * products, int Width )
{
    Vec_Int_t * entries = NULL, * selected = NULL, * roots = NULL, * parts[5] = {NULL, NULL, NULL, NULL, NULL}, * col;
    Vec_Wec_t * left = NULL, * right = NULL;
    Vec_Wrd_t * values = NULL, * sums = NULL; Vec_Bit_t * used = NULL, * taken = NULL, * trial = NULL;
    int n = Vec_IntSize(terms)/2+Vec_IntSize(constants)+Vec_IntSize(products)/4, nr = Vec_IntSize(outputs)/2;
    int i, j, k, rank, start, target, first, a, b, phase, kind, count, chosen[3], steps, found, landed, work = 0, attempts = 0, proved = 0, result = -1;
    word x, y, carry, next;
    if ( Width < 2 || Width > 64 || nr < 2 || n < 3 || n > 2048 || nr > 2048 ||
         Acec2_Stopped(m) || !Acec2_GapSimulate(m) ) return -1;
    entries = Vec_IntAlloc(5*n); values = Vec_WrdAlloc(n); sums = Vec_WrdAlloc(nr);
    left = Vec_WecStart(Width); right = Vec_WecStart(Width);
    used = Vec_BitStart(n); taken = Vec_BitStart(nr); selected = Vec_IntAlloc(64); roots = Vec_IntAlloc(32);
    for ( i = 0; i < 5; i++ ) parts[i] = Vec_IntAlloc(64);
    for ( kind = 0; kind < 3; kind++ )
    {
        count = kind == 0 ? Vec_IntSize(terms)/2 : kind == 1 ? Vec_IntSize(constants) : Vec_IntSize(products)/4;
        for ( i = 0; i < count; i++ )
        {
            a = kind == 0 ? Vec_IntEntry(terms, 2*i) : kind == 1 ? 1 : Vec_IntEntry(products, 4*i);
            b = kind == 2 ? Vec_IntEntry(products, 4*i+1) : 0;
            rank = kind == 0 ? Vec_IntEntry(terms, 2*i+1) : kind == 1 ? Vec_IntEntry(constants, i) : Vec_IntEntry(products, 4*i+2);
            phase = kind == 2 ? Vec_IntEntry(products, 4*i+3) : 0;
            if ( rank < 0 || rank >= Width || a < 0 || b < 0 || (a >> 1) >= Gia_ManObjNum(m->pGia) || (b >> 1) >= Gia_ManObjNum(m->pGia) ) goto finish;
            x = Vec_WrdEntry(m->vGapSim, a >> 1); if ( a & 1 ) x = ~x;
            if ( kind == 2 ) { y = Vec_WrdEntry(m->vGapSim, b >> 1); if ( b & 1 ) y = ~y; x &= y; if ( phase ) x = ~x; }
            Vec_WecPush(right, rank, Vec_WrdSize(values)); Vec_WrdPush(values, x);
            Vec_IntPushTwo(entries, kind, a); Vec_IntPushThree(entries, b, rank, phase);
        }
    }
    for ( i = 0; i < nr; i++ )
    {
        a = Vec_IntEntry(outputs, 2*i); rank = Vec_IntEntry(outputs, 2*i+1);
        if ( rank < 0 || rank >= Width || a < 0 || (a >> 1) >= Gia_ManObjNum(m->pGia) ) goto finish;
        x = Vec_WrdEntry(m->vGapSim, a >> 1); if ( a & 1 ) x = ~x;
        Vec_WrdPush(sums, x); Vec_WecPush(left, rank, i);
    }
    for ( start = 0; start < Width && work < 262144 && attempts < 8 && !Acec2_Stopped(m); start++ )
    Vec_IntForEachEntry(Vec_WecEntry(left, start), first, j)
    {
        if ( Vec_BitEntry(taken, first) ) continue;
        if ( work >= 262144 || attempts == 8 || Acec2_Stopped(m) ) break;
        trial = Vec_BitDup(used); Vec_IntClear(selected); Vec_IntClear(roots); landed = 0; carry = 0; steps = 0;
        for ( rank = start; rank < Width && steps < 16 && work < 262144; rank++ )
        {
            if ( Acec2_Stopped(m) ) break;
            col = Vec_WecEntry(left, rank); found = 0;
            Vec_IntForEachEntry(col, target, i)
            {
                if ( Vec_BitEntry(taken, target) || (!steps && target != first) ) continue;
                if ( steps && Vec_WrdEntry(sums, target) == carry ) { Vec_IntPush(roots, target); landed = 1; break; }
                count = Acec2_ChainStep(Vec_WecEntry(right, rank), values, trial, Vec_WrdEntry(sums, target), steps > 0, carry, chosen, &next, &work);
                if ( !count ) continue;
                Vec_IntPush(roots, target);
                for ( k = 0; k < count; k++ ) { Acec2_BitWrite(trial, chosen[k], 1); Vec_IntPush(selected, chosen[k]); }
                carry = next; steps++; found = 1; break;
            }
            if ( landed || !found ) break;
            if ( rank == Width-1 ) landed = 1;
        }
        if ( !landed && steps == 16 ) m->nGridChainLimits++;
        if ( landed && steps >= 2 )
        {
            for ( i = 0; i < 5; i++ ) Vec_IntClear(parts[i]);
            Vec_IntForEachEntry(roots, target, i) Vec_IntPushTwo(parts[0], Vec_IntEntry(outputs, 2*target), Vec_IntEntry(outputs, 2*target+1));
            Acec2_ChainTerms(entries, selected, parts); attempts++; m->nGridChainAttempts++;
            if ( Acec2_ProveGridRunInt(m, parts[0], parts[1], parts[2], parts[3], parts[4], Width, 1) == 1 )
            {
                Vec_IntForEachEntry(selected, target, i) Acec2_BitWrite(used, target, 1);
                Vec_IntForEachEntry(roots, target, i) Acec2_BitWrite(taken, target, 1);
                proved++; m->nGridChainProved++; m->nGridChainSteps += steps;
            }
        }
        Vec_BitFreeP(&trial);
    }
    if ( !proved || Acec2_Stopped(m) ) goto finish;
    for ( i = 0; i < 5; i++ ) Vec_IntClear(parts[i]);
    for ( i = 0; i < nr; i++ ) if ( !Vec_BitEntry(taken, i) ) Vec_IntPushTwo(parts[0], Vec_IntEntry(outputs, 2*i), Vec_IntEntry(outputs, 2*i+1));
    Vec_IntClear(selected); for ( i = 0; i < n; i++ ) if ( !Vec_BitEntry(used, i) ) Vec_IntPush(selected, i);
    Acec2_ChainTerms(entries, selected, parts);
    result = Acec2_ProveGridRunInt(m, parts[0], parts[1], parts[2], parts[3], parts[4], Width, 0);
    if ( result == 1 ) m->fWeightedTruth = 0;
finish:
    m->nGridChainWork += work;
    if ( work > 262144 || attempts == 8 ) m->nGridChainLimits++;
    Vec_IntFreeP(&entries); Vec_IntFreeP(&selected); Vec_IntFreeP(&roots);
    Vec_WecFreeP(&left); Vec_WecFreeP(&right); Vec_WrdFreeP(&values); Vec_WrdFreeP(&sums);
    Vec_BitFreeP(&used); Vec_BitFreeP(&taken); Vec_BitFreeP(&trial);
    for ( i = 0; i < 5; i++ ) Vec_IntFreeP(&parts[i]);
    return Acec2_Stopped(m) ? -1 : result;
}

/**Function*************************************************************

  Synopsis    [Certifies connected pieces of a weighted source obligation.]

  Description [Stop connectivity walks at checked cell outputs and the
  obligation's own endpoints. Shared primary inputs alone do not join pieces.
  Simulation proposes constant pieces; every selected piece and the combined
  remainder still need completed exact source proofs. Each original term
  occurs in exactly one piece, including explicit products without gate nodes.
  Constant corrections sum to the original correction modulo the same width.
  Failure of a piece rejects only the partition, never the original identity.]

  SideEffects [Uses private source traversal arrays and the exact proof cache.]

  SeeAlso     []

***********************************************************************/
static int Acec2_GridPartition( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                               Vec_Int_t * constants, Vec_Int_t * products, int Width )
{
    Gia_Man_t * g = m->pGia; Gia_Obj_t * o; Acec2_Cell_t * cell;
    Vec_Int_t * entries = NULL, * parents = NULL, * owner = NULL, * seen = NULL, * stack = NULL, * groups = NULL;
    Vec_Int_t * sizes = NULL, * chosen = NULL, * pieces[5] = {NULL, NULL, NULL, NULL, NULL}, * v;
    Vec_Wec_t * frontiers = NULL; Vec_Bit_t * stops = NULL; Vec_Wrd_t * samples = NULL;
    int i, j, k, n, node, root, other, kind, rank, lit, group, count = 0, rest = 0, work = 0, result = -1;
    word mask, pattern, value, scale, correction = 0, selected = 0, expected;
    if ( Width < 1 || Width > 64 || (Vec_IntSize(outputs) & 1) || (Vec_IntSize(terms) & 1) ||
         (Vec_IntSize(products) & 3) || Acec2_Stopped(m) ) return -1;
    if ( (ABC_INT64_T)Vec_IntSize(outputs)/2+Vec_IntSize(terms)/2+Vec_IntSize(products)/4 > 2048 )
    { m->nGridPartitionLimits++; return -1; }
    n = Vec_IntSize(outputs)/2+Vec_IntSize(terms)/2+Vec_IntSize(products)/4;
    if ( n < 16 ) return -1;
    entries = Vec_IntAlloc(4*n);
    for ( kind = 0; kind < 3; kind++ )
    {
        v = kind == 0 ? outputs : kind == 1 ? terms : products;
        for ( i = 0; i < Vec_IntSize(v); i += kind == 2 ? 4 : 2 )
        {
            rank = Vec_IntEntry(v, i+(kind == 2 ? 2 : 1));
            if ( rank < 0 || rank >= Width || (kind == 2 && (Vec_IntEntry(v, i+3) & ~1)) ) goto finish;
            for ( j = 0; j <= (kind == 2); j++ )
            {
                lit = Vec_IntEntry(v, i+j);
                if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(g) || Gia_ObjIsCo(Gia_ManObj(g, lit >> 1)) ) goto finish;
            }
            Vec_IntPushTwo(entries, kind == 2 ? 2+Vec_IntEntry(v, i+3) : kind, Vec_IntEntry(v, i));
            Vec_IntPushTwo(entries, kind == 2 ? Vec_IntEntry(v, i+1) : 0, rank);
        }
    }
    Vec_IntForEachEntry(constants, rank, i)
    {
        if ( rank < 0 || rank >= Width ) goto finish;
        correction += (word)1 << rank;
    }
    m->nGridPartitionAttempts++;
    parents = Vec_IntAlloc(n); owner = Vec_IntStartFull(Gia_ManObjNum(g)); seen = Vec_IntStart(Gia_ManObjNum(g));
    stack = Vec_IntAlloc(64); stops = Vec_BitStart(Gia_ManObjNum(g)); frontiers = Vec_WecStart(n);
    for ( i = 0; i < n; i++ ) Vec_IntPush(parents, i);
    for ( i = 0; i < n; i++ )
        if ( Vec_IntEntry(entries, 4*i) < 2 )
        {
            node = Vec_IntEntry(entries, 4*i+1) >> 1; Acec2_BitWrite(stops, node, 1);
            other = Vec_IntEntry(owner, node);
            if ( other < 0 ) Vec_IntWriteEntry(owner, node, i);
            else Vec_IntWriteEntry(parents, Acec2_WeightFind(Vec_IntArray(parents), NULL, NULL, i), Acec2_WeightFind(Vec_IntArray(parents), NULL, NULL, other));
        }
    Vec_PtrForEachEntry(Acec2_Cell_t *, m->vCells, cell, i)
        for ( j = 0; j < 2; j++ ) Acec2_BitWrite(stops, cell->Out[j] >> 1, 1);
    for ( i = 0; i < n; i++ )
    {
        root = Vec_IntEntry(entries, 4*i+1) >> 1; kind = Vec_IntEntry(entries, 4*i);
        Vec_IntClear(stack); Vec_IntPush(stack, root);
        if ( kind >= 2 ) Vec_IntPush(stack, Vec_IntEntry(entries, 4*i+2) >> 1);
        while ( Vec_IntSize(stack) )
        {
            if ( ++work > 131072 ) { m->nGridPartitionLimits++; goto finish; }
            if ( (work & 255) == 0 && Acec2_Stopped(m) ) goto finish;
            node = Vec_IntPop(stack);
            if ( !node || Vec_IntEntry(seen, node) == i+1 ) continue;
            Vec_IntWriteEntry(seen, node, i+1); o = Gia_ManObj(g, node);
            // A primary input joins a piece only when it is itself a
            // weighted endpoint, not merely a shared free support signal.
            other = Vec_IntEntry(owner, node);
            if ( !Gia_ObjIsCi(o) || other >= 0 )
            {
                if ( other < 0 ) Vec_IntWriteEntry(owner, node, i);
                else Vec_IntWriteEntry(parents, Acec2_WeightFind(Vec_IntArray(parents), NULL, NULL, i), Acec2_WeightFind(Vec_IntArray(parents), NULL, NULL, other));
            }
            if ( kind >= 2 || Gia_ObjIsCi(o) || (node != root && Vec_BitEntry(stops, node)) )
            { Vec_IntPush(Vec_WecEntry(frontiers, i), 2*node); continue; }
            if ( Gia_ObjIsBuf(o) ) Vec_IntPush(stack, Gia_ObjFaninId0(o, node));
            else if ( Gia_ObjIsAnd(o) )
            {
                Vec_IntPushTwo(stack, Gia_ObjFaninId0(o, node), Gia_ObjFaninId1(o, node));
                if ( Gia_ObjIsMux(g, o) ) Vec_IntPush(stack, Gia_ObjFaninId2(g, node));
            }
            else goto finish;
        }
    }
    groups = Vec_IntStart(n); sizes = Vec_IntStart(n); chosen = Vec_IntStartFull(n);
    samples = Vec_WrdStart(64*n); mask = Width == 64 ? ~(word)0 : ((word)1 << Width)-1;
    if ( !Acec2_GapSimulate(m) ) goto finish;
    for ( i = 0; i < n; i++ )
    {
        if ( (i & 31) == 0 && Acec2_Stopped(m) ) goto finish;
        group = Acec2_WeightFind(Vec_IntArray(parents), NULL, NULL, i); Vec_IntWriteEntry(groups, i, group); Vec_IntAddToEntry(sizes, group, 1);
        kind = Vec_IntEntry(entries, 4*i); lit = Vec_IntEntry(entries, 4*i+1); rank = Vec_IntEntry(entries, 4*i+3);
        pattern = Vec_WrdEntry(m->vGapSim, lit >> 1); if ( lit & 1 ) pattern = ~pattern;
        if ( kind >= 2 )
        {
            lit = Vec_IntEntry(entries, 4*i+2); value = Vec_WrdEntry(m->vGapSim, lit >> 1); if ( lit & 1 ) value = ~value;
            pattern &= value; if ( kind & 1 ) pattern = ~pattern;
        }
        scale = (word)1 << rank; if ( kind ) scale = -scale;
        for ( k = 0; k < 64; k++ ) if ( (pattern >> k) & 1 )
            Vec_WrdWriteEntry(samples, 64*group+k, Vec_WrdEntry(samples, 64*group+k)+scale);
    }
    for ( i = 0; i < n; i++ )
    {
        if ( !Vec_IntEntry(sizes, i) ) continue;
        value = Vec_WrdEntry(samples, 64*i) & mask;
        for ( k = 1; k < 64 && !((Vec_WrdEntry(samples, 64*i+k)^value) & mask); k++ ) {}
        if ( k == 64 && count < 7 ) { Vec_IntWriteEntry(chosen, i, count++); selected += value; }
        else rest = 1;
    }
    if ( count+rest < 2 || (!rest && ((selected-correction) & mask)) ) goto finish;
    for ( i = 0; i < 5; i++ ) pieces[i] = Vec_IntAlloc(64);
    for ( j = 0; j < count+rest; j++ )
    {
        for ( i = 0; i < 5; i++ ) Vec_IntClear(pieces[i]);
        expected = (correction-selected) & mask;
        for ( i = 0; i < n; i++ )
        {
            group = Vec_IntEntry(groups, i); other = Vec_IntEntry(chosen, group);
            if ( (other < 0 ? count : other) != j ) continue;
            if ( other >= 0 ) expected = Vec_WrdEntry(samples, 64*group) & mask;
            kind = Vec_IntEntry(entries, 4*i); lit = Vec_IntEntry(entries, 4*i+1); rank = Vec_IntEntry(entries, 4*i+3);
            if ( kind < 2 ) Vec_IntPushTwo(pieces[kind], lit, rank);
            else { Vec_IntPushTwo(pieces[3], lit, Vec_IntEntry(entries, 4*i+2)); Vec_IntPushTwo(pieces[3], rank, kind & 1); }
            Vec_IntAppend(pieces[4], Vec_WecEntry(frontiers, i));
        }
        for ( rank = 0; rank < Width; rank++ ) if ( (expected >> rank) & 1 ) Vec_IntPush(pieces[2], rank);
        Vec_IntUniqify(pieces[4]); m->nGridPartitionParts++;
        other = Acec2_ProveGridRunInt(m, pieces[0], pieces[1], pieces[2], pieces[3], pieces[4], Width, 0);
        if ( m->Pars.fVerbose ) Abc_Print(1, "Product-grid partition %d/%d: terms = %d/%d, products = %d, proof = %d.\n",
            j+1, count+rest, Vec_IntSize(pieces[0])/2, Vec_IntSize(pieces[1])/2, Vec_IntSize(pieces[3])/4, other);
        if ( other != 1 || Acec2_Stopped(m) ) goto finish;
    }
    m->nGridPartitionProved++; m->fWeightedTruth = 0; result = 1;
finish:
    m->nGridPartitionWork += work;
    Vec_IntFreeP(&entries); Vec_IntFreeP(&parents); Vec_IntFreeP(&owner); Vec_IntFreeP(&seen); Vec_IntFreeP(&stack);
    Vec_IntFreeP(&groups); Vec_IntFreeP(&sizes); Vec_IntFreeP(&chosen); Vec_WecFreeP(&frontiers); Vec_BitFreeP(&stops); Vec_WrdFreeP(&samples);
    for ( i = 0; i < 5; i++ ) Vec_IntFreeP(&pieces[i]);
    return Acec2_Stopped(m) ? -1 : result;
}

/**Function*************************************************************

  Synopsis    [Checks a complete run with its original bounded proof recipe.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveGridRun( Acec2_Man_t * m, Vec_Int_t * outputs, Vec_Int_t * terms,
                                Vec_Int_t * constants, Vec_Int_t * products, Vec_Int_t * cut, int Width )
{
    return Acec2_ProveGridRunBase(m, outputs, terms, constants, products, cut, Width, 0, 1);
}

/**Function*************************************************************

  Synopsis    [Retains exact low bits of an unfinished column-run proof.]

  Description [Higher-rank terms vanish modulo the smaller width. Every
  accepted prefix has its own completed source proof; simulation supplies
  only the proposed constant. The accumulated correction must vanish in
  all retained bits. At most eight new widths are attempted, using a small
  fixed polynomial pass followed by ordinary bounded Boolean checks.
  Completed source proofs share the full-run cache; effort limits retain
  their recipe.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GridLowPrefix( Acec2_Man_t * m, Vec_Int_t ** selected, Vec_Int_t * constants,
                                 Vec_Int_t * cut, int Start, int End, word Correction )
{
    Vec_Int_t * low[3], * bias = Vec_IntAlloc(32);
    int prefix, side, slot, pos, step, result, rank, proved = 0, attempts = 0, hits;
    for ( side = 0; side < 3; side++ ) low[side] = Vec_IntAlloc(100);
    for ( prefix = Start+1; prefix <= End && !Acec2_Stopped(m); prefix++ )
    {
        if ( attempts == 8 ) { m->nGridLowLimits++; break; }
        for ( side = 0; side < 3; side++ )
        {
            Vec_IntClear(low[side]); step = side == 2 ? 4 : 2;
            for ( slot = 0; slot < Vec_IntSize(selected[side]); slot += step )
                if ( Vec_IntEntry(selected[side], slot+(side == 2 ? 2 : 1)) < prefix )
                    for ( pos = 0; pos < step; pos++ ) Vec_IntPush(low[side], Vec_IntEntry(selected[side], slot+pos));
        }
        Vec_IntClear(bias);
        Vec_IntForEachEntry(constants, pos, slot) if ( pos < prefix ) Vec_IntPush(bias, pos);
        m->nGridLowAttempts++;
        hits = m->nGridProofHits;
        result = Acec2_ProveGridRunInt(m, low[0], low[1], bias, low[2], cut, prefix, 1);
        attempts += hits == m->nGridProofHits;
        m->nGridLowLimits += result < 0;
        if ( m->Pars.fVerbose ) Abc_Print(1, "Product-grid partial run %d..%d: width = %d, proof = %d.\n", Start, End, prefix, result);
        if ( result != 1 ) break;
        m->nGridLowProved++;
        for ( rank = 0; rank < prefix && !((Correction >> rank) & 1); rank++ ) {}
        proved = Abc_MaxInt(proved, rank);
    }
    for ( side = 0; side < 3; side++ ) Vec_IntFree(low[side]);
    Vec_IntFree(bias); return Acec2_Stopped(m) ? 0 : proved;
}

/**Function*************************************************************

  Synopsis    [Certifies a sum of grids using a checked region and its gaps.]

  Description [For the region identity O=T+B, shifted into product columns,
  the remaining obligation is Y+T+B=O+sum(P). Identical physical terms cancel.
  Missing products are explicit literal pairs in the private proof graph.
  Column runs are proposed by simulation and proved independently; their
  constant corrections must sum to zero at the requested modulus. The
  parent identity's shifted modulus bounds every retained prefix; it is
  never widened to the proposed product width.]

  SideEffects [Updates proof counters without changing source gates.]

  SeeAlso     []

***********************************************************************/
int Acec2_ProveGridExpression( Acec2_Man_t * m, int Record, Vec_Ptr_t * products, Vec_Int_t * vOutputs,
                              int Width, int Offset, int * pPrefix )
{
    Acec2_Record_t * r; Acec2_Product_t * product; Vec_Wec_t * cols[3] = {NULL, NULL, NULL};
    Vec_Int_t * terms[3] = {NULL, NULL, NULL}, * selected[3] = {NULL, NULL, NULL}, * v, * key = NULL, * constants = NULL, * cut = NULL;
    word values[64], mask, pattern, correction, total = 0, scale;
    int i, j, k, index, side, a, b, lit, rank, shift = Offset, width, requested = Width, neg, start, end, status, proofs = 0, result = -1;
    if ( !pPrefix ) return -1;
    *pPrefix = 0;
    if ( !m || !products || !Vec_PtrSize(products) || Vec_PtrSize(products) > 8 || !vOutputs ||
         (Vec_IntSize(vOutputs) & 1) || Record < 0 || Record >= Vec_PtrSize(m->vRecords) || Acec2_Stopped(m) ) return -1;
    r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Record);
    if ( Offset < 0 || Offset > 64 || requested < 2 || requested > 64 ||
         requested > m->Pars.nMaxWidth || r->Word >= 0 || r->Proof || r->Compose || r->Extend ||
         r->vOutputMasks || r->pProductReference ) return -1;
    if ( !Acec2_RecordCheck(m, r) ) return -1;
    width = Abc_MinInt(requested, Abc_MinInt(requested, r->Width)+shift);
    if ( width < 2 ) return -1;
    for ( i = 0; i < Vec_IntSize(vOutputs); i += 2 )
    {
        lit = Vec_IntEntry(vOutputs, i); rank = Vec_IntEntry(vOutputs, i+1);
        if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) || rank < 0 || rank >= requested ) return -1;
    }
    Vec_PtrForEachEntry(Acec2_Product_t *, products, product, index)
    for ( side = 0; side < 2; side++ )
    {
        if ( !product ) return -1;
        if ( product->Shift < -Offset || product->Shift > 64 || (product->fNeg & ~1) ) return -1;
        v = product->vOperands[side];
        if ( !v || Vec_IntSize(v) < 2 || Vec_IntSize(v) > 64 || (product->fSigned[side] & ~1) ) return -1;
        Vec_IntForEachEntry(v, lit, i)
            if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ) return -1;
    }
    m->nGridAttempts++; mask = width == 64 ? ~(word)0 : ((word)1 << width)-1;
    key = Vec_IntAlloc(4); constants = Vec_IntAlloc(64); cut = Vec_IntAlloc(64);
    for ( side = 0; side < 3; side++ ) { terms[side] = Vec_IntAlloc(64); selected[side] = Vec_IntAlloc(64); cols[side] = Vec_WecStart(width); }
    for ( i = 0; i < Vec_IntSize(vOutputs); i += 2 )
        if ( Vec_IntEntry(vOutputs, i+1) < width ) Vec_IntPushTwo(terms[0], Vec_IntEntry(vOutputs, i), Vec_IntEntry(vOutputs, i+1));
    for ( side = 0; side < 2; side++ )
    {
        v = side ? r->vOutputs : r->vTerms;
        for ( i = 0; i < Vec_IntSize(v); i += 2 )
            if ( (rank = Vec_IntEntry(v, i+1)+shift) < width ) Vec_IntPushTwo(terms[side], Vec_IntEntry(v, i), rank);
    }
    Vec_IntForEachEntry(r->vConstants, rank, i) if ( rank+shift < width ) Vec_IntPushTwo(terms[0], 1, rank+shift);
    Vec_PtrForEachEntry(Acec2_Product_t *, products, product, index)
    for ( i = 0; i < Vec_IntSize(product->vOperands[0]); i++ )
        for ( j = 0; j < Vec_IntSize(product->vOperands[1]) && i+j < width; j++ )
        {
            rank = i+j+product->Shift+Offset; if ( rank >= width ) continue;
            a = Vec_IntEntry(product->vOperands[0], i); b = Vec_IntEntry(product->vOperands[1], j);
            neg = product->fNeg ^ (product->fSigned[0] && i+1 == Vec_IntSize(product->vOperands[0])) ^
                  (product->fSigned[1] && j+1 == Vec_IntSize(product->vOperands[1]));
            lit = Acec2_GapProductNode(m, a, b, key);
            if ( lit >= 0 ) Vec_IntPushTwo(terms[1], lit ^ neg, rank);
            else { Vec_IntPushTwo(terms[2], a, b); Vec_IntPushTwo(terms[2], rank, neg); }
            if ( neg ) Vec_IntPushTwo(terms[0], 1, rank);
        }
    if ( !Acec2_GapSimulate(m) ) goto finish;
    // Cancel occurrences, not node membership: sharing can use a term twice.
    for ( i = 0; i < Vec_IntSize(terms[0]); i += 2 )
    {
        if ( (i & 127) == 0 && Acec2_Stopped(m) ) goto finish;
        for ( j = 0; j < Vec_IntSize(terms[1]); j += 2 )
            if ( Vec_IntEntry(terms[0], i) >= 0 && Vec_IntEntry(terms[0], i) == Vec_IntEntry(terms[1], j) &&
                 Vec_IntEntry(terms[0], i+1) == Vec_IntEntry(terms[1], j+1) )
            { Vec_IntWriteEntry(terms[0], i, -1); Vec_IntWriteEntry(terms[1], j, -1); break; }
    }
    for ( side = 0; side < 3; side++ )
        for ( i = 0; i < Vec_IntSize(terms[side]); i += side == 2 ? 4 : 2 )
            if ( Vec_IntEntry(terms[side], i) >= 0 && (side == 2 || Vec_IntEntry(terms[side], i) != 0) )
                Vec_WecPush(cols[side], Vec_IntEntry(terms[side], i+(side == 2 ? 2 : 1)), i);
    for ( start = 0; start < width && !Acec2_Stopped(m); start++ )
    {
        if ( !Vec_IntSize(Vec_WecEntry(cols[0], start)) && !Vec_IntSize(Vec_WecEntry(cols[1], start)) &&
             !Vec_IntSize(Vec_WecEntry(cols[2], start)) )
        {
            for ( rank = 0; rank <= start && !((total >> rank) & 1); rank++ ) {}
            *pPrefix = rank; continue;
        }
        memset(values, 0, sizeof(values));
        for ( side = 0; side < 3; side++ ) Vec_IntClear(selected[side]);
        for ( end = start; end < width && !Acec2_Stopped(m); end++ )
        {
            for ( side = 0; side < 3; side++ )
            {
                scale = (word)1 << end; if ( side ) scale = -scale;
                Vec_IntForEachEntry(Vec_WecEntry(cols[side], end), j, i)
                {
                    v = terms[side]; lit = Vec_IntEntry(v, j);
                    pattern = Vec_WrdEntry(m->vGapSim, lit >> 1); if ( lit & 1 ) pattern = ~pattern;
                    if ( side == 2 )
                    {
                        b = Vec_IntEntry(v, j+1); correction = Vec_WrdEntry(m->vGapSim, b >> 1); if ( b & 1 ) correction = ~correction;
                        pattern &= correction; if ( Vec_IntEntry(v, j+3) ) pattern = ~pattern;
                        Vec_IntPushTwo(selected[side], lit, b); Vec_IntPushTwo(selected[side], end, Vec_IntEntry(v, j+3));
                    }
                    else Vec_IntPushTwo(selected[side], lit, end);
                    for ( k = 0; k < 64; k++ ) if ( (pattern >> k) & 1 ) values[k] += scale;
                }
            }
            for ( k = 1; k < 64 && !((values[k]^values[0]) & mask); k++ ) {}
            if ( k != 64 ) continue;
            if ( proofs++ == 16 ) goto finish;
            correction = values[0] & mask; Vec_IntClear(constants);
            for ( rank = 0; rank < width; rank++ ) if ( (correction >> rank) & 1 ) Vec_IntPush(constants, rank);
            Vec_IntClear(cut);
            Vec_PtrForEachEntry(Acec2_Product_t *, products, product, index)
            for ( side = 0; side < 2; side++ ) Vec_IntForEachEntry(product->vOperands[side], lit, i)
                if ( lit >= 2 ) Vec_IntPush(cut, lit & ~1);
            for ( i = 0; i < Vec_IntSize(selected[1]); i += 2 )
                for ( j = 0; j < Vec_IntSize(r->vOutputs); j += 2 )
                    if ( (Vec_IntEntry(selected[1], i) >> 1) == (Vec_IntEntry(r->vOutputs, j) >> 1) && Vec_IntEntry(selected[1], i) >= 2 )
                    { Vec_IntPush(cut, Vec_IntEntry(selected[1], i) & ~1); break; }
            Vec_IntUniqify(cut);
            status = Acec2_ProveGridRun(m, selected[0], selected[1], constants, selected[2], cut, width);
            if ( m->Pars.fVerbose ) Abc_Print(1, "Product-grid columns %d..%d: boundary terms = %d/%d, explicit products = %d, proof = %d.\n",
                start, end, Vec_IntSize(selected[0])/2, Vec_IntSize(selected[1])/2, Vec_IntSize(selected[2])/4, status);
            if ( status != 1 )
            {
                rank = Acec2_GridLowPrefix(m, selected, constants, cut, start, end, total+correction);
                *pPrefix = Abc_MaxInt(*pPrefix, rank); result = status; goto finish;
            }
            total += correction;
            // Terms in later columns are zero modulo this prefix. Keep
            // only bits for which the accumulated exact correction vanishes.
            for ( rank = 0; rank <= end && !((total >> rank) & 1); rank++ ) {}
            *pPrefix = rank; break;
        }
        if ( end == width ) { result = 0; goto finish; }
        start = end;
    }
    if ( !Acec2_Stopped(m) ) result = (total & mask) ? 0 : width == requested ? 1 : -1;
finish:
    if ( Acec2_Stopped(m) ) { result = -1; *pPrefix = 0; }
    m->nGridProved += result == 1; m->nGridLimits += result < 0;
    m->nGridPrefixes += result != 1 && *pPrefix >= 4;
    for ( side = 0; side < 3; side++ ) { Vec_IntFreeP(&terms[side]); Vec_IntFreeP(&selected[side]); Vec_WecFreeP(&cols[side]); }
    Vec_IntFreeP(&key); Vec_IntFreeP(&constants); Vec_IntFreeP(&cut); return result;
}

/**Function*************************************************************

  Synopsis    [Checks one unshifted product using the shared grid-sum engine.]

  Description [The public product interface retains its ordered binary word
  and full operand-width requirement. The parent region may start above bit
  zero; its explicit offset limits the proof modulus.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveProductGridPrefix( Acec2_Man_t * m, int Record, Acec2_Product_t * product, Vec_Int_t * vOutputs, int * pPrefix )
{
    Vec_Ptr_t products; void * data[1]; Vec_Int_t * outputs; int i, result;
    if ( !pPrefix ) return -1;
    *pPrefix = 0;
    if ( !product || !product->vOperands[0] || !product->vOperands[1] || !vOutputs || product->Shift > 0 || product->Shift < -64 || product->fNeg ||
         Vec_IntSize(vOutputs) != Vec_IntSize(product->vOperands[0])+Vec_IntSize(product->vOperands[1]) ) return -1;
    data[0] = product; products.nSize = products.nCap = 1; products.pArray = data;
    outputs = Vec_IntAlloc(2*Vec_IntSize(vOutputs));
    for ( i = 0; i < Vec_IntSize(vOutputs); i++ ) Vec_IntPushTwo(outputs, Vec_IntEntry(vOutputs, i), i);
    result = Acec2_ProveGridExpression(m, Record, &products, outputs, Vec_IntSize(vOutputs), -product->Shift, pPrefix);
    Vec_IntFree(outputs); return result;
}

/**Function*************************************************************

  Synopsis    [Queues observed column-run identities for exact source proof.]

  Description [The proposed grid supplies ranks, not a certificate. Both
  boundaries retain their literal phases and multiplicities. Simulation
  only finds runs with a constant residual; the full modular source check
  must establish every identity before it enters the record database.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_GapGridRuns( Acec2_Man_t * m, Acec2_Record_t * r, Acec2_GapQueue_t * q,
                             Vec_Int_t * left, Vec_Int_t * right )
{
    Vec_Wec_t * cols[2] = {Vec_WecStart(r->Width), Vec_WecStart(r->Width)};
    Vec_Int_t * terms, * v, * selected[2] = {Vec_IntAlloc(32), Vec_IntAlloc(32)}, * key, * old, * constants;
    ABC_INT64_T values[64], scale; word pattern, correction;
    int side, i, j, k, rank, start, end, lit, closed;
    if ( Vec_IntSize(left)+Vec_IntSize(right) > 8192 || !Acec2_GapSimulate(m) ) goto finish;
    // Remove identical boundary occurrences before looking for a break.
    for ( i = 0; i < Vec_IntSize(left); i += 2 )
        for ( j = 0; j < Vec_IntSize(right); j += 2 )
            if ( Vec_IntEntry(left, i) >= 0 && Vec_IntEntry(left, i) == Vec_IntEntry(right, j) &&
                 Vec_IntEntry(left, i+1) == Vec_IntEntry(right, j+1) )
            { Vec_IntWriteEntry(left, i, -1); Vec_IntWriteEntry(right, j, -1); break; }
    for ( side = 0; side < 2; side++ )
    {
        terms = side ? right : left;
        for ( i = 0; i < Vec_IntSize(terms); i += 2 )
            if ( Vec_IntEntry(terms, i) >= 0 ) Vec_WecPush(cols[side], Vec_IntEntry(terms, i+1), Vec_IntEntry(terms, i));
    }
    for ( start = 0; start < r->Width && !Acec2_Stopped(m); start++ )
    {
        if ( !Vec_IntSize(Vec_WecEntry(cols[0], start)) && !Vec_IntSize(Vec_WecEntry(cols[1], start)) ) continue;
        memset(values, 0, sizeof(values)); Vec_IntClear(selected[0]); Vec_IntClear(selected[1]); closed = 0;
        for ( end = start; end < r->Width && end-start <= 48 && !Acec2_Stopped(m); end++ )
        {
            for ( side = 0; side < 2; side++ )
            {
                v = Vec_WecEntry(cols[side], end); scale = (ABC_INT64_T)1 << (end-start); if ( !side ) scale = -scale;
                Vec_IntForEachEntry(v, lit, i)
                {
                    Vec_IntPushTwo(selected[side], lit, end); pattern = Vec_WrdEntry(m->vGapSim, lit >> 1); if ( lit & 1 ) pattern = ~pattern;
                    for ( k = 0; k < 64; k++ ) if ( (pattern >> k) & 1 ) values[k] += scale;
                }
            }
            if ( !Vec_IntSize(selected[0]) || !Vec_IntSize(selected[1]) ) continue;
            m->nGapGroups++;
            for ( k = 1; k < 64 && values[k] == values[0]; k++ ) {}
            if ( k != 64 ) continue;
            correction = (word)(-values[0]); constants = Vec_IntAlloc(16);
            for ( rank = start; rank < r->Width; rank++ )
                if ( rank-start < 64 ? (correction >> (rank-start)) & 1 : values[0] > 0 ) Vec_IntPush(constants, rank);
            key = Vec_IntAlloc(32); Vec_IntPushTwo(key, r->Width, Vec_IntSize(selected[0]));
            Vec_IntPushTwo(key, Vec_IntSize(selected[1]), Vec_IntSize(constants));
            Vec_IntAppend(key, selected[0]); Vec_IntAppend(key, selected[1]); Vec_IntAppend(key, constants); Vec_IntFree(constants);
            Vec_WecForEachLevel(q->vCandidates, old, i) if ( Vec_IntEqual(old, key) ) break;
            if ( i == Vec_WecSize(q->vCandidates) )
            { Vec_IntAppend(Vec_WecPushLevel(q->vCandidates), key); m->nGapProposals++; }
            Vec_IntFree(key); closed = 1; break;
        }
        if ( Vec_WecSize(q->vCandidates) >= 32 ) { m->nGapLimits++; break; }
        if ( closed ) start = end;
    }
finish:
    Vec_WecFree(cols[0]); Vec_WecFree(cols[1]); Vec_IntFree(selected[0]); Vec_IntFree(selected[1]);
}

/**Function*************************************************************

  Synopsis    [Proposes missing grid products across a weighted boundary.]

  Description [Observed products infer operand order and a column offset.
  An absent physical product is reported, never invented as a source node.
  Primary output ordering is only an additional proposal for a result word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_GapGrids( Acec2_Man_t * m, Acec2_Record_t * r, Acec2_GapQueue_t * q )
{
    Vec_Ptr_t * products; Acec2_Product_t * p; Gia_Obj_t * o;
    Hsh_VecMan_t * owned; Vec_Int_t * key, * ids, * left, * right;
    int index, i, j, k, a, b, lit, rank, neg, id, found, absent, total;
    if ( m->Pars.nAnalysisLevel < 2 ) return;
    products = Acec2_RecordProductGrid(m, r); if ( !products ) return;
    q->vProducts = Vec_PtrAlloc(4); q->vCoverage = Vec_IntAlloc(12); key = Vec_IntAlloc(4);
    Vec_PtrForEachEntry(Acec2_Product_t *, products, p, index)
    {
        found = absent = total = 0;
        if ( Vec_IntSize(p->vOperands[0]) < 4 || Vec_IntSize(p->vOperands[1]) < 4 ||
             (ABC_INT64_T)Vec_IntSize(p->vOperands[0])*Vec_IntSize(p->vOperands[1]) > 65536 || Acec2_Stopped(m) ) goto next;
        left = Vec_IntDup(r->vTerms); right = Vec_IntDup(r->vOutputs); owned = Hsh_VecManStart(100); ids = Vec_IntAlloc(100);
        for ( i = 0; i < Vec_IntSize(left); i += 2 )
        {
            lit = Vec_IntEntry(left, i); o = Gia_ManObj(m->pGia, lit >> 1);
            if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
            a = Gia_ObjFaninLit0p(m->pGia, o); b = Gia_ObjFaninLit1p(m->pGia, o); if ( a > b ) ABC_SWAP(int, a, b);
            Vec_IntClear(key); Vec_IntPushTwo(key, a, b); Vec_IntPushTwo(key, Vec_IntEntry(left, i+1), lit & 1);
            id = Hsh_VecManAdd(owned, key); if ( id == Vec_IntSize(ids) ) Vec_IntPush(ids, i);
        }
        Vec_IntForEachEntry(p->vOperands[0], a, i)
        Vec_IntForEachEntry(p->vOperands[1], b, j)
        {
            int x = a, y = b;
            if ( a < 2 || b < 2 ) continue;
            total++; rank = i+j+p->Shift; if ( rank < 0 || rank >= r->Width ) continue;
            neg = p->fNeg ^ (p->fSigned[0] && i == Vec_IntSize(p->vOperands[0])-1) ^
                (p->fSigned[1] && j == Vec_IntSize(p->vOperands[1])-1);
            if ( x > y ) ABC_SWAP(int, x, y);
            Vec_IntClear(key); Vec_IntPushTwo(key, x, y); Vec_IntPushTwo(key, rank, neg);
            id = Hsh_VecManAdd(owned, key); if ( id == Vec_IntSize(ids) ) Vec_IntPush(ids, -1);
            k = Vec_IntEntry(ids, id);
            if ( k >= 0 ) { found++; Vec_IntWriteEntry(left, k, -1); Vec_IntWriteEntry(ids, id, -1); continue; }
            lit = Acec2_GapProductNode(m, a, b, key);
            if ( lit < 0 ) { absent++; continue; }
            Vec_IntPushTwo(right, lit ^ neg, rank);
        }
        Hsh_VecManStop(owned); Vec_IntFree(ids);
        if ( found >= 8 && 3*found >= total && !Acec2_Stopped(m) )
        {
            // Port positions propose a complete product word only when the
            // port count is consistent with this particular operand grid.
            if ( Gia_ManCoNum(m->pGia) == Vec_IntSize(p->vOperands[0])+Vec_IntSize(p->vOperands[1]) )
                Gia_ManForEachCo(m->pGia, o, i)
                {
                    rank = i+p->Shift; if ( rank < 0 || rank >= r->Width ) continue;
                    Vec_IntPushTwo(left, Gia_ObjFaninLit0p(m->pGia, o) ^ p->fNeg, rank);
                }
            Vec_PtrPush(q->vProducts, p); Vec_IntPushThree(q->vCoverage, found, total, absent);
            Acec2_GapGridRuns(m, r, q, left, right); p = NULL;
        }
        Vec_IntFree(left); Vec_IntFree(right);
next:
        if ( p ) { Vec_IntFree(p->vOperands[0]); Vec_IntFree(p->vOperands[1]); ABC_FREE(p); }
    }
    Vec_PtrFree(products); Vec_IntFree(key);
}

/**Function*************************************************************

  Synopsis    [Releases an owned proposal queue and its unproved operand grids.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_GapQueueFree( Acec2_GapQueue_t * q )
{
    Acec2_Product_t * p; int i;
    if ( !q ) return;
    if ( q->vProducts )
    {
        Vec_PtrForEachEntry(Acec2_Product_t *, q->vProducts, p, i)
        { Vec_IntFree(p->vOperands[0]); Vec_IntFree(p->vOperands[1]); ABC_FREE(p); }
        Vec_PtrFree(q->vProducts);
    }
    Vec_IntFreeP(&q->vCoverage); Vec_WecFree(q->vCandidates); ABC_FREE(q);
}

/**Function*************************************************************

  Synopsis    [Creates the persistent proposal queue for one source record.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_GapQueue_t * Acec2_GapStart( Acec2_Man_t * m, int Record )
{
    Acec2_Record_t * r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Record);
    Acec2_GapQueue_t * q = ABC_CALLOC(Acec2_GapQueue_t, 1);
    Vec_Wec_t * deps, * cones; Vec_Wrd_t * active; Vec_Int_t * v, * basis;
    int i, j, k, selected[3], work = 0, groups = m->nGapGroups, connected;
    q->Result = Record; q->vCandidates = Vec_WecAlloc(16); q->fProductNext = 1;
    if ( r->Word >= 0 || r->Proof || r->Compose || r->Extend || r->vOutputMasks || r->pProductReference || r->Prefix == r->Width || r->Width < 4 ||
         Vec_IntSize(r->vOutputs) < 4 || Vec_IntSize(r->vTerms) < 8 ) return q;
    if ( r->Width > 512 || Vec_IntSize(r->vOutputs) > 262144 || Vec_IntSize(r->vTerms) > 262144 )
    { m->nGapLimits++; return q; }
    Acec2_GapGrids(m, r, q);
    basis = Vec_IntDup(r->vOutputs); Vec_IntAppend(basis, r->vTerms); cones = Vec_WecStart(Vec_IntSize(r->vTerms)/2);
    deps = Acec2_GapDependencies(m, r, basis, cones, &work); active = Vec_WrdAlloc(32);
    Acec2_GapConnected(m, r, q, basis, deps, cones, &work);
    if ( Vec_WecSize(q->vCandidates) < 32 ) Acec2_GapOutputs(m, r, q, basis, &work);
    // Keep the original root-only proposals as alternatives. A ranked
    // input encountered structurally can cancel out of a source identity;
    // requiring it in every proposal would lose those closures.
    Vec_WecForEachLevel(deps, v, i)
    {
        for ( j = 0; j < Vec_IntSize(v) && Vec_IntEntry(v, j) < Vec_IntSize(r->vOutputs)/2; j++ ) {}
        Vec_IntShrink(v, j);
    }
    Vec_WecForEachLevel(deps, v, i) if ( Vec_IntSize(v) ) Vec_WrdPush(active, ((word)(unsigned)Vec_IntEntry(r->vTerms, 2*i+1) << 32) | (unsigned)i);
    if ( Vec_WrdSize(active) > 1 ) Vec_WrdSort(active, 0);
    for ( i = 0; i < Vec_WrdSize(active); i++ )
    {
        if ( work > 262144 || m->nGapGroups-groups >= 4096 || Vec_WecSize(q->vCandidates) >= 32 ) goto limited;
        if ( Acec2_Stopped(m) ) goto finish;
        selected[0] = (int)(unsigned)Vec_WrdEntry(active, i);
        Acec2_GapCandidate(m, r, q, basis, deps, selected, 1);
        for ( j = i+1; j < Vec_WrdSize(active); j++ )
        {
            if ( (Vec_WrdEntry(active, j) >> 32)-(Vec_WrdEntry(active, i) >> 32) > 3 ) break;
            if ( ++work > 262144 || m->nGapGroups-groups >= 4096 || Vec_WecSize(q->vCandidates) >= 32 ) goto limited;
            if ( Acec2_Stopped(m) ) goto finish;
            selected[1] = (int)(unsigned)Vec_WrdEntry(active, j);
            connected = Acec2_GapNeighbors(Vec_WecEntry(deps, selected[0]), Vec_WecEntry(deps, selected[1]));
            if ( connected ) Acec2_GapCandidate(m, r, q, basis, deps, selected, 2);
            for ( k = j+1; k < Vec_WrdSize(active); k++ )
            {
                if ( (Vec_WrdEntry(active, k) >> 32)-(Vec_WrdEntry(active, i) >> 32) > 3 ) break;
                if ( ++work > 262144 || m->nGapGroups-groups >= 4096 || Vec_WecSize(q->vCandidates) >= 32 ) goto limited;
                if ( Acec2_Stopped(m) ) goto finish;
                selected[2] = (int)(unsigned)Vec_WrdEntry(active, k);
                if ( connected + Acec2_GapNeighbors(Vec_WecEntry(deps, selected[0]), Vec_WecEntry(deps, selected[2])) +
                     Acec2_GapNeighbors(Vec_WecEntry(deps, selected[1]), Vec_WecEntry(deps, selected[2])) >= 2 )
                    Acec2_GapCandidate(m, r, q, basis, deps, selected, 3);
            }
        }
    }
    goto finish;
limited:
    m->nGapLimits++;
finish:
    m->nGapSteps += work; Vec_WrdFree(active); Vec_WecFree(deps); Vec_WecFree(cones); Vec_IntFree(basis); return q;
}

/**Function*************************************************************

  Synopsis    [Proves queued gaps and composes their checked source records.]

  Description [A queue survives subsequent requests. Whole-grid and local
  gap proposals alternate so a long local queue cannot hide a product
  certificate. Interrupted proposals remain unconsumed. Neither simulation
  nor a limited proof closes a gap.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CloseRecordGaps( Acec2_Man_t * m, int Record, int * pnQueries )
{
    Acec2_GapQueue_t * q; Acec2_Record_t * r, * old, * joined; Vec_Int_t * key, outputs, terms, constants;
    Acec2_Product_t * product; Gia_Obj_t * o; Vec_Int_t * bits;
    int before, attempts, id, combined, offset, width, i, scanned = 0, queries;
    if ( !m || !pnQueries || *pnQueries <= 0 || Record < 0 || Record >= Vec_PtrSize(m->vRecords) || Acec2_Stopped(m) ) return 0;
    queries = *pnQueries;
    r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Record);
    if ( r->Word >= 0 || r->Proof || r->Compose || r->Extend || r->vOutputMasks || r->pProductReference || r->Prefix == r->Width || r->Width < 4 ||
         Vec_IntSize(r->vOutputs) < 4 || Vec_IntSize(r->vTerms) < 8 ) return 0;
    if ( !m->vGapQueues ) m->vGapQueues = Vec_PtrAlloc(100);
    while ( Vec_PtrSize(m->vGapQueues) <= Record ) Vec_PtrPush(m->vGapQueues, NULL);
    q = (Acec2_GapQueue_t *)Vec_PtrEntry(m->vGapQueues, Record);
    if ( !q )
    {
        // A fresh queue can attempt its first proof in the same request.
        // Empty scans still spend a unit; many open records must not spend
        // the entire allowance only constructing queues.
        scanned = 1;
        q = Acec2_GapStart(m, Record);
        if ( Acec2_Stopped(m) ) { Acec2_GapQueueFree(q); return 0; }
        Vec_PtrWriteEntry(m->vGapQueues, Record, q);
    }
    before = Vec_PtrSize(m->vRecords);
    while ( *pnQueries > 0 && !Acec2_Stopped(m) )
    {
        // Preserve the direct single-product word attempt. The internal
        // weighted boundary is an alternative, not a prerequisite for it.
        if ( q->vProducts && q->NextProduct < Vec_PtrSize(q->vProducts) &&
             (Vec_PtrSize(q->vProducts) == 1 || q->NextExpression >= 2) &&
             (q->fProductNext || q->Next == Vec_WecSize(q->vCandidates)) )
        {
            product = (Acec2_Product_t *)Vec_PtrEntry(q->vProducts, q->NextProduct);
            if ( Gia_ManCoNum(m->pGia) != Vec_IntSize(product->vOperands[0])+Vec_IntSize(product->vOperands[1]) )
            { q->NextProduct++; continue; }
            bits = Vec_IntAlloc(Gia_ManCoNum(m->pGia));
            Gia_ManForEachCo(m->pGia, o, id) Vec_IntPush(bits, Gia_ObjFaninLit0p(m->pGia, o));
            (*pnQueries)--; Acec2_RecordGridProduct(m, q->Result, product, bits); Vec_IntFree(bits);
            if ( Acec2_Stopped(m) ) break;
            q->NextProduct++; q->fProductNext = 0; continue;
        }
        if ( q->vProducts && Vec_PtrSize(q->vProducts) >= 1 && Vec_PtrSize(q->vProducts) <= 8 &&
             q->NextExpression < 2 && (q->fProductNext || q->Next == Vec_WecSize(q->vCandidates)) )
        {
            offset = 0;
            Vec_PtrForEachEntry(Acec2_Product_t *, q->vProducts, product, i) offset = Abc_MaxInt(offset, -product->Shift);
            joined = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, q->Result);
            if ( q->NextExpression == 0 && joined->Width+offset <= 64 )
            {
                bits = Vec_IntDup(joined->vOutputs); width = joined->Width+offset;
                // Shifting both sides preserves the checked modulus. This
                // also admits a single embedded product with weighted roots.
                for ( i = 1; i < Vec_IntSize(bits); i += 2 ) Vec_IntAddToEntry(bits, i, offset);
            }
            else if ( q->NextExpression == 1 && Gia_ManCoNum(m->pGia) >= 4 && Gia_ManCoNum(m->pGia) <= 64 )
            {
                width = Gia_ManCoNum(m->pGia); bits = Vec_IntAlloc(2*width);
                Gia_ManForEachCo(m->pGia, o, id) Vec_IntPushTwo(bits, Gia_ObjFaninLit0p(m->pGia, o), id);
            }
            else { q->NextExpression++; continue; }
            (*pnQueries)--; Acec2_RecordGridExpression(m, q->Result, q->vProducts, bits, width, offset); Vec_IntFree(bits);
            if ( Acec2_Stopped(m) ) break;
            q->NextExpression++; q->fProductNext = 0; continue;
        }
        if ( q->Next == Vec_WecSize(q->vCandidates) ) break;
        key = Vec_WecEntry(q->vCandidates, q->Next); offset = 4;
        memset(&outputs, 0, sizeof(outputs)); memset(&terms, 0, sizeof(terms)); memset(&constants, 0, sizeof(constants));
        outputs.nSize = outputs.nCap = Vec_IntEntry(key, 1); outputs.pArray = Vec_IntEntryP(key, offset); offset += outputs.nSize;
        terms.nSize = terms.nCap = Vec_IntEntry(key, 2); terms.pArray = Vec_IntEntryP(key, offset); offset += terms.nSize;
        constants.nSize = constants.nCap = Vec_IntEntry(key, 3); constants.pArray = Vec_IntArray(key)+offset;
        attempts = m->nWeightedAttempts; id = Acec2_RecordWeighted(m, &outputs, &terms, &constants, Vec_IntEntry(key, 0));
        if ( m->nWeightedAttempts != attempts ) (*pnQueries)--;
        if ( Acec2_Stopped(m) ) break;
        q->Next++; q->fProductNext = 1;
        if ( id < 0 ) continue;
        combined = Acec2_RecordCompose(m, q->Result, id, Vec_IntEntry(key, 0));
        if ( combined >= 0 && combined != q->Result )
        {
            old = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, q->Result); joined = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, combined);
            if ( joined->Prefix > old->Prefix || Vec_IntSize(joined->vOutputs)+Vec_IntSize(joined->vTerms) < Vec_IntSize(old->vOutputs)+Vec_IntSize(old->vTerms) )
            { q->Result = combined; q->NextProduct = q->NextExpression = 0; m->nGapClosed++; }
        }
    }
    if ( scanned && *pnQueries == queries ) (*pnQueries)--;
    return Vec_PtrSize(m->vRecords)-before;
}

/**Function*************************************************************

  Synopsis    [Requests bounded gap closure before standalone word discovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_CloseGaps( Acec2_Man_t * m )
{
    int i, unit, before, queries = 16, count = Vec_PtrSize(m->vRecords);
    while ( queries > 0 && !Acec2_Stopped(m) )
    {
        before = queries;
        for ( i = 0; i < count && queries > 0 && !Acec2_Stopped(m); i++ )
        {
            unit = 1; Acec2_CloseRecordGaps(m, i, &unit); queries -= 1-unit;
        }
        if ( before == queries ) break;
    }
}

/**Function*************************************************************

  Synopsis    [Returns the latest checked boundary without altering its parents.]

  Description [Cell-cover reconstruction retains its original identities.
  Reporting and record matching can consume the independently checked
  composition, which explicitly records every source dependency.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_GapRecord( Acec2_Man_t * m, int Record )
{
    Acec2_GapQueue_t * q;
    if ( Record < 0 || !m->vGapQueues || Record >= Vec_PtrSize(m->vGapQueues) ) return Record;
    q = (Acec2_GapQueue_t *)Vec_PtrEntry(m->vGapQueues, Record);
    return q ? q->Result : Record;
}

/**Function*************************************************************

  Synopsis    [Suppresses a grid proposal already certified at its output word.]

  Description [A partial certificate or another output boundary does not
  remove a proposal. Exact operand literals, signedness and every output
  position must match a completed single-product word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_GapProductKnown( Acec2_Man_t * m, Acec2_Product_t * p )
{
    Acec2_Record_t * r; Acec2_Product_t * q; int i, j, side, order, width;
    width = Vec_IntSize(p->vOperands[0])+Vec_IntSize(p->vOperands[1]);
    if ( p->fNeg || Gia_ManCoNum(m->pGia) != width ) return 0;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        if ( r->vOutputMasks || r->Width < width || r->Prefix < width ||
             !r->vFactors || Vec_PtrSize(r->vFactors) != 1 || r->FactorWidth < width || Vec_WecSize(r->vResidual) ) continue;
        q = (Acec2_Product_t *)Vec_PtrEntry(r->vFactors, 0); if ( q->Shift || q->fNeg ) continue;
        for ( order = 0; order < 2; order++ )
        {
            for ( side = 0; side < 2; side++ )
                if ( q->fSigned[side] != p->fSigned[side ^ order] || !Vec_IntEqual(q->vOperands[side], p->vOperands[side ^ order]) ) break;
            if ( side == 2 ) break;
        }
        if ( order == 2 ) continue;
        for ( j = 0; j < width; j++ )
        {
            int k;
            for ( k = 0; k < Vec_IntSize(r->vOutputs); k += 2 ) if ( Vec_IntEntry(r->vOutputs, k+1) == j ) break;
            if ( k == Vec_IntSize(r->vOutputs) || Vec_IntEntry(r->vOutputs, k) != Gia_ObjFaninLit0p(m->pGia, Gia_ManCo(m->pGia, j)) ) break;
        }
        if ( j == width ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Reports remaining grid proposals separately from checked records.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_PrintGapProducts( Acec2_Man_t * m, FILE * f, int fJson )
{
    Acec2_GapQueue_t * q; Acec2_Product_t * p; int i, j, side, count = 0;
    if ( fJson ) fprintf(f, "[");
    if ( m->vGapQueues ) Vec_PtrForEachEntry(Acec2_GapQueue_t *, m->vGapQueues, q, i)
    {
        if ( !q || !q->vProducts ) continue;
        Vec_PtrForEachEntry(Acec2_Product_t *, q->vProducts, p, j)
        {
            if ( Acec2_GapProductKnown(m, p) ) continue;
            if ( !fJson )
            {
                if ( !count ) fprintf(f, "Unproved product candidates (observed grid evidence only):\n");
                fprintf(f, "  record %d: probable %d x %d product; observed products = %d/%d, missing physical products = %d, column offset = %d.\n",
                    i, Vec_IntSize(p->vOperands[0]), Vec_IntSize(p->vOperands[1]), Vec_IntEntry(q->vCoverage, 3*j),
                    Vec_IntEntry(q->vCoverage, 3*j+1), Vec_IntEntry(q->vCoverage, 3*j+2), p->Shift);
            }
            else
            {
                fprintf(f, "%s{\"record\":%d,\"status\":\"unproved\",\"observed_products\":%d,\"grid_products\":%d,\"absent_source_products\":%d,\"column_offset\":%d,\"negated\":%s,\"signed\":[%s,%s],\"operand_literals\":[",
                    count ? "," : "", i, Vec_IntEntry(q->vCoverage, 3*j), Vec_IntEntry(q->vCoverage, 3*j+1),
                    Vec_IntEntry(q->vCoverage, 3*j+2), p->Shift, p->fNeg ? "true" : "false",
                    p->fSigned[0] ? "true" : "false", p->fSigned[1] ? "true" : "false");
                for ( side = 0; side < 2; side++ )
                {
                    fprintf(f, "%s[", side ? "," : "");
                    Acec2_WriteList(f, p->vOperands[side], 1, 0);
                    fprintf(f, "]");
                }
                fprintf(f, "]}");
            }
            count++;
        }
    }
    if ( fJson ) fprintf(f, "]");
}

/**Function*************************************************************

  Synopsis    [Releases source simulations, product indices and gap queues.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_GapStop( Acec2_Man_t * m )
{
    Acec2_GapQueue_t * q; int i;
    if ( m->vGapQueues )
    {
        Vec_PtrForEachEntry(Acec2_GapQueue_t *, m->vGapQueues, q, i)
            Acec2_GapQueueFree(q);
        Vec_PtrFree(m->vGapQueues);
    }
    Vec_WrdFreeP(&m->vGapSim);
    if ( m->hGapProducts ) Hsh_VecManStop(m->hGapProducts);
    Vec_IntFreeP(&m->vGapProducts);
    if ( m->hGridProofs ) Hsh_VecManStop(m->hGridProofs);
    Vec_IntFreeP(&m->vGridProofs);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
