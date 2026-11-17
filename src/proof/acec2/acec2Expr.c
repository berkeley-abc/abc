/**CFile****************************************************************

  FileName    [acec2Expr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Exact factors of weighted partial-product expressions.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 13, 2026.]

  Revision    [$Id$]

  Description [Checked region identities supply weighted leaves. Plain
  two-input AND leaves supply exact bit products. A complete coefficient
  check certifies each factor; unsuccessful components remain addends.]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef struct Acec2_ExprRaw_t_ Acec2_ExprRaw_t;
struct Acec2_ExprRaw_t_ { int a, b, Rank, Leaf; };
typedef struct Acec2_ExprEdge_t_ Acec2_ExprEdge_t;
struct Acec2_ExprEdge_t_ { int a, b, Rank, Sign, First, End, Product; };

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Orders partial products by endpoints and signed weight.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprRawCompare( const void * p0, const void * p1 )
{
    const Acec2_ExprRaw_t * a = (const Acec2_ExprRaw_t *)p0, * b = (const Acec2_ExprRaw_t *)p1;
    if ( a->a != b->a ) return a->a < b->a ? -1 : 1;
    if ( a->b != b->b ) return a->b < b->b ? -1 : 1;
    if ( a->Rank != b->Rank ) return a->Rank < b->Rank ? -1 : 1;
    return a->Leaf == b->Leaf ? 0 : a->Leaf < b->Leaf ? -1 : 1;
}

/**Function*************************************************************

  Synopsis    [Finds a literal in a sorted private endpoint table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprIndex( Vec_Int_t * v, int Lit )
{
    int * p = (int *)bsearch(&Lit, Vec_IntArray(v), Vec_IntSize(v), sizeof(int),
                             (int (*)(const void *, const void *))Vec_IntSortCompare1);
    return p ? (int)(p-Vec_IntArray(v)) : -1;
}

/**Function*************************************************************

  Synopsis    [Classifies a complete modular coefficient as a signed power.]

  Description [Returns -2 for zero and -1 for any other coefficient.
  Signed carry propagation skips zero gaps and sign-extension runs, so
  a wide modulus does not require one step per bit for every product.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprPower( Acec2_ExprRaw_t * r, int First, int End, int Width, int * pSign )
{
    int i = First, rank = r[First].Rank >> 1, carry = 0, bit, next, ones = 0, first = -1;
    while ( rank < Width && (i < End || carry) )
    {
        next = i < End ? r[i].Rank >> 1 : Width;
        if ( next > rank && (carry == 0 || carry == -1) )
        {
            if ( carry == -1 ) { if ( first < 0 ) first = rank; ones += next-rank; }
            rank = next;
            if ( rank == Width ) break;
        }
        while ( i < End && (r[i].Rank >> 1) == rank ) carry += (r[i++].Rank & 1) ? -1 : 1;
        bit = carry % 2; if ( bit < 0 ) bit += 2;
        if ( bit ) { if ( first < 0 ) first = rank; ones++; }
        carry = (carry-bit)/2; rank++;
    }
    *pSign = 0;
    if ( !ones ) return -2;
    if ( ones == 1 ) return first;
    if ( ones == Width-first ) { *pSign = 1; return first; }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Finds an aggregated endpoint pair without approximate keys.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprEdgeFind( Acec2_ExprEdge_t * e, int nEdges, int a, int b )
{
    int lo = 0, hi = nEdges, mid;
    if ( a > b ) ABC_SWAP(int, a, b);
    while ( lo < hi )
    {
        mid = lo+(hi-lo)/2;
        if ( e[mid].a < a || (e[mid].a == a && e[mid].b < b) ) lo = mid+1;
        else hi = mid;
    }
    return lo < nEdges && e[lo].a == a && e[lo].b == b ? lo : -1;
}

/**Function*************************************************************

  Synopsis    [Releases a product record and both ordered operand vectors.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ProductFree( Acec2_Product_t * p )
{
    if ( !p ) return;
    Vec_IntFreeP(&p->vOperands[0]); Vec_IntFreeP(&p->vOperands[1]); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Checks an entire coefficient rectangle before accepting a bus.]

  Description [Gaps represent zero operand bits. All visible cross products
  must exist with the required coefficient. Bits above the modulus vanish.
  Offset -1 omits only a0*b0 and therefore represents floor(A*B/2).
  Lower offsets can discard a carry and are not accepted by this check.
  A missing or mismatched coefficient bounds the certified prefix. The
  returned width states the entire valid modulus, including truncated trees.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Product_t * Acec2_ExprFactor( Acec2_Man_t * m, Vec_Int_t * vNodes, Vec_Int_t * vLits,
    Vec_Int_t * vColor, Vec_Int_t * vRank, Acec2_ExprEdge_t * e, int nEdges, int Width, int * pWidth, int fProposal )
{
    Acec2_Product_t * p = ABC_CALLOC(Acec2_Product_t, 1);
    Vec_Int_t * vBus[2] = {NULL, NULL};
    Vec_Int_t * vPositions[2] = {Vec_IntAlloc(16), Vec_IntAlloc(16)};
    int low[2] = {ABC_INT_MAX, ABC_INT_MAX}, high[2] = {-ABC_INT_MAX, -ABC_INT_MAX}, count[2] = {0, 0};
    int i, j, ii, jj, id, side, rank, a, b, index, mode, neg, valid, best = 0, matches, bestMatches = -1;
    *pWidth = 0;
    Vec_IntForEachEntry(vNodes, id, i)
    {
        side = Vec_IntEntry(vColor, id); rank = Vec_IntEntry(vRank, id); count[side]++;
        low[side] = Abc_MinInt(low[side], rank); high[side] = Abc_MaxInt(high[side], rank);
    }
    if ( count[0] < 2 || count[1] < 2 ) goto finish;
    p->Shift = low[0]+low[1];
    if ( !fProposal && (p->Shift < -1 || p->Shift >= Width) ) goto finish;
    if ( (ABC_INT64_T)count[0]*count[1] > 2000000 ) { m->nExprLimits++; goto finish; }
    for ( side = 0; side < 2; side++ )
    {
        if ( high[side]-low[side] >= Width+1 ) goto finish;
        vBus[side] = Vec_IntStartFull(high[side]-low[side]+1);
        p->vOperands[side] = Vec_IntStart(Vec_IntSize(vBus[side]));
    }
    Vec_IntForEachEntry(vNodes, id, i)
    {
        side = Vec_IntEntry(vColor, id); rank = Vec_IntEntry(vRank, id)-low[side];
        if ( Vec_IntEntry(vBus[side], rank) >= 0 ) goto finish;
        Vec_IntWriteEntry(vBus[side], rank, id);
        Vec_IntPush(vPositions[side], rank);
        Vec_IntWriteEntry(p->vOperands[side], rank, Vec_IntEntry(vLits, id));
    }
    for ( mode = 0; mode < 8; mode++ )
    {
        valid = Width; matches = 0;
        Vec_IntForEachEntry(vPositions[0], i, ii)
        {
            if ( Acec2_Stopped(m) ) goto finish;
            a = Vec_IntEntry(vBus[0], i); if ( a < 0 ) continue;
            Vec_IntForEachEntry(vPositions[1], j, jj)
            {
                b = Vec_IntEntry(vBus[1], j); rank = i+j+p->Shift;
                if ( b < 0 || rank < 0 || rank >= Width ) continue;
                index = Acec2_ExprEdgeFind(e, nEdges, a, b);
                if ( index < 0 ) { valid = Abc_MinInt(valid, rank); continue; }
                if ( e[index].Rank != rank ) { valid = Abc_MinInt(valid, Abc_MinInt(rank, e[index].Rank)); continue; }
                neg = ((mode & 1) && i == Vec_IntSize(vBus[0])-1) ^ ((mode & 2) && j == Vec_IntSize(vBus[1])-1);
                neg ^= (mode >> 2) & 1;
                if ( e[index].Sign != neg ) valid = Abc_MinInt(valid, rank+1);
                else matches++;
            }
        }
        // An incomplete coefficient rectangle can still suggest operands.
        // Its best-supported sign interpretation is only a proposal: the
        // original result cones must pass an independent exact word proof.
        if ( fProposal )
        {
            if ( matches <= bestMatches ) continue;
            bestMatches = matches; best = Width;
            p->fSigned[0] = mode & 1; p->fSigned[1] = (mode >> 1) & 1; p->fNeg = (mode >> 2) & 1;
            continue;
        }
        if ( valid <= best || valid < 2 || valid <= p->Shift ) continue;
        best = valid; p->fSigned[0] = mode & 1; p->fSigned[1] = (mode >> 1) & 1; p->fNeg = (mode >> 2) & 1;
        if ( best == Width ) break;
    }
finish:
    Vec_IntFreeP(&vBus[0]); Vec_IntFreeP(&vBus[1]); Vec_IntFree(vPositions[0]); Vec_IntFree(vPositions[1]);
    if ( !best || Acec2_Stopped(m) ) { Acec2_ProductFree(p); return NULL; }
    if ( fProposal == 1 ) p->Shift = 0;
    *pWidth = best;
    return p;
}

/**Function*************************************************************

  Synopsis    [Adds a power of two to a modular constant bit vector.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ExprConstant( Vec_Int_t * v, int Rank )
{
    int bit;
    for ( ; Rank < Vec_IntSize(v); Rank++ )
    {
        bit = Vec_IntEntry(v, Rank); Vec_IntWriteEntry(v, Rank, bit ^ 1);
        if ( !bit ) break;
    }
}

/**Function*************************************************************

  Synopsis    [Releases all expression storage owned by one region record.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_ExprFree( Acec2_Expr_t * p )
{
    Acec2_Product_t * q; int i;
    if ( !p ) return;
    Vec_PtrForEachEntry(Acec2_Product_t *, p->vProducts, q, i) Acec2_ProductFree(q);
    Vec_PtrFree(p->vProducts); Vec_IntFree(p->vAddends); Vec_IntFree(p->vConstant); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Separates repeated operand ranks into checked product terms.]

  Description [Repeated ranks occur when several products share an operand.
  Deterministic bus partitions propose a sum of products. Each rectangle
  still passes the complete coefficient check, and only its own edges are
  consumed. Rejected or unvisited rectangles remain original addends.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprFactors( Acec2_Man_t * m, Acec2_Expr_t * p, Vec_Int_t * vNodes, Vec_Int_t * vLits,
    Vec_Int_t * vColor, Vec_Int_t * vRank, Vec_Int_t * vGroup, Vec_Wec_t * vAdj,
    Acec2_ExprEdge_t * e, int nEdges, Vec_Int_t * vWidths, int fProposal )
{
    Vec_Wrd_t * vOrder[2] = {Vec_WrdAlloc(16), Vec_WrdAlloc(16)};
    Vec_Wec_t * vGroups[2] = {Vec_WecAlloc(4), Vec_WecAlloc(4)};
    Vec_Int_t * vBoth = Vec_IntAlloc(Vec_IntSize(vNodes)), * v0, * v1, * row;
    Acec2_Product_t * product;
    word key;
    int i, j, side, id, next, edge, rank, prev, slot, g0, g1, width, attempts = 0, best = 0;
    Vec_IntForEachEntry(vNodes, id, i)
    {
        side = Vec_IntEntry(vColor, id); rank = Vec_IntEntry(vRank, id)+2*p->Width;
        Vec_WrdPush(vOrder[side], ((word)(unsigned)rank << 32) | (unsigned)id);
    }
    for ( side = 0; side < 2; side++ )
    {
        if ( Vec_WrdSize(vOrder[side]) > 1 ) Vec_WrdSort(vOrder[side], 0);
        prev = -1; slot = 0;
        Vec_WrdForEachEntry(vOrder[side], key, i)
        {
            id = (int)(unsigned)key; rank = (int)(key >> 32);
            slot = rank == prev ? slot+1 : 0; prev = rank;
            Vec_WecPush(vGroups[side], slot, id); Vec_IntWriteEntry(vGroup, id, slot);
        }
    }
    Vec_WecForEachLevel(vGroups[0], v0, g0)
        Vec_WecForEachLevel(vGroups[1], v1, g1)
        {
            if ( Acec2_Stopped(m) ) goto finish;
            if ( Vec_IntSize(v0) < 2 || Vec_IntSize(v1) < 2 ) continue;
            if ( attempts++ == 64 ) { m->nExprLimits++; goto finish; }
            Vec_IntClear(vBoth); Vec_IntAppend(vBoth, v0); Vec_IntAppend(vBoth, v1);
            product = Acec2_ExprFactor(m, vBoth, vLits, vColor, vRank, e, nEdges, p->Width, &width, fProposal);
            if ( !product ) continue;
            Vec_IntForEachEntry(v0, id, i)
            {
                row = Vec_WecEntry(vAdj, id);
                Vec_IntForEachEntry(row, edge, j)
                {
                    next = e[edge].a ^ e[edge].b ^ id;
                    if ( Vec_IntEntry(vGroup, next) == g1 ) e[edge].Product = Vec_PtrSize(p->vProducts);
                }
            }
            Vec_PtrPush(p->vProducts, product); Vec_IntPush(vWidths, width); best = Abc_MaxInt(best, width);
        }
finish:
    for ( side = 0; side < 2; side++ ) { Vec_WrdFree(vOrder[side]); Vec_WecFree(vGroups[side]); }
    Vec_IntFree(vBoth); return best;
}

/**Function*************************************************************

  Synopsis    [Certifies a square or a complete square within a larger graph.]

  Description [Diagonal terms fix twice each bit position plus the product
  shift. Off-diagonal coefficients have one extra bit of weight because
  a*b and b*a coincide. Check every retained diagonal and cross coefficient.
  If low columns are missing, try a complete higher operand slice and leave
  the other terms as addends. Its shift is at least -1, so no unrepresented
  carry from discarded partial products can enter the certified expression.]

  SideEffects [Returns the consumed endpoint set separately from the product.]

  SeeAlso     []

***********************************************************************/
static Acec2_Product_t * Acec2_ExprSquare( Acec2_Man_t * m, Vec_Int_t * vNodes, Vec_Int_t * vLits,
    Vec_Wec_t * vAdj, Acec2_ExprEdge_t * e, int nEdges, int Width, Vec_Int_t * vSelected, int * pWidth )
{
    Acec2_Product_t * p = NULL;
    Vec_Int_t * vRanks = NULL, * vSeen = NULL, * vQueue = NULL, * vBus = NULL, * row;
    int i, j, id, next, edge, rank, low = ABC_INT_MAX, high = -ABC_INT_MAX;
    int a, b, x, y, mode, neg, valid, best = 0;
    *pWidth = 0; Vec_IntClear(vSelected);
    Vec_IntForEachEntry(vNodes, id, i)
    {
        edge = Acec2_ExprEdgeFind(e, nEdges, id, id);
        if ( edge < 0 || e[edge].Rank < 0 ) continue;
        vRanks = Vec_IntStartFull(Vec_IntSize(vLits)); vSeen = Vec_IntStart(Vec_IntSize(vLits));
        vQueue = Vec_IntAlloc(Vec_IntSize(vNodes));
        Vec_IntWriteEntry(vRanks, id, e[edge].Rank); Vec_IntWriteEntry(vSeen, id, 1);
        Vec_IntPush(vQueue, id); break;
    }
    if ( !vQueue ) goto finish;
    for ( i = 0; i < Vec_IntSize(vQueue); i++ )
    {
        if ( Acec2_Stopped(m) ) goto finish;
        id = Vec_IntEntry(vQueue, i); rank = Vec_IntEntry(vRanks, id);
        low = Abc_MinInt(low, rank); high = Abc_MaxInt(high, rank);
        row = Vec_WecEntry(vAdj, id);
        Vec_IntForEachEntry(row, edge, j)
        {
            if ( e[edge].Rank < 0 ) goto finish;
            next = e[edge].a ^ e[edge].b ^ id; rank = 2*(e[edge].Rank-1)-Vec_IntEntry(vRanks, id);
            if ( rank < -2*Width || rank > 2*Width ) goto finish;
            if ( Vec_IntEntry(vSeen, next) )
            { if ( Vec_IntEntry(vRanks, next) != rank ) goto finish; }
            else
            { Vec_IntWriteEntry(vSeen, next, 1); Vec_IntWriteEntry(vRanks, next, rank); Vec_IntPush(vQueue, next); }
        }
    }
    if ( Vec_IntSize(vQueue) != Vec_IntSize(vNodes) ) goto finish;
    if ( low < -1 ) low += 2*((-low)/2);
    if ( low >= Width || high < low || high-low > 2*Width ) goto finish;
    p = ABC_CALLOC(Acec2_Product_t, 1); p->Shift = low;
    vBus = Vec_IntStartFull((high-low)/2+1); p->vOperands[0] = Vec_IntStart(Vec_IntSize(vBus));
    Vec_IntForEachEntry(vNodes, id, i)
    {
        rank = Vec_IntEntry(vRanks, id)-low;
        if ( rank < 0 ) continue;
        if ( (rank & 1) || Vec_IntEntry(vBus, rank/2) >= 0 ) goto finish;
        Vec_IntWriteEntry(vBus, rank/2, id); Vec_IntPush(vSelected, id);
        Vec_IntWriteEntry(p->vOperands[0], rank/2, Vec_IntEntry(vLits, id));
    }
    if ( Vec_IntSize(vSelected) < 2 ) goto finish;
    if ( (ABC_INT64_T)Vec_IntSize(vSelected)*Vec_IntSize(vSelected) > 2000000 )
    { m->nExprLimits++; goto finish; }
    p->vOperands[1] = Vec_IntDup(p->vOperands[0]);
    for ( mode = 0; mode < 4; mode++ )
    {
        valid = Width;
        Vec_IntForEachEntry(vSelected, a, i)
        {
            if ( Acec2_Stopped(m) ) goto finish;
            x = (Vec_IntEntry(vRanks, a)-low)/2;
            for ( j = i; j < Vec_IntSize(vSelected); j++ )
            {
                b = Vec_IntEntry(vSelected, j); y = (Vec_IntEntry(vRanks, b)-low)/2;
                rank = x+y+low+(a != b); edge = Acec2_ExprEdgeFind(e, nEdges, a, b);
                if ( rank < 0 || rank >= Width )
                { if ( edge >= 0 && e[edge].Rank != -2 ) valid = Abc_MinInt(valid, Abc_MaxInt(0, e[edge].Rank)); continue; }
                if ( edge < 0 || e[edge].Rank == -2 ) { valid = Abc_MinInt(valid, rank); continue; }
                if ( e[edge].Rank < 0 ) { valid = 0; continue; }
                if ( e[edge].Rank != rank ) { valid = Abc_MinInt(valid, Abc_MinInt(rank, e[edge].Rank)); continue; }
                neg = ((mode & 1) && ((x == Vec_IntSize(vBus)-1) ^ (y == Vec_IntSize(vBus)-1))) ^ (mode >> 1);
                if ( e[edge].Sign != neg ) valid = Abc_MinInt(valid, rank+1);
            }
        }
        if ( valid <= best || valid < 2 || valid <= low ) continue;
        best = valid; p->fSigned[0] = p->fSigned[1] = mode & 1; p->fNeg = mode >> 1;
        if ( best == Width ) break;
    }
finish:
    Vec_IntFreeP(&vRanks); Vec_IntFreeP(&vSeen); Vec_IntFreeP(&vQueue); Vec_IntFreeP(&vBus);
    if ( !best || Acec2_Stopped(m) ) { Acec2_ProductFree(p); Vec_IntClear(vSelected); return NULL; }
    *pWidth = best; return p;
}

/**Function*************************************************************

  Synopsis    [Certifies product factors within one weighted region.]

  Description [No word ordering, second design, or shared-signal assumption
  enters recognition. A record states an identity modulo its explicit width
  in the original design. Multiple roots retain their weighted encoding.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Expr_t * Acec2_ExprBoundary( Acec2_Man_t * m, int Tree, int Width, Vec_Int_t * vLeaves,
                                         Vec_Int_t * vBias, int fProposal )
{
    Vec_Int_t * vLits = Vec_IntAlloc(100);
    Vec_Int_t * vColor = NULL, * vRank = NULL, * vNodes = Vec_IntAlloc(100), * vAdjRow, * vUsed = Vec_IntStart(Vec_IntSize(vLeaves)/2);
    Vec_Int_t * vProductWidths = Vec_IntAlloc(4), * vGroup = NULL, * vSquare = Vec_IntAlloc(16);
    Vec_Wec_t * vAdj = NULL;
    Acec2_ExprRaw_t * r = ABC_ALLOC(Acec2_ExprRaw_t, Vec_IntSize(vLeaves)/2);
    Acec2_ExprEdge_t * e = NULL;
    Acec2_Expr_t * p = ABC_CALLOC(Acec2_Expr_t, 1);
    Acec2_Product_t * product;
    Gia_Obj_t * o;
    int i, j, k, id, a, b, lit, rank, start, next, edge, bad, width, bestWidth = 0, nRaw = 0, nEdges = 0;
    p->Tree = Tree; p->Width = Abc_MinInt(Width, m->Pars.nMaxWidth);
    p->vProducts = Vec_PtrAlloc(4); p->vAddends = Vec_IntAlloc(100); p->vConstant = Vec_IntStart(p->Width);
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) goto finish;
        lit = Vec_IntEntry(vLeaves, i); rank = Vec_IntEntry(vLeaves, i+1);
        if ( rank >= p->Width || lit < 2 ) continue;
        o = Gia_ManObj(m->pGia, lit >> 1);
        if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
        a = Gia_ObjFaninLit0p(m->pGia, o); b = Gia_ObjFaninLit1p(m->pGia, o);
        if ( a < 2 || b < 2 ) continue;
        if ( a > b ) ABC_SWAP(int, a, b);
        r[nRaw].a = a; r[nRaw].b = b; r[nRaw].Rank = 2*rank+(lit & 1); r[nRaw++].Leaf = i/2;
        Vec_IntPushTwo(vLits, a, b);
    }
    if ( nRaw < 3 ) goto finish;
    Vec_IntUniqify(vLits);
    // x*x is the literal x. Preserve such diagonal coefficients separately
    // from graph edges; an ordinary product may also have an operand addend.
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) goto finish;
        lit = Vec_IntEntry(vLeaves, i); rank = Vec_IntEntry(vLeaves, i+1);
        if ( rank >= p->Width || lit < 2 || Gia_ObjIsAnd(Gia_ManObj(m->pGia, lit >> 1)) ) continue;
        id = Acec2_ExprIndex(vLits, lit);
        if ( id < 0 ) id = Acec2_ExprIndex(vLits, lit ^ 1);
        if ( id < 0 ) continue;
        a = Vec_IntEntry(vLits, id); r[nRaw].a = r[nRaw].b = a;
        r[nRaw].Rank = 2*rank+((lit ^ a) & 1); r[nRaw++].Leaf = i/2;
    }
    qsort(r, nRaw, sizeof(Acec2_ExprRaw_t), Acec2_ExprRawCompare);
    if ( fProposal )
    {
        // Shared boundary occurrences can describe alternative carry paths.
        // Ignore repeated edges only when guessing operands; an observed
        // product word still requires a separate exact proof.
        for ( i = k = 0; i < nRaw; i++ )
            if ( !k || r[i].a != r[k-1].a || r[i].b != r[k-1].b || r[i].Rank != r[k-1].Rank ) r[k++] = r[i];
        nRaw = k;
    }
    e = ABC_CALLOC(Acec2_ExprEdge_t, nRaw); vAdj = Vec_WecStart(Vec_IntSize(vLits));
    for ( i = 0; i < nRaw; i = j )
    {
        for ( j = i+1; j < nRaw && r[i].a == r[j].a && r[i].b == r[j].b; j++ ) {}
        e[nEdges].a = a = Acec2_ExprIndex(vLits, r[i].a); e[nEdges].b = b = Acec2_ExprIndex(vLits, r[i].b);
        e[nEdges].First = i; e[nEdges].End = j; e[nEdges].Product = -1;
        e[nEdges].Rank = Acec2_ExprPower(r, i, j, p->Width, &e[nEdges].Sign);
        if ( a != b && e[nEdges].Rank != -2 ) { Vec_WecPush(vAdj, a, nEdges); Vec_WecPush(vAdj, b, nEdges); }
        nEdges++;
    }
    vColor = Vec_IntStartFull(Vec_IntSize(vLits)); vRank = Vec_IntStart(Vec_IntSize(vLits)); vGroup = Vec_IntStart(Vec_IntSize(vLits));
    for ( start = 0; start < Vec_IntSize(vLits); start++ )
    {
        if ( Acec2_Stopped(m) ) goto finish;
        if ( Vec_IntEntry(vColor, start) >= 0 || !Vec_IntSize(Vec_WecEntry(vAdj, start)) ) continue;
        Vec_IntClear(vNodes); Vec_IntPush(vNodes, start); Vec_IntWriteEntry(vColor, start, 0); bad = 0;
        for ( i = 0; i < Vec_IntSize(vNodes); i++ )
        {
            id = Vec_IntEntry(vNodes, i); vAdjRow = Vec_WecEntry(vAdj, id);
            Vec_IntForEachEntry(vAdjRow, edge, j)
            {
                next = e[edge].a ^ e[edge].b ^ id; bad |= e[edge].Rank < 0;
                rank = e[edge].Rank-Vec_IntEntry(vRank, id);
                if ( rank < -2*p->Width || rank > 2*p->Width ) { bad = 1; rank = 0; }
                if ( Vec_IntEntry(vColor, next) < 0 )
                {
                    Vec_IntWriteEntry(vColor, next, Vec_IntEntry(vColor, id) ^ 1);
                    Vec_IntWriteEntry(vRank, next, rank); Vec_IntPush(vNodes, next);
                }
                else bad |= Vec_IntEntry(vColor, next) == Vec_IntEntry(vColor, id) || Vec_IntEntry(vRank, next) != rank;
            }
        }
        if ( bad )
        {
            product = Acec2_ExprSquare(m, vNodes, vLits, vAdj, e, nEdges, p->Width, vSquare, &width);
            if ( !product ) continue;
            Vec_IntFill(vGroup, Vec_IntSize(vLits), 0);
            Vec_IntForEachEntry(vSquare, id, i) Vec_IntWriteEntry(vGroup, id, 1);
            Vec_IntForEachEntry(vSquare, id, i)
            {
                edge = Acec2_ExprEdgeFind(e, nEdges, id, id);
                if ( edge >= 0 ) e[edge].Product = Vec_PtrSize(p->vProducts);
                vAdjRow = Vec_WecEntry(vAdj, id);
                Vec_IntForEachEntry(vAdjRow, edge, j)
                {
                    next = e[edge].a ^ e[edge].b ^ id;
                    if ( Vec_IntEntry(vGroup, next) ) e[edge].Product = Vec_PtrSize(p->vProducts);
                }
            }
            Vec_PtrPush(p->vProducts, product); Vec_IntPush(vProductWidths, width);
        }
        else width = Acec2_ExprFactors(m, p, vNodes, vLits, vColor, vRank, vGroup, vAdj, e, nEdges, vProductWidths, fProposal);
        bestWidth = Abc_MaxInt(bestWidth, width);
    }
    if ( !Vec_PtrSize(p->vProducts) ) goto finish;
    p->Width = bestWidth; Vec_IntShrink(p->vConstant, bestWidth);
    for ( i = 0; i < nEdges; i++ )
        if ( e[i].Product >= 0 && Vec_IntEntry(vProductWidths, e[i].Product) == bestWidth )
            for ( j = e[i].First; j < e[i].End; j++ )
            {
                Vec_IntWriteEntry(vUsed, r[j].Leaf, 1);
                if ( r[j].Rank & 1 ) Acec2_ExprConstant(p->vConstant, r[j].Rank >> 1);
            }
    k = 0;
    Vec_PtrForEachEntry(Acec2_Product_t *, p->vProducts, product, i)
        if ( Vec_IntEntry(vProductWidths, i) == bestWidth ) Vec_PtrWriteEntry(p->vProducts, k++, product);
        else Acec2_ProductFree(product);
    Vec_PtrShrink(p->vProducts, k);
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 )
    {
        lit = Vec_IntEntry(vLeaves, i); rank = Vec_IntEntry(vLeaves, i+1);
        if ( rank >= p->Width || Vec_IntEntry(vUsed, i/2) || lit == 0 ) continue;
        if ( lit == 1 ) Acec2_ExprConstant(p->vConstant, rank);
        else Vec_IntPushTwo(p->vAddends, lit, rank);
    }
    Vec_IntForEachEntry(vBias, k, i) Acec2_ExprConstant(p->vConstant, k);
finish:
    ABC_FREE(r); ABC_FREE(e); Vec_IntFree(vLits); Vec_IntFree(vNodes); Vec_IntFree(vUsed); Vec_IntFree(vProductWidths); Vec_IntFree(vSquare);
    Vec_IntFreeP(&vColor); Vec_IntFreeP(&vRank); Vec_IntFreeP(&vGroup); Vec_WecFreeP(&vAdj);
    if ( !Vec_PtrSize(p->vProducts) || Acec2_Stopped(m) ) { Acec2_ExprFree(p); return NULL; }
    return p;
}

/**Function*************************************************************

  Synopsis    [Reads the weighted boundary of an original cell region.]

  Description [Optional parity leaves affect proposals only.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Expr_t * Acec2_ExprRegion( Acec2_Man_t * m, int Tree, int fProposal, Vec_Int_t * vProposalLeaves )
{
    return Acec2_ExprBoundary(m, Tree, Vec_IntEntry(m->vWidths, Tree),
        vProposalLeaves ? vProposalLeaves : Vec_WecEntry(m->vLeaves, Tree), Vec_WecEntry(m->vBias, Tree), fProposal);
}

/**Function*************************************************************

  Synopsis    [Finds operand groups in a component's aggregated coefficient graph.]

  Description [A temporary arithmetic cut represents polynomial variables
  as inputs and bilinear terms as bit products. This reuses the checked
  factor finder without requiring those AND gates in the source netlist.
  Returned operand literals refer exclusively to the original source.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Ptr_t * Acec2_RecordFactorsInt( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap, int * pWidth, int fProposal )
{
    Acec2_Man_t sample = *m; Gia_Man_t * g;
    Acec2_Expr_t * e = NULL; Acec2_Product_t * product;
    Vec_Wec_t * cols; Vec_Int_t * constants, * v, * ownedMap = NULL; Vec_Ptr_t * result = NULL;
    int i, j, k, lit, pairs = 0, valid = 1;
    *pWidth = 0;
    Vec_WecForEachLevel(r->vMonomials, v, i) pairs += Vec_IntSize(v) == 2;
    if ( r->Width < 4 || pairs < 3 || Acec2_Stopped(m) ) return NULL;
    if ( !vMap ) vMap = ownedMap = Vec_IntStart(Gia_ManObjNum(m->pGia));
    g = Gia_ManStart(Abc_MaxInt(100, 2*Vec_WecSize(r->vMonomials))); Gia_ManHashAlloc(g);
    Vec_IntForEachEntry(r->vCut, lit, i) Vec_IntWriteEntry(vMap, lit >> 1, Gia_ManAppendCi(g));
    cols = Vec_WecStart(r->Width); constants = Vec_IntStart(r->Width);
    sample.pGia = g; sample.vLeaves = Vec_WecStart(1); sample.vBias = Vec_WecStart(1); sample.vWidths = Vec_IntAlloc(1);
    Vec_IntPush(sample.vWidths, r->Width);
    if ( !Acec2_RecordColumns(r, g, vMap, NULL, cols, constants, &m->Pars, m->Deadline, 1000000) ) goto finish;
    Vec_WecForEachLevel(cols, v, i)
    {
        if ( Vec_IntSize(Vec_WecEntry(sample.vLeaves, 0)) > 200000 ) { m->nExprLimits++; goto finish; }
        Vec_IntForEachEntry(v, lit, j) Vec_IntPushTwo(Vec_WecEntry(sample.vLeaves, 0), lit, i);
        if ( Vec_IntEntry(constants, i) ) Vec_WecPush(sample.vBias, 0, i);
    }
    e = Acec2_ExprRegion(&sample, 0, fProposal, NULL); m->nExprLimits = sample.nExprLimits;
    if ( !e ) goto finish;
    Vec_PtrForEachEntry(Acec2_Product_t *, e->vProducts, product, i)
        for ( j = 0; j < 2; j++ )
            Vec_IntForEachEntry(product->vOperands[j], lit, k)
            {
                if ( lit < 2 ) continue;
                if ( (lit >> 1) > Vec_IntSize(r->vCut) ) { valid = 0; break; }
                Vec_IntWriteEntry(product->vOperands[j], k, Vec_IntEntry(r->vCut, (lit >> 1)-1) ^ (lit & 1));
            }
    if ( valid ) { *pWidth = e->Width; result = e->vProducts; e->vProducts = Vec_PtrAlloc(0); }
finish:
    Acec2_ExprFree(e); Vec_WecFree(cols); Vec_IntFree(constants); Vec_IntFreeP(&ownedMap);
    Vec_WecFree(sample.vLeaves); Vec_WecFree(sample.vBias); Vec_IntFree(sample.vWidths); Gia_ManStop(g);
    return result;
}

/**Function*************************************************************

  Synopsis    [Returns exact product factors of a weighted source identity.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Acec2_RecordFactors( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap, int * pWidth )
{
    return Acec2_RecordFactorsInt(m, r, vMap, pWidth, 0);
}

/**Function*************************************************************

  Synopsis    [Proposes operands from incomplete bilinear coefficient graphs.]

  Description [Missing low columns or product edges do not certify an
  arithmetic identity. The caller owns these operand guesses and must prove
  an observed result word before retaining any component record.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Acec2_RecordProductProposals( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap )
{
    int width;
    return Acec2_RecordFactorsInt(m, r, vMap, &width, 1);
}

/**Function*************************************************************

  Synopsis    [Extends top-column evidence through surviving parity cuts.]

  Description [A truncated multiplier's highest sum can have no carry cell.
  XOR cuts reached from a region's top roots reveal additional bit products
  at the same weight. This bounded extension only proposes operands; its
  ranks never authorize a replacement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acec2_ProductLeaves( Acec2_Man_t * m, int Tree )
{
    Vec_Int_t * vLeaves = Vec_IntDup(Vec_WecEntry(m->vLeaves, Tree));
    Vec_Int_t * vRoots = Vec_WecEntry(m->vRoots, Tree), * vRanks = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
    Vec_Bit_t * vSeen = Vec_BitStart(Gia_ManObjNum(m->pGia));
    int i, j, r, id, rank, maxRank = 0, pass, added = 0, limited = 0, * cut;
    for ( i = 0; i < Vec_IntSize(vRoots); i += 2 )
    {
        id = Vec_IntEntry(vRoots, i) >> 1; rank = Vec_IntEntry(vRoots, i+1);
        if ( rank > maxRank ) maxRank = rank;
        if ( Vec_IntEntry(vRanks, id) < 0 ) Vec_IntWriteEntry(vRanks, id, rank);
    }
    for ( i = 0; i < Vec_IntSize(vLeaves); i += 2 ) Acec2_BitWrite(vSeen, Vec_IntEntry(vLeaves, i) >> 1, 1);
    for ( pass = 0; pass < 2 && !limited && !Acec2_Stopped(m); pass++ )
        for ( i = 0; i < Vec_IntSize(m->vXors) && !limited; i += 5 )
        {
            if ( (i % 5120) == 0 && Acec2_Stopped(m) ) break;
            cut = Vec_IntEntryP(m->vXors, i); rank = -1;
            for ( j = 0; j < cut[0]; j++ )
            {
                r = Vec_IntEntry(vRanks, cut[j+1]);
                if ( r < 0 ) continue;
                if ( rank >= 0 && rank != r ) break;
                rank = r;
            }
            if ( j < cut[0] || rank < 0 || rank < maxRank-1 ) continue;
            id = cut[4] >> 1; r = Vec_IntEntry(vRanks, id);
            if ( r >= 0 && r != rank ) continue;
            Vec_IntWriteEntry(vRanks, id, rank);
            for ( j = 0; j < cut[0]; j++ )
            {
                id = cut[j+1];
                if ( Vec_IntEntry(vRanks, id) >= 0 || Vec_BitEntry(vSeen, id) || !Gia_ObjIsAnd(Gia_ManObj(m->pGia, id)) ) continue;
                if ( added == 128 ) { limited = 1; m->nProductLeafLimits++; break; }
                Vec_IntPushTwo(vLeaves, 2*id, rank); Acec2_BitWrite(vSeen, id, 1); added++;
            }
        }
    Vec_IntFree(vRanks); Vec_BitFree(vSeen); return vLeaves;
}

/**Function*************************************************************

  Synopsis    [Proposes an operand grid from a record's weighted boundary.]

  Description [Uses the record's actual ranked leaves and constant terms.
  Alternative cell partitions need no original tree ID. Product factors
  remain proposals until the independent weighted gap checks complete.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Acec2_RecordProductGrid( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Expr_t * e; Vec_Ptr_t * result; int i, lit, rank;
    if ( !m || !r || !r->vTerms || !r->vConstants || r->Width < 4 || r->Width > m->Pars.nMaxWidth ||
         r->Word >= 0 || r->Proof || r->Compose || r->Extend || (Vec_IntSize(r->vTerms) & 1) ||
         r->vOutputMasks || r->pProductReference || Vec_IntSize(r->vTerms) < 8 || Acec2_Stopped(m) ) return NULL;
    if ( Vec_IntSize(r->vTerms) > 32768 ) { m->nProductLeafLimits++; return NULL; }
    for ( i = 0; i < Vec_IntSize(r->vTerms); i += 2 )
    {
        lit = Vec_IntEntry(r->vTerms, i); rank = Vec_IntEntry(r->vTerms, i+1);
        if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || rank < 0 || rank >= r->Width ||
             Gia_ObjIsCo(Gia_ManObj(m->pGia, lit >> 1)) ) return NULL;
    }
    Vec_IntForEachEntry(r->vConstants, rank, i) if ( rank < 0 || rank >= r->Width ) return NULL;
    e = Acec2_ExprBoundary(m, r->Tree, r->Width, r->vTerms, r->vConstants, 2);
    if ( !e ) return NULL;
    result = e->vProducts; e->vProducts = Vec_PtrAlloc(0); Acec2_ExprFree(e); return result;
}

/**Function*************************************************************

  Synopsis    [Proposes unshifted operand words for independent certification.]

  Description [The proposal queue retains both original region boundaries
  and bounded top-column parity extensions. No guess is a certificate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Acec2_RegionProductProposals( Acec2_Man_t * m, int Tree )
{
    Acec2_Expr_t * e;
    Vec_Ptr_t * result;
    Vec_Int_t * leaves;
    Acec2_Product_t * product, * previous;
    int i, j, side;
    if ( Vec_IntSize(Vec_WecEntry(m->vTrees, Tree)) < 4 ||
         Vec_IntSize(Vec_WecEntry(m->vLeaves, Tree)) > 2048 ||
         Vec_IntEntry(m->vWidths, Tree) < 4 || Acec2_Stopped(m) ) return NULL;
    // Keep the original weighted interpretation first. Top-column parity
    // can reveal missing operand bits, but can also contain unrelated logic.
    // Its proposals must not displace candidates already supplied by cells.
    e = Acec2_ExprRegion(m, Tree, 1, NULL);
    result = e ? e->vProducts : Vec_PtrAlloc(0);
    if ( e ) { e->vProducts = Vec_PtrAlloc(0); Acec2_ExprFree(e); }
    leaves = Acec2_ProductLeaves(m, Tree);
    e = Vec_IntEqual(leaves, Vec_WecEntry(m->vLeaves, Tree)) ? NULL : Acec2_ExprRegion(m, Tree, 1, leaves);
    Vec_IntFree(leaves);
    if ( e )
    {
        Vec_PtrForEachEntry(Acec2_Product_t *, e->vProducts, product, i)
        {
            Vec_PtrForEachEntry(Acec2_Product_t *, result, previous, j)
            {
                if ( product->fNeg != previous->fNeg || product->Shift != previous->Shift ) continue;
                for ( side = 0; side < 2; side++ )
                    if ( product->fSigned[side] != previous->fSigned[side] ||
                         !Vec_IntEqual(product->vOperands[side], previous->vOperands[side]) ) break;
                if ( side == 2 ) break;
            }
            if ( j == Vec_PtrSize(result) ) Vec_PtrPush(result, product);
            else { Vec_IntFree(product->vOperands[0]); Vec_IntFree(product->vOperands[1]); ABC_FREE(product); }
        }
        Vec_PtrClear(e->vProducts); Acec2_ExprFree(e);
    }
    if ( !Vec_PtrSize(result) ) { Vec_PtrFree(result); return NULL; }
    return result;
}

/**Function*************************************************************

  Synopsis    [Recognizes one requested region without closing other words.]

  Description [Weighted multi-root results remain weighted. Recognition
  alone never authorizes replacing individual roots with product bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_FindExpression( Acec2_Man_t * m, int Tree )
{
    Acec2_Expr_t * p;
    if ( Tree < 0 || Tree >= Vec_WecSize(m->vTrees) || Acec2_Stopped(m) ) return;
    Vec_IntFillExtra(m->vTreeExpression, Vec_WecSize(m->vTrees), -1);
    if ( Vec_IntEntry(m->vTreeExpression, Tree) != -1 ) return;
    if ( Vec_IntSize(Vec_WecEntry(m->vLeaves, Tree)) < 6 || Vec_IntEntry(m->vWidths, Tree) < 2 )
        { Vec_IntWriteEntry(m->vTreeExpression, Tree, -2); return; }
    if ( Abc_MinInt(Vec_IntEntry(m->vWidths, Tree), m->Pars.nMaxWidth) > 65536 )
        { m->nExprLimits++; Vec_IntWriteEntry(m->vTreeExpression, Tree, -2); return; }
    p = Acec2_ExprRegion(m, Tree, 0, NULL);
    if ( !p )
    {
        if ( !Acec2_Stopped(m) ) Vec_IntWriteEntry(m->vTreeExpression, Tree, -2);
        return;
    }
    Vec_IntWriteEntry(m->vTreeExpression, Tree, Vec_PtrSize(m->vExpressions));
    m->nProducts += Vec_PtrSize(p->vProducts); Vec_PtrPush(m->vExpressions, p);
}

/**Function*************************************************************

  Synopsis    [Retains independently recognized product expressions.]

  Description [Previously requested regions are reused. Source cells and
  weighted regions remain immutable during expression recognition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_FindExpressions( Acec2_Man_t * m )
{
    int tree;
    for ( tree = 0; tree < Vec_WecSize(m->vTrees) && !Acec2_Stopped(m); tree++ )
        Acec2_FindExpression(m, tree);
}

/**Function*************************************************************

  Synopsis    [Expands a complete operand using an integer cell identity.]

  Description [All weighted roots must be exactly the complete operand bus.
  This is stronger than equality of a truncated word modulo its width. A
  signed operand whose top bit complements the region's top root equals
  the unsigned region value minus 2^(width-1), exactly over the integers.
  Partial results, extra carries, and other signed boundaries keep their
  original bits. No modular identity is lifted into a wider product.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acec2_ExprOperand( Acec2_Man_t * m, Vec_Int_t * vBits, int fSigned, int * pLifted, abctime Deadline )
{
    Vec_Int_t * vTrees = Vec_IntAlloc(8), * vTerms = Vec_IntAlloc(2*Vec_IntSize(vBits));
    Vec_Int_t * vRoots, * vWord = Vec_IntStart(Vec_IntSize(vBits)), * vConst = Vec_IntStart(Vec_IntSize(vBits)+2), * v;
    int i, j, lit, owner, tree, rank, count, Width = Vec_IntSize(vBits);
    *pLifted = 0;
    if ( !fSigned || Width >= 3 )
        Vec_IntForEachEntry(vBits, lit, i)
        {
            owner = Vec_IntEntry(m->vOwner, lit >> 1);
            if ( owner < 0 ) continue;
            tree = Acec2_Cell(m, owner/2)->Tree;
            if ( Vec_IntEntry(m->vNormal, tree) && Vec_IntEntry(m->vWidths, tree) == Vec_IntSize(vBits) ) Vec_IntPushUnique(vTrees, tree);
        }
    Vec_IntForEachEntry(vTrees, tree, i)
    {
        if ( Acec2_Stop(&m->Pars, Deadline) ) break;
        Vec_IntFill(vWord, Vec_IntSize(vBits), 0); vRoots = Vec_WecEntry(m->vRoots, tree);
        for ( j = 0; j < Vec_IntSize(vRoots); j += 2 )
            Vec_IntWriteEntry(vWord, Vec_IntEntry(vRoots, j+1), Vec_IntEntry(vRoots, j));
        for ( j = 0; j < Width; j++ )
            if ( Vec_IntEntry(vWord, j) != (Vec_IntEntry(vBits, j) ^ (fSigned && j == Width-1)) ) break;
        if ( j != Vec_IntSize(vBits) ) continue;
        // The extra coefficient bits prevent a modular wrap from concealing
        // a wrong integer composition before lifting it into multiplication.
        if ( Width > 65472 || !Acec2_CheckRegion(m, tree, Width+64) ) continue;
        v = Vec_WecEntry(m->vLeaves, tree);
        for ( j = 0; j < Vec_IntSize(v); j += 2 )
        {
            lit = Vec_IntEntry(v, j); rank = Vec_IntEntry(v, j+1);
            if ( fSigned && rank == Width-2 && (lit & 1) )
            {
                Vec_IntPushTwo(vTerms, lit ^ 1, 2*rank+1); Vec_IntAddToEntry(vConst, rank, 1);
            }
            else Vec_IntPushTwo(vTerms, lit, 2*rank);
        }
        Vec_IntForEachEntry(Vec_WecEntry(m->vBias, tree), rank, j) Vec_IntAddToEntry(vConst, rank, 1);
        if ( fSigned ) Vec_IntAddToEntry(vConst, Width-1, -1);
        for ( rank = 0; rank < Vec_IntSize(vConst); rank++ )
        {
            count = Vec_IntEntry(vConst, rank);
            if ( count % 2 ) Vec_IntPushTwo(vTerms, 1, 2*rank+(count < 0));
            if ( count/2 )
            {
                if ( rank+1 == Vec_IntSize(vConst) ) Vec_IntPush(vConst, 0);
                Vec_IntAddToEntry(vConst, rank+1, count/2);
            }
        }
        *pLifted = tree+1; break;
    }
    if ( !*pLifted )
        Vec_IntForEachEntry(vBits, lit, i) if ( lit ) Vec_IntPushTwo(vTerms, lit, 2*i+(fSigned && i == Vec_IntSize(vBits)-1));
    Vec_IntFree(vTrees); Vec_IntFree(vWord); Vec_IntFree(vConst); return vTerms;
}

/**Function*************************************************************

  Synopsis    [Adds a signed Boolean term to canonical compressor columns.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ExprPut( Vec_Wec_t * vCols, Vec_Int_t * vConst, int Lit, int Rank, int fNeg )
{
    int k, bit;
    if ( !Lit ) return;
    Vec_WecPush(vCols, Rank, Lit ^ fNeg);
    if ( !fNeg ) return;
    for ( k = Rank; k < Vec_IntSize(vConst); k++ )
    {
        bit = Vec_IntEntry(vConst, k); Vec_IntWriteEntry(vConst, k, bit ^ 1);
        if ( bit ) break;
    }
}

/**Function*************************************************************

  Synopsis    [Expands one product, retaining carries from a discarded low bit.]

  Description [Operand composition is justified over the integers. When the
  product is right shifted, expanded low partial products may sum above one.
  Compress that column and retain all its carries before discarding its sum.
  Global negation still applies after the shift.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ExprProductColumns( Acec2_Man_t * m, Acec2_Product_t * p, Gia_Man_t * g, Vec_Int_t * vMap,
    Vec_Wec_t * vCols, Vec_Int_t * vConst, int nMaxObjs, abctime Deadline )
{
    Vec_Int_t * vTerms[2], * vLowConst = NULL, * vNext = NULL;
    Vec_Wec_t * vLow = NULL;
    int i, j, lit, a, b, x, y, rank, neg, Width = Vec_IntSize(vConst), lifted[2], result = 0;
    for ( i = 0; i < 2; i++ ) vTerms[i] = Acec2_ExprOperand(m, p->vOperands[i], p->fSigned[i], &lifted[i], Deadline);
    if ( (ABC_INT64_T)(Vec_IntSize(vTerms[0])/2)*(Vec_IntSize(vTerms[1])/2) > 2000000 ) { m->nExprLimits++; goto finish; }
    if ( p->Shift == -1 && (lifted[0] || lifted[1]) )
    { vLow = Vec_WecStart(Width+1); vLowConst = Vec_IntStart(Width+1); vNext = Vec_IntAlloc(16); }
    for ( i = 0; i < Vec_IntSize(vTerms[0]); i += 2 )
    {
        if ( Acec2_Stop(&m->Pars, Deadline) ) goto finish;
        a = Vec_IntEntry(vTerms[0], i); x = Vec_IntEntry(vMap, a >> 1) ^ (a & 1);
        for ( j = 0; j < Vec_IntSize(vTerms[1]); j += 2 )
        {
            a = Vec_IntEntry(vTerms[0], i+1); b = Vec_IntEntry(vTerms[1], j+1);
            rank = (a >> 1)+(b >> 1)+p->Shift;
            if ( rank >= Width || (rank < 0 && !vLow) ) continue;
            neg = (a ^ b) & 1;
            b = Vec_IntEntry(vTerms[1], j); y = Vec_IntEntry(vMap, b >> 1) ^ (b & 1);
            lit = Gia_ManHashAnd(g, x, y);
            if ( Gia_ManObjNum(g) >= nMaxObjs ) goto finish;
            if ( rank < 0 )
            {
                if ( rank != -1 || neg ) goto finish;
                Vec_WecPush(vLow, 0, lit);
            }
            else Acec2_ExprPut(vCols, vConst, lit, rank, neg ^ p->fNeg);
        }
    }
    if ( vLow )
    {
        lit = Acec2_CompressColumn(g, vLow, vLowConst, vNext, 0, &m->Pars, Deadline, nMaxObjs);
        if ( lit < 0 ) goto finish;
        // Adding the low constant bit may carry the retained variable sum.
        if ( Vec_IntEntry(vLowConst, 0) ) Acec2_ExprPut(vCols, vConst, lit, 0, p->fNeg);
        Vec_IntForEachEntry(Vec_WecEntry(vLow, 1), lit, i) Acec2_ExprPut(vCols, vConst, lit, 0, p->fNeg);
        for ( i = 1; i <= Width; i++ ) if ( Vec_IntEntry(vLowConst, i) ) Acec2_ExprPut(vCols, vConst, 1, i-1, p->fNeg);
    }
    result = !Acec2_Stop(&m->Pars, Deadline);
finish:
    Vec_IntFree(vTerms[0]); Vec_IntFree(vTerms[1]); Vec_IntFreeP(&vLowConst); Vec_IntFreeP(&vNext); Vec_WecFreeP(&vLow);
    return result;
}

/**Function*************************************************************

  Synopsis    [Expands a certified expression over the current proved map.]

  Description [This is an exact modular identity in the original design.
  The caller must separately have a certified binary boundary before using
  these columns to replace individual result bits. Negative terms become
  complemented compressor inputs with their constant correction.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ExprColumns( Acec2_Man_t * m, Acec2_Expr_t * e, Gia_Man_t * g, Vec_Int_t * vMap,
                      Vec_Wec_t * vCols, Vec_Int_t * vConst, int nMaxObjs, abctime Deadline )
{
    Acec2_Product_t * p;
    int Width = Vec_IntSize(vConst), index, i, lit, rank;
    if ( Width > e->Width || Acec2_Stop(&m->Pars, Deadline) ) return 0;
    for ( i = 0; i < Width; i++ ) Vec_IntWriteEntry(vConst, i, Vec_IntEntry(e->vConstant, i));
    for ( i = 0; i < Vec_IntSize(e->vAddends); i += 2 )
    {
        if ( (i & 255) == 0 && Acec2_Stop(&m->Pars, Deadline) ) return 0;
        lit = Vec_IntEntry(e->vAddends, i); rank = Vec_IntEntry(e->vAddends, i+1);
        if ( rank < Width ) Vec_WecPush(vCols, rank, Vec_IntEntry(vMap, lit >> 1) ^ (lit & 1));
    }
    Vec_PtrForEachEntry(Acec2_Product_t *, e->vProducts, p, index)
        if ( !Acec2_ExprProductColumns(m, p, g, vMap, vCols, vConst, nMaxObjs, Deadline) ) return 0;
    return !Acec2_Stop(&m->Pars, Deadline);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
