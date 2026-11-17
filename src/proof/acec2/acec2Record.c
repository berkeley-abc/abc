/**CFile****************************************************************

  FileName    [acec2Record.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Persistent, checked weighted component identities.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 14, 2026.]

  Revision    [$Id$]

  Description [A record relates weighted source output literals to a
  polynomial over source cut nodes modulo its explicit width. Source-domain
  records are valid on values produced by the source design. Equal records
  over proved corresponding cut signals therefore have equal weighted sums.
  Only a binary boundary or a certified prefix permits individual bit merges.]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef struct Acec2_RecordPoly_t_ Acec2_RecordPoly_t;
struct Acec2_RecordPoly_t_
{
    Hsh_VecMan_t * h;
    Vec_Wrd_t * vCoefs;
    Vec_Int_t * vMono;
    int Width, nWords;
};

static void Acec2_RecordCoefficient( Acec2_RecordPoly_t * p, word * coef, int Sign );
static int Acec2_RecordFactorCheck( Acec2_Record_t * r );
static void Acec2_RecordFactorPopulate( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap );
static Vec_Int_t * Acec2_RegionRecords( Acec2_Man_t * m, int Tree );
static int Acec2_RegionClass( Acec2_Man_t * m, int Tree );
static void Acec2_RecordExtendProducts( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vSelected );
static void Acec2_RecordComposeProducts( Acec2_Man_t * m, Vec_Int_t * vMap, int First, Vec_Int_t * vSelected, int * pnQueries );
static Acec2_RecordPoly_t * Acec2_RecordComposition( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vRegions );
static int Acec2_RecordCompositionCheck( Acec2_Man_t * m, Acec2_Record_t * r );
static int Acec2_RecordSubtractProduct( Acec2_RecordPoly_t * p, Acec2_Product_t * product, Vec_Int_t * vCut );
static void Acec2_RecordProductWords( Acec2_Man_t * m, Vec_Int_t * vMap );
static void Acec2_RecordSumWords( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vSelected, int * pnQueries );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates a modular polynomial accumulator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordPolyStart( int Width )
{
    Acec2_RecordPoly_t * p = ABC_CALLOC(Acec2_RecordPoly_t, 1);
    p->Width = Width; p->nWords = (Width+63)/64;
    p->h = Hsh_VecManStart(100); p->vCoefs = Vec_WrdAlloc(100); p->vMono = Vec_IntAlloc(4);
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases a polynomial accumulator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordPolyStop( Acec2_RecordPoly_t * p )
{
    Hsh_VecManStop(p->h); Vec_WrdFree(p->vCoefs); Vec_IntFree(p->vMono); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Adds a signed power of two to a square-free monomial.]

  Description [The empty monomial denotes one. Node zero denotes zero
  and is eliminated before insertion. Unsigned arithmetic defines all carries.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordPower( Acec2_RecordPoly_t * p, int a, int b, int Rank, int Sign )
{
    int id, i; word old, value, delta;
    if ( Rank < 0 || Rank >= p->Width || a == 0 || b == 0 ) return;
    Vec_IntClear(p->vMono);
    if ( a > 0 ) Vec_IntPush(p->vMono, a);
    if ( b > 0 ) Vec_IntPushUniqueOrder(p->vMono, b);
    id = Hsh_VecManAdd(p->h, p->vMono);
    while ( Vec_WrdSize(p->vCoefs) < (id+1)*p->nWords ) Vec_WrdPush(p->vCoefs, 0);
    delta = (word)1 << (Rank & 63);
    for ( i = Rank/64; i < p->nWords && delta; i++ )
    {
        old = Vec_WrdEntry(p->vCoefs, id*p->nWords+i);
        value = Sign > 0 ? old+delta : old-delta;
        Vec_WrdWriteEntry(p->vCoefs, id*p->nWords+i, value);
        delta = Sign > 0 ? value < old : old < delta;
    }
    if ( p->Width & 63 )
    {
        i = (id+1)*p->nWords-1;
        Vec_WrdWriteEntry(p->vCoefs, i, Vec_WrdEntry(p->vCoefs, i) & (((word)1 << (p->Width & 63))-1));
    }
}

/**Function*************************************************************

  Synopsis    [Re-derives the formula of an independently certified product.]

  Description [The source word certificate owns the operand interpretation.
  Every record is checked against that immutable formula, with explicit
  signedness, literal phases, repeated bits and modular output width.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordProductPoly( Acec2_Man_t * m, Acec2_Word_t * w )
{
    Acec2_RecordPoly_t * p; Acec2_Product_t product;
    Vec_Int_t * cut = Vec_IntAlloc(100); int side, i, lit, valid = 1;
    if ( !w->pProduct || w->pProduct->Shift || w->pProduct->fNeg ) { Vec_IntFree(cut); return NULL; }
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(w->pProduct->vOperands[side], lit, i)
        {
            if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) ) valid = 0;
            if ( lit >= 2 ) Vec_IntPush(cut, lit & ~1);
        }
    Vec_IntUniqify(cut); product = *w->pProduct; product.fNeg = 1;
    p = Acec2_RecordPolyStart(w->Width);
    if ( !valid || !Acec2_RecordSubtractProduct(p, &product, cut) ) { Acec2_RecordPolyStop(p); p = NULL; }
    Vec_IntFree(cut); return p;
}

/**Function*************************************************************

  Synopsis    [Re-derives a decoded product's immutable source reference.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordSourceProduct( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Word_t word;
    memset(&word, 0, sizeof(word)); word.Width = r->Width; word.pProduct = r->pProductReference;
    return Acec2_RecordProductPoly(m, &word);
}

/**Function*************************************************************

  Synopsis    [Borrows the product description of an unencoded record.]

  Description [The caller checks the record certificate and required width
  before using this description as a proof. Pattern discovery can also use
  it to propose assignments without making a claim about the source.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Product_t * Acec2_RecordProduct( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Word_t * w; int i, mask;
    if ( !m || !r ) return NULL;
    if ( r->vOutputMasks ) Vec_IntForEachEntry(r->vOutputMasks, mask, i) if ( mask ) return NULL;
    if ( r->pProductReference ) return r->pProductReference;
    if ( r->Word < 0 || r->Word >= Vec_PtrSize(m->vWords) ) return NULL;
    w = (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word);
    return w->Width == r->Width && Vec_IntSize(w->vBits) == w->Width && !w->vSumProducts ? w->pProduct : NULL;
}

/**Function*************************************************************

  Synopsis    [Builds the explicitly extended sum of certified product records.]

  Description [Both observed product words and source product certificates
  use their checked binary record boundary. Missing ranks are zero. A
  partial product or an encoded output cannot justify a wider extension.
  Negation follows shifting, modulo the new word width.]

  SideEffects [Appends reference terms and constants.]

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordSumTerms( Acec2_Man_t * m, Acec2_Word_t * w, Vec_Int_t * terms, Vec_Int_t * constants )
{
    Acec2_Record_t * r; Acec2_Product_t * product; Vec_Int_t * bits;
    int i, j, id, shift, neg, lit, width;
    if ( !w->vSumProducts || !Vec_IntSize(w->vSumProducts) || Vec_IntSize(w->vSumProducts) % 3 ||
         w->Width < 1 || w->Width > m->Pars.nMaxWidth ) return 0;
    for ( i = 0; i < Vec_IntSize(w->vSumProducts); i += 3 )
    {
        id = Vec_IntEntry(w->vSumProducts, i); shift = Vec_IntEntry(w->vSumProducts, i+1);
        neg = Vec_IntEntry(w->vSumProducts, i+2);
        if ( id < 0 || id >= Vec_PtrSize(m->vRecords) || shift < 0 || shift > m->Pars.nMaxWidth || (neg & ~1) ) return 0;
        r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, id);
        product = Acec2_RecordProduct(m, r);
        if ( !product || product->Shift || product->fNeg || r->Prefix != r->Width ) return 0;
        width = Vec_IntSize(product->vOperands[0])+Vec_IntSize(product->vOperands[1]);
        if ( r->Width < width || !Acec2_RecordCheck(m, r) || Acec2_Stopped(m) ) return 0;
        bits = Vec_IntStart(r->Width);
        for ( j = 0; j < Vec_IntSize(r->vOutputs); j += 2 )
            Vec_IntWriteEntry(bits, Vec_IntEntry(r->vOutputs, j+1), Vec_IntEntry(r->vOutputs, j));
        for ( j = 0; j+shift < w->Width; j++ )
        {
            lit = j < r->Width ? Vec_IntEntry(bits, j) :
                (product->fSigned[0] || product->fSigned[1]) ? Vec_IntEntryLast(bits) : 0;
            if ( lit ^ neg ) Vec_IntPushTwo(terms, lit ^ neg, j+shift);
        }
        Vec_IntFree(bits);
        if ( neg && shift < w->Width ) Vec_IntPush(constants, shift);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the sum reference and composes its certified products.]

  Description [The new addition has its own free-cut proof. Complete product
  certificates justify only substitution and extension of its input words;
  no high bit is inferred from a truncated arithmetic identity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordSumPoly( Acec2_Man_t * m, Acec2_Word_t * w )
{
    Acec2_RecordPoly_t * p = NULL;
    Vec_Int_t * terms = Vec_IntAlloc(32), * constants = Vec_IntAlloc(8), * cut = Vec_IntAlloc(32), * sourceCut = Vec_IntAlloc(32);
    Acec2_Record_t * r; Acec2_Product_t product;
    int i, j, side, lit;
    if ( !w->fIndependent || w->fPolynomial || w->pProduct || w->Tree != -1 || w->Record != -1 ||
         !Acec2_RecordSumTerms(m, w, terms, constants) || !Vec_IntEqual(terms, w->vTerms) ||
         !Vec_IntEqual(constants, w->vConstants) ) goto finish;
    p = Acec2_RecordPolyStart(w->Width);
    for ( i = 0; i < Vec_IntSize(w->vSumProducts); i += 3 )
    {
        r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Vec_IntEntry(w->vSumProducts, i));
        product = *Acec2_RecordProduct(m, r);
        product.Shift = Vec_IntEntry(w->vSumProducts, i+1); product.fNeg = !Vec_IntEntry(w->vSumProducts, i+2);
        Vec_IntClear(cut);
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(product.vOperands[side], lit, j) if ( lit >= 2 ) Vec_IntPush(cut, lit & ~1);
        Vec_IntUniqify(cut);
        Vec_IntAppend(sourceCut, cut);
        if ( product.Shift >= w->Width ) continue;
        if ( !Acec2_RecordSubtractProduct(p, &product, cut) ) { Acec2_RecordPolyStop(p); p = NULL; break; }
    }
    Vec_IntUniqify(sourceCut);
    if ( p && w->vSourceCut && !Vec_IntEqual(sourceCut, w->vSourceCut) ) { Acec2_RecordPolyStop(p); p = NULL; }
finish:
    Vec_IntFree(terms); Vec_IntFree(constants); Vec_IntFree(cut); Vec_IntFree(sourceCut); return p;
}

/**Function*************************************************************

  Synopsis    [Expands one literal using its exact gate, when requested.]

  Description [Complemented and repeated inputs are handled algebraically.
  Arithmetic cuts remain source literals; names and the other design are
  never used to construct or justify the polynomial.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordLiteral( Acec2_RecordPoly_t * p, Gia_Man_t * g,
                                 int Lit, int Rank, int Sign, int fExpand )
{
    Gia_Obj_t * o = Gia_ManObj(g, Lit >> 1);
    int a, b, ca, cb;
    if ( Lit & 1 ) { Acec2_RecordPower(p, -1, -1, Rank, Sign); Sign = -Sign; }
    if ( !fExpand || !Gia_ObjIsAnd(o) || Gia_ObjIsMux(g, o) || Gia_ObjIsXor(o) )
    { Acec2_RecordPower(p, Lit >> 1, -1, Rank, Sign); return; }
    a = Gia_ObjFaninLit0p(g, o); b = Gia_ObjFaninLit1p(g, o); ca = a & 1; cb = b & 1;
    if ( ca && cb ) Acec2_RecordPower(p, -1, -1, Rank, Sign);
    if ( cb ) Acec2_RecordPower(p, a >> 1, -1, Rank, ca ? -Sign : Sign);
    if ( ca ) Acec2_RecordPower(p, b >> 1, -1, Rank, cb ? -Sign : Sign);
    Acec2_RecordPower(p, a >> 1, b >> 1, Rank, ca == cb ? Sign : -Sign);
}

/**Function*************************************************************

  Synopsis    [Accumulates weighted literals and a constant word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordTerms( Acec2_RecordPoly_t * p, Gia_Man_t * g,
                               Vec_Int_t * vTerms, Vec_Int_t * vConstants, int Sign, int fExpand )
{
    int i, rank;
    for ( i = 0; i < Vec_IntSize(vTerms); i += 2 )
        Acec2_RecordLiteral(p, g, Vec_IntEntry(vTerms, i), Vec_IntEntry(vTerms, i+1), Sign, fExpand);
    if ( vConstants ) Vec_IntForEachEntry(vConstants, rank, i) Acec2_RecordPower(p, -1, -1, rank, Sign);
}

/**Function*************************************************************

  Synopsis    [Checks a composed region against its local exact identities.]

  Description [No simulation is involved. Every internal use must cancel
  with the correct literal, phase and weight. Shared uses left on the cut
  remain in the identity. Local cut/SAT certificates justify the cells.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordRegionCheck( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_RecordPoly_t * p = Acec2_RecordPolyStart(r->Width);
    Acec2_Cell_t * c; int i, j, id, good = 1;
    Acec2_RecordTerms(p, m->pGia, r->vOutputs, NULL, 1, 0);
    Acec2_RecordTerms(p, m->pGia, r->vTerms, r->vConstants, -1, 0);
    Vec_IntForEachEntry(Vec_WecEntry(m->vTrees, r->Tree), id, i)
    {
        c = Acec2_Cell(m, id);
        if ( !Acec2_CheckParityCell(m, c) ) { good = 0; break; }
        for ( j = 0; j < c->nIns; j++ ) Acec2_RecordLiteral(p, m->pGia, c->In[j] ^ c->Phase, c->Rank, 1, 0);
        for ( j = 0; j < 2; j++ ) Acec2_RecordLiteral(p, m->pGia, c->Out[j] ^ c->Phase, c->Rank+j, -1, 0);
        if ( c->nIns == 2 && c->Phase ) Acec2_RecordPower(p, -1, -1, c->Rank, 1);
    }
    for ( i = 0; i < Vec_WrdSize(p->vCoefs); i++ ) if ( Vec_WrdEntry(p->vCoefs, i) ) { good = 0; break; }
    Acec2_RecordPolyStop(p); return good;
}

/**Function*************************************************************

  Synopsis    [Checks a region identity at the modulus requested by a consumer.]

  Description [The same composition checker is used by stored records and
  polynomial rewrites. Its source cells are already independently checked.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CheckRegion( Acec2_Man_t * m, int Tree, int Width )
{
    Acec2_Record_t r;
    if ( !m || Tree < 0 || Tree >= Vec_WecSize(m->vTrees) || Width < 1 || Width > 65536 ) return 0;
    if ( (ABC_INT64_T)(Width+63)/64*(6*(ABC_INT64_T)Vec_IntSize(Vec_WecEntry(m->vTrees, Tree))+1) > 2000000 ) return 0;
    memset(&r, 0, sizeof(r)); r.Tree = Tree; r.Width = Width;
    r.vOutputs = Vec_WecEntry(m->vRoots, Tree); r.vTerms = Vec_WecEntry(m->vLeaves, Tree);
    r.vConstants = Vec_WecEntry(m->vBias, Tree);
    return !Acec2_Stopped(m) && Acec2_RecordRegionCheck(m, &r);
}

/**Function*************************************************************

  Synopsis    [Identifies records with an explicit weighted reference.]

  Description [A separately stored polynomial is not an empty linear sum.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordLinearReference( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Word_t * w;
    if ( r->Compose || r->vOutputMasks || r->pProductReference || r->fPolynomial ) return 0;
    if ( r->Word < 0 ) return 1;
    if ( r->Word >= Vec_PtrSize(m->vWords) ) return 0;
    w = (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word);
    return !w->pProduct && !w->fPolynomial && !w->vSumProducts;
}

/**Function*************************************************************

  Synopsis    [Checks integer cell and modular record composition.]

  Description [A referenced record must have an explicit weighted reference.
  Records whose formula is stored only as a polynomial cannot be substituted
  as an empty linear sum. Shifted modular identities retain their modulus.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordPartsCheck( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_RecordPoly_t * p = Acec2_RecordPolyStart(r->Width);
    Acec2_Record_t * parent; Vec_Int_t * deps = NULL, * terms;
    Acec2_Part_t b; int i, j, rank, phase, kind, id, here = -1, side, good = 0;
    if ( Vec_IntSize(r->vParts) % 4 ) goto finish;
    Acec2_RecordTerms(p, m->pGia, r->vOutputs, NULL, 1, 0);
    Acec2_RecordTerms(p, m->pGia, r->vTerms, r->vConstants, -1, 0);
    for ( i = 0; i < Vec_IntSize(r->vParts); i += 4 )
    {
        rank = Vec_IntEntry(r->vParts, i+2); phase = Vec_IntEntry(r->vParts, i+3);
        kind = Vec_IntEntry(r->vParts, i); id = Vec_IntEntry(r->vParts, i+1);
        if ( rank < 0 || rank >= m->Pars.nMaxWidth || (phase != 0 && phase != 1) ) goto finish;
        if ( kind == 3 )
        {
            if ( !deps )
            {
                deps = Vec_IntAlloc(4); here = Vec_PtrFind(m->vRecords, r);
                if ( here < 0 ) here = Vec_PtrSize(m->vRecords);
            }
            if ( phase || id < 0 || id >= here ) goto finish;
            parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, id);
            // Earlier records are immutable checked identities. Shifting
            // increases their modulus; it never justifies additional bits.
            if ( parent->Domain != 1 || parent->Width < r->Width-rank || !Acec2_RecordLinearReference(m, parent) ) goto finish;
            Vec_IntPushUnique(deps, id);
            for ( side = 0; side < 2; side++ )
            {
                terms = side ? parent->vTerms : parent->vOutputs;
                for ( j = 0; j < Vec_IntSize(terms); j += 2 )
                    Acec2_RecordLiteral(p, m->pGia, Vec_IntEntry(terms, j), rank+Vec_IntEntry(terms, j+1), side ? 1 : -1, 0);
            }
            Vec_IntForEachEntry(parent->vConstants, j, side) Acec2_RecordPower(p, -1, -1, rank+j, 1);
            continue;
        }
        if ( !Acec2_GetPart(m, kind, id, &b) ) goto finish;
        if ( kind < 2 && !Acec2_CheckParityCell(m, (Acec2_Cell_t *)Vec_PtrEntry(kind ? m->vAlternatives : m->vCells, id)) ) goto finish;
        if ( b.Kind == 2 && !Acec2_CounterCheck(m, (Acec2_Counter_t *)Vec_PtrEntry(m->vCounters, b.Id), NULL) ) goto finish;
        for ( j = 0; j < b.nIns; j++ )
        {
            Acec2_RecordLiteral(p, m->pGia, b.In[2*j] ^ phase, rank+b.In[2*j+1], 1, 0);
            if ( phase ) Acec2_RecordPower(p, -1, -1, rank+b.In[2*j+1], -1);
        }
        for ( j = 0; j < b.nOuts; j++ )
        {
            Acec2_RecordLiteral(p, m->pGia, b.Out[2*j] ^ phase, rank+b.Out[2*j+1], -1, 0);
            if ( phase ) Acec2_RecordPower(p, -1, -1, rank+b.Out[2*j+1], 1);
        }
    }
    if ( deps ? (!r->vDependencies || !Vec_IntEqual(deps, r->vDependencies)) : (r->vDependencies && Vec_IntSize(r->vDependencies)) ) goto finish;
    for ( i = 0; i < Vec_WrdSize(p->vCoefs); i++ ) if ( Vec_WrdEntry(p->vCoefs, i) ) goto finish;
    good = 1;
finish:
    Vec_IntFreeP(&deps); Acec2_RecordPolyStop(p); return good;
}

/**Function*************************************************************

  Synopsis    [Checks that a reference was narrowed without changing its terms.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordNarrowEqual( Vec_Int_t * full, Vec_Int_t * narrow, int Width, int Stride )
{
    int i, j = 0, k;
    for ( i = 0; i < Vec_IntSize(full); i += Stride )
        if ( Vec_IntEntry(full, i+Stride-1) < Width )
            for ( k = 0; k < Stride; k++ )
                if ( j == Vec_IntSize(narrow) || Vec_IntEntry(narrow, j++) != Vec_IntEntry(full, i+k) ) return 0;
    return j == Vec_IntSize(narrow);
}

/**Function*************************************************************

  Synopsis    [Checks the source gate supplying a product's low bit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordLowBit( Acec2_Man_t * m, int Lit, int a, int b )
{
    Gia_Obj_t * o; int x, y;
    if ( a == b ) return Lit == a;
    if ( a == (b ^ 1) || !a || !b ) return Lit == 0;
    if ( a == 1 || b == 1 ) return Lit == (a == 1 ? b : a);
    if ( Lit < 2 || (Lit & 1) || (Lit >> 1) >= Gia_ManObjNum(m->pGia) ) return 0;
    o = Gia_ManObj(m->pGia, Lit >> 1);
    if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) return 0;
    x = Gia_ObjFaninLit0p(m->pGia, o); y = Gia_ObjFaninLit1p(m->pGia, o);
    return (x == a && y == b) || (x == b && y == a);
}

/**Function*************************************************************

  Synopsis    [Checks extension of an exact shifted product by its observed low bit.]

  Description [Multiplying a modular identity by two increases its valid
  modulus by one bit. The low bit is checked directly in the source gates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordExtensionCheck( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Record_t * parent; Acec2_Product_t * product;
    Vec_Int_t * a, * b; int i, k, id;
    if ( r->Extend != 1 || r->Tree != -1 || r->Word != -1 || r->Counter != -1 || r->vParts || Vec_IntSize(r->vDependencies) != 1 ) return 0;
    id = Vec_IntEntry(r->vDependencies, 0); if ( id < 0 || id >= Vec_PtrSize(m->vRecords) ) return 0;
    parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, id);
    if ( parent->vOutputMasks || !parent->vFactors || Vec_PtrSize(parent->vFactors) != 1 || parent->Width+1 != r->Width ||
         parent->FactorWidth != parent->Width ) return 0;
    product = (Acec2_Product_t *)Vec_PtrEntry(parent->vFactors, 0);
    if ( product->Shift != -1 || product->fNeg || !Acec2_RecordLowBit(m, r->LowLit,
         Vec_IntEntry(product->vOperands[0], 0), Vec_IntEntry(product->vOperands[1], 0)) ) return 0;
    for ( k = 0; k < 2; k++ )
    {
        a = k ? parent->vOutputs : parent->vTerms; b = k ? r->vOutputs : r->vTerms;
        if ( Vec_IntSize(b) != Vec_IntSize(a)+2 || Vec_IntEntry(b, 0) != r->LowLit || Vec_IntEntry(b, 1) != 0 ) return 0;
        for ( i = 0; i < Vec_IntSize(a); i += 2 )
            if ( Vec_IntEntry(b, i+2) != Vec_IntEntry(a, i) || Vec_IntEntry(b, i+3) != Vec_IntEntry(a, i+1)+1 ) return 0;
    }
    if ( Vec_IntSize(r->vConstants) != Vec_IntSize(parent->vConstants) ) return 0;
    for ( i = 0; i < Vec_IntSize(r->vConstants); i++ )
        if ( Vec_IntEntry(r->vConstants, i) != Vec_IntEntry(parent->vConstants, i)+1 ) return 0;
    return r->Prefix == parent->Prefix+1;
}

/**Function*************************************************************

  Synopsis    [Imports an earlier polynomial at the certified word modulus.]

  Description [The parent identity is immutable and already checked. The
  source word proof uses this polynomial as its reference, so narrowing
  retains exact coefficients without expanding dependent boundary signals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordWordPoly( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Word_t * w = (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word);
    Acec2_Record_t * parent;
    Acec2_RecordPoly_t * p;
    Vec_Int_t * v; int i, nWords;
    if ( w->Record < 0 || w->Record >= Vec_PtrSize(m->vRecords) ) return NULL;
    parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, w->Record);
    if ( parent == r || parent->Width < r->Width ) return NULL;
    p = Acec2_RecordPolyStart(r->Width); nWords = (parent->Width+63)/64;
    Vec_WecForEachLevel(parent->vMonomials, v, i)
    {
        Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v);
        Acec2_RecordCoefficient(p, Vec_WrdEntryP(parent->vCoefficients, i*nWords), 1);
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Names the complete weighted source identity without hashing.]

  Description [Lengths, phases, repeated terms, constants and modulus are
  part of the immutable proof descriptor. No simulation signature is used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_RecordIdentity( Acec2_Record_t * r )
{
    Vec_Int_t * key = Vec_IntAlloc(32); int side;
    Vec_IntPushTwo(key, r->Width, Vec_IntSize(r->vOutputs));
    Vec_IntPushTwo(key, Vec_IntSize(r->vTerms), Vec_IntSize(r->vConstants));
    Vec_IntAppend(key, r->vOutputs); Vec_IntAppend(key, r->vTerms); Vec_IntAppend(key, r->vConstants);
    if ( r->vOutputMasks ) { Vec_IntPush(key, Vec_IntSize(r->vOutputMasks)); Vec_IntAppend(key, r->vOutputMasks); }
    if ( r->pProductReference )
    {
        Vec_IntPushThree(key, -1, r->pProductReference->Shift, r->pProductReference->fNeg);
        for ( side = 0; side < 2; side++ )
        {
            Vec_IntPushTwo(key, r->pProductReference->fSigned[side], Vec_IntSize(r->pProductReference->vOperands[side]));
            Vec_IntAppend(key, r->pProductReference->vOperands[side]);
        }
    }
    if ( Vec_IntSize(r->vDependencies) )
    { Vec_IntPushTwo(key, -2, Vec_IntSize(r->vDependencies)); Vec_IntAppend(key, r->vDependencies); }
    if ( r->fPolynomial ) Vec_IntPush(key, r->fPolynomial == 2 ? -4 : -3);
    return key;
}

/**Function*************************************************************

  Synopsis    [Checks a record against its completed source proof.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordSourceCheck( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Proof_t * proof; Vec_Int_t * key; int valid;
    if ( r->Proof < 1 || r->Proof > Vec_PtrSize(m->vProofs) || r->Word != -1 || r->Tree != -1 ||
         r->Counter != -1 || r->Compose || r->Extend || r->vParts ) return 0;
    proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, r->Proof-1);
    if ( proof->Kind != (r->fPolynomial == 2 ? 8 : r->fPolynomial ? 7 : r->vOutputMasks ? 5 : r->pProductReference ? 6 : 3) || proof->Domain != 1 || !proof->vIdentity || proof->vCut ||
         !Vec_IntEqual(r->vSupport, proof->vRoots) ) return 0;
    if ( r->fPolynomial && ((r->fPolynomial != 1 && r->fPolynomial != 2) || r->vOutputMasks || r->pProductReference ||
         (r->fPolynomial == 1 && r->Prefix != r->Width) || Vec_IntSize(r->vTerms) || Vec_IntSize(r->vConstants) ||
         !proof->vMonomials || !proof->vCoefficients) ) return 0;
    if ( r->pProductReference && (r->Prefix != r->Width ||
         Vec_IntSize(r->vTerms) || Vec_IntSize(r->vConstants)) ) return 0;
    if ( proof->Kind == 6 || proof->Kind == 8 )
    {
        int here = Vec_PtrFind(m->vRecords, r), parent;
        if ( here < 0 ) here = Vec_PtrSize(m->vRecords);
        if ( Vec_IntSize(r->vDependencies) != 1 ) return 0;
        parent = Vec_IntEntry(r->vDependencies, 0); if ( parent < 0 || parent >= here ) return 0;
    }
    else if ( Vec_IntSize(r->vDependencies) ) return 0;
    key = Acec2_RecordIdentity(r); valid = Vec_IntEqual(key, proof->vIdentity); Vec_IntFree(key); return valid;
}

/**Function*************************************************************

  Synopsis    [Reconstructs the polynomial from its completed source proof.]

  Description [The proof owns a separate immutable result of exact backward
  substitution. Exported coefficients, cut membership and output phases are
  checked against this reference, rather than trusting the mutable record.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordSourcePolynomial( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Proof_t * proof; Acec2_RecordPoly_t * p; Vec_Int_t * v;
    int i, j, id, previous;
    if ( !Acec2_RecordSourceCheck(m, r) ) return NULL;
    proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, r->Proof-1);
    if ( (proof->Kind != 7 && proof->Kind != 8) || Vec_WrdSize(proof->vCoefficients) !=
         (ABC_INT64_T)Vec_WecSize(proof->vMonomials)*((r->Width+63)/64) ) return NULL;
    p = Acec2_RecordPolyStart(r->Width);
    Vec_WecForEachLevel(proof->vMonomials, v, i)
    {
        previous = 0;
        Vec_IntForEachEntry(v, id, j)
        {
            if ( id <= previous || id >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, id)) ||
                 (proof->Kind == 7 && !Gia_ObjIsCi(Gia_ManObj(m->pGia, id))) || Vec_IntFind(proof->vRoots, id) < 0 )
            { Acec2_RecordPolyStop(p); return NULL; }
            previous = id;
        }
        Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v);
        Acec2_RecordCoefficient(p, Vec_WrdEntryP(proof->vCoefficients, i*p->nWords), 1);
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Checks the record and re-derives its entire polynomial.]

  Description [Word certificates have an exact reference proof, over a free
  cut or on the source as specified by their word kind. Region certificates
  are checked by exact cell composition. The
  polynomial is then independently reconstructed from those certified terms.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordCheck( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_RecordPoly_t * p; Acec2_Word_t * w; Acec2_Counter_t * c; Acec2_Record_t * parent;
    Vec_Int_t * v, * cut = NULL; Vec_Bit_t * vSeen = NULL; int i, j, id, alive, count = 0, good = 0;
    if ( r->Domain != 1 || r->Word < -1 || r->Proof < 0 || r->Width < 1 || r->Width > m->Pars.nMaxWidth || r->Prefix < 0 || r->Prefix > r->Width || (r->Counter < 0 && !r->vParts && !r->Extend && !r->Compose && !r->Proof && r->Word < 0 && (r->Tree < 0 || r->Tree >= Vec_WecSize(m->vTrees))) ) return 0;
    if ( (Vec_IntSize(r->vOutputs) & 1) || Vec_IntSize(r->vBitStatus) != Vec_IntSize(r->vOutputs)/2 ) return 0;
    if ( r->pProductReference && !r->Proof ) return 0;
    if ( r->fPolynomial && !r->Proof ) return 0;
    if ( r->vOutputMasks && (!r->Proof || Vec_IntSize(r->vOutputMasks) != Vec_IntSize(r->vOutputs)/2) ) return 0;
    {
        Vec_Int_t * vCounts = Vec_IntStart(r->Prefix);
        for ( i = 0; i < Vec_IntSize(r->vOutputs); i += 2 )
        {
            j = Vec_IntEntry(r->vOutputs, i+1);
            if ( j < 0 || j >= r->Width ) { Vec_IntFree(vCounts); return 0; }
            if ( Vec_IntEntry(r->vBitStatus, i/2) != (j < r->Prefix ? (r->Prefix == r->Width ? 1 : 2) : 0) )
            { Vec_IntFree(vCounts); return 0; }
            if ( j < r->Prefix && Vec_IntAddToEntry(vCounts, j, 1) > 1 ) { Vec_IntFree(vCounts); return 0; }
        }
        Vec_IntFree(vCounts);
    }
    if ( r->Proof )
    {
        if ( !Acec2_RecordSourceCheck(m, r) ) return 0;
    }
    else if ( r->Compose )
    {
        if ( !Acec2_RecordCompositionCheck(m, r) ) return 0;
    }
    else if ( r->Extend )
    {
        if ( !Acec2_RecordExtensionCheck(m, r) ) return 0;
    }
    else if ( r->vParts )
    {
        if ( r->Word != -1 || r->Counter != -1 || r->Tree != -1 || !Acec2_RecordPartsCheck(m, r) ) return 0;
    }
    else if ( r->Counter >= 0 )
    {
        if ( r->Counter >= Vec_PtrSize(m->vCounters) || r->Word != -1 || r->Tree != -1 ) return 0;
        c = (Acec2_Counter_t *)Vec_PtrEntry(m->vCounters, r->Counter);
        if ( c->Width != r->Width || !Vec_IntEqual(c->vInputs, r->vTerms) ||
             !Vec_IntEqual(c->vOutputs, r->vOutputs) || Vec_IntSize(r->vConstants) || !Acec2_CounterCheck(m, c, NULL) ) return 0;
    }
    else if ( r->Word < 0 ) { if ( !Acec2_RecordRegionCheck(m, r) ) return 0; }
    else
    {
        if ( r->Word >= Vec_PtrSize(m->vWords) ) return 0;
        w = (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word);
        if ( w->Tree != r->Tree || w->Width != r->Width || Vec_IntSize(r->vOutputs) != 2*w->Width ) return 0;
        if ( (w->fPolynomial & ~1) || (w->fPolynomial && (w->pProduct || w->fIndependent)) ) return 0;
        if ( (w->fSource & ~1) || (w->fSource && (!w->fIndependent || w->pProduct || w->fPolynomial)) ) return 0;
        if ( w->vSumProducts && (!w->fIndependent || w->pProduct || w->fPolynomial) ) return 0;
        if ( w->pProduct )
        {
            if ( r->Tree != -1 || r->Prefix != r->Width || Vec_IntSize(r->vDependencies) ||
                 Vec_IntSize(r->vTerms) || Vec_IntSize(r->vConstants) ) return 0;
        }
        else if ( w->fIndependent )
        {
            if ( r->Tree != -1 || w->Record != -1 || r->Prefix != r->Width ||
                 !Vec_IntEqual(w->vTerms, r->vTerms) || !Vec_IntEqual(w->vConstants, r->vConstants) ) return 0;
            if ( w->vSumProducts )
            {
                Vec_Int_t * deps = Vec_IntAlloc(8);
                int here = Vec_PtrFind(m->vRecords, r), valid = 1;
                if ( here < 0 ) here = Vec_PtrSize(m->vRecords);
                for ( i = 0; i < Vec_IntSize(w->vSumProducts); i += 3 )
                {
                    id = Vec_IntEntry(w->vSumProducts, i);
                    if ( id < 0 || id >= here ) valid = 0;
                    Vec_IntPushUnique(deps, id);
                }
                valid &= Vec_IntEqual(deps, r->vDependencies); Vec_IntFree(deps);
                if ( !valid ) return 0;
            }
            else if ( Vec_IntSize(r->vDependencies) ) return 0;
        }
        else if ( r->Tree >= 0 )
        {
            if ( !Vec_IntEqual(w->vTerms, r->vTerms) || !Vec_IntEqual(w->vConstants, r->vConstants) ) return 0;
        }
        else
        {
            if ( w->Record < 0 || w->Record >= Vec_PtrSize(m->vRecords) || Vec_IntSize(r->vDependencies) != 1 ||
                 Vec_IntEntry(r->vDependencies, 0) != w->Record ) return 0;
            parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, w->Record);
            if ( parent->vOutputMasks || parent->Width < r->Width ||
                 !Acec2_RecordNarrowEqual(parent->vTerms, r->vTerms, r->Width, 2) ||
                 !Acec2_RecordNarrowEqual(parent->vConstants, r->vConstants, r->Width, 1) ) return 0;
            if ( w->vRollback )
            {
                Acec2_Record_t boundary;
                memset(&boundary, 0, sizeof(boundary)); boundary.Width = r->Width;
                boundary.vOutputs = parent->vOutputs; boundary.vTerms = w->vTerms;
                boundary.vConstants = w->vConstants; boundary.vParts = w->vRollback;
                if ( w->fPolynomial || !Acec2_RecordPartsCheck(m, &boundary) ) return 0;
            }
            else if ( w->fPolynomial )
            { if ( Vec_IntSize(w->vTerms) || Vec_IntSize(w->vConstants) ) return 0; }
            else if ( !Vec_IntEqual(w->vTerms, r->vTerms) || !Vec_IntEqual(w->vConstants, r->vConstants) )
                if ( Vec_IntSize(w->vConstants) || !Acec2_RecordNarrowEqual(parent->vOutputs, w->vTerms, r->Width, 2) ) return 0;
        }
        for ( i = 0; i < w->Width; i++ )
            if ( Vec_IntEntry(r->vOutputs, 2*i) != Vec_IntEntry(w->vBits, i) || Vec_IntEntry(r->vOutputs, 2*i+1) != i ) return 0;
    }
    if ( r->Compose )
    {
        Vec_Int_t * regions = Vec_IntAlloc(16);
        p = Acec2_RecordComposition(m, (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, r->Compose-1), regions);
        good = p && Vec_IntEqual(regions, r->vComposition); Vec_IntFree(regions);
        if ( !good ) { if ( p ) Acec2_RecordPolyStop(p); return 0; }
        good = 0;
    }
    else if ( r->fPolynomial ) p = Acec2_RecordSourcePolynomial(m, r);
    else if ( r->pProductReference ) p = Acec2_RecordSourceProduct(m, r);
    else if ( r->Word >= 0 && ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->pProduct )
        p = Acec2_RecordProductPoly(m, (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word));
    else if ( r->Word >= 0 && ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->vSumProducts )
        p = Acec2_RecordSumPoly(m, (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word));
    else if ( r->Word >= 0 && ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->fPolynomial )
        p = Acec2_RecordWordPoly(m, r);
    else
    {
        p = Acec2_RecordPolyStart(r->Width);
        Acec2_RecordTerms(p, m->pGia, r->vTerms, r->vConstants, 1, 1);
    }
    if ( !p ) return 0;
    if ( r->fPolynomial ) cut = Vec_IntAlloc(64);
    for ( i = 0; i < Hsh_VecSize(p->h); i++ )
    {
        alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        count += alive != 0;
        if ( alive && cut )
        {
            v = Hsh_VecReadEntry(p->h, i);
            Vec_IntForEachEntry(v, id, j) Vec_IntPush(cut, 2*id);
        }
    }
    if ( cut ) { Vec_IntUniqify(cut); if ( !Vec_IntEqual(cut, r->vCut) ) goto finish; }
    if ( count != Vec_WecSize(r->vMonomials) || Vec_WrdSize(r->vCoefficients) != count*p->nWords ) goto finish;
    vSeen = Vec_BitStart(Abc_MaxInt(1, Hsh_VecSize(p->h)));
    Vec_WecForEachLevel(r->vMonomials, v, i)
    {
        Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v);
        id = Hsh_VecManAdd(p->h, p->vMono);
        if ( id >= Vec_WrdSize(p->vCoefs)/p->nWords || Vec_BitEntry(vSeen, id) ) goto finish;
        Acec2_BitWrite(vSeen, id, 1);
        for ( j = 0; j < p->nWords; j++ )
            if ( Vec_WrdEntry(p->vCoefs, id*p->nWords+j) != Vec_WrdEntry(r->vCoefficients, i*p->nWords+j) ) goto finish;
    }
    good = !r->vFactors || Acec2_RecordFactorCheck(r);
finish:
    Vec_IntFreeP(&cut); Vec_BitFreeP(&vSeen); Acec2_RecordPolyStop(p); return good;
}

/**Function*************************************************************

  Synopsis    [Releases a persistent component certificate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RecordFree( Acec2_Record_t * r )
{
    Acec2_Product_t * product; int i;
    if ( !r ) return;
    Vec_IntFree(r->vOutputs); Vec_IntFree(r->vTerms); Vec_IntFree(r->vConstants); Vec_IntFree(r->vCut);
    Vec_IntFree(r->vCovered); Vec_IntFree(r->vSupport); Vec_IntFree(r->vDependencies); Vec_IntFree(r->vBitStatus);
    Vec_IntFreeP(&r->vParts);
    Vec_IntFreeP(&r->vOutputMasks);
    Vec_IntFreeP(&r->vComposition);
    if ( r->pProductReference )
    {
        Vec_IntFree(r->pProductReference->vOperands[0]); Vec_IntFree(r->pProductReference->vOperands[1]);
        ABC_FREE(r->pProductReference);
    }
    if ( r->vFactors )
    {
        Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, i)
        { Vec_IntFree(product->vOperands[0]); Vec_IntFree(product->vOperands[1]); ABC_FREE(product); }
        Vec_PtrFree(r->vFactors);
    }
    Vec_WecFreeP(&r->vResidual); Vec_WrdFreeP(&r->vResidualCoefs);
    Vec_WecFree(r->vMonomials); Vec_WrdFree(r->vCoefficients); ABC_FREE(r);
}

/**Function*************************************************************

  Synopsis    [Derives and checks the common polynomial representation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordPopulate( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_RecordPoly_t * p; Vec_Int_t * v; int i, j, id, alive;
    if ( r->Compose )
    {
        p = Acec2_RecordComposition(m, (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, r->Compose-1), r->vComposition);
        Vec_IntClear(r->vDependencies); Vec_IntPush(r->vDependencies, r->Compose-1);
        for ( i = 2; i < Vec_IntSize(r->vComposition); i += 3 )
            Vec_IntPushUnique(r->vDependencies, Vec_IntEntry(m->vTreeRecord, Vec_IntEntry(r->vComposition, i)));
    }
    else if ( r->fPolynomial ) p = Acec2_RecordSourcePolynomial(m, r);
    else if ( r->pProductReference ) p = Acec2_RecordSourceProduct(m, r);
    else if ( r->Word >= 0 && ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->pProduct )
        p = Acec2_RecordProductPoly(m, (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word));
    else if ( r->Word >= 0 && ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->vSumProducts )
        p = Acec2_RecordSumPoly(m, (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word));
    else if ( r->Word >= 0 && ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->fPolynomial )
        p = Acec2_RecordWordPoly(m, r);
    else
    {
        p = Acec2_RecordPolyStart(r->Width);
        Acec2_RecordTerms(p, m->pGia, r->vTerms, r->vConstants, 1, 1);
    }
    if ( !p ) return 0;
    for ( i = 0; i < Hsh_VecSize(p->h); i++ )
    {
        alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(p->h, i); Vec_IntAppend(Vec_WecPushLevel(r->vMonomials), v);
        Vec_IntForEachEntry(v, id, j) Vec_IntPush(r->vCut, 2*id);
        for ( j = 0; j < p->nWords; j++ ) Vec_WrdPush(r->vCoefficients, Vec_WrdEntry(p->vCoefs, i*p->nWords+j));
    }
    Vec_IntUniqify(r->vCut); Acec2_RecordPolyStop(p);
    Vec_IntClear(r->vBitStatus);
    for ( i = 1; i < Vec_IntSize(r->vOutputs); i += 2 )
        Vec_IntPush(r->vBitStatus, Vec_IntEntry(r->vOutputs, i) < r->Prefix ? (r->Prefix == r->Width ? 1 : 2) : 0);
    return Acec2_RecordCheck(m, r);
}

/**Function*************************************************************

  Synopsis    [Allocates an empty checked-component proposal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Record_t * Acec2_RecordAlloc( int Width )
{
    Acec2_Record_t * r = ABC_CALLOC(Acec2_Record_t, 1);
    r->Tree = r->Word = r->Counter = r->Expression = -1; r->Domain = 1; r->Width = Width;
    r->vOutputs = Vec_IntAlloc(32); r->vTerms = Vec_IntAlloc(64); r->vConstants = Vec_IntAlloc(16);
    r->vCut = Vec_IntAlloc(64); r->vCovered = Vec_IntAlloc(128); r->vSupport = Vec_IntAlloc(64);
    r->vDependencies = Vec_IntAlloc(16); r->vBitStatus = Vec_IntAlloc(16);
    r->vMonomials = Vec_WecAlloc(64); r->vCoefficients = Vec_WrdAlloc(64);
    return r;
}

/**Function*************************************************************

  Synopsis    [Finds the binary prefix of a weighted output boundary.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordPrefix( Acec2_Record_t * r )
{
    Vec_Int_t * counts = Vec_IntStart(r->Width); int i, prefix;
    for ( i = 1; i < Vec_IntSize(r->vOutputs); i += 2 ) Vec_IntAddToEntry(counts, Vec_IntEntry(r->vOutputs, i), 1);
    for ( prefix = 0; prefix < r->Width && Vec_IntEntry(counts, prefix) <= 1; prefix++ ) {}
    Vec_IntFree(counts); return prefix;
}

/**Function*************************************************************

  Synopsis    [Cancels identical occurrences on two ranked boundaries.]

  Description [Packed entries contain a rank and a source literal. Phase
  and multiplicity remain explicit; only identical occurrences cancel.]

  SideEffects [Sorts the supplied boundaries and appends the remainder.]

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordCancel( Acec2_Record_t * r, Vec_Wrd_t ** boundary )
{
    int i = 0, j = 0, k, side; word key;
    for ( side = 0; side < 2; side++ ) if ( Vec_WrdSize(boundary[side]) > 1 ) Vec_WrdSort(boundary[side], 0);
    while ( i < Vec_WrdSize(boundary[0]) || j < Vec_WrdSize(boundary[1]) )
    {
        if ( i < Vec_WrdSize(boundary[0]) && j < Vec_WrdSize(boundary[1]) && Vec_WrdEntry(boundary[0], i) == Vec_WrdEntry(boundary[1], j) )
        { i++; j++; continue; }
        side = i == Vec_WrdSize(boundary[0]) || (j < Vec_WrdSize(boundary[1]) && Vec_WrdEntry(boundary[1], j) < Vec_WrdEntry(boundary[0], i));
        k = side ? j++ : i++; key = Vec_WrdEntry(boundary[side], k);
        Vec_IntPushTwo(side ? r->vTerms : r->vOutputs, (int)(unsigned)key, (int)(key >> 32));
    }
}

/**Function*************************************************************

  Synopsis    [Rederives a wider identity from complete integer cells.]

  Description [A modular parent record cannot justify more bits. Instead,
  this operation rechecks each original integer cell/counter and composes
  a new identity at the requested modulus. Modular record dependencies are
  ineligible. Constants and boundaries are rebuilt, not zero-extended.]

  SideEffects [Appends a separately checked record; leaves its parent intact.]

  SeeAlso     []

***********************************************************************/
int Acec2_RecordLiftParts( Acec2_Man_t * m, int Parent, int Width )
{
    Acec2_Record_t * parent, * r, * old; Acec2_Part_t part;
    Vec_Wrd_t * boundary[2]; Vec_Int_t * bias;
    int i, j, k, side, rank, phase, value, bit, * entry, result = -1;
    if ( !m || Parent < 0 || Parent >= Vec_PtrSize(m->vRecords) || Width < 1 || Acec2_Stopped(m) ) return -1;
    parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Parent);
    if ( !parent->vParts || !Vec_IntSize(parent->vParts) || parent->Word >= 0 || parent->Proof ||
         parent->Compose || parent->Extend || Vec_IntSize(parent->vDependencies) ) return -1;
    if ( Width > m->Pars.nMaxWidth || Width > 512 || Vec_IntSize(parent->vParts) > 16384 )
    { m->nRecordLimits++; return -1; }
    if ( !Acec2_RecordCheck(m, parent) ) return -1;
    if ( Width <= parent->Width ) return Parent;
    for ( i = 0; i < Vec_IntSize(parent->vParts); i += 4 )
        if ( Vec_IntEntry(parent->vParts, i) > 2 ) return -1;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, old, i)
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) return -1;
        if ( old->vParts && old->Width == Width && Vec_IntEqual(old->vParts, parent->vParts) )
            return Acec2_RecordCheck(m, old) ? i : -1;
    }
    r = Acec2_RecordAlloc(Width); r->vParts = Vec_IntDup(parent->vParts); r->Discovery = parent->Discovery;
    boundary[0] = Vec_WrdAlloc(32); boundary[1] = Vec_WrdAlloc(32); bias = Vec_IntStart(Width);
    for ( i = 0; i < Vec_IntSize(r->vParts); i += 4 )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) goto finish;
        if ( !Acec2_GetPart(m, Vec_IntEntry(r->vParts, i), Vec_IntEntry(r->vParts, i+1), &part) ) goto finish;
        rank = Vec_IntEntry(r->vParts, i+2); phase = Vec_IntEntry(r->vParts, i+3);
        Vec_IntAppend(r->vCovered, part.vGates);
        for ( side = 0; side < 2; side++ )
            for ( j = 0; j < (side ? part.nIns : part.nOuts); j++ )
            {
                entry = (side ? part.In : part.Out)+2*j; k = rank+entry[1];
                Vec_IntPush(r->vSupport, entry[0] >> 1); if ( k >= Width ) continue;
                Vec_WrdPush(boundary[side], ((word)(unsigned)k << 32) | (unsigned)(entry[0] ^ phase));
                if ( phase ) Vec_IntAddToEntry(bias, k, side ? -1 : 1);
            }
    }
    Acec2_RecordCancel(r, boundary);
    for ( i = 0; i < Width; i++ )
    {
        value = Vec_IntEntry(bias, i); bit = (unsigned)value & 1;
        if ( bit ) Vec_IntPush(r->vConstants, i);
        if ( i+1 < Width ) Vec_IntAddToEntry(bias, i+1, (value-bit)/2);
    }
    Vec_IntUniqify(r->vCovered); Vec_IntUniqify(r->vSupport); r->Prefix = Acec2_RecordPrefix(r);
    if ( !Acec2_RecordPopulate(m, r) || Acec2_Stopped(m) ) goto finish;
    result = Vec_PtrSize(m->vRecords); Vec_PtrPush(m->vRecords, r); r = NULL;
    if ( m->Pars.fVerbose ) Abc_Print(1, "Checked cell partition: record = %d, modulus = %d -> %d, derived record = %d.\n",
        Parent, parent->Width, Width, result);
finish:
    Acec2_RecordFree(r); Vec_WrdFree(boundary[0]); Vec_WrdFree(boundary[1]); Vec_IntFree(bias); return result;
}

/**Function*************************************************************

  Synopsis    [Stores a weighted identity only after a complete source proof.]

  Description [The caller retains every input vector. Returns an existing
  or newly checked record ID, or minus one without a certificate. Proof
  support is retained separately from any claimed implementation footprint.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordWeighted( Acec2_Man_t * m, Vec_Int_t * vOutputs, Vec_Int_t * vTerms, Vec_Int_t * vConstants, int Width )
{
    Acec2_Record_t * r, * old; Acec2_Proof_t * proof; Vec_Int_t * key; int i, id;
    if ( !m || !vOutputs || !vTerms || !vConstants || Width < 1 || Acec2_Stopped(m) ) return -1;
    if ( Width > 512 || Width > m->Pars.nMaxWidth ) { m->nWeightedLimits++; return -1; }
    r = Acec2_RecordAlloc(Width);
    Vec_IntAppend(r->vOutputs, vOutputs); Vec_IntAppend(r->vTerms, vTerms); Vec_IntAppend(r->vConstants, vConstants);
    key = Acec2_RecordIdentity(r);
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, old, i)
        if ( old->Proof )
        {
            proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, old->Proof-1);
            if ( Vec_IntEqual(key, proof->vIdentity) ) { Vec_IntFree(key); Acec2_RecordFree(r); return i; }
        }
    if ( Acec2_ProveWeighted(m, vOutputs, vTerms, vConstants, Width) != 1 )
    { Vec_IntFree(key); Acec2_RecordFree(r); return -1; }
    for ( i = 0; i < Vec_IntSize(vOutputs); i += 2 ) Vec_IntPush(r->vSupport, Vec_IntEntry(vOutputs, i) >> 1);
    for ( i = 0; i < Vec_IntSize(vTerms); i += 2 ) Vec_IntPush(r->vSupport, Vec_IntEntry(vTerms, i) >> 1);
    Vec_IntUniqify(r->vSupport); r->Prefix = Acec2_RecordPrefix(r);
    proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 3; proof->Domain = 1;
    proof->fExhaustive = m->fWeightedTruth;
    proof->vIdentity = key; proof->vRoots = Vec_IntDup(r->vSupport);
    Vec_PtrPush(m->vProofs, proof); r->Proof = Vec_PtrSize(m->vProofs);
    if ( !Acec2_RecordPopulate(m, r) || Acec2_Stopped(m) )
    {
        Vec_PtrPop(m->vProofs); Vec_IntFree(proof->vRoots); Vec_IntFree(proof->vIdentity); ABC_FREE(proof);
        Acec2_RecordFree(r); return -1;
    }
    id = Vec_PtrSize(m->vRecords); Vec_PtrPush(m->vRecords, r); return id;
}

/**Function*************************************************************

  Synopsis    [Collects implementation gates below a certified output boundary.]

  Description [Product operand literals stop the traversal. A partial word
  owns only its retained output cones, independently of the parent region
  used in its proof. Generic output polynomials stop at source inputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordProductGates( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Vec_Bit_t * seen = Vec_BitStart(Gia_ManObjNum(m->pGia)); Vec_Int_t * stack = Vec_IntAlloc(100);
    Gia_Obj_t * o; Vec_Int_t * mono; int side, i, j, lit, id, steps = 0, valid = 1;
    if ( r->pProductReference )
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(r->pProductReference->vOperands[side], lit, i) Acec2_BitWrite(seen, lit >> 1, 1);
    if ( r->fPolynomial == 2 && r->Proof > 0 )
    {
        Acec2_Proof_t * proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, r->Proof-1);
        Vec_WecForEachLevel(proof->vMonomials, mono, i)
            Vec_IntForEachEntry(mono, id, j) Acec2_BitWrite(seen, id, 1);
    }
    for ( i = 0; i < Vec_IntSize(r->vOutputs); i += 2 ) Vec_IntPush(stack, Vec_IntEntry(r->vOutputs, i) >> 1);
    while ( Vec_IntSize(stack) )
    {
        if ( (++steps & 255) == 0 && Acec2_Stopped(m) ) { valid = 0; break; }
        id = Vec_IntPop(stack); if ( !id || Vec_BitEntry(seen, id) ) continue;
        Acec2_BitWrite(seen, id, 1); o = Gia_ManObj(m->pGia, id); if ( !Gia_ObjIsAnd(o) ) continue;
        Vec_IntPush(r->vCovered, id); Vec_IntPushTwo(stack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
        if ( Gia_ObjIsMux(m->pGia, o) ) Vec_IntPush(stack, Gia_ObjFaninId2(m->pGia, id));
    }
    Vec_IntSort(r->vCovered, 0); Vec_IntFree(stack); Vec_BitFree(seen); return valid && !Acec2_Stopped(m);
}

/**Function*************************************************************

  Synopsis    [Retains a completed exact output polynomial in the common form.]

  Description [Only the exact extraction engine calls this certificate
  importer, after all substitutions have completed. The supplied variables
  are CI ordinals starting at one; translate them to physical source IDs.
  Retain the completed polynomial independently of its exported record.
  Output order, modulus and support are sealed in the source proof. This
  generic word makes no claim that the surrounding logic is an arithmetic
  component. Inputs cancelled by substitution remain in proof support.]

  SideEffects [Borrows its arguments; stores a new source certificate once.]

  SeeAlso     []

***********************************************************************/
int Acec2_RecordOutputPolynomial( Acec2_Man_t * m, int Width, Hsh_VecMan_t * hMonomials, Vec_Wrd_t * vCoefficients )
{
    Acec2_Record_t * r = NULL, * old;
    Acec2_Proof_t * proof = NULL;
    Vec_Int_t * v, * mono; Gia_Obj_t * o;
    int i, j, id, alive, previous, nWords = (Width+63)/64, pushed = 0, result = 0;
    ABC_INT64_T storage = 0;
    if ( Width < 1 || Width > m->Pars.nMaxWidth || Width > Gia_ManCoNum(m->pGia) || Acec2_Stopped(m) ||
         Vec_WrdSize(vCoefficients) != (ABC_INT64_T)Hsh_VecSize(hMonomials)*nWords ) return 0;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, old, i)
        if ( old->fPolynomial == 1 && old->Width == Width ) return 0;
    r = Acec2_RecordAlloc(Width); r->Prefix = Width; r->fPolynomial = 1;
    proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 7; proof->Domain = 1;
    proof->vMonomials = Vec_WecAlloc(64); proof->vCoefficients = Vec_WrdAlloc(64);
    for ( i = 0; i < Hsh_VecSize(hMonomials); i++ )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) goto finish;
        alive = 0;
        for ( j = 0; j < nWords; j++ ) alive |= Vec_WrdEntry(vCoefficients, i*nWords+j) != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(hMonomials, i); storage += nWords+Vec_IntSize(v);
        if ( storage > 2000000 ) { m->nRecordLimits++; goto finish; }
        if ( (Width & 63) && (Vec_WrdEntry(vCoefficients, (i+1)*nWords-1) >> (Width & 63)) ) goto finish;
        mono = Vec_WecPushLevel(proof->vMonomials); previous = 0;
        Vec_IntForEachEntry(v, id, j)
        {
            if ( id <= previous || id > Gia_ManCiNum(m->pGia) ) goto finish;
            Vec_IntPush(mono, Gia_ObjId(m->pGia, Gia_ManCi(m->pGia, id-1))); previous = id;
        }
        for ( j = 0; j < nWords; j++ ) Vec_WrdPush(proof->vCoefficients, Vec_WrdEntry(vCoefficients, i*nWords+j));
    }
    for ( i = 0; i < Width; i++ )
    {
        id = Gia_ObjFaninLit0p(m->pGia, Gia_ManCo(m->pGia, i));
        Vec_IntPushTwo(r->vOutputs, id, i); Vec_IntPush(r->vSupport, id >> 1);
    }
    Gia_ManForEachCi(m->pGia, o, i) Vec_IntPush(r->vSupport, Gia_ObjId(m->pGia, o));
    Vec_IntUniqify(r->vSupport);
    proof->vRoots = Vec_IntDup(r->vSupport); proof->vIdentity = Acec2_RecordIdentity(r);
    Vec_PtrPush(m->vProofs, proof); pushed = 1; r->Proof = Vec_PtrSize(m->vProofs);
    if ( !Acec2_RecordProductGates(m, r) || !Acec2_RecordPopulate(m, r) || Acec2_Stopped(m) ) goto finish;
    Vec_PtrPush(m->vRecords, r); return 1;
finish:
    if ( pushed ) Vec_PtrPop(m->vProofs);
    Vec_IntFreeP(&proof->vRoots); Vec_IntFreeP(&proof->vIdentity);
    Vec_WecFree(proof->vMonomials); Vec_WrdFree(proof->vCoefficients); ABC_FREE(proof);
    Acec2_RecordFree(r); return result;
}

/**Function*************************************************************

  Synopsis    [Finds an existing exact product word over these source literals.]

  Description [Operand phases, signedness, every output bit and the exact
  modulus must agree. The independent record checker validates a match.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordGridFind( Acec2_Man_t * m, Acec2_Product_t * product, Vec_Int_t * outputs, int Width )
{
    Acec2_Record_t * r; Acec2_Product_t * p; int i, j, side;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        if ( (i & 63) == 0 && Acec2_Stopped(m) ) return -1;
        p = r->pProductReference;
        if ( !p || r->vOutputMasks || r->Width != Width || r->Prefix != Width || p->Shift || p->fNeg ||
             Vec_IntSize(r->vOutputs) != 2*Width ) continue;
        for ( side = 0; side < 2; side++ )
            if ( p->fSigned[side] != product->fSigned[side] || !Vec_IntEqual(p->vOperands[side], product->vOperands[side]) ) break;
        if ( side < 2 ) continue;
        for ( j = 0; j < Width; j++ )
            if ( Vec_IntEntry(r->vOutputs, 2*j) != Vec_IntEntry(outputs, j) || Vec_IntEntry(r->vOutputs, 2*j+1) != j ) break;
        if ( j == Width && Acec2_RecordCheck(m, r) ) return i;
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Stores one certified grid product or reuses its existing record.]

  Description [Different checked region partitions can prove the same output
  word over the same operands. One completed source certificate suffices;
  retain its original support and dependencies instead of adding duplicates.
  An operand grid is only a proposal. Every remaining weighted term must
  be checked, including products without source nodes. Complete integer
  cells may supply a separately rederived wider parent. Otherwise the
  parent modulus bounds the prefix. Covered gates and proof support are
  stored separately.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordGridProduct( Acec2_Man_t * m, int Record, Acec2_Product_t * product, Vec_Int_t * vOutputs )
{
    Acec2_Record_t * r, * parent; Acec2_Proof_t * proof; int i, side, lit, id, prefix;
    if ( !m || !product || !vOutputs || Record < 0 || Record >= Vec_PtrSize(m->vRecords) ) return -1;
    if ( product->Shift <= 0 && product->Shift >= -64 && Vec_IntSize(vOutputs) <= 64 )
    {
        id = Acec2_RecordLiftParts(m, Record, Vec_IntSize(vOutputs)+product->Shift);
        if ( id >= 0 ) Record = id;
    }
    Acec2_ProveProductGridPrefix(m, Record, product, vOutputs, &prefix);
    if ( prefix < 4 || Acec2_Stopped(m) ) return -1;
    id = Acec2_RecordGridFind(m, product, vOutputs, prefix);
    if ( Acec2_Stopped(m) ) return -1;
    if ( id >= 0 ) return id;
    r = Acec2_RecordAlloc(prefix); r->Prefix = r->Width;
    parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Record);
    r->pProductReference = ABC_ALLOC(Acec2_Product_t, 1); *r->pProductReference = *product;
    r->pProductReference->Shift = 0; r->pProductReference->fNeg = 0;
    for ( side = 0; side < 2; side++ )
    {
        r->pProductReference->vOperands[side] = Vec_IntDup(product->vOperands[side]);
        Vec_IntForEachEntry(product->vOperands[side], lit, i) Vec_IntPush(r->vSupport, lit >> 1);
    }
    for ( i = 0; i < prefix; i++ )
    { lit = Vec_IntEntry(vOutputs, i); Vec_IntPushTwo(r->vOutputs, lit, i); Vec_IntPush(r->vSupport, lit >> 1); }
    Vec_IntAppend(r->vSupport, parent->vSupport);
    Vec_IntUniqify(r->vSupport);
    if ( !Acec2_RecordProductGates(m, r) ) { Acec2_RecordFree(r); return -1; }
    proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 6; proof->Domain = 1;
    Vec_IntPush(r->vDependencies, Record);
    proof->vIdentity = Acec2_RecordIdentity(r); proof->vRoots = Vec_IntDup(r->vSupport);
    Vec_PtrPush(m->vProofs, proof); r->Proof = Vec_PtrSize(m->vProofs);
    r->Discovery = parent->Tree >= 0 ? parent->Tree+1 : parent->Discovery;
    if ( !Acec2_RecordPopulate(m, r) || Acec2_Stopped(m) )
    {
        Vec_PtrPop(m->vProofs); Vec_IntFree(proof->vIdentity); Vec_IntFree(proof->vRoots); ABC_FREE(proof);
        Acec2_RecordFree(r); return -1;
    }
    Acec2_RecordFactorPopulate(m, r, NULL);
    id = Vec_PtrSize(m->vRecords); Vec_PtrPush(m->vRecords, r); return id;
}

/**Function*************************************************************

  Synopsis    [Stores a checked sum of operand grids on a weighted boundary.]

  Description [Each grid is only a discovery proposal. The source checker
  proves all remaining gaps against the parent before the expected polynomial
  is retained. Internal operand literals remain source-constrained variables.
  The proof owns immutable coefficients, independent of the exported record;
  output multiplicity and a partially binary boundary are preserved.]

  SideEffects [Borrows the grids and boundary; appends a certificate on success.]

  SeeAlso     []

***********************************************************************/
int Acec2_RecordGridExpression( Acec2_Man_t * m, int Record, Vec_Ptr_t * products,
                                Vec_Int_t * outputs, int Width, int Offset )
{
    Acec2_Record_t * r = NULL, * parent, * old; Acec2_RecordPoly_t * p = NULL;
    Acec2_Product_t * product, copy; Acec2_Proof_t * proof = NULL;
    Vec_Int_t * cut = NULL, * mono; int i, j, side, lit, prefix, alive, pushed = 0, result = -1;
    if ( m && Width > Offset && Width <= 64 && Offset >= 0 && Record >= 0 && Record < Vec_PtrSize(m->vRecords) )
    { i = Acec2_RecordLiftParts(m, Record, Width-Offset); if ( i >= 0 ) Record = i; }
    Acec2_ProveGridExpression(m, Record, products, outputs, Width, Offset, &prefix);
    if ( prefix < 2 || Acec2_Stopped(m) ) return -1;
    parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Record);
    r = Acec2_RecordAlloc(prefix); r->fPolynomial = 2;
    r->Discovery = parent->Tree >= 0 ? parent->Tree+1 : parent->Discovery;
    p = Acec2_RecordPolyStart(prefix); cut = Vec_IntAlloc(64);
    Vec_PtrForEachEntry(Acec2_Product_t *, products, product, i)
        for ( side = 0; side < 2; side++ ) Vec_IntForEachEntry(product->vOperands[side], lit, j)
            if ( lit >= 2 ) { Vec_IntPush(cut, lit & ~1); Vec_IntPush(r->vSupport, lit >> 1); }
    Vec_IntUniqify(cut);
    Vec_PtrForEachEntry(Acec2_Product_t *, products, product, i)
    {
        copy = *product; copy.Shift += Offset; copy.fNeg ^= 1;
        if ( copy.Shift >= prefix ) continue;
        if ( !Acec2_RecordSubtractProduct(p, &copy, cut) ) goto finish;
    }
    for ( i = 0; i < Vec_IntSize(outputs); i += 2 )
        if ( Vec_IntEntry(outputs, i+1) < prefix )
        { Vec_IntPushTwo(r->vOutputs, Vec_IntEntry(outputs, i), Vec_IntEntry(outputs, i+1)); Vec_IntPush(r->vSupport, Vec_IntEntry(outputs, i) >> 1); }
    r->Prefix = Acec2_RecordPrefix(r);
    Vec_IntAppend(r->vSupport, parent->vSupport); Vec_IntUniqify(r->vSupport); Vec_IntPush(r->vDependencies, Record);
    proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 8; proof->Domain = 1;
    proof->vMonomials = Vec_WecAlloc(64); proof->vCoefficients = Vec_WrdAlloc(64);
    for ( i = 0; i < Hsh_VecSize(p->h); i++ )
    {
        alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        if ( !alive ) continue;
        mono = Hsh_VecReadEntry(p->h, i); Vec_IntAppend(Vec_WecPushLevel(proof->vMonomials), mono);
        for ( j = 0; j < p->nWords; j++ ) Vec_WrdPush(proof->vCoefficients, Vec_WrdEntry(p->vCoefs, i*p->nWords+j));
    }
    proof->vRoots = Vec_IntDup(r->vSupport); proof->vIdentity = Acec2_RecordIdentity(r);
    Vec_PtrPush(m->vProofs, proof); pushed = 1; r->Proof = Vec_PtrSize(m->vProofs);
    if ( !Acec2_RecordProductGates(m, r) || !Acec2_RecordPopulate(m, r) || Acec2_Stopped(m) ) goto finish;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, old, i)
    {
        if ( old->fPolynomial != 2 || old->Width != r->Width || !Vec_IntEqual(old->vOutputs, r->vOutputs) ||
             Vec_WecSize(old->vMonomials) != Vec_WecSize(r->vMonomials) || !Vec_WrdEqual(old->vCoefficients, r->vCoefficients) ) continue;
        Vec_WecForEachLevel(r->vMonomials, mono, j)
            if ( !Vec_IntEqual(mono, Vec_WecEntry(old->vMonomials, j)) ) break;
        if ( j == Vec_WecSize(r->vMonomials) && Acec2_RecordCheck(m, old) ) { result = i; goto finish; }
    }
    Acec2_RecordFactorPopulate(m, r, NULL);
    result = Vec_PtrSize(m->vRecords); Vec_PtrPush(m->vRecords, r); r = NULL; proof = NULL; pushed = 0;
finish:
    if ( pushed ) Vec_PtrPop(m->vProofs);
    if ( proof )
    {
        Vec_IntFreeP(&proof->vRoots); Vec_IntFreeP(&proof->vIdentity);
        Vec_WecFree(proof->vMonomials); Vec_WrdFree(proof->vCoefficients); ABC_FREE(proof);
    }
    Vec_IntFreeP(&cut); if ( p ) Acec2_RecordPolyStop(p); Acec2_RecordFree(r); return result;
}

/**Function*************************************************************

  Synopsis    [Transfers a checked identity from an exact parity-decoded copy.]

  Description [The private copy preserves source gates and appends explicit
  XOR decoders. Its construction supplies the source literal and mask for
  each mapped node. Reference terms must map to ordinary source literals.
  No new node ID is introduced in the original design or its certificates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordImportMasked( Acec2_Man_t * m, Acec2_Man_t * child, Acec2_Record_t * source,
                             Vec_Int_t * back, Vec_Int_t * masks )
{
    Acec2_Record_t * r; Acec2_Proof_t * proof; Acec2_Product_t * product = NULL;
    int i, side, id, lit, mask, any = 0, result = 0;
    if ( source->Word >= 0 && source->Word < Vec_PtrSize(child->vWords) )
        product = ((Acec2_Word_t *)Vec_PtrEntry(child->vWords, source->Word))->pProduct;
    else product = source->pProductReference;
    if ( (!product && !Acec2_RecordLinearReference(child, source)) || source->Prefix < 2 ||
         !Acec2_RecordCheck(child, source) || Acec2_Stopped(m) ) return 0;
    r = Acec2_RecordAlloc(source->Width); r->Prefix = source->Prefix;
    r->vOutputMasks = Vec_IntAlloc(Vec_IntSize(source->vOutputs)/2);
    for ( side = 0; side < 2; side++ )
    {
        Vec_Int_t * v = side ? source->vTerms : source->vOutputs, * dst = side ? r->vTerms : r->vOutputs;
        for ( i = 0; i < Vec_IntSize(v); i += 2 )
        {
            id = Vec_IntEntry(v, i) >> 1;
            if ( id >= Vec_IntSize(back) || id >= Vec_IntSize(masks) || Vec_IntEntry(back, id) < 0 ) goto finish;
            lit = Vec_IntEntry(back, id) ^ (Vec_IntEntry(v, i) & 1); mask = Vec_IntEntry(masks, id);
            if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) || mask < 0 ||
                 (mask >> 1) >= Gia_ManObjNum(m->pGia) || (side && mask) ) goto finish;
            Vec_IntPushTwo(dst, lit, Vec_IntEntry(v, i+1)); Vec_IntPush(r->vSupport, lit >> 1);
            if ( !side ) { Vec_IntPush(r->vOutputMasks, mask); any |= mask; Vec_IntPush(r->vSupport, mask >> 1); }
        }
    }
    if ( !any && !product ) goto finish;
    if ( product )
    {
        r->pProductReference = ABC_CALLOC(Acec2_Product_t, 1); *r->pProductReference = *product;
        for ( side = 0; side < 2; side++ ) r->pProductReference->vOperands[side] = Vec_IntAlloc(Vec_IntSize(product->vOperands[side]));
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(product->vOperands[side], lit, i)
            {
                id = lit >> 1;
                if ( id >= Vec_IntSize(back) || id >= Vec_IntSize(masks) || Vec_IntEntry(back, id) < 0 || Vec_IntEntry(masks, id) ) goto finish;
                lit = Vec_IntEntry(back, id) ^ (lit & 1);
                if ( lit < 0 || (lit >> 1) >= Gia_ManObjNum(m->pGia) ) goto finish;
                Vec_IntPush(r->pProductReference->vOperands[side], lit); Vec_IntPush(r->vSupport, lit >> 1);
            }
    }
    Vec_IntAppend(r->vConstants, source->vConstants); Vec_IntUniqify(r->vSupport);
    Vec_IntForEachEntry(source->vCovered, id, i)
        if ( id < Vec_IntSize(back) && Vec_IntEntry(back, id) >= 2 && !Vec_IntEntry(masks, id) &&
             Gia_ObjIsAnd(Gia_ManObj(m->pGia, Vec_IntEntry(back, id) >> 1)) )
            Vec_IntPush(r->vCovered, Vec_IntEntry(back, id) >> 1);
    Vec_IntUniqify(r->vCovered);
    proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 5; proof->Domain = 1;
    proof->vIdentity = Acec2_RecordIdentity(r); proof->vRoots = Vec_IntDup(r->vSupport);
    Vec_PtrPush(m->vProofs, proof); r->Proof = Vec_PtrSize(m->vProofs);
    if ( !Acec2_RecordPopulate(m, r) )
    {
        Vec_PtrPop(m->vProofs); Vec_IntFree(proof->vIdentity); Vec_IntFree(proof->vRoots); ABC_FREE(proof);
        goto finish;
    }
    Vec_PtrPush(m->vRecords, r); Acec2_RecordFactorPopulate(m, r, NULL); return 1;
finish:
    Acec2_RecordFree(r); return result;
}

/**Function*************************************************************

  Synopsis    [Adds two weighted-reference records and cancels boundary terms.]

  Description [Cancellation preserves multiplicity and literal phase. The
  composition may narrow either modulus but cannot widen it. Its derivation
  references only earlier immutable records and is checked algebraically.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordCompose( Acec2_Man_t * m, int First, int Second, int Width )
{
    Acec2_Record_t * r, * parents[2], * old;
    Vec_Wrd_t * boundary[2]; Vec_Int_t * terms;
    int side, part, i, rank, id;
    if ( !m || First < 0 || Second < 0 || First >= Vec_PtrSize(m->vRecords) || Second >= Vec_PtrSize(m->vRecords) ||
         Width < 1 || Width > m->Pars.nMaxWidth || Acec2_Stopped(m) ) return -1;
    parents[0] = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, First); parents[1] = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Second);
    for ( part = 0; part < 2; part++ )
        if ( parents[part]->Width < Width || !Acec2_RecordLinearReference(m, parents[part]) || !Acec2_RecordCheck(m, parents[part]) ) return -1;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, old, i)
        if ( old->vParts && Vec_IntSize(old->vParts) == 8 && old->Width == Width &&
             Vec_IntEntry(old->vParts, 0) == 3 && Vec_IntEntry(old->vParts, 1) == First &&
             Vec_IntEntry(old->vParts, 4) == 3 && Vec_IntEntry(old->vParts, 5) == Second &&
             !(Vec_IntEntry(old->vParts, 2) | Vec_IntEntry(old->vParts, 3) | Vec_IntEntry(old->vParts, 6) | Vec_IntEntry(old->vParts, 7)) ) return i;
    if ( (ABC_INT64_T)Vec_IntSize(parents[0]->vOutputs)+Vec_IntSize(parents[1]->vOutputs)+
         Vec_IntSize(parents[0]->vTerms)+Vec_IntSize(parents[1]->vTerms) > 16384 )
    { m->nRecordLimits++; return -1; }
    r = Acec2_RecordAlloc(Width); r->vParts = Vec_IntAlloc(8);
    r->Discovery = parents[0]->Tree >= 0 ? parents[0]->Tree+1 : parents[0]->Discovery;
    boundary[0] = Vec_WrdAlloc(32); boundary[1] = Vec_WrdAlloc(32);
    for ( part = 0; part < 2; part++ )
    {
        id = part ? Second : First;
        Vec_IntPushTwo(r->vParts, 3, id); Vec_IntPushTwo(r->vParts, 0, 0); Vec_IntPushUnique(r->vDependencies, id);
        for ( side = 0; side < 2; side++ )
        {
            terms = side ? parents[part]->vTerms : parents[part]->vOutputs;
            for ( i = 0; i < Vec_IntSize(terms); i += 2 )
            {
                rank = Vec_IntEntry(terms, i+1);
                if ( rank < Width ) Vec_WrdPush(boundary[side], ((word)(unsigned)rank << 32) | (unsigned)Vec_IntEntry(terms, i));
            }
        }
        Vec_IntForEachEntry(parents[part]->vConstants, rank, i) if ( rank < Width ) Vec_IntPush(r->vConstants, rank);
        Vec_IntAppend(r->vCovered, parents[part]->vCovered); Vec_IntAppend(r->vSupport, parents[part]->vSupport);
    }
    Acec2_RecordCancel(r, boundary);
    Vec_WrdFree(boundary[0]); Vec_WrdFree(boundary[1]);
    Vec_IntUniqify(r->vCovered); Vec_IntUniqify(r->vSupport); r->Prefix = Acec2_RecordPrefix(r);
    if ( Acec2_Stopped(m) || !Acec2_RecordPopulate(m, r) ) { Acec2_RecordFree(r); return -1; }
    id = Vec_PtrSize(m->vRecords); Vec_PtrPush(m->vRecords, r); return id;
}

/**Function*************************************************************

  Synopsis    [Stores a proved final word while retaining its arithmetic cut.]

  Description [A word proved from a composed region's weighted roots
  inherits its input polynomial by exact transitivity. The final-adder
  implementation cone is added to coverage independently of proof support.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Record_t * Acec2_RecordWord( Acec2_Man_t * m, int Word, int Parent )
{
    Acec2_Word_t * w = (Acec2_Word_t *)Vec_PtrEntry(m->vWords, Word);
    Acec2_Record_t * base = Parent < 0 ? NULL : (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Parent), * r = Acec2_RecordAlloc(w->Width);
    Vec_Bit_t * seen = Vec_BitStart(Gia_ManObjNum(m->pGia));
    Vec_Int_t * stack = Vec_IntAlloc(100); Gia_Obj_t * o; int i, lit, id, valid = 1;
    r->Word = Word; r->Prefix = w->Width;
    if ( w->pProduct )
    {
        int side;
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(w->pProduct->vOperands[side], lit, i)
            { Acec2_BitWrite(seen, lit >> 1, 1); Vec_IntPush(r->vSupport, lit >> 1); }
    }
    else if ( w->fIndependent && !base )
    {
        Vec_IntAppend(r->vTerms, w->vTerms); Vec_IntAppend(r->vConstants, w->vConstants);
        for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 ) Vec_IntPush(r->vSupport, Vec_IntEntry(w->vTerms, i) >> 1);
        if ( w->vSumProducts )
            for ( i = 0; i < Vec_IntSize(w->vSumProducts); i += 3 )
            {
                Acec2_Record_t * child;
                id = Vec_IntEntry(w->vSumProducts, i);
                if ( id < 0 || id >= Vec_PtrSize(m->vRecords) ) { valid = 0; break; }
                child = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, id);
                Vec_IntPushUnique(r->vDependencies, id);
                Vec_IntAppend(r->vCovered, child->vCovered); Vec_IntAppend(r->vSupport, child->vSupport);
            }
    }
    else if ( base )
    {
        Vec_IntPush(r->vDependencies, Parent);
        for ( i = 0; i < Vec_IntSize(base->vTerms); i += 2 )
            if ( Vec_IntEntry(base->vTerms, i+1) < w->Width ) Vec_IntPushTwo(r->vTerms, Vec_IntEntry(base->vTerms, i), Vec_IntEntry(base->vTerms, i+1));
        Vec_IntForEachEntry(base->vConstants, id, i) if ( id < w->Width ) Vec_IntPush(r->vConstants, id);
        Vec_IntAppend(r->vCovered, base->vCovered); Vec_IntAppend(r->vSupport, base->vSupport);
        if ( w->fPolynomial )
            Vec_IntForEachEntry(base->vCut, lit, i) Acec2_BitWrite(seen, lit >> 1, 1);
    }
    else valid = 0;
    for ( i = 0; i < Vec_IntSize(w->vTerms); i += 2 ) Acec2_BitWrite(seen, Vec_IntEntry(w->vTerms, i) >> 1, 1);
    if ( w->vSourceCut )
        Vec_IntForEachEntry(w->vSourceCut, lit, i)
        {
            if ( lit < 2 || (lit & 1) || (lit >> 1) >= Gia_ManObjNum(m->pGia) ) { valid = 0; break; }
            Acec2_BitWrite(seen, lit >> 1, 1); Vec_IntPush(r->vSupport, lit >> 1);
        }
    Acec2_BitWrite(seen, 0, 1);
    Vec_IntForEachEntry(w->vBits, lit, i)
    { Vec_IntPushTwo(r->vOutputs, lit, i); Vec_IntPush(r->vSupport, lit >> 1); Vec_IntPush(stack, lit >> 1); }
    while ( Vec_IntSize(stack) )
    {
        id = Vec_IntPop(stack); if ( Vec_BitEntry(seen, id) ) continue;
        Acec2_BitWrite(seen, id, 1); o = Gia_ManObj(m->pGia, id);
        if ( (w->fPolynomial || w->fSource) && Gia_ObjIsCi(o) ) { Vec_IntPush(r->vSupport, id); continue; }
        if ( !Gia_ObjIsAnd(o) || Acec2_Stopped(m) ) { valid = 0; break; }
        Vec_IntPush(r->vCovered, id); Vec_IntPushTwo(stack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
        if ( Gia_ObjIsMux(m->pGia, o) ) Vec_IntPush(stack, Gia_ObjFaninId2(m->pGia, id));
    }
    Vec_IntFill(r->vBitStatus, w->Width, 0); Vec_IntUniqify(r->vCovered); Vec_IntUniqify(r->vSupport);
    Vec_BitFree(seen); Vec_IntFree(stack);
    if ( !valid || Acec2_Stopped(m) || !Acec2_RecordPopulate(m, r) ) { Acec2_RecordFree(r); return NULL; }
    return r;
}

/**Function*************************************************************

  Synopsis    [Includes possible high carries in a weighted boundary width.]

  Description [The largest occupied column alone is insufficient when it
  contains several roots. Bound their unsigned sum with each nonzero literal
  set to one, without assuming that these assignments are independent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_WeightedWidth( Vec_Int_t * vTerms, int Limit )
{
    Vec_Int_t * counts; int i, rank, width = 0, highest = 0;
    ABC_UINT64_T carry = 0;
    for ( i = 1; i < Vec_IntSize(vTerms); i += 2 ) width = Abc_MaxInt(width, Vec_IntEntry(vTerms, i)+1);
    width = Abc_MinInt(width, Limit); counts = Vec_IntStart(width);
    for ( i = 0; i < Vec_IntSize(vTerms); i += 2 )
    {
        rank = Vec_IntEntry(vTerms, i+1);
        if ( Vec_IntEntry(vTerms, i) && rank >= 0 && rank < width ) Vec_IntAddToEntry(counts, rank, 1);
    }
    for ( i = 0; i < width; i++ )
    {
        carry += (unsigned)Vec_IntEntry(counts, i);
        if ( carry & 1 ) highest = i+1;
        carry >>= 1;
    }
    while ( carry && i < Limit ) { highest = ++i; carry >>= 1; }
    Vec_IntFree(counts); return Abc_MaxInt(width, highest);
}

/**Function*************************************************************

  Synopsis    [Stores only completed component certificates.]

  Description [Gate coverage and proof support have separate ownership.
  Support denotes the union of source fanin cones rooted at the listed IDs;
  it is not counted as recognized arithmetic implementation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Record_t * Acec2_RecordCreate( Acec2_Man_t * m, int Tree, int Word, int Parent )
{
    Acec2_Record_t * r = ABC_CALLOC(Acec2_Record_t, 1);
    Acec2_Word_t * w = Word < 0 ? NULL : (Acec2_Word_t *)Vec_PtrEntry(m->vWords, Word);
    Acec2_Cell_t * c; int i, j, id;
    r->Tree = Tree; r->Word = Word; r->Counter = -1; r->Domain = 1;
    r->Width = w ? w->Width : Acec2_WeightedWidth(Vec_WecEntry(m->vRoots, Tree), m->Pars.nMaxWidth);
    r->Prefix = w ? w->Width : Abc_MinInt(Vec_IntEntry(m->vPrefix, Tree), r->Width);
    r->Expression = Vec_IntEntry(m->vTreeExpression, Tree);
    r->vOutputs = w ? Vec_IntAlloc(2*w->Width) : Vec_IntDup(Vec_WecEntry(m->vRoots, Tree));
    if ( w ) Vec_IntForEachEntry(w->vBits, id, i) Vec_IntPushTwo(r->vOutputs, id, i);
    r->vTerms = Vec_IntDup(w ? w->vTerms : Vec_WecEntry(m->vLeaves, Tree));
    r->vConstants = Vec_IntDup(w ? w->vConstants : Vec_WecEntry(m->vBias, Tree));
    r->vCovered = Vec_IntAlloc(100); r->vSupport = Vec_IntAlloc(100); r->vDependencies = Vec_IntAlloc(2);
    r->vCut = Vec_IntAlloc(100); r->vBitStatus = Vec_IntStart(Vec_IntSize(r->vOutputs)/2);
    r->vMonomials = Vec_WecAlloc(100); r->vCoefficients = Vec_WrdAlloc(100);
    // Narrowing a modulus also narrows every stored boundary and term.
    for ( j = 0, i = 0; i < Vec_IntSize(r->vOutputs); i += 2 )
        if ( Vec_IntEntry(r->vOutputs, i+1) < r->Width )
        { Vec_IntWriteEntry(r->vOutputs, j++, Vec_IntEntry(r->vOutputs, i)); Vec_IntWriteEntry(r->vOutputs, j++, Vec_IntEntry(r->vOutputs, i+1)); }
    Vec_IntShrink(r->vOutputs, j); Vec_IntShrink(r->vBitStatus, j/2);
    for ( j = 0, i = 0; i < Vec_IntSize(r->vTerms); i += 2 )
        if ( Vec_IntEntry(r->vTerms, i+1) < r->Width )
        { Vec_IntWriteEntry(r->vTerms, j++, Vec_IntEntry(r->vTerms, i)); Vec_IntWriteEntry(r->vTerms, j++, Vec_IntEntry(r->vTerms, i+1)); }
    Vec_IntShrink(r->vTerms, j);
    for ( j = 0, i = 0; i < Vec_IntSize(r->vConstants); i++ )
        if ( Vec_IntEntry(r->vConstants, i) < r->Width ) Vec_IntWriteEntry(r->vConstants, j++, Vec_IntEntry(r->vConstants, i));
    Vec_IntShrink(r->vConstants, j);
    if ( ((ABC_INT64_T)2*Vec_IntSize(r->vTerms)+Vec_IntSize(r->vConstants)+1)*((r->Width+63)/64) > 1000000 )
    { m->nRecordLimits++; Acec2_RecordFree(r); return NULL; }
    if ( Parent >= 0 ) Vec_IntPush(r->vDependencies, Parent);
    Vec_IntForEachEntry(Vec_WecEntry(m->vTrees, Tree), id, i)
    {
        Vec_IntAppend(r->vCovered, Vec_WecEntry(m->vCellGates, id)); c = Acec2_Cell(m, id);
        for ( j = 0; j < c->nIns; j++ ) Vec_IntPush(r->vSupport, c->In[j] >> 1);
        for ( j = 0; j < 2; j++ ) Vec_IntPush(r->vSupport, c->Out[j] >> 1);
    }
    for ( i = 0; i < Vec_IntSize(r->vOutputs); i += 2 ) Vec_IntPush(r->vSupport, Vec_IntEntry(r->vOutputs, i) >> 1);
    Vec_IntUniqify(r->vCovered); Vec_IntUniqify(r->vSupport);
    if ( r->Width < 1 ) { Acec2_RecordFree(r); return NULL; }
    if ( !Acec2_RecordPopulate(m, r) )
    {
        Abc_Print(-1, "&atree2: internal certificate error in region %d.\n", Tree);
        Acec2_RecordFree(r); return NULL;
    }
    return r;
}

/**Function*************************************************************

  Synopsis    [Imports a general counter through the common identity checker.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Record_t * Acec2_RecordCounter( Acec2_Man_t * m, int Counter )
{
    Acec2_Counter_t * c = (Acec2_Counter_t *)Vec_PtrEntry(m->vCounters, Counter);
    Acec2_Record_t * r = ABC_CALLOC(Acec2_Record_t, 1);
    int i, counts[8] = {0};
    r->Tree = r->Word = r->Expression = -1; r->Counter = Counter;
    r->Width = c->Width; r->Domain = 1;
    r->vOutputs = Vec_IntDup(c->vOutputs); r->vTerms = Vec_IntDup(c->vInputs); r->vConstants = Vec_IntAlloc(0);
    r->vCovered = Vec_IntDup(c->vGates); r->vSupport = Vec_IntAlloc(16); r->vDependencies = Vec_IntAlloc(0);
    r->vCut = Vec_IntAlloc(16); r->vBitStatus = Vec_IntStart(Vec_IntSize(r->vOutputs)/2);
    r->vMonomials = Vec_WecAlloc(16); r->vCoefficients = Vec_WrdAlloc(16);
    for ( i = 0; i < Vec_IntSize(c->vInputs); i += 2 ) Vec_IntPush(r->vSupport, Vec_IntEntry(c->vInputs, i) >> 1);
    for ( i = 0; i < Vec_IntSize(c->vOutputs); i += 2 )
    {
        Vec_IntPush(r->vSupport, Vec_IntEntry(c->vOutputs, i) >> 1);
        counts[Vec_IntEntry(c->vOutputs, i+1)]++;
    }
    while ( r->Prefix < r->Width && counts[r->Prefix] <= 1 ) r->Prefix++;
    Vec_IntUniqify(r->vSupport);
    if ( !Acec2_RecordPopulate(m, r) ) { Acec2_RecordFree(r); return NULL; }
    return r;
}

/**Function*************************************************************

  Synopsis    [Imports only newly completed counter certificates.]

  Description [Existing records retain their IDs and dependencies.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordCounters( Acec2_Man_t * m )
{
    Acec2_Record_t * r;
    while ( m->nCounterRecords < Vec_PtrSize(m->vCounters) && !Acec2_Stopped(m) )
    {
        r = Acec2_RecordCounter(m, m->nCounterRecords++);
        if ( r ) Vec_PtrPush(m->vRecords, r);
    }
}

/**Function*************************************************************

  Synopsis    [Imports counters found by any analysis, including failed word proofs.]

  Description [A completed counter certificate outlives the polynomial
  attempt that discovered it. Internal cells-only analyses need no records.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RefreshCounterRecords( Acec2_Man_t * m )
{
    int before;
    if ( !m->nRecordStage || m->nCounterRecords == Vec_PtrSize(m->vCounters) ) return;
    before = Vec_PtrSize(m->vRecords);
    Acec2_RecordCounters(m);
    if ( Vec_PtrSize(m->vRecords) != before ) Acec2_BuildCounterRegions(m);
}

/**Function*************************************************************

  Synopsis    [Retains a completed region word before further discovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RecordTreeWord( Acec2_Man_t * m, int Tree )
{
    Acec2_Record_t * r; int parent, word;
    if ( !m->nRecordStage || Tree < 0 || Tree >= Vec_IntSize(m->vTreeRecord) || Acec2_Stopped(m) ) return;
    parent = Vec_IntEntry(m->vTreeRecord, Tree); word = Vec_IntEntry(m->vTreeWord, Tree);
    if ( parent < 0 || word < 0 || ((Acec2_Record_t *)Vec_PtrEntry(m->vRecords, parent))->Word == word ) return;
    r = Acec2_RecordCreate(m, Tree, word, parent); if ( !r ) return;
    Vec_IntWriteEntry(m->vTreeRecord, Tree, Vec_PtrSize(m->vRecords)); Vec_PtrPush(m->vRecords, r);
}

/**Function*************************************************************

  Synopsis    [Stores completed cell certificates before optional searches.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_BuildRecordsBasic( Acec2_Man_t * m )
{
    Acec2_Record_t * r; int tree, parent, word;
    if ( m->nRecordStage ) return;
    m->nRecordStage = 1;
    Vec_IntFill(m->vTreeRecord, Vec_WecSize(m->vTrees), -1);
    for ( tree = 0; tree < Vec_WecSize(m->vTrees) && !Acec2_Stopped(m); tree++ )
    {
        r = Acec2_RecordCreate(m, tree, -1, -1); if ( !r ) continue;
        parent = Vec_PtrSize(m->vRecords); Vec_PtrPush(m->vRecords, r); Vec_IntWriteEntry(m->vTreeRecord, tree, parent);
        word = Vec_IntEntry(m->vTreeWord, tree); if ( word < 0 ) continue;
        r = Acec2_RecordCreate(m, tree, word, parent); if ( !r ) continue;
        Vec_IntWriteEntry(m->vTreeRecord, tree, Vec_PtrSize(m->vRecords)); Vec_PtrPush(m->vRecords, r);
    }
    Acec2_RecordCounters(m);
    Acec2_BuildCellRegions(m);
    Acec2_BuildCounterRegions(m);
}

/**Function*************************************************************

  Synopsis    [Requests shared counter records without requiring an adder region.]

  Description [One source work unit visits at most four parity roots or
  queued boundary extensions. The source cut, truth workspace and completed
  attempts persist across requests. Only newly checked counters and changed
  composed identities are appended; reconstruction keeps its original cover.]

  SideEffects [Updates recognition work and stage timing.]

  SeeAlso     []

***********************************************************************/
int Acec2_EnrichCounters( Acec2_Man_t * m, Vec_Bit_t * vLive, int * pnWork )
{
    abctime clk, stage; int before, work = 4;
    if ( !m || !pnWork || *pnWork <= 0 || Acec2_Stopped(m) ) return 0;
    clk = Abc_Clock(); Acec2_BuildRecordsBasic(m); before = Vec_PtrSize(m->vRecords);
    m->nCounterRequests++;
    Acec2_AdvanceCounters(m, vLive, &work);
    if ( work < 4 ) { (*pnWork)--; m->nCounterWork += 4-work; }
    stage = Abc_Clock(); m->TimeCounters += stage-clk;
    Acec2_RefreshCounterRecords(m);
    m->TimeRecords += Abc_Clock()-stage;
    m->Time += Abc_Clock()-clk;
    return Vec_PtrSize(m->vRecords)-before;
}

/**Function*************************************************************

  Synopsis    [Requests proved carry alternatives and their checked region view.]

  Description [Existing cells and records retain their IDs. The closure
  partition is rebuilt only after a new source identity has been admitted.]

  SideEffects [Updates recognition work and stage timing.]

  SeeAlso     []

***********************************************************************/
int Acec2_EnrichCarries( Acec2_Man_t * m, Vec_Bit_t * vLive, int * pnWork )
{
    abctime clk, stage; int before, added;
    if ( !m || !pnWork || *pnWork <= 0 || m->fCarryComplete || Acec2_Stopped(m) ) return 0;
    clk = Abc_Clock(); Acec2_BuildRecordsBasic(m); before = Vec_PtrSize(m->vRecords);
    m->nCarryRequests++; added = Acec2_AdvanceCarries(m, vLive, pnWork);
    stage = Abc_Clock(); m->TimeDetect += stage-clk;
    if ( added ) Acec2_BuildClosureRegions(m);
    added = Vec_PtrSize(m->vRecords)-before; m->nCarryRecords += added;
    m->TimeRecords += Abc_Clock()-stage; m->Time += Abc_Clock()-clk;
    return added;
}

/**Function*************************************************************

  Synopsis    [Enriches the shared identities with words and product expressions.]

  Description [CEC can first use the inexpensive cell records, including
  alternative partitions, without paying for SAT word closure or product
  certificates. Standalone profiling requests the complete analysis.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_BuildRecords( Acec2_Man_t * m )
{
    Acec2_Record_t * r; Vec_Int_t * vMap; int tree, firstProduct;
    Acec2_BuildRecordsBasic(m);
    // Expression discovery follows the early certificate checkpoint. Refresh
    // its report links without changing any stored identity or proof.
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, tree)
        if ( r->Tree >= 0 && r->Tree < Vec_IntSize(m->vTreeExpression) )
            r->Expression = Vec_IntEntry(m->vTreeExpression, r->Tree);
    if ( m->nRecordStage > m->Pars.nAnalysisLevel ) return;
    if ( m->nRecordStage < 2 )
    {
        Acec2_CloseGaps(m);
        Acec2_CloseRecordWords(m);
        Acec2_DiscoverLinearWords(m); m->nRecordStage = 2;
    }
    if ( m->Pars.nAnalysisLevel < 2 ) return;
    vMap = Vec_IntStart(Gia_ManObjNum(m->pGia));
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, tree)
        if ( !Acec2_Stopped(m) ) Acec2_RecordFactorPopulate(m, r, vMap);
    Acec2_RecordExtendProducts(m, vMap, NULL);
    if ( m->Pars.nAnalysisLevel >= 3 ) Acec2_RecordComposeProducts(m, vMap, 0, NULL, NULL);
    firstProduct = Vec_PtrSize(m->vRecords);
    Acec2_RecordProductWords(m, vMap);
    if ( m->Pars.nAnalysisLevel >= 3 )
    {
        Acec2_RecordComposeProducts(m, vMap, firstProduct, NULL, NULL);
        Acec2_RecordSumWords(m, vMap, NULL, NULL);
    }
    m->nRecordStage = m->Pars.nAnalysisLevel+1;
    Vec_IntFree(vMap);
}

/**Function*************************************************************

  Synopsis    [Constructs canonical columns from a checked persistent polynomial.]

  Description [The modulus may be narrowed, never widened. Mapping source
  variables through proved equalities is the only cross-design operation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordColumns( Acec2_Record_t * r, Gia_Man_t * g, Vec_Int_t * vMap,
                         Vec_Int_t * vFrontier, Vec_Wec_t * vCols, Vec_Int_t * vConst,
                         Acec2_Par_t * pPars, abctime Deadline, int nMaxObjs )
{
    int width = Vec_IntSize(vConst), nWords = (r->Width+63)/64, i, j, id, lit, rank, sign;
    Vec_Int_t * v; Vec_Wrd_t * vCoef = NULL; word carry, value;
    if ( width < 1 || width > r->Width ) return 0;
    if ( vFrontier )
        Vec_IntForEachEntry(r->vCut, lit, i)
            if ( !Vec_IntEntry(vFrontier, Vec_IntEntry(vMap, lit >> 1) >> 1) ) return 0;
    vCoef = Vec_WrdStart((width+63)/64);
    Vec_WecForEachLevel(r->vMonomials, v, i)
    {
        if ( (i & 255) == 0 && Acec2_Stop(pPars, Deadline) ) { Vec_WrdFree(vCoef); return 0; }
        lit = 1;
        Vec_IntForEachEntry(v, id, j)
        {
            lit = Gia_ManHashAnd(g, lit, Vec_IntEntry(vMap, id));
            if ( Gia_ManObjNum(g) >= nMaxObjs ) { Vec_WrdFree(vCoef); return 0; }
        }
        sign = Vec_IntSize(v) && ((Vec_WrdEntry(r->vCoefficients, i*nWords+(width-1)/64) >> ((width-1)&63)) & 1);
        carry = 1;
        for ( j = 0; j < Vec_WrdSize(vCoef); j++ )
        {
            value = Vec_WrdEntry(r->vCoefficients, i*nWords+j);
            if ( sign ) { value = ~value; Vec_WrdWriteEntry(vCoef, j, value+carry); carry = value+carry < value; }
            else Vec_WrdWriteEntry(vCoef, j, value);
        }
        for ( rank = 0; rank < width; rank++ )
            if ( (Vec_WrdEntry(vCoef, rank/64) >> (rank & 63)) & 1 )
            {
                if ( Vec_IntSize(v) ) Vec_WecPush(vCols, rank, lit ^ sign);
                if ( !Vec_IntSize(v) || sign )
                    for ( j = rank; j < width; j++ )
                    {
                        Vec_IntWriteEntry(vConst, j, Vec_IntEntry(vConst, j) ^ 1);
                        if ( Vec_IntEntry(vConst, j) != sign ) break;
                    }
            }
    }
    Vec_WrdFree(vCoef); return 1;
}

/**Function*************************************************************

  Synopsis    [Adds a complete signed modular coefficient to a monomial.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordCoefficient( Acec2_RecordPoly_t * p, word * coef, int Sign )
{
    int id = Hsh_VecManAdd(p->h, p->vMono), i;
    word old, add, next, value, carry = Sign < 0;
    while ( Vec_WrdSize(p->vCoefs) < (id+1)*p->nWords ) Vec_WrdPush(p->vCoefs, 0);
    for ( i = 0; i < p->nWords; i++ )
    {
        old = Vec_WrdEntry(p->vCoefs, id*p->nWords+i); add = Sign < 0 ? ~coef[i] : coef[i];
        value = old+add; next = value < old; old = value; value += carry; carry = next | (value < old);
        Vec_WrdWriteEntry(p->vCoefs, id*p->nWords+i, value);
    }
    if ( p->Width & 63 )
    {
        i = (id+1)*p->nWords-1;
        Vec_WrdWriteEntry(p->vCoefs, i, Vec_WrdEntry(p->vCoefs, i) & (((word)1 << (p->Width & 63))-1));
    }
}

/**Function*************************************************************

  Synopsis    [Subtracts an explicit product from a modular polynomial.]

  Description [Widths, signed ports, literal phases, shifts and repeated
  bits have their explicit bit-vector meanings. A negative shift is the
  one-bit truncation supported by the factor finder.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordSubtractProduct( Acec2_RecordPoly_t * p, Acec2_Product_t * product, Vec_Int_t * vCut )
{
    int i, j, side, a, b, ca, cb, rank, sign;
    if ( product->Shift < -1 || product->Shift > p->Width || (product->fNeg & ~1) ) return 0;
    for ( side = 0; side < 2; side++ )
    {
        if ( !Vec_IntSize(product->vOperands[side]) || (product->fSigned[side] & ~1) ) return 0;
        Vec_IntForEachEntry(product->vOperands[side], a, i)
            if ( a < 0 || (a >= 2 && Vec_IntFind(vCut, a & ~1) < 0) ) return 0;
    }
    for ( i = 0; i < Vec_IntSize(product->vOperands[0]); i++ )
        for ( j = 0; j < Vec_IntSize(product->vOperands[1]); j++ )
        {
            rank = i+j+product->Shift; if ( rank < 0 || rank >= p->Width ) continue;
            a = Vec_IntEntry(product->vOperands[0], i); b = Vec_IntEntry(product->vOperands[1], j);
            ca = a & 1; cb = b & 1;
            sign = product->fNeg ^ (product->fSigned[0] && i == Vec_IntSize(product->vOperands[0])-1) ^
                   (product->fSigned[1] && j == Vec_IntSize(product->vOperands[1])-1) ? 1 : -1;
            if ( ca && cb ) Acec2_RecordPower(p, -1, -1, rank, sign);
            if ( cb ) Acec2_RecordPower(p, a >> 1, -1, rank, ca ? -sign : sign);
            if ( ca ) Acec2_RecordPower(p, b >> 1, -1, rank, cb ? -sign : sign);
            Acec2_RecordPower(p, a >> 1, b >> 1, rank, ca == cb ? sign : -sign);
        }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Expands product operands using complete integer adder identities.]

  Description [Truncated intermediate sums remain explicit words. Only an
  exact complete boundary can be distributed through a product. Residual
  terms are preserved, and negative shifts are left to their existing proof.]

  SideEffects [Records which source regions justify the operand expansion.]

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordComposition( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vRegions )
{
    Acec2_RecordPoly_t * p = NULL; Acec2_Product_t * product;
    Vec_Int_t * terms[2] = {NULL, NULL}, * v;
    int index, side, i, j, lifted[2], a, b, ca, cb, rank, sign, good = 0;
    ABC_INT64_T pairs = 0;
    Vec_IntClear(vRegions);
    if ( r->vOutputMasks || !r->vFactors || r->FactorWidth != r->Width || !Vec_PtrSize(r->vFactors) ) return NULL;
    Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, index)
        if ( product->Shift < 0 ) return NULL;
    p = Acec2_RecordPolyStart(r->Width);
    Vec_WecForEachLevel(r->vResidual, v, i)
    {
        Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v);
        Acec2_RecordCoefficient(p, Vec_WrdEntryP(r->vResidualCoefs, i*p->nWords), 1);
    }
    Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, index)
    {
        if ( Acec2_Stopped(m) ) goto finish;
        for ( side = 0; side < 2; side++ )
        {
            terms[side] = Acec2_ExprOperand(m, product->vOperands[side], product->fSigned[side], lifted+side, m->Deadline);
            if ( lifted[side] )
            {
                if ( Vec_IntEntry(m->vTreeRecord, lifted[side]-1) < 0 ) goto finish;
                Vec_IntPushThree(vRegions, index, side, lifted[side]-1);
            }
        }
        pairs += (ABC_INT64_T)(Vec_IntSize(terms[0])/2)*(Vec_IntSize(terms[1])/2);
        if ( (pairs+Vec_WecSize(r->vResidual))*p->nWords > 1000000 ) { m->nRecordLimits++; goto finish; }
        for ( i = 0; i < Vec_IntSize(terms[0]); i += 2 )
        {
            if ( Acec2_Stopped(m) ) goto finish;
            for ( j = 0; j < Vec_IntSize(terms[1]); j += 2 )
            {
                rank = (Vec_IntEntry(terms[0], i+1) >> 1)+(Vec_IntEntry(terms[1], j+1) >> 1)+product->Shift;
                if ( rank >= r->Width ) continue;
                sign = ((Vec_IntEntry(terms[0], i+1)^Vec_IntEntry(terms[1], j+1)^product->fNeg)&1) ? -1 : 1;
                a = Vec_IntEntry(terms[0], i); b = Vec_IntEntry(terms[1], j); ca = a & 1; cb = b & 1;
                if ( ca && cb ) Acec2_RecordPower(p, -1, -1, rank, sign);
                if ( cb ) Acec2_RecordPower(p, a >> 1, -1, rank, ca ? -sign : sign);
                if ( ca ) Acec2_RecordPower(p, b >> 1, -1, rank, cb ? -sign : sign);
                Acec2_RecordPower(p, a >> 1, b >> 1, rank, ca == cb ? sign : -sign);
            }
        }
        Vec_IntFreeP(&terms[0]); Vec_IntFreeP(&terms[1]);
    }
    good = Vec_IntSize(vRegions) && !Acec2_Stopped(m);
finish:
    Vec_IntFreeP(&terms[0]); Vec_IntFreeP(&terms[1]);
    if ( !good ) { Acec2_RecordPolyStop(p); return NULL; }
    return p;
}

/**Function*************************************************************

  Synopsis    [Checks a composed expression's boundary and proof dependencies.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordCompositionCheck( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Record_t * parent; Vec_Int_t * deps; int i, tree, here, good;
    if ( r->Compose < 1 || r->Compose > Vec_PtrSize(m->vRecords) || r->Extend || r->vParts ||
         r->Tree != -1 || r->Word != -1 || r->Counter != -1 || !r->vComposition || Vec_IntSize(r->vComposition) % 3 ) return 0;
    here = Vec_PtrFind(m->vRecords, r);
    if ( here >= 0 && r->Compose-1 >= here ) return 0;
    parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, r->Compose-1);
    if ( r->Width != parent->Width || r->Prefix != parent->Prefix ||
         !Vec_IntEqual(r->vOutputs, parent->vOutputs) || !Vec_IntEqual(r->vTerms, parent->vTerms) ||
         !Vec_IntEqual(r->vConstants, parent->vConstants) ) return 0;
    deps = Vec_IntAlloc(16); Vec_IntPush(deps, r->Compose-1); good = 1;
    for ( i = 2; i < Vec_IntSize(r->vComposition); i += 3 )
    {
        tree = Vec_IntEntry(r->vComposition, i);
        if ( tree < 0 || tree >= Vec_IntSize(m->vTreeRecord) || Vec_IntEntry(m->vTreeRecord, tree) < 0 ) { good = 0; break; }
        if ( here >= 0 && Vec_IntEntry(m->vTreeRecord, tree) >= here ) { good = 0; break; }
        Vec_IntPushUnique(deps, Vec_IntEntry(m->vTreeRecord, tree));
    }
    good &= Vec_IntEqual(deps, r->vDependencies); Vec_IntFree(deps); return good;
}

/**Function*************************************************************

  Synopsis    [Stores distributed sum-of-products certificates alongside their source form.]

  Description [The original component remains available. A new polynomial
  has the same boundary and explicit dependencies on the checked operand
  adders, so profiling and equivalence matching consume the same result.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordComposeProducts( Acec2_Man_t * m, Vec_Int_t * vMap, int First, Vec_Int_t * vSelected, int * pnQueries )
{
    Acec2_Record_t * parent, * r; Vec_Int_t * cells, * gates; int i, j, k, id, tree, n = Vec_PtrSize(m->vRecords);
    if ( !m->vComposeTried ) m->vComposeTried = Vec_IntAlloc(100);
    Vec_IntFillExtra(m->vComposeTried, n, 0);
    for ( i = First; i < n && !Acec2_Stopped(m); i++ )
    {
        if ( vSelected && (i >= Vec_IntSize(vSelected) || !Vec_IntEntry(vSelected, i)) ) continue;
        parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, i);
        if ( parent->vOutputMasks || !parent->vFactors || parent->FactorWidth != parent->Width || Vec_IntEntry(m->vComposeTried, i) ) continue;
        for ( j = 0; j < Vec_PtrSize(m->vRecords); j++ )
            if ( ((Acec2_Record_t *)Vec_PtrEntry(m->vRecords, j))->Compose == i+1 ) break;
        if ( j < Vec_PtrSize(m->vRecords) ) continue;
        if ( pnQueries ) { if ( *pnQueries <= 0 ) break; (*pnQueries)--; }
        r = Acec2_RecordAlloc(parent->Width); r->Prefix = parent->Prefix; r->Compose = i+1;
        r->vComposition = Vec_IntAlloc(16);
        Vec_IntAppend(r->vOutputs, parent->vOutputs); Vec_IntAppend(r->vTerms, parent->vTerms); Vec_IntAppend(r->vConstants, parent->vConstants);
        Vec_IntAppend(r->vCovered, parent->vCovered); Vec_IntAppend(r->vSupport, parent->vSupport); Vec_IntAppend(r->vBitStatus, parent->vBitStatus);
        if ( !Acec2_RecordPopulate(m, r) )
        {
            // This recipe depends only on the parent's immutable factors
            // and original integer-adder regions, not on the CEC effort tier.
            if ( !Acec2_Stopped(m) ) Vec_IntWriteEntry(m->vComposeTried, i, 1);
            Acec2_RecordFree(r); continue;
        }
        for ( j = 2; j < Vec_IntSize(r->vComposition); j += 3 )
        {
            tree = Vec_IntEntry(r->vComposition, j); cells = Vec_WecEntry(m->vTrees, tree);
            Vec_IntForEachEntry(cells, id, k) { gates = Vec_WecEntry(m->vCellGates, id); Vec_IntAppend(r->vCovered, gates); }
        }
        Vec_IntUniqify(r->vCovered);
        Acec2_RecordFactorPopulate(m, r, vMap); Vec_PtrPush(m->vRecords, r);
        Vec_IntWriteEntry(m->vComposeTried, i, 1);
    }
}

/**Function*************************************************************

  Synopsis    [Computes the exact residual after the reported product terms.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_RecordPoly_t * Acec2_RecordResidual( Acec2_Record_t * r )
{
    Acec2_RecordPoly_t * p; Acec2_Product_t * product; Vec_Int_t * v;
    ABC_INT64_T pairs = 0; int i, nWords = (r->Width+63)/64;
    if ( r->FactorWidth < 2 || r->FactorWidth > r->Width || !r->vFactors || !Vec_PtrSize(r->vFactors) ) return NULL;
    Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, i)
        pairs += (ABC_INT64_T)Vec_IntSize(product->vOperands[0])*Vec_IntSize(product->vOperands[1]);
    if ( (pairs+Vec_WecSize(r->vMonomials))*((r->FactorWidth+63)/64) > 1000000 ) return NULL;
    p = Acec2_RecordPolyStart(r->FactorWidth);
    Vec_WecForEachLevel(r->vMonomials, v, i)
    {
        Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v);
        Acec2_RecordCoefficient(p, Vec_WrdEntryP(r->vCoefficients, i*nWords), 1);
    }
    Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, i)
        if ( !Acec2_RecordSubtractProduct(p, product, r->vCut) ) { Acec2_RecordPolyStop(p); return NULL; }
    return p;
}

/**Function*************************************************************

  Synopsis    [Independently checks every coefficient in a reported factorization.]

  Description [Residual terms remain explicit. A product label alone never
  claims that the entire component is a multiplier.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordFactorCheck( Acec2_Record_t * r )
{
    Acec2_RecordPoly_t * p = Acec2_RecordResidual(r);
    Vec_Bit_t * seen = NULL; Vec_Int_t * v; int i, j, id, alive, count = 0, good = 0;
    if ( !p || !r->vResidual || !r->vResidualCoefs ) goto finish;
    for ( i = 0; i < Hsh_VecSize(p->h); i++ )
    {
        alive = 0; for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        count += alive != 0;
    }
    if ( count != Vec_WecSize(r->vResidual) || Vec_WrdSize(r->vResidualCoefs) != count*p->nWords ) goto finish;
    seen = Vec_BitStart(Hsh_VecSize(p->h));
    Vec_WecForEachLevel(r->vResidual, v, i)
    {
        Vec_IntClear(p->vMono); Vec_IntAppend(p->vMono, v); id = Hsh_VecManAdd(p->h, p->vMono);
        if ( id >= Vec_WrdSize(p->vCoefs)/p->nWords || Vec_BitEntry(seen, id) ) goto finish;
        Acec2_BitWrite(seen, id, 1);
        for ( j = 0; j < p->nWords; j++ )
            if ( Vec_WrdEntry(r->vResidualCoefs, i*p->nWords+j) != Vec_WrdEntry(p->vCoefs, id*p->nWords+j) ) goto finish;
    }
    good = 1;
finish:
    Vec_BitFreeP(&seen); if ( p ) Acec2_RecordPolyStop(p); return good;
}

/**Function*************************************************************

  Synopsis    [Stores product terms and the exact remaining polynomial.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordFactorPopulate( Acec2_Man_t * m, Acec2_Record_t * r, Vec_Int_t * vMap )
{
    Acec2_RecordPoly_t * p; Acec2_Product_t * product, * copy;
    Acec2_Expr_t * expr = r->Tree >= 0 ? Acec2_Expression(m, r->Tree) : NULL;
    Vec_Ptr_t * factors = NULL; int i, j, alive, shift = 0;
    Acec2_Word_t * w = r->Word < 0 ? NULL : (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word);
    if ( r->vFactors ) return;
    // Preserve proved source-word phases when an expression already has
    // them. Factoring only positive polynomial variables can otherwise
    // describe a complemented operand and a large linear correction.
    // A wider weighted boundary can contain an additional carry. Keep the
    // known operand interpretation and account for every high correction in
    // the exact residual at this record's modulus.
    if ( expr && expr->Width <= r->Width ) factors = expr->vProducts;
    else if ( r->Extend && Vec_IntSize(r->vDependencies) == 1 )
    {
        Acec2_Record_t * parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, Vec_IntEntry(r->vDependencies, 0));
        factors = parent->vFactors; shift = 1;
    }
    product = r->pProductReference ? r->pProductReference : w ? w->pProduct : NULL;
    if ( product )
    {
        r->vFactors = Vec_PtrAlloc(1); r->FactorWidth = r->Width;
        copy = ABC_ALLOC(Acec2_Product_t, 1); *copy = *product;
        copy->vOperands[0] = Vec_IntDup(product->vOperands[0]); copy->vOperands[1] = Vec_IntDup(product->vOperands[1]);
        Vec_PtrPush(r->vFactors, copy);
    }
    else if ( factors && Vec_PtrSize(factors) )
    {
        r->vFactors = Vec_PtrAlloc(Vec_PtrSize(factors)); r->FactorWidth = r->Width;
        Vec_PtrForEachEntry(Acec2_Product_t *, factors, product, i)
        {
            copy = ABC_ALLOC(Acec2_Product_t, 1); *copy = *product; copy->Shift += shift;
            copy->vOperands[0] = Vec_IntDup(product->vOperands[0]); copy->vOperands[1] = Vec_IntDup(product->vOperands[1]);
            Vec_PtrPush(r->vFactors, copy);
        }
    }
    else r->vFactors = Acec2_RecordFactors(m, r, vMap, &r->FactorWidth);
    if ( !r->vFactors ) return;
    p = Acec2_RecordResidual(r);
    if ( p )
    {
        r->vResidual = Vec_WecAlloc(16); r->vResidualCoefs = Vec_WrdAlloc(16);
        for ( i = 0; i < Hsh_VecSize(p->h); i++ )
        {
            alive = 0; for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
            if ( !alive ) continue;
            Vec_IntAppend(Vec_WecPushLevel(r->vResidual), Hsh_VecReadEntry(p->h, i));
            for ( j = 0; j < p->nWords; j++ ) Vec_WrdPush(r->vResidualCoefs, Vec_WrdEntry(p->vCoefs, i*p->nWords+j));
        }
        Acec2_RecordPolyStop(p);
        if ( Acec2_RecordFactorCheck(r) ) return;
        Abc_Print(-1, "&atree2: internal component-factor certificate error.\n");
    }
    else m->nRecordLimits++;
    Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, i)
    { Vec_IntFree(product->vOperands[0]); Vec_IntFree(product->vOperands[1]); ABC_FREE(product); }
    Vec_PtrFreeP(&r->vFactors); Vec_WecFreeP(&r->vResidual); Vec_WrdFreeP(&r->vResidualCoefs); r->FactorWidth = 0;
}

/**Function*************************************************************

  Synopsis    [Stores an independently proved product in the common record form.]

  Description [The caller supplies a completed source-word certificate.
  Equal observed words and operand descriptions are stored once. Discovery
  identifies the proposing region without claiming ownership of its gates.]

  SideEffects [Consumes the supplied word on success, duplication or failure.]

  SeeAlso     []

***********************************************************************/
int Acec2_RecordAddProductWord( Acec2_Man_t * m, Acec2_Word_t * w, int Tree )
{
    Acec2_Word_t * old;
    Acec2_Record_t * r;
    int i, side, word;
    if ( !w ) return 0;
    if ( !w->pProduct || Acec2_Stopped(m) ) { Acec2_WordFree(w); return 0; }
    Vec_PtrForEachEntry(Acec2_Word_t *, m->vWords, old, i)
    {
        if ( !old->pProduct || old->Width != w->Width || !Vec_IntEqual(old->vBits, w->vBits) ) continue;
        for ( side = 0; side < 2; side++ )
            if ( old->pProduct->fSigned[side] != w->pProduct->fSigned[side] ||
                 !Vec_IntEqual(old->pProduct->vOperands[side], w->pProduct->vOperands[side]) ) break;
        if ( side == 2 ) { Acec2_WordFree(w); return 0; }
    }
    word = Vec_PtrSize(m->vWords); Vec_PtrPush(m->vWords, w);
    r = Acec2_RecordWord(m, word, -1);
    if ( r )
    {
        r->Discovery = Tree+1;
        Acec2_RecordFactorPopulate(m, r, NULL);
        if ( !Acec2_Stopped(m) && Acec2_RecordCheck(m, r) )
        { Vec_PtrPush(m->vRecords, r); m->nProductWords++; return 1; }
        Acec2_RecordFree(r);
    }
    Vec_PtrPop(m->vWords); Acec2_WordFree(w); return 0;
}

/**Function*************************************************************

  Synopsis    [Finds source product words from retained operand proposals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordProductWords( Acec2_Man_t * m, Vec_Int_t * vMap )
{
    Hsh_VecMan_t * seen = Hsh_VecManStart(100);
    Vec_Ptr_t * candidates = Vec_PtrAlloc(100), * guesses = Vec_PtrAlloc(16), * factors;
    Vec_Int_t * prefixes = Vec_IntAlloc(100), * key = Vec_IntAlloc(100);
    Acec2_Record_t * r; Acec2_Product_t * product; Acec2_Word_t * w;
    int i, j, side, id, before, pass;
    if ( !m->Pars.fAlgebra ) goto finish;
    for ( pass = 0; pass < 2 && !Acec2_Stopped(m); pass++ )
    for ( i = 0; i < (pass ? Vec_WecSize(m->vTrees) : Vec_PtrSize(m->vRecords)); i++ )
    {
        if ( Acec2_Stopped(m) ) break;
        r = pass ? NULL : (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, i);
        factors = r ? r->vFactors : NULL;
        if ( !factors && Vec_PtrSize(candidates) < 64 )
        {
            factors = r ? Acec2_RecordProductProposals(m, r, vMap) : Acec2_RegionProductProposals(m, i);
            if ( factors ) Vec_PtrForEachEntry(Acec2_Product_t *, factors, product, j) Vec_PtrPush(guesses, product);
        }
        if ( !factors ) continue;
        Vec_PtrForEachEntry(Acec2_Product_t *, factors, product, j)
        {
            if ( product->fNeg ) continue;
            Vec_IntClear(key);
            for ( side = 0; side < 2; side++ )
            {
                Vec_IntPushTwo(key, product->fSigned[side], Vec_IntSize(product->vOperands[side]));
                Vec_IntAppend(key, product->vOperands[side]);
            }
            before = Hsh_VecSize(seen); id = Hsh_VecManAdd(seen, key);
            if ( id == before ) { Vec_PtrPush(candidates, product); Vec_IntPush(prefixes, 0); }
            if ( r && r->vFactors && !product->Shift && Vec_PtrSize(r->vFactors) == 1 && !Vec_WecSize(r->vResidual) )
                Vec_IntWriteEntry(prefixes, id, Abc_MaxInt(Vec_IntEntry(prefixes, id), Abc_MinInt(r->Prefix, r->FactorWidth)));
        }
        if ( !r || factors != r->vFactors ) Vec_PtrFree(factors);
    }
    Vec_PtrForEachEntry(Acec2_Product_t *, candidates, product, i)
    {
        if ( Acec2_Stopped(m) ) break;
        if ( m->nProductAttempts >= 64 ) { m->nProductLimits++; break; }
        w = Acec2_CertifyProductWord(m, product, Vec_IntEntry(prefixes, i)); if ( !w ) continue;
        Acec2_RecordAddProductWord(m, w, -1);
    }
finish:
    Vec_PtrForEachEntry(Acec2_Product_t *, guesses, product, i)
    { Vec_IntFree(product->vOperands[0]); Vec_IntFree(product->vOperands[1]); ABC_FREE(product); }
    Vec_PtrFree(guesses);
    Hsh_VecManStop(seen); Vec_PtrFree(candidates); Vec_IntFree(prefixes); Vec_IntFree(key);
}

/**Function*************************************************************

  Synopsis    [Finds a complete independently certified product with these operands.]

  Description [Operand exchange is allowed. Shift and negation belong to
  the consuming sum, while signedness stays with each operand.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordFullProduct( Acec2_Man_t * m, Acec2_Product_t * product )
{
    Acec2_Record_t * r; Acec2_Product_t * p;
    int i, side, swap;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        if ( r->Prefix != r->Width ) continue;
        p = Acec2_RecordProduct(m, r);
        if ( !p || p->Shift || p->fNeg || r->Width < Vec_IntSize(p->vOperands[0])+Vec_IntSize(p->vOperands[1]) ) continue;
        for ( swap = 0; swap < 2; swap++ )
        {
            for ( side = 0; side < 2; side++ )
                if ( product->fSigned[side] != p->fSigned[side ^ swap] ||
                     !Vec_IntEqual(product->vOperands[side], p->vOperands[side ^ swap]) ) break;
            if ( side == 2 ) return i;
        }
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Orders source product terms without process-global state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordSumCompare( const void * a, const void * b )
{
    const int * x = (const int *)a, * y = (const int *)b; int i;
    for ( i = 0; i < 3; i++ ) if ( x[i] != y[i] ) return x[i] < y[i] ? -1 : 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Proposes a wider expression from an existing exact factorization.]

  Description [The earlier prefix supplies a hypothesis, not a proof of
  high bits. Full product records supply the independent final-adder cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_Word_t * Acec2_RecordSumProposal( Acec2_Man_t * m, Acec2_Record_t * r )
{
    Acec2_Word_t * w; Acec2_Product_t * p; Acec2_Record_t * child;
    int i, j, side, lit, id, width = 0, extra, count;
    if ( !r->vFactors || r->FactorWidth != r->Width || !r->vResidual || Vec_WecSize(r->vResidual) ) return NULL;
    count = Vec_PtrSize(r->vFactors); if ( count < 2 || count > 8 ) return NULL;
    w = ABC_CALLOC(Acec2_Word_t, 1); w->Tree = w->Record = -1; w->fIndependent = 1;
    w->vTerms = Vec_IntAlloc(64); w->vConstants = Vec_IntAlloc(8); w->vSumProducts = Vec_IntAlloc(3*count);
    w->vSourceCut = Vec_IntAlloc(32);
    Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, p, i)
    {
        if ( p->Shift < 0 || p->Shift > m->Pars.nMaxWidth || Acec2_Stopped(m) ) goto fail;
        id = Acec2_RecordFullProduct(m, p); if ( id < 0 ) goto fail;
        child = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, id);
        width = Abc_MaxInt(width, child->Width+p->Shift);
        Vec_IntPushTwo(w->vSumProducts, id, p->Shift); Vec_IntPush(w->vSumProducts, p->fNeg);
        for ( side = 0; side < 2; side++ )
            Vec_IntForEachEntry(p->vOperands[side], lit, j) if ( lit >= 2 ) Vec_IntPush(w->vSourceCut, lit & ~1);
    }
    for ( extra = 0; (1 << extra) < count; extra++ ) {}
    w->Width = Abc_MinInt(width+extra, m->Pars.nMaxWidth);
    if ( w->Width > 512 ) goto fail;
    qsort(Vec_IntArray(w->vSumProducts), count, 3*sizeof(int), Acec2_RecordSumCompare);
    Vec_IntUniqify(w->vSourceCut);
    return w;
fail:
    Acec2_WordFree(w); return NULL;
}

/**Function*************************************************************

  Synopsis    [Closes sums of certified products through the source final adder.]

  Description [Proposals are deduplicated before proof and retain the
  strongest known prefix. Every additional bit is checked over the product
  output cut; the common record checker then composes the exact expression.]

  SideEffects [Stores complete proofs and explicit dependencies.]

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordSumWords( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vSelected, int * pnQueries )
{
    Hsh_VecMan_t * seen = Hsh_VecManStart(16);
    Vec_Ptr_t * candidates = Vec_PtrAlloc(16);
    Vec_Int_t * prefixes = Vec_IntAlloc(16);
    Acec2_Record_t * r; Acec2_Word_t * w;
    int i, id, before, word, count = Vec_PtrSize(m->vRecords);
    if ( !m->Pars.fAlgebra ) goto finish;
    for ( i = 0; i < count && !Acec2_Stopped(m); i++ )
    {
        if ( vSelected && (i >= Vec_IntSize(vSelected) || !Vec_IntEntry(vSelected, i)) ) continue;
        r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, i);
        w = Acec2_RecordSumProposal(m, r); if ( !w ) continue;
        before = Hsh_VecSize(seen); id = Hsh_VecManAdd(seen, w->vSumProducts);
        if ( id == before ) { Vec_PtrPush(candidates, w); Vec_IntPush(prefixes, r->Prefix); }
        else { Vec_IntWriteEntry(prefixes, id, Abc_MaxInt(Vec_IntEntry(prefixes, id), r->Prefix)); Acec2_WordFree(w); }
    }
    Vec_PtrForEachEntry(Acec2_Word_t *, candidates, w, i)
    {
        if ( Acec2_Stopped(m) ) break;
        if ( Vec_IntEntry(prefixes, i) >= w->Width ) continue;
        if ( m->nSumAttempts >= 8 ) { m->nSumLimits++; break; }
        if ( pnQueries ) { if ( *pnQueries <= 0 ) break; (*pnQueries)--; }
        m->nSumAttempts++;
        if ( !Acec2_RecordSumTerms(m, w, w->vTerms, w->vConstants) ||
             !Acec2_CertifyLinearWord(m, w, Abc_MaxInt(4, Vec_IntEntry(prefixes, i)+1)) ) continue;
        word = Vec_PtrSize(m->vWords); Vec_PtrPush(m->vWords, w);
        r = Acec2_RecordWord(m, word, -1);
        if ( !r ) { Vec_PtrPop(m->vWords); continue; }
        Acec2_RecordFactorPopulate(m, r, vMap); Vec_PtrPush(m->vRecords, r);
        Vec_PtrWriteEntry(candidates, i, NULL); m->nSumWords++;
    }
finish:
    Vec_PtrForEachEntry(Acec2_Word_t *, candidates, w, i) Acec2_WordFree(w);
    Vec_PtrFree(candidates); Vec_IntFree(prefixes); Hsh_VecManStop(seen);
}

/**Function*************************************************************

  Synopsis    [Adds an exact source operand description to a stable proposal queue.]

  Description [Operand phases and sign modes belong to the key. Shift belongs
  to the consuming expression, not to the unshifted source product proposal.]

  SideEffects [Copies only new proposals; the caller retains the input.]

  SeeAlso     []

***********************************************************************/
static void Acec2_SourceProductAdd( Acec2_Man_t * m, int Tree, Acec2_Product_t * product )
{
    Acec2_Product_t * copy;
    Vec_Int_t * key, * queue = Vec_WecEntry(m->vSourceProductIds, Tree);
    int side, id, i, fullQueue, fullStore;
    if ( product->fNeg ) return;
    for ( side = 0; side < 2; side++ )
        if ( Vec_IntSize(product->vOperands[side]) < 2 || Vec_IntSize(product->vOperands[side]) > 256 ) return;
    key = Vec_IntAlloc(32);
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntPushTwo(key, product->fSigned[side], Vec_IntSize(product->vOperands[side]));
        Vec_IntAppend(key, product->vOperands[side]);
    }
    fullQueue = Vec_IntSize(queue) >= 128;
    fullStore = Vec_PtrSize(m->vSourceProducts) >= 4096;
    if ( fullQueue || fullStore )
    {
        // At capacity, a known proposal remains usable and is not a limit.
        // This bounded scan avoids inserting rejected keys into the hash.
        for ( i = 0; i < (fullQueue ? Vec_IntSize(queue) : Hsh_VecSize(m->hSourceProducts)); i++ )
        {
            id = fullQueue ? Vec_IntEntry(queue, i) : i;
            if ( !Vec_IntEqual(key, Hsh_VecReadEntry(m->hSourceProducts, id)) ) continue;
            if ( !fullQueue ) Vec_IntPushUnique(queue, id);
            Vec_IntFree(key); return;
        }
        m->nProductLimits++; Vec_IntFree(key); return;
    }
    id = Hsh_VecManAdd(m->hSourceProducts, key); Vec_IntFree(key);
    if ( id == Vec_PtrSize(m->vSourceProducts) )
    {
        copy = ABC_CALLOC(Acec2_Product_t, 1);
        for ( side = 0; side < 2; side++ )
        { copy->vOperands[side] = Vec_IntDup(product->vOperands[side]); copy->fSigned[side] = product->fSigned[side]; }
        Vec_PtrPush(m->vSourceProducts, copy);
    }
    Vec_IntPushUnique(queue, id);
}

/**Function*************************************************************

  Synopsis    [Queues independent operands from a region and its joined records.]

  Description [A reconstruction partition is not the only arithmetic view.
  Checked record factors and record-based proposals can expose a larger
  product. New proposals append to a stable exact-key queue, so a saved
  cursor cannot skip operands inserted by later record enrichment.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_SourceProductsCollect( Acec2_Man_t * m, int Tree )
{
    Vec_Int_t * selected = Acec2_RegionRecords(m, Tree), * map = NULL;
    Vec_Ptr_t * products;
    Acec2_Record_t * r;
    Acec2_Product_t * product;
    int i, j, owned;
    if ( !m->hSourceProducts )
    {
        m->hSourceProducts = Hsh_VecManStart(100); m->vSourceProducts = Vec_PtrAlloc(100);
        m->vSourceProductIds = Vec_WecStart(Vec_WecSize(m->vTrees));
    }
    for ( i = 0; i <= Vec_IntSize(selected) && !Acec2_Stopped(m); i++ )
    {
        if ( i < Vec_IntSize(selected) && !Vec_IntEntry(selected, i) ) continue;
        r = i < Vec_IntSize(selected) ? (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, i) : NULL;
        products = r ? r->vFactors : NULL; owned = products == NULL;
        if ( !products )
        {
            if ( r && !map ) map = Vec_IntStart(Gia_ManObjNum(m->pGia));
            products = r ? Acec2_RecordProductProposals(m, r, map) : Acec2_RegionProductProposals(m, Tree);
        }
        if ( !products ) continue;
        Vec_PtrForEachEntry(Acec2_Product_t *, products, product, j)
        {
            Acec2_SourceProductAdd(m, Tree, product);
            if ( owned ) { Vec_IntFree(product->vOperands[0]); Vec_IntFree(product->vOperands[1]); ABC_FREE(product); }
        }
        if ( owned ) Vec_PtrFree(products);
    }
    Vec_IntFree(selected); Vec_IntFreeP(&map);
}

/**Function*************************************************************

  Synopsis    [Reads the product prefix already supplied by checked records.]

  Description [A shifted region extended by its observed low AND can prove
  the full product without a separate word SAT query. Only exact factors
  with no residual contribute, at the smaller certified binary modulus.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_SourceProductPrefix( Acec2_Man_t * m, Acec2_Product_t * product )
{
    Acec2_Record_t * r; Acec2_Product_t * factor;
    int i, side, prefix = 0;
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        if ( (i & 63) == 0 && Acec2_Stopped(m) ) break;
        if ( !r->vFactors || Vec_PtrSize(r->vFactors) != 1 || !r->vResidual ||
             Vec_WecSize(r->vResidual) || r->FactorWidth <= prefix || r->Prefix <= prefix ) continue;
        factor = (Acec2_Product_t *)Vec_PtrEntry(r->vFactors, 0);
        if ( factor->Shift || factor->fNeg ) continue;
        for ( side = 0; side < 2; side++ )
            if ( factor->fSigned[side] != product->fSigned[side] ||
                 !Vec_IntEqual(factor->vOperands[side], product->vOperands[side]) ) break;
        if ( side == 2 ) prefix = Abc_MaxInt(prefix, Abc_MinInt(r->Prefix, r->FactorWidth));
    }
    return prefix;
}

/**Function*************************************************************

  Synopsis    [Certifies requested source products without cross-design assumptions.]

  Description [Completed product words consume no new query. Increased
  effort retries unfinished proposals while new records append new operands.]

  SideEffects [Consumes queries and stores completed source records.]

  SeeAlso     []

***********************************************************************/
static int Acec2_EnrichProductRegion( Acec2_Man_t * m, int Tree, int * pnQueries )
{
    Vec_Int_t * queue;
    Acec2_Product_t * product;
    Acec2_Word_t * w, * previous;
    int i, j, side, prefix, width, added = 0, tier, attempts, scanned = 0;
    if ( !m || !pnQueries || *pnQueries <= 0 || !m->Pars.fAlgebra ||
         Tree < 0 || Tree >= Vec_WecSize(m->vTrees) || Acec2_Stopped(m) ) return 0;
    Tree = Acec2_RegionClass(m, Tree);
    tier = m->Pars.nCecPolyLimit > 0 ? m->Pars.nCecPolyLimit : ABC_INT_MAX;
    if ( !m->vProductProgress ) m->vProductProgress = Vec_IntStart(2*Vec_WecSize(m->vTrees));
    Acec2_SourceProductsCollect(m, Tree); queue = Vec_WecEntry(m->vSourceProductIds, Tree);
    // Finish a traversal before revisiting earlier effort-limited proposals.
    if ( Vec_IntEntry(m->vProductProgress, 2*Tree) != tier &&
         (!Vec_IntEntry(m->vProductProgress, 2*Tree+1) || Vec_IntEntry(m->vProductProgress, 2*Tree+1) >= Vec_IntSize(queue)) )
    { Vec_IntWriteEntry(m->vProductProgress, 2*Tree, tier); Vec_IntWriteEntry(m->vProductProgress, 2*Tree+1, 0); }
    for ( i = Vec_IntEntry(m->vProductProgress, 2*Tree+1); i < Vec_IntSize(queue) && *pnQueries > 0 && !Acec2_Stopped(m); i++ )
    {
        // Cache lookups do not consume a proof query, but keep discovery
        // bounded when many completed proposals are already in the queue.
        if ( scanned++ == 8 ) break;
        product = (Acec2_Product_t *)Vec_PtrEntry(m->vSourceProducts, Vec_IntEntry(queue, i));
        prefix = Acec2_SourceProductPrefix(m, product);
        Vec_PtrForEachEntry(Acec2_Word_t *, m->vWords, previous, j)
        {
            if ( !previous->pProduct ) continue;
            for ( side = 0; side < 2; side++ )
                if ( previous->pProduct->fSigned[side] != product->fSigned[side] ||
                     !Vec_IntEqual(previous->pProduct->vOperands[side], product->vOperands[side]) ) break;
            if ( side == 2 ) prefix = Abc_MaxInt(prefix, previous->Width);
        }
        width = Abc_MinInt(m->Pars.nMaxWidth, Vec_IntSize(product->vOperands[0])+Vec_IntSize(product->vOperands[1]));
        if ( prefix >= width ) { Vec_IntWriteEntry(m->vProductProgress, 2*Tree+1, i+1); continue; }
        attempts = m->nCertificateAttempts;
        w = Acec2_CertifyProductWord(m, product, prefix);
        if ( m->nCertificateAttempts != attempts ) (*pnQueries)--;
        if ( Acec2_Stopped(m) ) { Acec2_WordFree(w); break; }
        Vec_IntWriteEntry(m->vProductProgress, 2*Tree+1, i+1);
        if ( !w ) continue;
        added += Acec2_RecordAddProductWord(m, w, Tree);
    }
    return added;
}

/**Function*************************************************************

  Synopsis    [Advances the recognition grouping over newly checked records.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RegionClass( Acec2_Man_t * m, int Tree )
{
    Acec2_Record_t * r; int i, tree, root, first, count = m->vRecords ? Vec_PtrSize(m->vRecords) : 0;
    if ( !m->vRegionClasses )
    {
        m->vRegionClasses = Vec_IntAlloc(Vec_WecSize(m->vTrees));
        for ( i = 0; i < Vec_WecSize(m->vTrees); i++ ) Vec_IntPush(m->vRegionClasses, i);
    }
    for ( ; m->iRegionClassRecord < count && !Acec2_Stopped(m); m->iRegionClassRecord++ )
    {
        r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, m->iRegionClassRecord);
        if ( !r->vParts ) continue;
        first = -1;
        for ( i = 0; i < Vec_IntSize(r->vParts); i += 4 )
        {
            if ( Vec_IntEntry(r->vParts, i) != 0 ) continue;
            tree = Acec2_Cell(m, Vec_IntEntry(r->vParts, i+1))->Tree;
            if ( tree < 0 ) continue;
            root = Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, tree);
            if ( first < 0 ) first = root;
            else
            {
                first = Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, first);
                Vec_IntWriteEntry(m->vRegionClasses, Abc_MaxInt(first, root), Abc_MinInt(first, root));
                first = Abc_MinInt(first, root);
            }
        }
    }
    return Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, Tree);
}

/**Function*************************************************************

  Synopsis    [Selects a component's records and their dependent compositions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_RegionRecords( Acec2_Man_t * m, int Tree )
{
    Acec2_Record_t * r; Acec2_Word_t * w;
    Vec_Int_t * selected = Vec_IntStart(Vec_PtrSize(m->vRecords));
    int i, j, id, belongs;
    Tree = Acec2_RegionClass(m, Tree);
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        belongs = (r->Tree >= 0 && Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, r->Tree) == Tree) ||
                  (r->Discovery > 0 && Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, r->Discovery-1) == Tree);
        if ( r->Word >= 0 )
        { w = (Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word); belongs |= w->Tree >= 0 && Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, w->Tree) == Tree; }
        if ( r->vParts )
            for ( j = 0; j < Vec_IntSize(r->vParts); j += 4 )
                if ( Vec_IntEntry(r->vParts, j) == 0 )
                {
                    id = Acec2_Cell(m, Vec_IntEntry(r->vParts, j+1))->Tree;
                    belongs |= id >= 0 && Acec2_WeightFind(Vec_IntArray(m->vRegionClasses), NULL, NULL, id) == Tree;
                }
        Vec_IntForEachEntry(r->vDependencies, id, j)
            if ( id >= 0 && id < i ) belongs |= Vec_IntEntry(selected, id);
        Vec_IntWriteEntry(selected, i, belongs);
    }
    return selected;
}

/**Function*************************************************************

  Synopsis    [Rotates record closure, linear-word discovery and gap closure.]

  Description [A difficult early record cannot hide later records or the
  independent source cut. Word and gap actions keep separate record cursors
  so alternating actions cannot partition the records between them. Each
  traversal has a fixed end: newly appended records cannot prevent another
  attempt on an older record. Shared work counts keep overlapping regions
  from favoring the same first record. A request spends at most one proposal from
  the shared budget; completed actions leave that budget available.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_EnrichWords( Acec2_Man_t * m, int Tree, Vec_Int_t * vSelected, int * pnQueries )
{
    Vec_Int_t * queue; Vec_Wrd_t * order; word key;
    int count = Vec_IntSize(vSelected), start, action, attempt, i, id, before, cursor, index;
    int group = Acec2_RegionClass(m, Tree);
    if ( count > ABC_INT_MAX/2 ) { m->nRecordLimits++; return; }
    if ( !m->vRegionWord ) m->vRegionWord = Vec_IntStart(3*Vec_WecSize(m->vTrees));
    if ( !m->vRegionWordQueues ) m->vRegionWordQueues = Vec_WecStart(2*Vec_WecSize(m->vTrees));
    if ( !m->vRecordWork ) m->vRecordWork = Vec_IntAlloc(2*count);
    Vec_IntFillExtra(m->vRecordWork, 2*count, 0);
    start = Vec_IntEntry(m->vRegionWord, 3*group+2);
    for ( attempt = 0; attempt < 3 && *pnQueries > 0 && !Acec2_Stopped(m); attempt++ )
    {
        action = (start+attempt) % 3;
        Vec_IntWriteEntry(m->vRegionWord, 3*group+2, (action+1) % 3);
        if ( action == 1 ) Acec2_DiscoverLinearRegion(m, Tree, pnQueries);
        else if ( count )
        {
            cursor = 3*group+action/2; queue = Vec_WecEntry(m->vRegionWordQueues, 2*group+action/2);
            if ( !Vec_IntSize(queue) )
            {
                // Joined records can belong to many requested regions.
                // Give less-served records priority when starting a batch,
                // using shared work counts rather than a separate history
                // for every overlapping region. This changes discovery only.
                order = Vec_WrdAlloc(count);
                for ( i = 0; i < count && !Acec2_Stopped(m); i++ )
                    if ( Vec_IntEntry(vSelected, i) )
                        Vec_WrdPush(order, ((word)(unsigned)Vec_IntEntry(m->vRecordWork, 2*i+action/2) << 32) | (unsigned)i);
                if ( Vec_WrdSize(order) > 1 ) Vec_WrdSort(order, 0);
                Vec_WrdForEachEntry(order, key, i) Vec_IntPush(queue, (int)(unsigned)key);
                Vec_WrdFree(order); Vec_IntWriteEntry(m->vRegionWord, cursor, 0);
            }
            index = Vec_IntEntry(m->vRegionWord, cursor);
            for ( ; index < Vec_IntSize(queue) && *pnQueries > 0 && !Acec2_Stopped(m); index++ )
            {
                id = Vec_IntEntry(queue, index);
                if ( id >= count || !Vec_IntEntry(vSelected, id) ) continue;
                before = *pnQueries;
                if ( action ) Acec2_CloseRecordGaps(m, id, pnQueries);
                else Acec2_CloseRecordWord(m, id, pnQueries);
                if ( before == *pnQueries ) continue;
                i = 2*id+action/2;
                if ( Vec_IntEntry(m->vRecordWork, i) < ABC_INT_MAX ) Vec_IntAddToEntry(m->vRecordWork, i, 1);
                index++;
                break;
            }
            Vec_IntWriteEntry(m->vRegionWord, cursor, index);
            if ( index == Vec_IntSize(queue) ) Vec_IntClear(queue);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Advances one region through the shared recognition stages.]

  Description [Requests add independently checked source records without
  changing existing cell IDs, region weights, or certificates. Word and
  product proofs retain their progress. The query budget bounds proposals;
  each proposal also obeys the manager's effort limits and cancellation.]

  SideEffects [Appends records and updates per-stage work counters.]

  SeeAlso     []

***********************************************************************/
int Acec2_EnrichRegion( Acec2_Man_t * m, int Tree, int Level, int * pnQueries )
{
    Vec_Int_t * selected, * map = NULL;
    Acec2_Record_t * r;
    abctime clk;
    int i, before, count, actions, start, attempt, action, query, group;
    if ( !m || !pnQueries || *pnQueries <= 0 || Tree < 0 || Tree >= Vec_WecSize(m->vTrees) ||
         Level < 0 || Level > 3 || Acec2_Stopped(m) ) return 0;
    clk = Abc_Clock(); Acec2_BuildRecordsBasic(m); before = Vec_PtrSize(m->vRecords);
    m->nStageRequests[Level]++;
    if ( !m->vRegionRequests ) m->vRegionRequests = Vec_IntStart(Vec_WecSize(m->vTrees));
    if ( !m->vRegionStage ) m->vRegionStage = Vec_IntStart(Vec_WecSize(m->vTrees));
    Vec_IntWriteEntry(m->vRegionRequests, Tree, Abc_MaxInt(Level, Vec_IntEntry(m->vRegionRequests, Tree)));
    selected = Acec2_RegionRecords(m, Tree);
    group = Acec2_RegionClass(m, Tree);
    if ( Level >= 2 )
    {
        Acec2_FindExpression(m, Tree);
        map = Vec_IntStart(Gia_ManObjNum(m->pGia));
        for ( i = 0; i < Vec_IntSize(selected) && !Acec2_Stopped(m); i++ )
            if ( Vec_IntEntry(selected, i) )
            { r = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, i); Acec2_RecordFactorPopulate(m, r, map); }
        Acec2_RecordExtendProducts(m, map, selected);
    }
    actions = Level == 3 ? 4 : Level;
    start = actions ? Vec_IntEntry(m->vRegionStage, group) % actions : 0;
    // One difficult word must not consume every request before products or
    // compositions are considered. Rotate the requested actions, each with
    // at most one query, and debit only actual attempts from the shared budget.
    for ( attempt = 0; attempt < actions && *pnQueries > 0 && !Acec2_Stopped(m); attempt++ )
    {
        action = (start+attempt) % actions; query = 1;
        Vec_IntWriteEntry(m->vRegionStage, group, (action+1) % actions);
        m->nStageActions[action]++;
        Vec_IntFree(selected); selected = Acec2_RegionRecords(m, Tree);
        if ( action == 0 ) Acec2_EnrichWords(m, Tree, selected, &query);
        else if ( action == 1 ) Acec2_EnrichProductRegion(m, Tree, &query);
        else if ( action == 2 ) Acec2_RecordComposeProducts(m, map, 0, selected, &query);
        else Acec2_RecordSumWords(m, map, selected, &query);
        assert(query >= 0 && query <= 1);
        *pnQueries -= 1-query; m->nStageQueries[action] += 1-query;
    }
    Vec_IntFree(selected); Vec_IntFreeP(&map);
    count = Vec_PtrSize(m->vRecords)-before; m->nStageRecords[Level] += count;
    clk = Abc_Clock()-clk; m->TimeRecords += clk; m->Time += clk;
    return count;
}

/**Function*************************************************************

  Synopsis    [Returns the two operand bits of an extendible product prefix.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordExtensionInputs( Acec2_Record_t * r, int * a, int * b )
{
    Acec2_Product_t * p;
    if ( r->vOutputMasks || !r->vFactors || Vec_PtrSize(r->vFactors) != 1 || r->FactorWidth != r->Width ) return 0;
    p = (Acec2_Product_t *)Vec_PtrEntry(r->vFactors, 0);
    if ( p->Shift != -1 || p->fNeg ) return 0;
    *a = Vec_IntEntry(p->vOperands[0], 0); *b = Vec_IntEntry(p->vOperands[1], 0);
    if ( *a > *b ) ABC_SWAP(int, *a, *b);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Includes an observed low partial product outside the adder tree.]

  Description [Only requested operand pairs are indexed. One source pass
  finds their gates, so many product records do not rescan the whole design.
  The original shifted records remain available as separate certificates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordExtendProducts( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vSelected )
{
    Vec_Wrd_t * keys = Vec_WrdAlloc(16); Vec_Int_t * literals;
    Acec2_Record_t * parent, * r; Gia_Obj_t * o; word key, * found;
    int i, j, k, a, b, lit, count = Vec_PtrSize(m->vRecords);
    if ( !m->vExtended ) m->vExtended = Vec_IntAlloc(100);
    Vec_IntFillExtra(m->vExtended, count, 0);
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, parent, i)
        if ( (!vSelected || (i < Vec_IntSize(vSelected) && Vec_IntEntry(vSelected, i))) &&
             !Vec_IntEntry(m->vExtended, i) && parent->Width < m->Pars.nMaxWidth &&
             Acec2_RecordExtensionInputs(parent, &a, &b) && a >= 2 && a != b && a != (b ^ 1) )
            Vec_WrdPush(keys, ((word)(unsigned)a << 32) | (unsigned)b);
    Vec_WrdUniqify(keys); literals = Vec_IntStartFull(Vec_WrdSize(keys));
    if ( Vec_WrdSize(keys) )
    {
        Gia_ManForEachAnd(m->pGia, o, i)
        {
            if ( (i & 1023) == 0 && Acec2_Stopped(m) ) break;
            if ( Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) continue;
            a = Gia_ObjFaninLit0p(m->pGia, o); b = Gia_ObjFaninLit1p(m->pGia, o);
            if ( a > b ) ABC_SWAP(int, a, b);
            key = ((word)(unsigned)a << 32) | (unsigned)b;
            found = (word *)bsearch(&key, Vec_WrdArray(keys), Vec_WrdSize(keys), sizeof(word), (int (*)(const void *, const void *))Vec_WrdSortCompare1);
            if ( found && Vec_IntEntry(literals, (int)(found-Vec_WrdArray(keys))) < 0 ) Vec_IntWriteEntry(literals, (int)(found-Vec_WrdArray(keys)), 2*i);
        }
    }
    for ( i = 0; i < count && !Acec2_Stopped(m); i++ )
    {
        if ( vSelected && (i >= Vec_IntSize(vSelected) || !Vec_IntEntry(vSelected, i)) ) continue;
        parent = (Acec2_Record_t *)Vec_PtrEntry(m->vRecords, i);
        if ( Vec_IntEntry(m->vExtended, i) || parent->Width >= m->Pars.nMaxWidth ||
             !Acec2_RecordExtensionInputs(parent, &a, &b) ) continue;
        if ( a == b ) lit = a;
        else if ( a == (b ^ 1) || !a || !b ) lit = 0;
        else if ( a == 1 || b == 1 ) lit = a == 1 ? b : a;
        else
        {
            key = ((word)(unsigned)a << 32) | (unsigned)b;
            found = (word *)bsearch(&key, Vec_WrdArray(keys), Vec_WrdSize(keys), sizeof(word), (int (*)(const void *, const void *))Vec_WrdSortCompare1);
            lit = found ? Vec_IntEntry(literals, (int)(found-Vec_WrdArray(keys))) : -1;
        }
        if ( lit < 0 ) { Vec_IntWriteEntry(m->vExtended, i, -1); continue; }
        r = Acec2_RecordAlloc(parent->Width+1); r->Extend = 1; r->LowLit = lit; r->Prefix = parent->Prefix+1;
        Vec_IntPush(r->vDependencies, i); Vec_IntPushTwo(r->vOutputs, lit, 0); Vec_IntPushTwo(r->vTerms, lit, 0);
        for ( k = 0; k < 2; k++ )
        {
            Vec_Int_t * src = k ? parent->vOutputs : parent->vTerms, * dst = k ? r->vOutputs : r->vTerms;
            for ( j = 0; j < Vec_IntSize(src); j += 2 ) Vec_IntPushTwo(dst, Vec_IntEntry(src, j), Vec_IntEntry(src, j+1)+1);
        }
        Vec_IntForEachEntry(parent->vConstants, a, j) Vec_IntPush(r->vConstants, a+1);
        Vec_IntAppend(r->vCovered, parent->vCovered); Vec_IntAppend(r->vSupport, parent->vSupport);
        if ( Gia_ObjIsAnd(Gia_ManObj(m->pGia, lit >> 1)) ) Vec_IntPush(r->vCovered, lit >> 1);
        Vec_IntPush(r->vSupport, lit >> 1); Vec_IntUniqify(r->vCovered); Vec_IntUniqify(r->vSupport);
        Vec_IntFill(r->vBitStatus, Vec_IntSize(r->vOutputs)/2, 0);
        if ( !Acec2_RecordPopulate(m, r) ) { Acec2_RecordFree(r); continue; }
        Acec2_RecordFactorPopulate(m, r, vMap); Vec_PtrPush(m->vRecords, r);
        Vec_IntWriteEntry(m->vExtended, i, Vec_PtrSize(m->vRecords));
    }
    Vec_IntFree(literals); Vec_WrdFree(keys);
}

/**Function*************************************************************

  Synopsis    [Orders exact monomial keys without process-global state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordKeyCompare( const void * a, const void * b )
{
    const int * x = (const int *)a, * y = (const int *)b; int i;
    for ( i = 0; i < 2; i++ ) if ( x[i] != y[i] ) return x[i] < y[i] ? -1 : 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Orders arbitrary square-free monomials lexicographically.]

  Description [The last entry is an accumulator index, not a variable.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordMonomialCompare( const void * a, const void * b )
{
    Vec_Int_t * x = (Vec_Int_t *)a, * y = (Vec_Int_t *)b; int i;
    for ( i = 0; i < Abc_MinInt(Vec_IntSize(x), Vec_IntSize(y))-1; i++ )
        if ( Vec_IntEntry(x, i) != Vec_IntEntry(y, i) ) return Vec_IntEntry(x, i) < Vec_IntEntry(y, i) ? -1 : 1;
    return (Vec_IntSize(x) > Vec_IntSize(y)) - (Vec_IntSize(x) < Vec_IntSize(y));
}

/**Function*************************************************************

  Synopsis    [Maps exact higher-degree source polynomials through a common cut.]

  Description [Only complemented variables branch. Repeated mapped literals
  are idempotent, and opposite phases annihilate a monomial. Bound expansion
  by deterministic work, without using a truncated result as a matching key.
  Quadratic results retain the existing key format; higher-degree keys use
  a negative term count and explicit monomial lengths.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_RecordKeyGeneral( Acec2_Record_t * r, Vec_Int_t * vMap, int Width, int Flip, int * pLimited )
{
    Acec2_RecordPoly_t * p = Acec2_RecordPolyStart(Width);
    Vec_Int_t * mapped = Vec_IntAlloc(16), * key = NULL, * v, * entry;
    Vec_Wec_t * order = Vec_WecAlloc(32);
    int i, j, k, lit, mask, count, sign, valid, id, alive, degree = 0, work = 0, nWords = (r->Width+63)/64;
    Vec_WecForEachLevel(r->vMonomials, v, i)
    {
        Vec_IntClear(mapped); valid = 1;
        Vec_IntForEachEntry(v, id, j)
        {
            if ( ++work > 200000 ) { if ( pLimited ) *pLimited = 1; goto finish; }
            if ( id < 0 || id >= Vec_IntSize(vMap) || Vec_IntEntry(vMap, id) < 0 ) goto finish;
            lit = Vec_IntEntry(vMap, id);
            if ( !lit ) { valid = 0; break; }
            if ( lit > 1 ) Vec_IntPush(mapped, lit);
        }
        if ( !valid ) continue;
        Vec_IntUniqify(mapped); count = 0;
        Vec_IntForEachEntry(mapped, lit, j)
        {
            if ( j && (lit ^ Vec_IntEntry(mapped, j-1)) == 1 ) { valid = 0; break; }
            count += lit & 1;
        }
        if ( !valid ) continue;
        if ( count > 16 || (1 << count) > 200000-work ) { if ( pLimited ) *pLimited = 1; goto finish; }
        for ( mask = 0; mask < (1 << count); mask++ )
        {
            Vec_IntClear(p->vMono); sign = Flip ? -1 : 1; k = 0;
            Vec_IntForEachEntry(mapped, lit, j)
            {
                if ( ++work > 200000 ) { if ( pLimited ) *pLimited = 1; goto finish; }
                if ( !(lit & 1) ) Vec_IntPush(p->vMono, lit >> 1);
                else if ( (mask >> k++) & 1 ) { Vec_IntPush(p->vMono, lit >> 1); sign = -sign; }
            }
            Acec2_RecordCoefficient(p, Vec_WrdEntryP(r->vCoefficients, i*nWords), sign);
        }
    }
    if ( Flip ) for ( i = 0; i < Width; i++ ) Acec2_RecordPower(p, -1, -1, i, 1);
    for ( i = 0; i < Hsh_VecSize(p->h); i++ )
    {
        alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(p->h, i); degree = Abc_MaxInt(degree, Vec_IntSize(v));
        entry = Vec_WecPushLevel(order); Vec_IntAppend(entry, v); Vec_IntPush(entry, i);
    }
    if ( Vec_WecSize(order) > 1 ) qsort(Vec_WecArray(order), Vec_WecSize(order), sizeof(Vec_Int_t), Acec2_RecordMonomialCompare);
    key = Vec_IntAlloc(64); Vec_IntPushTwo(key, Width, degree <= 2 ? Vec_WecSize(order) : -Vec_WecSize(order));
    Vec_WecForEachLevel(order, v, i)
    {
        id = Vec_IntEntryLast(v); count = Vec_IntSize(v)-1;
        if ( degree <= 2 ) Vec_IntPushTwo(key, count ? Vec_IntEntry(v, 0) : -1, count > 1 ? Vec_IntEntry(v, 1) : -1);
        else { Vec_IntPush(key, count); for ( j = 0; j < count; j++ ) Vec_IntPush(key, Vec_IntEntry(v, j)); }
        for ( k = 0; k < p->nWords; k++ )
        {
            word value = Vec_WrdEntry(p->vCoefs, id*p->nWords+k);
            Vec_IntPushTwo(key, (int)(unsigned)value, (int)(unsigned)(value >> 32));
        }
    }
finish:
    Vec_IntFree(mapped); Vec_WecFree(order); Acec2_RecordPolyStop(p); return key;
}

/**Function*************************************************************

  Synopsis    [Maps a checked polynomial through already proved cut signals.]

  Description [Complements, constants and repeated variables are expanded
  exactly. The complete modular coefficients, not a fingerprint, form the
  matching key. Flipping a binary prefix complements its whole word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Acec2_RecordKey( Acec2_Record_t * r, Vec_Int_t * vMap, Vec_Int_t * vFrontier, int Width, int Flip, int * pLimited )
{
    Acec2_RecordPoly_t * p;
    Vec_Int_t * v, * key = NULL, * order;
    int i, j, k, lit, mapped[2], mask, sign, valid, id, alive, general = 0, nWords = (r->Width+63)/64;
    if ( pLimited ) *pLimited = 0;
    if ( Width < 1 || Width > r->Width ) return NULL;
    Vec_IntForEachEntry(r->vCut, lit, i)
    {
        lit = Vec_IntEntry(vMap, lit >> 1);
        if ( lit < 0 || (vFrontier && ((lit >> 1) >= Vec_IntSize(vFrontier) || !Vec_IntEntry(vFrontier, lit >> 1))) ) return NULL;
    }
    p = Acec2_RecordPolyStart(Width); order = Vec_IntAlloc(3*Vec_WecSize(r->vMonomials));
    Vec_WecForEachLevel(r->vMonomials, v, i)
    {
        if ( Vec_IntSize(v) > 2 ) { general = 1; goto finish; }
        for ( j = 0; j < Vec_IntSize(v); j++ ) mapped[j] = Vec_IntEntry(vMap, Vec_IntEntry(v, j));
        for ( mask = 0; mask < (1 << Vec_IntSize(v)); mask++ )
        {
            Vec_IntClear(p->vMono); sign = Flip ? -1 : 1; valid = 1;
            for ( j = 0; j < Vec_IntSize(v); j++ )
                if ( (mask >> j) & 1 )
                {
                    if ( !(mapped[j] >> 1) ) { valid = 0; break; }
                    Vec_IntPushUniqueOrder(p->vMono, mapped[j] >> 1);
                    if ( mapped[j] & 1 ) sign = -sign;
                }
                else if ( !(mapped[j] & 1) ) { valid = 0; break; }
            if ( valid ) Acec2_RecordCoefficient(p, Vec_WrdEntryP(r->vCoefficients, i*nWords), sign);
        }
    }
    if ( Flip ) for ( i = 0; i < Width; i++ ) Acec2_RecordPower(p, -1, -1, i, 1);
    for ( i = 0; i < Hsh_VecSize(p->h); i++ )
    {
        alive = 0;
        for ( j = 0; j < p->nWords; j++ ) alive |= Vec_WrdEntry(p->vCoefs, i*p->nWords+j) != 0;
        if ( !alive ) continue;
        v = Hsh_VecReadEntry(p->h, i);
        Vec_IntPushThree(order, Vec_IntSize(v) ? Vec_IntEntry(v, 0) : -1, Vec_IntSize(v) > 1 ? Vec_IntEntry(v, 1) : -1, i);
    }
    if ( Vec_IntSize(order) > 3 ) qsort(Vec_IntArray(order), Vec_IntSize(order)/3, 3*sizeof(int), Acec2_RecordKeyCompare);
    key = Vec_IntAlloc(Vec_IntSize(order)*3); Vec_IntPushTwo(key, Width, Vec_IntSize(order)/3);
    for ( i = 0; i < Vec_IntSize(order); i += 3 )
    {
        Vec_IntPushTwo(key, Vec_IntEntry(order, i), Vec_IntEntry(order, i+1)); id = Vec_IntEntry(order, i+2);
        for ( k = 0; k < p->nWords; k++ )
        {
            word value = Vec_WrdEntry(p->vCoefs, id*p->nWords+k);
            Vec_IntPushTwo(key, (int)(unsigned)value, (int)(unsigned)(value >> 32));
        }
    }
finish:
    Vec_IntFree(order); Acec2_RecordPolyStop(p);
    return general ? Acec2_RecordKeyGeneral(r, vMap, Width, Flip, pLimited) : key;
}

/**Function*************************************************************

  Synopsis    [Canonicalizes the top constant through the output-bit phase.]

  Description [For a binary W-bit word, toggling its highest bit adds
  2^(W-1) modulo 2^W. Remove this constant from the matching key and return
  its explicit phase flag. This permits signed correction conventions to
  match without changing any stored source certificate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordKeyTop( Vec_Int_t * key, int Width )
{
    int general = Vec_IntEntry(key, 1) < 0, first = general ? 3 : 4;
    int i, step = first-2+2*((Width+63)/64), index = first+(Width-1)/32, alive = 0;
    unsigned mask = 1u << ((Width-1) & 31);
    if ( !Vec_IntEntry(key, 1) || (general ? Vec_IntEntry(key, 2) != 0 : Vec_IntEntry(key, 2) != -1 || Vec_IntEntry(key, 3) != -1) ) return 0;
    if ( !((unsigned)Vec_IntEntry(key, index) & mask) ) return 0;
    Vec_IntWriteEntry(key, index, (int)((unsigned)Vec_IntEntry(key, index) ^ mask));
    for ( i = first; i < 2+step; i++ ) alive |= Vec_IntEntry(key, i) != 0;
    if ( !alive )
    {
        for ( i = 2+step; i < Vec_IntSize(key); i++ ) Vec_IntWriteEntry(key, i-step, Vec_IntEntry(key, i));
        Vec_IntShrink(key, Vec_IntSize(key)-step); Vec_IntAddToEntry(key, 1, general ? 1 : -1);
    }
    return 2;
}

/**Function*************************************************************

  Synopsis    [Installs bit equalities implied by two checked binary records.]

  Description [Equal weighted sums imply equal bits only in their common
  binary prefix. Missing boundary positions denote zero, explicitly.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordAliases( Acec2_Record_t ** r, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces, int Width, int Flip )
{
    Vec_Int_t * bits[2] = {Vec_IntStart(Width), Vec_IntStart(Width)};
    Vec_Int_t * masks[2] = {Vec_IntStart(Width), Vec_IntStart(Width)};
    int side, i, rank, source[2], mapped[2], mask[2], target, lit, phase, result = 0;
    for ( side = 0; side < 2; side++ )
        for ( i = 0; i < Vec_IntSize(r[side]->vOutputs); i += 2 )
        {
            rank = Vec_IntEntry(r[side]->vOutputs, i+1);
            if ( rank < Width )
            {
                Vec_IntWriteEntry(bits[side], rank, Vec_IntEntry(r[side]->vOutputs, i));
                if ( r[side]->vOutputMasks ) Vec_IntWriteEntry(masks[side], rank, Vec_IntEntry(r[side]->vOutputMasks, i/2));
            }
        }
    for ( i = 0; i < Width; i++ )
    {
        phase = (Flip & 1) ^ ((Flip >> 1) && i == Width-1);
        for ( side = 0; side < 2; side++ )
        {
            lit = Vec_IntEntry(masks[side], i);
            mask[side] = Vec_IntEntry(vMaps[side], lit >> 1) ^ (lit & 1);
        }
        // Equal decoded words imply equal observed bits when their masks
        // already correspond. Opposite mask phases invert the observed bit.
        // An unmatched mask stays in the surrounding Boolean problem.
        if ( (mask[0] >> 1) != (mask[1] >> 1) ) continue;
        phase ^= (mask[0] ^ mask[1]) & 1;
        for ( side = 0; side < 2; side++ )
        {
            source[side] = Vec_IntEntry(bits[side], i);
            mapped[side] = Vec_IntEntry(vMaps[side], source[side] >> 1) ^ (source[side] & 1) ^ (side ? 0 : phase);
        }
        if ( mapped[0] == mapped[1] ) continue;
        if ( (mapped[0] >> 1) == (mapped[1] >> 1) )
        {
            Abc_Print(-1, "&acec2: contradictory checked component identities at bit %d.\n", i); result = -2; break;
        }
        target = Abc_MinInt(mapped[0], mapped[1]);
        for ( side = 0; side < 2; side++ )
        {
            if ( source[side] < 2 || mapped[side] == target ) continue;
            lit = target ^ (source[side] & 1) ^ (side ? 0 : phase);
            if ( Vec_IntEntry(vReplaces[side], source[side] >> 1) == lit ) continue;
            Vec_IntWriteEntry(vReplaces[side], source[side] >> 1, lit); result++;
        }
    }
    Vec_IntFree(bits[0]); Vec_IntFree(bits[1]); Vec_IntFree(masks[0]); Vec_IntFree(masks[1]); return result;
}

/**Function*************************************************************

  Synopsis    [Matches independent certificates over the proved common cut.]

  Description [No arithmetic SAT query or structural template is needed.
  Exact polynomial keys suffice because each source identity was checked
  independently. Ordinary CEC still proves the surrounding Boolean logic.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
struct Acec2_RecordMatch_t_
{
    Acec2_Man_t * pMans[2];
    Hsh_VecMan_t * hKeys;
    Vec_Int_t * vWidths, * vOwners, * vMaps[2], * vFrontier;
    int nRecords[2], iWidth, Side, Record, Flip;
};

/**Function*************************************************************

  Synopsis    [Creates comparison-owned progress for exact record matching.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_RecordMatch_t * Acec2_RecordMatchStart()
{
    return ABC_CALLOC(Acec2_RecordMatch_t, 1);
}

/**Function*************************************************************

  Synopsis    [Discards keys bound to the previous comparison frontier.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordMatchClear( Acec2_RecordMatch_t * q )
{
    if ( q->hKeys ) Hsh_VecManStop(q->hKeys);
    Vec_IntFreeP(&q->vWidths); Vec_IntFreeP(&q->vOwners);
    Vec_IntFreeP(&q->vMaps[0]); Vec_IntFreeP(&q->vMaps[1]); Vec_IntFreeP(&q->vFrontier);
    memset(q, 0, sizeof(*q));
}

/**Function*************************************************************

  Synopsis    [Releases persistent comparison keys and traversal state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RecordMatchStop( Acec2_RecordMatch_t * q )
{
    if ( !q ) return;
    Acec2_RecordMatchClear(q); ABC_FREE(q);
}

/**Function*************************************************************

  Synopsis    [Starts a finite traversal over the current record database.]

  Description [New records wait for the next traversal; they cannot prevent
  completion of a current width. Mappings and frontier are copied exactly.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecordMatchInit( Acec2_RecordMatch_t * q, Acec2_Man_t ** m,
                                  Vec_Int_t ** maps, Vec_Int_t * frontier )
{
    Acec2_Record_t * r; int side, i;
    Acec2_RecordMatchClear(q);
    q->vWidths = Vec_IntAlloc(64); q->vOwners = Vec_IntAlloc(100);
    if ( frontier ) q->vFrontier = Vec_IntDup(frontier);
    for ( side = 0; side < 2; side++ )
    {
        q->pMans[side] = m[side]; q->nRecords[side] = Vec_PtrSize(m[side]->vRecords);
        q->vMaps[side] = Vec_IntDup(maps[side]);
        Vec_PtrForEachEntry(Acec2_Record_t *, m[side]->vRecords, r, i)
            if ( r->Prefix >= 2 ) Vec_IntPush(q->vWidths, r->Prefix);
    }
    Vec_IntUniqify(q->vWidths); Vec_IntSort(q->vWidths, 1);
}

/**Function*************************************************************

  Synopsis    [Resumes bounded matching over unchanged proved source mappings.]

  Description [Keys are retained only while both mappings and the optional
  frontier agree exactly. A changed cut restarts the comparison. Otherwise
  effort exhaustion preserves the width, side, record and phase cursors.]

  SideEffects [Commits only equal independently checked polynomial keys.]

  SeeAlso     []

***********************************************************************/
int Acec2_MatchRecordsStep( Acec2_Man_t ** m, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                            Vec_Int_t * vFrontier, Acec2_Par_t * pPars, abctime Deadline,
                            int * pnWords, Acec2_RecordMatch_t * q )
{
    Vec_Int_t * key; Acec2_Record_t * r, * pair[2];
    int side, width, phase, id, found, added, limited, work = 0, result = 0;
    *pnWords = 0;
    if ( !q || !m[0] || !m[1] || Acec2_Stop(pPars, Deadline) ) return 0;
    if ( !q->vWidths || q->pMans[0] != m[0] || q->pMans[1] != m[1] ||
         !Vec_IntEqual(q->vMaps[0], vMaps[0]) || !Vec_IntEqual(q->vMaps[1], vMaps[1]) ||
         (q->vFrontier != NULL) != (vFrontier != NULL) ||
         (vFrontier && !Vec_IntEqual(q->vFrontier, vFrontier)) )
        Acec2_RecordMatchInit(q, m, vMaps, vFrontier);
    while ( q->iWidth < Vec_IntSize(q->vWidths) )
    {
        width = Vec_IntEntry(q->vWidths, q->iWidth);
        if ( !q->hKeys ) { q->hKeys = Hsh_VecManStart(100); Vec_IntClear(q->vOwners); }
        for ( ; q->Side < 2; q->Side++, q->Record = q->Flip = 0 )
            for ( ; q->Record < q->nRecords[q->Side]; q->Record++, q->Flip = 0 )
            {
                side = q->Side; r = (Acec2_Record_t *)Vec_PtrEntry(m[side]->vRecords, q->Record);
                if ( r->Prefix < width ) continue;
                if ( Acec2_Stop(pPars, Deadline) ) goto finish;
                for ( ; q->Flip < (side ? 1 : 2); q->Flip++ )
                {
                    if ( work >= 200000 )
                    {
                        m[side]->nRecordLimits++;
                        if ( pPars->fVerbose ) Abc_Print(1, "Component record matching yielded after 200000 terms; cursor retained.\n");
                        goto finish;
                    }
                    work += Vec_WecSize(r->vMonomials);
                    key = Acec2_RecordKey(r, vMaps[side], vFrontier, width, q->Flip, &limited);
                    if ( !key ) { m[side]->nRecordLimits += limited; continue; }
                    phase = q->Flip | Acec2_RecordKeyTop(key, width);
                    id = Hsh_VecManAdd(q->hKeys, key); Vec_IntFree(key);
                    while ( Vec_IntSize(q->vOwners) <= id ) Vec_IntPush(q->vOwners, -1);
                    if ( !side ) { if ( Vec_IntEntry(q->vOwners, id) < 0 ) Vec_IntWriteEntry(q->vOwners, id, 4*q->Record+phase); continue; }
                    found = Vec_IntEntry(q->vOwners, id); if ( found < 0 ) continue;
                    pair[0] = (Acec2_Record_t *)Vec_PtrEntry(m[0]->vRecords, found/4); pair[1] = r;
                    added = Acec2_RecordAliases(pair, vMaps, vReplaces, width, (found & 3) ^ phase);
                    if ( added < 0 ) { result = added; goto finish; }
                    if ( added ) { result += added; (*pnWords)++; }
                }
            }
        Hsh_VecManStop(q->hKeys); q->hKeys = NULL;
        q->iWidth++; q->Side = q->Record = q->Flip = 0;
        // Rebuild immediately after a productive widest-prefix pass.
        if ( result ) break;
    }
finish:
    if ( q->iWidth == Vec_IntSize(q->vWidths) ) Acec2_RecordMatchClear(q);
    return result;
}

/**Function*************************************************************

  Synopsis    [Returns the full operand product span for reporting.]

  Description [Zero denotes a record without a complete single-product
  factorization. The record's proof modulus remains a separate property.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_RecordFullProductWidth( Acec2_Record_t * r )
{
    Acec2_Product_t * p = r->pProductReference;
    if ( !p && r->vFactors && Vec_PtrSize(r->vFactors) == 1 && r->FactorWidth == r->Width &&
         r->vResidual && !Vec_WecSize(r->vResidual) ) p = (Acec2_Product_t *)Vec_PtrEntry(r->vFactors, 0);
    return p ? Abc_MaxInt(0, Vec_IntSize(p->vOperands[0])+Vec_IntSize(p->vOperands[1])+p->Shift) : 0;
}

/**Function*************************************************************

  Synopsis    [Writes exact identities, proof scope and component provenance.]

  Description [The untruncated product width describes its operands, not a
  claim about unproved columns or a requirement to preserve overflow bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_RecordWriteJson( Acec2_Man_t * m, FILE * f )
{
    Acec2_Record_t * r; Acec2_Product_t * product; Vec_Int_t * v;
    int i, j, k, nWords, side;
    fprintf(f, "[");
    Vec_PtrForEachEntry(Acec2_Record_t *, m->vRecords, r, i)
    {
        nWords = (r->Width+63)/64;
        fprintf(f, "%s{\"id\":%d,\"region\":%d,\"word\":%d,\"counter\":%d,\"expression\":%d,\"width\":%d,\"binary_prefix\":%d,\"domain\":\"source\",\"justification\":\"%s\",\"cut_literals\":[",
            i ? ",\n" : "", i, r->Tree, r->Word, r->Counter, r->Expression, r->Width, r->Prefix,
            r->fPolynomial == 2 ? "checked_grid_expression" : r->fPolynomial ? "checked_output_polynomial" : r->vOutputMasks ? "checked_masked_source" : r->pProductReference ? "checked_product_grid" : r->Proof ? "checked_weighted_source" : r->Compose ? "checked_operand_composition" : r->Extend ? "checked_product_low_bit" : r->vParts ? (Vec_IntSize(r->vDependencies) ? "checked_record_composition" : "checked_counter_composition") : r->Counter >= 0 ? "checked_counter_cut" : r->Word < 0 ? "checked_cell_composition" : ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->pProduct ? "checked_product_word" : ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->vSumProducts ? "checked_product_sum_word" : ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->fIndependent ? "checked_linear_word" : ((Acec2_Word_t *)Vec_PtrEntry(m->vWords, r->Word))->fPolynomial ? "checked_polynomial_word" : "checked_word_closure");
        Acec2_WriteList(f, r->vCut, 1, 0);
        fprintf(f, "],\"untruncated_product_width\":%d,\"certified_modulus_bits\":%d,\"component_status\":\"%s\",\"identity_complete\":true,\"binary_complete\":%s,\"product_factorization_complete\":%s,\"outputs\":[",
            Acec2_RecordFullProductWidth(r), r->Width,
            r->Prefix == r->Width ? "checked_binary_word" : "checked_weighted_identity", r->Prefix == r->Width ? "true" : "false",
            r->vFactors && Vec_PtrSize(r->vFactors) && r->FactorWidth == r->Width && !Vec_WecSize(r->vResidual) ? "true" : "false");
        for ( j = 0; j < Vec_IntSize(r->vOutputs); j += 2 )
            fprintf(f, "%s{\"literal\":%d,\"xor_literal\":%d,\"rank\":%d,\"status\":\"%s\",\"origin\":\"source\"}", j ? "," : "", Vec_IntEntry(r->vOutputs, j), r->vOutputMasks ? Vec_IntEntry(r->vOutputMasks, j/2) : 0, Vec_IntEntry(r->vOutputs, j+1),
                Vec_IntEntry(r->vBitStatus, j/2) == 1 ? "binary_word" : Vec_IntEntry(r->vBitStatus, j/2) == 2 ? "binary_prefix" : "weighted_root");
        fprintf(f, "],\"polynomial\":[");
        Vec_WecForEachLevel(r->vMonomials, v, j)
        {
            fprintf(f, "%s{\"source_ids\":[", j ? "," : "");
            Acec2_WriteList(f, v, 1, 0);
            fprintf(f, "],\"coefficient_limbs\":[");
            for ( k = 0; k < nWords; k++ ) fprintf(f, "%s\"%016llx\"", k ? "," : "", (unsigned long long)Vec_WrdEntry(r->vCoefficients, j*nWords+k));
            fprintf(f, "]}");
        }
        fprintf(f, "],\"source_product_reference\":");
        product = r->pProductReference;
        if ( !product ) fprintf(f, "null");
        else
        {
            fprintf(f, "{\"shift\":%d,\"negated\":%s,\"signed\":[%s,%s],\"operand_literals\":[", product->Shift,
                product->fNeg ? "true" : "false", product->fSigned[0] ? "true" : "false", product->fSigned[1] ? "true" : "false");
            for ( side = 0; side < 2; side++ )
            {
                fprintf(f, "%s[", side ? "," : "");
                Acec2_WriteList(f, product->vOperands[side], 1, 0);
                fprintf(f, "]");
            }
            fprintf(f, "]}");
        }
        fprintf(f, ",\"cut_terms\":[");
        for ( j = 0; j < Vec_IntSize(r->vTerms); j += 2 )
            fprintf(f, "%s[%d,%d]", j ? "," : "", Vec_IntEntry(r->vTerms, j), Vec_IntEntry(r->vTerms, j+1));
        fprintf(f, "],\"constant_columns\":[");
        Acec2_WriteList(f, r->vConstants, 1, 0);
        fprintf(f, "],\"parts\":[");
        if ( r->vParts )
            for ( j = 0; j < Vec_IntSize(r->vParts); j += 4 )
                fprintf(f, "%s[%d,%d,%d,%d]", j ? "," : "", Vec_IntEntry(r->vParts, j), Vec_IntEntry(r->vParts, j+1), Vec_IntEntry(r->vParts, j+2), Vec_IntEntry(r->vParts, j+3));
        fprintf(f, "],\"source_proof\":%d,\"composition_parent\":%d,\"operand_compositions\":[", r->Proof-1, r->Compose-1);
        if ( r->vComposition )
            for ( j = 0; j < Vec_IntSize(r->vComposition); j += 3 )
                fprintf(f, "%s[%d,%d,%d]", j ? "," : "", Vec_IntEntry(r->vComposition, j), Vec_IntEntry(r->vComposition, j+1), Vec_IntEntry(r->vComposition, j+2));
        fprintf(f, "],\"dependencies\":[");
        Acec2_WriteList(f, r->vDependencies, 1, 0);
        fprintf(f, "],\"covered_gates\":[");
        Acec2_WriteList(f, r->vCovered, 1, 0);
        fprintf(f, "],\"support_cone_roots\":[");
        Acec2_WriteList(f, r->vSupport, 1, 0);
        fprintf(f, "],\"factorization\":");
        if ( !r->vFactors ) fprintf(f, "null");
        else
        {
            fprintf(f, "{\"width\":%d,\"products\":[", r->FactorWidth);
            Vec_PtrForEachEntry(Acec2_Product_t *, r->vFactors, product, j)
            {
                fprintf(f, "%s{\"shift\":%d,\"negated\":%s,\"signed\":[%s,%s],\"operand_literals\":[", j ? "," : "", product->Shift,
                    product->fNeg ? "true" : "false", product->fSigned[0] ? "true" : "false", product->fSigned[1] ? "true" : "false");
                for ( side = 0; side < 2; side++ )
                {
                    fprintf(f, "%s[", side ? "," : "");
                    Acec2_WriteList(f, product->vOperands[side], 1, 0);
                    fprintf(f, "]");
                }
                fprintf(f, "]}");
            }
            fprintf(f, "],\"residual\":["); nWords = (r->FactorWidth+63)/64;
            Vec_WecForEachLevel(r->vResidual, v, j)
            {
                fprintf(f, "%s{\"source_ids\":[", j ? "," : "");
                Acec2_WriteList(f, v, 1, 0);
                fprintf(f, "],\"coefficient_limbs\":[");
                for ( k = 0; k < nWords; k++ ) fprintf(f, "%s\"%016llx\"", k ? "," : "", (unsigned long long)Vec_WrdEntry(r->vResidualCoefs, j*nWords+k));
                fprintf(f, "]}");
            }
            fprintf(f, "]}");
        }
        fprintf(f, "}");
    }
    fprintf(f, "]");
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
