/**CFile****************************************************************

  FileName    [acec2Template.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Matches structurally instantiated, independently proved arithmetic templates.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 12, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"
#include "base/wlc/wlc.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

enum { ACEC2_TEMPLATE_FORMS = 64 };

typedef struct Acec2_TemplEntry_t_ Acec2_TemplEntry_t;
struct Acec2_TemplEntry_t_
{
    Gia_Man_t * g;
    int nProved; // certified low prefix; zero means unproved
    unsigned Tried[8]; // prefixes with completed certificates or rejections
    unsigned Limited[8]; // unknown prefixes at the recorded effort tier
    int nTriedEffort;
};
struct Acec2_Templ_t_
{
    Hsh_VecMan_t * hKeys;
    Vec_Ptr_t * vEntries;
    Hsh_VecMan_t * hShiftKeys;
    Vec_Int_t * vShiftSteps, * vShiftLimited;
    int fPending, fMatchStopped;
    int nShiftPad, nShiftGain;
    int nObjs;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Owns reusable template structures and their exact certificates.]

  Description [The cache belongs to one CEC invocation. Clearing it discards
  only reusable work, never any proof already installed in the miter.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Templ_t * Acec2_TemplateStart( void )
{
    Acec2_Templ_t * p = ABC_CALLOC(Acec2_Templ_t, 1);
    p->hKeys = Hsh_VecManStart(100); p->vEntries = Vec_PtrAlloc(100);
    p->hShiftKeys = Hsh_VecManStart(100); p->vShiftSteps = Vec_IntAlloc(100); p->vShiftLimited = Vec_IntAlloc(100);
    return p;
}
/**Function*************************************************************

  Synopsis    [Releases cached template graphs, certificates and their keys.]

  Description [Retains the entry vector and separate shifted-search state.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_TemplateClear( Acec2_Templ_t * p )
{
    Acec2_TemplEntry_t * e;
    int i;
    Vec_PtrForEachEntry(Acec2_TemplEntry_t *, p->vEntries, e, i) { Gia_ManStop(e->g); ABC_FREE(e); }
    Vec_PtrClear(p->vEntries); Hsh_VecManStop(p->hKeys); p->hKeys = NULL; p->nObjs = 0;
}
/**Function*************************************************************

  Synopsis    [Releases all state owned by a template-search invocation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_TemplateStop( Acec2_Templ_t * p )
{
    if ( !p ) return;
    Acec2_TemplateClear(p); Vec_PtrFree(p->vEntries);
    Hsh_VecManStop(p->hShiftKeys); Vec_IntFree(p->vShiftSteps); Vec_IntFree(p->vShiftLimited); ABC_FREE(p);
}
/**Function*************************************************************

  Synopsis    [Records that another template-search pass has work to try.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_TemplateSetPending( Acec2_Templ_t * p )
{
    p->fPending = 1;
}
/**Function*************************************************************

  Synopsis    [Reads and optionally clears the pending-work flag.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_TemplatePending( Acec2_Templ_t * p, int fClear )
{
    int value = p->fPending;
    if ( fClear ) p->fPending = 0;
    return value;
}

/**Function*************************************************************

  Synopsis    [Revisits failed structural searches after new equalities.]

  Description [Certificates stay valid, but a failed template lookup is not
  reusable after operand correspondences change. Stable original search keys
  alone do not capture these new matching opportunities.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_TemplateNewProofs( Acec2_Templ_t * p )
{
    Vec_IntFill(p->vShiftSteps, Vec_IntSize(p->vShiftSteps), 0);
    Vec_IntFill(p->vShiftLimited, Vec_IntSize(p->vShiftLimited), 0);
    p->fPending = 0;
}

/**Function*************************************************************

  Synopsis    [Builds a signed or unsigned product from literal operands.]

  Description [The four modes independently select each operand's sign bit.
  The result is reduced modulo 2^Width.]

  SideEffects [Appends gates to the caller's private GIA.]

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acec2_ProductBits( Gia_Man_t * g, Vec_Int_t ** vOps, int Mode, int Width )
{
    Vec_Wec_t * vCols = Vec_WecStart(Width);
    Vec_Int_t * vBias = Vec_IntStart(Width), * vBits = Vec_IntStart(Width), * v;
    int i, j, k, a, b, c, x, y, lit, neg, carry, sum;
    Vec_IntForEachEntry(vOps[0], a, i)
        Vec_IntForEachEntry(vOps[1], b, j)
        {
            if ( i+j >= Width ) continue;
            x = a;
            y = b;
            lit = Gia_ManHashAnd(g, x, y);
            neg = ((Mode & 1) && i == Vec_IntSize(vOps[0])-1) ^ ((Mode & 2) && j == Vec_IntSize(vOps[1])-1);
            Vec_WecPush(vCols, i+j, lit ^ neg);
            if ( neg )
                for ( k = i+j; k < Width; k++ )
                { x = Vec_IntEntry(vBias, k); Vec_IntWriteEntry(vBias, k, x ^ 1); if ( x ) break; }
        }
    for ( k = 0; k < Width; k++ )
    {
        v = Vec_WecEntry(vCols, k);
        while ( Vec_IntSize(v) > 1 )
        {
            a = Vec_IntPop(v); b = Vec_IntPop(v); c = Vec_IntSize(v) ? Vec_IntPop(v) : 0;
            sum = Gia_ManHashXor(g, Gia_ManHashXor(g, a, b), c);
            carry = Gia_ManHashMaj(g, a, b, c); Vec_IntPush(v, sum);
            if ( k+1 < Width ) Vec_WecPush(vCols, k+1, carry);
        }
        if ( Vec_IntSize(v) ) Vec_IntWriteEntry(vBits, k, Vec_IntEntry(v, 0));
    }
    carry = 0;
    for ( k = 0; k < Width; k++ )
    {
        a = Vec_IntEntry(vBits, k); b = Vec_IntEntry(vBias, k);
        Vec_IntWriteEntry(vBits, k, Gia_ManHashXor(g, a, carry) ^ b);
        carry = b ? Gia_ManHashOr(g, a, carry) : Gia_ManHashAnd(g, a, carry);
    }
    Vec_WecFree(vCols); Vec_IntFree(vBias); return vBits;
}

/**Function*************************************************************

  Synopsis    [Tests a structural AND without inserting speculative nodes.]

  Description [Negative literals denote missing template subgraphs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TemplateAnd( Gia_Man_t * g, int a, int b )
{
    if ( a == 0 || b == 0 ) return 0;
    return a < 0 || b < 0 ? -1 : Gia_ManHashAndTry(g, a, b);
}
/**Function*************************************************************

  Synopsis    [Looks up a phased XOR without inserting speculative nodes.]

  Description [Returns a negative literal if the required structure is absent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TemplateXor( Gia_Man_t * g, int a, int b )
{
    int x, y, z;
    if ( a < 0 || b < 0 ) return -1;
    x = Acec2_TemplateAnd(g, a & ~1, b | 1);
    y = Acec2_TemplateAnd(g, b & ~1, a | 1);
    z = Acec2_TemplateAnd(g, x < 0 ? -1 : x ^ 1, y < 0 ? -1 : y ^ 1);
    return z < 0 ? -1 : z ^ 1 ^ ((a ^ b) & 1);
}
/**Function*************************************************************

  Synopsis    [Looks up a simplified mux without inserting speculative nodes.]

  Description [Returns a negative literal if the required structure is absent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TemplateMux( Gia_Man_t * g, int c, int a, int b )
{
    int x, y, z, phase = 0;
    if ( c == 0 ) return b;
    if ( c == 1 || a == b ) return a;
    if ( c < 0 || a < 0 || b < 0 ) return -1;
    if ( b > a ) { ABC_SWAP(int, a, b); c ^= 1; }
    if ( a & 1 ) { a ^= 1; b ^= 1; phase = 1; }
    x = Acec2_TemplateAnd(g, c ^ 1, b); y = Acec2_TemplateAnd(g, c, a);
    z = Acec2_TemplateAnd(g, x < 0 ? -1 : x ^ 1, y < 0 ? -1 : y ^ 1);
    return z < 0 ? -1 : z ^ 1 ^ phase;
}
/**Function*************************************************************

  Synopsis    [Retains a new valid template literal within the forms limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_TemplatePush( Vec_Int_t * v, int Lit )
{
    if ( Lit >= 0 && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS && Vec_IntFind(v, Lit) < 0 ) Vec_IntPush(v, Lit);
}
/**Function*************************************************************

  Synopsis    [Reads a phased candidate literal or reports a missing form.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TemplateEntry( Vec_Int_t * v, int i, int Phase )
{
    return i < Vec_IntSize(v) ? Vec_IntEntry(v, i) ^ Phase : -1;
}

/**Function*************************************************************

  Synopsis    [Finds template result literals already present in the miter.]

  Description [Every matched gate is a Boolean identity. Recognizing XORs
  and muxes follows the same canonical form as the initial miter copy.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wec_t * Acec2_TemplateFind( Gia_Man_t * g, Gia_Man_t * pNew, Vec_Wec_t * vInputs )
{
    Vec_Wec_t * vMap = Vec_WecStart(Gia_ManObjNum(g)), * vBits = Vec_WecStart(Gia_ManCoNum(g));
    Vec_Int_t * v, * va, * vb, * vc;
    Gia_Obj_t * o, * a, * b, * c;
    int i, j, k, t, x, y, z, ca, cb, cc;
    Vec_IntPush(Vec_WecEntry(vMap, 0), 0);
    Gia_ManForEachCi(g, o, i) Vec_IntAppend(Vec_WecEntry(vMap, Gia_ObjId(g, o)), Vec_WecEntry(vInputs, i));
    Gia_ManForEachAnd(g, o, i)
    {
        v = Vec_WecEntry(vMap, i); va = Vec_WecEntry(vMap, Gia_ObjFaninId0(o, i)); vb = Vec_WecEntry(vMap, Gia_ObjFaninId1(o, i));
        for ( j = 0; j < Abc_MaxInt(1, Vec_IntSize(va)) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; j++ )
            for ( k = 0; k < Abc_MaxInt(1, Vec_IntSize(vb)) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; k++ )
            {
                x = Acec2_TemplateEntry(va, j, Gia_ObjFaninC0(o)); y = Acec2_TemplateEntry(vb, k, Gia_ObjFaninC1(o));
                Acec2_TemplatePush(v, Acec2_TemplateAnd(pNew, x, y));
            }
        if ( !Gia_ObjIsMuxType(o) ) continue;
        if ( Gia_ObjRecognizeExor(o, &a, &b) )
        {
            ca = Gia_IsComplement(a); cb = Gia_IsComplement(b);
            va = Vec_WecEntry(vMap, Gia_ObjId(g, Gia_Regular(a))); vb = Vec_WecEntry(vMap, Gia_ObjId(g, Gia_Regular(b)));
            for ( j = 0; j < Vec_IntSize(va) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; j++ )
                for ( k = 0; k < Vec_IntSize(vb) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; k++ )
                    Acec2_TemplatePush(v, Acec2_TemplateXor(pNew, Vec_IntEntry(va, j) ^ ca, Vec_IntEntry(vb, k) ^ cb));
        }
        else
        {
            c = Gia_ObjRecognizeMux(o, &a, &b); ca = Gia_IsComplement(a); cb = Gia_IsComplement(b); cc = Gia_IsComplement(c);
            va = Vec_WecEntry(vMap, Gia_ObjId(g, Gia_Regular(a))); vb = Vec_WecEntry(vMap, Gia_ObjId(g, Gia_Regular(b)));
            vc = Vec_WecEntry(vMap, Gia_ObjId(g, Gia_Regular(c)));
            for ( j = 0; j < Abc_MaxInt(1, Vec_IntSize(va)) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; j++ )
                for ( k = 0; k < Abc_MaxInt(1, Vec_IntSize(vb)) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; k++ )
                    for ( t = 0; t < Abc_MaxInt(1, Vec_IntSize(vc)) && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; t++ )
                    {
                        x = Acec2_TemplateEntry(va, j, ca); y = Acec2_TemplateEntry(vb, k, cb); z = Acec2_TemplateEntry(vc, t, cc);
                        Acec2_TemplatePush(v, Acec2_TemplateMux(pNew, z, x, y));
                    }
        }
    }
    Gia_ManForEachCo(g, o, i)
    {
        v = Vec_WecEntry(vBits, i); va = Vec_WecEntry(vMap, Gia_ObjFaninId0p(g, o));
        Vec_IntForEachEntry(va, x, j) Acec2_TemplatePush(v, x ^ Gia_ObjFaninC0(o));
    }
    Vec_WecFree(vMap); return vBits;
}

/**Function*************************************************************

  Synopsis    [Builds one architecture over an independent operand interface.]

  Description [Input repetition and phases are explicit in vOps. Port
  extension, operand order and architecture are only structural proposals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_TemplateBuild( Vec_Int_t ** vOps, int nInputs, int Width, int Mode,
                                     int Arch, int Swap, int Shape, int fSigned )
{
    Gia_Man_t * g = Gia_ManStart(1000), * clean;
    Vec_Int_t * vArgs[2], * vBits = Vec_IntAlloc(Width+2), * vTemp = Vec_IntAlloc(100);
    int side, i, n, max = Abc_MaxInt(Vec_IntSize(vOps[0]), Vec_IntSize(vOps[1]));
    for ( i = 0; i < nInputs; i++ ) Gia_ManAppendCi(g);
    Gia_ManHashAlloc(g);
    for ( side = 0; side < 2; side++ )
    {
        vArgs[side] = Vec_IntDup(vOps[side]); n = Vec_IntSize(vArgs[side]);
        if ( Shape == 1 ) n++;
        if ( Shape == 2 ) n = max;
        if ( Shape == 3 ) n = max+1;
        if ( Shape == 4 || Shape == 5+side ) n = Abc_MaxInt(n, Width);
        if ( Shape == 7+side ) n++;
        Vec_IntFillExtra(vArgs[side], n, (Mode & (1 << side)) ? Vec_IntEntryLast(vArgs[side]) : 0);
    }
    if ( Arch == 0 ) Wlc_BlastMultiplier(g, Vec_IntArray(vArgs[Swap]), Vec_IntArray(vArgs[!Swap]),
        Vec_IntSize(vArgs[Swap]), Vec_IntSize(vArgs[!Swap]), vTemp, vBits, fSigned);
    if ( Arch == 1 ) Wlc_BlastBoothYJ(g, NULL, Vec_IntArray(vArgs[Swap]), Vec_IntArray(vArgs[!Swap]),
        Vec_IntSize(vArgs[Swap]), Vec_IntSize(vArgs[!Swap]), vBits, fSigned, 0, 0);
    if ( Arch == 2 ) Wlc_BlastWallace(g, NULL, Vec_IntArray(vArgs[Swap]), Vec_IntArray(vArgs[!Swap]),
        Vec_IntSize(vArgs[Swap]), Vec_IntSize(vArgs[!Swap]), vBits, fSigned, 0, 0);
    Vec_IntFillExtra(vBits, Width, fSigned ? Vec_IntEntryLast(vBits) : 0);
    for ( i = 0; i < Width; i++ ) Gia_ManAppendCo(g, Vec_IntEntry(vBits, i));
    Gia_ManHashStop(g); clean = Gia_ManCleanup(g); Gia_ManStop(g);
    Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]); Vec_IntFree(vBits); Vec_IntFree(vTemp);
    return clean;
}

/**Function*************************************************************

  Synopsis    [Caches architecture instances over symbolic, independent inputs.]

  Description [Keys contain the complete literal operand lists, including
  repeated inputs, constants, phases and signedness. A bounded cache also
  permits reuse across different occurrences of the same multiplier shape.]

  SideEffects [May evict previously cached structures.]

  SeeAlso     []

***********************************************************************/
static Acec2_TemplEntry_t * Acec2_TemplateGet( Acec2_Templ_t * p, Vec_Int_t ** vOps, int nInputs,
                                             int Width, int Mode, int Arch, int Swap, int Shape, int Sign )
{
    Vec_Int_t * vKey;
    Acec2_TemplEntry_t * e;
    int id, oldSize, side;
    if ( Vec_PtrSize(p->vEntries) >= 2048 || p->nObjs > 2000000 )
    { Acec2_TemplateClear(p); p->hKeys = Hsh_VecManStart(100); }
    vKey = Vec_IntAlloc(16+Vec_IntSize(vOps[0])+Vec_IntSize(vOps[1])); oldSize = Hsh_VecSize(p->hKeys);
    Vec_IntPushThree(vKey, nInputs, Width, Mode); Vec_IntPushThree(vKey, Arch, Swap, Shape); Vec_IntPush(vKey, Sign);
    for ( side = 0; side < 2; side++ ) { Vec_IntPush(vKey, Vec_IntSize(vOps[side])); Vec_IntAppend(vKey, vOps[side]); }
    id = Hsh_VecManAdd(p->hKeys, vKey); Vec_IntFree(vKey);
    if ( id < oldSize ) return (Acec2_TemplEntry_t *)Vec_PtrEntry(p->vEntries, id);
    e = ABC_CALLOC(Acec2_TemplEntry_t, 1);
    e->g = Acec2_TemplateBuild(vOps, nInputs, Width, Mode, Arch, Swap, Shape, Sign);
    Vec_PtrPush(p->vEntries, e); p->nObjs += Gia_ManObjNum(e->g);
    return e;
}

/**Function*************************************************************

  Synopsis    [Imports an equality established by earlier reconstruction.]

  Description [The lower object ID becomes the representative.]

  SideEffects [Updates a private literal equivalence forest.]

  SeeAlso     []

***********************************************************************/
static void Acec2_TemplateUnion( Vec_Int_t * vRepr, int a, int b )
{
    a = Acec2_LitFind(vRepr, a); b = Acec2_LitFind(vRepr, b);
    if ( a == b ) return;
    assert( (a >> 1) != (b >> 1) );
    if ( a > b ) ABC_SWAP(int, a, b);
    Vec_IntWriteEntry(vRepr, b >> 1, a ^ (b & 1));
}

/**Function*************************************************************

  Synopsis    [Certifies matched multiplier instances before merging roots.]

  Description [Templates are proved over independent cut inputs using exact
  polynomial equality. Substitution then preserves that proof inside the
  original Boolean network. No name, generator provenance or simulation is
  accepted as proof. Missing structures and resource limits simply fall back
  to the generic component checker. The shared AIG is never enlarged.]

  SideEffects [Installs only proved root aliases in private replacement maps.]

  SeeAlso     []

***********************************************************************/
int Acec2_TemplateMatch( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals, Vec_Int_t ** vReplaces,
                       Vec_Int_t ** vOps, int Width, Acec2_Par_t * pPars, abctime Deadline, int * pnWords, Acec2_Templ_t * pTemplates )
{
    Vec_Int_t * vInputs, * vArgs[2], * vUsed, * vRepr, * vLinked, * v, * vRefBits, * vFirst;
    Vec_Wec_t * vInputSets, * vBitSets;
    Vec_Int_t * vHeads, * vNext, * vColors;
    Gia_Man_t * g, * ref, * clean;
    Acec2_Man_t * m, * mRef;
    Acec2_Par_t Pars = *pPars;
    Acec2_Templ_t * pLocal = pTemplates ? NULL : Acec2_TemplateStart();
    Acec2_TemplEntry_t * e;
    int side, i, j, lit, key, mode, modeIndex, arch, swap, shape, sign, matched, useful, a, b, ports[2], merged = 0, proved = 0, fStopped = 0, result, nLimit, nNeed, nWords = 0, fModeMerged, nZeros = 0, fComplete = 0;
    int na = Vec_IntSize(vOps[0]), nb = Vec_IntSize(vOps[1]), nMax = Abc_MaxInt(na, nb), fCancelled = 0;
    abctime stop;
    if ( !pTemplates ) pTemplates = pLocal;
    pTemplates->fMatchStopped = 0;
    if ( !na || !nb || Width < 4 || Width > 256 || nMax > 128 ) { Acec2_TemplateStop(pLocal); return 0; }
    if ( !Pars.pCancelled ) Pars.pCancelled = &fCancelled;
    pPars = &Pars;
    vInputs = Vec_IntAlloc(na+nb); vUsed = Vec_IntStart(Gia_ManObjNum(pNew)); vRepr = Vec_IntStartFull(Gia_ManObjNum(pNew)); vLinked = Vec_IntStart(Gia_ManObjNum(pNew));
    vColors = Vec_IntStart(Gia_ManObjNum(pNew));
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            a = Vec_IntEntry(vOriginals[side], i);
            Acec2_TemplateUnion(vRepr, lit, a);
            Vec_IntWriteEntry(vUsed, a >> 1, 1);
        }
        vArgs[side] = Vec_IntAlloc(Vec_IntSize(vOps[side]));
        Vec_IntForEachEntry(vOps[side], lit, i)
        {
            if ( lit < 2 ) { Vec_IntPush(vArgs[side], lit); continue; }
            j = Vec_IntFind(vInputs, lit & ~1);
            if ( j < 0 ) { j = Vec_IntSize(vInputs); Vec_IntPush(vInputs, lit & ~1); }
            Vec_IntPush(vArgs[side], Abc_Var2Lit(j+1, lit & 1));
        }
    }
    for ( side = 0; side < 2; side++ )
    {
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            a = Acec2_LitFind(vRepr, lit) >> 1;
            Vec_IntWriteEntry(vColors, a, Vec_IntEntry(vColors, a) | (1 << side));
        }
    }
    vHeads = Vec_IntStartFull(Gia_ManObjNum(pNew)); vNext = Vec_IntStartFull(Gia_ManObjNum(pNew));
    for ( i = 0; i < Gia_ManObjNum(pNew); i++ )
    {
        if ( !Vec_IntEntry(vUsed, i) ) continue;
        a = Acec2_LitFind(vRepr, 2*i);
        Vec_IntWriteEntry(vNext, i, Vec_IntEntry(vHeads, a >> 1));
        Vec_IntWriteEntry(vHeads, a >> 1, 2*i ^ (a & 1));
    }
    vInputSets = Vec_WecStart(Vec_IntSize(vInputs));
    Vec_IntForEachEntry(vInputs, lit, i)
    {
        v = Vec_WecEntry(vInputSets, i); Acec2_TemplatePush(v, lit);
        a = Acec2_LitFind(vRepr, lit);
        for ( b = Vec_IntEntry(vHeads, a >> 1); b >= 0 && Vec_IntSize(v) < ACEC2_TEMPLATE_FORMS; b = Vec_IntEntry(vNext, b >> 1) )
            Acec2_TemplatePush(v, b ^ (a & 1));
    }
    Vec_IntFree(vHeads); Vec_IntFree(vNext);
    // Both signed and unsigned products are divisible by the combined
    // power of two of their constant zero prefixes. Seed these exact
    // reference bits even if the simpler architecture is already shared
    // and therefore does not need another certificate of its own.
    for ( side = 0; side < 2; side++ )
    {
        for ( i = 0; i < Vec_IntSize(vArgs[side]) && !Vec_IntEntry(vArgs[side], i); i++ ) {}
        if ( i == Vec_IntSize(vArgs[side]) ) { nZeros = Width; break; }
        nZeros += i;
    }
    Pars.fVerbose = 0;
    for ( modeIndex = 0; modeIndex < 4; modeIndex++ )
    {
        // Ordinary unsigned and signed words precede mixed signedness.
        mode = modeIndex == 1 ? 3 : modeIndex > 1 ? modeIndex-1 : 0;
        ref = NULL; mRef = NULL; vFirst = Vec_IntStartFull(Width); fModeMerged = 0;
        for ( i = 0; i < Abc_MinInt(nZeros, Width); i++ ) Vec_IntWriteEntry(vFirst, i, 0);
        for ( shape = 0; shape < 9; shape++ )
        {
            if ( na == nb && (shape == 2 || shape == 3) ) continue;
            if ( shape == 4 && Width <= nMax+1 ) continue;
            for ( side = 0; side < 2; side++ )
            {
                ports[side] = Vec_IntSize(vArgs[side]);
                if ( shape == 1 || shape == 7+side ) ports[side]++;
                if ( shape == 2 ) ports[side] = nMax;
                if ( shape == 3 ) ports[side] = nMax+1;
                if ( shape == 4 || shape == 5+side ) ports[side] = Abc_MaxInt(ports[side], Width);
            }
            for ( sign = 0; sign < 2; sign++ )
            {
                nLimit = Width;
                for ( side = 0; side < 2; side++ )
                {
                    // A sign interpretation changes the operand by a multiple
                    // of 2^port_width. The lower product bits can still match.
                    if ( (!sign && (mode & (1 << side))) ||
                         (sign && !(mode & (1 << side)) && ports[side] == Vec_IntSize(vArgs[side]) && Vec_IntEntryLast(vArgs[side])) )
                        nLimit = Abc_MinInt(nLimit, ports[side]);
                }
                if ( nLimit < 4 ) continue;
                for ( arch = 0; arch < 3; arch++ )
                    for ( swap = 0; swap < 2; swap++ )
                    {
                        if ( fStopped || Acec2_Stop(pPars, Deadline) ) { fStopped = 1; goto mode_finish; }
                        e = Acec2_TemplateGet(pTemplates, vArgs, Vec_IntSize(vInputs), Width, mode, arch, swap, shape, sign);
                        g = e->g;
                        vBitSets = Acec2_TemplateFind(g, pNew, vInputSets);
                        matched = useful = nNeed = 0;
                        Vec_WecForEachLevel(vBitSets, v, i)
                            Vec_IntForEachEntry(v, lit, j)
                                if ( i < nLimit && lit >= 2 && Vec_IntEntry(vUsed, lit >> 1) )
                                {
                                    matched++; useful += Vec_IntEntry(vColors, Acec2_LitFind(vRepr, lit) >> 1) != 3;
                                    if ( i >= nNeed ) nNeed = i+1;
                                }
                        // A cached certificate for an already shared word
                        // can anchor another architecture of the same word.
                        if ( matched < 4 || (!useful && e->nProved < nNeed) ) { Vec_WecFree(vBitSets); continue; }
                        if ( e->nTriedEffort != Pars.nCecPolyLimit )
                        { memset(e->Limited, 0, sizeof(e->Limited)); e->nTriedEffort = Pars.nCecPolyLimit; }
                        if ( e->nProved < nNeed && ((e->Tried[(nNeed-1)/32] | e->Limited[(nNeed-1)/32]) & (1u << ((nNeed-1)%32))) )
                        { Vec_WecFree(vBitSets); continue; }
                        stop = Deadline;
                        if ( e->nProved < nNeed && !ref )
                        {
                            ref = Gia_ManStart(1000); for ( i = 0; i < Vec_IntSize(vInputs); i++ ) Gia_ManAppendCi(ref);
                            Gia_ManHashAlloc(ref); vRefBits = Acec2_ProductBits(ref, vArgs, mode, Width);
                            Vec_IntForEachEntry(vRefBits, lit, i) { Gia_ManAppendCo(ref, lit); }
                            Vec_IntFree(vRefBits); Gia_ManHashStop(ref); clean = Gia_ManCleanup(ref); Gia_ManStop(ref); ref = clean;
                            mRef = Acec2_AnalyzeCells(ref, &Pars, Deadline);
                        }
                        m = e->nProved >= nNeed ? NULL : Acec2_AnalyzeCells(g, &Pars, Deadline);
                        result = e->nProved >= nNeed ? 1 : Acec2_PolyComparePrefix(m, mRef, nNeed, stop);
                        // An interrupted attempt is not a failed certificate.
                        // Cache completed results and deterministic effort
                        // limits. Clock expiry and cancellation stay retryable.
                        if ( !Acec2_Stop(pPars, stop) )
                        {
                            if ( result >= 0 ) e->Tried[(nNeed-1)/32] |= 1u << ((nNeed-1)%32);
                            else if ( (m && m->fPolyEffortLimit) || (mRef && mRef->fPolyEffortLimit) )
                                e->Limited[(nNeed-1)/32] |= 1u << ((nNeed-1)%32);
                        }
                        if ( result == 1 ) e->nProved = Abc_MaxInt(e->nProved, nNeed);
                        if ( result == 1 )
                        {
                            proved++;
                            Vec_WecForEachLevel(vBitSets, v, i)
                            Vec_IntForEachEntry(v, lit, j)
                            {
                                // Certified constant result bits are also
                                // representatives. Booth may retain a Boolean
                                // cone for a zero bit that another architecture
                                // folds to literal zero during construction.
                                if ( i >= nNeed || lit < 0 || (lit >= 2 && !Vec_IntEntry(vUsed, lit >> 1)) ) continue;
                                key = i; a = Acec2_LitFind(vRepr, lit); b = Vec_IntEntry(vFirst, key);
                                if ( b < 0 ) { Vec_IntWriteEntry(vFirst, key, a); continue; }
                                b = Acec2_LitFind(vRepr, b);
                                if ( a == b ) continue;
                                assert( (a >> 1) != (b >> 1) );
                                fModeMerged = 1;
                                if ( a > b ) ABC_SWAP(int, a, b);
                                Vec_IntWriteEntry(vRepr, b >> 1, a ^ (b & 1));
                                Vec_IntWriteEntry(vColors, a >> 1, Vec_IntEntry(vColors, a >> 1) | Vec_IntEntry(vColors, b >> 1));
                                Vec_IntWriteEntry(vLinked, a >> 1, 1); Vec_IntWriteEntry(vLinked, b >> 1, 1);
                            }
                            if ( fModeMerged )
                            {
                                for ( i = 0; i < Width; i++ )
                                {
                                    a = Vec_IntEntry(vFirst, i);
                                    if ( a < 0 ) break;
                                    a = Acec2_LitFind(vRepr, a);
                                    if ( a >= 2 && Vec_IntEntry(vColors, a >> 1) != 3 ) break;
                                }
                                fComplete = i == Width;
                            }
                        }
                        if ( (m && m->fStopped) || (mRef && mRef->fStopped) ) fStopped = 1;
                        Acec2_Free(m); Vec_WecFree(vBitSets);
                        // Install a complete proved correspondence promptly.
                        // A later pass can discover further occurrences; it
                        // reuses these certificates as shared word anchors.
                        if ( fStopped || fComplete ) goto mode_finish;
                    }
            }
        }
mode_finish:
        nWords += fModeMerged;
        Acec2_Free(mRef); if ( ref ) Gia_ManStop(ref); Vec_IntFree(vFirst);
        if ( fStopped || fComplete || Acec2_Stop(pPars, Deadline) ) break;
    }
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            a = Vec_IntEntry(vReplaces[side], i); if ( a < 0 ) a = lit;
            b = Acec2_LitFind(vRepr, lit);
            if ( Vec_IntEntry(vLinked, b >> 1) )
            { Vec_IntWriteEntry(vReplaces[side], i, b); merged += a != b; }
        }
    if ( pPars->fVerbose && proved ) Abc_Print(1, "Certified templates: operands = %d x %d, width = %d, instances = %d, new root aliases = %d.\n", na, nb, Width, proved, merged);
    if ( merged ) *pnWords += nWords;
    pTemplates->fMatchStopped = fStopped || (Deadline && Abc_Clock() >= Deadline);
    Vec_WecFree(vInputSets);
    Vec_IntFree(vColors);
    Vec_IntFree(vInputs); Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]); Vec_IntFree(vUsed); Vec_IntFree(vRepr); Vec_IntFree(vLinked);
    Acec2_TemplateStop(pLocal);
    return merged;
}

/**Function*************************************************************

  Synopsis    [Searches bounded low-zero extensions after direct matching stalls.]

  Description [Removed zero bits can change the surviving structure of a
  Booth recoder, including constant carry chains. The per-invocation cursor
  continues this search across arithmetic rounds. Every candidate is proved
  by the ordinary template certificate before any replacement.]

  SideEffects [Records search progress and proved aliases privately.]

  SeeAlso     []

***********************************************************************/
int Acec2_TemplateShifted( Gia_Man_t * pNew, Vec_Int_t ** vMaps, Vec_Int_t ** vOriginals,
                         Vec_Int_t ** vReplaces, Vec_Int_t ** vOps, int Width, Acec2_Par_t * pPars,
                         abctime Deadline, int * pnWords, Acec2_Templ_t * pTemplates )
{
    Acec2_Par_t Pars = *pPars;
    Acec2_Templ_t * p = pTemplates ? pTemplates : Acec2_TemplateStart();
    Vec_Int_t * vKey = Vec_IntAlloc(100), * vArgs[2], * vKeys[2], * vAliases = Vec_IntStartFull(Gia_ManObjNum(pNew));
    int id, step, order, side, pad, i, lit, old, preferred, first = 0, merged = 0, fCancelled = 0;
    unsigned done, limited;
    if ( !Pars.pCancelled ) Pars.pCancelled = &fCancelled;
    pPars = &Pars;
    if ( Hsh_VecSize(p->hShiftKeys) >= 1024 )
    { Hsh_VecManStop(p->hShiftKeys); p->hShiftKeys = Hsh_VecManStart(100); Vec_IntClear(p->vShiftSteps); Vec_IntClear(p->vShiftLimited); }
    // Stable original literals keep the cursor when sweeping rebuilds the
    // same operand with different destination IDs. This is only a search
    // key; no equality is inferred from a key collision.
    for ( side = 0; side < 2; side++ )
        Vec_IntForEachEntry(vMaps[side], lit, i)
        {
            old = Vec_IntEntry(vOriginals[side], i) ^ (lit & 1);
            if ( Vec_IntEntry(vAliases, lit >> 1) < 0 || old < Vec_IntEntry(vAliases, lit >> 1) )
                Vec_IntWriteEntry(vAliases, lit >> 1, old);
        }
    for ( side = 0; side < 2; side++ )
    {
        vKeys[side] = Vec_IntAlloc(Vec_IntSize(vOps[side]));
        Vec_IntForEachEntry(vOps[side], lit, i)
            Vec_IntPush(vKeys[side], lit < 2 ? lit : Vec_IntEntry(vAliases, lit >> 1) ^ (lit & 1));
    }
    if ( Vec_IntSize(vKeys[0]) > Vec_IntSize(vKeys[1]) ) first = 1;
    else if ( Vec_IntSize(vKeys[0]) == Vec_IntSize(vKeys[1]) )
        for ( i = 0; i < Vec_IntSize(vKeys[0]); i++ )
            if ( Vec_IntEntry(vKeys[0], i) != Vec_IntEntry(vKeys[1], i) )
            { first = Vec_IntEntry(vKeys[0], i) > Vec_IntEntry(vKeys[1], i); break; }
    Vec_IntPush(vKey, Width);
    for ( side = 0; side < 2; side++ ) { Vec_IntPush(vKey, Vec_IntSize(vKeys[side ^ first])); Vec_IntAppend(vKey, vKeys[side ^ first]); }
    Vec_IntFree(vKeys[0]); Vec_IntFree(vKeys[1]); Vec_IntFree(vAliases);
    id = Hsh_VecManAdd(p->hShiftKeys, vKey); Vec_IntFree(vKey);
    if ( id == Vec_IntSize(p->vShiftSteps) ) { Vec_IntPush(p->vShiftSteps, 0); Vec_IntPush(p->vShiftLimited, 0); }
    done = (unsigned)Vec_IntEntry(p->vShiftSteps, id); limited = (unsigned)Vec_IntEntry(p->vShiftLimited, id); preferred = p->nShiftPad;
    for ( order = 0; order < 32; order++ )
    {
        // A useful shift on one component is a promising proposal for other
        // components in the same netlist. The completed-variant mask keeps
        // this scheduling preference independent of search completeness.
        step = order;
        if ( preferred )
        {
            step = order < 2 ? 2*(preferred-1)+order : order-2;
            if ( order >= 2 && step >= 2*(preferred-1) ) step += 2;
        }
        if ( (done | limited) & ((unsigned)1 << step) ) continue;
        if ( Acec2_Stop(pPars, Deadline) ) break;
        pad = step/2+1;
        if ( Width+pad > pPars->nMaxWidth || Width+pad > 256 )
        { done |= (unsigned)1 << step; Vec_IntWriteEntry(p->vShiftSteps, id, (int)done); continue; }
        for ( side = 0; side < 2; side++ )
        {
            vArgs[side] = Vec_IntAlloc(Vec_IntSize(vOps[side ^ first])+pad);
            if ( side == (step & 1) ) for ( i = 0; i < pad; i++ ) Vec_IntPush(vArgs[side], 0);
            Vec_IntAppend(vArgs[side], vOps[side ^ first]);
        }
        merged += Acec2_TemplateMatch(pNew, vMaps, vOriginals, vReplaces, vArgs, Width+pad, pPars, Deadline, pnWords, p);
        Vec_IntFree(vArgs[0]); Vec_IntFree(vArgs[1]);
        // An interrupted variant remains unknown. Do not restart it on
        // every round without new operand evidence; visit other variants.
        if ( !p->fMatchStopped ) { done |= (unsigned)1 << step; Vec_IntWriteEntry(p->vShiftSteps, id, (int)done); }
        else { limited |= (unsigned)1 << step; Vec_IntWriteEntry(p->vShiftLimited, id, (int)limited); }
        if ( merged )
        {
            if ( merged > p->nShiftGain ) { p->nShiftPad = pad; p->nShiftGain = merged; }
            break;
        }
        if ( p->fMatchStopped ) break;
    }
    if ( pPars->fVerbose )
    {
        unsigned bits = done; int completed = 0, nLimited = 0;
        while ( bits ) { bits &= bits-1; completed++; }
        bits = limited; while ( bits ) { bits &= bits-1; nLimited++; }
        Abc_Print(1, "Shifted template search: completed = %d / 32, limited = %d, new aliases = %d.\n", completed, nLimited, merged);
    }
    if ( (done | limited) != ~(unsigned)0 && !merged ) p->fPending = 1;
    if ( !pTemplates ) Acec2_TemplateStop(p);
    return merged;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
