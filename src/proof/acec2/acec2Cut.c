/**CFile****************************************************************

  FileName    [acec2Cut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Bounded cut enumeration and exact multi-output identities.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id$]

  Description [Uses the common-support XOR/carry matching approach of
  acecRe.c.  Cut tables, candidate alternatives, and coverage scratch are
  private to this analysis.  Each accepted identity is checked on every
  assignment of its independent cut inputs.]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

typedef struct Acec2_Choice_t_ Acec2_Choice_t;
struct Acec2_Choice_t_
{
    Acec2_Cell_t * pCell;
    int KindId;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Re-derives a proposed local truth table from the actual gates.]

  Description [Leaves are independent variables. An uncovered input, an
  invalid cut, cancellation, or a bounded traversal failure rejects the
  shortcut and leaves the ordinary gate rule intact. No GIA scratch is used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_EvaluateCut( Acec2_Man_t * p, int * pCut, Vec_Int_t * vTruth,
                              Vec_Int_t * vStack, Vec_Int_t * vTouched )
{
    const int Vars[3] = {0xAA, 0xCC, 0xF0};
    Gia_Man_t * g = p->pGia;
    Gia_Obj_t * o;
    int n = pCut[0], root = pCut[4], i, j, id, fan, a, b, c, steps = 0, result = -1;
    if ( n < 1 || n > 3 || root <= 0 || root >= Gia_ManObjNum(g) ||
         !Gia_ObjIsAnd(Gia_ManObj(g, root)) ) return -1;
    for ( i = 0; i < n; i++ )
    {
        id = pCut[i+1];
        if ( id <= 0 || id >= root || Gia_ObjIsCo(Gia_ManObj(g, id)) ) return -1;
        for ( j = 0; j < i; j++ ) if ( pCut[j+1] == id ) return -1;
    }
    Vec_IntClear(vStack); Vec_IntClear(vTouched);
    for ( i = 0; i < n; i++ )
    { Vec_IntWriteEntry(vTruth, pCut[i+1], Vars[i]); Vec_IntPush(vTouched, pCut[i+1]); }
    Vec_IntPush(vStack, root);
    while ( Vec_IntSize(vStack) )
    {
        if ( ++steps > 4096 || (!(steps & 255) && Acec2_Stopped(p)) ) goto finish;
        id = Vec_IntEntryLast(vStack);
        if ( Vec_IntEntry(vTruth, id) >= 0 ) { Vec_IntPop(vStack); continue; }
        o = Gia_ManObj(g, id);
        if ( !Gia_ObjIsAnd(o) ) goto finish;
        for ( i = 0; i < (Gia_ObjIsMux(g, o) ? 3 : 2); i++ )
        {
            fan = i == 2 ? Gia_ObjFaninId2(g, id) : i ? Gia_ObjFaninId1(o, id) : Gia_ObjFaninId0(o, id);
            if ( Vec_IntEntry(vTruth, fan) < 0 ) break;
        }
        if ( i < (Gia_ObjIsMux(g, o) ? 3 : 2) ) { Vec_IntPush(vStack, fan); continue; }
        a = Vec_IntEntry(vTruth, Gia_ObjFaninId0(o, id)) ^ (Gia_ObjFaninC0(o) ? 255 : 0);
        b = Vec_IntEntry(vTruth, Gia_ObjFaninId1(o, id)) ^ (Gia_ObjFaninC1(o) ? 255 : 0);
        if ( Gia_ObjIsMux(g, o) )
        {
            c = Vec_IntEntry(vTruth, Gia_ObjFaninId2(g, id)) ^ (Gia_ObjFaninC2(g, o) ? 255 : 0);
            a = (c & b) | ((c ^ 255) & a);
        }
        else a = Gia_ObjIsXor(o) ? a ^ b : a & b;
        Vec_IntWriteEntry(vTruth, id, a); Vec_IntPush(vTouched, id); Vec_IntPop(vStack);
    }
    result = Vec_IntEntry(vTruth, root);
finish:
    Vec_IntForEachEntry(vTouched, id, i) Vec_IntWriteEntry(vTruth, id, -1);
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks an imported truth table against the original cut cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CheckCut( Acec2_Man_t * p, int * pCut, Vec_Int_t * vTruth,
                    Vec_Int_t * vStack, Vec_Int_t * vTouched )
{
    int Truth = Acec2_EvaluateCut(p, pCut, vTruth, vStack, vTouched);
    return Truth >= 0 && !((Truth ^ pCut[5]) & ((1 << (1 << pCut[0]))-1));
}

/**Function*************************************************************

  Synopsis    [Classifies parity and carry truth tables on at most 3 inputs.]

  Description [Truth tables repeat to eight bits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CutClass( int n, int t )
{
    if ( n == 2 )
    {
        if ( t == 0x66 || t == 0x99 ) return 2;
        if ( t == 0x88 || t == 0x44 || t == 0x22 || t == 0x11 ||
             t == 0x77 || t == 0xBB || t == 0xDD || t == 0xEE ) return 1;
    }
    if ( n == 3 )
    {
        if ( t == 0x96 || t == 0x69 ) return 2;
        if ( t == 0xE8 || t == 0xD4 || t == 0xB2 || t == 0x71 ||
             t == 0x17 || t == 0x2B || t == 0x4D || t == 0x8E ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Merges sorted supports before any truth-table computation.]

  Description [Cut records contain size, three leaf IDs, and truth table.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CutMergeLeaves( int * a, int * b, int * c )
{
    int i = 0, j = 0;
    c[0] = c[1] = c[2] = c[3] = c[4] = 0;
    while ( i < a[0] || j < b[0] )
    {
        if ( c[0] == 3 ) return 0;
        if ( j == b[0] || (i < a[0] && a[i+1] < b[j+1]) )
            c[++c[0]] = a[++i];
        else if ( i == a[0] || b[j+1] < a[i+1] )
            c[++c[0]] = b[++j];
        else
        {
            c[++c[0]] = a[++i];
            j++;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes truth only for a new support.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CutTruth( int * a, int * b, int * c, int f0, int f1, int fXor )
{
    int i, k, m, u, v, t0, t1;
    c[4] = 0;
    for ( m = 0; m < 8; m++ )
    {
        u = v = 0;
        for ( i = 0; i < a[0]; i++ )
            for ( k = 0; k < c[0]; k++ )
                if ( a[i+1] == c[k+1] ) u |= ((m >> k) & 1) << i;
        for ( i = 0; i < b[0]; i++ )
            for ( k = 0; k < c[0]; k++ )
                if ( b[i+1] == c[k+1] ) v |= ((m >> k) & 1) << i;
        t0 = ((a[4] >> u) & 1) ^ f0;
        t1 = ((b[4] >> v) & 1) ^ f1;
        c[4] |= (fXor ? t0 ^ t1 : t0 & t1) << m;
    }
}

/**Function*************************************************************

  Synopsis    [Detects merged leaves that may intercept a child's cut cone.]

  Description [A leaf introduced by the other child is an independent input
  even when the first child has expanded it. Composing the two old tables
  would retain that expansion. Topological bounds exclude disjoint cones;
  the remaining merges are evaluated on the actual gates before pruning or
  propagation. False positives here affect cost only.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CutIntercepts( Gia_Man_t * g, int * a, int * b, int Root )
{
    int i, j;
    for ( i = 1; i <= b[0]; i++ )
    {
        if ( b[i] > Root || Gia_ObjIsCi(Gia_ManObj(g, b[i])) ) continue;
        for ( j = 1; j <= a[0]; j++ ) if ( b[i] == a[j] ) break;
        if ( j > a[0] ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Tests support containment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CutSubset( int * a, int * b )
{
    int i, k;
    if ( a[0] > b[0] ) return 0;
    for ( i = 1; i <= a[0]; i++ )
    {
        for ( k = 1; k <= b[0]; k++ ) if ( a[i] == b[k] ) break;
        if ( k > b[0] ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prunes a larger support only when its independent function agrees.]

  Description [A larger cut may expose an internal signal computed from the
  smaller cut's leaves. Its independent truth table can describe an adder
  that is lost by support containment alone. Compare functions after lifting
  the smaller table to the larger support before discarding either record.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CutSubsumes( int * a, int * b )
{
    int i, j, m, index;
    if ( !Acec2_CutSubset(a, b) ) return 0;
    for ( m = 0; m < 8; m++ )
    {
        index = 0;
        for ( i = 0; i < a[0]; i++ )
            for ( j = 0; j < b[0]; j++ )
                if ( a[i+1] == b[j+1] ) index |= ((m >> j) & 1) << i;
        if ( ((a[4] >> index) & 1) != ((b[4] >> m) & 1) ) return 0;
    }
    return 1;
}
/**Function*************************************************************

  Synopsis    [Unpacks compact stored cuts into working records.]

  Description [Stored records use three leaves and one size/truth word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CutUnpack( int * pStored, int * pCut )
{
    pCut[0] = pStored[3] & 3;
    pCut[1] = pStored[0]; pCut[2] = pStored[1]; pCut[3] = pStored[2];
    pCut[4] = pStored[3] >> 2;
}

/**Function*************************************************************

  Synopsis    [Orders function records by support, then output ID.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_FuncCompare( const void * p0, const void * p1 )
{
    const int * a = (const int *)p0, * b = (const int *)p1;
    int i;
    for ( i = 0; i < 6; i++ )
        if ( a[i] != b[i] ) return a[i] < b[i] ? -1 : 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Retains discovered arithmetic cuts independently of propagation.]

  Description [The per-node cut budget bounds propagation to later gates.
  A checked parity or carry at this node remains evidence even when its
  support cannot be retained for propagation. Duplicate records are local
  to the current node and are removed before allocating candidate pairs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_RecordCut( Acec2_Man_t * p, Vec_Int_t * vFuncs, int Start, int * Cut, int Id, int Class,
                            Vec_Int_t ** vCheck )
{
    int i, k, Truth = Cut[4], Check[6];
    for ( i = Start; i < Vec_IntSize(vFuncs); i += 6 )
        if ( !memcmp(Vec_IntEntryP(vFuncs, i), Cut, 4*sizeof(int)) ) return 1;
    if ( vCheck )
    {
        memcpy(Check, Cut, 4*sizeof(int)); Check[4] = Id;
        Truth = Acec2_EvaluateCut(p, Check, vCheck[0], vCheck[1], vCheck[2]);
        p->nCutChecks++;
        if ( Truth >= 0 && Truth != Cut[4] ) p->nCutCorrections++;
        Class = Truth < 0 ? 0 : Acec2_CutClass(Cut[0], Truth);
        if ( !Class ) { p->nUnconfirmedCuts++; return !p->fStopped; }
    }
    if ( Vec_IntSize(vFuncs) > ABC_INT_MAX/2-6 || Vec_IntSize(p->vCarries) > ABC_INT_MAX/2-6 ||
         Vec_IntSize(p->vXors) > ABC_INT_MAX/2-5 )
    {
        p->fStopped = p->fStorageLimit = 1;
        return 0;
    }
    for ( k = 0; k < 4; k++ ) Vec_IntPush(vFuncs, Cut[k]);
    Vec_IntPushTwo(vFuncs, Id, Truth);
    if ( Class == 1 )
    {
        for ( k = 0; k < 4; k++ ) Vec_IntPush(p->vCarries, Cut[k]);
        Vec_IntPushTwo(p->vCarries, Id, Truth);
    }
    if ( Class == 2 )
    {
        Vec_IntPush(p->vXorNext, Vec_IntEntry(p->vXorFirst, Id));
        Vec_IntWriteEntry(p->vXorFirst, Id, Vec_IntSize(p->vXors)/5);
        for ( k = 0; k < 4; k++ ) Vec_IntPush(p->vXors, Cut[k]);
        Vec_IntPush(p->vXors, Abc_Var2Lit(Id, Truth == 0x99 || Truth == 0x69));
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Restores XOR3 cuts by composing retained XOR2 relations.]

  Description [The parity index retains every discovered decomposition.
  Combining adjacent XORs proposes arithmetic supports lost by propagation
  budgets. Re-evaluate each new cut on independent leaves before admitting
  it. A repeated leaf cancels parity and does not propose a full-adder cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ExpandXors( Acec2_Man_t * p, Vec_Int_t * vFuncs, Vec_Bit_t * vLimited )
{
    Vec_Int_t * vNew, * vTruth, * vStack, * vTouched;
    int i, j, k, leaf, other, root, phase, lo, hi, mid, cmp, pos, Cut[6], Prev[6];
    int nFuncs = Vec_IntSize(vFuncs)/6, nXors = Vec_IntSize(p->vXors)/5;
    ABC_INT64_T steps = 0, Budget = 16*(ABC_INT64_T)Gia_ManObjNum(p->pGia);
    if ( !p->nCutLimits || p->fStopped ) return;
    vNew = Vec_IntAlloc(100);
    for ( i = 0; i < nXors; i++ )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(p) ) break;
        if ( Vec_IntEntry(p->vXors, 5*i) != 2 ) continue;
        root = Vec_IntEntry(p->vXors, 5*i+4) >> 1;
        if ( !Vec_BitEntry(vLimited, root) ) continue;
        for ( j = 0; j < 2; j++ )
        {
            leaf = Vec_IntEntry(p->vXors, 5*i+1+j);
            other = Vec_IntEntry(p->vXors, 5*i+2-j);
            for ( k = Vec_IntEntry(p->vXorFirst, leaf); k >= 0; k = Vec_IntEntry(p->vXorNext, k) )
            {
                if ( ++steps > Budget || Vec_IntSize(vNew) > ABC_INT_MAX/2-6 )
                { p->nXorExpansionLimits++; goto collected; }
                if ( Vec_IntEntry(p->vXors, 5*k) != 2 ) continue;
                Cut[0] = 3; Cut[1] = other;
                Cut[2] = Vec_IntEntry(p->vXors, 5*k+1); Cut[3] = Vec_IntEntry(p->vXors, 5*k+2);
                if ( Cut[1] > Cut[2] ) ABC_SWAP(int, Cut[1], Cut[2]);
                if ( Cut[2] > Cut[3] ) ABC_SWAP(int, Cut[2], Cut[3]);
                if ( Cut[1] > Cut[2] ) ABC_SWAP(int, Cut[1], Cut[2]);
                if ( Cut[1] == Cut[2] || Cut[2] == Cut[3] ) continue;
                Cut[4] = root;
                phase = (Vec_IntEntry(p->vXors, 5*i+4) ^ Vec_IntEntry(p->vXors, 5*k+4)) & 1;
                Cut[5] = phase ? 0x69 : 0x96;
                lo = 0; hi = nFuncs;
                while ( lo < hi )
                {
                    mid = lo+(hi-lo)/2;
                    cmp = Acec2_FuncCompare(Vec_IntEntryP(vFuncs, 6*mid), Cut);
                    if ( cmp < 0 ) lo = mid+1;
                    else hi = mid;
                }
                if ( lo < nFuncs && !Acec2_FuncCompare(Vec_IntEntryP(vFuncs, 6*lo), Cut) ) continue;
                for ( pos = 0; pos < 6; pos++ ) Vec_IntPush(vNew, Cut[pos]);
            }
        }
    }
collected:
    qsort(Vec_IntArray(vNew), Vec_IntSize(vNew)/6, 6*sizeof(int), Acec2_FuncCompare);
    vTruth = Vec_IntStartFull(Gia_ManObjNum(p->pGia)); Vec_IntWriteEntry(vTruth, 0, 0);
    vStack = Vec_IntAlloc(32); vTouched = Vec_IntAlloc(32);
    memset(Prev, 0, sizeof(Prev));
    for ( i = 0; i < Vec_IntSize(vNew); i += 6 )
    {
        if ( Acec2_Stopped(p) ) break;
        memcpy(Cut, Vec_IntEntryP(vNew, i), sizeof(Cut));
        if ( !memcmp(Cut, Prev, sizeof(Cut)) ) continue;
        memcpy(Prev, Cut, sizeof(Cut));
        if ( !Acec2_CheckCut(p, Cut, vTruth, vStack, vTouched) ) continue;
        root = Cut[4]; Cut[4] = Cut[5];
        if ( !Acec2_RecordCut(p, vFuncs, Vec_IntSize(vFuncs), Cut, root, 2, NULL) ) break;
        p->nXorExpanded++;
    }
    Vec_IntFree(vNew); Vec_IntFree(vTruth); Vec_IntFree(vStack); Vec_IntFree(vTouched);
}

/**Function*************************************************************

  Synopsis    [Completes arithmetic supports affected by propagation limits.]

  Description [For each support with a known parity, propagate exact tables
  through a bounded local
  fanout closure. The support signals are independent inputs and their own
  definitions are never traversed. This recovers remote sums and carries
  without retaining more cuts at every intervening gate. All scratch is
  private. Per-support and total edge budgets bound reconvergent closures.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_RecoverCuts( Acec2_Man_t * p, Vec_Int_t * vFuncs )
{
    Gia_Man_t * g = p->pGia;
    Vec_Int_t * vStarts, * vCursor, * vFans, * vKnown, * vRecorded, * vQueue;
    Gia_Obj_t * o;
    unsigned char * pTruth;
    int i, j, k, id, fan, a, b, t, cls, end, stamp = 0, affected, work, Cut[5];
    int n = Gia_ManObjNum(g), nFuncs = Vec_IntSize(vFuncs);
    ABC_INT64_T Budget = 32*(ABC_INT64_T)n;
    if ( !p->nCutLimits || !nFuncs || p->fStopped ) return;
    if ( n >= ABC_INT_MAX/2 || Gia_ManAndNum(g) >= ABC_INT_MAX/4 )
    { p->nRecoveryLimits++; return; }
    vStarts = Vec_IntStart(n+1);
    Gia_ManForEachAnd(g, o, i)
        if ( !Gia_ObjIsMux(g, o) )
        {
            Vec_IntAddToEntry(vStarts, Gia_ObjFaninId0(o, i)+1, 1);
            Vec_IntAddToEntry(vStarts, Gia_ObjFaninId1(o, i)+1, 1);
        }
    for ( i = 1; i <= n; i++ ) Vec_IntAddToEntry(vStarts, i, Vec_IntEntry(vStarts, i-1));
    vCursor = Vec_IntDup(vStarts); vFans = Vec_IntStart(Vec_IntEntry(vStarts, n));
    Gia_ManForEachAnd(g, o, i)
        if ( !Gia_ObjIsMux(g, o) )
            for ( k = 0; k < 2; k++ )
            {
                id = k ? Gia_ObjFaninId1(o, i) : Gia_ObjFaninId0(o, i);
                Vec_IntWriteEntry(vFans, Vec_IntEntry(vCursor, id), i);
                Vec_IntAddToEntry(vCursor, id, 1);
            }
    Vec_IntFree(vCursor);
    vKnown = Vec_IntStart(n); vRecorded = Vec_IntStart(n); vQueue = Vec_IntAlloc(128);
    pTruth = ABC_ALLOC(unsigned char, n);
    for ( i = 0; i < nFuncs; i = end )
    {
        if ( Acec2_Stopped(p) ) break;
        if ( p->nRecoverySteps >= Budget ) { p->nRecoveryLimits++; break; }
        memcpy(Cut, Vec_IntEntryP(vFuncs, i), 4*sizeof(int)); affected = 0;
        for ( end = i; end < nFuncs; end += 6 )
        {
            if ( memcmp(Cut, Vec_IntEntryP(vFuncs, end), 4*sizeof(int)) ) break;
            affected |= Acec2_CutClass(Cut[0], Vec_IntEntry(vFuncs, end+5)) == 2;
        }
        if ( !affected ) continue;
        stamp++; Vec_IntClear(vQueue);
        Vec_IntWriteEntry(vKnown, 0, stamp); pTruth[0] = 0;
        for ( j = i; j < end; j += 6 ) Vec_IntWriteEntry(vRecorded, Vec_IntEntry(vFuncs, j+4), stamp);
        for ( j = 0; j < Cut[0]; j++ )
        {
            id = Cut[j+1]; Vec_IntWriteEntry(vKnown, id, stamp);
            pTruth[id] = (unsigned char)(j == 0 ? 0xAA : j == 1 ? 0xCC : 0xF0);
            Vec_IntPush(vQueue, id);
        }
        work = 0;
        for ( j = 0; j < Vec_IntSize(vQueue); j++ )
        {
            id = Vec_IntEntry(vQueue, j);
            for ( k = Vec_IntEntry(vStarts, id); k < Vec_IntEntry(vStarts, id+1); k++ )
            {
                if ( ++work > 4096 || ++p->nRecoverySteps > Budget )
                { p->nRecoveryLimits++; goto next_support; }
                if ( !(work & 255) && Acec2_Stopped(p) ) goto finish;
                fan = Vec_IntEntry(vFans, k);
                if ( Vec_IntEntry(vKnown, fan) == stamp ) continue;
                o = Gia_ManObj(g, fan); a = Gia_ObjFaninId0(o, fan); b = Gia_ObjFaninId1(o, fan);
                if ( Vec_IntEntry(vKnown, a) != stamp || Vec_IntEntry(vKnown, b) != stamp ) continue;
                a = pTruth[a] ^ (Gia_ObjFaninC0(o) ? 255 : 0);
                b = pTruth[b] ^ (Gia_ObjFaninC1(o) ? 255 : 0);
                t = Gia_ObjIsXor(o) ? a ^ b : a & b;
                Vec_IntWriteEntry(vKnown, fan, stamp); pTruth[fan] = (unsigned char)t;
                Vec_IntPush(vQueue, fan);
                cls = Acec2_CutClass(Cut[0], t);
                if ( !cls || Vec_IntEntry(vRecorded, fan) == stamp ) continue;
                Cut[4] = t;
                if ( !Acec2_RecordCut(p, vFuncs, Vec_IntSize(vFuncs), Cut, fan, cls, NULL) ) goto finish;
                Vec_IntWriteEntry(vRecorded, fan, stamp); p->nRecoveredCuts++;
            }
        }
next_support: ;
    }
finish:
    ABC_FREE(pTruth); Vec_IntFree(vKnown); Vec_IntFree(vRecorded); Vec_IntFree(vQueue);
    Vec_IntFree(vStarts); Vec_IntFree(vFans);
}

/**Function*************************************************************

  Synopsis    [Finds and exhaustively validates a phased HA/FA identity.]

  Description [All phases refer to literals, not simulation signatures.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Acec2_Cell_t * Acec2_MatchCut( int * s, int * c )
{
    int phase, cs, ss, m, k, count, ok;
    for ( cs = 0; cs < 2; cs++ )
    for ( phase = 0; phase < (1 << s[0]); phase++ )
    {
        ss = (s[5] & 1);
        for ( k = 0; k < s[0]; k++ ) ss ^= (phase >> k) & 1;
        ok = 1;
        for ( m = 0; m < 8; m++ )
        {
            count = 0;
            for ( k = 0; k < s[0]; k++ ) count += ((m ^ phase) >> k) & 1;
            if ( count != (((s[5] >> m) & 1) ^ ss) + 2*(((c[5] >> m) & 1) ^ cs) )
            {
                ok = 0;
                break;
            }
        }
        if ( ok )
        {
            Acec2_Cell_t * p = ABC_CALLOC( Acec2_Cell_t, 1 );
            p->nIns = s[0];
            p->Tree = -1;
            p->In[2] = -1;
            for ( k = 0; k < s[0]; k++ ) p->In[k] = Abc_Var2Lit( s[k+1], (phase >> k) & 1 );
            p->Out[0] = Abc_Var2Lit( s[4], ss );
            p->Out[1] = Abc_Var2Lit( c[4], cs );
            return p;
        }
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Prefers full adders and carries with useful external fanout.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CellCompare( const void * p0, const void * p1 )
{
    const Acec2_Cell_t * a = *(Acec2_Cell_t * const *)p0;
    const Acec2_Cell_t * b = *(Acec2_Cell_t * const *)p1;
    int i;
    // Establish the independent gate-cut cover first. Source-constrained
    // alternatives remain available for region composition, but should not
    // replace its interfaces merely because an equivalent carry has a
    // larger gate number.
    if ( (a->Proof == 0) != (b->Proof == 0) ) return a->Proof ? 1 : -1;
    if ( a->nIns != b->nIns ) return a->nIns > b->nIns ? -1 : 1;
    // Both polarities belong to the same parity node. Choose its observed
    // carry before using arbitrary literal phase as a tie breaker.
    if ( (a->Out[0] >> 1) != (b->Out[0] >> 1) ) return (a->Out[0] >> 1) > (b->Out[0] >> 1) ? -1 : 1;
    if ( a->Ext[1] != b->Ext[1] ) return a->Ext[1] > b->Ext[1] ? -1 : 1;
    if ( a->Out[1] != b->Out[1] ) return a->Out[1] > b->Out[1] ? -1 : 1;
    if ( a->Out[0] != b->Out[0] ) return a->Out[0] > b->Out[0] ? -1 : 1;
    for ( i = 0; i < 3; i++ )
        if ( a->In[i] != b->In[i] ) return a->In[i] < b->In[i] ? -1 : 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Prefers complete checked adders over two-input decompositions.]

  Description [The reconstruction cover keeps its original independent-cut
  ordering. Profiling instead selects a full adder before its two-input
  decomposition. Recovered cells retain their source-domain proof; this
  ordering does not promote them to independent-cut identities. Carry
  polarity selection retains the existing operand boundaries.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CellCompareClosure( const void * p0, const void * p1 )
{
    const Acec2_Cell_t * a = *(Acec2_Cell_t * const *)p0;
    const Acec2_Cell_t * b = *(Acec2_Cell_t * const *)p1;
    if ( a->nIns != b->nIns ) return a->nIns > b->nIns ? -1 : 1;
    return Acec2_CellCompare(p0, p1);
}

/**Function*************************************************************

  Synopsis    [Collects a cell interior without modifying GIA scratch.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CellCone( Acec2_Man_t * p, Acec2_Cell_t * c, Vec_Int_t * vMarks,
                          int Stamp, Vec_Int_t * vStack, Vec_Int_t * vInside )
{
    Gia_Obj_t * o; int id, k, leaf;
    Vec_IntClear(vStack); Vec_IntClear(vInside);
    if ( c->Proof && (((Acec2_Proof_t *)Vec_PtrEntry(p->vProofs, c->Proof-1))->Kind == 2 ||
                     ((Acec2_Proof_t *)Vec_PtrEntry(p->vProofs, c->Proof-1))->Kind == 4) )
    {
        // Both outputs use source-constrained proofs. Their complete cones
        // are proof support; only the endpoints are claimed as footprint.
        Vec_IntPushTwo(vInside, c->Out[0] >> 1, c->Out[1] >> 1); return 1;
    }
    Vec_IntPush(vStack, Abc_Lit2Var(c->Out[0]));
    if ( !c->Proof ) Vec_IntPush(vStack, Abc_Lit2Var(c->Out[1]));
    while ( Vec_IntSize(vStack) )
    {
        id = Vec_IntPop(vStack); leaf = 0;
        for ( k = 0; k < c->nIns; k++ ) leaf |= id == Abc_Lit2Var(c->In[k]);
        if ( leaf || id == 0 || Vec_IntEntry(vMarks, id) == Stamp ) continue;
        Vec_IntWriteEntry(vMarks, id, Stamp);
        o = Gia_ManObj(p->pGia, id);
        if ( !Gia_ObjIsAnd(o) || Gia_ObjIsMux(p->pGia, o) ) return 0;
        Vec_IntPush(vInside, id);
        Vec_IntPushTwo(vStack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
    }
    // A functional carry can depend on the same values through a different
    // cone. Its proof support is stored separately; count only its endpoint
    // and the sum implementation as the conservative cell footprint.
    if ( c->Proof ) Vec_IntPushUnique(vInside, Abc_Lit2Var(c->Out[1]));
    return 1;
}

/**Function*************************************************************

  Synopsis    [Identifies reassociated half adders inside a selected full adder.]

  Description [Only a cover preference is inferred. These identities remain
  available as alternatives, with their original exact source certificates.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_HalfInside( Acec2_Man_t * p, Acec2_Cell_t * c, Vec_Ptr_t * cells, Vec_Wec_t * users, Vec_Int_t * stack )
{
    Acec2_Cell_t * fa; Gia_Obj_t * o; int i, j, id, cell, found, steps;
    if ( c->nIns != 2 || !c->Proof ||
         ((Acec2_Proof_t *)Vec_PtrEntry(p->vProofs, c->Proof-1))->Kind != 4 ) return 0;
    Vec_IntForEachEntry(Vec_WecEntry(users, c->In[0] >> 1), cell, i)
    {
        if ( i == 64 ) break;
        fa = (Acec2_Cell_t *)Vec_PtrEntry(cells, cell); found = 0;
        for ( j = 0; j < 3; j++ ) found |= (fa->In[j] >> 1) == (c->In[1] >> 1);
        if ( !found ) continue;
        Vec_IntClear(stack); Vec_IntPush(stack, fa->Out[1] >> 1); steps = 0;
        while ( Vec_IntSize(stack) && steps++ < 1024 )
        {
            id = Vec_IntPop(stack);
            if ( id == (c->Out[1] >> 1) ) return 1;
            found = !id;
            for ( j = 0; j < 3; j++ ) found |= (fa->In[j] >> 1) == id;
            if ( found ) continue;
            o = Gia_ManObj(p->pGia, id); if ( !Gia_ObjIsAnd(o) ) continue;
            Vec_IntPushTwo(stack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
            if ( Gia_ObjIsMux(p->pGia, o) ) Vec_IntPush(stack, Gia_ObjFaninId2(p->pGia, id));
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Orders borrowed cell choices using the profiling preference.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ChoiceCompare( const void * p0, const void * p1 )
{
    const Acec2_Choice_t * a = (const Acec2_Choice_t *)p0, * b = (const Acec2_Choice_t *)p1;
    int result = Acec2_CellCompareClosure(&a->pCell, &b->pCell);
    return result ? result : (a->KindId > b->KindId)-(a->KindId < b->KindId);
}

/**Function*************************************************************

  Synopsis    [Selects an independent arithmetic partition for checked records.]

  Description [All cells remain in their original pools. Complete adders
  precede their half-adder decompositions; output ownership is unique while
  implementation gates may overlap. This view never changes the cover used
  for reconstruction, source node metadata, or existing cell/record IDs.]

  SideEffects [Returns owned (cell kind, index) pairs; limits are counted.]

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Acec2_RecordCover( Acec2_Man_t * m )
{
    Vec_Int_t * result = Vec_IntAlloc(100), * gates, * stack, * full;
    Vec_Ptr_t * selected;
    Vec_Wec_t * users;
    Vec_Bit_t * owned, * covered, * chain;
    Acec2_Choice_t * choices;
    Acec2_Cell_t * c, * fa;
    Acec2_Proof_t * proof;
    int i, j, k, n, kind, id, count = 0, fresh, owner, matched, phase, nextPhase, reject;
    if ( Acec2_Stopped(m) ) return result;
    if ( (ABC_INT64_T)Vec_PtrSize(m->vCells)+Vec_PtrSize(m->vAlternatives) > 10000000 )
    { m->nRecordLimits++; return result; }
    n = Vec_PtrSize(m->vCells)+Vec_PtrSize(m->vAlternatives);
    if ( !n ) return result;
    choices = ABC_ALLOC(Acec2_Choice_t, n);
    for ( kind = 0; kind < 2; kind++ )
        Vec_PtrForEachEntry(Acec2_Cell_t *, kind ? m->vAlternatives : m->vCells, c, i)
        { choices[count].pCell = c; choices[count++].KindId = 2*i+kind; }
    qsort(choices, n, sizeof(Acec2_Choice_t), Acec2_ChoiceCompare);
    owned = Vec_BitStart(Gia_ManObjNum(m->pGia)); covered = Vec_BitStart(Gia_ManObjNum(m->pGia));
    chain = Vec_BitStart(Gia_ManObjNum(m->pGia)); full = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
    users = Vec_WecStart(Gia_ManObjNum(m->pGia)); selected = Vec_PtrAlloc(100); stack = Vec_IntAlloc(100);
    for ( i = 0; i < n; i++ )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(m) ) break;
        c = choices[i].pCell; kind = choices[i].KindId & 1; id = choices[i].KindId >> 1;
        if ( Vec_BitEntry(owned, c->Out[0] >> 1) || Vec_BitEntry(owned, c->Out[1] >> 1) ) continue;
        proof = c->Proof ? (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, c->Proof-1) : NULL;
        if ( proof && proof->Kind == 2 && !proof->fBoundary ) continue;
        gates = Vec_WecEntry(kind ? m->vAltGates : m->vCellGates, id); fresh = 0;
        Vec_IntForEachEntry(gates, j, k) if ( !Vec_BitEntry(covered, j) ) { fresh = 1; break; }
        if ( !fresh || Acec2_HalfInside(m, c, selected, users, stack) ) continue;
        reject = c->nIns == 2 && Vec_BitEntry(chain, c->Out[0] >> 1) && Vec_BitEntry(chain, c->Out[1] >> 1);
        owner = Vec_IntEntry(full, c->Out[0] >> 1);
        if ( c->nIns == 2 && owner >= 0 )
        {
            fa = (Acec2_Cell_t *)Vec_PtrEntry(selected, owner); matched = 0; phase = -1;
            for ( j = 0; j < 2; j++ )
                for ( k = 0; k < 3; k++ )
                    if ( (c->In[j] >> 1) == (fa->In[k] >> 1) )
                    {
                        nextPhase = (c->In[j] ^ fa->In[k]) & 1;
                        if ( fa->Proof || phase < 0 || phase == nextPhase ) { phase = nextPhase; matched++; }
                        break;
                    }
            reject |= matched == 2;
        }
        if ( reject ) continue;
        if ( c->nIns == 3 )
        {
            for ( j = 0; j < 3; j++ ) Vec_WecPush(users, c->In[j] >> 1, Vec_PtrSize(selected));
            Vec_IntForEachEntry(gates, j, k) if ( Vec_IntEntry(full, j) < 0 ) Vec_IntWriteEntry(full, j, Vec_PtrSize(selected));
            if ( proof && proof->vChain )
            {
                Acec2_BitWrite(chain, Vec_IntEntry(proof->vChain, 2) >> 1, 1);
                Acec2_BitWrite(chain, Vec_IntEntry(proof->vChain, 3) >> 1, 1);
            }
        }
        Vec_PtrPush(selected, c); Vec_IntPushTwo(result, kind, id);
        Vec_IntForEachEntry(gates, j, k) Acec2_BitWrite(covered, j, 1);
        for ( j = 0; j < 2; j++ ) Acec2_BitWrite(owned, c->Out[j] >> 1, 1);
    }
    if ( Acec2_Stopped(m) ) Vec_IntClear(result);
    ABC_FREE(choices); Vec_IntFree(stack); Vec_IntFree(full); Vec_PtrFree(selected); Vec_WecFree(users);
    Vec_BitFree(owned); Vec_BitFree(covered); Vec_BitFree(chain);
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks source footprint and external carry fanout for a cell.]

  Description [The same filter admits candidates during initial detection
  and incremental recognition. An unused XOR interior is parity evidence.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_PrepareCell( Acec2_Man_t * p, Acec2_Cell_t * c, Vec_Int_t * marks,
                              int stamp, Vec_Int_t * stack, Vec_Int_t * inside )
{
    Gia_Obj_t * o; int j, k, id;
    if ( p->vFocus && (!Vec_BitEntry(p->vFocus, c->Out[0] >> 1) || !Vec_BitEntry(p->vFocus, c->Out[1] >> 1)) ) return 0;
    if ( Acec2_Stopped(p) || !Acec2_CellCone(p, c, marks, stamp, stack, inside) ) return 0;
    for ( j = 0; j < 2; j++ )
    {
        c->Ext[j] = Vec_IntEntry(p->vRefs, c->Out[j] >> 1);
        Vec_IntForEachEntry(inside, id, k)
        {
            o = Gia_ManObj(p->pGia, id);
            c->Ext[j] -= Gia_ObjFaninId0(o, id) == (c->Out[j] >> 1);
            c->Ext[j] -= Gia_ObjFaninId1(o, id) == (c->Out[j] >> 1);
        }
        assert(c->Ext[j] >= 0);
    }
    c->Ext[1] = Acec2_ParityCarryRefs(p, c, marks, -stamp, stack);
    if ( c->Ext[1] ) return 1;
    if ( c->nIns == 2 && Vec_IntSize(p->vVanish) <= ABC_INT_MAX-5 )
    {
        Vec_IntPushTwo(p->vVanish, c->In[0], c->In[1]);
        Vec_IntPushTwo(p->vVanish, c->Out[0], c->Out[1]); Vec_IntPush(p->vVanish, c->Proof);
    }
    p->nCarryFiltered++; return 0;
}

/**Function*************************************************************

  Synopsis    [Imports checked alternatives without changing existing cell IDs.]

  Description [All candidates are consumed. Exact duplicate identities are
  discarded; accepted footprints use the same carry filter as detection.]

  SideEffects [Appends alternatives, never modifies the primary cover.]

  SeeAlso     []

***********************************************************************/
int Acec2_ImportCells( Acec2_Man_t * m, Vec_Ptr_t * candidates )
{
    Hsh_VecMan_t * seen = Hsh_VecManStart(100);
    Vec_Int_t * key = Vec_IntAlloc(6), * marks = Vec_IntStart(Gia_ManObjNum(m->pGia));
    Vec_Int_t * stack = Vec_IntAlloc(32), * inside = Vec_IntAlloc(32);
    Acec2_Cell_t * c; Vec_Ptr_t * cells;
    int kind, i, k, old, added = 0;
    for ( kind = 0; kind < 3; kind++ )
    {
        cells = kind == 2 ? candidates : kind ? m->vAlternatives : m->vCells;
        Vec_PtrForEachEntry(Acec2_Cell_t *, cells, c, i)
        {
            Vec_IntClear(key); Vec_IntPush(key, c->nIns);
            for ( k = 0; k < 3; k++ ) Vec_IntPush(key, c->In[k]);
            Vec_IntPushTwo(key, c->Out[0], c->Out[1]); old = Hsh_VecSize(seen);
            k = Hsh_VecManAdd(seen, key);
            if ( kind != 2 ) continue;
            if ( k < old || !Acec2_PrepareCell(m, c, marks, i+1, stack, inside) ) { ABC_FREE(c); continue; }
            Vec_PtrPush(m->vAlternatives, c); Vec_IntAppend(Vec_WecPushLevel(m->vAltGates), inside); added++;
        }
    }
    m->nCandidates += Vec_PtrSize(candidates); Vec_PtrClear(candidates);
    Hsh_VecManStop(seen); Vec_IntFree(key); Vec_IntFree(marks); Vec_IntFree(stack); Vec_IntFree(inside);
    return added;
}

/**Function*************************************************************

  Synopsis    [Selects a cover and retains all checked alternatives.]

  Description [A reassociated half adder inside a selected full adder stays
  in the alternative database. Selecting both would count its operands twice.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_Select( Acec2_Man_t * p, Vec_Ptr_t * vCandidates )
{
    Vec_Int_t * vMarks = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Vec_Bit_t * vCovered = Vec_BitStart( Gia_ManObjNum(p->pGia) );
    Vec_Bit_t * vDisjoint = Vec_BitStart( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vFaOwner = Vec_IntStartFull(Gia_ManObjNum(p->pGia));
    Vec_Bit_t * vChainInside = Vec_BitStart(Gia_ManObjNum(p->pGia));
    Vec_Wec_t * vFaUsers = p->fFast && p->fSingleUse ? NULL : Vec_WecStart(Gia_ManObjNum(p->pGia));
    Vec_Int_t * vStack = Vec_IntAlloc( 32 ), * vInside = Vec_IntAlloc( 32 );
    Acec2_Cell_t * pCell;
    int i, k, j, Id, fOverlap, fDisjoint, n = Vec_PtrSize(p->vCells), kept = 0, nAll = Vec_PtrSize(vCandidates), owner, matched, phase, fresh;
    for ( i = 0; i < Vec_IntSize(p->vDisjoint); i += 2 )
        Vec_IntForEachEntry(Vec_WecEntry(Vec_IntEntry(p->vDisjoint, i) ? p->vAltGates : p->vCellGates,
            Vec_IntEntry(p->vDisjoint, i+1)), Id, k) Acec2_BitWrite(vDisjoint, Id, 1);
    Vec_PtrForEachEntry(Acec2_Cell_t *, p->vCells, pCell, i)
    {
        if ( vFaUsers && pCell->nIns == 3 ) for ( k = 0; k < 3; k++ ) Vec_WecPush(vFaUsers, pCell->In[k] >> 1, i);
        Vec_IntForEachEntry(Vec_WecEntry(p->vCellGates, i), Id, k)
        {
            Acec2_BitWrite(vCovered, Id, 1);
            if ( pCell->nIns == 3 && Vec_IntEntry(vFaOwner, Id) < 0 ) Vec_IntWriteEntry(vFaOwner, Id, i);
        }
    }
    // An XOR's private implementation gates are not an observed carry.
    Vec_PtrForEachEntry( Acec2_Cell_t *, vCandidates, pCell, i )
    {
        if ( !Acec2_PrepareCell(p, pCell, vMarks, i+1, vStack, vInside) )
        { ABC_FREE(pCell); continue; }
        Vec_PtrWriteEntry(vCandidates, kept++, pCell);
    }
    Vec_PtrShrink(vCandidates, kept);
    Vec_IntFill(vMarks, Gia_ManObjNum(p->pGia), 0); nAll = Vec_PtrSize(vCandidates);
    qsort( Vec_PtrArray(vCandidates), Vec_PtrSize(vCandidates), sizeof(void *),
        p->fFast && p->fSingleUse ? Acec2_CellCompare : Acec2_CellCompareClosure );
    Vec_PtrForEachEntry( Acec2_Cell_t *, vCandidates, pCell, i )
    {
        if ( p->fStopped || ((i & 255) == 0 && Acec2_Stopped(p)) )
        {
            ABC_FREE( pCell );
            continue;
        }
        fOverlap = !Acec2_CellCone(p, pCell, vMarks, nAll+i+1, vStack, vInside);
        // The initial CEC reconstruction uses an interior-disjoint cover.
        // Keep other exact decompositions as alternatives for records and
        // later recognition. Standalone profiling retains unique outputs
        // and permits shared implementation gates in its selected cover.
        if ( p->fFast && p->fSingleUse )
            Vec_IntForEachEntry(vInside, Id, k)
                if ( Vec_BitEntry(vCovered, Id) ) { fOverlap = 1; break; }
        if ( pCell->Proof )
        {
            Acec2_Proof_t * proof = (Acec2_Proof_t *)Vec_PtrEntry(p->vProofs, pCell->Proof-1);
            // Preserve the existing arithmetic interfaces. Recovered source
            // decompositions extend a separate checked region cover, so they
            // cannot hide a previously recognized word or operand sum.
            if ( proof->Kind == 2 || (proof->Kind == 4 && p->fFast && p->fSingleUse) ) fOverlap = 1;
        }
        for ( k = 0; k < 2; k++ )
            if ( Vec_IntEntry(p->vOwner, Abc_Lit2Var(pCell->Out[k])) >= 0 ) fOverlap = 1;
        fresh = 0;
        Vec_IntForEachEntry(vInside, Id, k) fresh += !Vec_BitEntry(vCovered, Id);
        // An identity entirely inside the existing implementation is a
        // retained alternative decomposition, not another arithmetic stage.
        // Interior sharing is allowed when the candidate extends the cover.
        if ( !fresh ) fOverlap = 1;
        if ( !fOverlap && vFaUsers && Acec2_HalfInside(p, pCell, p->vCells, vFaUsers, vStack) ) fOverlap = 1;
        // A two-input decomposition of a selected FA remains an alternative.
        // Selecting both counts the same arithmetic operation twice and leaves
        // the decomposed carry as a spurious extra boundary. Other interior
        // overlap is permitted, including implementations with shared gates.
        owner = Vec_IntEntry(vFaOwner, pCell->Out[0] >> 1);
        if ( pCell->nIns == 2 && Vec_BitEntry(vChainInside, pCell->Out[0] >> 1) &&
             Vec_BitEntry(vChainInside, pCell->Out[1] >> 1) ) fOverlap = 1;
        if ( pCell->nIns == 2 && owner >= 0 )
        {
            Acec2_Cell_t * fa = Acec2_Cell(p, owner);
            matched = 0; phase = -1;
            for ( k = 0; k < 2; k++ )
                for ( j = 0; j < 3; j++ )
                    if ( (pCell->In[k] >> 1) == (fa->In[j] >> 1) )
                    {
                        Id = (pCell->In[k] ^ fa->In[j]) & 1;
                        if ( (!p->fFast && fa->Proof) || phase < 0 || phase == Id ) { phase = Id; matched++; }
                        break;
                    }
            if ( matched == 2 ) fOverlap = 1;
        }
        // Preserve a second independent interpretation instead of assuming
        // that allowing shared interiors always improves word connectivity.
        // Both covers refer to the same checked cells; neither owns them.
        fDisjoint = !pCell->Proof;
        Vec_IntForEachEntry(vInside, Id, k) if ( Vec_BitEntry(vDisjoint, Id) ) fDisjoint = 0;
        if ( fDisjoint )
        {
            Vec_IntPushTwo(p->vDisjoint, fOverlap ? 1 : 0, fOverlap ? Vec_PtrSize(p->vAlternatives) : n);
            Vec_IntForEachEntry(vInside, Id, k) Acec2_BitWrite(vDisjoint, Id, 1);
        }
        if ( fOverlap )
        {
            Vec_PtrPush(p->vAlternatives, pCell);
            Vec_IntAppend(Vec_WecPushLevel(p->vAltGates), vInside); continue;
        }
        if ( pCell->nIns == 3 )
        {
            if ( vFaUsers ) for ( k = 0; k < 3; k++ ) Vec_WecPush(vFaUsers, pCell->In[k] >> 1, n);
            if ( pCell->Proof )
            {
                Acec2_Proof_t * proof = (Acec2_Proof_t *)Vec_PtrEntry(p->vProofs, pCell->Proof-1);
                if ( proof->vChain )
                {
                    Acec2_BitWrite(vChainInside, Vec_IntEntry(proof->vChain, 2) >> 1, 1);
                    Acec2_BitWrite(vChainInside, Vec_IntEntry(proof->vChain, 3) >> 1, 1);
                }
            }
            Vec_IntForEachEntry(vInside, Id, k)
                if ( Vec_IntEntry(vFaOwner, Id) < 0 ) Vec_IntWriteEntry(vFaOwner, Id, n);
        }
        Vec_IntForEachEntry( vInside, Id, k )
        {
            if ( !Vec_BitEntry(vCovered, Id) )
            {
                p->nCovered++; Acec2_BitWrite(vCovered, Id, 1);
                Vec_IntWriteEntry(p->vNodeCell, Id, n);
            }
            else Vec_IntWriteEntry(p->vNodeCell, Id, -2);
        }
        p->nFadds += pCell->nIns == 3;
        p->nHadds += pCell->nIns == 2;
        Vec_IntWriteEntry( p->vOwner, Abc_Lit2Var(pCell->Out[0]), 2*n );
        Vec_IntWriteEntry( p->vOwner, Abc_Lit2Var(pCell->Out[1]), 2*n+1 );
        Vec_PtrPush( p->vCells, pCell );
        Vec_IntAppend(Vec_WecPushLevel(p->vCellGates), vInside);
        n++;
    }
    Vec_IntFree( vMarks );
    Vec_BitFree( vCovered );
    Vec_BitFree( vDisjoint );
    Vec_IntFree(vFaOwner);
    Vec_BitFree(vChainInside);
    Vec_WecFreeP(&vFaUsers);
    Vec_IntFree( vStack );
    Vec_IntFree( vInside );
}

/**Function*************************************************************

  Synopsis    [Enumerates bounded cuts and matches exact adder candidates.]

  Description [Muxes form analysis boundaries. Native XORs and buffers are
  evaluated exactly. No input GIA scratch fields are used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_Detect( Acec2_Man_t * p )
{
    Vec_Int_t * vCuts = Vec_IntAlloc( 1000 ), * vOffsets = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vCounts = Vec_IntStart( Gia_ManObjNum(p->pGia) ), * vFuncs = Vec_IntAlloc( 1000 );
    Vec_Bit_t * vLimited = Vec_BitStart(Gia_ManObjNum(p->pGia));
    Vec_Int_t * vCheck[3];
    Vec_Ptr_t * vCandidates = Vec_PtrAlloc( 100 );
    int Temp[65][5], Cut[5], Cut0[5], Cut1[5], i, j, k, a, b, n, n0, n1, off0, off1, cls, pos, fLimit;
    int * s, * c, end, pairs, m, fConstant, start, Check[5], Truth;
    Gia_Obj_t * pObj;
    Acec2_Cell_t * pCell;
    vCheck[0] = Vec_IntStartFull(Gia_ManObjNum(p->pGia)); Vec_IntWriteEntry(vCheck[0], 0, 0);
    vCheck[1] = Vec_IntAlloc(32); vCheck[2] = Vec_IntAlloc(32);
    Vec_IntFill( vCuts, 4, 0 );
    Vec_IntWriteEntry( vCounts, 0, 1 );
    Gia_ManForEachObj1( p->pGia, pObj, i )
    {
        if ( (i & 255) == 0 && Acec2_Stopped(p) ) break;
        if ( p->vFocus && !Vec_BitEntry(p->vFocus, i) ) continue;
        if ( Gia_ObjIsCo(pObj) ) continue;
        Temp[0][0] = 1; Temp[0][1] = i; Temp[0][2] = Temp[0][3] = 0; Temp[0][4] = 0xAA;
        n = 1; fLimit = fConstant = 0; start = Vec_IntSize(vFuncs);
        if ( Gia_ObjIsAnd(pObj) && !Gia_ObjIsMux(p->pGia, pObj) )
        {
            a = Gia_ObjFaninId0( pObj, i ); b = Gia_ObjFaninId1( pObj, i );
            off0 = Vec_IntEntry(vOffsets, a); off1 = Vec_IntEntry(vOffsets, b);
            n0 = Vec_IntEntry(vCounts, a); n1 = Vec_IntEntry(vCounts, b);
            for ( a = 0; a < n0 && !p->fStopped; a++ )
            {
                Acec2_CutUnpack(Vec_IntEntryP(vCuts, off0+4*a), Cut0);
                for ( b = 0; b < n1 && !p->fStopped; b++ )
                {
                    Acec2_CutUnpack(Vec_IntEntryP(vCuts, off1+4*b), Cut1);
                    if ( !Acec2_CutMergeLeaves(Cut0, Cut1, Cut) ) continue;
                    for ( j = 1; j < n; j++ )
                        if ( Temp[j][0] == Cut[0] && Acec2_CutSubset(Temp[j], Cut) ) break;
                    if ( j < n )
                    {
                        p->nDuplicates++;
                        continue;
                    }
                    Acec2_CutTruth(Cut0, Cut1, Cut, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), Gia_ObjIsXor(pObj));
                    p->nTruths++;
                    if ( Acec2_CutIntercepts(p->pGia, Cut0, Cut1, Gia_ObjFaninId0(pObj, i)) ||
                         Acec2_CutIntercepts(p->pGia, Cut1, Cut0, Gia_ObjFaninId1(pObj, i)) )
                    {
                        memcpy(Check, Cut, 4*sizeof(int)); Check[4] = i;
                        Truth = Acec2_EvaluateCut(p, Check, vCheck[0], vCheck[1], vCheck[2]);
                        p->nCutChecks++;
                        if ( Truth < 0 ) { p->nUnconfirmedCuts++; continue; }
                        p->nCutCorrections += Truth != Cut[4]; Cut[4] = Truth;
                    }
                    for ( j = 1; j < n; j++ )
                        if ( Acec2_CutSubsumes(Temp[j], Cut) ) break;
                    if ( j < n ) { p->nDominated++; continue; }
                    for ( j = 1; j < n; )
                        if ( Acec2_CutSubsumes(Cut, Temp[j]) )
                        {
                            n--; p->nDominated++;
                            memmove(Temp[j], Temp[j+1], (size_t)(n-j)*5*sizeof(int));
                        }
                        else j++;
                    if ( !fConstant && (Cut[4] == 0 || Cut[4] == 255) )
                    {
                        Vec_IntPushTwo(p->vConstants, i, Cut[4] != 0);
                        fConstant = 1;
                    }
                    cls = Acec2_CutClass( Cut[0], Cut[4] );
                    if ( cls && !Acec2_RecordCut(p, vFuncs, start, Cut, i, cls, vCheck) ) break;
                    pos = n;
                    if ( n == p->Pars.nCuts+1 )
                    {
                        fLimit = 1;
                        for ( j = n-1; j > 0; j-- )
                            if ( Acec2_CutClass(Temp[j][0], Temp[j][4]) < cls ) { pos = j; break; }
                        if ( pos == n ) continue;
                    }
                    else n++;
                    memcpy( Temp[pos], Cut, 5*sizeof(int) );
                }
            }
        }
        // Vec_Int doubles its capacity; reserve room before that can overflow.
        if ( Vec_IntSize(vCuts) > ABC_INT_MAX/2-4*n || Vec_IntSize(vFuncs) > ABC_INT_MAX/2-6*n ||
             Vec_IntSize(p->vXors) > ABC_INT_MAX/2-5*n )
        {
            p->fStopped = p->fStorageLimit = 1;
            break;
        }
        p->nCutLimits += fLimit;
        if ( Gia_ObjIsAnd(pObj) )
        {
            fLimit |= Vec_BitEntry(vLimited, Gia_ObjFaninId0(pObj, i)) | Vec_BitEntry(vLimited, Gia_ObjFaninId1(pObj, i));
            if ( Gia_ObjIsMux(p->pGia, pObj) ) fLimit |= Vec_BitEntry(vLimited, Gia_ObjFaninId2(p->pGia, i));
            Acec2_BitWrite(vLimited, i, fLimit);
        }
        Vec_IntWriteEntry( vOffsets, i, Vec_IntSize(vCuts) );
        Vec_IntWriteEntry( vCounts, i, n );
        for ( j = 0; j < n; j++ )
        {
            Vec_IntPushThree(vCuts, Temp[j][1], Temp[j][2], Temp[j][3]);
            Vec_IntPush(vCuts, Temp[j][0] | (Temp[j][4] << 2));
        }
        p->nCuts += n-1;
    }
    Vec_IntFree( vCuts );
    Vec_IntFree( vOffsets );
    Vec_IntFree( vCounts );
    for ( i = 0; i < 3; i++ ) Vec_IntFree(vCheck[i]);
    qsort( Vec_IntArray(vFuncs), Vec_IntSize(vFuncs)/6, 6*sizeof(int), Acec2_FuncCompare );
    Acec2_ExpandXors(p, vFuncs, vLimited);
    qsort( Vec_IntArray(vFuncs), Vec_IntSize(vFuncs)/6, 6*sizeof(int), Acec2_FuncCompare );
    Acec2_RecoverCuts(p, vFuncs);
    Vec_BitFree(vLimited);
    qsort( Vec_IntArray(vFuncs), Vec_IntSize(vFuncs)/6, 6*sizeof(int), Acec2_FuncCompare );
    for ( i = 0; i < Vec_IntSize(vFuncs); i = end )
    {
        if ( Acec2_Stopped(p) ) break;
        s = Vec_IntEntryP(vFuncs, i);
        for ( end = i+6; end < Vec_IntSize(vFuncs); end += 6 )
            if ( memcmp(s, Vec_IntEntryP(vFuncs, end), 4*sizeof(int)) ) break;
        fLimit = 0;
        for ( j = i; j < end; j += 6 )
        {
            if ( ((j-i) & 255) == 0 && Acec2_Stopped(p) ) break;
            s = Vec_IntEntryP(vFuncs, j);
            if ( Acec2_CutClass(s[0], s[5]) != 2 ) continue;
            pairs = 0;
            for ( k = i; k < end; k += 6 )
            {
                c = Vec_IntEntryP(vFuncs, k);
                if ( Acec2_CutClass(c[0], c[5]) != 1 ) continue;
                pCell = Acec2_MatchCut( s, c );
                if ( pCell && pairs == 128 ) { ABC_FREE(pCell); fLimit = 1; break; }
                else if ( pCell )
                {
                    if ( Vec_PtrSize(vCandidates) >= ABC_INT_MAX/4-1 )
                    { ABC_FREE(pCell); p->fStopped = p->fStorageLimit = 1; break; }
                    Vec_PtrPush(vCandidates, pCell); pairs++;
                }
            }
        }
        p->nPairLimits += fLimit;
    }
    Acec2_BuildXors(p);
    Acec2_BuildParity(p);
    Acec2_PairParities(p, vCandidates);
    if ( !p->fFast ) Acec2_RecoverCarries(p, vCandidates);
    p->nCandidates = Vec_PtrSize(vCandidates);
    Acec2_Select( p, vCandidates );
    Vec_PtrClear(vCandidates);
    if ( !p->fFast && Vec_IntSize(p->vXors) && !Acec2_Stopped(p) ) Acec2_RecoverParityCells(p, vCandidates);
    p->nCandidates += Vec_PtrSize(vCandidates);
    if ( Vec_PtrSize(vCandidates) ) Acec2_Select(p, vCandidates);
    Vec_PtrFree( vCandidates );
    Vec_IntFree( vFuncs );
    // Count each output once per arity; XOR2 and XOR3 counts can overlap.
    vCounts = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    for ( m = 0; m < Vec_IntSize(p->vXors); m += 5 )
    {
        i = Abc_Lit2Var(Vec_IntEntry(p->vXors, m+4));
        cls = Vec_IntEntry(p->vXors, m) == 2 ? 1 : 2;
        if ( Vec_IntEntry(vCounts, i) & cls ) continue;
        if ( !Vec_IntEntry(vCounts, i) && Vec_IntEntry(p->vNodeCell, i) == -1 ) p->nParityOnly++;
        Vec_IntWriteEntry( vCounts, i, Vec_IntEntry(vCounts, i) | cls );
        p->nXor2 += Vec_IntEntry(p->vXors, m) == 2;
        p->nXor3 += Vec_IntEntry(p->vXors, m) == 3;
    }
    Vec_IntFree( vCounts );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
