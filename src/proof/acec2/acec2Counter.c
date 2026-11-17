/**CFile****************************************************************

  FileName    [acec2Counter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Exact small weighted counters organized by parity boundaries.]

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

struct Acec2_CountCtx_t_
{
    Acec2_Man_t * m;
    Vec_Int_t * vOffsets, * vFanouts, * vStamp, * vIndex, * vQueue, * vBlocked;
    Vec_Wrd_t * vTruth;
    Vec_Bit_t * vObserved;
    Vec_Int_t * vRoots, * vDone;
    Vec_Wec_t * vRetries;
    Hsh_VecMan_t * hBridges;
    int iRoot, iRetry, fLimited;
    int Stamp, nSteps;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns a variable's complete six-input truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Acec2_CountVariable( int i )
{
    static const word Truths[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000)
    };
    return Truths[i];
}

/**Function*************************************************************

  Synopsis    [Re-derives a counter identity on an independent source cut.]

  Description [The checker visits only the output cones. Escaping the cut,
  exceeding the cone bound or meeting unsupported gates rejects the proposal.
  All assignments to up to six cut signals are checked simultaneously.]

  SideEffects [Optionally records the exact implementation cone.]

  SeeAlso     []

***********************************************************************/
static int Acec2_CounterEvaluate( Acec2_Man_t * m, Acec2_Counter_t * c, Vec_Int_t * vGates, word * pTruth )
{
    Hsh_Int1Man_t * h = Hsh_Int1ManStart(100);
    Vec_Int_t * vStack = Vec_IntAlloc(100), * vOrder = Vec_IntAlloc(100);
    Vec_Wrd_t * vTruth = Vec_WrdAlloc(100);
    word lhs[8] = {0}, rhs[8] = {0}, a, b, value, carry, next;
    Gia_Obj_t * o; Vec_Int_t * v;
    int id, i, j, k, index, f0, f1, side, lit, rank, result = 0, n = Vec_IntSize(c->vInputs)/2;
    if ( (Vec_IntSize(c->vInputs) & 1) || n < 2 || n > 6 || c->Width < 1 || c->Width > 8 || (Vec_IntSize(c->vOutputs) & 1) ) goto finish;
    if ( Acec2_Stopped(m) ) goto finish;
    Acec2_IndexAdd(h, 0); Vec_WrdPush(vTruth, 0);
    for ( i = 0; i < n; i++ )
    {
        id = Vec_IntEntry(c->vInputs, 2*i) >> 1;
        if ( id <= 0 || id >= Gia_ManObjNum(m->pGia) || Acec2_IndexLookup(h, id) >= 0 ) goto finish;
        Acec2_IndexAdd(h, id); Vec_WrdPush(vTruth, Acec2_CountVariable(i));
    }
    for ( i = 0; i < Vec_IntSize(c->vOutputs); i += 2 ) Vec_IntPush(vStack, Vec_IntEntry(c->vOutputs, i) >> 1);
    while ( Vec_IntSize(vStack) )
    {
        id = Vec_IntPop(vStack);
        if ( id < 0 || id >= Gia_ManObjNum(m->pGia) ) goto finish;
        if ( Acec2_IndexLookup(h, id) >= 0 ) continue;
        if ( Vec_IntSize(vOrder) == 4096 ) { m->nCounterLimits++; goto finish; }
        if ( Acec2_Stopped(m) ) goto finish;
        o = Gia_ManObj(m->pGia, id);
        if ( !Gia_ObjIsAnd(o) || Gia_ObjIsMux(m->pGia, o) ) goto finish;
        Acec2_IndexAdd(h, id); Vec_WrdPush(vTruth, 0); Vec_IntPush(vOrder, id);
        Vec_IntPushTwo(vStack, Gia_ObjFaninId0(o, id), Gia_ObjFaninId1(o, id));
    }
    Vec_IntSort(vOrder, 0);
    Vec_IntForEachEntry(vOrder, id, i)
    {
        o = Gia_ManObj(m->pGia, id); f0 = Gia_ObjFaninLit0p(m->pGia, o); f1 = Gia_ObjFaninLit1p(m->pGia, o);
        a = Vec_WrdEntry(vTruth, Acec2_IndexLookup(h, f0 >> 1)); if ( f0 & 1 ) a = ~a;
        b = Vec_WrdEntry(vTruth, Acec2_IndexLookup(h, f1 >> 1)); if ( f1 & 1 ) b = ~b;
        Vec_WrdWriteEntry(vTruth, Acec2_IndexLookup(h, id), Gia_ObjIsXor(o) ? a ^ b : a & b);
    }
    for ( side = 0; side < 2; side++ )
    {
        v = side ? c->vInputs : c->vOutputs;
        for ( i = 0; i < Vec_IntSize(v); i += 2 )
        {
            lit = Vec_IntEntry(v, i); rank = Vec_IntEntry(v, i+1);
            if ( rank < 0 || rank >= c->Width ) goto finish;
            index = Acec2_IndexLookup(h, lit >> 1); if ( index < 0 ) goto finish;
            value = Vec_WrdEntry(vTruth, index); if ( lit & 1 ) value = ~value;
            carry = value;
            for ( j = rank; j < c->Width; j++ )
            {
                next = (side ? rhs[j] : lhs[j]) & carry;
                if ( side ) rhs[j] ^= carry; else lhs[j] ^= carry;
                carry = next;
            }
        }
    }
    for ( k = 0; k < c->Width; k++ ) if ( lhs[k] != rhs[k] ) goto finish;
    if ( pTruth )
        for ( i = 0; i < Vec_IntSize(c->vOutputs); i += 2 )
            pTruth[i/2] = Vec_WrdEntry(vTruth, Acec2_IndexLookup(h, Vec_IntEntry(c->vOutputs, i) >> 1));
    if ( vGates ) { Vec_IntClear(vGates); Vec_IntAppend(vGates, vOrder); }
    result = 1;
finish:
    Hsh_Int1ManStop(h); Vec_IntFree(vStack); Vec_IntFree(vOrder); Vec_WrdFree(vTruth); return result;
}

/**Function*************************************************************

  Synopsis    [Checks a counter and optionally records its implementation cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CounterCheck( Acec2_Man_t * m, Acec2_Counter_t * c, Vec_Int_t * vGates )
{
    return Acec2_CounterEvaluate(m, c, vGates, NULL);
}

/**Function*************************************************************

  Synopsis    [Re-derives positive output-node functions on a checked counter cut.]

  Description [The caller provides room for every counter output truth table.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CounterTruth( Acec2_Man_t * m, Acec2_Counter_t * c, word * pTruth )
{
    return Acec2_CounterEvaluate(m, c, NULL, pTruth);
}

/**Function*************************************************************

  Synopsis    [Stores compact private fanouts for all parity-cut proposals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_CountCtx_t * Acec2_CountStart( Acec2_Man_t * m )
{
    Acec2_CountCtx_t * p = ABC_CALLOC(Acec2_CountCtx_t, 1);
    Gia_Obj_t * o; Vec_Int_t * v; int n = Gia_ManObjNum(m->pGia), i, j, id, edges, pass;
    p->m = m; p->vOffsets = Vec_IntStart(n+1); p->vObserved = Vec_BitStart(n);
    Vec_WecForEachLevel(m->vXorLeaves, v, i)
        Vec_IntForEachEntry(v, id, j) Acec2_BitWrite(p->vObserved, id, 1);
    Gia_ManForEachCo(m->pGia, o, i) Acec2_BitWrite(p->vObserved, Gia_ObjFaninId0p(m->pGia, o), 1);
    Gia_ManForEachAnd(m->pGia, o, i)
        for ( j = 0; j < 2; j++ ) Vec_IntAddToEntry(p->vOffsets, j ? Gia_ObjFaninId1(o, i) : Gia_ObjFaninId0(o, i), 1);
    for ( i = 1; i <= n; i++ ) Vec_IntAddToEntry(p->vOffsets, i, Vec_IntEntry(p->vOffsets, i-1));
    edges = Vec_IntEntry(p->vOffsets, n); p->vFanouts = Vec_IntStart(edges);
    Gia_ManForEachAnd(m->pGia, o, i)
        for ( j = 0; j < 2; j++ )
        { id = j ? Gia_ObjFaninId1(o, i) : Gia_ObjFaninId0(o, i); Vec_IntWriteEntry(p->vFanouts, Vec_IntAddToEntry(p->vOffsets, id, -1), i); }
    p->vStamp = Vec_IntStart(n); p->vIndex = Vec_IntStart(n);
    p->vQueue = Vec_IntAlloc(512); p->vTruth = Vec_WrdAlloc(512); p->vBlocked = Vec_IntAlloc(16);
    p->vRoots = Vec_IntAlloc(100); p->vRetries = Vec_WecAlloc(16);
    for ( pass = 0; pass < 2; pass++ )
        for ( i = n-1; i > 0; i-- )
            if ( Vec_IntEntry(m->vXorBest, i) >= 0 && (Vec_IntEntry(m->vNodeCell, i) < 0) == (pass == 0) )
                Vec_IntPush(p->vRoots, i);
    p->vDone = Vec_IntStart(Vec_IntSize(p->vRoots));
    p->hBridges = Hsh_VecManStart(100);
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the per-design cut truth workspace.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CountStop( Acec2_CountCtx_t * p )
{
    Vec_IntFree(p->vOffsets); Vec_IntFree(p->vFanouts); Vec_IntFree(p->vStamp); Vec_IntFree(p->vIndex);
    Vec_IntFree(p->vQueue); Vec_IntFree(p->vBlocked); Vec_WrdFree(p->vTruth); Vec_BitFree(p->vObserved);
    Vec_IntFree(p->vRoots); Vec_IntFree(p->vDone); Vec_WecFree(p->vRetries);
    Hsh_VecManStop(p->hBridges); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Evaluates only the bounded forward closure of a parity cut.]

  Description [Every evaluated function has a complete truth table over the
  cut. Unknown fanins remain boundaries; they are never assigned constants.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CountClosure( Acec2_CountCtx_t * p, Vec_Int_t * vCut )
{
    Acec2_Man_t * m = p->m; Gia_Obj_t * o;
    int i, j, id, node, a, b; word x, y;
    ++p->Stamp; Vec_IntClear(p->vQueue); Vec_WrdClear(p->vTruth); Vec_IntClear(p->vBlocked);
    Vec_IntPush(p->vQueue, 0); Vec_WrdPush(p->vTruth, 0);
    Vec_IntWriteEntry(p->vStamp, 0, p->Stamp); Vec_IntWriteEntry(p->vIndex, 0, 0);
    Vec_IntForEachEntry(vCut, id, i)
    {
        Vec_IntWriteEntry(p->vStamp, id, p->Stamp); Vec_IntWriteEntry(p->vIndex, id, Vec_IntSize(p->vQueue));
        Vec_IntPush(p->vQueue, id); Vec_WrdPush(p->vTruth, Acec2_CountVariable(i));
    }
    for ( i = 0; i < Vec_IntSize(p->vQueue) && Vec_IntSize(p->vQueue) < 512 && p->nSteps < m->nCounterStepLimit; i++ )
    {
        id = Vec_IntEntry(p->vQueue, i);
        for ( j = Vec_IntEntry(p->vOffsets, id); j < Vec_IntEntry(p->vOffsets, id+1); j++ )
        {
            if ( ++p->nSteps > m->nCounterStepLimit || ((p->nSteps & 1023) == 0 && Acec2_Stopped(m)) ) return;
            node = Vec_IntEntry(p->vFanouts, j);
            if ( Vec_IntEntry(p->vStamp, node) == p->Stamp ) continue;
            o = Gia_ManObj(m->pGia, node); if ( Gia_ObjIsMux(m->pGia, o) ) continue;
            a = Gia_ObjFaninId0(o, node); b = Gia_ObjFaninId1(o, node);
            if ( Vec_IntEntry(p->vStamp, a) != p->Stamp || Vec_IntEntry(p->vStamp, b) != p->Stamp )
            {
                node = Vec_IntEntry(p->vStamp, a) == p->Stamp ? b : a;
                if ( Vec_IntSize(p->vBlocked) < 32 && node && Vec_IntEntry(m->vXorFirst, node) < 0 ) Vec_IntPushUnique(p->vBlocked, node);
                continue;
            }
            x = Vec_WrdEntry(p->vTruth, Vec_IntEntry(p->vIndex, a)); if ( Gia_ObjFaninC0(o) ) x = ~x;
            y = Vec_WrdEntry(p->vTruth, Vec_IntEntry(p->vIndex, b)); if ( Gia_ObjFaninC1(o) ) y = ~y;
            Vec_IntWriteEntry(p->vStamp, node, p->Stamp); Vec_IntWriteEntry(p->vIndex, node, Vec_IntSize(p->vQueue));
            Vec_IntPush(p->vQueue, node); Vec_WrdPush(p->vTruth, Gia_ObjIsXor(o) ? x ^ y : x & y);
            if ( Vec_IntSize(p->vQueue) == 512 ) break;
        }
    }
    if ( Vec_IntSize(p->vQueue) == 512 ) m->nCounterLimits++;
    // A temporarily blocked gate may become known later in the same pass.
    // Retain only unresolved boundaries, preferring earlier source signals.
    for ( i = 0, j = 0; i < Vec_IntSize(p->vBlocked); i++ )
    {
        id = Vec_IntEntry(p->vBlocked, i);
        if ( Vec_IntEntry(p->vStamp, id) != p->Stamp ) Vec_IntWriteEntry(p->vBlocked, j++, id);
    }
    Vec_IntShrink(p->vBlocked, j); Vec_IntSort(p->vBlocked, 0);
    if ( Vec_IntSize(p->vBlocked) > 4 ) Vec_IntShrink(p->vBlocked, 4);
}

/**Function*************************************************************

  Synopsis    [Looks up an observed function using its entire truth table.]

  Description [Shared implementation and opposite polarity are permitted.
  Only functionally proved output literals are returned.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CountLookup( Acec2_CountCtx_t * p, word Truth, int Exclude )
{
    int i, id, best = -1, refs = -1, score; word value;
    for ( i = 1; i < Vec_IntSize(p->vQueue); i++ )
    {
        id = Vec_IntEntry(p->vQueue, i); if ( id == Exclude ) continue;
        value = Vec_WrdEntry(p->vTruth, i);
        if ( value != Truth && ~value != Truth ) continue;
        score = Abc_MinInt(Vec_IntEntry(p->m->vRefs, id), 1000000) + 1000001*Vec_BitEntry(p->vObserved, id);
        if ( score <= refs ) continue;
        best = 2*id+(value != Truth); refs = score;
    }
    return best;
}

/**Function*************************************************************

  Synopsis    [Keeps exact counter alternatives independently of the cell cover.]

  Description [At least one carry must have use outside this counter's
  implementation. A parity network with only private carries stays parity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CountSave( Acec2_CountCtx_t * p, Vec_Int_t * vCut, int Phase, int Even,
                           int Width, Vec_Int_t * vOutputs )
{
    Acec2_Man_t * m = p->m; Acec2_Counter_t * c = ABC_CALLOC(Acec2_Counter_t, 1);
    Gia_Obj_t * o; int i, j, id, lit, outside = 0, refs;
    c->Width = Width; c->vInputs = Vec_IntAlloc(12); c->vOutputs = Vec_IntDup(vOutputs); c->vGates = Vec_IntAlloc(100);
    Vec_IntForEachEntry(vCut, id, i) Vec_IntPushTwo(c->vInputs, 2*id+((Phase >> i) & 1), (Even >> i) & 1);
    if ( !Acec2_CounterCheck(m, c, c->vGates) ) goto fail;
    for ( i = 2; i < Vec_IntSize(vOutputs); i += 2 )
    {
        lit = Vec_IntEntry(vOutputs, i); refs = Vec_IntEntry(m->vRefs, lit >> 1);
        Vec_IntForEachEntry(c->vGates, id, j)
        {
            o = Gia_ManObj(m->pGia, id);
            refs -= Gia_ObjFaninId0(o, id) == (lit >> 1); refs -= Gia_ObjFaninId1(o, id) == (lit >> 1);
        }
        outside += refs > 0;
    }
    if ( !outside ) goto fail;
    Vec_PtrPush(m->vCounters, c); return 1;
fail:
    Vec_IntFree(c->vInputs); Vec_IntFree(c->vOutputs); Vec_IntFree(c->vGates); ABC_FREE(c); return 0;
}

/**Function*************************************************************

  Synopsis    [Matches binary or carry-save output encodings of a weighted sum.]

  Description [Odd-weight inputs appear in the low parity function. Additional
  even-weight inputs can enter at the next column. Truth-table
  equality checks every input assignment, including correlated source cuts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CountMatch( Acec2_CountCtx_t * p, Vec_Int_t * vCut, int Root )
{
    Vec_Int_t * vOutputs = Vec_IntAlloc(8), * vChoices = Vec_IntAlloc(32);
    word expected[4], root, x, next, masks[4], u, v, want;
    int n = Vec_IntSize(vCut), even = 0, width, total, phase, i, j, k, lit, a, b, result = 0;
    if ( Vec_IntEntry(p->vStamp, Root) != p->Stamp ) goto finish;
    root = Vec_WrdEntry(p->vTruth, Vec_IntEntry(p->vIndex, Root)); total = n;
    for ( i = 0; i < n; i++ )
        if ( (root & 1) == ((root >> (1 << i)) & 1) ) { even |= 1 << i; total++; }
    if ( total > 7 ) goto finish;
    width = total > 3 ? 3 : 2;
    for ( j = 0; j < 2; j++ )
        for ( i = Vec_IntSize(p->vQueue)-1; i > n && Vec_IntSize(vChoices) < 32; i-- )
        {
            lit = Vec_IntEntry(p->vQueue, i);
            if ( lit != Root && Vec_IntEntry(p->m->vRefs, lit) > 0 &&
                 Vec_BitEntry(p->vObserved, lit) == !j ) Vec_IntPush(vChoices, i);
        }
    for ( phase = 0; phase < (1 << n) && !Acec2_Stopped(p->m); phase++ )
    {
        memset(expected, 0, sizeof(expected));
        for ( i = 0; i < n; i++ )
        {
            x = Acec2_CountVariable(i); if ( (phase >> i) & 1 ) x = ~x;
            for ( j = (even >> i) & 1; j < width; j++ ) { next = expected[j] & x; expected[j] ^= x; x = next; }
        }
        if ( expected[0] != root && expected[0] != ~root ) continue;
        Vec_IntClear(vOutputs); Vec_IntPushTwo(vOutputs, 2*Root+(expected[0] != root), 0);
        for ( j = 1; j < width; j++ )
        {
            lit = Acec2_CountLookup(p, expected[j], Root); if ( lit < 0 ) break;
            Vec_IntPushTwo(vOutputs, lit, j);
        }
        if ( j == width && Acec2_CountSave(p, vCut, phase, even, width, vOutputs) ) { result = 1; break; }
        Vec_IntShrink(vOutputs, 2);
        masks[0] = ~expected[1] & ~expected[2]; masks[1] = expected[1] & ~expected[2];
        masks[2] = ~expected[1] & expected[2]; masks[3] = expected[1] & expected[2];
        // Two or three equal-rank carry outputs are also exact counters.
        for ( i = 0; i < Vec_IntSize(vChoices) && !result; i++ )
            for ( a = 0; a < 2 && !result; a++ )
            {
                k = Vec_IntEntry(vChoices, i); u = Vec_WrdEntry(p->vTruth, k); if ( a ) u = ~u;
                if ( !masks[3] && !(u & masks[0]) && !(~u & masks[2]) )
                {
                    want = masks[2] | (masks[1] & ~u); lit = Acec2_CountLookup(p, want, Root);
                    if ( lit >= 0 && (lit >> 1) != Vec_IntEntry(p->vQueue, k) )
                    {
                        Vec_IntPushTwo(vOutputs, 2*Vec_IntEntry(p->vQueue, k)+a, 1); Vec_IntPushTwo(vOutputs, lit, 1);
                        result = Acec2_CountSave(p, vCut, phase, even, width, vOutputs); Vec_IntShrink(vOutputs, 2);
                    }
                }
                for ( j = i+1; j < Vec_IntSize(vChoices) && !result && masks[3]; j++ )
                    for ( b = 0; b < 2 && !result; b++ )
                    {
                        k = Vec_IntEntry(vChoices, j); v = Vec_WrdEntry(p->vTruth, k); if ( b ) v = ~v;
                        if ( (masks[0] & (u | v)) || (masks[1] & u & v) ||
                             (masks[2] & ~(u | v)) || (masks[3] & ~(u & v)) ) continue;
                        want = (masks[1] & ~(u | v)) | (masks[2] & (u ^ v)) | masks[3];
                        lit = Acec2_CountLookup(p, want, Root);
                        if ( lit < 0 || (lit >> 1) == Vec_IntEntry(p->vQueue, k) ||
                             (lit >> 1) == Vec_IntEntry(p->vQueue, Vec_IntEntry(vChoices, i)) ) continue;
                        Vec_IntPushTwo(vOutputs, 2*Vec_IntEntry(p->vQueue, Vec_IntEntry(vChoices, i))+a, 1);
                        Vec_IntPushTwo(vOutputs, 2*Vec_IntEntry(p->vQueue, k)+b, 1); Vec_IntPushTwo(vOutputs, lit, 1);
                        result = Acec2_CountSave(p, vCut, phase, even, width, vOutputs); Vec_IntShrink(vOutputs, 2);
                    }
            }
        if ( result ) break;
    }
finish:
    Vec_IntFree(vOutputs); Vec_IntFree(vChoices); return result;
}

/**Function*************************************************************

  Synopsis    [Closes a counter through two inputs of the next column.]

  Description [A three-input parity can survive when its carry is absorbed
  into the next sum and carry. Its three unit inputs and two weight-two
  inputs still have a complete three-bit counter identity. Earlier failed
  four-input closures provide the remaining boundary candidates. All cheap
  searches finish first; these extensions share the original cut and edge
  limits. Duplicate cuts are tried once and every result is checked on all
  independent cut assignments.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CountBridges( Acec2_CountCtx_t * p, Vec_Wec_t * vRetries, int First, int Last, int * pnAttempts )
{
    Acec2_Man_t * m = p->m;
    Vec_Int_t * entry, * cut = Vec_IntAlloc(5), * key = Vec_IntAlloc(6);
    int i, j, k, root, id, before;
    for ( i = First; i < Last; i++ )
    {
        entry = Vec_WecEntry(vRetries, i);
        root = Vec_IntEntry(entry, 0);
        for ( j = 5; j < Vec_IntSize(entry); j++ )
        {
            if ( *pnAttempts >= m->nCounterCutLimit || p->nSteps >= m->nCounterStepLimit || Acec2_Stopped(m) ) goto finish;
            id = Vec_IntEntry(entry, j); if ( id == root ) continue;
            Vec_IntClear(cut);
            for ( k = 1; k < 5; k++ ) Vec_IntPush(cut, Vec_IntEntry(entry, k));
            if ( Vec_IntFind(cut, id) >= 0 ) continue;
            Vec_IntPush(cut, id); Vec_IntSort(cut, 0);
            Vec_IntClear(key); Vec_IntPush(key, root); Vec_IntAppend(key, cut);
            before = Hsh_VecSize(p->hBridges); if ( Hsh_VecManAdd(p->hBridges, key) < before ) continue;
            (*pnAttempts)++; m->nCounterBridgeChecks++;
            Acec2_CountClosure(p, cut);
            if ( Acec2_CountMatch(p, cut, root) ) { m->nCounterBridges++; break; }
        }
    }
finish:
    Vec_IntFree(cut); Vec_IntFree(key);
}

/**Function*************************************************************

  Synopsis    [Expands one persistent parity equation into bounded counter cuts.]

  Description [A fixed proposal/edge budget makes incomplete detection
  explicit. Counter alternatives do not compete with the FA/HA cover.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_CountRoot( Acec2_CountCtx_t * p, int root )
{
    Acec2_Man_t * m = p->m;
    Vec_Int_t * vCut = Vec_IntAlloc(6), * vNext = Vec_IntAlloc(8), * vBlocked = Vec_IntAlloc(4);
    Vec_Wec_t * vRetries = p->vRetries; Vec_Int_t * retry;
    int offset, i, j, id, step, n, done, extra, first;
    offset = Vec_IntEntry(m->vXorBest, root);
    n = Vec_IntEntry(m->vXors, offset);
    for ( i = 0; i < n; i++ ) Vec_IntPush(vCut, Vec_IntEntry(m->vXors, offset+1+i));
    for ( step = 0; step < 6; step++ )
    {
        done = 1;
        for ( i = Vec_IntSize(vCut)-1; i >= 0; i-- )
        {
            id = Vec_IntEntry(vCut, i); offset = Vec_IntEntry(m->vXorBest, id); if ( offset < 0 ) continue;
            Vec_IntClear(vNext); Vec_IntAppend(vNext, vCut); Vec_IntRemove(vNext, id);
            n = Vec_IntEntry(m->vXors, offset);
            for ( j = 0; j < n; j++ )
            {
                id = Vec_IntEntry(m->vXors, offset+1+j);
                if ( !Vec_IntRemove(vNext, id) ) Vec_IntPush(vNext, id);
            }
            if ( Vec_IntSize(vNext) < 2 || Vec_IntSize(vNext) > 6 ) continue;
            Vec_IntClear(vCut); Vec_IntAppend(vCut, vNext); Vec_IntSort(vCut, 0); done = 0; break;
        }
        if ( done ) break;
    }
    if ( Vec_IntSize(vCut) < 3 ) goto finish;
    m->nCounterCuts++; Acec2_CountClosure(p, vCut);
    if ( Vec_IntSize(vCut) >= 4 ) Acec2_CountMatch(p, vCut, root);
    if ( Vec_IntSize(vCut) == 6 ) goto finish;
    Vec_IntAppend(vBlocked, p->vBlocked);
    first = Vec_WecSize(vRetries);
    for ( extra = 0; extra < Vec_IntSize(vBlocked) && m->nCounterCuts < m->nCounterCutLimit &&
                    p->nSteps < m->nCounterStepLimit && !Acec2_Stopped(m); extra++ )
    {
        id = Vec_IntEntry(vBlocked, extra); if ( Vec_IntFind(vCut, id) >= 0 || id == root ) continue;
        Vec_IntClear(vNext); Vec_IntAppend(vNext, vCut); Vec_IntPush(vNext, id); Vec_IntSort(vNext, 0);
        m->nCounterCuts++; Acec2_CountClosure(p, vNext);
        if ( Acec2_CountMatch(p, vNext, root) ) { Vec_WecShrink(vRetries, first); break; }
        if ( Vec_IntSize(vCut) == 3 && Vec_IntSize(p->vBlocked) )
        {
            retry = Vec_WecPushLevel(vRetries); Vec_IntPush(retry, root);
            Vec_IntAppend(retry, vNext); Vec_IntAppend(retry, p->vBlocked);
        }
    }
finish:
    Vec_IntFree(vCut); Vec_IntFree(vNext); Vec_IntFree(vBlocked);
}

/**Function*************************************************************

  Synopsis    [Keeps a parity boundary whose inputs remain in an open cone.]

  Description [The low sum itself may already be shared while the carry
  outputs are unproved. Expand parity-only fanins before rejecting such a
  root. An expansion bound conservatively keeps the candidate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CountLive( Acec2_Man_t * m, Vec_Bit_t * vLive, int Root )
{
    int stack[64], top = 0, steps = 0, id, offset, n, i;
    if ( !vLive ) return 1;
    stack[top++] = Root;
    while ( top )
    {
        id = stack[--top];
        if ( Vec_BitEntry(vLive, id) ) continue;
        offset = Vec_IntEntry(m->vXorBest, id); if ( offset < 0 ) return 0;
        n = Vec_IntEntry(m->vXors, offset);
        if ( top+n > 64 || ++steps > 64 ) return 1;
        for ( i = 0; i < n; i++ ) stack[top++] = Vec_IntEntry(m->vXors, offset+1+i);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resumes bounded counter recognition on unresolved parity roots.]

  Description [One work unit visits one parity root or one queued boundary
  extension. A skipped root remains eligible for a later live mask. Completed
  roots and cuts are not repeated, and all requests share the original limits.
  No cell, region or existing certificate is changed.]

  SideEffects [Appends checked counters to the owning analysis.]

  SeeAlso     []

***********************************************************************/
int Acec2_AdvanceCounters( Acec2_Man_t * m, Vec_Bit_t * vLive, int * pnWork )
{
    Acec2_CountCtx_t * p; Vec_Int_t * entry;
    int before, i, index, root, n;
    if ( !m || !pnWork || *pnWork <= 0 || m->fCounterComplete || !Vec_IntSize(m->vXors) || Acec2_Stopped(m) ||
         (vLive && Vec_BitSize(vLive) < Gia_ManObjNum(m->pGia)) ) return 0;
    if ( !m->pCounterCtx )
    {
        m->nCounterCutLimit = Abc_MaxInt(256, Abc_MinInt(4096, 2*(Vec_IntSize(m->vXors)/5)));
        m->nCounterStepLimit = 1024*m->nCounterCutLimit;
        m->pCounterCtx = Acec2_CountStart(m);
    }
    p = m->pCounterCtx; before = Vec_PtrSize(m->vCounters); n = Vec_IntSize(p->vRoots);
    for ( i = 0; i < n && *pnWork > 0; i++ )
    {
        if ( m->nCounterCuts >= m->nCounterCutLimit || p->nSteps >= m->nCounterStepLimit || Acec2_Stopped(m) ) goto finish;
        index = p->iRoot; p->iRoot = (index+1) % n;
        root = Vec_IntEntry(p->vRoots, index);
        if ( Vec_IntEntry(p->vDone, index) || !Acec2_CountLive(m, vLive, root) ) continue;
        (*pnWork)--; Acec2_CountRoot(p, root);
        if ( !Acec2_Stopped(m) ) Vec_IntWriteEntry(p->vDone, index, 1);
    }
    // Finish all currently eligible cheap roots before their extensions.
    if ( i < n ) goto finish;
    n = Vec_WecSize(p->vRetries);
    for ( i = 0; i < n && *pnWork > 0; i++ )
    {
        if ( m->nCounterCuts >= m->nCounterCutLimit || p->nSteps >= m->nCounterStepLimit || Acec2_Stopped(m) ) goto finish;
        index = p->iRetry; p->iRetry = (index+1) % n;
        entry = Vec_WecEntry(p->vRetries, index); root = Vec_IntEntry(entry, 0);
        if ( root < 0 || !Acec2_CountLive(m, vLive, root) ) continue;
        (*pnWork)--; Acec2_CountBridges(p, p->vRetries, index, index+1, &m->nCounterCuts);
        if ( !Acec2_Stopped(m) ) Vec_IntWriteEntry(entry, 0, -1);
    }
finish:
    m->nCounterSteps = p->nSteps;
    if ( !p->fLimited && (m->nCounterCuts >= m->nCounterCutLimit || p->nSteps >= m->nCounterStepLimit) )
    { p->fLimited = 1; m->nCounterLimits++; }
    return Vec_PtrSize(m->vCounters)-before;
}

/**Function*************************************************************

  Synopsis    [Runs the same resumable counter analysis for standalone profiling.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_FindCounters( Acec2_Man_t * m )
{
    int work = ABC_INT_MAX;
    Acec2_AdvanceCounters(m, NULL, &work);
    Acec2_CounterStop(m); m->fCounterComplete = 1;
}

/**Function*************************************************************

  Synopsis    [Releases the analysis-owned counter search state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_CounterStop( Acec2_Man_t * m )
{
    if ( m->pCounterCtx ) { Acec2_CountStop(m->pCounterCtx); m->pCounterCtx = NULL; }
}

/**Function*************************************************************

  Synopsis    [Reports checked counters without changing the FA/HA cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_CountersWriteJson( Acec2_Man_t * m, FILE * f )
{
    Acec2_Counter_t * c; int i, j, k; Vec_Int_t * v;
    fprintf(f, "[");
    Vec_PtrForEachEntry(Acec2_Counter_t *, m->vCounters, c, i)
    {
        fprintf(f, "%s{\"id\":%d,\"width\":%d,\"domain\":\"free_cut\"", i ? "," : "", i, c->Width);
        for ( k = 0; k < 2; k++ )
        {
            v = k ? c->vOutputs : c->vInputs;
            fprintf(f, ",\"%s\":[", k ? "outputs" : "inputs");
            for ( j = 0; j < Vec_IntSize(v); j += 2 ) fprintf(f, "%s[%d,%d]", j ? "," : "", Vec_IntEntry(v, j), Vec_IntEntry(v, j+1));
            fprintf(f, "]");
        }
        fprintf(f, ",\"covered_gates\":[");
        Acec2_WriteList(f, c->vGates, 1, 0);
        fprintf(f, "]}");
    }
    fprintf(f, "]");
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
