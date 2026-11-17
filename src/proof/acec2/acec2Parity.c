/**CFile****************************************************************

  FileName    [acec2Parity.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Exact phased parity expressions and reassociated adder pairs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 14, 2026.]

  Revision    [$Id$]

  Description [Checked parity equations are composed by symmetric difference.
  Hashing only indexes exact sorted leaf sets. AND and majority cuts can
  therefore be paired with differently associated sums. Two checked half
  adders can also compose through an OR of their mutually exclusive carries.
  These identities hold on the source, not on an independently cut sum cone.]

***********************************************************************/

#include "acec2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

struct Acec2_ParityCtx_t_
{
    Hsh_VecMan_t * hSets;
    Vec_Int_t * vForms;         // object -> twice its set index plus phase; -1 is an atom
    Vec_Int_t * vHeads, * vNext;
    Vec_Int_t * vWork;
    Vec_Int_t * vCheckTruth, * vCheckStack, * vCheckTouched;
    int nStorage;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Appends an exact expression and returns its constant phase.]

  Description [An unexpanded node is an opaque source atom, including when
  a storage bound prevented expansion. Constant zero has no atoms.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ParityAppend( Acec2_ParityCtx_t * p, Vec_Int_t * v, int Lit )
{
    int form, id = Lit >> 1;
    if ( !id ) return Lit & 1;
    form = Vec_IntEntry(p->vForms, id);
    if ( form < 0 ) Vec_IntPush(v, id);
    else Vec_IntAppend(v, Hsh_VecReadEntry(p->hSets, form >> 1));
    return (Lit & 1) ^ (form < 0 ? 0 : form & 1);
}

/**Function*************************************************************

  Synopsis    [Cancels even multiplicities in a parity expression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ParityReduce( Vec_Int_t * v )
{
    int i, j, n = 0;
    if ( Vec_IntSize(v) > 1 ) Vec_IntSort(v, 0);
    for ( i = 0; i < Vec_IntSize(v); i = j )
    {
        for ( j = i+1; j < Vec_IntSize(v) && Vec_IntEntry(v, j) == Vec_IntEntry(v, i); j++ ) {}
        if ( (j-i) & 1 ) Vec_IntWriteEntry(v, n++, Vec_IntEntry(v, i));
    }
    Vec_IntShrink(v, n);
}

/**Function*************************************************************

  Synopsis    [Looks up a leaf set, comparing all atoms after hashing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ParityLookup( Acec2_ParityCtx_t * p, Vec_Int_t * v )
{
    Hsh_VecObj_t * entry; int id;
    id = Vec_IntEntry(p->hSets->vTable, Hsh_VecManHash(v, Vec_IntSize(p->hSets->vTable)));
    while ( id >= 0 )
    {
        entry = Hsh_VecObj(p->hSets, id);
        if ( entry->nSize == Vec_IntSize(v) &&
             (!entry->nSize || !memcmp(entry->pArray, Vec_IntArray(v), (size_t)entry->nSize*sizeof(int))) ) return id;
        id = entry->iNext;
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Builds persistent exact forms from the selected XOR equations.]

  Description [Each selected equation has already been checked against its
  source cone. Expansions are topological and bounded; an omitted expansion
  remains an atom and cannot introduce an incorrect equality.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_BuildParity( Acec2_Man_t * m )
{
    Acec2_ParityCtx_t * p; Vec_Int_t * v;
    int id, i, k, phase, set, lit, n = Gia_ManObjNum(m->pGia);
    if ( m->pParity || !m->vXorBest ) return;
    p = m->pParity = ABC_CALLOC(Acec2_ParityCtx_t, 1);
    p->hSets = Hsh_VecManStart(100); p->vForms = Vec_IntStartFull(n);
    p->vHeads = Vec_IntAlloc(100); p->vNext = Vec_IntStartFull(n);
    p->vWork = Vec_IntAlloc(32); v = p->vWork;
    p->nStorage = (int)Abc_MinInt(16000000, (int)Abc_MinInt(n, 499000)*32+4096);
    for ( id = 1; id < n; id++ )
    {
        if ( !(id & 255) && Acec2_Stopped(m) ) break;
        i = Vec_IntEntry(m->vXorBest, id); if ( i < 0 ) continue;
        if ( Vec_IntSize(p->hSets->vData) > p->nStorage-2052 ) { m->nParitySetLimits++; continue; }
        Vec_IntClear(v); phase = Vec_IntEntry(m->vXors, i+4) & 1;
        for ( k = 0; k < Vec_IntEntry(m->vXors, i); k++ )
        {
            lit = 2*Vec_IntEntry(m->vXors, i+1+k);
            if ( (lit >> 1) >= id || lit < 0 ) break;
            phase ^= Acec2_ParityAppend(p, v, lit);
        }
        if ( k != Vec_IntEntry(m->vXors, i) ) continue;
        Acec2_ParityReduce(v);
        if ( Vec_IntSize(v) > 2048 ) { m->nParitySetLimits++; continue; }
        set = Hsh_VecManAdd(p->hSets, v);
        if ( set == Vec_IntSize(p->vHeads) ) Vec_IntPush(p->vHeads, -1);
        Vec_IntWriteEntry(p->vForms, id, 2*set+phase);
        Vec_IntWriteEntry(p->vNext, id, Vec_IntEntry(p->vHeads, set));
        Vec_IntWriteEntry(p->vHeads, set, id); m->nParityForms++;
    }
}

/**Function*************************************************************

  Synopsis    [Checks that a list of source literals has identically zero XOR.]

  Description [The complete set and phase are compared, never a fingerprint.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ParityZero( Acec2_Man_t * m, int * pLits, int nLits )
{
    Acec2_ParityCtx_t * p = m->pParity; int i, phase = 0;
    if ( !p || nLits < 0 || nLits > 8 || Acec2_Stopped(m) ) return 0;
    Vec_IntClear(p->vWork);
    for ( i = 0; i < nLits; i++ )
    {
        if ( pLits[i] < 0 || (pLits[i] >> 1) >= Vec_IntSize(p->vForms) ) return 0;
        phase ^= Acec2_ParityAppend(p, p->vWork, pLits[i]);
    }
    Acec2_ParityReduce(p->vWork);
    return !phase && !Vec_IntSize(p->vWork);
}

/**Function*************************************************************

  Synopsis    [Tests membership in an exact source parity leaf set.]

  Description [An opaque source node denotes itself; hashes never replace
  the exact atom comparison.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ParityHasLeaf( Acec2_Man_t * m, int Lit, int Leaf )
{
    Acec2_ParityCtx_t * p = m->pParity; Vec_Int_t * atoms; int form, low = 0, high, mid;
    if ( !p || Lit < 0 || (Lit >> 1) >= Vec_IntSize(p->vForms) || Leaf < 1 ) return 0;
    form = Vec_IntEntry(p->vForms, Lit >> 1); if ( form < 0 ) return (Lit >> 1) == Leaf;
    atoms = Hsh_VecReadEntry(p->hSets, form >> 1); high = Vec_IntSize(atoms);
    while ( low < high ) { mid = low+(high-low)/2; if ( Vec_IntEntry(atoms, mid) < Leaf ) low = mid+1; else high = mid; }
    return low < Vec_IntSize(atoms) && Vec_IntEntry(atoms, low) == Leaf;
}

/**Function*************************************************************

  Synopsis    [Materializes a decoded parity over mapped source atoms.]

  Description [Only exact symmetric difference performs mask cancellation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ParityBuild( Acec2_Man_t * m, Gia_Man_t * g, Vec_Int_t * map, int Lit, int Mask )
{
    Acec2_ParityCtx_t * p = m->pParity; int i, atom, result, phase;
    if ( !p || Lit < 0 || Mask < 0 || (Lit >> 1) >= Vec_IntSize(p->vForms) ||
         (Mask >> 1) >= Vec_IntSize(p->vForms) || Acec2_Stopped(m) ) return -1;
    Vec_IntClear(p->vWork); phase = Acec2_ParityAppend(p, p->vWork, Lit);
    phase ^= Acec2_ParityAppend(p, p->vWork, Mask); Acec2_ParityReduce(p->vWork);
    result = phase;
    Vec_IntForEachEntry(p->vWork, atom, i)
    {
        if ( atom >= Vec_IntSize(map) || Vec_IntEntry(map, atom) < 0 ) return -1;
        result = Gia_ManHashXor(g, result, Vec_IntEntry(map, atom));
    }
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks the source parity and carry of one chain link.]

  Description [A source-only carry cites its completed SAT certificate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ParityHalfCheck( Acec2_Man_t * m, int * h, int Proof, int Parent )
{
    Acec2_ParityCtx_t * p = m->pParity;
    Acec2_Proof_t * proof; int cut[6], parity[3], k, truth = 0;
    if ( !p || Proof < 0 || Proof >= Parent ) return 0;
    for ( k = 0; k < 4; k++ )
        if ( h[k] < 0 || (h[k] >> 1) >= Gia_ManObjNum(m->pGia) || Gia_ObjIsCo(Gia_ManObj(m->pGia, h[k] >> 1)) ) return 0;
    for ( k = 0; k < 3; k++ ) parity[k] = h[k];
    if ( !Acec2_ParityZero(m, parity, 3) ) return 0;
    if ( Proof )
    {
        proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, Proof-1);
        if ( proof->Kind == 1 )
            return proof->Domain == 1 && proof->vIdentity && Vec_IntSize(proof->vIdentity) == 6 &&
                Vec_IntEntry(proof->vIdentity, 0) == 2 && Vec_IntEntry(proof->vIdentity, 3) == -1 &&
                Vec_IntEntry(proof->vIdentity, 1) == Abc_MinInt(h[0], h[1]) &&
                Vec_IntEntry(proof->vIdentity, 2) == Abc_MaxInt(h[0], h[1]) &&
                Vec_IntEntry(proof->vIdentity, 5) == h[3];
        if ( proof->Kind != 4 || proof->vChain ) return 0;
        if ( proof->ChainProof[0] ) return Acec2_ParityHalfCheck(m, h, proof->ChainProof[0], Proof);
    }
    if ( !p->vCheckTruth )
    {
        p->vCheckTruth = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
        Vec_IntWriteEntry(p->vCheckTruth, 0, 0);
        p->vCheckStack = Vec_IntAlloc(32); p->vCheckTouched = Vec_IntAlloc(32);
    }
    for ( k = 0; k < 4; k++ )
        truth |= (((((k & 1) ^ (h[0] & 1)) & (((k >> 1) & 1) ^ (h[1] & 1))) ^ (h[3] & 1)) << k);
    cut[0] = 2; cut[1] = h[0] >> 1; cut[2] = h[1] >> 1; cut[3] = -1; cut[4] = h[3] >> 1; cut[5] = truth;
    return cut[1] != cut[2] && Acec2_CheckCut(m, cut, p->vCheckTruth, p->vCheckStack, p->vCheckTouched);
}

/**Function*************************************************************

  Synopsis    [Checks endpoints and each link in a stored two-half-adder chain.]

  Description [Parity links are rederived from the exact source forms.
  Independent carries are re-evaluated on their cuts; source-only carries
  must cite an earlier completed SAT certificate with matching endpoints.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CheckParityCell( Acec2_Man_t * m, Acec2_Cell_t * c )
{
    Acec2_Proof_t * proof; Gia_Obj_t * o; int k, * h, inputs[3], link[2], a, b;
    if ( !c->Proof ) return 1;
    if ( c->Proof < 0 || c->Proof > Vec_PtrSize(m->vProofs) ) return 0;
    proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, c->Proof-1);
    if ( proof->Kind != 4 ) return 1;
    if ( proof->Domain != 1 || !proof->vIdentity || Vec_IntSize(proof->vIdentity) != 6 ||
         c->nIns != Vec_IntEntry(proof->vIdentity, 0) ) return 0;
    for ( k = 0; k < 3; k++ ) if ( c->In[k] != Vec_IntEntry(proof->vIdentity, k+1) ) return 0;
    for ( k = 0; k < 2; k++ ) if ( c->Out[k] != Vec_IntEntry(proof->vIdentity, k+4) ) return 0;
    if ( !proof->vChain )
    {
        if ( proof->ChainProof[0] )
        {
            Acec2_Proof_t * carry;
            if ( proof->ChainProof[0] < 0 || proof->ChainProof[0] >= c->Proof ) return 0;
            carry = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, proof->ChainProof[0]-1);
            if ( carry->Kind != 1 || carry->Domain != 1 || !carry->vIdentity || Vec_IntSize(carry->vIdentity) != 6 ) return 0;
            if ( Vec_IntEntry(carry->vIdentity, 0) != c->nIns || Vec_IntEntry(carry->vIdentity, 5) != c->Out[1] ) return 0;
            for ( k = 0; k < 3; k++ ) if ( Vec_IntEntry(carry->vIdentity, k+1) != c->In[k] ) return 0;
        }
        return 1;
    }
    if ( c->nIns != 3 || Vec_IntSize(proof->vChain) != 8 || c->Out[1] < 0 ||
         (c->Out[1] >> 1) >= Gia_ManObjNum(m->pGia) || (c->Out[1] & 1) ) return 0;
    h = Vec_IntArray(proof->vChain);
    if ( !Acec2_ParityHalfCheck(m, h, proof->ChainProof[0], c->Proof) ||
         !Acec2_ParityHalfCheck(m, h+4, proof->ChainProof[1], c->Proof) ) return 0;
    link[0] = h[2]; link[1] = h[4];
    if ( !Acec2_ParityZero(m, link, 2) || c->Out[0] != (h[6] ^ 1) ) return 0;
    inputs[0] = h[0] ^ 1; inputs[1] = h[1] ^ 1; inputs[2] = h[5] ^ 1;
    if ( inputs[0] > inputs[1] ) ABC_SWAP(int, inputs[0], inputs[1]);
    if ( inputs[1] > inputs[2] ) ABC_SWAP(int, inputs[1], inputs[2]);
    if ( inputs[0] > inputs[1] ) ABC_SWAP(int, inputs[0], inputs[1]);
    for ( k = 0; k < 3; k++ ) if ( inputs[k] != c->In[k] ) return 0;
    o = Gia_ManObj(m->pGia, c->Out[1] >> 1);
    if ( !Gia_ObjIsAnd(o) || Gia_ObjIsXor(o) || Gia_ObjIsMux(m->pGia, o) ) return 0;
    a = Gia_ObjFaninLit0p(m->pGia, o) ^ 1; b = Gia_ObjFaninLit1p(m->pGia, o) ^ 1;
    if ( !((a == h[3] && b == h[7]) || (b == h[3] && a == h[7])) ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts carry uses outside a reassociated half-adder sum.]

  Description [The parity atoms bound this traversal even when the two
  proposed inputs are not a structural cut. A carry used only to implement
  the same XOR remains private parity logic. The footprint stays separate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ParityCarryRefs( Acec2_Man_t * m, Acec2_Cell_t * c, Vec_Int_t * seen, int Stamp, Vec_Int_t * stack )
{
    Acec2_ParityCtx_t * p = m->pParity; Gia_Obj_t * o; Vec_Int_t * atoms;
    int form, id, pin, fan, low, high, mid, steps = 0, refs = Vec_IntEntry(m->vRefs, c->Out[1] >> 1);
    if ( !p || c->nIns != 2 || !c->Proof ||
         ((Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, c->Proof-1))->Kind != 4 ) return c->Ext[1];
    form = Vec_IntEntry(p->vForms, c->Out[0] >> 1); if ( form < 0 ) return c->Ext[1];
    atoms = Hsh_VecReadEntry(p->hSets, form >> 1);
    Vec_IntClear(stack); Vec_IntPush(stack, c->Out[0] >> 1);
    while ( Vec_IntSize(stack) )
    {
        id = Vec_IntPop(stack);
        if ( !id || id == (c->Out[1] >> 1) || Vec_IntEntry(seen, id) == Stamp ) continue;
        Vec_IntWriteEntry(seen, id, Stamp);
        low = 0; high = Vec_IntSize(atoms);
        while ( low < high ) { mid = low+(high-low)/2; if ( Vec_IntEntry(atoms, mid) < id ) low = mid+1; else high = mid; }
        if ( low < Vec_IntSize(atoms) && Vec_IntEntry(atoms, low) == id ) continue;
        if ( ++steps > 65536 ) { m->nParityPairLimits++; return c->Ext[1]; }
        if ( !(steps & 255) && Acec2_Stopped(m) ) return c->Ext[1];
        o = Gia_ManObj(m->pGia, id); if ( !Gia_ObjIsAnd(o) ) continue;
        for ( pin = 0; pin < 2+Gia_ObjIsMux(m->pGia, o); pin++ )
        {
            fan = pin == 2 ? Gia_ObjFaninId2(m->pGia, id) : pin ? Gia_ObjFaninId1(o, id) : Gia_ObjFaninId0(o, id);
            refs -= fan == (c->Out[1] >> 1); Vec_IntPush(stack, fan);
        }
    }
    return refs;
}

/**Function*************************************************************

  Synopsis    [Stores a checked parity/carry identity once.]

  Description [The caller has established the integer carry equation. This
  final check also requires the exact parity equation on the source.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_ParityStore( Acec2_Man_t * m, Vec_Ptr_t * candidates, Hsh_VecMan_t * known,
                             Vec_Int_t * key, Acec2_Cell_t * c )
{
    Acec2_Proof_t * proof; int j, identity[4], nKnown;
    for ( j = 0; j < c->nIns; j++ ) identity[j] = c->In[j];
    identity[c->nIns] = c->Out[0];
    if ( !Acec2_ParityZero(m, identity, c->nIns+1) ) { ABC_FREE(c); return 0; }
    Vec_IntClear(key); Vec_IntPush(key, c->nIns);
    for ( j = 0; j < 3; j++ ) Vec_IntPush(key, c->In[j]);
    Vec_IntPushTwo(key, c->Out[0], c->Out[1]); nKnown = Hsh_VecSize(known);
    if ( Hsh_VecManAdd(known, key) != nKnown ) { ABC_FREE(c); return 0; }
    proof = ABC_CALLOC(Acec2_Proof_t, 1); proof->Kind = 4; proof->Domain = 1;
    proof->vIdentity = Vec_IntDup(key); proof->vRoots = Vec_IntAlloc(5);
    for ( j = 0; j < c->nIns; j++ ) Vec_IntPushUnique(proof->vRoots, c->In[j] >> 1);
    Vec_IntPushUnique(proof->vRoots, c->Out[0] >> 1); Vec_IntPushUnique(proof->vRoots, c->Out[1] >> 1);
    Vec_PtrPush(m->vProofs, proof); c->Proof = Vec_PtrSize(m->vProofs);
    Vec_PtrPush(candidates, c); m->nParityPairs++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Composes two half adders whose carries feed an OR.]

  Description [The first sum may be reassociated before reaching the second
  half adder. Exact parity equality establishes this link. The first carry
  and sum cannot both be one, so the two carries are mutually exclusive and
  their OR is their integer sum. No simulation result is used as a proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_ParityChains( Acec2_Man_t * m, Vec_Ptr_t * candidates, Hsh_VecMan_t * known, Vec_Int_t * key )
{
    Gia_Man_t * g = m->pGia; Gia_Obj_t * obj;
    Vec_Int_t * heads, * next;
    Acec2_Cell_t * a, * b, * c, * first, * second;
    int i, j, k, side, pin, n = Vec_PtrSize(candidates), steps = 0, pairs, lhs, rhs, lits[2], t;
    if ( Gia_ManObjNum(g) > ABC_INT_MAX/2 ) { m->nParityPairLimits++; return; }
    heads = Vec_IntStartFull(2*Gia_ManObjNum(g)); next = Vec_IntStartFull(n);
    for ( i = 0; i < n; i++ )
    {
        a = (Acec2_Cell_t *)Vec_PtrEntry(candidates, i); if ( a->nIns != 2 ) continue;
        Vec_IntWriteEntry(next, i, Vec_IntEntry(heads, a->Out[1])); Vec_IntWriteEntry(heads, a->Out[1], i);
    }
    Gia_ManForEachAnd(g, obj, i)
    {
        if ( !(i & 255) && Acec2_Stopped(m) ) break;
        if ( Gia_ObjIsXor(obj) || Gia_ObjIsMux(g, obj) ) continue;
        lhs = Gia_ObjFaninLit0(obj, i) ^ 1; rhs = Gia_ObjFaninLit1(obj, i) ^ 1; pairs = 0;
        for ( j = Vec_IntEntry(heads, lhs); j >= 0; j = Vec_IntEntry(next, j) )
        for ( k = Vec_IntEntry(heads, rhs); k >= 0; k = Vec_IntEntry(next, k) )
        {
            if ( ++steps > 262144 ) { m->nParityPairLimits++; goto finish; }
            if ( ++pairs > 256 ) { m->nParityPairLimits++; goto next_gate; }
            a = (Acec2_Cell_t *)Vec_PtrEntry(candidates, j); b = (Acec2_Cell_t *)Vec_PtrEntry(candidates, k);
            for ( side = 0; side < 2; side++ )
            for ( pin = 0; pin < 2; pin++ )
            {
                first = side ? b : a; second = side ? a : b;
                lits[0] = first->Out[0]; lits[1] = second->In[pin];
                if ( !Acec2_ParityZero(m, lits, 2) ) continue;
                c = ABC_CALLOC(Acec2_Cell_t, 1); c->nIns = 3; c->Tree = -1;
                c->In[0] = first->In[0]; c->In[1] = first->In[1]; c->In[2] = second->In[pin^1];
                if ( (c->In[0] >> 1) == (c->In[2] >> 1) || (c->In[1] >> 1) == (c->In[2] >> 1) )
                { ABC_FREE(c); continue; }
                c->Out[0] = second->Out[0]; c->Out[1] = 2*i+1;
                // Use the same full-adder orientation as the cut matcher.
                for ( t = 0; t < 3; t++ ) c->In[t] ^= 1;
                c->Out[0] ^= 1; c->Out[1] ^= 1;
                if ( c->In[0] > c->In[1] ) ABC_SWAP(int, c->In[0], c->In[1]);
                if ( c->In[1] > c->In[2] ) ABC_SWAP(int, c->In[1], c->In[2]);
                if ( c->In[0] > c->In[1] ) ABC_SWAP(int, c->In[0], c->In[1]);
                if ( Acec2_ParityStore(m, candidates, known, key, c) )
                {
                    Acec2_Proof_t * proof = (Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, c->Proof-1);
                    proof->vChain = Vec_IntAlloc(8);
                    Vec_IntPushTwo(proof->vChain, first->In[0], first->In[1]);
                    Vec_IntPushTwo(proof->vChain, first->Out[0], first->Out[1]);
                    Vec_IntPushTwo(proof->vChain, second->In[pin], second->In[pin^1]);
                    Vec_IntPushTwo(proof->vChain, second->Out[0], second->Out[1]);
                    proof->ChainProof[0] = first->Proof; proof->ChainProof[1] = second->Proof;
                }
            }
        }
next_gate: ;
    }
finish:
    Vec_IntFree(heads); Vec_IntFree(next);
}

/**Function*************************************************************

  Synopsis    [Pairs AND/majority cuts with equivalent reassociated sums.]

  Description [All existing candidates remain available. New identities are
  checked on the source and retained even when the reconstruction cover does
  not select them. Each support is compared exactly after its hash lookup.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_PairParities( Acec2_Man_t * m, Vec_Ptr_t * candidates )
{
    Acec2_ParityCtx_t * p = m->pParity;
    Hsh_VecMan_t * known = Hsh_VecManStart(100);
    Vec_Int_t * key = Vec_IntAlloc(6), * truth = Vec_IntStartFull(Gia_ManObjNum(m->pGia));
    Vec_Int_t * stack = Vec_IntAlloc(32), * touched = Vec_IntAlloc(32);
    Acec2_Cell_t * c;
    int i, j, id, set, phase, carry[6], sum[6], pairs;
    Vec_IntWriteEntry(truth, 0, 0);
    Vec_PtrForEachEntry(Acec2_Cell_t *, candidates, c, i)
    {
        Vec_IntClear(key); Vec_IntPush(key, c->nIns);
        for ( j = 0; j < 3; j++ ) Vec_IntPush(key, c->In[j]);
        Vec_IntPushTwo(key, c->Out[0], c->Out[1]); Hsh_VecManAdd(known, key);
    }
    for ( i = 0; p && i < Vec_IntSize(m->vCarries) && !Acec2_Stopped(m); i += 6 )
    {
        memcpy(carry, Vec_IntEntryP(m->vCarries, i), sizeof(carry));
        Vec_IntClear(p->vWork); phase = 0;
        for ( j = 0; j < carry[0]; j++ ) phase ^= Acec2_ParityAppend(p, p->vWork, 2*carry[j+1]);
        Acec2_ParityReduce(p->vWork); set = Acec2_ParityLookup(p, p->vWork);
        if ( set < 0 ) continue;
        if ( !Acec2_CheckCut(m, carry, truth, stack, touched) ) continue;
        pairs = 0;
        for ( id = Vec_IntEntry(p->vHeads, set); id >= 0; id = Vec_IntEntry(p->vNext, id) )
        {
            if ( id == carry[4] ) continue;
            if ( pairs++ == 128 ) { m->nParityPairLimits++; break; }
            memcpy(sum, carry, 4*sizeof(int)); sum[4] = id;
            sum[5] = (carry[0] == 3 ? 0x96 : 0x66) ^ ((phase ^ (Vec_IntEntry(p->vForms, id) & 1)) ? 255 : 0);
            c = Acec2_MatchCut(sum, carry); if ( !c ) continue;
            // Ordinary shared-cut pairs already have their own enumeration
            // and limit accounting. This pass adds the missing association,
            // rather than bypassing that pair limit with source certificates.
            if ( Acec2_CheckCut(m, sum, truth, stack, touched) ) { ABC_FREE(c); continue; }
            Acec2_ParityStore(m, candidates, known, key, c);
        }
    }
    if ( p && !m->fStopped ) Acec2_ParityChains(m, candidates, known, key);
    Hsh_VecManStop(known); Vec_IntFree(key); Vec_IntFree(truth); Vec_IntFree(stack); Vec_IntFree(touched);
}

/**Function*************************************************************

  Synopsis    [Pairs newly proved carries with all equal parity associations.]

  Description [A new sum inherits only the earlier checked carry equation.
  Its own parity is checked exactly. The subsequent half-adder chain pass
  can combine old and new cells without changing the reconstruction cover.]

  SideEffects [Appends certificates and cells; existing entries retain IDs.]

  SeeAlso     []

***********************************************************************/
void Acec2_PairRecovered( Acec2_Man_t * m, Vec_Ptr_t * candidates, int First )
{
    Acec2_ParityCtx_t * p = m->pParity;
    Hsh_VecMan_t * known; Vec_Int_t * key; Acec2_Cell_t * base, * c;
    int i, j, id, phase, set, pairs, last = Vec_PtrSize(candidates);
    if ( !p || First >= last || Acec2_Stopped(m) ) return;
    known = Hsh_VecManStart(100); key = Vec_IntAlloc(6);
    Vec_PtrForEachEntry(Acec2_Cell_t *, candidates, c, i)
    {
        Vec_IntClear(key); Vec_IntPush(key, c->nIns);
        for ( j = 0; j < 3; j++ ) Vec_IntPush(key, c->In[j]);
        Vec_IntPushTwo(key, c->Out[0], c->Out[1]); Hsh_VecManAdd(known, key);
    }
    for ( i = First; i < last && !Acec2_Stopped(m); i++ )
    {
        base = (Acec2_Cell_t *)Vec_PtrEntry(candidates, i);
        Vec_IntClear(p->vWork); phase = 0;
        for ( j = 0; j < base->nIns; j++ ) phase ^= Acec2_ParityAppend(p, p->vWork, base->In[j]);
        Acec2_ParityReduce(p->vWork); set = Acec2_ParityLookup(p, p->vWork);
        if ( set < 0 ) continue;
        pairs = 0;
        for ( id = Vec_IntEntry(p->vHeads, set); id >= 0; id = Vec_IntEntry(p->vNext, id) )
        {
            if ( id == (base->Out[1] >> 1) ) continue;
            if ( pairs++ == 128 ) { m->nParityPairLimits++; break; }
            c = ABC_ALLOC(Acec2_Cell_t, 1); *c = *base;
            c->Proof = 0; c->Out[0] = 2*id+(phase ^ (Vec_IntEntry(p->vForms, id) & 1));
            if ( Acec2_ParityStore(m, candidates, known, key, c) )
                ((Acec2_Proof_t *)Vec_PtrEntry(m->vProofs, c->Proof-1))->ChainProof[0] = base->Proof;
        }
    }
    if ( !Acec2_Stopped(m) ) Acec2_ParityChains(m, candidates, known, key);
    Hsh_VecManStop(known); Vec_IntFree(key);
}

/**Function*************************************************************

  Synopsis    [Releases the private parity-expression index.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_ParityFree( Acec2_ParityCtx_t * p )
{
    if ( !p ) return;
    Hsh_VecManStop(p->hSets); Vec_IntFree(p->vForms);
    Vec_IntFree(p->vHeads); Vec_IntFree(p->vNext); Vec_IntFree(p->vWork);
    Vec_IntFreeP(&p->vCheckTruth); Vec_IntFreeP(&p->vCheckStack); Vec_IntFreeP(&p->vCheckTouched); ABC_FREE(p);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
