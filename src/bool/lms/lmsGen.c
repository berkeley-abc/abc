/**CFile****************************************************************

  FileName    [lmsGen.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Generate timing-driven AIG structures from truth tables.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2026.]

  Revision    [$Id: lmsGen.c,v 1.00 2026/10/04 00:00:00 alanmi Exp $]

***********************************************************************/
#include "lmsInt.h"
#include "opt/dau/dau.h"
#include "misc/util/utilTruth.h"
#include "map/if/acd/ac_wrapper.h"
#include "bool/kit/kit.h"
#include "bool/bdc/bdc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define LMG_NODES 128
#define LMG_PROFILES 1024

typedef struct Lmg_Graph_t_ {
    int nVars, nNodes, Root, fFailed, fXor;
    int Fans[LMG_NODES][2], Times[LMG_NODES + 7];
    void * pKernels;
    struct Lmg_Func_t_ * pOwner;
} Lmg_Graph_t;
typedef struct Lmg_Residual_t_ {
    struct Lmg_Residual_t_ * pNext;
    word Truth;
    int Times[5], Size, Fans[1];
} Lmg_Residual_t;
typedef struct Lmg_Child_t_ {
    struct Lmg_Child_t_ * pNext;
    word Truth;
    struct Lmg_Func_t_ * pFunc;
} Lmg_Child_t;
typedef struct Lmg_AcdRecord_t_ {
    struct Lmg_AcdRecord_t_ * pNext;
    unsigned Mask;
    int LutSize;
    unsigned char Record[256];
} Lmg_AcdRecord_t;
typedef struct Lmg_Profile_t_ {
    struct Lmg_Profile_t_ * pNext;
    int Area, nAnds, Root, Depths[6];
    int Fans[1];
} Lmg_Profile_t;
typedef struct Lmg_Func_t_ {
    word Truth;
    int Valid, nVars, Prime;
    char * pDsd;
    char * pFusedDsd;
    char * pMore[6];
    Lmg_AcdRecord_t * pAcd;
    Lmg_Profile_t * pProfiles;
    int nProfiles, nDropped, fReady;
    Vec_Int_t * pCovers[4];
    Vec_Int_t * pCofCovers[6][4];
    Vec_Int_t * pBidec[2];
    void * pKernels;
    Lmg_Residual_t * pResiduals;
    Lmg_Child_t * pChildren;
} Lmg_Func_t;


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static void Lmg_GraphInit( Lmg_Graph_t * p, int nVars, const int * pTimes,
    void * pKernels, Lmg_Func_t * pOwner )
{
    int i;
    memset(p, 0, sizeof(*p));
    p->nVars = nVars; p->Times[0] = -1000000;
    p->pKernels = pKernels; p->pOwner = pOwner;
    p->fXor = Lms_KernelIsXor(pKernels);
    for ( i = 0; i < nVars; ++i ) p->Times[i+1] = pTimes[i];
}

// Trials only need the populated prefix of the graph.
static void Lmg_Copy( Lmg_Graph_t * pDst, const Lmg_Graph_t * pSrc )
{
    pDst->nVars = pSrc->nVars; pDst->nNodes = pSrc->nNodes; pDst->Root = pSrc->Root;
    pDst->pKernels = pSrc->pKernels;
    pDst->pOwner = pSrc->pOwner;
    pDst->fFailed = pSrc->fFailed;
    pDst->fXor = pSrc->fXor;
    memcpy(pDst->Fans, pSrc->Fans, pSrc->nNodes * sizeof(pSrc->Fans[0]));
    memcpy(pDst->Times, pSrc->Times, (pSrc->nVars + 1 + pSrc->nNodes) * sizeof(int));
}
// Preserve the historical AND-mode tie break. XOR-mode trials use the same
// live logical-cover area as the final profile pool, not serialized ANDs.
static int Lmg_TrialArea( Lmg_Graph_t * p, int Root )
{
    return p->fXor ? Lms_AigXorMetrics(p->nVars, &p->Fans[0][0], p->nNodes, Root, NULL) : p->nNodes;
}
static int Lmg_And( Lmg_Graph_t * p, int a, int b )
{
    int i;
    if ( a < 0 || b < 0 ) { p->fFailed = 1; return 0; }
    if ( !a || !b || a == (b ^ 1) ) return 0;
    if ( a == 1 || a == b ) return b;
    if ( b == 1 ) return a;
    if ( a > b ) ABC_SWAP( int, a, b );
    for ( i = 0; i < p->nNodes; ++i )
        if ( p->Fans[i][0] == a && p->Fans[i][1] == b )
            return 2 * (p->nVars + 1 + i);
    if ( p->nNodes == LMG_NODES ) { p->fFailed = 1; return 0; }
    i = p->nVars + 1 + p->nNodes;
    p->Fans[p->nNodes][0] = a;
    p->Fans[p->nNodes++][1] = b;
    p->Times[i] = 1 + Abc_MaxInt(p->Times[a >> 1], p->Times[b >> 1]);
    if ( p->fXor && Lms_AigXorInputs(p->nVars, &p->Fans[0][0], i, &a, &b) )
        p->Times[i] = 1 + Abc_MaxInt(p->Times[a], p->Times[b]);
    return 2 * i;
}
static int Lmg_Or( Lmg_Graph_t * p, int a, int b )
{
    return Lmg_And(p, a ^ 1, b ^ 1) ^ 1;
}
static int Lmg_Xor( Lmg_Graph_t * p, int a, int b )
{
    int u = Lmg_And(p, a, b ^ 1), v = Lmg_And(p, a ^ 1, b);
    return Lmg_Or(p, u, v);
}
static int Lmg_Mux( Lmg_Graph_t * p, int c, int t, int e )
{
    int u, v;
    if ( c < 0 || t < 0 || e < 0 ) { p->fFailed = 1; return 0; }
    if ( c < 2 ) return c ? t : e;
    if ( t == e ) return t;
    if ( t == 0 ) return Lmg_And(p, c^1, e);
    if ( e == 0 ) return Lmg_And(p, c, t);
    if ( t == 1 ) return Lmg_Or(p, c, e);
    if ( e == 1 ) return Lmg_Or(p, c^1, t);
    if ( t == (e ^ 1) ) return Lmg_Xor(p, c, e);
    u = Lmg_And(p, c, t); v = Lmg_And(p, c ^ 1, e);
    return Lmg_Or(p, u, v);
}
static unsigned Lmg_Cofactor( unsigned t, int n, int v, int c );
static int Lmg_Small( Lmg_Graph_t * p, unsigned t, int n, int * pLits );
static int Lmg_Residual5( Lmg_Graph_t * p, word Truth, int * pLits );
static int Lmg_KernelBuild( Lmg_Graph_t * p, unsigned Truth, int * pLits )
{
    int Buffer[255], Times[4], Depths[4], Map[132], Lits[4], i, j, n = 4, Root;
    Vec_Int_t V = { 255, 0, Buffer };
    memcpy(Lits, pLits, sizeof(Lits));
    for ( i = n-1; i >= 0; --i )
    {
        unsigned a = Lmg_Cofactor(Truth, n, i, 0), b = Lmg_Cofactor(Truth, n, i, 1);
        if ( Lits[i] >= 2 && a != b ) continue;
        Truth = Lits[i] < 2 && Lits[i] ? b : a;
        for ( j = i; j+1 < n; ++j ) Lits[j] = Lits[j+1];
        --n;
    }
    if ( n < 4 ) return Lmg_Small(p, Truth, n, Lits);
    for ( i = 0; i < 4; ++i ) Times[i] = p->Times[Lits[i]>>1];
    if ( Lms_KernelFrontier(p->pKernels, Truth, Times, &V, Depths) < 0 ||
         p->nNodes+Vec_IntSize(&V)/2 >= LMG_NODES ) return -1;
    Map[0] = 0;
    for ( i = 0; i < 4; ++i ) Map[i+1] = Lits[i];
    for ( i = 0; i < Vec_IntSize(&V)/2; ++i )
    {
        int a = Vec_IntEntry(&V, 2*i), b = Vec_IntEntry(&V, 2*i+1);
        Map[i+5] = Lmg_And(p, Map[a>>1]^(a&1), Map[b>>1]^(b&1));
    }
    Root = Vec_IntEntryLast(&V);
    return Map[Root>>1] ^ (Root&1);
}
// Huffman-style arrival balancing; inversions are free in the AIG model.
static int Lmg_Balance( Lmg_Graph_t * p, int * pLits, int n, int fXor )
{
    int i, k, a, b;
    while ( n > 1 )
    {
        for ( k = 0, i = 1; i < n; ++i )
            if ( p->Times[pLits[i] >> 1] < p->Times[pLits[k] >> 1] ) k = i;
        a = pLits[k]; pLits[k] = pLits[--n];
        for ( k = 0, i = 1; i < n; ++i )
            if ( p->Times[pLits[i] >> 1] < p->Times[pLits[k] >> 1] ) k = i;
        b = pLits[k];
        pLits[k] = fXor ? Lmg_Xor(p, a, b) : Lmg_And(p, a, b);
    }
    return pLits[0];
}
static unsigned Lmg_Cofactor( unsigned t, int n, int v, int c )
{
    unsigned r = 0;
    int i, m = (1 << v) - 1;
    for ( i = 0; i < (1 << (n - 1)); ++i )
        r |= ((t >> ((i & m) | ((i & ~m) << 1) | (c << v))) & 1) << i;
    return r;
}
// All three-input residuals are synthesized, not looked up. Enumerating
// Shannon roots also considers different short paths for late inputs.
// The fallback trials do not reserve nodes up front: Lmg_And bounds every
// insertion and marks fFailed. Failed trials never displace valid ones;
// if all trials overflow, the caller rejects this candidate at export.
static int Lmg_Small( Lmg_Graph_t * p, unsigned t, int n, int * pLits )
{
    Lmg_Graph_t Best, Trial;
    int v, i, k, a, b, r, BestLit = -1, BestDelay = ABC_INFINITY, BestArea = ABC_INFINITY;
    unsigned Mask = (1u << (1 << n)) - 1;
    t &= Mask;
    if ( !t || t == Mask ) return t != 0;
    if ( n == 1 ) return pLits[0] ^ (t == 1);
    if ( n == 2 && (t == 6 || t == 9) ) return Lmg_Xor(p, pLits[0], pLits[1]) ^ (t == 9);
    // Repeated decompositions often synthesize identical small residuals.
    // Reuse the kernel's frozen profiles instead of replaying Shannon trials.
    // Dummy inputs specialize to zero; the truth is independent of them.
    if ( n <= 3 )
    {
        int Buffer[255], Times[4] = {0}, Depths[4], Map[132], Root;
        unsigned Truth = 0;
        Vec_Int_t V = {255,0,Buffer};
        for ( i = 0; i < 16; i += 1 << n ) Truth |= t << i;
        for ( i = 0; i < n; ++i ) Times[i] = p->Times[pLits[i]>>1];
        if ( Lms_KernelFrontier(p->pKernels, Truth, Times, &V, Depths) >= 0 &&
             p->nNodes+Vec_IntSize(&V)/2 < LMG_NODES )
        {
            Map[0] = 0;
            for ( i = 0; i < 4; ++i ) Map[i+1] = i < n ? pLits[i] : 0;
            for ( i = 0; i < Vec_IntSize(&V)/2; ++i )
            {
                a = Vec_IntEntry(&V,2*i); b = Vec_IntEntry(&V,2*i+1);
                Map[i+5] = Lmg_And(p, Map[a>>1]^(a&1), Map[b>>1]^(b&1));
            }
            Root = Vec_IntEntryLast(&V);
            return Map[Root>>1]^(Root&1);
        }
    }
    for ( v = 0; v < n; ++v )
    {
        int Lits[4];
        Lmg_Copy(&Trial, p);
        for ( k = i = 0; i < n; ++i ) if ( i != v ) Lits[k++] = pLits[i];
        a = Lmg_Small(&Trial, Lmg_Cofactor(t, n, v, 1), n-1, Lits);
        b = Lmg_Small(&Trial, Lmg_Cofactor(t, n, v, 0), n-1, Lits);
        r = Lmg_Mux(&Trial, pLits[v], a, b);
        if ( Trial.fFailed ) continue;
        if ( Trial.Times[r >> 1] < BestDelay ||
             (Trial.Times[r >> 1] == BestDelay && Lmg_TrialArea(&Trial, r) < BestArea) )
        {
            Lmg_Copy(&Best, &Trial); BestLit = r; BestDelay = Trial.Times[r >> 1]; BestArea = Lmg_TrialArea(&Trial, r);
        }
    }
    // Majority and its input/output phases admit a four-AND factorization.
    if ( n == 3 )
    for ( k = 0; k < 8; ++k )
    {
        unsigned m = 0;
        for ( i = 0; i < 8; ++i )
            if ( Abc_TtBitCount16(i ^ k) >= 2 ) m |= 1u << i;
        if ( t != m && t != (m ^ 255) ) continue;
        for ( v = 0; v < 3; ++v )
        {
            int x = pLits[(v+1)%3] ^ ((k >> ((v+1)%3)) & 1);
            int y = pLits[(v+2)%3] ^ ((k >> ((v+2)%3)) & 1);
            int z = pLits[v] ^ ((k >> v) & 1);
            Lmg_Copy(&Trial, p);
            a = Lmg_And(&Trial, x, y); b = Lmg_Or(&Trial, x, y);
            b = Lmg_And(&Trial, z, b); r = Lmg_Or(&Trial, a, b) ^ (t != m);
            if ( Trial.fFailed ) continue;
            if ( Trial.Times[r >> 1] < BestDelay ||
                 (Trial.Times[r >> 1] == BestDelay && Lmg_TrialArea(&Trial, r) < BestArea) )
            { Lmg_Copy(&Best, &Trial); BestLit = r; BestDelay = Trial.Times[r >> 1]; BestArea = Lmg_TrialArea(&Trial, r); }
        }
    }
    if ( BestLit < 0 ) { p->fFailed = 1; return 0; }
    Lmg_Copy(p, &Best);
    return BestLit;
}
// Scan the common DSD token header. Prime nodes have an explicit kind,
// rather than retaining the first hexadecimal digit as an operator code.
static int Lmg_ParseHead( const char ** pp, int * pInv, char * pKind,
    char * pEnd, unsigned * pTruth )
{
    const char * s = *pp;
    *pInv = 0; *pTruth = 0; *pEnd = 0;
    if ( *s == '!' ) { *pInv = 1; ++s; }
    if ( !*s ) return 0;
    *pKind = *s++;
    if ( *pKind >= 'a' && *pKind <= 'f' ) { *pp = s; return 1; }
    if ( *pKind == '(' || *pKind == '[' || *pKind == '<' )
        *pEnd = *pKind == '(' ? ')' : *pKind == '[' ? ']' : '>';
    else
    {
        --s;
        while ( *s && *s != '{' )
        {
            char h = *s++;
            if ( !((h >= '0' && h <= '9') || (h >= 'A' && h <= 'F')) ) return 0;
            *pTruth = (*pTruth << 4) | (unsigned)(h <= '9' ? h-'0' : h-'A'+10);
        }
        if ( !*s ) return 0;
        ++s; *pKind = '{'; *pEnd = '}';
    }
    *pp = s;
    return 1;
}

static int Lmg_Parse( Lmg_Graph_t * p, const char ** pp, int * pVars, int nPrimeMax )
{
    int Inv = 0, Lits[6], n = 0, r;
    char c, End;
    unsigned t = 0;
    if ( !Lmg_ParseHead(pp, &Inv, &c, &End, &t) ) return -1;
    if ( c >= 'a' && c <= 'f' ) return (pVars ? pVars[c-'a'] : 2*(c-'a'+1)) ^ Inv;
    while ( **pp != End )
    {
        if ( !**pp || n == 6 ) return -1;
        Lits[n] = Lmg_Parse(p, pp, pVars, nPrimeMax);
        if ( Lits[n++] < 0 ) return -1;
    }
    ++*pp;
    if ( End == '}' ) { if ( n > nPrimeMax ) return -1; r = Lmg_Small(p, t, n, Lits); }
    else if ( c == '<' ) { if ( n != 3 ) return -1; r = Lmg_Mux(p, Lits[0], Lits[1], Lits[2]); }
    else { if ( !n ) return -1; r = Lmg_Balance(p, Lits, n, c == '['); }
    return r ^ Inv;
}
typedef struct Lmg_Op_t_ {
    word Truth;
    int nFans, Fans[6];
    int Kind, Inv, nOriginal, Original[6];
} Lmg_Op_t;
static int Lmg_SopAndPlain( Lmg_Graph_t * p, int a, int b );
static int Lmg_SopOr( Lmg_Graph_t * p, int a, int b );
// Fuse a parent with each eligible child before lowering the pair. In
// particular a XOR selector and its MUX become one four-input function.
static int Lmg_ParseFused( Lmg_Graph_t * p, const char ** pp, Lmg_Op_t * pOp, int Mode, int * pfXorMux )
{
    Lmg_Op_t Children[6];
    int Lits[6], n = 0, Inv = 0, r, i, a;
    unsigned t = 0;
    word Truth = 0;
    char c, End;
    memset(pOp, 0, sizeof(*pOp));
    if ( !Lmg_ParseHead(pp, &Inv, &c, &End, &t) ) return -1;
    if ( c >= 'a' && c <= 'f' ) return 2*(c-'a'+1) ^ Inv;
    while ( **pp != End )
    {
        if ( !**pp || n == 6 ) return -1;
        Lits[n] = Lmg_ParseFused(p, pp, Children+n, Mode, pfXorMux);
        if ( Lits[n++] < 0 ) return -1;
    }
    ++*pp;
    if ( !n || p->nNodes > LMG_NODES-32 ) return -1;
    if ( End == '}' )
    { if ( n > 4 ) return -1; r = n == 4 ? Lmg_KernelBuild(p, t, Lits) : Lmg_Small(p, t, n, Lits); }
    else if ( c == '<' )
    { if ( n != 3 ) return -1; r = Lmg_Mux(p, Lits[0], Lits[1], Lits[2]); }
    else
    {
        int Balanced[6];
        memcpy(Balanced, Lits, n*sizeof(int));
        r = Lmg_Balance(p, Balanced, n, c == '[');
    }
    if ( r < 0 || p->fFailed ) return -1;
    for ( a = 0; a < (1 << n); ++a )
    {
        int Value = End == '}' ? ((t >> a)&1) : c == '(' ? a == (1 << n)-1 :
            c == '[' ? (Abc_TtBitCount16(a)&1) : ((a >> ((a&1) ? 1 : 2))&1);
        Truth |= (word)Value << a;
    }
    // Split an XOR selector on either operand. Build the guarded branches
    // as products of sums before balancing, not as isolated MUX outputs:
    // MUX(x^y,P,Q) = !x (!y|P)(y|Q) | x (!y|Q)(y|P).
    // This exposes early guards even when x itself is a compound function.
    if ( c == '<' && Children[0].Kind == '[' && Children[0].nOriginal == 2 )
        *pfXorMux = 1;
    if ( c == '<' && Children[0].Kind == '[' && Children[0].nOriginal == 2 )
    for ( i = 0; i < 2; ++i )
    {
        Lmg_Graph_t Trial;
        int x = Children[0].Original[i], y = Children[0].Original[1-i];
        int P = Lits[1+Children[0].Inv], Q = Lits[2-Children[0].Inv];
        int C0, C1, T0, T1, Root;
        Lmg_Copy(&Trial, p);
        C0 = Lmg_SopOr(&Trial, y^1, P); C1 = Lmg_SopOr(&Trial, y, Q);
        T0 = Lmg_SopAndPlain(&Trial, x^1, C0);
        T0 = Lmg_SopAndPlain(&Trial, T0, C1);
        C0 = Lmg_SopOr(&Trial, y^1, Q); C1 = Lmg_SopOr(&Trial, y, P);
        T1 = Lmg_SopAndPlain(&Trial, x, C0);
        T1 = Lmg_SopAndPlain(&Trial, T1, C1);
        if ( T0 < 0 || T1 < 0 || Trial.nNodes >= LMG_NODES-1 ) continue;
        Root = Lmg_Or(&Trial, T0, T1);
        if ( Trial.fFailed ) continue;
        if ( Mode == i+1 || (!Mode && Trial.Times[Root>>1] < p->Times[r>>1]) )
        { Lmg_Copy(p,&Trial); r = Root; }
    }
    for ( i = 0; i < n; ++i )
    {
        Lmg_Graph_t Trial;
        unsigned Composed = 0;
        int Fans[4], j, k = 0, Count = n-1+Children[i].nFans, Root;
        if ( Mode && c == '<' && Children[0].Kind == '[' && Children[0].nOriginal == 2 ) continue;
        if ( !Children[i].nFans || Count > 4 ) continue;
        for ( j = 0; j < n && k < 4; ++j )
            if ( j == i )
            { int z; for ( z = 0; z < Children[i].nFans && k < 4; ++z ) Fans[k++] = Children[i].Fans[z]; }
            else Fans[k++] = Lits[j];
        if ( k != Count ) continue;
        for ( a = 0; a < 16; ++a )
        {
            int Index = 0, Pos = 0;
            for ( j = 0; j < n; ++j )
            {
                int Value;
                if ( j == i )
                {
                    int Mask = (1 << Children[i].nFans)-1;
                    Value = (int)((Children[i].Truth >> ((a >> Pos)&Mask))&1);
                    Pos += Children[i].nFans;
                }
                else Value = (a >> Pos++)&1;
                Index |= Value << j;
            }
            Composed |= (unsigned)((Truth >> Index)&1) << a;
        }
        Lmg_Copy(&Trial, p);
        Root = Count == 4 ? Lmg_KernelBuild(&Trial, Composed, Fans) : Lmg_Small(&Trial, Composed, Count, Fans);
        if ( Root < 0 || Trial.fFailed || Trial.Times[Root>>1] >= p->Times[r>>1] ) continue;
        Lmg_Copy(p, &Trial); r = Root;
    }
    pOp->Truth = Truth; pOp->nFans = n; memcpy(pOp->Fans, Lits, n*sizeof(int));
    if ( Inv ) pOp->Truth = ~pOp->Truth;
    pOp->Kind = End == '}' ? '{' : c; pOp->Inv = Inv; pOp->nOriginal = n;
    memcpy(pOp->Original, Lits, n*sizeof(int));
    return r ^ Inv;
}
static int Lmg_Export( Lmg_Graph_t * pG, Vec_Int_t * vAig, int * pDepths )
{
    int nVars = pG->nVars;
    int Map[LMG_NODES+7], Depth[LMG_NODES+7], i, j, Root;
    if ( pG->Root < 0 || pG->fFailed ) return -1;
    // Compact the live cone and derive exact per-pin depths, including holes.
    for ( i = 0; i < LMG_NODES+7; ++i ) { Map[i] = -1; Depth[i] = -1; }
    Depth[pG->Root >> 1] = 0;
    for ( i = pG->nNodes-1; i >= 0; --i )
        if ( Depth[nVars+1+i] >= 0 )
            for ( j = 0; j < 2; ++j )
            {
                int v = pG->Fans[i][j] >> 1;
                Depth[v] = Abc_MaxInt(Depth[v], Depth[nVars+1+i]+1);
            }
    Vec_IntClear(vAig);
    for ( i = 0; i <= nVars; ++i ) Map[i] = i;
    for ( i = 0; i < pG->nNodes; ++i )
        if ( Depth[nVars+1+i] >= 0 )
        {
            Map[nVars+1+i] = nVars+1+Vec_IntSize(vAig)/2;
            for ( j = 0; j < 2; ++j )
                Vec_IntPush(vAig, 2*Map[pG->Fans[i][j] >> 1] + (pG->Fans[i][j] & 1));
        }
    Root = 2*Map[pG->Root >> 1] + (pG->Root & 1);
    Vec_IntPush(vAig, Root);
    for ( i = 0; i < nVars; ++i ) pDepths[i] = Depth[i+1];
    if ( pG->fXor ) Lms_AigXorMetrics(nVars, Vec_IntArray(vAig), Vec_IntSize(vAig)/2, Root, pDepths);
    return pG->Root < 2 ? 0 : pG->Times[pG->Root >> 1];
}
static int Lmg_Build( word Truth, int nVars, int * pTimes, const char * pDsd, Vec_Int_t * vAig, int * pDepths, void * pKernels )
{
    Lmg_Graph_t G;
    Lmg_GraphInit(&G, nVars, pTimes, pKernels, NULL);
    G.Root = Truth == 0 || Truth == ~(word)0 ? Truth != 0 : Lmg_Parse(&G, &pDsd, NULL, 3);
    return Lmg_Export(&G, vAig, pDepths);
}

// ACD produces LUT functions, not AIG costs. Synthesize each component using
// actual intermediate arrivals, then compact and cost the complete live cone.
// The record uses local pin order and topological LUT IDs; no canonicalization.
static int Lmg_AcdBuild( unsigned char * pRecord, int nVars, int * pTimes,
    Vec_Int_t * vAig, int * pDepths, void * pKernels )
{
    Lmg_Graph_t G;
    int Map[16], i, j, Pos = 2, nLuts = pRecord[1];
    if ( nLuts < 1 || nLuts > 8 ) return -1;
    Lmg_GraphInit(&G, nVars, pTimes, pKernels, NULL);
    for ( i = 0; i < nVars; ++i ) Map[i] = 2*(i+1);
    for ( i = 0; i < nLuts; ++i )
    {
        int Lits[4], n, nBytes;
        unsigned t = 0;
        if ( Pos >= pRecord[0] ) return -1;
        n = pRecord[Pos++];
        if ( n > 4 ) return -1;
        nBytes = n <= 3 ? 1 : 2;
        if ( Pos+n+nBytes > pRecord[0] ) return -1;
        for ( j = 0; j < n; ++j )
        {
            int Id = pRecord[Pos++];
            if ( Id >= nVars+i ) return -1;
            Lits[j] = Map[Id];
        }
        for ( j = 0; j < nBytes; ++j ) t |= (unsigned)pRecord[Pos++] << (8*j);
        // Four-input exhaustive Shannon trials are bounded. Each component
        // adds at most 21 ANDs, and generated records here have at most 5 LUTs.
        if ( G.nNodes > LMG_NODES-32 ) return -1;
        if ( n < 4 ) Map[nVars+i] = Lmg_Small(&G, t, n, Lits);
        else
        {
            Map[nVars+i] = Lmg_KernelBuild(&G, t, Lits);
            if ( Map[nVars+i] < 0 ) return -1;
        }
    }
    if ( Pos != pRecord[0] ) return -1;
    G.Root = Map[nVars+nLuts-1];
    return Lmg_Export(&G, vAig, pDepths);
}

// Pin-depth dominance is arrival-independent. Keep whole compact AIGs, not
// LUT records, so a new timing vector needs only six additions/comparisons.
// The cap is enforced only while constructing the deterministic pool.
static int Lmg_ProfileDominates( int nVars, int Area0, int * pDepths0,
    int Area1, int * pDepths1 )
{
    int i;
    if ( Area0 > Area1 ) return 0;
    for ( i = 0; i < nVars; ++i ) if ( pDepths0[i] > pDepths1[i] ) return 0;
    return 1;
}
static int Lmg_ProfileAdd( Lmg_Func_t * f, Vec_Int_t * v, int * pDepths )
{
    Lmg_Profile_t * p, ** pp;
    int nAnds = Vec_IntSize(v)/2;
    int Area = Lms_KernelIsXor(f->pKernels) ? Lms_AigXorMetrics(f->nVars, Vec_IntArray(v), nAnds, Vec_IntEntryLast(v), NULL) : nAnds;
    for ( p = f->pProfiles; p; p = p->pNext )
        if ( Lmg_ProfileDominates(f->nVars, p->Area, p->Depths, Area, pDepths) ) return 0;
    for ( pp = &f->pProfiles; *pp; )
        if ( Lmg_ProfileDominates(f->nVars, Area, pDepths, (*pp)->Area, (*pp)->Depths) )
        { p = *pp; *pp = p->pNext; ABC_FREE(p); --f->nProfiles; }
        else pp = &(*pp)->pNext;
    if ( f->nProfiles == LMG_PROFILES ) { ++f->nDropped; return -1; }
    p = (Lmg_Profile_t *)ABC_ALLOC(char, sizeof(Lmg_Profile_t) + 2*nAnds*sizeof(int));
    p->Area = Area; p->nAnds = nAnds; p->Root = Vec_IntEntryLast(v);
    memcpy(p->Depths, pDepths, f->nVars*sizeof(int));
    if ( nAnds ) memcpy(p->Fans, Vec_IntArray(v), 2*nAnds*sizeof(int));
    p->pNext = f->pProfiles; f->pProfiles = p; ++f->nProfiles;
    return 1;
}
static int Lmg_ProfileSelect( Lmg_Func_t * f, int * pTimes,
    Vec_Int_t * v, int * pDepths )
{
    Lmg_Profile_t * p, * pBest = NULL;
    int i, Best = ABC_INFINITY;
    for ( p = f->pProfiles; p; p = p->pNext )
    {
        int Delay = 0;
        for ( i = 0; i < f->nVars; ++i )
            if ( p->Depths[i] >= 0 ) Delay = Abc_MaxInt(Delay, pTimes[i]+p->Depths[i]);
        if ( !pBest || Delay < Best || (Delay == Best && p->Area < pBest->Area) )
        { pBest = p; Best = Delay; }
    }
    Vec_IntClear(v);
    if ( !pBest ) return -1;
    Vec_IntPushArray(v, pBest->Fans, 2*pBest->nAnds);
    Vec_IntPush(v, pBest->Root);
    memcpy(pDepths, pBest->Depths, f->nVars*sizeof(int));
    return Best;
}
static void Lmg_FusedProfiles( Lmg_Func_t * f, int * pTimes )
{
    const char * s = f->pDsd ? f->pDsd : f->pFusedDsd;
    int Buffer[2*LMG_NODES+1], Depths[6], Mode, nModes = 1, fXorMux = 0;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    Lmg_Graph_t G;
    Lmg_Op_t Op;
    if ( !s || f->nVars < 3 ) return;
    for ( Mode = 0; Mode < nModes; ++Mode )
    {
        s = f->pDsd ? f->pDsd : f->pFusedDsd;
        Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, f);
        G.Root = Lmg_ParseFused(&G, &s, &Op, Mode, &fXorMux);
        // Only a binary XOR selector has mode-specific alternatives. The
        // parser also finds these inside compound/nested expressions.
        if ( fXorMux ) nModes = 3;
        if ( G.Root < 0 || *s || Lmg_Export(&G, &V, Depths) < 0 ) continue;
        Lmg_ProfileAdd(f, &V, Depths);
    }
}
// Flatten only positive AND edges, preserving complemented subfunctions
// and unit-cost XOR/XNOR roots in the XOR model.
// This balances factor products without delaying late data behind early guards.
static int Lmg_SopLeaves( Lmg_Graph_t * p, int Lit, int * pLits, int * pnLits )
{
    int Id = Lit >> 1, a, b;
    if ( !(Lit & 1) && Id > p->nVars &&
         !(p->fXor && Lms_AigXorInputs(p->nVars, &p->Fans[0][0], Id, &a, &b)) )
        return Lmg_SopLeaves(p, p->Fans[Id-p->nVars-1][0], pLits, pnLits) &&
               Lmg_SopLeaves(p, p->Fans[Id-p->nVars-1][1], pLits, pnLits);
    if ( *pnLits == 32 ) return 0;
    pLits[(*pnLits)++] = Lit;
    return 1;
}
static int Lmg_SopAndPlain( Lmg_Graph_t * p, int a, int b )
{
    int Lits[32], n = 0;
    if ( a < 0 || b < 0 || p->nNodes >= LMG_NODES-1 ) return -1;
    if ( !Lmg_SopLeaves(p, a, Lits, &n) || !Lmg_SopLeaves(p, b, Lits, &n) ||
         p->nNodes+n >= LMG_NODES ) return Lmg_And(p, a, b);
    return Lmg_Balance(p, Lits, n, 0);
}
// Distribute an early guard through an OR, balancing the resulting products.
// This is an algebraic move on the constructed graph, not a truth-specific
// pattern. Try both sides and retain the arrival/area winner.
static int Lmg_GuardAnd( Lmg_Graph_t * p, int a, int b, int Limit )
{
    Lmg_Graph_t Best, Trial;
    int r, Side;
    if ( a < 0 || b < 0 ) return -1;
    Lmg_Copy(&Best, p);
    r = Lmg_SopAndPlain(&Best, a, b);
    if ( r < 0 || Best.fFailed ) return -1;
    for ( Side = 0; Limit && Side < 2; ++Side )
    {
        int Or = Side ? a : b, Guard = Side ? b : a, Id = Or >> 1, x, y, Root;
        if ( !(Or&1) || Id <= p->nVars || p->nNodes > LMG_NODES-24 ||
             p->Times[Guard>>1] >= p->Times[Id] ) continue;
        Lmg_Copy(&Trial, p);
        x = Lmg_GuardAnd(&Trial, Guard, p->Fans[Id-p->nVars-1][0]^1, Limit-1);
        y = Lmg_GuardAnd(&Trial, Guard, p->Fans[Id-p->nVars-1][1]^1, Limit-1);
        Root = Lmg_SopAndPlain(&Trial, x^1, y^1);
        if ( Root < 0 || Trial.fFailed ) continue;
        Root ^= 1;
        if ( Trial.Times[Root>>1] < Best.Times[r>>1] ||
             (Trial.Times[Root>>1] == Best.Times[r>>1] && Lmg_TrialArea(&Trial, Root) < Lmg_TrialArea(&Best, r)) )
        { Lmg_Copy(&Best, &Trial); r = Root; }
    }
    Lmg_Copy(p, &Best);
    return r;
}
static int Lmg_SopAnd( Lmg_Graph_t * p, int a, int b )
{
    return Lmg_GuardAnd(p, a, b, 2);
}
static int Lmg_SopOr( Lmg_Graph_t * p, int a, int b )
{
    int r;
    if ( a < 0 || b < 0 ) return -1;
    r = Lmg_SopAnd(p, a^1, b^1);
    return r < 0 ? -1 : r^1;
}
static int Lmg_SopFlat( Lmg_Graph_t * p, unsigned * pCubes, int nCubes )
{
    int Terms[64], Lits[6], i, k, n, r;
    if ( !nCubes ) return 0;
    for ( i = 0; i < nCubes; ++i )
    {
        if ( !pCubes[i] ) return 1;
        for ( n = k = 0; k < 2*p->nVars; ++k )
            if ( (pCubes[i] >> k) & 1 ) Lits[n++] = 2*(k/2+1) ^ !(k&1);
        if ( p->nNodes+n >= LMG_NODES ) return -1;
        Terms[i] = Lmg_Balance(p, Lits, n, 0)^1;
    }
    if ( p->nNodes+nCubes >= LMG_NODES ) return -1;
    r = Lmg_Balance(p, Terms, nCubes, 0);
    return r^1;
}
// Optimize small quotients as whole functions, rather than committing to the
// literal-factor tree. Their supports may overlap the remainder's support.
static int Lmg_SopKernel( Lmg_Graph_t * p, unsigned * pCubes, int nCubes )
{
    unsigned Support = 0, Truth = 0;
    int Vars[6], Lits[6];
    int n = 0, i, j, a;
    for ( i = 0; i < nCubes; ++i ) Support |= pCubes[i];
    for ( i = 0; i < p->nVars; ++i )
        if ( (Support >> (2*i)) & 3 ) { Vars[n] = i; Lits[n++] = 2*(i+1); }
    if ( n > 4 || !n || p->nNodes > LMG_NODES-32 ) return -1;
    for ( a = 0; a < 16; ++a )
    for ( i = 0; i < nCubes; ++i )
    {
        for ( j = 0; j < n; ++j )
        {
            int Code = (pCubes[i] >> (2*Vars[j])) & 3;
            if ( Code && Code != (((a >> j)&1) ? 2 : 1) ) break;
        }
        if ( j == n ) { Truth |= 1u << a; break; }
    }
    if ( n < 4 ) return Lmg_Small(p, Truth, n, Lits);
    return Lmg_KernelBuild(p, Truth, Lits);
}
// Algebraic literal factoring permits overlap between quotient and remainder.
// All trials use the same truth-derived cover, not recorded function templates.
static int Lmg_SopFactor( Lmg_Graph_t * p, unsigned * pCubes, int nCubes,
    int Mode, int Force )
{
    unsigned Quotient[64], Remainder[64];
    int Counts[12] = {0}, i, k, Lit = -1, nq = 0, nr = 0, a, b;
    if ( nCubes < 2 ) return Lmg_SopFlat(p, pCubes, nCubes);
    if ( Force < 0 && p->nVars > 4 )
    {
        a = Lmg_SopKernel(p, pCubes, nCubes);
        if ( a >= 0 ) return a;
    }
    for ( i = 0; i < nCubes; ++i )
    {
        if ( !pCubes[i] ) return 1;
        for ( k = 0; k < 2*p->nVars; ++k ) Counts[k] += (pCubes[i] >> k) & 1;
    }
    if ( Force >= 0 ) Lit = Counts[Force] >= 2 ? Force : -1;
    else for ( k = 0; k < 2*p->nVars; ++k )
    {
        int t = p->Times[k/2+1], BestT = Lit < 0 ? 0 : p->Times[Lit/2+1];
        if ( Counts[k] < 2 ) continue;
        if ( Lit < 0 ||
             (Mode == 0 && Counts[k] > Counts[Lit]) ||
             (Mode == 1 && (t > BestT || (t == BestT && Counts[k] > Counts[Lit]))) ||
             (Mode == 2 && (t < BestT || (t == BestT && Counts[k] > Counts[Lit]))) ) Lit = k;
    }
    if ( Lit < 0 ) return Lmg_SopFlat(p, pCubes, nCubes);
    for ( i = 0; i < nCubes; ++i )
        if ( (pCubes[i] >> Lit) & 1 ) Quotient[nq++] = pCubes[i] ^ (1u << Lit);
        else Remainder[nr++] = pCubes[i];
    a = Lmg_SopFactor(p, Quotient, nq, Mode, -1);
    a = Lmg_SopAnd(p, 2*(Lit/2+1) ^ !(Lit&1), a);
    b = Lmg_SopFactor(p, Remainder, nr, Mode, -1);
    return Lmg_SopOr(p, a, b);
}
// A cover split need not be driven by a common literal. Factoring arbitrary
// halves exposes overlapping-support decompositions, including fused parity
// and majority. Both sides are tried in the same graph to retain sharing.
static void Lmg_SopGroups( Lmg_Func_t * f, int * pTimes, Vec_Int_t * vCover,
    int Phase )
{
    int Buffer[2*LMG_NODES+1], Depths[6], n = Vec_IntSize(vCover), i, Mode;
    unsigned Mask;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    if ( n < 3 || n > 8 ) return;
    for ( Mask = 1; Mask < (1u << n); Mask += 2 )
    {
        unsigned A[8], B[8];
        int na = 0, nb = 0;
        int Count = Abc_TtBitCount16(Mask);
        if ( Count == n || (n > 5 && (Count < n/2-1 || Count > (n+1)/2+1)) ) continue;
        for ( i = 0; i < n; ++i )
            if ( (Mask >> i) & 1 ) A[na++] = Vec_IntEntry(vCover, i);
            else B[nb++] = Vec_IntEntry(vCover, i);
        for ( Mode = 0; Mode < 2; ++Mode )
        {
            Lmg_Graph_t G;
            int a, b;
            Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, NULL);
            a = Lmg_SopFactor(&G, A, na, Mode, -1);
            b = Lmg_SopFactor(&G, B, nb, Mode, -1);
            G.Root = Lmg_SopOr(&G, a, b);
            if ( G.Root < 0 ) continue;
            G.Root ^= Phase;
            if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
            Lmg_ProfileAdd(f, &V, Depths);
        }
    }
}
// The irredundant cover is not the only useful cover. Consensus primes can
// enable shallower factorizations even though they add redundant cubes.
static Vec_Int_t * Lmg_SopPrimes( word Truth, int nVars )
{
    Vec_Int_t * v = Vec_IntAlloc(32);
    int Limit = 1, Index, i;
    for ( i = 0; i < nVars; ++i ) Limit *= 3;
    for ( Index = 0; Index < Limit; ++Index )
    {
        word Mask = ~(word)0;
        unsigned Cube = 0;
        int x = Index;
        for ( i = 0; i < nVars; ++i, x /= 3 )
            if ( x%3 )
            {
                Cube |= (unsigned)(x%3) << (2*i);
                Mask &= x%3 == 1 ? ~s_Truths6[i] : s_Truths6[i];
            }
        if ( Mask & ~Truth ) continue;
        for ( i = 0; i < nVars; ++i )
            if ( (Cube >> (2*i)) & 3 )
                if ( !((Abc_Tt6Cofactor0(Mask, i) | Abc_Tt6Cofactor1(Mask, i)) & ~Truth) ) break;
        if ( i == nVars ) Vec_IntPush(v, Cube);
    }
    return v;
}
static void Lmg_SopProfiles( Lmg_Func_t * f, int * pTimes )
{
    int Buffer[2*LMG_NODES+1], Depths[6], Phase, Cover, Mode, Force, i, Rotate;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    for ( Cover = 0; Cover < 4; ++Cover )
    {
        Vec_Int_t * vCover = f->pCovers[Cover];
        Phase = Cover&1;
        if ( !vCover || Vec_IntSize(vCover) > 64 ) continue;
        for ( Mode = -1; Mode < 3; ++Mode )
        for ( Force = -1; Force < (Mode == 0 ? 2*f->nVars : 0); ++Force )
        for ( Rotate = 0; Rotate < (Mode < 0 && Vec_IntSize(vCover) <= 8 ? Abc_MaxInt(1, Vec_IntSize(vCover)) : 1); ++Rotate )
        {
            Lmg_Graph_t G;
            unsigned Cubes[64];
            Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, NULL);
            for ( i = 0; i < Vec_IntSize(vCover); ++i )
                Cubes[i] = (unsigned)Vec_IntEntry(vCover, (i+Rotate)%Vec_IntSize(vCover));
            G.Root = Mode < 0 ? Lmg_SopFlat(&G, Cubes, Vec_IntSize(vCover)) :
                Lmg_SopFactor(&G, Cubes, Vec_IntSize(vCover), Mode, Force);
            if ( G.Root < 0 ) continue;
            G.Root ^= Phase;
            if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
            Lmg_ProfileAdd(f, &V, Depths);
        }
        Lmg_SopGroups(f, pTimes, vCover, Phase);
    }
}
// One- and two-selector Shannon decompositions with independently optimized
// residuals. Decode the selectors once and balance the final SOP/POS tree;
// this permits late data paths shorter than cascaded binary MUXes.
static void Lmg_ShannonProfiles( Lmg_Func_t * f, int * pTimes )
{
    int Buffer[2*LMG_NODES+1], Depths[6], s0, s1, Phase, i;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    if ( f->nVars < 5 ) return;
    for ( s0 = 0; s0 < f->nVars; ++s0 )
    for ( s1 = f->nVars == 5 ? -1 : s0+1; s1 < f->nVars; ++s1 )
    {
        int Vars[4], n = 0, k, Mode;
        if ( s1 >= 0 && s1 <= s0 ) continue;
        for ( i = 0; i < f->nVars; ++i ) if ( i != s0 && i != s1 ) Vars[n++] = i;
        for ( Phase = 0; Phase < 2; ++Phase )
        for ( Mode = 0; Mode < 2; ++Mode )
        {
            Lmg_Graph_t G;
            int Terms[4], nTerms = s1 < 0 ? 2 : 4;
            Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, NULL);
            for ( k = 0; k < nTerms; ++k )
            {
                unsigned t = 0;
                int a, j, Lits[4] = {0}, Guard = 2*(s0+1) ^ !(k&1), Data;
                if ( s1 >= 0 ) Guard = Lmg_And(&G, Guard, 2*(s1+1) ^ !((k>>1)&1));
                for ( a = 0; a < 16; ++a )
                {
                    int Index = ((k&1) << s0) | (s1 < 0 ? 0 : ((k>>1)&1) << s1);
                    for ( j = 0; j < n; ++j ) Index |= ((a>>j)&1) << Vars[j];
                    t |= (unsigned)(((f->Truth >> Index)&1)^Phase) << a;
                }
                for ( j = 0; j < n; ++j ) Lits[j] = 2*(Vars[j]+1);
                Data = n == 4 ? Lmg_KernelBuild(&G, t, Lits) : Lmg_Small(&G, t, n, Lits);
                if ( Data < 0 ) break;
                Terms[k] = Mode ? Lmg_SopAnd(&G, Guard, Data) :
                    G.nNodes >= LMG_NODES-1 ? -1 : Lmg_And(&G, Guard, Data);
                if ( Terms[k] < 0 ) break;
                Terms[k] ^= 1;
            }
            if ( k != nTerms || G.nNodes+nTerms >= LMG_NODES ) continue;
            G.Root = Lmg_Balance(&G, Terms, nTerms, 0)^1^Phase;
            if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
            Lmg_ProfileAdd(f, &V, Depths);
        }
    }
}

// Exact two-factor checks use projections of the truth table. The factors
// may overlap in their support: this includes guarded residuals and parity
// compositions that are not disjoint-support decompositions.
static int Lmg_FactorBuild( Lmg_Graph_t * p, word Truth )
{
    unsigned t = 0;
    int Vars[6], Lits[6], n = 0, i, a;
    if ( !Truth || Truth == ~(word)0 ) return Truth != 0;
    for ( i = 0; i < p->nVars; ++i )
        if ( Abc_TtHasVar(&Truth, p->nVars, i) ) Vars[n++] = i;
    if ( n > 5 || (n == 5 && p->nVars != 6) ) return -1;
    for ( i = 0; i < n; ++i ) Lits[i] = 2*(Vars[i]+1);
    for ( a = 0; a < (1 << n); ++a )
    {
        int Index = 0;
        for ( i = 0; i < n; ++i ) Index |= ((a >> i)&1) << Vars[i];
        t |= (unsigned)((Truth >> Index)&1) << a;
    }
    if ( n == 5 ) return Lmg_Residual5(p, (word)t*ABC_CONST(0x100000001), Lits);
    return n == 4 ? Lmg_KernelBuild(p, t, Lits) : Lmg_Small(p, t, n, Lits);
}
// A locally dominated SOP/POS may expose factors that combine with the
// selector. Do not discard it before composing the complete guarded cone.
static int Lmg_CofactorCover( Lmg_Func_t * f, Lmg_Graph_t * p, int Var, int Side, int Phase, int Factor )
{
    Vec_Int_t ** ppCover = &f->pCofCovers[Var][2*Side+Phase];
    int Root;
    if ( !*ppCover )
    {
        Vec_Int_t * vWork;
        word t = Side ? Abc_Tt6Cofactor1(f->Truth, Var) : Abc_Tt6Cofactor0(f->Truth, Var);
        unsigned Truth[2];
        if ( Phase ) t = ~t;
        Truth[0] = (unsigned)t; Truth[1] = (unsigned)(t >> 32);
        // ISOP grows its workspace to one million integers. Retain only the
        // handful of output cubes, not a 4 MiB workspace per cached cofactor.
        vWork = Vec_IntAlloc(0);
        if ( Kit_TruthIsop(Truth, f->nVars, vWork, 0) < 0 )
        { Vec_IntFree(vWork); return -1; }
        *ppCover = Vec_IntAlloc(Vec_IntSize(vWork));
        if ( Vec_IntSize(vWork) ) Vec_IntAppend(*ppCover, vWork);
        Vec_IntFree(vWork);
    }
    if ( Vec_IntSize(*ppCover) > 64 ) return -1;
    Root = Factor < 0 ? Lmg_SopFlat(p, (unsigned *)Vec_IntArray(*ppCover), Vec_IntSize(*ppCover)) :
        Lmg_SopFactor(p, (unsigned *)Vec_IntArray(*ppCover), Vec_IntSize(*ppCover), Factor, -1);
    return Root < 0 ? -1 : Root ^ Phase;
}
// A six-input function may have much smaller single-variable cofactors.
// Compact their actual support rather than refusing the five nominal pins.
static void Lmg_CofactorProfiles( Lmg_Func_t * f, int * pTimes )
{
    int Buffer[2*LMG_NODES+1], Depths[6], v, Mode, Phase;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    if ( f->nVars < 5 ) return;
    for ( v = 0; v < f->nVars; ++v )
    for ( Phase = 0; Phase < 2; ++Phase )
    for ( Mode = 0; Mode < 18; ++Mode )
    {
        Lmg_Graph_t G;
        int a, b, c = 2*(v+1);
        Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, f);
        a = Mode < 2 ? Lmg_FactorBuild(&G, Phase ? ~Abc_Tt6Cofactor0(f->Truth, v) : Abc_Tt6Cofactor0(f->Truth, v)) :
            Lmg_CofactorCover(f, &G, v, 0, ((Mode-2)&1)^Phase, (Mode-2)/4-1);
        b = Mode < 2 ? Lmg_FactorBuild(&G, Phase ? ~Abc_Tt6Cofactor1(f->Truth, v) : Abc_Tt6Cofactor1(f->Truth, v)) :
            Lmg_CofactorCover(f, &G, v, 1, (((Mode-2)>>1)&1)^Phase, (Mode-2)/4-1);
        if ( Mode >= 2 && Phase ) { if ( a >= 0 ) a ^= 1; if ( b >= 0 ) b ^= 1; }
        if ( a < 0 || b < 0 || G.nNodes+3 >= LMG_NODES ) continue;
        if ( Mode )
        {
            a = Lmg_SopAnd(&G, c^1, a); b = Lmg_SopAnd(&G, c, b);
            G.Root = Lmg_SopOr(&G, a, b);
        }
        else G.Root = Lmg_Mux(&G, c, b, a);
        G.Root ^= Phase;
        if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
        Lmg_ProfileAdd(f, &V, Depths);
    }
}
static void Lmg_BidecProfiles( Lmg_Func_t * f, int * pTimes )
{
    int Buffer[2*LMG_NODES+1], Depths[6], i, Phase, Kind;
    unsigned X, Y, Limit = 1u << f->nVars;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    if ( f->nVars < 5 ) return;
    for ( X = 1; X < Limit; ++X )
    {
        if ( f->nVars-Abc_TtBitCount16(X) > 4 ) continue;
        for ( Y = X+1; Y < Limit; ++Y )
        {
            if ( (X&Y) || f->nVars-Abc_TtBitCount16(Y) > 4 ) continue;
            for ( Kind = 0; Kind < 2; ++Kind )
            for ( Phase = 0; Phase < (Kind ? 1 : 2); ++Phase )
            {
                word t = Phase ? ~f->Truth : f->Truth, a = t, b = t, c;
                Lmg_Graph_t G;
                int u, v;
                for ( i = 0; i < f->nVars; ++i )
                {
                    if ( X >> i & 1 ) a = Kind ? Abc_Tt6Cofactor0(a, i) :
                        Abc_Tt6Cofactor0(a, i) | Abc_Tt6Cofactor1(a, i);
                    if ( Y >> i & 1 ) b = Kind ? Abc_Tt6Cofactor0(b, i) :
                        Abc_Tt6Cofactor0(b, i) | Abc_Tt6Cofactor1(b, i);
                }
                if ( Kind )
                {
                    c = a;
                    for ( i = 0; i < f->nVars; ++i )
                        if ( Y >> i & 1 ) c = Abc_Tt6Cofactor0(c, i);
                    b ^= c;
                    if ( (a^b) != t ) continue;
                }
                else if ( (a&b) != t ) continue;
                Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, NULL);
                u = Lmg_FactorBuild(&G, a); v = Lmg_FactorBuild(&G, b);
                if ( u < 0 || v < 0 || G.nNodes+3 >= LMG_NODES ) continue;
                G.Root = (Kind ? Lmg_Xor(&G, u, v) : Lmg_SopAnd(&G, u, v)) ^ Phase;
                if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
                Lmg_ProfileAdd(f, &V, Depths);
            }
        }
    }
}
// BDC supplies an independent algebraic decomposition, including functions
// outside the read-once DSD domain. Balance its products at current arrivals;
// both output phases are synthesized once and reused across timing probes.
static void Lmg_BdcProfiles( Lmg_Func_t * f, int * pTimes )
{
    int Buffer[2*LMG_NODES+1], Depths[6], Phase, i;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    for ( Phase = 0; Phase < 2; ++Phase )
    {
        Vec_Int_t * v = f->pBidec[Phase];
        Lmg_Graph_t G;
        int Map[LMG_NODES+8], Root;
        if ( !v || Vec_IntSize(v)/2 >= LMG_NODES/2 ) continue;
        Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, NULL);
        Map[0] = 0; Map[1] = 1;
        for ( i = 0; i < f->nVars; ++i )
            Map[i+2] = 2*(i+1);
        for ( i = 0; i < Vec_IntSize(v)/2; ++i )
        {
            int a = Vec_IntEntry(v, 2*i), b = Vec_IntEntry(v, 2*i+1);
            Map[f->nVars+2+i] = Lmg_SopAnd(&G, Map[a>>1]^(a&1), Map[b>>1]^(b&1));
            if ( Map[f->nVars+2+i] < 0 ) break;
        }
        if ( i < Vec_IntSize(v)/2 ) continue;
        Root = Vec_IntEntryLast(v);
        G.Root = (Root < 2 ? Root : Map[Root>>1]^(Root&1)) ^ Phase;
        if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
        Lmg_ProfileAdd(f, &V, Depths);
    }
}
// A guard makes some residual minterms unobservable. Add an off-set cube
// to the residual and exclude the same cube at the guard. This exact identity
// lets a cheaper residual use those don't-cares, without copying library cones.
static void Lmg_CareGuardProfiles( Lmg_Func_t * f, int * pTimes )
{
    int Buffer[2*LMG_NODES+1], Depths[6], v, k, i, Phase;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    if ( f->nVars < 5 ) return;
    for ( Phase = 0; Phase < 2; ++Phase )
    {
    word Truth = Phase ? ~f->Truth : f->Truth;
    Vec_Int_t * vOff = f->pCovers[Phase ? 2 : 3];
    if ( !vOff ) continue;
    for ( v = 0; v < f->nVars; ++v )
    {
        word a = Abc_Tt6Cofactor0(Truth, v), b = Abc_Tt6Cofactor1(Truth, v);
        int Guard = 2*(v+1) ^ (b == 0);
        if ( (a != 0 && b != 0) || a == b ) continue;
        for ( k = 0; k < Vec_IntSize(vOff); ++k )
        {
            unsigned Cube = (unsigned)Vec_IntEntry(vOff, k);
            word Mask = ~(word)0;
            Lmg_Graph_t G;
            int Residual, Product, Filter;
            if ( Cube >> (2*v) & 3 ) continue;
            for ( i = 0; i < f->nVars; ++i )
                if ( Cube >> (2*i) & 3 )
                    Mask &= (Cube >> (2*i) & 3) == 1 ? ~s_Truths6[i] : s_Truths6[i];
            assert(!(Mask & Truth));
            Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, f);
            Residual = Lmg_FactorBuild(&G, a | b | Mask);
            if ( Residual < 0 ) continue;
            Product = Lmg_SopFlat(&G, &Cube, 1);
            if ( Product < 0 ) continue;
            Filter = Lmg_SopAnd(&G, Guard, Product^1);
            G.Root = Lmg_SopAnd(&G, Filter, Residual);
            if ( G.Root >= 0 ) G.Root ^= Phase;
            if ( Lmg_Export(&G, &V, Depths) < 0 ) continue;
            Lmg_ProfileAdd(f, &V, Depths);
        }
    }
    }
}

// Try at most three nonempty threshold masks, plus the unconstrained mask.
// These are timing-guided partitions, not enumeration of all supports.
static void Lmg_AcdProfiles( Lmg_Func_t * f, int * pTimes )
{
    word Truth = f->Truth;
    int nVars = f->nVars;
    int Buffer[2*LMG_NODES+1], Depths[6], Sorted[6], i, j, k, nMasks = 0;
    unsigned Masks[4] = {0};
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    // The ACD API expects essential support (as its mapper callers provide).
    // Wire/constant/redundant-input cuts already have a safe DSD candidate.
    if ( nVars < 4 || Abc_TtSupportSize(&Truth, nVars) != nVars ) return;
    memcpy(Sorted, pTimes, nVars*sizeof(int));
    for ( i = 0; i < nVars; ++i ) for ( j = i+1; j < nVars; ++j )
        if ( Sorted[i] < Sorted[j] ) ABC_SWAP(int, Sorted[i], Sorted[j]);
    for ( i = 0; i < nVars && nMasks < 3; ++i )
    {
        unsigned Mask = 0;
        if ( i && Sorted[i] == Sorted[i-1] ) continue;
        for ( j = 0; j < nVars; ++j ) if ( pTimes[j] >= Sorted[i] ) Mask |= 1u << j;
        if ( Abc_TtBitCount16(Mask) <= 3 ) Masks[nMasks++] = Mask;
    }
    Masks[nMasks++] = 0;
    for ( k = 3; k <= 4; ++k )
    {
        if ( nVars <= k ) continue;
        for ( i = 0; i < nMasks; ++i )
        {
            Lmg_AcdRecord_t * pRec;
            unsigned Profile = Masks[i];
            int d;
            if ( Abc_TtBitCount16(Profile) >= k ) continue;
            // ACD's LUT record depends only on truth, size and late mask.
            // Keep it across numeric arrival profiles, including failed searches.
            // AIG implementation/cost still depends on the full arrival vector.
            for ( pRec = f->pAcd; pRec; pRec = pRec->pNext )
                if ( pRec->Mask == Profile && pRec->LutSize == k ) break;
            if ( !pRec )
            {
                word t = Truth;
                pRec = ABC_CALLOC(Lmg_AcdRecord_t, 1);
                pRec->Mask = Profile; pRec->LutSize = k;
                pRec->pNext = f->pAcd; f->pAcd = pRec;
                if ( acd_decompose(&t, nVars, k, &Profile, pRec->Record) < 0 )
                    pRec->Record[0] = 0;
            }
            if ( !pRec->Record[0] ) continue;
            d = Lmg_AcdBuild(pRec->Record, nVars, pTimes, &V, Depths, f->pKernels);
            if ( d < 0 ) continue;
            Lmg_ProfileAdd(f, &V, Depths);
        }
    }
}
static void Lmg_FuncClear( Lmg_Func_t * f );
static void Lmg_ProfilesClear( Lmg_Func_t * f )
{
    Lmg_Profile_t * p, * pNext;
    for ( p = f->pProfiles; p; p = pNext )
    { pNext = p->pNext; ABC_FREE(p); }
    f->pProfiles = NULL; f->nProfiles = 0;
}
static void Lmg_ResidualsClear( Lmg_Func_t * f )
{
    Lmg_Residual_t * r, * rNext;
    Lmg_Child_t * c, * cNext;
    for ( r = f->pResiduals; r; r = rNext )
    { rNext = r->pNext; ABC_FREE(r); }
    f->pResiduals = NULL;
    for ( c = f->pChildren; c; c = cNext )
    { cNext = c->pNext; Lmg_FuncClear(c->pFunc); ABC_FREE(c->pFunc); ABC_FREE(c); }
    f->pChildren = NULL;
}
static void Lmg_FuncClear( Lmg_Func_t * f )
{
    int i, j;
    Lmg_AcdRecord_t * pRec, * pNext;
    ABC_FREE(f->pDsd);
    ABC_FREE(f->pFusedDsd);
    for ( i = 0; i < 4; ++i ) if ( f->pCovers[i] )
    { Vec_IntFree(f->pCovers[i]); f->pCovers[i] = NULL; }
    for ( i = 0; i < 6; ++i ) for ( j = 0; j < 4; ++j ) if ( f->pCofCovers[i][j] )
    { Vec_IntFree(f->pCofCovers[i][j]); f->pCofCovers[i][j] = NULL; }
    for ( i = 0; i < 2; ++i ) if ( f->pBidec[i] )
    { Vec_IntFree(f->pBidec[i]); f->pBidec[i] = NULL; }
    for ( i = 0; i < 6; ++i ) ABC_FREE(f->pMore[i]);
    for ( pRec = f->pAcd; pRec; pRec = pNext )
    { pNext = pRec->pNext; ABC_FREE(pRec); }
    f->pAcd = NULL;
    Lmg_ProfilesClear(f);
    f->nDropped = f->fReady = 0;
    Lmg_ResidualsClear(f);
}
// One split is deliberately bounded. Do not perform exponential Shannon
// synthesis on each new cut. Cofactors must use the supported primitives.
static void Lmg_FuncInit( Lmg_Func_t * f, word Truth, int nVars )
{
    char Dsd[1024]; word t = Truth;
    int i;
    Lmg_FuncClear(f);
    f->Valid = 1; f->Truth = Truth; f->nVars = nVars;
    f->Prime = Dau_DsdDecompose(&t, nVars, 0, 1, Dsd);
    if ( f->Prime <= 3 ) f->pDsd = Abc_UtilStrsav(Dsd);
    if ( nVars < 3 || Truth == 0 || Truth == ~(word)0 ) return;
    for ( i = 0; i < nVars; ++i )
    {
        char d0[1024], d1[1024], Line[2064];
        word c0 = Abc_Tt6Cofactor0(Truth, i), c1 = Abc_Tt6Cofactor1(Truth, i);
        if ( c0 == 0 || c0 == ~(word)0 || c1 == 0 || c1 == ~(word)0 ) continue;
        if ( Dau_DsdDecompose(&c0, nVars, 0, 1, d0) > 3 ||
             Dau_DsdDecompose(&c1, nVars, 0, 1, d1) > 3 ) continue;
        sprintf(Line, "<%c%s%s>", 'a'+i, d1, d0);
        f->pMore[i] = Abc_UtilStrsav(Line);
    }
}
static int Lmg_FuncSynth( Lmg_Func_t * f, int * pTimes, Vec_Int_t * vAig, int * pDepths )
{
    int Buffer[2*LMG_NODES+1];
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer }, * v = &V;
    int i, d, Depths[6], Max = 0, Best = ABC_INFINITY;
    Vec_IntClear(vAig);
    for ( i = 0; i < f->nVars; ++i ) Max = Abc_MaxInt(Max, pTimes[i]);
    for ( i = -1; i < f->nVars; ++i )
    {
        const char * s = i < 0 ? f->pDsd : f->pMore[i];
        // Nonconstant Shannon branches put every essential input at least
        // two gates from the output. Keep the cheaper primary on a tie.
        if ( i >= 0 && Max + 2 >= Best ) break;
        if ( !s ) continue;
        d = Lmg_Build(f->Truth, f->nVars, pTimes, s, v, Depths, f->pKernels);
        if ( d < 0 ) continue;
        Lmg_ProfileAdd(f, v, Depths);
        if ( d < Best || (d == Best && Vec_IntSize(v) < Vec_IntSize(vAig)) )
        {
            Best = d; Vec_IntClear(vAig); Vec_IntAppend(vAig, v);
            memcpy(pDepths, Depths, f->nVars*sizeof(int));
        }
    }
    return Best == ABC_INFINITY ? -1 : Best;
}
// A conjunction of independent literals (in either output phase) needs n-1
// ANDs. Arrival balancing attains its minimum delay, so decomposition, care
// searches and a sampled frontier cannot improve either ranking key. Keep
// input phases and pin order; this is not truth-table canonicalization.
static int Lmg_IsLiteralProduct( Lmg_Func_t * f )
{
    const char * s = f->pDsd;
    unsigned Seen = 0;
    int n = 0;
    if ( !s ) return 0;
    if ( *s == '!' ) ++s;
    if ( *s++ != '(' ) return 0;
    while ( *s && *s != ')' )
    {
        unsigned Bit;
        if ( *s == '!' ) ++s;
        if ( *s < 'a' || *s >= 'a'+f->nVars ) return 0;
        Bit = 1u << (*s++-'a');
        if ( Seen & Bit ) return 0;
        Seen |= Bit; ++n;
    }
    return n == f->nVars && *s == ')' && !s[1];
}
// Every essential input must reach the root of a binary AND DAG. Unfolding
// it into a tree gives the Kraft bound sum(2^arrival) <= 2^output. Very early
// inputs are omitted, never rounded upward, to keep this a lower bound even
// for arrivals separated by thousands of levels. A variable with neither
// cofactor constant additionally needs at least two gates to the output.
static int Lmg_DelayLower( Lmg_Func_t * f, int * pTimes )
{
    word Sum = 0, Capacity = 1;
    int i, Max = 0, Base, Lower = 0, Level = 0;
    for ( i = 0; i < f->nVars; ++i ) Max = Abc_MaxInt(Max, pTimes[i]);
    Base = Max-32;
    for ( i = 0; i < f->nVars; ++i )
    {
        word a, b;
        if ( !Abc_TtHasVar(&f->Truth, f->nVars, i) ) continue;
        a = Abc_Tt6Cofactor0(f->Truth, i); b = Abc_Tt6Cofactor1(f->Truth, i);
        Lower = Abc_MaxInt(Lower, pTimes[i] +
            (a == 0 || a == ~(word)0 || b == 0 || b == ~(word)0 ? 1 : 2));
        if ( pTimes[i] >= Base ) Sum += (word)1 << (pTimes[i]-Base);
    }
    while ( Capacity < Sum ) { Capacity <<= 1; ++Level; }
    return Abc_MaxInt(Lower, Base+Level);
}
static int Lmg_AtLowerBounds( Lmg_Func_t * f, int * pTimes, int Delay, Vec_Int_t * v )
{
    return !Lms_KernelIsXor(f->pKernels) && f->nVars >= 2 && Delay >= 0 &&
        Abc_TtSupportSize(&f->Truth, f->nVars) == f->nVars &&
        Vec_IntSize(v)/2 == f->nVars-1 && Delay == Lmg_DelayLower(f, pTimes);
}
// Optimize a contextual five-input residual once at construction time. The
// child has fewer variables than its parent, and its builders refuse another
// five-input recursion. This shares the generic rules and four-input kernels,
// rather than treating the residual as an opaque extra gate.
static int Lmg_Residual5( Lmg_Graph_t * p, word Truth, int * pLits )
{
    Lmg_Func_t * f;
    Lmg_Child_t * c;
    int Buffer[2*LMG_NODES+1], Depths[6], Times[6], Key[5], Base = ABC_INFINITY;
    int Map[LMG_NODES+7], i, Root;
    Lmg_Residual_t * r;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    if ( !p->pOwner ) return -1;
    for ( i = 0; i < 5; ++i )
    { Times[i] = p->Times[pLits[i]>>1]; Base = Abc_MinInt(Base, Times[i]); }
    for ( i = 0; i < 5; ++i ) Key[i] = Times[i]-Base;
    for ( r = p->pOwner->pResiduals; r; r = r->pNext )
        if ( r->Truth == Truth && !memcmp(r->Times, Key, sizeof(Key)) ) break;
    if ( r )
    { Vec_IntPushArray(&V, r->Fans, r->Size); goto import_graph; }
    for ( c = p->pOwner->pChildren; c; c = c->pNext ) if ( c->Truth == Truth ) break;
    if ( !c )
    {
        c = ABC_CALLOC(Lmg_Child_t,1); c->Truth = Truth; c->pFunc = ABC_CALLOC(Lmg_Func_t,1);
        c->pNext = p->pOwner->pChildren; p->pOwner->pChildren = c;
        f = c->pFunc; Lmg_FuncInit(f, Truth, 5);
        f->pKernels = p->pKernels;
        if ( !f->pDsd && f->Prime <= 4 )
        {
            char Dsd[1024]; word t = Truth;
            Dau_DsdDecompose(&t, 5, 0, 1, Dsd); f->pFusedDsd = Abc_UtilStrsav(Dsd);
        }
        for ( i = 0; i < 2; ++i )
        {
            word t = i ? ~Truth : Truth;
            unsigned tt[2] = {(unsigned)t,(unsigned)(t>>32)};
            Vec_Int_t * v = Vec_IntAlloc(0);
            if ( Kit_TruthIsop(tt, 5, v, 0) >= 0 )
            {
                f->pCovers[i] = Vec_IntAlloc(Vec_IntSize(v));
                if ( Vec_IntSize(v) ) Vec_IntAppend(f->pCovers[i], v);
            }
            Vec_IntFree(v); f->pCovers[i+2] = Lmg_SopPrimes(t,5);
        }
    }
    f = c->pFunc;
    Lmg_ProfilesClear(f);
    Lmg_FuncSynth(f, Times, &V, Depths);
    if ( Lmg_IsLiteralProduct(f) ) goto cache_graph;
    if ( Lmg_AtLowerBounds(f, Times, Lmg_ProfileSelect(f, Times, &V, Depths), &V) )
        goto cache_graph;
    Lmg_FusedProfiles(f, Times);
    Lmg_SopProfiles(f, Times);
    Lmg_CofactorProfiles(f, Times);
    Lmg_ShannonProfiles(f, Times);
    Lmg_CareGuardProfiles(f, Times);
    if ( Lmg_ProfileSelect(f, Times, &V, Depths) < 0 ) return -1;
cache_graph:
    {
        r = (Lmg_Residual_t *)ABC_ALLOC(char, sizeof(Lmg_Residual_t)+Vec_IntSize(&V)*sizeof(int));
        r->Truth = Truth; r->Size = Vec_IntSize(&V);
        memcpy(r->Times, Key, sizeof(Key)); memcpy(r->Fans, Vec_IntArray(&V), r->Size*sizeof(int));
        r->pNext = p->pOwner->pResiduals; p->pOwner->pResiduals = r;
    }
import_graph:
    if ( p->nNodes+Vec_IntSize(&V)/2 >= LMG_NODES ) return -1;
    Map[0] = 0;
    for ( i = 0; i < 5; ++i ) Map[i+1] = pLits[i];
    for ( i = 0; i < Vec_IntSize(&V)/2; ++i )
    {
        int a = Vec_IntEntry(&V, 2*i), b = Vec_IntEntry(&V, 2*i+1);
        Map[i+6] = Lmg_And(p, Map[a>>1]^(a&1), Map[b>>1]^(b&1));
    }
    Root = Vec_IntEntryLast(&V); Root = Map[Root>>1] ^ (Root&1);
    return Root;
}
static int Lmg_Generate( Lmg_Func_t * f, int * pTimes, Vec_Int_t * v,
    int * pDepths )
{
    int i, d;
    Lmg_ProfilesClear(f);
    d = Lmg_FuncSynth(f, pTimes, v, pDepths);
    if ( Lmg_IsLiteralProduct(f) || Lmg_AtLowerBounds(f, pTimes, d, v) )
        return d;
    if ( f->nVars <= 4 )
    {
        int Buffer[2*LMG_NODES+1], Depths[6];
        Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
        // Complete four-input queries also receive an exact candidate at
        // their sampled arrivals, not only the fixed timing probe basis.
        // Add it locally: residual frontiers remain query-order independent.
        if ( f->nVars == 4 && Lms_KernelSample(f->pKernels, (unsigned)f->Truth,
                pTimes, &V, Depths) >= 0 )
            Lmg_ProfileAdd(f, &V, Depths);
        for ( i = 0; Lms_KernelProfile(f->pKernels, (unsigned)f->Truth, i, &V, Depths) >= 0; ++i )
        {
            Lmg_Graph_t G;
            int Map[LMG_NODES+7], j, Root = Vec_IntEntryLast(&V);
            Lmg_GraphInit(&G, f->nVars, pTimes, f->pKernels, f);
            Map[0] = 0;
            for ( j = 0; j < 4; ++j )
            {
                Map[j+1] = j < f->nVars ? 2*(j+1) : 0;
            }
            for ( j = 0; j < Vec_IntSize(&V)/2; ++j )
            {
                int a = Vec_IntEntry(&V,2*j), b = Vec_IntEntry(&V,2*j+1);
                Map[j+5] = Lmg_And(&G, Map[a>>1]^(a&1), Map[b>>1]^(b&1));
            }
            G.Root = Map[Root>>1]^(Root&1);
            if ( Lmg_Export(&G, &V, Depths) >= 0 ) Lmg_ProfileAdd(f, &V, Depths);
        }
    }
    else
    {
        if ( !f->fReady )
        {
            if ( !f->pDsd && f->Prime <= 4 )
            {
                char Dsd[1024]; word t = f->Truth;
                Dau_DsdDecompose(&t, f->nVars, 0, 1, Dsd); f->pFusedDsd = Abc_UtilStrsav(Dsd);
            }
            for ( i = 0; i < 2; ++i )
            {
                word t = i ? ~f->Truth : f->Truth;
                unsigned Truth[2] = {(unsigned)t,(unsigned)(t>>32)};
                Vec_Int_t * vCover = Vec_IntAlloc(0);
                if ( Kit_TruthIsop(Truth, f->nVars, vCover, 0) >= 0 )
                {
                    f->pCovers[i] = Vec_IntAlloc(Vec_IntSize(vCover));
                    if ( Vec_IntSize(vCover) ) Vec_IntAppend(f->pCovers[i], vCover);
                }
                Vec_IntFree(vCover);
                f->pCovers[i+2] = Lmg_SopPrimes(t, f->nVars);
                f->pBidec[i] = Bdc_ManBidecResub(&t, NULL, f->nVars);
            }
            f->fReady = 1;
        }
        Lmg_FusedProfiles(f, pTimes);
        Lmg_AcdProfiles(f, pTimes);
        Lmg_SopProfiles(f, pTimes);
        Lmg_ShannonProfiles(f, pTimes);
        Lmg_CofactorProfiles(f, pTimes);
        Lmg_BidecProfiles(f, pTimes);
        Lmg_BdcProfiles(f, pTimes);
        Lmg_CareGuardProfiles(f, pTimes);
    }
    return Lmg_ProfileSelect(f, pTimes, v, pDepths);
}

////////////////////////////////////////////////////////////////////////
///                       PUBLIC INTERFACE                           ///
////////////////////////////////////////////////////////////////////////

struct Lms_Gen_t_ {
    Lmg_Func_t Func;
    void * pKernels;
};

/**Function*************************************************************

  Synopsis    [Allocate an AND-cost structure generator.]

  Description [The caller releases it with Lms_GenStop.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
Lms_Gen_t * Lms_GenStart( void )
{
    Lms_Gen_t * p = ABC_CALLOC(Lms_Gen_t, 1);
    p->pKernels = Lms_KernelStart();
    return p;
}
/**Function*************************************************************

  Synopsis    [Allocate a unit AND/XOR-cost structure generator.]

  Description [Graphs still use ordinary AND nodes for serialized XOR patterns.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
Lms_Gen_t * Lms_GenStartXor( void )
{
    Lms_Gen_t * p = ABC_CALLOC(Lms_Gen_t, 1);
    p->pKernels = Lms_KernelStartXor();
    return p;
}
/**Function*************************************************************

  Synopsis    [Free a structure generator.]

  Description [Accepts NULL.]

  SideEffects [Frees cached functions and kernels.]

  SeeAlso     []

***********************************************************************/
void Lms_GenStop( Lms_Gen_t * p )
{
    if ( !p ) return;
    Lmg_FuncClear(&p->Func);
    Lms_KernelStop(p->pKernels);
    ABC_FREE(p);
}
/**Function*************************************************************

  Synopsis    [Return the last query's pool-overflow count.]

  Description [Returns zero for NULL.]

  SideEffects [None.]

  SeeAlso     []

***********************************************************************/
int Lms_GenSkipped( Lms_Gen_t * p )
{
    return p ? p->Func.nDropped : 0;
}
/**Function*************************************************************

  Synopsis    [Generate timing-driven area/pin-depth alternatives.]

  Description [Visits candidates in supplied input order. Returns their count, or -1
  on invalid arguments or a callback failure.]

  SideEffects [Updates the generator and invokes pVisit.]

  SeeAlso     []

***********************************************************************/
int Lms_GenGenerate( Lms_Gen_t * p, word Truth, int nVars,
    const int * pArrivals, Lms_GenVisit_t pVisit, void * pData )
{
    int Buffer[2*LMG_NODES+1], Times[6] = {0}, Depths[6], i, Base = ABC_INFINITY;
    Vec_Int_t V = { 2*LMG_NODES+1, 0, Buffer };
    Lmg_Func_t * f;
    Lmg_Profile_t * q;
    if ( !p || !pArrivals || !pVisit || nVars < 2 || nVars > 6 ||
         Abc_TtSupport(&Truth, 6) != (1 << nVars)-1 ) return -1;
    for ( i = 0; i < nVars; ++i )
    {
        if ( pArrivals[i] < 0 || pArrivals[i] > 1000000 ) return -1;
        Base = Abc_MinInt(Base, pArrivals[i]);
    }
    for ( i = 0; i < nVars; ++i ) Times[i] = pArrivals[i]-Base;
    f = &p->Func;
    if ( !f->Valid || f->Truth != Truth || f->nVars != nVars )
    {
        Lmg_FuncInit(f, Truth, nVars);
        f->pKernels = p->pKernels;
    }
    f->nDropped = 0;
    Lmg_Generate(f, Times, &V, Depths);
    for ( i = 0, q = f->pProfiles; q; q = q->pNext, ++i )
        if ( !pVisit(pData, nVars, q->Fans, q->nAnds, q->Root, q->Depths) )
            return -1;
    return i;
}

ABC_NAMESPACE_IMPL_END
