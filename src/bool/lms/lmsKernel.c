/**CFile****************************************************************

  FileName    [lmsKernel.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Generate and cache small-function timing alternatives.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2026.]

  Revision    [$Id: lmsKernel.c,v 1.00 2026/10/04 00:00:00 alanmi Exp $]

***********************************************************************/
#include "lmsInt.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define LMK_FUNCS 32768
#define LMK_TABLES 128
typedef struct Lmk_Profile_t_ {
    struct Lmk_Profile_t_ * pNext;
    int Area, nAnds, Root, Depths[4], Fans[1];
} Lmk_Profile_t;
typedef struct Lmk_Table_t_ {
    int Times[4], nFuncs, Mask, fXor;
    int * Delay, * Fan0, * Fan1, * Phase;
    int * Heap, nHeap, * Done, nDone, * Map;
    unsigned * Marks, Epoch;
    word Age;
} Lmk_Table_t;
typedef struct Lmk_Man_t_ {
    Lmk_Table_t * pTables[LMK_TABLES];
    Lmk_Table_t * pSmallTables[LMK_TABLES];
    Lmk_Table_t * pSampleTables[2];
    Lmk_Profile_t * pProfiles[LMK_FUNCS];
    word Queries;
    int fXor;
} Lmk_Man_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Complemented edges make the phase at minterm zero immaterial. Input order
// is never changed: this is not NPN classification or input canonicalization.
static int Lmk_Less( Lmk_Table_t * p, int a, int b )
{
    return p->Delay[a] < p->Delay[b] || (p->Delay[a] == p->Delay[b] && a < b);
}
static void Lmk_Push( Lmk_Table_t * p, int Id )
{
    int i = p->nHeap++, k;
    while ( i && Lmk_Less(p, Id, p->Heap[k=(i-1)/2]) )
    { p->Heap[i] = p->Heap[k]; i = k; }
    p->Heap[i] = Id;
}
static int Lmk_Pop( Lmk_Table_t * p )
{
    int Root = p->Heap[0], Last = p->Heap[--p->nHeap], i = 0, k;
    while ( (k=2*i+1) < p->nHeap )
    {
        if ( k+1 < p->nHeap && Lmk_Less(p, p->Heap[k+1], p->Heap[k]) ) ++k;
        if ( !Lmk_Less(p, p->Heap[k], Last) ) break;
        p->Heap[i] = p->Heap[k]; i = k;
    }
    if ( p->nHeap ) p->Heap[i] = Last;
    return Root;
}
static void Lmk_Init( Lmk_Table_t * p, int * pTimes, int nVars )
{
    unsigned Truths[4] = { 0xAAAA, 0xCCCC, 0xF0F0, 0xFF00 };
    int i, Id;
    if ( !p->Delay )
    {
        p->nFuncs = nVars == 3 ? 128 : LMK_FUNCS;
        p->Mask = nVars == 3 ? 255 : 65535;
        p->Delay = ABC_ALLOC(int, 7*p->nFuncs);
        p->Fan0 = p->Delay+p->nFuncs; p->Fan1 = p->Fan0+p->nFuncs;
        p->Phase = p->Fan1+p->nFuncs; p->Heap = p->Phase+p->nFuncs;
        p->Done = p->Heap+p->nFuncs; p->Map = p->Done+p->nFuncs;
        p->Marks = ABC_CALLOC(unsigned, p->nFuncs);
    }
    p->nHeap = p->nDone = 0; p->Epoch = 0;
    memset(p->Marks, 0, p->nFuncs*sizeof(unsigned));
    memcpy(p->Times, pTimes, sizeof(p->Times));
    for ( i = 0; i < p->nFuncs; ++i ) p->Delay[i] = -1;
    p->Delay[0] = 0; p->Fan0[0] = -1;
    for ( i = 0; i < nVars; ++i )
    {
        Id = (Truths[i] & p->Mask) >> 1;
        p->Delay[Id] = pTimes[i]; p->Fan0[Id] = -2-i;
        Lmk_Push(p, Id);
    }
}
// Every pair is evaluated once, when its later-arriving function is settled.
// Thus the first discovery of a truth has minimum possible output arrival.
// Retain the first implementation of a truth, so subsequent queries cannot
// change an earlier result. Reconstruction shares identical subfunctions.
// Area-oriented alternatives are provided by the surrounding frontier.
static void Lmk_Advance( Lmk_Table_t * p, int Target )
{
    while ( p->nHeap && p->Delay[Target] < 0 )
    {
        int a = Lmk_Pop(p), i, pa, pb, Delay = p->Delay[a]+1;
        unsigned ta = (unsigned)a << 1;
        for ( i = 0; i < p->nDone; ++i )
        {
            int b = p->Done[i];
            unsigned tb = (unsigned)b << 1;
            if ( p->fXor )
            {
                int Id = (ta ^ tb) >> 1;
                if ( Id && p->Delay[Id] < 0 )
                {
                    p->Delay[Id] = Delay; Lmk_Push(p, Id);
                    p->Fan0[Id] = 2*a; p->Fan1[Id] = 2*b;
                    p->Phase[Id] = 2; // XOR opcode, with no output phase.
                }
            }
            for ( pa = 0; pa < 2; ++pa )
            for ( pb = 0; pb < 2; ++pb )
            {
                unsigned t = (ta ^ (pa ? (unsigned)p->Mask : 0)) & (tb ^ (pb ? (unsigned)p->Mask : 0));
                int Phase = t&1, Id = (t ^ (Phase ? (unsigned)p->Mask : 0)) >> 1;
                if ( !Id || p->Delay[Id] >= 0 ) continue;
                p->Delay[Id] = Delay; Lmk_Push(p, Id);
                // A seeded variable cannot arrive earlier through another
                // function of independent inputs. All other first delays are
                // minimal because the queue is processed in arrival order.
                assert(p->Delay[Id] == Delay);
                p->Fan0[Id] = 2*a+pa;
                p->Fan1[Id] = 2*b+pb; p->Phase[Id] = Phase;
            }
        }
        p->Done[p->nDone++] = a;
    }
}
static int Lmk_Build( Lmk_Table_t * p, int Id, Vec_Int_t * v )
{
    int a, b, r;
    if ( p->Marks[Id] == p->Epoch ) return p->Map[Id];
    if ( p->Fan0[Id] < 0 )
    {
        p->Marks[Id] = p->Epoch;
        return p->Map[Id] = p->Fan0[Id] == -1 ? 0 : 2*(-p->Fan0[Id]-1);
    }
    a = Lmk_Build(p, p->Fan0[Id] >> 1, v);
    b = Lmk_Build(p, p->Fan1[Id] >> 1, v);
    if ( a < 0 || b < 0 || Vec_IntSize(v)+(p->Phase[Id]&2 ? 6 : 2) > 254 ) return -1;
    a ^= p->Fan0[Id]&1; b ^= p->Fan1[Id]&1;
    r = 2*(5+Vec_IntSize(v)/2);
    if ( p->Phase[Id]&2 )
    {
        Vec_IntPushTwo(v, a, b^1);
        Vec_IntPushTwo(v, a^1, b);
        Vec_IntPushTwo(v, r^1, (r+2)^1);
        r = (r+4)^1;
    }
    else Vec_IntPushTwo(v, a, b);
    p->Marks[Id] = p->Epoch;
    return p->Map[Id] = r ^ (p->Phase[Id]&1);
}
/**Function*************************************************************

  Synopsis    [Allocate an AND-cost small-function kernel manager.]

  Description [The caller releases it with Lms_KernelStop.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
void * Lms_KernelStart( void )
{
    return ABC_CALLOC(Lmk_Man_t, 1);
}
/**Function*************************************************************

  Synopsis    [Allocate a unit AND/XOR-cost kernel manager.]

  Description [Returned graphs serialize XORs as three ANDs.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
void * Lms_KernelStartXor( void )
{
    Lmk_Man_t * p = (Lmk_Man_t *)Lms_KernelStart();
    p->fXor = 1;
    return p;
}
/**Function*************************************************************

  Synopsis    [Return whether a kernel manager uses unit XOR costs.]

  Description [Returns zero for NULL.]

  SideEffects [None.]

  SeeAlso     []

***********************************************************************/
int Lms_KernelIsXor( void * pData )
{
    return pData && ((Lmk_Man_t *)pData)->fXor;
}
static int Lmk_Synth( void * pData, unsigned Truth, int * pTimes,
    Vec_Int_t * vAig, int * pDepths, int fSample )
{
    Lmk_Man_t * m = (Lmk_Man_t *)pData;
    Lmk_Table_t * p = NULL;
    Lmk_Table_t ** ppTables;
    int Pins[132][4], Levels[132] = {0}, Times[4];
    int Base = pTimes[0], Slot = 0, i, j, Id, Root, Delay, nVars;
    int nTables = fSample ? 1 : LMK_TABLES;
    if ( !m ) return -1;
    // Three-input residuals need only 128 complement-normalized functions.
    // Do not seed an irrelevant fourth variable and enumerate its cofactors.
    // A separate table cache prevents small kernels from evicting costly
    // four-input searches. Both frontiers retain the same external pin order.
    nVars = (Truth&255u) == ((Truth>>8)&255u) ? 3 : 4;
    ppTables = nVars == 3 ? m->pSmallTables : m->pTables;
    if ( fSample ) ppTables = m->pSampleTables + (nVars == 4);
    for ( i = 1; i < nVars; ++i ) Base = Abc_MinInt(Base, pTimes[i]);
    for ( i = 0; i < 4; ++i ) Times[i] = i < nVars ? pTimes[i]-Base : 0;
    ++m->Queries;
    for ( i = 0; i < nTables; ++i )
    {
        if ( !ppTables[i] ) { Slot = i; break; }
        if ( !memcmp(ppTables[i]->Times, Times, sizeof(Times)) ) { p = ppTables[i]; break; }
        if ( ppTables[i]->Age < ppTables[Slot]->Age ) Slot = i;
    }
    if ( !p )
    {
        p = ppTables[Slot];
        if ( !p ) p = ppTables[Slot] = ABC_CALLOC(Lmk_Table_t, 1);
        p->fXor = m->fXor;
        Lmk_Init(p, Times, nVars);
    }
    p->Age = m->Queries;
    Truth &= p->Mask;
    Id = (Truth ^ ((Truth&1) ? (unsigned)p->Mask : 0)) >> 1;
    Lmk_Advance(p, Id);
    if ( p->Delay[Id] < 0 ) return -1;
    if ( !++p->Epoch ) { memset(p->Marks, 0, p->nFuncs*sizeof(unsigned)); ++p->Epoch; }
    Vec_IntClear(vAig);
    Root = Lmk_Build(p, Id, vAig);
    if ( Root < 0 ) return -1;
    Root ^= Truth&1;
    memset(Pins, -1, sizeof(Pins));
    for ( i = 0; i < 4; ++i ) { Levels[i+1] = pTimes[i]; Pins[i+1][i] = 0; }
    for ( i = 0; i < Vec_IntSize(vAig)/2; ++i )
    {
        int a = Vec_IntEntry(vAig, 2*i) >> 1, b = Vec_IntEntry(vAig, 2*i+1) >> 1;
        if ( m->fXor ) Lms_AigXorInputs(4, Vec_IntArray(vAig), i+5, &a, &b);
        Levels[i+5] = 1+Abc_MaxInt(Levels[a], Levels[b]);
        for ( j = 0; j < 4; ++j )
        { int d = Abc_MaxInt(Pins[a][j], Pins[b][j]); Pins[i+5][j] = d < 0 ? -1 : d+1; }
    }
    for ( i = 0; i < 4; ++i ) pDepths[i] = Pins[Root>>1][i];
    Delay = Root < 2 ? 0 : Levels[Root>>1];
    assert(Root < 2 || Delay == Base+p->Delay[Id]);
    Vec_IntPush(vAig, Root);
    return Delay;
}
/**Function*************************************************************

  Synopsis    [Synthesize a small function at the supplied arrivals.]

  Description [Returns output arrival, or -1 on failure. vAig holds fanin pairs
  followed by the root literal.]

  SideEffects [Updates timing tables and writes vAig and pDepths.]

  SeeAlso     []

***********************************************************************/
int Lms_KernelSynth( void * pData, unsigned Truth, int * pTimes,
    Vec_Int_t * vAig, int * pDepths )
{
    return Lmk_Synth(pData, Truth, pTimes, vAig, pDepths, 0);
}
// Sampled arrivals have their own bounded scratch storage. They neither
// evict fixed-probe tables nor change the history-independent frontiers.
/**Function*************************************************************

  Synopsis    [Synthesize a sampled query in separate scratch storage.]

  Description [Uses bounded tables without evicting the fixed-probe tables.]

  SideEffects [Updates scratch tables and writes vAig and pDepths.]

  SeeAlso     []

***********************************************************************/
int Lms_KernelSample( void * pData, unsigned Truth, int * pTimes,
    Vec_Int_t * vAig, int * pDepths )
{
    return Lmk_Synth(pData, Truth, pTimes, vAig, pDepths, 1);
}
static int Lmk_Dominates( int Area, int * pDepths, Lmk_Profile_t * p )
{
    int i;
    if ( Area > p->Area ) return 0;
    for ( i = 0; i < 4; ++i ) if ( pDepths[i] > p->Depths[i] ) return 0;
    return 1;
}
static void Lmk_ProfileAdd( Lmk_Man_t * m, int Id, Vec_Int_t * v, int * pDepths )
{
    Lmk_Profile_t * p, ** pp;
    int i, nAnds = Vec_IntSize(v)/2;
    int Area = m->fXor ? Lms_AigXorMetrics(4, Vec_IntArray(v), nAnds, Vec_IntEntryLast(v), NULL) : nAnds;
    for ( p = m->pProfiles[Id]; p; p = p->pNext )
    {
        if ( p->Area > Area ) continue;
        for ( i = 0; i < 4; ++i ) if ( p->Depths[i] > pDepths[i] ) break;
        if ( i == 4 ) return;
    }
    for ( pp = m->pProfiles+Id; *pp; )
        if ( Lmk_Dominates(Area, pDepths, *pp) )
        { p = *pp; *pp = p->pNext; ABC_FREE(p); }
        else pp = &(*pp)->pNext;
    p = (Lmk_Profile_t *)ABC_ALLOC(char, sizeof(Lmk_Profile_t)+2*nAnds*sizeof(int));
    p->Area = Area; p->nAnds = nAnds; p->Root = Vec_IntEntryLast(v);
    memcpy(p->Depths, pDepths, sizeof(p->Depths));
    if ( nAnds ) memcpy(p->Fans, Vec_IntArray(v), 2*nAnds*sizeof(int));
    p->pNext = m->pProfiles[Id]; m->pProfiles[Id] = p;
}
// These pools are independent of query history and arrival magnitudes. All
// construction calls use the same finite timing basis, so the table cache
// never churns on intermediate arrival vectors from decomposition records.
/**Function*************************************************************

  Synopsis    [Select a timing winner from a fixed-probe frontier.]

  Description [The frontier is independent of query order.]

  SideEffects [Builds missing profiles and writes vAig and pDepths.]

  SeeAlso     []

***********************************************************************/
int Lms_KernelFrontier( void * pData, unsigned Truth, int * pTimes,
    Vec_Int_t * vAig, int * pDepths )
{
    Lmk_Man_t * m = (Lmk_Man_t *)pData;
    Lmk_Profile_t * p, * pBest = NULL;
    unsigned Phase = Truth&1, t = (Truth&65535u) ^ (Phase ? 65535u : 0);
    int Id = t >> 1, i, Best = ABC_INFINITY;
    if ( !m ) return -1;
    if ( !m->pProfiles[Id] )
    {
        int Times[4], Depths[4], Gap, a, b, c, d;
        unsigned Mask;
        Vec_Int_t * v = Vec_IntAlloc(256);
        for ( Gap = 0; Gap < 4; ++Gap )
        for ( Mask = 0; Mask < 16; ++Mask )
        {
            int Late = Gap == 3 ? 32 : Gap;
            if ( Abc_TtBitCount16(Mask) > 3 || (!Mask && Gap) || (Mask && !Gap) ) continue;
            for ( i = 0; i < 4; ++i ) Times[i] = (Mask >> i & 1) ? Late : 0;
            if ( Lms_KernelSynth(m, t, Times, v, Depths) >= 0 )
                Lmk_ProfileAdd(m, Id, v, Depths);
        }
        for ( a = 0; a < 4; ++a )
        for ( b = 0; b < 4; ++b ) if ( b != a )
        for ( c = 0; c < 4; ++c ) if ( c != a && c != b )
        {
            d = 6-a-b-c;
            Times[a] = 0; Times[b] = 1; Times[c] = 2; Times[d] = 3;
            if ( Lms_KernelSynth(m, t, Times, v, Depths) >= 0 )
                Lmk_ProfileAdd(m, Id, v, Depths);
        }
        for ( Mask = 1; Mask < 16; ++Mask ) if ( Abc_TtBitCount16(Mask) == 3 )
        for ( a = 0; a < 4; ++a ) if ( Mask >> a & 1 )
        {
            for ( Gap = 0; Gap < 2; ++Gap )
            {
                for ( i = 0; i < 4; ++i ) Times[i] = (Mask >> i & 1) ? (Gap ? 32 : 30) : 0;
                Times[a] = Gap ? 30 : 32;
                if ( Lms_KernelSynth(m, t, Times, v, Depths) >= 0 )
                    Lmk_ProfileAdd(m, Id, v, Depths);
            }
        }
        for ( a = 0; a < 4; ++a )
        for ( b = 0; b < 4; ++b ) if ( b != a )
        for ( Gap = 1; Gap <= 2; ++Gap )
        {
            memset(Times, 0, sizeof(Times)); Times[a] = 32; Times[b] = 32-Gap;
            if ( Lms_KernelSynth(m, t, Times, v, Depths) >= 0 )
                Lmk_ProfileAdd(m, Id, v, Depths);
        }
        Vec_IntFree(v);
    }
    for ( p = m->pProfiles[Id]; p; p = p->pNext )
    {
        int Delay = 0;
        for ( i = 0; i < 4; ++i )
            if ( p->Depths[i] >= 0 ) Delay = Abc_MaxInt(Delay, pTimes[i]+p->Depths[i]);
        if ( !pBest || Delay < Best || (Delay == Best && p->Area < pBest->Area) )
        { pBest = p; Best = Delay; }
    }
    if ( !pBest ) return -1;
    Vec_IntClear(vAig); Vec_IntPushArray(vAig, pBest->Fans, 2*pBest->nAnds);
    Vec_IntPush(vAig, pBest->Root ^ Phase);
    memcpy(pDepths, pBest->Depths, sizeof(pBest->Depths));
    return Best;
}
// Enumerate an already frozen pool, preserving each whole graph. This avoids
// repeating complete-cut synthesis for every synthetic timing probe.
/**Function*************************************************************

  Synopsis    [Enumerate a small-function frontier profile.]

  Description [Returns its area, or -1 when Index is past the end.]

  SideEffects [Builds missing profiles and writes vAig and pDepths.]

  SeeAlso     []

***********************************************************************/
int Lms_KernelProfile( void * pData, unsigned Truth, int Index,
    Vec_Int_t * vAig, int * pDepths )
{
    Lmk_Man_t * m = (Lmk_Man_t *)pData;
    unsigned Phase = Truth&1, t = (Truth&65535u) ^ (Phase ? 65535u : 0);
    Lmk_Profile_t * p;
    int Times[4] = {0};
    if ( !m || Index < 0 ) return -1;
    if ( !m->pProfiles[t>>1] && Lms_KernelFrontier(m, Truth, Times, vAig, pDepths) < 0 ) return -1;
    for ( p = m->pProfiles[t>>1]; p && Index; p = p->pNext ) --Index;
    if ( !p ) return -1;
    Vec_IntClear(vAig); Vec_IntPushArray(vAig, p->Fans, 2*p->nAnds);
    Vec_IntPush(vAig, p->Root ^ Phase);
    memcpy(pDepths, p->Depths, sizeof(p->Depths));
    return p->Area;
}
/**Function*************************************************************

  Synopsis    [Free a small-function kernel manager.]

  Description [Accepts NULL.]

  SideEffects [Frees tables and profiles.]

  SeeAlso     []

***********************************************************************/
void Lms_KernelStop( void * pData )
{
    Lmk_Man_t * p = (Lmk_Man_t *)pData;
    int i;
    if ( !p ) return;
    for ( i = 0; i < 2; ++i )
    {
        Lmk_Table_t * a = p->pSampleTables[i];
        if ( a ) { ABC_FREE(a->Delay); ABC_FREE(a->Marks); ABC_FREE(a); }
    }
    for ( i = 0; i < LMK_TABLES; ++i )
    {
        Lmk_Table_t * a = p->pTables[i], * b = p->pSmallTables[i];
        if ( a ) { ABC_FREE(a->Delay); ABC_FREE(a->Marks); ABC_FREE(a); }
        if ( b ) { ABC_FREE(b->Delay); ABC_FREE(b->Marks); ABC_FREE(b); }
    }
    for ( i = 0; i < LMK_FUNCS; ++i )
    {
        Lmk_Profile_t * q, * qNext;
        for ( q = p->pProfiles[i]; q; q = qNext )
        { qNext = q->pNext; ABC_FREE(q); }
    }
    ABC_FREE(p);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
