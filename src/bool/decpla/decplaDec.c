/**CFile****************************************************************

  FileName    [decplaDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Bounded bi-decomposition with shared completed AIG nodes.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaDec.c,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "decplaInt.h"
#include "bool/bdc/bdc.h"
#include "misc/util/utilTruth.h"
#include <limits.h>
ABC_NAMESPACE_IMPL_START

typedef struct Decpla_Cache_t_ { int lit; word * support; } Decpla_Cache_t;
typedef struct Decpla_CacheState_t_ {
    Decpla_Cache_t cache[512];
    int nCache, nextInternal, nInternal;
} Decpla_CacheState_t;
typedef struct Decpla_Stats_t_ {
    unsigned nAnd, nOr, nMux, nReuse, nFallback, nAbandoned, nWeak, nXor, nDivisor;
    unsigned nCompletionTrials, nCompletionChanges;
} Decpla_Stats_t;
typedef struct Decpla_Dec_t_ {
    Decpla_Options_t o;
    Gia_Man_t * g;
    Decpla_Sat_t * sat;
    Decpla_Cache_t cache[512];
    int nCache, ni, nw, failed, work, nextInternal, nInternal;
    int fDivisorTrial, iSkipReuse, fCompletionTrial, nCommitted, fXorTrial;
    Vec_Int_t * shared, * outputs;
    word random;
    Decpla_Stats_t stats;
    unsigned nResubTrials, nResubChanges;
    unsigned nSupportTrials, nSupportChanges;
    FILE * err;
} Decpla_Dec_t;

void Decpla_OptionsDefault( Decpla_Options_t * o )
{
    memset(o,0,sizeof(*o));
    o->nCubesMax = 1024; o->nWorkMax = 200000;
    o->nNodesMax = 200000; o->nConfLimit = 10000; o->fReuse = 1;
    o->Features = 15;
}
static unsigned Decpla_DecRandom( Decpla_Dec_t * p, unsigned n )
{
    word z = (p->random += ABC_CONST(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * ABC_CONST(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * ABC_CONST(0x94d049bb133111eb);
    return (unsigned)((z ^ (z >> 31)) % n);
}
static int Decpla_Work( Decpla_Dec_t * p, int amount )
{
    if ( amount > p->work ) { p->work = 0; return 0; }
    p->work -= amount; return 1;
}
static void Decpla_IsfFree( Decpla_Isf_t * f )
{ free(f->On.pData); free(f->Off.pData); memset(f,0,sizeof(*f)); }
static int Decpla_Copy( Decpla_Cover_t * dst, const Decpla_Cover_t * src )
{
    size_t k; dst->nWords = src->nWords;
    for ( k = 0; k < src->nCubes; ++k ) if ( !Decpla_CoverPush(dst,src->pData+k*src->nWords) ) return 0;
    return 1;
}
static int Decpla_Subset( const word * a, const word * b, int nw )
{ int w; for ( w = 0; w < nw; ++w ) if ( a[w] & ~b[w] ) return 0; return 1; }
// Exact union insertion, with absorption. Exhaustion rejects the candidate;
// it must never be mistaken for an empty cover or a successful proof.
static int Decpla_Insert( Decpla_Dec_t * p, Decpla_Cover_t * c, const word * cube )
{
    size_t k;
    for ( k = 0; k < c->nCubes; ) {
        word * old = c->pData+k*p->nw;
        if ( !Decpla_Work(p,p->nw) ) return 0;
        if ( Decpla_Subset(old,cube,p->nw) ) return 1;
        if ( Decpla_Subset(cube,old,p->nw) ) {
            --c->nCubes;
            memmove(old,old+p->nw,(c->nCubes-k)*p->nw*sizeof(word));
        } else ++k;
    }
    if ( c->nCubes >= (size_t)p->o.nCubesMax ) return 0;
    if ( !Decpla_CoverPush(c,cube) ) { p->failed = 1; return 0; }
    return 1;
}
static int Decpla_Project( Decpla_Dec_t * p, Decpla_Cover_t * dst, const Decpla_Cover_t * src, const word * kill )
{
    size_t k; int w, ok = 1;
    word * tmp = (word *)malloc(p->nw*sizeof(word));
    if ( !tmp ) { p->failed = 1; return 0; }
    dst->nWords = p->nw;
    for ( k = 0; k < src->nCubes; ++k ) {
        if ( !Decpla_Work(p,p->nw) ) { ok = 0; break; }
        for ( w = 0; w < p->nw; ++w ) tmp[w] = src->pData[k*p->nw+w] & ~kill[w];
        if ( !Decpla_Insert(p,dst,tmp) ) { ok = 0; break; }
    }
    free(tmp); return ok;
}
static int Decpla_Intersect( const word * a, const word * b, word * dst, int nw )
{
    int w;
    for ( w = 0; w < nw; ++w ) {
        word t = a[w] | b[w];
        if ( t & (t>>1) & ABC_CONST(0x5555555555555555) ) return 0;
        dst[w] = t;
    }
    return 1;
}
static int Decpla_Product( Decpla_Dec_t * p, Decpla_Cover_t * dst, const Decpla_Cover_t * a, const Decpla_Cover_t * b, const word * kill )
{
    size_t i, j; int w, ok = 1;
    word * tmp = (word *)malloc(p->nw*sizeof(word));
    if ( !tmp ) { p->failed = 1; return 0; }
    dst->nWords = p->nw;
    for ( i = 0; ok && i < a->nCubes; ++i ) for ( j = 0; j < b->nCubes; ++j ) {
        if ( !Decpla_Work(p,p->nw) ) { ok = 0; break; }
        if ( !Decpla_Intersect(a->pData+i*p->nw,b->pData+j*p->nw,tmp,p->nw) ) continue;
        for ( w = 0; w < p->nw; ++w ) tmp[w] &= ~kill[w];
        if ( !Decpla_Insert(p,dst,tmp) ) { ok = 0; break; }
    }
    free(tmp); return ok;
}
// OR feasibility: On & exists_A(Off) & exists_B(Off) is empty.
static int Decpla_PartitionTest( Decpla_Dec_t * p, const Decpla_Isf_t * f, const word * a, const word * b )
{
    Decpla_Cover_t x, y; size_t i, j, k; int result = -1;
    word * tmp = (word *)malloc(2*p->nw*sizeof(word));
    memset(&x,0,sizeof(x)); memset(&y,0,sizeof(y));
    if ( !tmp ) { p->failed = 1; return -1; }
    if ( !Decpla_Project(p,&x,&f->Off,a) || !Decpla_Project(p,&y,&f->Off,b) ) goto done;
    for ( i = 0; i < f->On.nCubes; ++i ) for ( j = 0; j < x.nCubes; ++j ) {
        if ( !Decpla_Work(p,p->nw) ) goto done;
        if ( !Decpla_Intersect(f->On.pData+i*p->nw,x.pData+j*p->nw,tmp,p->nw) ) continue;
        for ( k = 0; k < y.nCubes; ++k ) {
            if ( !Decpla_Work(p,p->nw) ) goto done;
            if ( Decpla_Intersect(tmp,y.pData+k*p->nw,tmp+p->nw,p->nw) ) { result = 0; goto done; }
        }
    }
    result = 1;
done:
    free(x.pData); free(y.pData); free(tmp); return result;
}
static word Decpla_Group( Decpla_Dec_t * p, const Decpla_Isf_t * f, const int * vars, int nv, word * a, word * b )
{
    int i, j, found = 0, na = 1, nb = 1;
    memset(a,0,p->nw*sizeof(word)); memset(b,0,p->nw*sizeof(word));
    for ( i = 0; !found && i < nv && p->work; ++i ) for ( j = i+1; j < nv && p->work; ++j ) {
        Decpla_CubeSet(a,vars[i],3); Decpla_CubeSet(b,vars[j],3);
        if ( Decpla_PartitionTest(p,f,a,b) == 1 ) { found = 1; break; }
        Decpla_CubeSet(a,vars[i],0); Decpla_CubeSet(b,vars[j],0);
    }
    if ( !found ) return 0;
    for ( i = 0; i < nv && p->work; ++i ) {
        word * first = na <= nb ? a : b, * second = first == a ? b : a;
        int v = vars[i];
        if ( Decpla_CubeLit(a,v) || Decpla_CubeLit(b,v) ) continue;
        Decpla_CubeSet(first,v,3);
        if ( Decpla_PartitionTest(p,f,a,b) == 1 ) { if ( first == a ) ++na; else ++nb; continue; }
        Decpla_CubeSet(first,v,0); Decpla_CubeSet(second,v,3);
        if ( Decpla_PartitionTest(p,f,a,b) == 1 ) { if ( second == a ) ++na; else ++nb; continue; }
        Decpla_CubeSet(second,v,0);
    }
    return (word)(na < nb ? na : nb)*nv + na+nb;
}
// Does cube contain a point outside this cover? Exact bounded subtraction;
// unknown (-1) rejects a weak candidate instead of claiming progress.
static int Decpla_Uncovered( Decpla_Dec_t * p, word * cube, const Decpla_Cover_t * c, size_t start, int depth )
{
    size_t k; int w, v, result;
    if ( depth >= 128 ) return -1;
    for ( k = start; k < c->nCubes; ++k ) {
        const word * other = c->pData+k*p->nw;
        if ( !Decpla_Work(p,p->nw) ) return -1;
        for ( w = 0; w < p->nw; ++w ) {
            word t = cube[w] | other[w];
            if ( t & (t>>1) & ABC_CONST(0x5555555555555555) ) break;
        }
        if ( w < p->nw ) continue;
        if ( Decpla_Subset(other,cube,p->nw) ) return 0;
        for ( v = 0; v < p->ni; ++v ) if ( !Decpla_CubeLit(cube,v) && Decpla_CubeLit(other,v) ) break;
        if ( v == p->ni ) return -1;
        Decpla_CubeSet(cube,v,Decpla_CubeLit(other,v)^3);
        result = Decpla_Uncovered(p,cube,c,k+1,depth+1);
        if ( result == 0 ) {
            Decpla_CubeSet(cube,v,Decpla_CubeLit(other,v));
            result = Decpla_Uncovered(p,cube,c,k,depth+1);
        }
        Decpla_CubeSet(cube,v,0); return result;
    }
    return 1;
}
static word Decpla_WeakGroup( Decpla_Dec_t * p, const Decpla_Isf_t * f, const int * vars, int nv, word * a, word * b )
{
    int v, found = 0; size_t k;
    word * cube = (word *)malloc(p->nw*sizeof(word));
    if ( !cube ) { p->failed = 1; return 0; }
    memset(a,0,p->nw*sizeof(word)); memset(b,0,p->nw*sizeof(word));
    for ( v = 0; v < nv && p->work; ++v ) {
        Decpla_Cover_t projected;
        memset(&projected,0,sizeof(projected)); Decpla_CubeSet(a,vars[v],3);
        if ( Decpla_Project(p,&projected,&f->Off,a) ) {
            for ( k = 0; k < f->On.nCubes && p->work; ++k ) {
                memcpy(cube,f->On.pData+k*p->nw,p->nw*sizeof(word));
                if ( Decpla_Uncovered(p,cube,&projected,0,0) == 1 ) { found = 1; break; }
            }
        }
        free(projected.pData);
        if ( found ) break;
        Decpla_CubeSet(a,vars[v],0);
    }
    free(cube); return (word)found;
}
static int Decpla_And( Decpla_Dec_t * p, int a, int b )
{
    if ( p->failed || a < 0 || b < 0 ) return -1;
    return Gia_ManHashAnd(p->g,a,b);
}
static int Decpla_Combine( Decpla_Dec_t * p, int * lits, int n, int isOr )
{
    int i, m;
    if ( !n ) return isOr ? 0 : 1;
    while ( n > 1 ) {
        for ( i = m = 0; i+1 < n; i += 2 ) {
            int t = Decpla_And(p,lits[i]^isOr,lits[i+1]^isOr);
            if ( t < 0 ) return -1;
            lits[m++] = t^isOr;
        }
        if ( i < n ) lits[m++] = lits[i];
        n = m;
    }
    return lits[0];
}
static int Decpla_Sop( Decpla_Dec_t * p, const Decpla_Isf_t * f )
{
    int phase = f->On.nCubes <= f->Off.nCubes, v, n, result = -1;
    const Decpla_Cover_t * c = phase ? &f->On : &f->Off;
    Vec_Int_t * cubes = Vec_IntAlloc(16), * lits = Vec_IntAlloc(16); size_t k;
    ++p->stats.nFallback;
    for ( k = 0; k < c->nCubes; ++k ) {
        Vec_IntClear(lits);
        for ( v = 0; v < p->ni; ++v ) {
            unsigned val = Decpla_CubeLit(c->pData+k*p->nw,v);
            if ( val ) Vec_IntPush(lits,2*(v+1) ^ (val == 1));
        }
        n = Decpla_Combine(p,Vec_IntArray(lits),Vec_IntSize(lits),0);
        if ( n < 0 ) goto done;
        Vec_IntPush(cubes,n);
    }
    result = Decpla_Combine(p,Vec_IntArray(cubes),Vec_IntSize(cubes),1);
    if ( result >= 0 ) result ^= !phase;
done:
    Vec_IntFree(cubes); Vec_IntFree(lits); return result;
}

/**Function*************************************************************

  Synopsis    [Moves a cache entry to the most recently used position.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Decpla_CacheTouch( Decpla_Dec_t * p, int i )
{
    Decpla_Cache_t entry = p->cache[i];
    memmove(p->cache+i,p->cache+i+1,(p->nCache-i-1)*sizeof(*p->cache));
    p->cache[p->nCache-1] = entry;
}
static int Decpla_Reuse( Decpla_Dec_t * p, const Decpla_Isf_t * f, const word * support )
{
    int i, complement, phase, coneSize, tried = 0;
    if ( !p->o.fReuse ) return -1;
    // Most-recent first; cap queries, not correctness. A missed or timed-out
    // match merely causes ordinary decomposition. Both polarities are tried.
    for ( i = p->nCache-1; i >= 0 && tried < 32; --i ) {
        if ( (p->cache[i].lit>>1) == p->iSkipReuse ) continue;
        if ( !Decpla_Subset(p->cache[i].support,support,p->nw) ) continue;
        ++tried;
        coneSize = Decpla_ConePrepare(p->sat,p->cache[i].lit);
        if ( coneSize < 0 ) return -1;
        for ( complement = 0; complement < 2; ++complement ) {
            int ok = 1, lit = p->cache[i].lit ^ complement;
            for ( phase = 0; ok && phase < 2; ++phase ) {
                const Decpla_Cover_t * c = phase ? &f->On : &f->Off; size_t k;
                for ( k = 0; k < c->nCubes; ++k ) {
                    if ( !Decpla_Work(p,coneSize) || Decpla_CubeProve(p->sat,c->pData+k*p->nw,lit,phase,100) != 1 ) { ok = 0; break; }
                }
            }
            if ( ok ) { Decpla_CacheTouch(p,i); ++p->stats.nReuse; return lit; }
        }
    }
    return -1;
}
static int Decpla_Remember( Decpla_Dec_t * p, int lit, const word * support )
{
    int i;
    // Constants and PIs already have direct completion shortcuts.
    if ( !p->o.fReuse || lit < 2 || Gia_ObjIsCi(Gia_ManObj(p->g,lit>>1)) ) return 0;
    for ( i = 0; i < p->nCache; ++i ) if ( (p->cache[i].lit>>1) == (lit>>1) ) {
        Decpla_CacheTouch(p,i); return 0;
    }
    if ( p->nCache == 512 || (size_t)(p->nCache+1)*p->nw*sizeof(word) > 8*1024*1024 ) {
        if ( !p->nCache ) return 0;
        // Recycle the oldest entry and its support buffer at either limit.
        Decpla_CacheTouch(p,0); i = p->nCache-1;
    } else {
        i = p->nCache;
        p->cache[i].support = (word *)malloc(p->nw*sizeof(word));
        if ( !p->cache[i].support ) return 0;
        ++p->nCache;
    }
    memcpy(p->cache[i].support,support,p->nw*sizeof(word));
    p->cache[i].lit = lit;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Copies and exchanges the functional cache around trials.]

  Description [Each alternative starts with the same cache. Only the
               selected alternative retains its entries and harvesting
               budget. The caller manages each trial's structural graph.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Decpla_CacheFree( Decpla_CacheState_t * state )
{
    int i;
    for ( i = 0; i < state->nCache; ++i ) free(state->cache[i].support);
    free(state);
}
static Decpla_CacheState_t * Decpla_CacheCopy( const Decpla_Cache_t * cache, int nCache, int nw, int nextInternal, int nInternal )
{
    Decpla_CacheState_t * state = (Decpla_CacheState_t *)calloc(1,sizeof(*state));
    int i;
    if ( !state ) return NULL;
    state->nextInternal = nextInternal; state->nInternal = nInternal;
    for ( i = 0; i < nCache; ++i ) {
        state->cache[i].support = (word *)malloc(nw*sizeof(word));
        if ( !state->cache[i].support ) { Decpla_CacheFree(state); return NULL; }
        memcpy(state->cache[i].support,cache[i].support,nw*sizeof(word));
        state->cache[i].lit = cache[i].lit; ++state->nCache;
    }
    return state;
}
static Decpla_CacheState_t * Decpla_CacheSave( Decpla_Dec_t * p )
{
    return Decpla_CacheCopy(p->cache,p->nCache,p->nw,p->nextInternal,p->nInternal);
}
static void Decpla_CacheSwap( Decpla_Dec_t * p, Decpla_CacheState_t * state )
{
    int i, swap;
    for ( i = 0; i < 512; ++i ) {
        Decpla_Cache_t entry = p->cache[i];
        p->cache[i] = state->cache[i]; state->cache[i] = entry;
    }
    swap = p->nCache; p->nCache = state->nCache; state->nCache = swap;
    swap = p->nextInternal; p->nextInternal = state->nextInternal; state->nextInternal = swap;
    swap = p->nInternal; p->nInternal = state->nInternal; state->nInternal = swap;
}

/**Function*************************************************************

  Synopsis    [Harvests new internal divisors reachable from a completion.]

  Description [Skip abandoned cones and retain half the cache for roots.
               Conservative supports only filter subsequent exact proofs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Decpla_Internal( Decpla_Dec_t * p, int lit )
{
    word * support; Vec_Int_t * stack, * nodes; int id, i, budget = p->o.nWorkMax;
    if ( !(p->o.Features & 4) || !p->o.fReuse || p->nInternal >= 256 ) return;
    support = (word *)calloc(p->nw,sizeof(word)); stack = Vec_IntAlloc(32);
    if ( !support ) { Vec_IntFree(stack); return; }
    nodes = Vec_IntAlloc(32);
    if ( p->nextInternal < p->ni+1 ) p->nextInternal = p->ni+1;
    Gia_ManIncrementTravId(p->g); Vec_IntPush(stack,lit>>1);
    while ( Vec_IntSize(stack) && budget-- > 0 ) {
        Gia_Obj_t * obj;
        id = Vec_IntPop(stack); obj = Gia_ManObj(p->g,id);
        if ( id < p->nextInternal || !Gia_ObjIsAnd(obj) || Gia_ObjIsTravIdCurrent(p->g,obj) ) continue;
        Gia_ObjSetTravIdCurrent(p->g,obj); Vec_IntPush(nodes,id);
        Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
    }
    Vec_IntSort(nodes,0);
    for ( i = 0; i < Vec_IntSize(nodes) && p->nInternal < 256 && budget > 0; ++i ) {
        memset(support,0,p->nw*sizeof(word)); Vec_IntClear(stack);
        Gia_ManIncrementTravId(p->g); Vec_IntPush(stack,Vec_IntEntry(nodes,i));
        while ( Vec_IntSize(stack) && budget-- > 0 ) {
            Gia_Obj_t * obj;
            id = Vec_IntPop(stack); obj = Gia_ManObj(p->g,id);
            if ( Gia_ObjIsTravIdCurrent(p->g,obj) ) continue;
            Gia_ObjSetTravIdCurrent(p->g,obj);
            if ( Gia_ObjIsCi(obj) ) Decpla_CubeSet(support,Gia_ObjCioId(obj),3);
            else if ( Gia_ObjIsAnd(obj) ) {
                Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
            }
        }
        if ( Vec_IntSize(stack) ) break; // Never cache incomplete support.
        p->nInternal += Decpla_Remember(p,2*Vec_IntEntry(nodes,i),support);
    }
    p->nextInternal = Gia_ManObjNum(p->g);
    free(support); Vec_IntFree(stack); Vec_IntFree(nodes);
}
// Evaluate both possible first components before committing to an order.
// A cached first component costs no new gates. Lookup is proof-based and
// preview hits are not counted as actual reuse.
static int Decpla_PreviewReuse( Decpla_Dec_t * p, const Decpla_Isf_t * f, const word * a, const word * b )
{
    Decpla_Cover_t projected; Decpla_Isf_t left; Decpla_Man_t local;
    word * support; int result = 0, phase, w, v; size_t k;
    unsigned savedReuse = p->stats.nReuse;
    memset(&projected,0,sizeof(projected)); memset(&left,0,sizeof(left)); memset(&local,0,sizeof(local));
    if ( !p->o.fReuse || !p->nCache ) return 0;
    support = (word *)calloc(p->nw,sizeof(word));
    if ( !support ) return 0;
    p->work = p->o.nWorkMax / 4;
    if ( !Decpla_Project(p,&projected,&f->Off,a) || !Decpla_Product(p,&left.On,&f->On,&projected,b) || !Decpla_Project(p,&left.Off,&f->Off,b) ) goto done;
    local.nInputs = p->ni; local.nOutputs = 1; local.pIsfs = &left;
    if ( !Decpla_Minimize(&local,p->err) ) goto done;
    for ( phase = 0; phase < 2; ++phase ) {
        const Decpla_Cover_t * c = phase ? &left.On : &left.Off;
        for ( k = 0; k < c->nCubes; ++k ) for ( w = 0; w < p->nw; ++w ) support[w] |= c->pData[k*p->nw+w];
    }
    for ( v = 0; v < p->ni; ++v ) if ( Decpla_CubeLit(support,v) ) Decpla_CubeSet(support,v,3);
    p->work = p->o.nWorkMax / 4;
    result = Decpla_Reuse(p,&left,support) >= 0;
done:
    p->stats.nReuse = savedReuse; free(support); free(projected.pData); Decpla_IsfFree(&left); return result;
}
// Intersect a cover with the *completed* left function's zero set without
// globally expanding either polarity of that function. Split only cubes
// whose ternary evaluation is unknown, within the work/cube limits.
static int Decpla_FilterRec( Decpla_Dec_t * p, word * cube, int lit, const word * kill, Decpla_Cover_t * dst, int depth, int coneSize )
{
    int value, v, ok;
    word * projected;
    if ( !Decpla_Work(p,coneSize) ) return 0;
    value = Decpla_CubeEval(p->sat,cube,lit);
    if ( value < 0 ) { p->failed = 1; return 0; }
    if ( value == 1 ) return 1;
    if ( value == 0 ) {
        projected = (word *)malloc(p->nw*sizeof(word));
        if ( !projected ) { p->failed = 1; return 0; }
        for ( v = 0; v < p->nw; ++v ) projected[v] = cube[v] & ~kill[v];
        ok = Decpla_Insert(p,dst,projected); free(projected); return ok;
    }
    if ( depth >= 128 ) return 0;
    // Evaluation already found the first unspecified input in this cone.
    v = Decpla_CubeSplit(p->sat);
    if ( v < 0 ) return 0;
    Decpla_CubeSet(cube,v,1); ok = Decpla_FilterRec(p,cube,lit,kill,dst,depth+1,coneSize);
    if ( ok ) { Decpla_CubeSet(cube,v,2); ok = Decpla_FilterRec(p,cube,lit,kill,dst,depth+1,coneSize); }
    Decpla_CubeSet(cube,v,0); return ok;
}
static int Decpla_Filter( Decpla_Dec_t * p, Decpla_Cover_t * dst, const Decpla_Cover_t * src, int lit, const word * kill )
{
    size_t k; int ok = 1, coneSize = Decpla_ConePrepare(p->sat,lit);
    word * tmp;
    if ( coneSize < 0 ) { p->failed = 1; return 0; }
    tmp = (word *)malloc(p->nw*sizeof(word));
    if ( !tmp ) { p->failed = 1; return 0; }
    dst->nWords = p->nw;
    for ( k = 0; ok && k < src->nCubes; ++k ) {
        memcpy(tmp,src->pData+k*p->nw,p->nw*sizeof(word));
        ok = Decpla_FilterRec(p,tmp,lit,kill,dst,0,coneSize);
    }
    free(tmp); return ok;
}

/**Function*************************************************************

  Synopsis    [Finds a cached divisor and constructs its exact residual.]

  Description [Simulation rejects candidates but never proves them. In the
               OR phase, the divisor must be zero on every Off cube and one
               at some On point. The residual is (On & !divisor, Off).
               Complementing the specification gives the dual AND phase.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_Divisor( Decpla_Dec_t * p, const Decpla_Isf_t * f, Decpla_Isf_t * residual, int * outputPhase )
{
    int candidates[64], scores[256], literals[256], phases[256];
    int i, id, v, phase, complement, sample, nc = 0, nt = 0, tried;
    int result = -1, n = Gia_ManObjNum(p->g);
    word * sim, * kill, random = ABC_CONST(0x243f6a8885a308d3);
    Vec_Int_t * stack;
    if ( !p->o.fReuse || !p->nCache || p->fDivisorTrial || p->ni > p->o.nWorkMax / 64 ) return -1;
    for ( i = p->nCache-1; i >= 0 && nc < 64; --i ) {
        id = p->cache[i].lit>>1;
        if ( id < Vec_IntSize(p->shared) && Vec_IntEntry(p->shared,id) ) candidates[nc++] = p->cache[i].lit;
    }
    if ( !nc ) return -1;
    sim = (word *)malloc(n*sizeof(word)); kill = (word *)calloc(p->nw,sizeof(word));
    stack = Vec_IntAlloc(32);
    if ( !sim || !kill ) goto done;
    memset(sim,0,(p->ni+1)*sizeof(word));
    // Use a separate deterministic stream so misses do not change grouping.
    for ( sample = 0; sample < 64; ++sample ) {
        const Decpla_Cover_t * c = (sample&1) ? &f->On : &f->Off;
        const word * cube = c->pData + ((size_t)(sample/2)*c->nCubes/32)*p->nw;
        for ( v = 0; v < p->ni; ++v ) {
            unsigned value = Decpla_CubeLit(cube,v);
            random ^= random << 13; random ^= random >> 7; random ^= random << 17;
            if ( value == 2 || (!value && (random&1)) ) sim[v+1] |= (word)1 << sample;
        }
    }
    // Simulate just the union of candidate cones, once for all 64 patterns.
    Gia_ManIncrementTravId(p->g); p->work = p->o.nWorkMax;
    for ( i = 0; i < nc; ++i ) {
        Vec_IntPush(stack,candidates[i]>>1);
        while ( Vec_IntSize(stack) ) {
            Gia_Obj_t * obj;
            id = Vec_IntPop(stack);
            if ( !Decpla_Work(p,1) ) goto done;
            if ( id < 0 ) {
                word a, b;
                id = ~id; obj = Gia_ManObj(p->g,id);
                a = sim[Gia_ObjFaninId0(obj,id)]; b = sim[Gia_ObjFaninId1(obj,id)];
                sim[id] = (Gia_ObjFaninC0(obj) ? ~a : a) & (Gia_ObjFaninC1(obj) ? ~b : b);
                continue;
            }
            obj = Gia_ManObj(p->g,id);
            if ( !Gia_ObjIsAnd(obj) || Gia_ObjIsTravIdCurrent(p->g,obj) ) continue;
            Gia_ObjSetTravIdCurrent(p->g,obj);
            Vec_IntPush(stack,~id);
            Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
        }
        for ( phase = 0; phase < 2; ++phase ) for ( complement = 0; complement < 2; ++complement ) {
            word on = phase ? ABC_CONST(0x5555555555555555) : ABC_CONST(0xaaaaaaaaaaaaaaaa);
            int lit = candidates[i]^complement;
            word values = (lit&1) ? ~sim[lit>>1] : sim[lit>>1];
            if ( (values & ~on) || !(values & on) ) continue;
            literals[nt] = lit; phases[nt] = phase; scores[nt++] = Abc_TtCountOnes(values & on);
        }
    }
    for ( tried = 0; tried < 8; ++tried ) {
        const Decpla_Cover_t * on, * off;
        size_t k;
        int best = -1, coneSize, ok = 1;
        for ( i = 0; i < nt; ++i ) if ( scores[i] > 0 && (best < 0 || scores[i] > scores[best]) ) best = i;
        if ( best < 0 ) break;
        scores[best] = 0; phase = phases[best];
        on = phase ? &f->Off : &f->On; off = phase ? &f->On : &f->Off;
        coneSize = Decpla_ConePrepare(p->sat,literals[best]);
        if ( coneSize < 0 ) break;
        p->work = p->o.nWorkMax;
        for ( k = 0; k < off->nCubes; ++k )
            if ( !Decpla_Work(p,coneSize) || Decpla_CubeProve(p->sat,off->pData+k*p->nw,literals[best],0,100) != 1 ) { ok = 0; break; }
        if ( !ok ) continue;
        p->work = p->o.nWorkMax;
        if ( Decpla_Filter(p,&residual->On,on,literals[best],kill) && residual->On.nCubes < on->nCubes && Decpla_Copy(&residual->Off,off) ) {
            result = literals[best]; *outputPhase = phase; break;
        }
        Decpla_IsfFree(residual);
        if ( p->failed ) break;
    }
done:
    free(sim); free(kill); Vec_IntFree(stack); return result;
}
static int Decpla_ParityRoot( const int * parent, const int * parity, int v, int * value )
{
    *value = 0;
    while ( parent[v] != v ) { *value ^= parity[v]; v = parent[v]; }
    return v;
}
// Optional bounded leaf comparison against ABC's mature truth-table engine.
// Only <=8-variable ISFs are expanded, with care bits passed explicitly.
static int Decpla_SmallBdc( Decpla_Dec_t * p, const Decpla_Isf_t * f, const int * vars, int nv )
{
    unsigned on[8], care[8]; Bdc_Par_t pars; Bdc_Man_t * manager;
    int x, phase, v, count, result = -1;
    if ( nv < 2 || nv > 8 ) return -1;
    memset(on,0,sizeof(on)); memset(care,0,sizeof(care)); memset(&pars,0,sizeof(pars));
    count = 1 << (nv < 5 ? 5 : nv); p->work = p->o.nWorkMax;
    for ( x = 0; x < count; ++x ) for ( phase = 0; phase < 2 && !(care[x>>5] & (1u << (x&31))); ++phase ) {
        const Decpla_Cover_t * cover = phase ? &f->On : &f->Off; size_t k;
        for ( k = 0; k < cover->nCubes; ++k ) {
            int matches = 1;
            if ( !Decpla_Work(p,nv) ) return -1;
            for ( v = 0; v < nv; ++v ) {
                unsigned lit = Decpla_CubeLit(cover->pData+k*p->nw,vars[v]);
                if ( lit && lit != (unsigned)((x>>v)&1)+1 ) { matches = 0; break; }
            }
            if ( matches ) {
                care[x>>5] |= 1u << (x&31);
                if ( phase ) on[x>>5] |= 1u << (x&31);
                break;
            }
        }
    }
    pars.nVarsMax = 8; manager = Bdc_ManAlloc(&pars);
    if ( Bdc_ManDecompose(manager,on,care,nv,NULL,1000) >= 0 ) {
        Bdc_FuncSetCopyInt(Bdc_ManFunc(manager,0),1);
        for ( v = 0; v < nv; ++v ) Bdc_FuncSetCopyInt(Bdc_ManFunc(manager,v+1),2*(vars[v]+1));
        for ( v = nv+1; v < Bdc_ManNodeNum(manager); ++v ) {
            Bdc_Fun_t * node = Bdc_ManFunc(manager,v);
            int lit = Decpla_And(p,Bdc_FunFanin0Copy(node),Bdc_FunFanin1Copy(node));
            if ( lit < 0 ) break;
            Bdc_FuncSetCopyInt(node,lit);
        }
        if ( !p->failed ) result = Bdc_FunObjCopy(Bdc_ManRoot(manager));
    }
    Bdc_ManFree(manager); return result;
}
// Bounded disjoint XOR decomposition. Care minterms impose bipartite parity
// equations g(A) XOR h(B) = f. A conflicting cycle rejects the partition.
// Every observed vertex is fixed in the child ISFs, so their independent
// completion cannot violate a parent care point. Unobserved vertices stay DC.
// The bounded truth table is temporary; the recursive representation is cubes.
static int Decpla_XorGroup( Decpla_Dec_t * p, const Decpla_Isf_t * f, const int * vars, int nv, Decpla_Isf_t * children )
{
    int truth[256], parent[256], parity[256], seen[256], bestValues[256], bestSeen[256];
    int x, v, phase, mask, limit, best = 0, bestScore = 0, bestNa = 0;
    word * cube;
    if ( nv < 2 || nv > 8 ) return 0;
    limit = 1 << nv; p->work = p->o.nWorkMax;
    for ( x = 0; x < limit; ++x ) {
        truth[x] = -1;
        for ( phase = 0; phase < 2 && truth[x] < 0; ++phase ) {
            const Decpla_Cover_t * cover = phase ? &f->On : &f->Off; size_t k;
            for ( k = 0; k < cover->nCubes; ++k ) {
                int matches = 1;
                if ( !Decpla_Work(p,nv) ) return 0;
                for ( v = 0; v < nv; ++v ) {
                    unsigned lit = Decpla_CubeLit(cover->pData+k*p->nw,vars[v]);
                    if ( lit && lit != (unsigned)((x>>v)&1)+1 ) { matches = 0; break; }
                }
                if ( matches ) { truth[x] = phase; break; }
            }
        }
    }
    for ( mask = 1; mask < limit-1; mask += 2 ) {
        int na = 0, rows, count, ok = 1, score;
        for ( v = 0; v < nv; ++v ) na += (mask>>v)&1;
        score = na < nv-na ? na : nv-na;
        if ( score <= bestScore ) continue;
        rows = 1 << na; count = rows + (1 << (nv-na));
        for ( v = 0; v < count; ++v ) { parent[v] = v; parity[v] = seen[v] = 0; }
        for ( x = 0; x < limit && ok; ++x ) if ( truth[x] >= 0 ) {
            int a = 0, b = 0, ia = 0, ib = 0, ra, rb, pa, pb;
            if ( !Decpla_Work(p,nv+count) ) return 0;
            for ( v = 0; v < nv; ++v )
                if ( (mask>>v)&1 ) a |= ((x>>v)&1) << ia++;
                else b |= ((x>>v)&1) << ib++;
            b += rows; seen[a] = seen[b] = 1;
            ra = Decpla_ParityRoot(parent,parity,a,&pa); rb = Decpla_ParityRoot(parent,parity,b,&pb);
            if ( ra == rb ) ok = (pa ^ pb) == truth[x];
            else { parent[ra] = rb; parity[ra] = pa ^ pb ^ truth[x]; }
        }
        if ( ok ) {
            best = mask; bestScore = score; bestNa = na;
            for ( v = 0; v < count; ++v ) {
                Decpla_ParityRoot(parent,parity,v,&bestValues[v]); bestSeen[v] = seen[v];
            }
        }
    }
    if ( !best ) return 0;
    cube = (word *)calloc(p->nw,sizeof(word));
    if ( !cube ) { p->failed = 1; return 0; }
    for ( phase = 0; phase < 2; ++phase ) {
        int count = 1 << (phase ? nv-bestNa : bestNa), base = phase ? 1 << bestNa : 0;
        children[phase].On.nWords = children[phase].Off.nWords = p->nw;
        for ( x = 0; x < count; ++x ) if ( bestSeen[base+x] ) {
            int bit = 0; Decpla_Cover_t * dst = bestValues[base+x] ? &children[phase].On : &children[phase].Off;
            memset(cube,0,p->nw*sizeof(word));
            for ( v = 0; v < nv; ++v ) if ( ((best>>v)&1) == !phase )
                Decpla_CubeSet(cube,vars[v],((x>>bit++)&1)+1);
            if ( !Decpla_CoverPush(dst,cube) ) { p->failed = 1; free(cube); return 0; }
        }
    }
    free(cube); return 1;
}
static int Decpla_ConeSize( Gia_Man_t * g, int lit, Vec_Int_t * stack, const int * shared );
static int Decpla_Recurse( Decpla_Dec_t * p, Decpla_Isf_t * f, int depth );
static int Decpla_RecurseBody( Decpla_Dec_t * p, Decpla_Isf_t * f, int depth, word * support, int * vars, int nv, int fTryXor );

/**Function*************************************************************

  Synopsis    [Counts shared AND/XOR gates for a root and completed outputs.]

  Description [A candidate exceeding the committed AND limit is infeasible,
               even if extracting XORs would reduce its gate count.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_GateCost( Decpla_Dec_t * p, int lit, int * pAnds )
{
    Gia_Man_t * copy = Gia_ManDup(p->g), * clean, * xag;
    int i, root, cost;
    if ( p->outputs ) Vec_IntForEachEntry(p->outputs,root,i) Gia_ManAppendCo(copy,root);
    Gia_ManAppendCo(copy,lit);
    clean = Gia_ManCleanup(copy); Gia_ManStop(copy);
    *pAnds = Gia_ManAndNum(clean);
    if ( Gia_ManAndNum(clean) > p->o.nNodesMax ) {
        Gia_ManStop(clean); return INT_MAX;
    }
    xag = Gia_ManDupMuxes(clean,1); Gia_ManStop(clean);
    cost = Gia_ManAndNum(xag); Gia_ManStop(xag);
    return cost;
}

/**Function*************************************************************

  Synopsis    [Accepts an XOR trial only when both area measures permit it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_XorBetter( Decpla_Dec_t * p, int baseline, int trial )
{
    int baseAnds, trialAnds, baseGates, trialGates;
    Gia_ManLevelNum(p->g);
    if ( Gia_ObjLevelId(p->g,trial>>1) > Gia_ObjLevelId(p->g,baseline>>1)+2 ) return 0;
    baseGates = Decpla_GateCost(p,baseline,&baseAnds);
    trialGates = Decpla_GateCost(p,trial,&trialAnds);
    return trialAnds <= baseAnds && trialGates < baseGates;
}

/**Function*************************************************************

  Synopsis    [Selects a Shannon variable by cofactor cover complexity.]

  Description [Sum literal counts in each cofactor's smaller cover.
               Constant cofactors cost zero; ties use total cube counts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_ShannonVar( const Decpla_Isf_t * f, const int * vars, int nv )
{
    typedef struct { size_t cubes[2][2], literals[2][2]; } Cofactor;
    Cofactor * scores = (Cofactor *)calloc(nv,sizeof(*scores));
    int v, w, phase, branch, best = vars[0], bestSimple = -1;
    size_t bestCost = ~(size_t)0, bestSize = ~(size_t)0;
    if ( !scores ) return best;
    for ( phase = 0; phase < 2; ++phase ) {
        const Decpla_Cover_t * c = phase ? &f->On : &f->Off;
        size_t k;
        for ( k = 0; k < c->nCubes; ++k ) {
            const word * cube = c->pData+k*c->nWords;
            size_t literals = 0;
            for ( w = 0; w < c->nWords; ++w ) literals += Abc_TtCountOnes(cube[w]);
            for ( v = 0; v < nv; ++v ) {
                unsigned val = Decpla_CubeLit(cube,vars[v]);
                for ( branch = 0; branch < 2; ++branch ) if ( !val || val == (unsigned)branch+1 ) {
                    ++scores[v].cubes[phase][branch];
                    scores[v].literals[phase][branch] += literals - (val != 0);
                }
            }
        }
    }
    for ( v = 0; v < nv; ++v ) {
        int simple = 0;
        size_t cost = 0, size = 0;
        for ( branch = 0; branch < 2; ++branch ) {
            size_t on = scores[v].cubes[1][branch], off = scores[v].cubes[0][branch];
            size_t a = scores[v].literals[1][branch], b = scores[v].literals[0][branch];
            size += on+off;
            if ( on && off ) cost += a < b ? a : b;
            simple += !on || !off ? 2 : on == 1 || off == 1;
        }
        if ( cost < bestCost || (cost == bestCost && (simple > bestSimple || (simple == bestSimple && size < bestSize))) ) {
            bestCost = cost; bestSize = size; bestSimple = simple; best = vars[v];
        }
    }
    free(scores);
    return best;
}

/**Function*************************************************************

  Synopsis    [Builds one ordered completion of an AND/OR partition.]

  Description [The second component uses the actual first completion.
               Swapping On and Off constructs the dual AND partition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_Complete( Decpla_Dec_t * p, const Decpla_Isf_t * f, const word * a, const word * b, int phase, int weak, int depth )
{
    Decpla_Isf_t normalized = *f, left, right;
    Decpla_Cover_t projected;
    int l = -1, r = -1, result = -1, ok;
    memset(&left,0,sizeof(left)); memset(&right,0,sizeof(right)); memset(&projected,0,sizeof(projected));
    if ( phase ) { normalized.On = f->Off; normalized.Off = f->On; }
    p->work = p->o.nWorkMax;
    ok = Decpla_Project(p,&projected,&normalized.Off,a) &&
         Decpla_Product(p,&left.On,&normalized.On,&projected,b) &&
         Decpla_Project(p,&left.Off,&normalized.Off,b);
    free(projected.pData);
    if ( ok ) l = Decpla_Recurse(p,&left,depth+1);
    p->work = p->o.nWorkMax;
    if ( l >= 0 ) ok = Decpla_Filter(p,&right.On,&normalized.On,l,a) && Decpla_Project(p,&right.Off,&normalized.Off,a);
    else ok = 0;
    if ( ok ) r = Decpla_Recurse(p,&right,depth+1);
    Decpla_IsfFree(&left); Decpla_IsfFree(&right);
    if ( r >= 0 ) {
        result = Decpla_And(p,l^1,r^1);
        if ( result >= 0 ) result ^= !phase;
        if ( weak ) ++p->stats.nWeak;
        if ( phase ) ++p->stats.nAnd; else ++p->stats.nOr;
    } else ++p->stats.nAbandoned;
    return result;
}

static int Decpla_Recurse( Decpla_Dec_t * p, Decpla_Isf_t * f, int depth )
{
    Decpla_Man_t local;
    word * support = NULL;
    int * vars = NULL;
    int v, w, phase, nv = 0, result = -1;
    size_t k;
    if ( p->failed ) return -1;
    if ( !f->On.nCubes ) return 0;
    if ( !f->Off.nCubes ) return 1;
    if ( depth >= 128 ) return Decpla_Sop(p,f);
    // Match before projection commits to one support; a cached completion
    // can satisfy the ISF using different variables.
    if ( (p->o.Features & 16) && p->nCache ) {
        word * allowed = (word *)malloc(p->nw*sizeof(word));
        if ( allowed ) {
            memset(allowed,255,p->nw*sizeof(word)); p->work = p->o.nWorkMax;
            result = Decpla_Reuse(p,f,allowed); free(allowed);
            if ( result >= 0 ) return result;
        }
    }
    memset(&local,0,sizeof(local)); local.nInputs = p->ni; local.nOutputs = 1; local.pIsfs = f;
    if ( depth ? !Decpla_Minimize(&local,p->err) : p->o.fBaseline ? !Decpla_Minimize(&local,p->err) : !Decpla_MinimizeSeeded(&local,p->o.Seed,8*1024*1024,p->err) ) { p->failed = 1; return -1; }
    support = (word *)calloc(p->nw,sizeof(word));
    vars = (int *)malloc(p->ni*sizeof(int));
    if ( !support || !vars ) { p->failed = 1; goto done; }
    for ( phase = 0; phase < 2; ++phase ) {
        const Decpla_Cover_t * c = phase ? &f->On : &f->Off;
        for ( k = 0; k < c->nCubes; ++k ) for ( w = 0; w < p->nw; ++w ) support[w] |= c->pData[k*p->nw+w];
    }
    for ( v = 0; v < p->ni; ++v ) if ( Decpla_CubeLit(support,v) ) { Decpla_CubeSet(support,v,3); vars[nv++] = v; }
    // A one-variable consistent ISF is a PI or its complement.
    if ( nv == 1 ) { result = 2*(vars[0]+1) ^ (Decpla_CubeLit(f->On.pData,vars[0]) == 1); goto remember; }
    p->work = p->o.nWorkMax;
    result = Decpla_Reuse(p,f,support);
    if ( result >= 0 ) goto done;
    // A single cube (or complement of one) already has a direct completion.
    if ( f->On.nCubes == 1 || f->Off.nCubes == 1 ) { result = Decpla_Sop(p,f); goto remember; }
    result = Decpla_RecurseBody(p,f,depth,support,vars,nv,1);
remember:
    if ( result >= 0 ) { Decpla_Internal(p,result); Decpla_Remember(p,result,support); }
done:
    free(support); free(vars); return result;
}

/**Function*************************************************************

  Synopsis    [Decomposes an already minimized, nontrivial specification.]

  Description [A trial baseline enters here without repeating support
               minimization or the cache scan. Skipping its root XOR trial
               leaves normal XOR trials enabled in baseline descendants.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_RecurseBody( Decpla_Dec_t * p, Decpla_Isf_t * f, int depth, word * support, int * vars, int nv, int fTryXor )
{
    word * masks = (word *)calloc(4*p->nw,sizeof(word));
    word scoreBest = 0, scores[2] = {0,0};
    int v, w, phase, result = -1, phaseBest = 0, directionBest = 0;
    size_t k;
    if ( !masks ) { p->failed = 1; return -1; }
    if ( fTryXor && !p->fXorTrial && (p->o.Features & 8) && nv <= 8 && depth <= 2 &&
         f->On.nCubes+f->Off.nCubes <= 64 && Gia_ManObjNum(p->g) <= 4096 &&
         (!p->outputs || Vec_IntSize(p->outputs) <= 512) ) {
        Decpla_Isf_t children[2];
        memset(children,0,sizeof(children));
        if ( Decpla_XorGroup(p,f,vars,nv,children) ) {
            Decpla_CacheState_t * state = Decpla_CacheSave(p);
            word random = p->random, baselineRandom;
            int baseline, trial = -1, l, r, a, b;
            if ( !state ) {
                Decpla_IsfFree(&children[0]); Decpla_IsfFree(&children[1]);
                goto no_xor_trial;
            }
            baseline = Decpla_RecurseBody(p,f,depth,support,vars,nv,0);
            baselineRandom = p->random; p->random = random;
            Decpla_CacheSwap(p,state);
            // The XOR children must not harvest the baseline's abandoned nodes.
            p->nextInternal = Gia_ManObjNum(p->g); p->fXorTrial = 1;
            l = Decpla_Recurse(p,&children[0],depth+1);
            r = l < 0 ? -1 : Decpla_Recurse(p,&children[1],depth+1);
            if ( l >= 0 && r >= 0 ) {
                a = Decpla_And(p,l,r^1); b = Decpla_And(p,l^1,r);
                trial = Decpla_And(p,a < 0 ? -1 : a^1,b < 0 ? -1 : b^1);
                if ( trial >= 0 ) trial ^= 1;
            }
            p->fXorTrial = 0; result = baseline;
            if ( baseline >= 0 && trial >= 0 && baseline != trial && Decpla_XorBetter(p,baseline,trial) ) {
                result = trial; ++p->stats.nXor;
            }
            if ( result == baseline ) { p->random = baselineRandom; Decpla_CacheSwap(p,state); }
            Decpla_CacheFree(state); p->nextInternal = Gia_ManObjNum(p->g);
        }
        Decpla_IsfFree(&children[0]); Decpla_IsfFree(&children[1]);
        if ( result >= 0 ) goto remember;
    }
no_xor_trial:
    {
        Decpla_Isf_t residual;
        int divisor, phase = 0, rest;
        memset(&residual,0,sizeof(residual));
        divisor = Decpla_Divisor(p,f,&residual,&phase);
        if ( divisor >= 0 ) {
            word random = p->random, baselineRandom;
            int baseline, trial, oldArea, newArea, i;
            Vec_Int_t * stack = Vec_IntAlloc(32);
            // A valid divisor may introduce inputs outside this ISF's support.
            for ( i = 0; i < p->nCache; ++i ) if ( (p->cache[i].lit>>1) == (divisor>>1) ) {
                for ( w = 0; w < p->nw; ++w ) support[w] |= p->cache[i].support[w];
                break;
            }
            // Compare both completions without nesting further divisor trials.
            p->fDivisorTrial = 1;
            baseline = Decpla_Recurse(p,f,depth);
            baselineRandom = p->random; p->random = random;
            // The ordinary completion also satisfies the residual; reusing
            // it here would hide useful, smaller residual completions.
            p->iSkipReuse = baseline < 0 ? 0 : baseline>>1;
            rest = Decpla_Recurse(p,&residual,depth+1);
            trial = Decpla_And(p,divisor^1,rest < 0 ? -1 : rest^1);
            p->iSkipReuse = 0;
            p->fDivisorTrial = 0;
            result = baseline;
            if ( baseline >= 0 && trial >= 0 ) {
                trial ^= !phase;
                Vec_IntFillExtra(p->shared,Gia_ManObjNum(p->g),0);
                oldArea = Decpla_ConeSize(p->g,baseline,stack,Vec_IntArray(p->shared));
                newArea = Decpla_ConeSize(p->g,trial,stack,Vec_IntArray(p->shared));
                Gia_ManLevelNum(p->g);
                if ( newArea < oldArea && Gia_ObjLevelId(p->g,trial>>1) <= Gia_ObjLevelId(p->g,baseline>>1)+2 ) {
                    result = trial; ++p->stats.nDivisor;
                }
            }
            if ( result == baseline ) p->random = baselineRandom;
            Vec_IntFree(stack);
        }
        Decpla_IsfFree(&residual);
        if ( divisor >= 0 ) goto remember;
    }
    for ( v = nv-1; v > 0; --v ) { int j = (int)Decpla_DecRandom(p,(unsigned)v+1), t = vars[v]; vars[v] = vars[j]; vars[j] = t; }
    if ( p->o.Features & 32 ) {
        result = Decpla_SmallBdc(p,f,vars,nv);
        if ( result >= 0 ) goto remember;
    }
    for ( phase = 0; phase < 2; ++phase ) {
        Decpla_Isf_t normalized = *f; word score;
        word * first = masks+2*phase*p->nw, * second = first+p->nw;
        if ( phase ) { normalized.On = f->Off; normalized.Off = f->On; }
        p->work = p->o.nWorkMax;
        score = Decpla_Group(p,&normalized,vars,nv,first,second);
        if ( !score && (p->o.Features & 1) ) {
            p->work = p->o.nWorkMax;
            score = Decpla_WeakGroup(p,&normalized,vars,nv,first,second);
        }
        scores[phase] = score;
        if ( score ) {
            int direction, nDirections = (p->o.Features & 2) && score > 1 ? 2 : 1;
            for ( direction = 0; direction < nDirections; ++direction ) {
                word * a = first + direction*p->nw, * b = first + (1-direction)*p->nw;
                word ranked = score;
                if ( p->o.Features & 2 ) ranked += (word)Decpla_PreviewReuse(p,&normalized,a,b) * ((word)nv*nv+nv+1);
                if ( ranked > scoreBest ) {
                    scoreBest = ranked; phaseBest = phase; directionBest = direction;
                }
            }
        }
    }
    if ( scoreBest ) {
        int choices[4], lits[4], count = 1, i, best = -1, bestArea = 0, bestLevel = 0;
        int savedTrial = p->fCompletionTrial;
        word random = p->random, endings[4];
        size_t cubes = f->On.nCubes + f->Off.nCubes;
        choices[0] = 2*phaseBest+directionBest;
        if ( !savedTrial && (cubes <= 16 || (depth <= 2 && cubes <= 128)) ) {
            for ( i = 0; i < 4; ++i )
                // Reversing a weak split gives a zero first component and no progress.
                if ( i != choices[0] && scores[i/2] && !(scores[i/2] == 1 && (i&1)) ) choices[count++] = i;
        }
        if ( count > 1 ) p->fCompletionTrial = 1;
        for ( i = 0; i < count; ++i ) {
            int choice = choices[i];
            const word * first = masks+2*(choice/2)*p->nw;
            p->random = random;
            lits[i] = Decpla_Complete(p,f,first+(choice&1)*p->nw,first+(!(choice&1))*p->nw,choice/2,scores[choice/2] == 1,depth);
            endings[i] = p->random;
        }
        p->fCompletionTrial = savedTrial;
        if ( count == 1 ) result = lits[0];
        else {
            Vec_Int_t * stack = Vec_IntAlloc(32);
            p->stats.nCompletionTrials += count;
            Vec_IntFillExtra(p->shared,Gia_ManObjNum(p->g),0);
            Gia_ManLevelNum(p->g);
            for ( i = 0; i < count; ++i ) if ( lits[i] >= 0 ) {
                int area = Decpla_ConeSize(p->g,lits[i],stack,Vec_IntArray(p->shared));
                int level = Gia_ObjLevelId(p->g,lits[i]>>1);
                if ( best < 0 || area < bestArea || (area == bestArea && level < bestLevel) ) {
                    best = i; bestArea = area; bestLevel = level;
                }
            }
            if ( best >= 0 ) {
                result = lits[best]; p->random = endings[best];
                p->stats.nCompletionChanges += best != 0;
            }
            Vec_IntFree(stack);
        }
        if ( result >= 0 ) goto remember;
    }
    if ( !p->failed && (p->o.Features & 8) ) {
        Decpla_Isf_t children[2]; int l = -1, r = -1;
        memset(children,0,sizeof(children));
        if ( Decpla_XorGroup(p,f,vars,nv,children) ) {
            l = Decpla_Recurse(p,&children[0],depth+1);
            if ( l >= 0 ) r = Decpla_Recurse(p,&children[1],depth+1);
        }
        Decpla_IsfFree(&children[0]); Decpla_IsfFree(&children[1]);
        if ( r >= 0 ) {
            int a = Decpla_And(p,l,r^1), b = Decpla_And(p,l^1,r);
            if ( a >= 0 && b >= 0 ) { result = Decpla_And(p,a^1,b^1); if ( result >= 0 ) result ^= 1; }
            ++p->stats.nXor; goto remember;
        }
    }
    // Every Shannon cofactor loses the selected variable, so recursion
    // terminates even if no AND/OR or XOR partition exists.
    if ( !p->failed ) {
        Decpla_Isf_t children[2];
        int best = Decpla_ShannonVar(f,vars,nv), branch, lits[2] = {-1,-1};
        word * tmp = (word *)malloc(p->nw*sizeof(word));
        memset(children,0,sizeof(children));
        if ( !tmp ) { p->failed = 1; goto done; }
        for ( branch = 0; branch < 2 && !p->failed; ++branch ) {
            for ( phase = 0; phase < 2 && !p->failed; ++phase ) {
                const Decpla_Cover_t * c = phase ? &f->On : &f->Off;
                Decpla_Cover_t * dst = phase ? &children[branch].On : &children[branch].Off;
                dst->nWords = p->nw;
                for ( k = 0; k < c->nCubes; ++k ) {
                    unsigned val = Decpla_CubeLit(c->pData+k*p->nw,best);
                    if ( val && val != (unsigned)branch+1 ) continue;
                    memcpy(tmp,c->pData+k*p->nw,p->nw*sizeof(word)); Decpla_CubeSet(tmp,best,0);
                    if ( !Decpla_CoverPush(dst,tmp) ) { p->failed = 1; break; }
                }
            }
            if ( !p->failed ) lits[branch] = Decpla_Recurse(p,&children[branch],depth+1);
        }
        free(tmp); Decpla_IsfFree(&children[0]); Decpla_IsfFree(&children[1]);
        if ( lits[0] >= 0 && lits[1] >= 0 ) {
            int a = Decpla_And(p,2*(best+1)^1,lits[0]), b = Decpla_And(p,2*(best+1),lits[1]);
            if ( a >= 0 && b >= 0 ) { result = Decpla_And(p,a^1,b^1); if ( result >= 0 ) result ^= 1; }
            ++p->stats.nMux;
        }
    }
remember:
done:
    free(masks); return result;
}
static int Decpla_ConeSize( Gia_Man_t * g, int lit, Vec_Int_t * stack, const int * shared )
{
    int size = 0;
    Gia_ManIncrementTravId(g); Vec_IntClear(stack); Vec_IntPush(stack,lit>>1);
    while ( Vec_IntSize(stack) ) {
        int id = Vec_IntPop(stack); Gia_Obj_t * obj = Gia_ManObj(g,id);
        if ( !Gia_ObjIsAnd(obj) || shared[id] || Gia_ObjIsTravIdCurrent(g,obj) ) continue;
        Gia_ObjSetTravIdCurrent(g,obj); ++size;
        Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
    }
    return size;
}

/**Function*************************************************************

  Synopsis    [Marks the nodes already needed by completed outputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Decpla_MarkShared( Decpla_Dec_t * p, int lit )
{
    Vec_Int_t * stack = Vec_IntAlloc(32);
    Vec_IntFillExtra(p->shared,Gia_ManObjNum(p->g),0);
    Vec_IntPush(stack,lit>>1);
    while ( Vec_IntSize(stack) ) {
        int id = Vec_IntPop(stack);
        Gia_Obj_t * obj = Gia_ManObj(p->g,id);
        if ( Vec_IntEntry(p->shared,id) ) continue;
        Vec_IntWriteEntry(p->shared,id,1);
        if ( Gia_ObjIsAnd(obj) ) {
            ++p->nCommitted;
            Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
        }
    }
    Vec_IntFree(stack);
}

/**Function*************************************************************

  Synopsis    [Counts the distinct ANDs reachable from a set of roots.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_OutputsArea( Gia_Man_t * g, Vec_Int_t * roots, Vec_Int_t * stack )
{
    int i, lit, area = 0;
    Gia_ManIncrementTravId(g); Vec_IntClear(stack);
    Vec_IntForEachEntry(roots,lit,i) Vec_IntPush(stack,lit>>1);
    while ( Vec_IntSize(stack) ) {
        int id = Vec_IntPop(stack);
        Gia_Obj_t * obj = Gia_ManObj(g,id);
        if ( !Gia_ObjIsAnd(obj) || Gia_ObjIsTravIdCurrent(g,obj) ) continue;
        Gia_ObjSetTravIdCurrent(g,obj); ++area;
        Vec_IntPush(stack,Gia_ObjFaninId0(obj,id));
        Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
    }
    return area;
}

/**Function*************************************************************

  Synopsis    [Checks that a shared factor fits the product's depth bound.]

  Description [Scale weights relative to the permitted level. Round tiny
               weights upward to avoid shifts by unbounded logic levels.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_FactorFits( Gia_Man_t * g, Vec_Int_t * row, int a, int b, int limit )
{
    word weight = 0;
    int i, lit, level = 1+Abc_MaxInt(Gia_ObjLevelId(g,a>>1),Gia_ObjLevelId(g,b>>1));
    if ( level > limit ) return 0;
    weight = (word)1 << Abc_MaxInt(0,32-(limit-level));
    Vec_IntForEachEntry(row,lit,i) if ( lit != a && lit != b ) {
        level = Gia_ObjLevelId(g,lit>>1);
        if ( level > limit ) return 0;
        weight += (word)1 << Abc_MaxInt(0,32-(limit-level));
    }
    return weight <= ((word)1 << 32);
}

/**Function*************************************************************

  Synopsis    [Propagates factored product replacements to all outputs.]

  Description [The explicit stack handles factors appended after their
               users. Copies stay in the shared hash table until the
               whole-graph area and depth comparison chooses a winner.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_FactorCopy( Decpla_Dec_t * p, Vec_Int_t * outputs, Vec_Int_t * replacements, Vec_Int_t * trial )
{
    int n = Gia_ManObjNum(p->g), i, lit, id, value, result = 0;
    Vec_Int_t * map = Vec_IntStartFull(n), * stack = Vec_IntAlloc(64);
    Gia_Obj_t * obj;
    Vec_IntWriteEntry(map,0,0);
    Gia_ManForEachCi(p->g,obj,i) Vec_IntWriteEntry(map,Gia_ObjId(p->g,obj),Gia_ObjId(p->g,obj)*2);
    Vec_IntForEachEntry(outputs,lit,i) {
        Vec_IntPush(stack,lit>>1);
        while ( Vec_IntSize(stack) ) {
            int entry = Vec_IntPop(stack), replacement = -1;
            id = entry < 0 ? ~entry : entry;
            if ( id < Vec_IntSize(replacements) ) replacement = Vec_IntEntry(replacements,id);
            if ( replacement == 2*id ) replacement = -1;
            obj = Gia_ManObj(p->g,id);
            if ( entry < 0 ) {
                if ( replacement >= 0 ) value = Vec_IntEntry(map,replacement>>1) ^ (replacement&1);
                else {
                    int a = Vec_IntEntry(map,Gia_ObjFaninId0(obj,id)) ^ Gia_ObjFaninC0(obj);
                    int b = Vec_IntEntry(map,Gia_ObjFaninId1(obj,id)) ^ Gia_ObjFaninC1(obj);
                    value = Decpla_And(p,a,b);
                }
                if ( value < 0 ) goto done;
                Vec_IntWriteEntry(map,id,value); continue;
            }
            value = Vec_IntEntry(map,id);
            if ( value == -2 ) goto done;
            if ( value >= 0 ) continue;
            Vec_IntWriteEntry(map,id,-2); Vec_IntPush(stack,~id);
            if ( replacement >= 0 ) Vec_IntPush(stack,replacement>>1);
            else {
                Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
            }
        }
        Vec_IntWriteEntry(trial,i,Vec_IntEntry(map,lit>>1) ^ (lit&1));
    }
    result = 1;
done:
    Vec_IntFree(map); Vec_IntFree(stack); return result;
}

/**Function*************************************************************

  Synopsis    [Factors common pairs in maximal uncomplemented AND trees.]

  Description [The trial preserves each output function. A bounded pair
               search is accepted only for lower total area and at most
               one additional level. Other output cones remain available.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Decpla_CubeFactors( Decpla_Dec_t * p, Vec_Int_t * outputs )
{
    Gia_Man_t * g = p->g;
    Vec_Wec_t * rows;
    Vec_Wrd_t * pairs;
    Vec_Int_t * stack, * trial, * limits, * roots, * refs, * boundary, * replacements, * changed;
    int i, j, k, lit, round, n = Gia_ManObjNum(g), budget = p->o.nWorkMax, oldDepth = 0, newDepth = 0, fChanged = 0;
    if ( !Vec_IntSize(outputs) || Vec_IntSize(outputs) > 512 ) return;
    rows = Vec_WecAlloc(128); pairs = Vec_WrdAlloc(256);
    stack = Vec_IntAlloc(64); trial = Vec_IntDup(outputs); limits = Vec_IntAlloc(128);
    roots = Vec_IntAlloc(128); refs = Vec_IntStart(n); boundary = Vec_IntStart(n);
    replacements = Vec_IntStartFull(n); changed = Vec_IntAlloc(128);
    Gia_ManLevelNum(g);
    Vec_IntForEachEntry(outputs,lit,i) {
        oldDepth = Abc_MaxInt(oldDepth,Gia_ObjLevelId(g,lit>>1));
        Vec_IntAddToEntry(refs,lit>>1,1); Vec_IntWriteEntry(boundary,lit>>1,1);
        Vec_IntPush(stack,lit>>1);
    }
    Gia_ManIncrementTravId(g);
    while ( Vec_IntSize(stack) ) {
        int id = Vec_IntPop(stack), a, b;
        Gia_Obj_t * obj = Gia_ManObj(g,id);
        if ( --budget < 0 ) goto done;
        if ( !Gia_ObjIsAnd(obj) || Gia_ObjIsTravIdCurrent(g,obj) ) continue;
        Gia_ObjSetTravIdCurrent(g,obj);
        a = Gia_ObjFaninId0(obj,id); b = Gia_ObjFaninId1(obj,id);
        Vec_IntAddToEntry(refs,a,1); Vec_IntAddToEntry(refs,b,1);
        if ( Gia_ObjFaninC0(obj) ) Vec_IntWriteEntry(boundary,a,1);
        if ( Gia_ObjFaninC1(obj) ) Vec_IntWriteEntry(boundary,b,1);
        Vec_IntPush(stack,a); Vec_IntPush(stack,b);
    }
    for ( i = 1; i < n; ++i ) {
        Vec_Int_t * row;
        int valid = 1;
        if ( !Vec_IntEntry(refs,i) || !Vec_IntEntry(boundary,i) || !Gia_ObjIsAnd(Gia_ManObj(g,i)) ) continue;
        row = Vec_WecPushLevel(rows);
        Gia_ManIncrementTravId(g); Vec_IntClear(stack); Vec_IntPush(stack,2*i);
        while ( Vec_IntSize(stack) && valid ) {
            int edge = Vec_IntPop(stack), id = edge>>1;
            Gia_Obj_t * obj = Gia_ManObj(g,id);
            if ( --budget < 0 ) goto done;
            if ( !Gia_ObjIsAnd(obj) || (edge&1) ) {
                Vec_IntPushUnique(row,edge);
                if ( Vec_IntSize(row) > 32 ) valid = 0;
            } else if ( !Gia_ObjIsTravIdCurrent(g,obj) ) {
                Gia_ObjSetTravIdCurrent(g,obj);
                Vec_IntPush(stack,Gia_ObjFaninLit0p(g,obj));
                Vec_IntPush(stack,Gia_ObjFaninLit1p(g,obj));
            }
        }
        Vec_IntPush(roots,i); Vec_IntPush(limits,Gia_ObjLevelId(g,i)+1); Vec_IntPush(changed,0);
        if ( !valid || Vec_IntSize(row) < 2 ) { Vec_IntClear(row); continue; }
        Vec_IntSort(row,0);
        for ( j = 1; j < Vec_IntSize(row); ++j )
            if ( (Vec_IntEntry(row,j)>>1) == (Vec_IntEntry(row,j-1)>>1) ) valid = 0;
        if ( !valid ) { Vec_IntClear(row); continue; }
    }
    if ( Vec_WecSize(rows) < 2 ) goto done;
    for ( round = 0; round < 64; ++round ) {
        word best = 0;
        int bestCount = 1;
        Vec_WrdClear(pairs);
        for ( i = 0; i < Vec_WecSize(rows); ++i ) {
            Vec_Int_t * row = Vec_WecEntry(rows,i);
            for ( j = 0; j < Vec_IntSize(row); ++j ) for ( k = j+1; k < Vec_IntSize(row); ++k ) {
                int a = Vec_IntEntry(row,j), b = Vec_IntEntry(row,k);
                if ( --budget < 0 ) goto assemble;
                if ( Decpla_FactorFits(g,row,a,b,Vec_IntEntry(limits,i)) )
                    Vec_WrdPush(pairs,((word)Abc_MinInt(a,b)<<32) | (unsigned)Abc_MaxInt(a,b));
            }
        }
        Vec_WrdSortUnsigned(pairs);
        for ( j = 0; j < Vec_WrdSize(pairs); j = k ) {
            for ( k = j+1; k < Vec_WrdSize(pairs) && Vec_WrdEntry(pairs,j) == Vec_WrdEntry(pairs,k); ++k ) {}
            if ( k-j > bestCount ) { bestCount = k-j; best = Vec_WrdEntry(pairs,j); }
        }
        if ( !best ) break;
        {
            int a = (int)(best>>32), b = (int)(unsigned)best;
            int combined = Decpla_And(p,a,b);
            if ( combined < 0 ) goto done;
            Gia_ObjSetLevelId(g,combined>>1,1+Abc_MaxInt(Gia_ObjLevelId(g,a>>1),Gia_ObjLevelId(g,b>>1)));
            for ( i = 0; i < Vec_WecSize(rows); ++i ) {
                Vec_Int_t * row = Vec_WecEntry(rows,i);
                int ia = Vec_IntFind(row,a), ib = Vec_IntFind(row,b);
                if ( ia < 0 || ib < 0 || !Decpla_FactorFits(g,row,a,b,Vec_IntEntry(limits,i)) ) continue;
                Vec_IntWriteEntry(row,ia,combined);
                Vec_IntDrop(row,ib);
                Vec_IntWriteEntry(changed,i,1); fChanged = 1;
            }
        }
    }
assemble:
    if ( !fChanged ) goto done;
    for ( i = 0; i < Vec_WecSize(rows); ++i ) {
        Vec_Int_t * row = Vec_WecEntry(rows,i);
        // Preserve the original tree and its sharing unless a factor changed it.
        if ( !Vec_IntEntry(changed,i) ) continue;
        while ( Vec_IntSize(row) > 1 ) {
            int a, b, combined;
            for ( j = 0; j < 2; ++j ) for ( k = j+1; k < Vec_IntSize(row); ++k )
                if ( Gia_ObjLevelId(g,Vec_IntEntry(row,k)>>1) < Gia_ObjLevelId(g,Vec_IntEntry(row,j)>>1) ) {
                    int swap = Vec_IntEntry(row,j);
                    Vec_IntWriteEntry(row,j,Vec_IntEntry(row,k)); Vec_IntWriteEntry(row,k,swap);
                }
            a = Vec_IntEntry(row,0); b = Vec_IntEntry(row,1); combined = Decpla_And(p,a,b);
            if ( combined < 0 ) goto done;
            Gia_ObjSetLevelId(g,combined>>1,1+Abc_MaxInt(Gia_ObjLevelId(g,a>>1),Gia_ObjLevelId(g,b>>1)));
            Vec_IntWriteEntry(row,0,combined); Vec_IntDrop(row,1);
        }
        Vec_IntWriteEntry(replacements,Vec_IntEntry(roots,i),Vec_IntEntry(row,0));
    }
    if ( !Decpla_FactorCopy(p,outputs,replacements,trial) ) goto done;
    Gia_ManLevelNum(g);
    Vec_IntForEachEntry(trial,lit,i) newDepth = Abc_MaxInt(newDepth,Gia_ObjLevelId(g,lit>>1));
    if ( newDepth <= oldDepth+1 && Decpla_OutputsArea(g,trial,stack) < Decpla_OutputsArea(g,outputs,stack) )
        Vec_IntForEachEntry(trial,lit,i) Vec_IntWriteEntry(outputs,i,lit);
done:
    Vec_WecFree(rows); Vec_WrdFree(pairs); Vec_IntFree(stack); Vec_IntFree(trial); Vec_IntFree(limits);
    Vec_IntFree(roots); Vec_IntFree(refs); Vec_IntFree(boundary); Vec_IntFree(replacements); Vec_IntFree(changed);
}

// Revisit roots after all cones exist. Targeted care-point simulation rejects
// most divisors cheaply, but never accepts one: every surviving replacement
// must satisfy every original cube by an exact proof. Bounded to small AIGs
// and eight candidate proofs per output. The caller retains the old solution
// if the cleaned global area increases.
static void Decpla_ResubRoots( Decpla_Dec_t * p, const Decpla_Man_t * source, Vec_Int_t * outputs )
{
    int i, id, phase, sample, v, n = Gia_ManObjNum(p->g);
    word * sim; int * shared; Vec_Int_t * stack;
    if ( n > 8192 ) return;
    sim = (word *)malloc(n*sizeof(word)); shared = (int *)calloc(n,sizeof(int)); stack = Vec_IntAlloc(32);
    if ( !sim || !shared ) { free(sim); free(shared); Vec_IntFree(stack); return; }
    for ( i = 0; i < source->nOutputs; ++i ) {
        const Decpla_Isf_t * f = &source->pIsfs[i]; word wanted = 0;
        int best = Vec_IntEntry(outputs,i), tried = 0;
        if ( !f->On.nCubes || !f->Off.nCubes ) continue;
        // Cost only nodes not already needed by the other outputs.
        memset(shared,0,n*sizeof(int)); Vec_IntClear(stack);
        for ( v = 0; v < Vec_IntSize(outputs); ++v ) if ( v != i ) Vec_IntPush(stack,Vec_IntEntry(outputs,v)>>1);
        while ( Vec_IntSize(stack) ) {
            Gia_Obj_t * obj;
            id = Vec_IntPop(stack); obj = Gia_ManObj(p->g,id);
            if ( shared[id] ) continue;
            shared[id] = 1;
            if ( Gia_ObjIsAnd(obj) ) {
                Vec_IntPush(stack,Gia_ObjFaninId0(obj,id)); Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
            }
        }
        memset(sim,0,n*sizeof(word));
        for ( sample = 0; sample < 64; ++sample ) {
            const Decpla_Cover_t * c = (sample&1) ? &f->On : &f->Off;
            const word * cube = c->pData + ((size_t)(sample/2)*c->nCubes/32)*p->nw;
            word bit = (word)1 << sample;
            if ( sample&1 ) wanted |= bit;
            for ( v = 0; v < p->ni; ++v ) {
                unsigned value = Decpla_CubeLit(cube,v);
                if ( value == 2 || (!value && Decpla_DecRandom(p,2)) ) sim[v+1] |= bit;
            }
        }
        for ( id = p->ni+1; id < n; ++id ) {
            Gia_Obj_t * obj = Gia_ManObj(p->g,id);
            word a = sim[Gia_ObjFaninId0(obj,id)], b = sim[Gia_ObjFaninId1(obj,id)];
            sim[id] = (Gia_ObjFaninC0(obj) ? ~a : a) & (Gia_ObjFaninC1(obj) ? ~b : b);
        }
        // Small cones first, so successful replacements do not chase a
        // sequence of slightly smaller, expensive candidates.
        while ( tried < 8 ) {
            int candidate = -1, minSize = Decpla_ConeSize(p->g,best,stack,shared), ok = 1;
            for ( id = 0; id < n; ++id ) if ( sim[id] == wanted || ~sim[id] == wanted ) {
                int size = Decpla_ConeSize(p->g,2*id,stack,shared);
                if ( size < minSize ) { candidate = 2*id + (sim[id] != wanted); minSize = size; }
            }
            if ( candidate < 0 ) break;
            ++tried;
            for ( phase = 0; phase < 2 && ok; ++phase ) {
                const Decpla_Cover_t * c = phase ? &f->On : &f->Off; size_t k;
                for ( k = 0; k < c->nCubes; ++k )
                    if ( Decpla_CubeProve(p->sat,c->pData+k*p->nw,candidate,phase,100) != 1 ) { ok = 0; break; }
            }
            if ( ok ) { best = candidate; ++p->stats.nReuse; break; }
            // Invalidate this signature for this output only.
            sim[candidate>>1] = wanted ^ ABC_CONST(1);
        }
        Vec_IntWriteEntry(outputs,i,best);
    }
    free(sim); free(shared); Vec_IntFree(stack);
}
/**Function*************************************************************

  Synopsis    [Copies an AIG with one internal signal replaced.]

  Description [An explicit DFS stack permits a divisor later in the old
               topological order. An active-node mark rejects cycles.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Decpla_ResubCopy( Gia_Man_t * g, int root, int divisor )
{
    Gia_Man_t * copy = Gia_ManStart(Gia_ManObjNum(g)), * clean = NULL;
    Vec_Int_t * stack = Vec_IntAlloc(64);
    Gia_Obj_t * obj;
    int i, id;
    copy->pName = Abc_UtilStrsav(g->pName); copy->pSpec = Abc_UtilStrsav(g->pSpec);
    Gia_ManHashStart(copy); Gia_ManFillValue(g); Gia_ManConst0(g)->Value = 0;
    Gia_ManForEachCi(g,obj,i) obj->Value = Gia_ManAppendCi(copy);
    Gia_ManForEachCo(g,obj,i) {
        Vec_IntPush(stack,Gia_ObjFaninId0p(g,obj));
        while ( Vec_IntSize(stack) ) {
            int entry = Vec_IntPop(stack);
            id = entry < 0 ? ~entry : entry; obj = Gia_ManObj(g,id);
            if ( entry < 0 ) {
                if ( id == root ) obj->Value = Gia_ManObj(g,divisor>>1)->Value ^ (divisor&1);
                else obj->Value = Gia_ManHashAnd(copy,Gia_ObjFanin0Copy(obj),Gia_ObjFanin1Copy(obj));
                continue;
            }
            if ( obj->Value == ~1u ) goto done;
            if ( obj->Value != ~0u ) continue;
            obj->Value = ~1u; Vec_IntPush(stack,~id);
            if ( id == root ) Vec_IntPush(stack,divisor>>1);
            else {
                assert(Gia_ObjIsAnd(obj));
                Vec_IntPush(stack,Gia_ObjFaninId0(obj,id));
                Vec_IntPush(stack,Gia_ObjFaninId1(obj,id));
            }
        }
    }
    Gia_ManForEachCo(g,obj,i) Gia_ManAppendCo(copy,Gia_ObjFanin0Copy(obj));
    clean = Gia_ManCleanup(copy);
    // Keep a map into the final graph for the unvisited resubstitution roots.
    Gia_ManForEachObj(g,obj,i) if ( obj->Value != ~0u ) {
        unsigned value = Gia_ManObj(copy,obj->Value>>1)->Value;
        obj->Value = value == ~0u ? ~0u : value ^ (obj->Value&1);
    }
done:
    Gia_ManStop(copy); Vec_IntFree(stack); return clean;
}

/**Function*************************************************************

  Synopsis    [Proves all original cubes at outputs affected by a trial.]

  Description [Unaffected cones retain their previous proof. Every trial
               has a fresh solver; timeout or work exhaustion rejects it.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_ResubCheck( Decpla_Dec_t * p, const Decpla_Man_t * source, Gia_Man_t * old, Gia_Man_t * trial )
{
    Decpla_Sat_t * sat = Decpla_SatStart(trial);
    int i, phase, ok = sat != NULL;
    for ( i = 0; i < source->nOutputs && ok; ++i ) {
        int lit, cost;
        if ( !Gia_ObjIsTravIdCurrent(old,Gia_ManCo(old,i)) ) continue;
        lit = Gia_ObjFaninLit0p(trial,Gia_ManCo(trial,i));
        cost = Decpla_ConePrepare(sat,lit);
        if ( cost < 0 ) { ok = 0; break; }
        for ( phase = 0; phase < 2 && ok; ++phase ) {
            const Decpla_Cover_t * c = phase ? &source->pIsfs[i].On : &source->pIsfs[i].Off;
            size_t k;
            for ( k = 0; k < c->nCubes; ++k )
                if ( !Decpla_Work(p,cost) ||
                     Decpla_CubeProve(sat,c->pData+k*c->nWords,lit,phase,Abc_MinInt(100,p->o.nConfLimit)) != 1 ) {
                    ok = 0; break;
                }
        }
    }
    Decpla_SatStop(sat); return ok;
}

/**Function*************************************************************

  Synopsis    [Counts two-input AND/XOR gates in a completed AIG.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_ResubArea( Gia_Man_t * g )
{
    Gia_Man_t * xag = Gia_ManDupMuxes(g,1);
    int area = Gia_ManAndNum(xag);
    Gia_ManStop(xag); return area;
}

/**Function*************************************************************

  Synopsis    [Ranks resubstitution roots by removable cone size.]

  Description [Iterative dereferencing measures MFFCs within the search
               work budget, then restores all references. Larger cones
               come first, with higher node IDs breaking ties.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Decpla_ResubOrder( Decpla_Dec_t * p, Gia_Man_t * g )
{
    Vec_Int_t * roots = Vec_IntAlloc(128), * cone = Vec_IntAlloc(64);
    Vec_Wrd_t * order = Vec_WrdAlloc(128);
    int * refs = (int *)calloc(Gia_ManObjNum(g),sizeof(int));
    Gia_Obj_t * obj;
    int root, id, i, j, fanin;
    if ( !refs ) goto done;
    Gia_ManForEachObj(g,obj,id) {
        if ( Gia_ObjIsAnd(obj) || Gia_ObjIsCo(obj) ) ++refs[Gia_ObjFaninId0(obj,id)];
        if ( Gia_ObjIsAnd(obj) ) ++refs[Gia_ObjFaninId1(obj,id)];
    }
    for ( root = Gia_ManObjNum(g)-1; root > 0 && p->work; --root ) {
        if ( !Gia_ObjIsAnd(Gia_ManObj(g,root)) ) continue;
        Vec_IntClear(cone); Vec_IntPush(cone,root);
        for ( i = 0; i < Vec_IntSize(cone) && Decpla_Work(p,1); ++i ) {
            id = Vec_IntEntry(cone,i); obj = Gia_ManObj(g,id);
            fanin = Gia_ObjFaninId0(obj,id);
            if ( --refs[fanin] == 0 && Gia_ObjIsAnd(Gia_ManObj(g,fanin)) ) Vec_IntPush(cone,fanin);
            fanin = Gia_ObjFaninId1(obj,id);
            if ( --refs[fanin] == 0 && Gia_ObjIsAnd(Gia_ManObj(g,fanin)) ) Vec_IntPush(cone,fanin);
        }
        for ( j = 0; j < i; ++j ) {
            id = Vec_IntEntry(cone,j); obj = Gia_ManObj(g,id);
            ++refs[Gia_ObjFaninId0(obj,id)]; ++refs[Gia_ObjFaninId1(obj,id)];
        }
        if ( i == Vec_IntSize(cone) ) Vec_WrdPush(order,((word)i<<32) | (unsigned)root);
    }
    Vec_WrdSortUnsigned(order);
    for ( i = Vec_WrdSize(order)-1; i >= 0; --i ) Vec_IntPush(roots,(int)(unsigned)Vec_WrdEntry(order,i));
done:
    free(refs); Vec_IntFree(cone); Vec_WrdFree(order); return roots;
}

/**Function*************************************************************

  Synopsis    [Resubstitutes internal nodes using the original PLA care.]

  Description [One word of sampled care points per output filters divisors.
               Flipping the root computes exact observability on these
               points, including reconvergence. Only a full cube proof
               permits acceptance. Each accepted trial is a smaller AIG
               with no more AND/XOR gates and at most one extra level.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Decpla_ResubInternal( Decpla_Dec_t * p, const Decpla_Man_t * source, Gia_Man_t * g )
{
    Vec_Int_t * roots;
    int initialDepth, area, restart = 1, visited = 0, position = 0, no = source->nOutputs;
    if ( !Gia_ManAndNum(g) || Gia_ManObjNum(g) > 20000 || no > 128 ) return g;
    initialDepth = Gia_ManLevelNum(g); area = Decpla_ResubArea(g);
    p->work = p->o.nWorkMax > INT_MAX/64 ? INT_MAX : 64*p->o.nWorkMax;
    roots = Decpla_ResubOrder(p,g);
    while ( restart && p->work && p->nResubTrials < 512 && p->nResubChanges < 64 && visited < 4096 && position < Vec_IntSize(roots) ) {
        int n = Gia_ManObjNum(g), i, j, id, w, root, sample;
        word * sim = (word *)calloc((size_t)n*no,sizeof(word));
        word * flip = (word *)malloc((size_t)n*no*sizeof(word));
        word * mask = (word *)malloc(no*sizeof(word));
        Vec_Int_t * tfo = Vec_IntAlloc(64);
        Vec_Wrd_t * candidates = Vec_WrdAlloc(n);
        Gia_Obj_t * obj;
        restart = 0;
        if ( !sim || !flip || !mask || !Decpla_Work(p,n*no) ) {
            free(sim); free(flip); free(mask); Vec_IntFree(tfo); Vec_WrdFree(candidates); break;
        }
        Gia_ManForEachObj(g,obj,id) if ( !Gia_ObjIsCo(obj) )
            Vec_WrdPush(candidates,((word)Gia_ObjLevelId(g,id)<<32) | (unsigned)id);
        Vec_WrdSortUnsigned(candidates);
        for ( i = 0; i < no; ++i ) for ( sample = 0; sample < 64; ++sample ) {
            const Decpla_Isf_t * f = source->pIsfs+i;
            const Decpla_Cover_t * c = (sample&1) ? &f->On : &f->Off;
            const word * cube;
            if ( !c->nCubes ) c = c == &f->On ? &f->Off : &f->On;
            if ( !c->nCubes ) continue;
            cube = c->pData+((size_t)(sample/2)*c->nCubes/32)*c->nWords;
            Gia_ManForEachCi(g,obj,j) {
                unsigned value = Decpla_CubeLit(cube,j);
                if ( value == 2 || (!value && Decpla_DecRandom(p,2)) )
                    sim[(size_t)Gia_ObjId(g,obj)*no+i] |= (word)1 << sample;
            }
        }
        Gia_ManForEachAnd(g,obj,id) for ( w = 0; w < no; ++w ) {
            word a = sim[(size_t)Gia_ObjFaninId0(obj,id)*no+w];
            word b = sim[(size_t)Gia_ObjFaninId1(obj,id)*no+w];
            sim[(size_t)id*no+w] = (Gia_ObjFaninC0(obj) ? ~a : a) & (Gia_ObjFaninC1(obj) ? ~b : b);
        }
        Gia_ManStaticFanoutStart(g);
        while ( position < Vec_IntSize(roots) && p->work && !restart && p->nResubTrials < 512 && visited < 4096 ) {
            int tried = 0, divisor, c;
            root = Vec_IntEntry(roots,position++);
            if ( root < 0 ) continue;
            if ( !Gia_ObjIsAnd(Gia_ManObj(g,root)) ) continue;
            ++visited; Gia_ManIncrementTravId(g); Gia_ObjSetTravIdCurrentId(g,root);
            Vec_IntClear(tfo); Vec_IntPush(tfo,root);
            for ( i = 0; i < Vec_IntSize(tfo); ++i ) {
                int fanout;
                id = Vec_IntEntry(tfo,i);
                Gia_ObjForEachFanoutStaticId(g,id,fanout,j)
                    if ( !Gia_ObjIsTravIdCurrentId(g,fanout) ) {
                        Gia_ObjSetTravIdCurrentId(g,fanout); Vec_IntPush(tfo,fanout);
                    }
            }
            if ( !Decpla_Work(p,Vec_IntSize(tfo)*no) ) break;
            Vec_IntSort(tfo,0); memset(mask,0,no*sizeof(word));
            for ( w = 0; w < no; ++w ) flip[(size_t)root*no+w] = ~sim[(size_t)root*no+w];
            Vec_IntForEachEntry(tfo,id,i) {
                if ( id == root ) continue;
                obj = Gia_ManObj(g,id);
                if ( Gia_ObjIsCo(obj) ) {
                    int ci = Gia_ObjCioId(obj), fanin = Gia_ObjFaninId0(obj,id);
                    if ( source->pIsfs[ci].On.nCubes || source->pIsfs[ci].Off.nCubes )
                        mask[ci] = sim[(size_t)fanin*no+ci] ^ flip[(size_t)fanin*no+ci];
                } else for ( w = 0; w < no; ++w ) {
                    int aId = Gia_ObjFaninId0(obj,id), bId = Gia_ObjFaninId1(obj,id);
                    word a = (Gia_ObjIsTravIdCurrentId(g,aId) ? flip : sim)[(size_t)aId*no+w];
                    word b = (Gia_ObjIsTravIdCurrentId(g,bId) ? flip : sim)[(size_t)bId*no+w];
                    flip[(size_t)id*no+w] = (Gia_ObjFaninC0(obj) ? ~a : a) & (Gia_ObjFaninC1(obj) ? ~b : b);
                }
            }
            for ( c = 0; c < 2*Vec_WrdSize(candidates) && tried < 8 && p->work && p->nResubTrials < 512; ++c ) {
                Gia_Man_t * trial;
                int candidate = (int)(unsigned)Vec_WrdEntry(candidates,c/2), trialArea;
                word phase = (c&1) ? ~(word)0 : 0;
                divisor = 2*candidate+(c&1);
                if ( Gia_ObjLevelId(g,candidate) > Gia_ObjLevelId(g,root)+1 ) break;
                if ( Gia_ObjIsTravIdCurrentId(g,candidate) ) continue;
                if ( !Decpla_Work(p,no) ) break;
                for ( w = 0; w < no; ++w )
                    if ( (sim[(size_t)candidate*no+w] ^ phase ^ sim[(size_t)root*no+w]) & mask[w] ) break;
                if ( w < no ) continue;
                if ( !Decpla_Work(p,n) ) break;
                ++tried; ++p->nResubTrials;
                trial = Decpla_ResubCopy(g,root,divisor);
                if ( !trial ) continue;
                trialArea = Decpla_ResubArea(trial);
                if ( Gia_ManAndNum(trial) < Gia_ManAndNum(g) && trialArea <= area &&
                     Gia_ManLevelNum(trial) <= initialDepth+1 && Decpla_ResubCheck(p,source,g,trial) ) {
                    // Map every pending root once; skip deleted or merged roots.
                    Gia_ManIncrementTravId(trial);
                    for ( i = 0; i < Vec_IntSize(roots); ++i ) {
                        int old = Vec_IntEntry(roots,i), mapped = -1;
                        if ( old >= 0 && Gia_ManObj(g,old)->Value != ~0u ) {
                            id = Gia_ManObj(g,old)->Value>>1;
                            if ( !Gia_ObjIsTravIdCurrentId(trial,id) ) {
                                Gia_ObjSetTravIdCurrentId(trial,id); mapped = id;
                            }
                        }
                        Vec_IntWriteEntry(roots,i,mapped);
                    }
                    Gia_ManStaticFanoutStop(g); Gia_ManStop(g); g = trial; area = trialArea;
                    ++p->nResubChanges; restart = 1; break;
                }
                Gia_ManStop(trial);
            }
        }
        if ( !restart ) Gia_ManStaticFanoutStop(g);
        free(sim); free(flip); free(mask); Vec_IntFree(tfo); Vec_WrdFree(candidates);
    }
    Vec_IntFree(roots);
    return g;
}

/**Function*************************************************************

  Synopsis    [Collects one bit per input occurring in either cover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Decpla_SupportMask( const Decpla_Isf_t * f, word * mask, int nw )
{
    int phase, w;
    size_t k;
    memset(mask,0,nw*sizeof(word));
    for ( phase = 0; phase < 2; ++phase ) {
        const Decpla_Cover_t * c = phase ? &f->On : &f->Off;
        for ( k = 0; k < c->nCubes; ++k ) for ( w = 0; w < nw; ++w )
            mask[w] |= c->pData[k*nw+w];
    }
    for ( w = 0; w < nw; ++w )
        mask[w] = (mask[w] | (mask[w]>>1)) & ABC_CONST(0x5555555555555555);
}

/**Function*************************************************************

  Synopsis    [Compares four support choices for a bounded output problem.]

  Description [Compare weighted selection with input deletion in forward,
               reverse and seeded shuffled orders. Each trial starts with
               identical graphs, caches, counters and grouping random states.
               The original output index diversifies shuffled deletion.
               Keep only the chosen graph. Additional area excludes nodes
               already used by completed outputs; allow two extra levels
               relative to the original weighted result.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Decpla_ChooseSupport( Decpla_Dec_t * p, Decpla_Isf_t * f, int iOutput )
{
    Decpla_Isf_t original, alternative;
    Decpla_Man_t local;
    Decpla_CacheState_t * initial;
    Decpla_Stats_t initialStats = p->stats;
    Gia_Man_t * prefix = NULL;
    Vec_Int_t * stack;
    word masks[4][8], random = p->random;
    int order[256], choice, j, result, bestArea, bestLevel, maxLevel, changed = 0;
    if ( p->o.fBaseline || p->ni > 256 || f->On.nCubes+f->Off.nCubes > 2048 ||
         !f->On.nCubes || !f->Off.nCubes || Gia_ManObjNum(p->g) > 8192 )
        return Decpla_Recurse(p,f,0);
    memset(&original,0,sizeof(original));
    if ( !Decpla_Copy(&original.On,&f->On) || !Decpla_Copy(&original.Off,&f->Off) ) {
        Decpla_IsfFree(&original); return Decpla_Recurse(p,f,0);
    }
    initial = Decpla_CacheSave(p);
    if ( initial ) prefix = Gia_ManDup(p->g);
    result = Decpla_Recurse(p,f,0);
    if ( !prefix || result < 0 || p->failed ) goto done;
    Decpla_SupportMask(f,masks[0],p->nw);
    stack = Vec_IntAlloc(32);
    Vec_IntFillExtra(p->shared,Gia_ManObjNum(p->g),0);
    bestArea = Decpla_ConeSize(p->g,result,stack,Vec_IntArray(p->shared));
    // Avoid three more decompositions when at most one new AND can be saved.
    if ( bestArea <= 1 ) { Vec_IntFree(stack); goto done; }
    Gia_ManLevelNum(p->g); bestLevel = Gia_ObjLevelId(p->g,result>>1); maxLevel = bestLevel+2;
    for ( choice = 1; choice < 4; ++choice ) {
        Decpla_CacheState_t * state;
        Decpla_Stats_t bestStats = p->stats;
        Gia_Man_t * other, * swapGraph;
        Decpla_Sat_t * otherSat, * swapSat;
        word bestRandom = p->random;
        int trial, trialArea, trialLevel, bestWork = p->work, accept = 0;
        memset(&alternative,0,sizeof(alternative));
        if ( !Decpla_Copy(&alternative.On,&original.On) || !Decpla_Copy(&alternative.Off,&original.Off) ) {
            Decpla_IsfFree(&alternative); break;
        }
        for ( j = 0; j < p->ni; ++j ) order[j] = choice == 2 ? p->ni-1-j : j;
        if ( choice == 3 ) {
            p->random = p->o.Seed ^ ((word)iOutput * ABC_CONST(0x9e3779b97f4a7c15));
            for ( j = p->ni-1; j > 0; --j ) {
                int k = (int)Decpla_DecRandom(p,(unsigned)j+1), swap = order[j];
                order[j] = order[k]; order[k] = swap;
            }
            p->random = bestRandom;
        }
        memset(&local,0,sizeof(local));
        local.nInputs = p->ni; local.nOutputs = 1; local.pIsfs = &alternative;
        if ( !Decpla_MinimizeOrder(&local,order,p->err) ) { Decpla_IsfFree(&alternative); break; }
        Decpla_SupportMask(&alternative,masks[choice],p->nw);
        for ( j = 0; j < choice; ++j )
            if ( !memcmp(masks[j],masks[choice],p->nw*sizeof(word)) ) break;
        if ( j < choice ) { Decpla_IsfFree(&alternative); continue; }
        state = Decpla_CacheCopy(initial->cache,initial->nCache,p->nw,initial->nextInternal,initial->nInternal);
        if ( !state ) { Decpla_IsfFree(&alternative); break; }
        other = Gia_ManDup(prefix); Gia_ManHashStart(other);
        otherSat = Decpla_SatStart(other);
        if ( !otherSat ) { Gia_ManStop(other); Decpla_CacheFree(state); Decpla_IsfFree(&alternative); break; }
        ++p->nSupportTrials; Decpla_CacheSwap(p,state);
        swapGraph = p->g; p->g = other; other = swapGraph;
        swapSat = p->sat; p->sat = otherSat; otherSat = swapSat;
        p->random = random; p->stats = initialStats;
        trial = Decpla_Recurse(p,&alternative,0);
        Vec_IntFillExtra(p->shared,Gia_ManObjNum(p->g),0);
        if ( trial >= 0 && !p->failed ) {
            trialArea = Decpla_ConeSize(p->g,trial,stack,Vec_IntArray(p->shared));
            Gia_ManLevelNum(p->g); trialLevel = Gia_ObjLevelId(p->g,trial>>1);
            if ( trialArea <= p->o.nNodesMax-p->nCommitted && trialLevel <= maxLevel &&
                 (trialArea < bestArea || (trialArea == bestArea && trialLevel < bestLevel)) ) {
                result = trial; bestArea = trialArea; bestLevel = trialLevel; accept = changed = 1;
            }
        }
        if ( !accept ) {
            Decpla_CacheSwap(p,state); p->random = bestRandom; p->work = bestWork; p->stats = bestStats;
            swapGraph = p->g; p->g = other; other = swapGraph;
            swapSat = p->sat; p->sat = otherSat; otherSat = swapSat;
            p->failed = 0; // Failure of an optional trial leaves a valid result.
        }
        Decpla_SatStop(otherSat); Gia_ManStop(other); Decpla_CacheFree(state);
        Decpla_IsfFree(&alternative);
    }
    p->nSupportChanges += changed;
    Vec_IntFree(stack);
done:
    if ( prefix ) Gia_ManStop(prefix);
    if ( initial ) Decpla_CacheFree(initial);
    Decpla_IsfFree(&original); return result;
}

typedef struct Decpla_Order_t_ { int index, size; } Decpla_Order_t;
static int Decpla_OrderSmall( const void * a, const void * b )
{
    const Decpla_Order_t * x = (const Decpla_Order_t *)a, * y = (const Decpla_Order_t *)b;
    return x->size != y->size ? (x->size > y->size ? 1 : -1) : (x->index > y->index) - (x->index < y->index);
}
static int Decpla_OrderLarge( const void * a, const void * b )
{
    const Decpla_Order_t * x = (const Decpla_Order_t *)a, * y = (const Decpla_Order_t *)b;
    return x->size != y->size ? (x->size < y->size ? 1 : -1) : (x->index > y->index) - (x->index < y->index);
}
Gia_Man_t * Decpla_Decompose( const Decpla_Man_t * source, const Decpla_Options_t * options, FILE * out, FILE * err )
{
    Decpla_Dec_t p; Gia_Man_t * result = NULL;
    Vec_Int_t * outputs, * order; int i;
    abctime start = Abc_Clock();
    memset(&p,0,sizeof(p)); p.o = *options; p.ni = source->nInputs; p.nw = (p.ni+31)/32;
    p.random = options->Seed; p.err = err;
    if ( p.o.nCubesMax < 1 || p.o.nWorkMax < 1 || p.o.nNodesMax < 1 || p.o.nConfLimit < 1 || options->OutputOrder < 0 || options->OutputOrder > 3 || !Decpla_Check(source,err) ) return NULL;
    p.g = Gia_ManStart(1024); Gia_ManHashStart(p.g);
    for ( i = 0; i < p.ni; ++i ) Gia_ManAppendCi(p.g);
    p.sat = Decpla_SatStart(p.g); p.shared = Vec_IntAlloc(32); outputs = Vec_IntStart(source->nOutputs);
    p.outputs = outputs;
    order = Vec_IntStartNatural(source->nOutputs);
    if ( options->OutputOrder == 1 || options->OutputOrder == 2 ) {
        Decpla_Order_t * ranks = (Decpla_Order_t *)malloc(source->nOutputs*sizeof(Decpla_Order_t));
        Decpla_Options_t singleOptions = *options;
        singleOptions.OutputOrder = 0;
        if ( !ranks ) p.failed = 1;
        for ( i = 0; ranks && i < source->nOutputs; ++i ) {
            Decpla_Man_t single = *source; Gia_Man_t * g;
            single.nOutputs = 1; single.pIsfs = source->pIsfs+i;
            single.pOutputs = source->pOutputs ? source->pOutputs+i : NULL;
            g = Decpla_Decompose(&single,&singleOptions,NULL,err);
            if ( !g ) { p.failed = 1; break; }
            ranks[i].index = i; ranks[i].size = Gia_ManAndNum(g); Gia_ManStop(g);
        }
        if ( !p.failed ) {
            qsort(ranks,source->nOutputs,sizeof(*ranks),options->OutputOrder == 1 ? Decpla_OrderSmall : Decpla_OrderLarge);
            for ( i = 0; i < source->nOutputs; ++i ) Vec_IntWriteEntry(order,i,ranks[i].index);
            if ( out ) {
                fprintf(out,"decpla: output schedule (index:independent ANDs):");
                for ( i = 0; i < source->nOutputs; ++i ) fprintf(out," %d:%d",ranks[i].index,ranks[i].size);
                fprintf(out,"\n");
            }
        }
        free(ranks);
    }
    if ( options->fOrderSeed ) p.random = options->OrderSeed;
    if ( options->OutputOrder == 3 ) for ( i = source->nOutputs-1; i > 0; --i ) {
        int j = (int)Decpla_DecRandom(&p,(unsigned)i+1), t = Vec_IntEntry(order,i);
        Vec_IntWriteEntry(order,i,Vec_IntEntry(order,j)); Vec_IntWriteEntry(order,j,t);
    }
    // The explicit order stream must not consume grouping random numbers.
    if ( options->fOrderSeed ) {
        p.random = options->Seed;
        if ( out ) {
            fprintf(out,"decpla: output schedule (order seed %u):",options->OrderSeed);
            for ( i = 0; i < source->nOutputs; ++i ) fprintf(out," %d",Vec_IntEntry(order,i));
            fprintf(out,"\n");
        }
    }
    if ( !p.sat ) p.failed = 1;
    for ( i = 0; i < source->nOutputs && !p.failed; ++i ) {
        Decpla_Isf_t f; int lit = -1, oi = Vec_IntEntry(order,i);
        memset(&f,0,sizeof(f));
        if ( Decpla_Copy(&f.On,&source->pIsfs[oi].On) && Decpla_Copy(&f.Off,&source->pIsfs[oi].Off) ) lit = Decpla_ChooseSupport(&p,&f,oi);
        Decpla_IsfFree(&f);
        if ( lit < 0 ) { p.failed = 1; break; }
        Vec_IntWriteEntry(outputs,oi,lit);
        Decpla_MarkShared(&p,lit);
        if ( p.nCommitted > p.o.nNodesMax ) p.failed = 1;
    }
    if ( !p.failed ) {
        Gia_Man_t * original = NULL;
        if ( (p.o.Features & 64) && p.o.fReuse ) {
            Gia_Man_t * copy = Gia_ManDup(p.g);
            for ( i = 0; i < Vec_IntSize(outputs); ++i ) Gia_ManAppendCo(copy,Vec_IntEntry(outputs,i));
            original = Gia_ManCleanup(copy); Gia_ManStop(copy);
            Decpla_ResubRoots(&p,source,outputs);
        }
        Decpla_CubeFactors(&p,outputs);
        for ( i = 0; i < Vec_IntSize(outputs); ++i ) Gia_ManAppendCo(p.g,Vec_IntEntry(outputs,i));
        result = Gia_ManCleanup(p.g);
        if ( original ) {
            if ( Gia_ManAndNum(original) < Gia_ManAndNum(result) || (Gia_ManAndNum(original) == Gia_ManAndNum(result) && Gia_ManLevelNum(original) < Gia_ManLevelNum(result)) ) {
                Gia_ManStop(result); result = original;
            } else Gia_ManStop(original);
        }
        if ( p.o.fReuse && (p.o.Features & 4) ) result = Decpla_ResubInternal(&p,source,result);
        if ( Decpla_Verify(source,result,p.o.nConfLimit,err) != 1 ) { Gia_ManStop(result); result = NULL; }
    } else if ( p.nCommitted > p.o.nNodesMax )
        fprintf(err,"decpla: committed AND limit exceeded (%d > %d); no AIG installed\n",p.nCommitted,p.o.nNodesMax);
    else fprintf(err,"decpla: decomposition stopped (allocation failure); no AIG installed\n");
    if ( result && out ) fprintf(out,"decpla: VERIFIED  inputs = %d  outputs = %d  ANDs = %d  levels = %d  time = %.3f s\n"
        "decpla: OR splits = %u  AND splits = %u  MUX splits = %u  reuse = %u  direct/SOP = %u  abandoned splits = %u  weak = %u  XOR = %u  divisors = %u\n"
        "decpla: constructed ANDs = %d  committed ANDs = %d  completion trials = %u  alternatives selected = %u\n"
        "decpla: internal replacements = %u  candidates = %u\n"
        "decpla: support trials = %u  alternatives selected = %u\n",
        Gia_ManCiNum(result),Gia_ManCoNum(result),Gia_ManAndNum(result),Gia_ManLevelNum(result),(double)(Abc_Clock()-start)/CLOCKS_PER_SEC,
        p.stats.nOr,p.stats.nAnd,p.stats.nMux,p.stats.nReuse,p.stats.nFallback,p.stats.nAbandoned,p.stats.nWeak,p.stats.nXor,p.stats.nDivisor,
        Gia_ManAndNum(p.g),Gia_ManAndNum(result),p.stats.nCompletionTrials,p.stats.nCompletionChanges,p.nResubChanges,p.nResubTrials,
        p.nSupportTrials,p.nSupportChanges);
    for ( i = 0; i < p.nCache; ++i ) free(p.cache[i].support);
    Decpla_SatStop(p.sat); Vec_IntFree(p.shared); Vec_IntFree(outputs); Vec_IntFree(order); Gia_ManStop(p.g); return result;
}
ABC_NAMESPACE_IMPL_END
