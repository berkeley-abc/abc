/**CFile****************************************************************

  FileName    [lmsEval.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

  Synopsis    [Exact filtering and memoization of recorded delay profiles.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 5, 2026.]

  Revision    [$Id: lmsEval.c,v 1.00 2026/10/05 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lms.h"
#include "misc/util/utilTruth.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// A direct-mapped, bounded cache. Collisions replace an entry, never relax
// key equality. Best is stored plus one so that zero denotes an empty slot.
#define LMS_EVAL_CACHE_SIZE (1 << 18)
typedef struct Lms_EvalEntry_t_ {
    word Times;
    int Class, nVars, Best, Delay;
} Lms_EvalEntry_t;

struct Lms_Eval_t_ {
    int nVars, nClasses;
    const int * pStarts;
    const word * pDelays;
    const char * pAreas;
    word ** ppMasks;
    size_t nBytes;
    word nQueries, nCandidates, nVisited;
    Lms_EvalEntry_t * pCache;
    int fCache;
    word nCacheQueries, nCacheHits, nCacheReplaced, nCacheBypassed;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocate an exact LMS candidate evaluator.]

  Description [Borrows immutable class offsets, pin depths, and areas until Stop.]

  SideEffects [Allocates memory.]

  SeeAlso     []

***********************************************************************/
Lms_Eval_t * Lms_EvalStart( int nVars, int nClasses, const int * pStarts,
    const word * pDelays, const char * pAreas )
{
    Lms_Eval_t * p = ABC_CALLOC(Lms_Eval_t, 1);
    assert(nVars > 0 && nVars <= 16 && nClasses >= 0);
    p->nVars = nVars; p->nClasses = nClasses;
    p->pStarts = pStarts; p->pDelays = pDelays; p->pAreas = pAreas;
    p->ppMasks = ABC_CALLOC(word *, nClasses);
    return p;
}
/**Function*************************************************************

  Synopsis    [Free an LMS candidate evaluator.]

  Description [Accepts NULL.]

  SideEffects [Frees the index and cache.]

  SeeAlso     []

***********************************************************************/
void Lms_EvalStop( Lms_Eval_t * p )
{
    int i;
    if ( !p ) return;
    for ( i = 0; i < p->nClasses; ++i ) ABC_FREE(p->ppMasks[i]);
    ABC_FREE(p->pCache); ABC_FREE(p->ppMasks); ABC_FREE(p);
}
// Enabling starts a cold cache for reproducible per-run measurements. The
// index of pin depths is independent and can remain warm.
/**Function*************************************************************

  Synopsis    [Enable or disable exact winner caching.]

  Description [Enabling starts with an empty bounded cache.]

  SideEffects [Changes the cache and resets its counters.]

  SeeAlso     []

***********************************************************************/
void Lms_EvalCacheEnable( Lms_Eval_t * p, int fEnable )
{
    p->fCache = fEnable;
    if ( !fEnable ) return;
    if ( !p->pCache ) p->pCache = ABC_CALLOC(Lms_EvalEntry_t, LMS_EVAL_CACHE_SIZE);
    else memset(p->pCache, 0, LMS_EVAL_CACHE_SIZE*sizeof(Lms_EvalEntry_t));
    p->nCacheQueries = p->nCacheHits = p->nCacheReplaced = p->nCacheBypassed = 0;
}
/**Function*************************************************************

  Synopsis    [Print evaluator statistics.]

  Description [Writes to pFile.]

  SideEffects [None.]

  SeeAlso     []

***********************************************************************/
void Lms_EvalStats( Lms_Eval_t * p, FILE * pFile )
{
    if ( !p ) return;
    fprintf(pFile, "LMS filtering: %llu queries, %llu/%llu candidates visited (%.1f%% skipped), %.2f MiB index.\n",
        (unsigned long long)p->nQueries, (unsigned long long)p->nVisited,
        (unsigned long long)p->nCandidates,
        p->nCandidates ? 100.0*(1.0-(double)p->nVisited/(double)p->nCandidates) : 0.0,
        (double)p->nBytes/(1024*1024));
    if ( p->fCache )
        fprintf(pFile, "LMS winner cache: %llu/%llu hits (%.1f%%), %llu replacements, %llu bypassed, %.2f MiB.\n",
            (unsigned long long)p->nCacheHits, (unsigned long long)p->nCacheQueries,
            p->nCacheQueries ? 100.0*(double)p->nCacheHits/(double)p->nCacheQueries : 0.0,
            (unsigned long long)p->nCacheReplaced,
            (unsigned long long)p->nCacheBypassed,
            (double)(LMS_EVAL_CACHE_SIZE*sizeof(Lms_EvalEntry_t))/(1024*1024));
}
/**Function*************************************************************

  Synopsis    [Reset evaluator statistics.]

  Description [Retains allocated indexes and cache entries.]

  SideEffects [Clears counters.]

  SeeAlso     []

***********************************************************************/
void Lms_EvalResetStats( Lms_Eval_t * p )
{
    if ( p )
    {
        p->nQueries = p->nCandidates = p->nVisited = 0;
        p->nCacheQueries = p->nCacheHits = p->nCacheReplaced = p->nCacheBypassed = 0;
    }
}
// Common integer arrivals admit exact offset removal. Pin depths are in
// [0,15], so an arrival earlier than Max-15 cannot determine the maximum:
// even its largest depth reaches at most Max, while the latest pin reaches
// at least Max. Saturating these differences at 15 therefore preserves every
// candidate delay (relative to Max), not just the winning candidate.
// All additions must be exactly representable and above the negative clamp.
// Fractional, negative, or very large arrivals bypass memoization entirely.
static int Lms_EvalKey( int Class, int nVars, const float * pTimes,
    Lms_EvalEntry_t * pKey, unsigned * pHash )
{
    unsigned Hash = (unsigned)Class*12582917u + (unsigned)nVars;
    int i, Base = 0, Times[16];
    for ( i = 0; i < nVars; ++i )
    {
        if ( !(pTimes[i] >= 0 && pTimes[i] <= 16777200.0f) ||
             pTimes[i] != (float)(int)pTimes[i] ) return -1;
        Times[i] = (int)pTimes[i];
        Base = Abc_MaxInt(Base, Times[i]);
    }
    pKey->Times = 0;
    for ( i = 0; i < nVars; ++i )
        pKey->Times |= (word)Abc_MinInt(Base-Times[i], 15) << (4*i);
    Hash ^= (unsigned)pKey->Times;
    Hash = Hash*16777619u ^ (unsigned)(pKey->Times >> 32);
    Hash ^= Hash >> 16; Hash *= 2246822519u; Hash ^= Hash >> 13;
    *pHash = Hash;
    return Base;
}
// Large classes are indexed lazily. For each pin and depth, a bit marks a
// structure whose pin depth is no greater. The bounded index is optional:
// allocation limits merely select the exact scan below.
static word * Lms_EvalMasks( Lms_Eval_t * p, int Class, int nWords )
{
    int First = p->pStarts[Class], Count = p->pStarts[Class+1]-First;
    word * pMasks;
    size_t nBytes = (size_t)p->nVars*16*nWords*sizeof(word);
    int i, k, d, w;
    if ( p->ppMasks[Class] ) return p->ppMasks[Class];
    if ( Count < 16 || nBytes > 64*1024*1024-p->nBytes ) return NULL;
    pMasks = ABC_CALLOC(word, nBytes/sizeof(word));
    for ( i = 0; i < Count; ++i )
        for ( k = 0; k < p->nVars; ++k )
        {
            d = (int)((p->pDelays[First+i] >> (4*k)) & 15);
            pMasks[(k*16+d)*nWords+(i>>6)] |= (word)1 << (i&63);
        }
    for ( k = 0; k < p->nVars; ++k )
        for ( d = 1; d < 16; ++d )
            for ( w = 0; w < nWords; ++w )
                pMasks[(k*16+d)*nWords+w] |= pMasks[(k*16+d-1)*nWords+w];
    p->nBytes += nBytes;
    return p->ppMasks[Class] = pMasks;
}
// Match the original evaluator's float addition followed by int conversion.
// Adjust the integer estimate at the boundary, including fractional arrivals
// and float rounding near powers of two. This never rejects an equal delay.
static int Lms_EvalBound( float Time, int Delay )
{
    double Estimate = (double)Delay-(double)(int)Time;
    int Bound = Estimate < -1 ? -1 : Estimate > 15 ? 15 : (int)Estimate;
    while ( Bound >= 0 && (int)(Time+Bound) > Delay ) --Bound;
    while ( Bound < 15 && (int)(Time+(Bound+1)) <= Delay ) ++Bound;
    return Bound;
}
static int Lms_EvalDelay( word Profile, int nVars, const float * pTimes,
    int Late, int Second, int Limit )
{
    int i, Delay, Temp;
    Delay = (int)(pTimes[Late] + ((Profile >> (4*Late)) & 15));
    Delay = Abc_MaxInt(Delay, -ABC_INFINITY);
    if ( Delay > Limit ) return Delay;
    if ( Second >= 0 )
    {
        Temp = (int)(pTimes[Second] + ((Profile >> (4*Second)) & 15));
        Delay = Abc_MaxInt(Delay, Temp);
        if ( Delay > Limit ) return Delay;
    }
    for ( i = 0; i < nVars; ++i )
    {
        if ( i == Late || i == Second ) continue;
        Temp = (int)(pTimes[i] + ((Profile >> (4*i)) & 15));
        Delay = Abc_MaxInt(Delay, Temp);
        if ( Delay > Limit ) break;
    }
    return Delay;
}
/**Function*************************************************************

  Synopsis    [Select the exact delay/area winner in one function class.]

  Description [Preserves the original evaluator tie order and float-to-int costs.]

  SideEffects [Updates cache, indexes, and counters.]

  SeeAlso     []

***********************************************************************/
int Lms_EvalFind( Lms_Eval_t * p, int Class, int nVars,
    const float * pTimes, int * pDelay )
{
    int First = p->pStarts[Class], Count = p->pStarts[Class+1]-First;
    int nWords = (Count+63)/64, Late = 0, Second = -1, Best = First;
    int i, w, Delay, Area, BestDelay, BestArea, b0, b1;
    word * pMasks;
    Lms_EvalEntry_t Key, * pEntry = NULL;
    int Base = 0;
    assert(Count > 0 && nVars > 0 && nVars <= p->nVars);
    if ( p->fCache )
    {
        unsigned Hash;
        ++p->nCacheQueries;
        Base = Lms_EvalKey(Class, nVars, pTimes, &Key, &Hash);
        if ( Base < 0 ) ++p->nCacheBypassed;
        else pEntry = p->pCache+(Hash & (LMS_EVAL_CACHE_SIZE-1));
        if ( pEntry && pEntry->Best && pEntry->Class == Class && pEntry->nVars == nVars &&
             pEntry->Times == Key.Times )
        {
            ++p->nCacheHits;
            *pDelay = pEntry->Delay+Base;
            return pEntry->Best-1;
        }
    }
    ++p->nQueries; p->nCandidates += Count;
    for ( i = 1; i < nVars; ++i )
        if ( pTimes[i] > pTimes[Late] ) { Second = Late; Late = i; }
        else if ( Second < 0 || pTimes[i] > pTimes[Second] ) Second = i;
    BestDelay = Lms_EvalDelay(p->pDelays[First], nVars, pTimes, Late, Second, INT_MAX);
    BestArea = p->pAreas[First]; ++p->nVisited;
    pMasks = Lms_EvalMasks(p, Class, nWords);
    if ( !pMasks )
    {
        for ( i = First+1; i < First+Count; ++i )
        {
            Area = p->pAreas[i]; ++p->nVisited;
            Delay = Lms_EvalDelay(p->pDelays[i], nVars, pTimes, Late, Second,
                BestDelay-(Area >= BestArea));
            if ( Delay < BestDelay || (Delay == BestDelay && Area < BestArea) )
            { Best = i; BestDelay = Delay; BestArea = Area; }
        }
    }
    else
    {
        b0 = Lms_EvalBound(pTimes[Late], BestDelay);
        b1 = Second < 0 ? 15 : Lms_EvalBound(pTimes[Second], BestDelay);
        for ( w = 0; w < nWords && b0 >= 0 && b1 >= 0; ++w )
        {
            word Bits = pMasks[(Late*16+b0)*nWords+w];
            if ( Second >= 0 ) Bits &= pMasks[(Second*16+b1)*nWords+w];
            if ( !w ) Bits &= ~(word)1;
            while ( Bits )
            {
                i = First+64*w+Abc_Tt6FirstBit(Bits); Bits &= Bits-1;
                Area = p->pAreas[i]; ++p->nVisited;
                Delay = Lms_EvalDelay(p->pDelays[i], nVars, pTimes, Late, Second,
                    BestDelay-(Area >= BestArea));
                if ( Delay > BestDelay || (Delay == BestDelay && Area >= BestArea) ) continue;
                Best = i; BestArea = Area;
                if ( Delay == BestDelay ) continue;
                BestDelay = Delay;
                b0 = Lms_EvalBound(pTimes[Late], BestDelay);
                b1 = Second < 0 ? 15 : Lms_EvalBound(pTimes[Second], BestDelay);
                if ( b0 < 0 || b1 < 0 ) break;
                Bits &= pMasks[(Late*16+b0)*nWords+w];
                if ( Second >= 0 ) Bits &= pMasks[(Second*16+b1)*nWords+w];
            }
        }
    }
    *pDelay = BestDelay;
    if ( pEntry )
    {
        p->nCacheReplaced += pEntry->Best != 0;
        pEntry->Class = Class; pEntry->nVars = nVars; pEntry->Times = Key.Times;
        pEntry->Best = Best+1; pEntry->Delay = BestDelay-Base;
    }
    return Best;
}

ABC_NAMESPACE_IMPL_END
