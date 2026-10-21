/**CFile****************************************************************

  FileName    [giaResub.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Resubstitution.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaResub.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecWec.h"
#include "misc/vec/vecQue.h"
#include "misc/vec/vecHsh.h"
#include "misc/util/utilTruth.h"
#include "base/io/ioResub.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes MFFCs of all qualifying nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCheckMffc_rec( Gia_Man_t * p,Gia_Obj_t * pObj, int Limit, Vec_Int_t * vNodes )
{
    int iFanin;
    if ( Gia_ObjIsCi(pObj) )
        return 1;
    assert( Gia_ObjIsAnd(pObj) );
    iFanin = Gia_ObjFaninId0p(p, pObj);
    Vec_IntPush( vNodes, iFanin );
    if ( !Gia_ObjRefDecId(p, iFanin) && (Vec_IntSize(vNodes) > Limit || !Gia_ObjCheckMffc_rec(p, Gia_ObjFanin0(pObj), Limit, vNodes)) )
        return 0;
    iFanin = Gia_ObjFaninId1p(p, pObj);
    Vec_IntPush( vNodes, iFanin );
    if ( !Gia_ObjRefDecId(p, iFanin) && (Vec_IntSize(vNodes) > Limit || !Gia_ObjCheckMffc_rec(p, Gia_ObjFanin1(pObj), Limit, vNodes)) )
        return 0;
    if ( !Gia_ObjIsMux(p, pObj) )
        return 1;
    iFanin = Gia_ObjFaninId2p(p, pObj);
    Vec_IntPush( vNodes, iFanin );
    if ( !Gia_ObjRefDecId(p, iFanin) && (Vec_IntSize(vNodes) > Limit || !Gia_ObjCheckMffc_rec(p, Gia_ObjFanin2(p, pObj), Limit, vNodes)) )
        return 0;
    return 1;
}
int Gia_ObjCheckMffc( Gia_Man_t * p, Gia_Obj_t * pRoot, int Limit, Vec_Int_t * vNodes, Vec_Int_t * vLeaves, Vec_Int_t * vInners )
{
    int RetValue, iObj, i;
    Vec_IntClear( vNodes );
    RetValue = Gia_ObjCheckMffc_rec( p, pRoot, Limit, vNodes );
    if ( RetValue )
    {
        Vec_IntClear( vLeaves );
        Vec_IntClear( vInners );
        Vec_IntSort( vNodes, 0 );
        Vec_IntForEachEntry( vNodes, iObj, i )
            if ( Gia_ObjRefNumId(p, iObj) > 0 || Gia_ObjIsCi(Gia_ManObj(p, iObj)) )
            {
                if ( !Vec_IntSize(vLeaves) || Vec_IntEntryLast(vLeaves) != iObj )
                    Vec_IntPush( vLeaves, iObj );
            }
            else
            {
                if ( !Vec_IntSize(vInners) || Vec_IntEntryLast(vInners) != iObj )
                    Vec_IntPush( vInners, iObj );
            }
        Vec_IntPush( vInners, Gia_ObjId(p, pRoot) );
    }
    Vec_IntForEachEntry( vNodes, iObj, i )
        Gia_ObjRefIncId( p, iObj );
    return RetValue;
}
Vec_Wec_t * Gia_ManComputeMffcs( Gia_Man_t * p, int LimitMin, int LimitMax, int SuppMax, int RatioBest )
{
    Gia_Obj_t * pObj;
    Vec_Wec_t * vMffcs;
    Vec_Int_t * vNodes, * vLeaves, * vInners, * vMffc;
    int i, iPivot;
    assert( p->pMuxes );
    vNodes  = Vec_IntAlloc( 2 * LimitMax );
    vLeaves = Vec_IntAlloc( 2 * LimitMax );
    vInners = Vec_IntAlloc( 2 * LimitMax );
    vMffcs  = Vec_WecAlloc( 1000 );
    Gia_ManCreateRefs( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !Gia_ObjRefNum(p, pObj) )
            continue;
        if ( !Gia_ObjCheckMffc(p, pObj, LimitMax, vNodes, vLeaves, vInners) )
            continue;
        if ( Vec_IntSize(vInners) < LimitMin )
            continue;
        if ( Vec_IntSize(vLeaves) > SuppMax )
            continue;
        // improve cut
        // collect cut
        vMffc = Vec_WecPushLevel( vMffcs );
        Vec_IntGrow( vMffc, Vec_IntSize(vLeaves) + Vec_IntSize(vInners) + 20 );
        Vec_IntPush( vMffc, i );
        Vec_IntPush( vMffc, Vec_IntSize(vLeaves) );
        Vec_IntPush( vMffc, Vec_IntSize(vInners) );
        Vec_IntAppend( vMffc, vLeaves );
//        Vec_IntAppend( vMffc, vInners );
        // add last entry equal to the ratio
        Vec_IntPush( vMffc, 1000 * Vec_IntSize(vInners) / Vec_IntSize(vLeaves) );
    }
    Vec_IntFree( vNodes );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vInners );
    // sort MFFCs by their inner/leaf ratio
    Vec_WecSortByLastInt( vMffcs, 1 );
    Vec_WecForEachLevel( vMffcs, vMffc, i )
        Vec_IntPop( vMffc );
    // remove those whose ratio is not good
    iPivot = RatioBest * Vec_WecSize(vMffcs) / 100;
    Vec_WecForEachLevelStart( vMffcs, vMffc, i, iPivot )
        Vec_IntErase( vMffc );
    assert( iPivot <= Vec_WecSize(vMffcs) );
    Vec_WecShrink( vMffcs, iPivot );
    return vMffcs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintDivStats( Gia_Man_t * p, Vec_Wec_t * vMffcs, Vec_Wec_t * vPivots ) 
{
    int fVerbose = 0;
    Vec_Int_t * vMffc;
    int i, nDivs, nDivsAll = 0, nDivs0 = 0;
    Vec_WecForEachLevel( vMffcs, vMffc, i )
    {
        nDivs = Vec_IntSize(vMffc) - 3 - Vec_IntEntry(vMffc, 1) - Vec_IntEntry(vMffc, 2);
        nDivs0 += (nDivs == 0);
        nDivsAll += nDivs;
        if ( !fVerbose )
            continue;
        printf( "%6d : ",      Vec_IntEntry(vMffc, 0) );
        printf( "Leaf =%3d  ", Vec_IntEntry(vMffc, 1) );
        printf( "Mffc =%4d  ", Vec_IntEntry(vMffc, 2) );
        printf( "Divs =%4d  ", nDivs );
        printf( "\n" );
    }
    printf( "Collected %d (%.1f %%) MFFCs and %d (%.1f %%) have no divisors (div ave for others is %.2f).\n", 
        Vec_WecSize(vMffcs), 100.0 * Vec_WecSize(vMffcs) / Gia_ManAndNum(p), 
        nDivs0, 100.0 * nDivs0 / Gia_ManAndNum(p), 
        1.0*nDivsAll/Abc_MaxInt(1, Vec_WecSize(vMffcs) - nDivs0) );
    printf( "Using %.2f MB for MFFCs and %.2f MB for pivots.   ", 
        Vec_WecMemory(vMffcs)/(1<<20), Vec_WecMemory(vPivots)/(1<<20) );
}

/**Function*************************************************************

  Synopsis    [Compute divisors and Boolean functions for the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAddDivisors( Gia_Man_t * p, Vec_Wec_t * vMffcs )
{
    Vec_Wec_t * vPivots;
    Vec_Int_t * vMffc, * vPivot, * vPivot0, * vPivot1;
    Vec_Int_t * vCommon, * vCommon2, * vMap;
    Gia_Obj_t * pObj;
    int i, k, iObj, iPivot, iMffc;
//abctime clkStart = Abc_Clock();
    // initialize pivots (mapping of nodes into MFFCs whose leaves they are)
    vMap = Vec_IntStartFull( Gia_ManObjNum(p) );
    vPivots = Vec_WecStart( Gia_ManObjNum(p) );
    Vec_WecForEachLevel( vMffcs, vMffc, i )
    {
        assert( Vec_IntSize(vMffc) == 3 + Vec_IntEntry(vMffc, 1) );
        iPivot = Vec_IntEntry( vMffc, 0 );
        Vec_IntWriteEntry( vMap, iPivot, i );
        // iterate through the MFFC leaves
        Vec_IntForEachEntryStart( vMffc, iObj, k, 3 )
        {
            vPivot = Vec_WecEntry( vPivots, iObj );
            if ( Vec_IntSize(vPivot) == 0 )
                Vec_IntGrow(vPivot, 4);
            Vec_IntPush( vPivot, iPivot );            
        }
    }
    Vec_WecForEachLevel( vPivots, vPivot, i )
        Vec_IntSort( vPivot, 0 );
    // create pivots for internal nodes while growing MFFCs
    vCommon = Vec_IntAlloc( 100 );
    vCommon2 = Vec_IntAlloc( 100 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        // find commont pivots
        // the slow down happens because some PIs have very large sets of pivots
        vPivot0 = Vec_WecEntry( vPivots, Gia_ObjFaninId0(pObj, i) );
        vPivot1 = Vec_WecEntry( vPivots, Gia_ObjFaninId1(pObj, i) );
        Vec_IntTwoFindCommon( vPivot0, vPivot1, vCommon );
        if ( Gia_ObjIsMuxId(p, i) )
        {
            vPivot = Vec_WecEntry( vPivots, Gia_ObjFaninId2(p, i) );
            Vec_IntTwoFindCommon( vPivot, vCommon, vCommon2 );
            ABC_SWAP( Vec_Int_t *, vCommon, vCommon2 );
        }
        if ( Vec_IntSize(vCommon) == 0 )
            continue;
        // add new pivots (this trick increased memory used in vPivots)
        vPivot = Vec_WecEntry( vPivots, i );
        Vec_IntTwoMerge2( vPivot, vCommon, vCommon2 );
        ABC_SWAP( Vec_Int_t, *vPivot, *vCommon2 );
        // grow MFFCs
        Vec_IntForEachEntry( vCommon, iObj, k )
        {
            iMffc = Vec_IntEntry( vMap, iObj );
            assert( iMffc != -1 );
            vMffc = Vec_WecEntry( vMffcs, iMffc );
            Vec_IntPush( vMffc, i );
        }
    }
//Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    Vec_IntFree( vCommon );
    Vec_IntFree( vCommon2 );
    Vec_IntFree( vMap );
    Gia_ManPrintDivStats( p, vMffcs, vPivots );
    Vec_WecFree( vPivots );
    // returns the modified array of MFFCs
}
void Gia_ManResubTest( Gia_Man_t * p )
{
    Vec_Wec_t * vMffcs;
    Gia_Man_t * pNew = Gia_ManDupMuxes( p, 2 );
abctime clkStart = Abc_Clock();
    vMffcs = Gia_ManComputeMffcs( pNew, 4, 100, 8, 100 );
    Gia_ManAddDivisors( pNew, vMffcs );
    Vec_WecFree( vMffcs );
Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    Gia_ManStop( pNew );
}





/**Function*************************************************************

  Synopsis    [Resubstitution data-structure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// Research quality controls are process-local opt-ins.  Invalid values fail
// explicitly rather than silently enabling a different experiment.
int Abc_ResubQualityOption( char const * pName )
{
    char const * pValue = getenv( pName );
    if ( pValue == NULL || !strcmp(pValue, "0") ) return 0;
    if ( !strcmp(pValue, "1") ) return 1;
    fprintf( stderr, "stran-quality-invalid-option: %s=%s (expected 0 or 1)\n", pName, pValue );
    exit( 2 );
    return 0;
}

int Abc_ResubQualityNoTruncation( void )
{
    return Abc_ResubQualityOption( "ABC_STRAN_QUALITY_NO_TRUNCATION" );
}

static int Gia_ResbPairClassCacheMode( void )
{
    char const * pValue = getenv("ABC_STRICT_PAIR_CLASS_CACHE");
    if ( pValue == NULL || !strcmp(pValue, "0") ) return 0;
    if ( !strcmp(pValue, "1") ) return 1;
    if ( !strcmp(pValue, "2") ) return 2;
    fprintf(stderr, "stran-quality-invalid-option: ABC_STRICT_PAIR_CLASS_CACHE=%s (expected0/1/2)\n", pValue);
    exit(2);
    return 0;
}

// A few legacy template return values still combine two bounded 15-bit
// indices.  Real divisor pairs use the manager-owned intern table below and
// therefore do not inherit this representation limit.
static int s_ResbQualityNoTruncation = 0;
static int Gia_ResbLegacyPackTwo15( int Lo, int Hi, int Compl )
{
    if ( Lo < 0 || Hi < 0 || Lo > 0x7fff || Hi > 0x7fff )
    {
        fprintf( stderr, "resub-unsupported: legacy-composite-width lo=%d hi=%d max=32767\n", Lo, Hi );
        exit( 3 );
    }
    return Abc_Var2Lit((Hi << 15) | Lo, Compl);
}

typedef struct Gia_ResbMan_t_ Gia_ResbMan_t;
typedef struct Gia_ResbRootCache_t_ Gia_ResbRootCache_t;
// The caller owns the ODC scope. Each manager captures the policy at bind
// time, so an existing iterator never changes its ordered pair universe.
static int s_ResubCarePairTruth = 0;
int Abc_ResubSetCarePairTruth( int Enable )
{
    int Previous = s_ResubCarePairTruth;
    assert( Enable == 0 || Enable == 1 );
    s_ResubCarePairTruth = Enable;
    return Previous;
}
struct Gia_ResbRootCache_t_
{
    int         nWords;
    int         nDivs;
    int         nLimit;
    int         nDivsMax;
    int         fQualityNoTruncation;
    int         fUseZero;
    int         fUseXor;
    int         fCarePairTruth;
    int         nStage5Paths;
    int         nBinds;
    Vec_Ptr_t * vContextDivs;
    Vec_Wrd_t * vContextSets;
    Vec_Int_t * vResidualCacheBins;
    Vec_Int_t * vResidualCacheMeta;
    Vec_Int_t * vResidualCacheGates;
    Vec_Wrd_t * vResidualCacheHashes;
    Vec_Wrd_t * vResidualCacheMasks;
    Vec_Wrd_t * vResidualCacheSolveTimes;
};
struct Gia_ResbMan_t_
{
    int         nWords;
    int         nLimit;
    int         nDivsMax;
    int         fQualityNoTruncation;
    int         iChoice;
    int         fChoiceSelected;
    int         fSkipTemplates;
    int         fTopCacheReady;
    int         fUseResidualCache;
    int         fUseRecursiveFailCache;
    int         nStage5Paths;
    int         nCurrentPath;
    int         nStage5TopFrontier;
    int         nSecondPath;
    int         fSecondPivotSelected;
    int         nSecondPivotRank;
    int         nSecondPivotCover;
    int         nSecondPivotNew;
    int         nSecondPivotSym;
    int         nResidualCacheHits[2][2];
    int         iResidualCacheBind;
    int         nResidualRecDepth;
    long long   nResidualCacheLookups;
    long long   nResidualCacheHitsTotal;
    long long   nResidualCacheMisses;
    long long   nResidualCacheSamePageHits;
    long long   nResidualCacheCrossPageHits;
    long long   nResidualCacheFailHits;
    long long   nResidualCacheSuccessHits;
    long long   nResidualCachePayloadBytes;
    long long   nMultiPathCacheEntries;
    long long   nMultiPathCacheLookups;
    long long   nMultiPathCacheHits;
    long long   nMultiPathCacheFailHits;
    long long   nMultiPathCacheSuccessHits;
    long long   nMultiPathCachePayloadBytes;
    abctime     timeResidualCacheSaved;
    abctime     timeResidualCacheLookup;
    long long   nResidualRecCalls;
    long long   nResidualRecUnique;
    long long   nResidualRecDuplicate;
    long long   nResidualRecSamePage;
    long long   nResidualRecCrossPage;
    long long   nResidualRecFailHits;
    long long   nResidualRecSuccessDuplicate;
    long long   nResidualRecPayloadBytes;
    long long   nResidualRecDuplicateDepth[4];
    abctime     timeResidualRecSaved;
    abctime     timeResidualRecLookup;
    void **     ppRootCache;
    Gia_ResbRootCache_t * pRootCache;
    int         fUseSolvSched;
    int         fSolvScheduleReady;
    int         fSolvScheduleProfiled;
    int         nSolvSchedulePivots;
    int         nSolvScheduleComplete;
    abctime     timeSolvSchedule;
    int         fProfilePivots;
    int         fPairClassCache;
    int         fGreedyPairRanked;
    Vec_Int_t * vPairSigClasses;
    Vec_Int_t * vPairSigReps;
    Vec_Int_t * vPairSigDupRows;
    unsigned char * pPairClassMasks; // one FindUnatePairs call and one OFF/ON orientation
    long long   nPairClassVisits, nPairClassComputations;
    int         nPairSigDup;
    int         fTopPivotProfileReady;
    int         nTopPivotKind;
    int         nTopPivotRank;
    int         nTopPivotCover;
    int         nTopPivotTotal;
    int         nTopPivotNovel;
    int         nTopPivotRemain;
    int         fTopPivotDuplicate;
    int         nTopFrontier;
    int         nTopFrontierUnique;
    int         nTopFrontierZeroNovel;
    int         nTopFrontierCoverSum;
    int         nTopFrontierNovelSum;
    int         fUseZero;
    int         fUseXor;
    int         fCarePairTruth;
    int         fDebug;
    int         fVerbose;
    int         fVeryVerbose;
    Vec_Ptr_t * vDivs;
    Vec_Int_t * vGates;
    Vec_Int_t * vUnateLits[2];
    Vec_Int_t * vNotUnateVars[2];
    Vec_Int_t * vUnatePairs[2];
    Vec_Int_t * vBinateVars;
    Vec_Int_t * vPairVars;
    // Pair descriptors are positive literals over stable interned keys.  Each
    // key stores the two original divisor literals without narrowing them to
    // the historical 15-bit inline fields.
    Vec_Int_t * vPairKeys;
    Hsh_IntMan_t * pPairHash;
    Vec_Int_t * vUnateLitsW[2];
    Vec_Int_t * vUnatePairsW[2];
    Vec_Int_t * vTopUnateLits[2];
    Vec_Int_t * vTopUnateLitsW[2];
    Vec_Int_t * vTopUnatePairs[2];
    Vec_Int_t * vTopUnatePairsW[2];
    Vec_Int_t * vTopPivotNovel;
    Vec_Int_t * vTopPivotDuplicate;
    Vec_Wrd_t * vTopPivotCovers;
    Vec_Int_t * vSecondPivotRanks;
    Vec_Wrd_t * vSecondPivotCovers;
    Vec_Int_t * vSolvOrder;
    Vec_Int_t * vSolvDepth;
    Vec_Int_t * vSolvComplete;
    Vec_Wrd_t * vSolvAmbiguity;
    Vec_Wrd_t * vSolvClassMasks[2];
    Vec_Int_t * vSolvClassCounts[2];
    Vec_Int_t * vSolvSelected;
    Vec_Int_t * vResidualCacheBins;
    Vec_Int_t * vResidualCacheMeta;
    Vec_Int_t * vResidualCacheGates;
    Vec_Wrd_t * vResidualCacheHashes;
    Vec_Wrd_t * vResidualCacheMasks;
    Vec_Wrd_t * vResidualCacheSolveTimes;
    Vec_Wec_t * vSorter;
    word *      pSets[2];
    word *      pDivA;
    word *      pDivB;
    Vec_Wrd_t * vSims;
};

// Return a literal whose variable is a stable index into this binding's pair
// table.  The two key words are kept unique by the hash manager, so the same
// divisor pair discovered from OFF and ON receives the same variable and the
// common/opposite-phase test remains exact.  Only the descriptor is compact;
// emitted recipes recover the original, unrestricted divisor literals.
static int Gia_ResbPairIntern( Gia_ResbMan_t * p, int Lo, int Hi, int Compl )
{
    int iKey, iPair;
    assert( Lo >= 0 && Hi >= 0 );
    iKey = Vec_IntSize(p->vPairKeys) / 2;
    Vec_IntPushTwo( p->vPairKeys, Lo, Hi );
    iPair = Hsh_IntManAdd( p->pPairHash, iKey );
    if ( iPair != iKey )
        Vec_IntShrink( p->vPairKeys, 2 * iKey );
    // Pair descriptors share ABC's signed literal type.  Exhausting this
    // address space would be a hard representation error, never a rejected
    // candidate or an UNKNOWN proof result.
    if ( iPair < 0 || iPair > 0x3fffffff )
    {
        fprintf( stderr, "resub-unsupported: pair-table-size=%d max=%d\n",
            iPair, 0x3fffffff );
        exit( 3 );
    }
    return Abc_Var2Lit( iPair, Compl );
}

static inline int Gia_ResbPairLit0( Gia_ResbMan_t * p, int Pair )
{
    int iPair = Abc_Lit2Var(Pair);
    Hsh_IntObj_t * pObj = Hsh_IntObj( p->pPairHash, iPair );
    assert( pObj != NULL );
    return Vec_IntEntry( p->vPairKeys, 2 * pObj->iData );
}

static inline int Gia_ResbPairLit1( Gia_ResbMan_t * p, int Pair )
{
    int iPair = Abc_Lit2Var(Pair);
    Hsh_IntObj_t * pObj = Hsh_IntObj( p->pPairHash, iPair );
    assert( pObj != NULL );
    return Vec_IntEntry( p->vPairKeys, 2 * pObj->iData + 1 );
}

Gia_ResbMan_t * Gia_ResbAlloc( int nWords )
{
    Gia_ResbMan_t * p   = ABC_CALLOC( Gia_ResbMan_t, 1 );
    p->nWords           = nWords;
    p->vUnateLits[0]    = Vec_IntAlloc( 100 );
    p->vUnateLits[1]    = Vec_IntAlloc( 100 );
    p->vNotUnateVars[0] = Vec_IntAlloc( 100 );
    p->vNotUnateVars[1] = Vec_IntAlloc( 100 );
    p->vUnatePairs[0]   = Vec_IntAlloc( 100 );
    p->vUnatePairs[1]   = Vec_IntAlloc( 100 );
    p->vUnateLitsW[0]   = Vec_IntAlloc( 100 );
    p->vUnateLitsW[1]   = Vec_IntAlloc( 100 );
    p->vUnatePairsW[0]  = Vec_IntAlloc( 100 );
    p->vUnatePairsW[1]  = Vec_IntAlloc( 100 );
    p->vTopUnateLits[0] = Vec_IntAlloc( 100 );
    p->vTopUnateLits[1] = Vec_IntAlloc( 100 );
    p->vTopUnateLitsW[0] = Vec_IntAlloc( 100 );
    p->vTopUnateLitsW[1] = Vec_IntAlloc( 100 );
    p->vTopUnatePairs[0] = Vec_IntAlloc( 100 );
    p->vTopUnatePairs[1] = Vec_IntAlloc( 100 );
    p->vTopUnatePairsW[0] = Vec_IntAlloc( 100 );
    p->vTopUnatePairsW[1] = Vec_IntAlloc( 100 );
    p->vTopPivotNovel    = Vec_IntAlloc( 100 );
    p->vTopPivotDuplicate = Vec_IntAlloc( 100 );
    p->vTopPivotCovers   = Vec_WrdAlloc( 100 * nWords );
    p->vSecondPivotRanks = Vec_IntAlloc( 4 );
    p->vSecondPivotCovers = Vec_WrdAlloc( 4 * nWords );
    p->vSolvOrder        = Vec_IntAlloc( 100 );
    p->vSolvDepth        = Vec_IntAlloc( 100 );
    p->vSolvComplete     = Vec_IntAlloc( 100 );
    p->vSolvAmbiguity    = Vec_WrdAlloc( 100 );
    p->vSolvClassMasks[0] = Vec_WrdAlloc( 4 * nWords );
    p->vSolvClassMasks[1] = Vec_WrdAlloc( 8 * nWords );
    p->vSolvClassCounts[0] = Vec_IntAlloc( 8 );
    p->vSolvClassCounts[1] = Vec_IntAlloc( 16 );
    p->vSolvSelected     = Vec_IntAlloc( 100 );
    p->vResidualCacheBins = Vec_IntAlloc( 100 );
    p->vResidualCacheMeta = Vec_IntAlloc( 100 );
    p->vResidualCacheGates = Vec_IntAlloc( 100 );
    p->vResidualCacheHashes = Vec_WrdAlloc( 100 );
    p->vResidualCacheMasks = Vec_WrdAlloc( 200 * nWords );
    p->vResidualCacheSolveTimes = Vec_WrdAlloc( 100 );
    p->vSorter          = Vec_WecAlloc( nWords*64 );
    p->vBinateVars      = Vec_IntAlloc( 100 );
    p->vPairVars        = Vec_IntAlloc( 100 );
    p->vPairKeys        = Vec_IntAlloc( 200 );
    p->pPairHash        = Hsh_IntManStart( p->vPairKeys, 2, 100 );
    p->vGates           = Vec_IntAlloc( 100 );
    p->vDivs            = Vec_PtrAlloc( 100 );
    p->pSets[0]         = ABC_CALLOC( word, nWords );
    p->pSets[1]         = ABC_CALLOC( word, nWords );
    p->pDivA            = ABC_CALLOC( word, nWords );
    p->pDivB            = ABC_CALLOC( word, nWords );
    p->vSims            = Vec_WrdAlloc( 100 );
    return p;
}
void Gia_ResbInit( Gia_ResbMan_t * p, Vec_Ptr_t * vDivs, int nWords, int nLimit, int nDivsMax, int iChoice, int fUseZero, int fUseXor, int fDebug, int fVerbose, int fVeryVerbose )
{
    assert( p->nWords == nWords );
    p->nLimit       = nLimit;
    p->nDivsMax     = nDivsMax;
    p->fQualityNoTruncation = Abc_ResubQualityNoTruncation();
    s_ResbQualityNoTruncation = p->fQualityNoTruncation;
    p->iChoice      = iChoice;
    p->fChoiceSelected = 0;
    p->fSkipTemplates = 0;
    p->fTopCacheReady = 0;
    p->fUseResidualCache = 1;
    p->fUseRecursiveFailCache = 1;
    p->nStage5Paths = 1;
    p->nCurrentPath = 1;
    p->nStage5TopFrontier = 0;
    p->nSecondPath = 0;
    p->fSecondPivotSelected = 0;
    p->nSecondPivotRank = 0;
    p->nSecondPivotCover = 0;
    p->nSecondPivotNew = 0;
    p->nSecondPivotSym = 0;
    memset( p->nResidualCacheHits, 0, sizeof(p->nResidualCacheHits) );
    p->iResidualCacheBind = 1;
    p->nResidualRecDepth = 0;
    p->nResidualCacheLookups = 0;
    p->nResidualCacheHitsTotal = 0;
    p->nResidualCacheMisses = 0;
    p->nResidualCacheSamePageHits = 0;
    p->nResidualCacheCrossPageHits = 0;
    p->nResidualCacheFailHits = 0;
    p->nResidualCacheSuccessHits = 0;
    p->nResidualCachePayloadBytes = 0;
    p->nMultiPathCacheEntries = 0;
    p->nMultiPathCacheLookups = 0;
    p->nMultiPathCacheHits = 0;
    p->nMultiPathCacheFailHits = 0;
    p->nMultiPathCacheSuccessHits = 0;
    p->nMultiPathCachePayloadBytes = 0;
    p->timeResidualCacheSaved = 0;
    p->timeResidualCacheLookup = 0;
    p->nResidualRecCalls = 0;
    p->nResidualRecUnique = 0;
    p->nResidualRecDuplicate = 0;
    p->nResidualRecSamePage = 0;
    p->nResidualRecCrossPage = 0;
    p->nResidualRecFailHits = 0;
    p->nResidualRecSuccessDuplicate = 0;
    p->nResidualRecPayloadBytes = 0;
    memset( p->nResidualRecDuplicateDepth, 0,
        sizeof(p->nResidualRecDuplicateDepth) );
    p->timeResidualRecSaved = 0;
    p->timeResidualRecLookup = 0;
    p->ppRootCache = NULL;
    p->pRootCache = NULL;
    p->fUseSolvSched = 0;
    p->fSolvScheduleReady = 0;
    p->fSolvScheduleProfiled = 0;
    p->nSolvSchedulePivots = p->nSolvScheduleComplete = 0;
    p->timeSolvSchedule = 0;
    p->fProfilePivots = 0;
    p->fPairClassCache = 0;
    p->fGreedyPairRanked = Abc_ResubQualityOption("ABC_STRICT_GREEDY_PAIR_RANKED");
    p->nPairSigDup = 0;
    assert( p->pPairClassMasks == NULL );
    Vec_IntFreeP( &p->vPairSigClasses );
    Vec_IntFreeP( &p->vPairSigReps );
    Vec_IntFreeP( &p->vPairSigDupRows );
    p->fTopPivotProfileReady = 0;
    p->nTopPivotKind = p->nTopPivotRank = 0;
    p->nTopPivotCover = p->nTopPivotTotal = 0;
    p->nTopPivotNovel = p->nTopPivotRemain = 0;
    p->fTopPivotDuplicate = 0;
    p->nTopFrontier = p->nTopFrontierUnique = 0;
    p->nTopFrontierZeroNovel = 0;
    p->nTopFrontierCoverSum = p->nTopFrontierNovelSum = 0;
    p->fUseZero     = fUseZero;
    p->fUseXor      = fUseXor;
    p->fCarePairTruth = s_ResubCarePairTruth && !fUseXor;
    p->fDebug       = fDebug;
    p->fVerbose     = fVerbose;
    p->fVeryVerbose = fVeryVerbose;
    Abc_TtCopy( p->pSets[0], (word *)Vec_PtrEntry(vDivs, 0), nWords, 0 );
    Abc_TtCopy( p->pSets[1], (word *)Vec_PtrEntry(vDivs, 1), nWords, 0 );
    Vec_PtrClear( p->vDivs );
    Vec_PtrAppend( p->vDivs, vDivs );
    Vec_IntClear( p->vGates );
    Vec_IntClear( p->vUnateLits[0]    );
    Vec_IntClear( p->vUnateLits[1]    );
    Vec_IntClear( p->vNotUnateVars[0] );
    Vec_IntClear( p->vNotUnateVars[1] );
    Vec_IntClear( p->vUnatePairs[0]   );
    Vec_IntClear( p->vUnatePairs[1]   );
    Vec_IntClear( p->vUnateLitsW[0]   );
    Vec_IntClear( p->vUnateLitsW[1]   );
    Vec_IntClear( p->vUnatePairsW[0]  );
    Vec_IntClear( p->vUnatePairsW[1]  );
    Vec_IntClear( p->vBinateVars      );
    Vec_IntClear( p->vPairVars        );
    // Pair ids are local to one immutable iterator binding.  Recreate the
    // table before any vectors carrying these ids are rebuilt.
    Hsh_IntManStop( p->pPairHash );
    Vec_IntClear( p->vPairKeys );
    p->pPairHash = Hsh_IntManStart( p->vPairKeys, 2, 100 );
    // Exact remainder states are local to one root binding.  In particular,
    // the pass-owned manager must not carry them across ResumeStart() roots.
    Vec_IntClear( p->vResidualCacheBins );
    Vec_IntClear( p->vResidualCacheMeta );
    Vec_IntClear( p->vResidualCacheGates );
    Vec_WrdClear( p->vResidualCacheHashes );
    Vec_WrdClear( p->vResidualCacheMasks );
    Vec_WrdClear( p->vResidualCacheSolveTimes );
    Vec_IntClear( p->vSolvOrder );
    Vec_IntClear( p->vSolvDepth );
    Vec_IntClear( p->vSolvComplete );
    Vec_WrdClear( p->vSolvAmbiguity );
}
void Gia_ResbFree( Gia_ResbMan_t * p )
{
    assert( p->pPairClassMasks == NULL );
    Vec_IntFreeP( &p->vPairSigClasses );
    Vec_IntFreeP( &p->vPairSigReps );
    Vec_IntFreeP( &p->vPairSigDupRows );
    Vec_IntFree( p->vUnateLits[0]    );
    Vec_IntFree( p->vUnateLits[1]    );
    Vec_IntFree( p->vNotUnateVars[0] );
    Vec_IntFree( p->vNotUnateVars[1] );
    Vec_IntFree( p->vUnatePairs[0]   );
    Vec_IntFree( p->vUnatePairs[1]   );
    Vec_IntFree( p->vUnateLitsW[0]   );
    Vec_IntFree( p->vUnateLitsW[1]   );
    Vec_IntFree( p->vUnatePairsW[0]  );
    Vec_IntFree( p->vUnatePairsW[1]  );
    Vec_IntFree( p->vTopUnateLits[0] );
    Vec_IntFree( p->vTopUnateLits[1] );
    Vec_IntFree( p->vTopUnateLitsW[0] );
    Vec_IntFree( p->vTopUnateLitsW[1] );
    Vec_IntFree( p->vTopUnatePairs[0] );
    Vec_IntFree( p->vTopUnatePairs[1] );
    Vec_IntFree( p->vTopUnatePairsW[0] );
    Vec_IntFree( p->vTopUnatePairsW[1] );
    Vec_IntFree( p->vTopPivotNovel );
    Vec_IntFree( p->vTopPivotDuplicate );
    Vec_WrdFree( p->vTopPivotCovers );
    Vec_IntFree( p->vSecondPivotRanks );
    Vec_WrdFree( p->vSecondPivotCovers );
    Vec_IntFree( p->vSolvOrder );
    Vec_IntFree( p->vSolvDepth );
    Vec_IntFree( p->vSolvComplete );
    Vec_WrdFree( p->vSolvAmbiguity );
    Vec_WrdFree( p->vSolvClassMasks[0] );
    Vec_WrdFree( p->vSolvClassMasks[1] );
    Vec_IntFree( p->vSolvClassCounts[0] );
    Vec_IntFree( p->vSolvClassCounts[1] );
    Vec_IntFree( p->vSolvSelected );
    Vec_IntFree( p->vResidualCacheBins );
    Vec_IntFree( p->vResidualCacheMeta );
    Vec_IntFree( p->vResidualCacheGates );
    Vec_WrdFree( p->vResidualCacheHashes );
    Vec_WrdFree( p->vResidualCacheMasks );
    Vec_WrdFree( p->vResidualCacheSolveTimes );
    Vec_IntFree( p->vBinateVars      );
    Vec_IntFree( p->vPairVars        );
    Hsh_IntManStop( p->pPairHash );
    Vec_IntFree( p->vPairKeys );
    Vec_IntFree( p->vGates           );
    Vec_WrdFree( p->vSims            );
    Vec_PtrFree( p->vDivs            );
    Vec_WecFree( p->vSorter          );
    ABC_FREE( p->pSets[0] );
    ABC_FREE( p->pSets[1] );
    ABC_FREE( p->pDivA );
    ABC_FREE( p->pDivB );
    ABC_FREE( p );
}

static inline void Gia_ResbCopyIntVec( Vec_Int_t * vDest,
    Vec_Int_t * vSource )
{
    Vec_IntClear( vDest );
    Vec_IntAppend( vDest, vSource );
}

static void Gia_ResbSaveTopSummary( Gia_ResbMan_t * p )
{
    int n;
    for ( n = 0; n < 2; n++ )
    {
        Gia_ResbCopyIntVec( p->vTopUnateLits[n], p->vUnateLits[n] );
        Gia_ResbCopyIntVec( p->vTopUnateLitsW[n], p->vUnateLitsW[n] );
        Gia_ResbCopyIntVec( p->vTopUnatePairs[n], p->vUnatePairs[n] );
        Gia_ResbCopyIntVec( p->vTopUnatePairsW[n], p->vUnatePairsW[n] );
    }
    p->fTopCacheReady = 1;
}

static void Gia_ResbLoadTopSummary( Gia_ResbMan_t * p )
{
    int n;
    assert( p->fTopCacheReady );
    for ( n = 0; n < 2; n++ )
    {
        Gia_ResbCopyIntVec( p->vUnateLits[n], p->vTopUnateLits[n] );
        Gia_ResbCopyIntVec( p->vUnateLitsW[n], p->vTopUnateLitsW[n] );
        Gia_ResbCopyIntVec( p->vUnatePairs[n], p->vTopUnatePairs[n] );
        Gia_ResbCopyIntVec( p->vUnatePairsW[n], p->vTopUnatePairsW[n] );
    }
}

static Gia_ResbRootCache_t * Gia_ResbRootCacheAlloc( Gia_ResbMan_t * p )
{
    Gia_ResbRootCache_t * pCache = ABC_CALLOC( Gia_ResbRootCache_t, 1 );
    word * pSet;
    int n;
    pCache->nWords = p->nWords;
    pCache->nDivs = Vec_PtrSize(p->vDivs);
    pCache->nLimit = p->nLimit;
    pCache->nDivsMax = p->nDivsMax;
    pCache->fQualityNoTruncation = p->fQualityNoTruncation;
    pCache->fUseZero = p->fUseZero;
    pCache->fUseXor = p->fUseXor;
    pCache->fCarePairTruth = p->fCarePairTruth;
    pCache->nStage5Paths = p->nStage5Paths;
    pCache->nBinds = 1;
    pCache->vContextDivs = Vec_PtrAlloc( pCache->nDivs );
    Vec_PtrAppend( pCache->vContextDivs, p->vDivs );
    pCache->vContextSets = Vec_WrdAlloc( 2 * p->nWords );
    for ( n = 0; n < 2; n++ )
    {
        pSet = (word *)Vec_PtrEntry(p->vDivs, n);
        Vec_WrdPushArray( pCache->vContextSets, pSet, p->nWords );
    }
    // These vectors are swapped with the shared manager.  Allocate them
    // minimally so a root that only needs a handful of entries does not pay
    // the manager's deliberately generous default capacities.
    pCache->vResidualCacheBins = Vec_IntAlloc( 1 );
    pCache->vResidualCacheMeta = Vec_IntAlloc( 1 );
    pCache->vResidualCacheGates = Vec_IntAlloc( 1 );
    pCache->vResidualCacheHashes = Vec_WrdAlloc( 1 );
    pCache->vResidualCacheMasks = Vec_WrdAlloc( 1 );
    pCache->vResidualCacheSolveTimes = Vec_WrdAlloc( 1 );
    return pCache;
}

static int Gia_ResbRootCacheCompatible( Gia_ResbRootCache_t * pCache,
    Vec_Ptr_t * vDivs, int nWords, int nLimit, int nDivsMax,
    int fUseZero, int fUseXor, int nStage5Paths )
{
    word * pSets = Vec_WrdArray(pCache->vContextSets);
    int i;
    if ( pCache->nWords != nWords || pCache->nDivs != Vec_PtrSize(vDivs) ||
         pCache->nLimit != nLimit || pCache->nDivsMax != nDivsMax ||
         pCache->fUseZero != fUseZero || pCache->fUseXor != fUseXor ||
         pCache->fCarePairTruth != (s_ResubCarePairTruth && !fUseXor) ||
         pCache->nStage5Paths != nStage5Paths ||
         pCache->fQualityNoTruncation != Abc_ResubQualityNoTruncation() )
        return 0;
    if ( memcmp(pSets, Vec_PtrEntry(vDivs, 0), sizeof(word) * nWords) ||
         memcmp(pSets + nWords, Vec_PtrEntry(vDivs, 1),
             sizeof(word) * nWords) )
        return 0;
    // The SEQ snapshot and its simulation store are immutable for this pass.
    // Exact pointer/order comparison therefore identifies the same physical
    // divisor functions without copying B complete signatures per root.
    for ( i = 2; i < Vec_PtrSize(vDivs); i++ )
        if ( Vec_PtrEntry(pCache->vContextDivs, i) !=
             Vec_PtrEntry(vDivs, i) )
            return 0;
    return 1;
}

static void Gia_ResbRootCacheSwap( Gia_ResbMan_t * p,
    Gia_ResbRootCache_t * pCache )
{
    Vec_Int_t * vInt;
    Vec_Wrd_t * vWrd;
    vInt = p->vResidualCacheBins;
    p->vResidualCacheBins = pCache->vResidualCacheBins;
    pCache->vResidualCacheBins = vInt;
    vInt = p->vResidualCacheMeta;
    p->vResidualCacheMeta = pCache->vResidualCacheMeta;
    pCache->vResidualCacheMeta = vInt;
    vInt = p->vResidualCacheGates;
    p->vResidualCacheGates = pCache->vResidualCacheGates;
    pCache->vResidualCacheGates = vInt;
    vWrd = p->vResidualCacheHashes;
    p->vResidualCacheHashes = pCache->vResidualCacheHashes;
    pCache->vResidualCacheHashes = vWrd;
    vWrd = p->vResidualCacheMasks;
    p->vResidualCacheMasks = pCache->vResidualCacheMasks;
    pCache->vResidualCacheMasks = vWrd;
    vWrd = p->vResidualCacheSolveTimes;
    p->vResidualCacheSolveTimes = pCache->vResidualCacheSolveTimes;
    pCache->vResidualCacheSolveTimes = vWrd;
}

static void Gia_ResbRootCacheFree( Gia_ResbRootCache_t * pCache )
{
    if ( pCache == NULL )
        return;
    Vec_PtrFree( pCache->vContextDivs );
    Vec_WrdFree( pCache->vContextSets );
    Vec_IntFree( pCache->vResidualCacheBins );
    Vec_IntFree( pCache->vResidualCacheMeta );
    Vec_IntFree( pCache->vResidualCacheGates );
    Vec_WrdFree( pCache->vResidualCacheHashes );
    Vec_WrdFree( pCache->vResidualCacheMasks );
    Vec_WrdFree( pCache->vResidualCacheSolveTimes );
    ABC_FREE( pCache );
}

void Abc_ResubRootCacheStop( void * pVoid )
{
    Gia_ResbRootCacheFree( (Gia_ResbRootCache_t *)pVoid );
}

static void Gia_ResbRootCacheEnsureAttached( Gia_ResbMan_t * p )
{
    Gia_ResbRootCache_t * pCache;
    if ( p->ppRootCache == NULL || p->pRootCache != NULL )
        return;
    assert( *p->ppRootCache == NULL );
    pCache = Gia_ResbRootCacheAlloc( p );
    *p->ppRootCache = pCache;
    p->pRootCache = pCache;
    Gia_ResbRootCacheSwap( p, pCache );
}

enum
{
    GIA_RESUB_RESIDUAL_KIND = 0,
    GIA_RESUB_RESIDUAL_USE_OR,
    GIA_RESUB_RESIDUAL_LIMIT,
    GIA_RESUB_RESIDUAL_PATH,
    GIA_RESUB_RESIDUAL_RESULT,
    GIA_RESUB_RESIDUAL_GATE_START,
    GIA_RESUB_RESIDUAL_GATE_SIZE,
    GIA_RESUB_RESIDUAL_SECOND_RANK,
    GIA_RESUB_RESIDUAL_SECOND_COVER,
    GIA_RESUB_RESIDUAL_DIVERSITY_NEW,
    GIA_RESUB_RESIDUAL_DIVERSITY_SYM,
    GIA_RESUB_RESIDUAL_BIND,
    GIA_RESUB_RESIDUAL_META_SIZE
};

#define GIA_RESUB_RESIDUAL_UNRESOLVED  (-2)
#define GIA_RESUB_RESIDUAL_SUCCESS_ONLY (-3)

// Cache one deterministic remainder path below a Stage-5 pivot.  Path one is
// the historical primary recursion; later path indices identify the one-time
// second-pivot choice before recursion returns to primary greedy.  The exact
// OFF/ON masks are compared after hashing, so hash collisions cannot merge
// candidates.  The current literal/pair pivot is intentionally absent from
// the value and is reattached by the caller on every successful hit.
static word Gia_ResbResidualCacheHash( Gia_ResbMan_t * p, int PivotKind,
    int fUseOr, int nLimit, int PathIndex )
{
    word Hash = ABC_CONST(1469598103934665603);
    int i, n;
    Hash ^= (word)PivotKind;
    Hash *= ABC_CONST(1099511628211);
    Hash ^= (word)fUseOr;
    Hash *= ABC_CONST(1099511628211);
    Hash ^= (word)nLimit;
    Hash *= ABC_CONST(1099511628211);
    Hash ^= (word)PathIndex;
    Hash *= ABC_CONST(1099511628211);
    for ( n = 0; n < 2; n++ )
        for ( i = 0; i < p->nWords; i++ )
        {
            Hash ^= p->pSets[n][i];
            Hash *= ABC_CONST(1099511628211);
        }
    return Hash;
}

static void Gia_ResbResidualCacheRehash( Gia_ResbMan_t * p, int nBins )
{
    int Entry, Slot, Mask = nBins - 1;
    word Hash;
    assert( nBins >= 2 && !(nBins & Mask) );
    Vec_IntFill( p->vResidualCacheBins, nBins, 0 );
    Vec_WrdForEachEntry( p->vResidualCacheHashes, Hash, Entry )
    {
        Slot = (int)Hash & Mask;
        while ( Vec_IntEntry(p->vResidualCacheBins, Slot) )
            Slot = (Slot + 1) & Mask;
        Vec_IntWriteEntry( p->vResidualCacheBins, Slot, Entry + 1 );
    }
}

static int Gia_ResbResidualCacheKeyEqual( Gia_ResbMan_t * p, int Entry,
    int PivotKind, int fUseOr, int nLimit, int PathIndex )
{
    int iMeta = Entry * GIA_RESUB_RESIDUAL_META_SIZE;
    word * pMasks = Vec_WrdEntryP( p->vResidualCacheMasks,
        Entry * 2 * p->nWords );
    return Vec_IntEntry(p->vResidualCacheMeta,
               iMeta + GIA_RESUB_RESIDUAL_KIND) == PivotKind &&
           Vec_IntEntry(p->vResidualCacheMeta,
               iMeta + GIA_RESUB_RESIDUAL_USE_OR) == fUseOr &&
           Vec_IntEntry(p->vResidualCacheMeta,
               iMeta + GIA_RESUB_RESIDUAL_LIMIT) == nLimit &&
           Vec_IntEntry(p->vResidualCacheMeta,
               iMeta + GIA_RESUB_RESIDUAL_PATH) == PathIndex &&
           !memcmp( pMasks, p->pSets[0], sizeof(word) * p->nWords ) &&
           !memcmp( pMasks + p->nWords, p->pSets[1],
               sizeof(word) * p->nWords );
}

static int Gia_ResbResidualCacheFindOrAdd( Gia_ResbMan_t * p,
    int PivotKind, int fUseOr, int nLimit, int PathIndex, int * pfFound )
{
    word Hash;
    int nEntries, nBins;
    int Entry, Slot, Mask;
    abctime clk = p->fProfilePivots ? Abc_Clock() : 0;
    Gia_ResbRootCacheEnsureAttached( p );
    Hash = Gia_ResbResidualCacheHash( p, PivotKind, fUseOr, nLimit,
        PathIndex );
    if ( PivotKind && PathIndex > 1 )
        p->nMultiPathCacheLookups++;
    nEntries = Vec_WrdSize(p->vResidualCacheHashes);
    nBins = Vec_IntSize(p->vResidualCacheBins);
    if ( nBins == 0 )
        Gia_ResbResidualCacheRehash( p, 16 );
    else if ( 2 * (nEntries + 1) >= nBins )
        Gia_ResbResidualCacheRehash( p, 2 * nBins );
    nBins = Vec_IntSize(p->vResidualCacheBins);
    Mask = nBins - 1;
    Slot = (int)Hash & Mask;
    while ( (Entry = Vec_IntEntry(p->vResidualCacheBins, Slot) - 1) >= 0 )
    {
        if ( Vec_WrdEntry(p->vResidualCacheHashes, Entry) == Hash &&
             Gia_ResbResidualCacheKeyEqual(p, Entry, PivotKind, fUseOr,
                 nLimit, PathIndex) )
        {
            int iMeta = Entry * GIA_RESUB_RESIDUAL_META_SIZE;
            int fCrossPage = Vec_IntEntry(p->vResidualCacheMeta,
                iMeta + GIA_RESUB_RESIDUAL_BIND) !=
                p->iResidualCacheBind;
            if ( PivotKind )
            {
                p->nResidualCacheLookups++;
                p->nResidualCacheHitsTotal++;
                p->nResidualCacheSamePageHits += !fCrossPage;
                p->nResidualCacheCrossPageHits += fCrossPage;
                if ( p->fProfilePivots )
                    p->timeResidualCacheLookup += Abc_Clock() - clk;
                p->nMultiPathCacheHits += PathIndex > 1;
            }
            else
            {
                p->nResidualRecDuplicate++;
                p->nResidualRecSamePage += !fCrossPage;
                p->nResidualRecCrossPage += fCrossPage;
                p->nResidualRecDuplicateDepth[Abc_MinInt(
                    p->nResidualRecDepth, 3)]++;
                if ( p->fProfilePivots )
                    p->timeResidualRecLookup += Abc_Clock() - clk;
            }
            *pfFound = 1;
            return Entry;
        }
        Slot = (Slot + 1) & Mask;
    }
    Entry = nEntries;
    Vec_WrdPush( p->vResidualCacheHashes, Hash );
    Vec_WrdPushArray( p->vResidualCacheMasks, p->pSets[0], p->nWords );
    Vec_WrdPushArray( p->vResidualCacheMasks, p->pSets[1], p->nWords );
    Vec_IntPush( p->vResidualCacheMeta, PivotKind );
    Vec_IntPush( p->vResidualCacheMeta, fUseOr );
    Vec_IntPush( p->vResidualCacheMeta, nLimit );
    Vec_IntPush( p->vResidualCacheMeta, PathIndex );
    Vec_IntPush( p->vResidualCacheMeta, GIA_RESUB_RESIDUAL_UNRESOLVED );
    Vec_IntPush( p->vResidualCacheMeta, 0 );
    Vec_IntPush( p->vResidualCacheMeta, 0 );
    Vec_IntPush( p->vResidualCacheMeta, 0 );
    Vec_IntPush( p->vResidualCacheMeta, 0 );
    Vec_IntPush( p->vResidualCacheMeta, 0 );
    Vec_IntPush( p->vResidualCacheMeta, 0 );
    Vec_IntPush( p->vResidualCacheMeta, p->iResidualCacheBind );
    Vec_WrdPush( p->vResidualCacheSolveTimes, 0 );
    Vec_IntWriteEntry( p->vResidualCacheBins, Slot, Entry + 1 );
    if ( PivotKind )
        p->nResidualCachePayloadBytes +=
            sizeof(word) * (2 * p->nWords + 2) +
            sizeof(int) * GIA_RESUB_RESIDUAL_META_SIZE;
    else
        p->nResidualRecPayloadBytes +=
            sizeof(word) * (2 * p->nWords + 2) +
            sizeof(int) * GIA_RESUB_RESIDUAL_META_SIZE;
    if ( PivotKind && PathIndex > 1 )
    {
        p->nMultiPathCacheEntries++;
        p->nMultiPathCachePayloadBytes +=
            sizeof(word) * (2 * p->nWords + 2) +
            sizeof(int) * GIA_RESUB_RESIDUAL_META_SIZE;
    }
    if ( PivotKind )
    {
        p->nResidualCacheLookups++;
        p->nResidualCacheMisses++;
        if ( p->fProfilePivots )
            p->timeResidualCacheLookup += Abc_Clock() - clk;
    }
    else
    {
        p->nResidualRecUnique++;
        if ( p->fProfilePivots )
            p->timeResidualRecLookup += Abc_Clock() - clk;
    }
    *pfFound = 0;
    return Entry;
}

static void Gia_ResbResidualCacheStore( Gia_ResbMan_t * p, int Entry,
    int iResLit, abctime SolveTime )
{
    int iMeta = Entry * GIA_RESUB_RESIDUAL_META_SIZE;
    int GateStart = Vec_IntSize(p->vResidualCacheGates);
    int GateSize = iResLit >= 0 ? Vec_IntSize(p->vGates) : 0;
    assert( Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_RESULT) ==
        GIA_RESUB_RESIDUAL_UNRESOLVED );
    assert( !(GateSize & 1) );
    if ( GateSize )
        Vec_IntPushArray( p->vResidualCacheGates, Vec_IntArray(p->vGates),
            GateSize );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_RESULT, iResLit );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_GATE_START, GateStart );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_GATE_SIZE, GateSize );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_SECOND_RANK, p->nSecondPivotRank );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_SECOND_COVER, p->nSecondPivotCover );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_DIVERSITY_NEW, p->nSecondPivotNew );
    Vec_IntWriteEntry( p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_DIVERSITY_SYM, p->nSecondPivotSym );
    Vec_WrdWriteEntry( p->vResidualCacheSolveTimes, Entry,
        (word)SolveTime );
    p->nResidualCachePayloadBytes += sizeof(int) * GateSize;
    if ( Vec_IntEntry(p->vResidualCacheMeta,
            iMeta + GIA_RESUB_RESIDUAL_PATH) > 1 )
        p->nMultiPathCachePayloadBytes += sizeof(int) * GateSize;
}

static int Gia_ResbResidualCacheLoad( Gia_ResbMan_t * p, int Entry,
    int PivotKind )
{
    int iMeta = Entry * GIA_RESUB_RESIDUAL_META_SIZE;
    int iResLit = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_RESULT);
    int GateStart = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_GATE_START);
    int GateSize = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_GATE_SIZE);
    assert( PivotKind == 1 || PivotKind == 2 );
    assert( iResLit != GIA_RESUB_RESIDUAL_UNRESOLVED );
    assert( iResLit != GIA_RESUB_RESIDUAL_SUCCESS_ONLY );
    Vec_IntClear( p->vGates );
    if ( iResLit >= 0 && GateSize )
        Vec_IntPushArray( p->vGates,
            Vec_IntArray(p->vResidualCacheGates) + GateStart, GateSize );
    p->nSecondPivotRank = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_SECOND_RANK);
    p->nSecondPivotCover = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_SECOND_COVER);
    p->nSecondPivotNew = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_DIVERSITY_NEW);
    p->nSecondPivotSym = Vec_IntEntry(p->vResidualCacheMeta,
        iMeta + GIA_RESUB_RESIDUAL_DIVERSITY_SYM);
    p->fSecondPivotSelected = p->nSecondPivotRank > 0;
    p->nResidualCacheHits[PivotKind-1][iResLit >= 0]++;
    p->nResidualCacheFailHits += iResLit < 0;
    p->nResidualCacheSuccessHits += iResLit >= 0;
    if ( Vec_IntEntry(p->vResidualCacheMeta,
            iMeta + GIA_RESUB_RESIDUAL_PATH) > 1 )
    {
        p->nMultiPathCacheFailHits += iResLit < 0;
        p->nMultiPathCacheSuccessHits += iResLit >= 0;
    }
    p->timeResidualCacheSaved +=
        (abctime)Vec_WrdEntry(p->vResidualCacheSolveTimes, Entry);
    return iResLit;
}

/**Function*************************************************************

  Synopsis    [Print resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManResubPrintNode( Vec_Int_t * vRes, int nVars, int Node, int fCompl )
{
    extern void Gia_ManResubPrintLit( Vec_Int_t * vRes, int nVars, int iLit );
    int iLit0 = Vec_IntEntry( vRes, 2*Node + 0 );
    int iLit1 = Vec_IntEntry( vRes, 2*Node + 1 );
    assert( iLit0 != iLit1 );
    if ( iLit0 > iLit1 && Abc_LitIsCompl(fCompl) ) // xor
    {
        printf( "~" );
        fCompl = 0;
    }
    printf( "(" );
    Gia_ManResubPrintLit( vRes, nVars, Abc_LitNotCond(iLit0, fCompl) );
    printf( " %c ", iLit0 > iLit1 ? '^' : (fCompl ? '|' : '&') );
    Gia_ManResubPrintLit( vRes, nVars, Abc_LitNotCond(iLit1, fCompl) );
    printf( ")" );
}
void Gia_ManResubPrintLit( Vec_Int_t * vRes, int nVars, int iLit )
{
    if ( Abc_Lit2Var(iLit) < nVars )
    {
        if ( nVars < 26 )
            printf( "%s%c", Abc_LitIsCompl(iLit) ? "~":"", 'a' + Abc_Lit2Var(iLit)-2 );
        else
            printf( "%si%d", Abc_LitIsCompl(iLit) ? "~":"", Abc_Lit2Var(iLit)-2 );
    }
    else
        Gia_ManResubPrintNode( vRes, nVars, Abc_Lit2Var(iLit) - nVars, Abc_LitIsCompl(iLit) );
}
int Gia_ManResubPrint( Vec_Int_t * vRes, int nVars )
{
    int iTopLit;
    if ( Vec_IntSize(vRes) == 0 )
        return printf( "none" );
    assert( Vec_IntSize(vRes) % 2 == 1 );
    iTopLit = Vec_IntEntryLast(vRes);
    if ( iTopLit == 0 )
        return printf( "const0" );
    if ( iTopLit == 1 )
        return printf( "const1" );
    Gia_ManResubPrintLit( vRes, nVars, iTopLit );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Verify resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gia_ManResubRecipeIsWellFormed( Gia_ResbMan_t * p )
{
    int nVars = Vec_PtrSize(p->vDivs);
    int nGates, iTopLit, i, iLit0, iLit1;
    if ( Vec_IntSize(p->vGates) == 0 ||
         !(Vec_IntSize(p->vGates) & 1) )
        return 0;
    nGates = Vec_IntSize(p->vGates) / 2;
    iTopLit = Vec_IntEntryLast(p->vGates);
    if ( iTopLit < 0 || (Abc_Lit2Var(iTopLit) >= nVars &&
         Abc_Lit2Var(iTopLit) - nVars >= nGates) )
        return 0;
    Vec_IntForEachEntryDouble( p->vGates, iLit0, iLit1, i )
    {
        int iGate = i / 2;
        int iVar0, iVar1;
        if ( iLit0 < 0 || iLit1 < 0 )
            return 0;
        iVar0 = Abc_Lit2Var(iLit0);
        iVar1 = Abc_Lit2Var(iLit1);
        if ( iVar0 >= nVars + iGate || iVar1 >= nVars + iGate )
            return 0;
        // Reversed fanins encode XOR in this resub format.  Root-only
        // recipes request ANDs exclusively, and XOR fanins are plain.
        if ( iVar0 > iVar1 && (!p->fUseXor ||
             Abc_LitIsCompl(iLit0) || Abc_LitIsCompl(iLit1)) )
            return 0;
        // Equal physical fanins are a degenerate AND (x&x or x&!x) in root
        // mode.  An XOR-enabled mixed recipe would make the operation tag
        // ambiguous, so reject that shape.
        if ( iVar0 == iVar1 && p->fUseXor )
            return 0;
    }
    return 1;
}

int Gia_ManResubVerify( Gia_ResbMan_t * p, word * pFunc )
{
    int nVars = Vec_PtrSize(p->vDivs);
    int nGates, iTopLit, RetValue;
    word * pDivRes; 
    if ( Vec_IntSize(p->vGates) == 0 )
        return -1;
    // A recipe is untrusted search output.  Verification must reject a
    // malformed candidate, not terminate the whole ABC process.
    if ( !Gia_ManResubRecipeIsWellFormed(p) )
        return 0;
    nGates = Vec_IntSize(p->vGates) / 2;
    iTopLit = Vec_IntEntryLast(p->vGates);
    if ( iTopLit < 0 )
        return 0;
    if ( iTopLit == 0 )
    {
        if ( pFunc ) Abc_TtClear( pFunc, p->nWords );
        return Abc_TtIsConst0( p->pSets[1], p->nWords );
    }
    if ( iTopLit == 1 )
    {
        if ( pFunc ) Abc_TtFill( pFunc, p->nWords );
        return Abc_TtIsConst0( p->pSets[0], p->nWords );
    }
    if ( Abc_Lit2Var(iTopLit) < nVars )
        pDivRes = (word *)Vec_PtrEntry( p->vDivs, Abc_Lit2Var(iTopLit) );
    else
    {
        int i, iLit0, iLit1;
        int iTopGate = Abc_Lit2Var(iTopLit) - nVars;
        if ( iTopGate < 0 || iTopGate >= nGates )
            return 0;
        Vec_WrdFill( p->vSims, p->nWords * nGates, 0 );
        Vec_IntForEachEntryDouble( p->vGates, iLit0, iLit1, i )
        {
            int iVar0 = Abc_Lit2Var(iLit0);
            int iVar1 = Abc_Lit2Var(iLit1);
            word * pDiv0 = iVar0 < nVars ? (word *)Vec_PtrEntry(p->vDivs, iVar0) : Vec_WrdEntryP(p->vSims, p->nWords*(iVar0 - nVars));
            word * pDiv1 = iVar1 < nVars ? (word *)Vec_PtrEntry(p->vDivs, iVar1) : Vec_WrdEntryP(p->vSims, p->nWords*(iVar1 - nVars));
            word * pDiv  = Vec_WrdEntryP(p->vSims, p->nWords*i/2);
            if ( iVar0 < iVar1 )
                Abc_TtAndCompl( pDiv, pDiv0, Abc_LitIsCompl(iLit0), pDiv1, Abc_LitIsCompl(iLit1), p->nWords );
            else if ( iVar0 > iVar1 )
            {
                Abc_TtXor( pDiv, pDiv0, pDiv1, p->nWords, 0 );
            }
            else
                Abc_TtAndCompl( pDiv, pDiv0, Abc_LitIsCompl(iLit0),
                    pDiv1, Abc_LitIsCompl(iLit1), p->nWords );
        }
        pDivRes = Vec_WrdEntryP( p->vSims, p->nWords*iTopGate );
    }
    if ( Abc_LitIsCompl(iTopLit) )
        RetValue = !Abc_TtIntersectOne(p->pSets[1], 0, pDivRes, 0, p->nWords) && !Abc_TtIntersectOne(p->pSets[0], 0, pDivRes, 1, p->nWords);
    else
        RetValue = !Abc_TtIntersectOne(p->pSets[0], 0, pDivRes, 0, p->nWords) && !Abc_TtIntersectOne(p->pSets[1], 0, pDivRes, 1, p->nWords);
    if ( pFunc ) Abc_TtCopy( pFunc, pDivRes, p->nWords, Abc_LitIsCompl(iTopLit) );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Construct AIG manager from gates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManConstructFromMap( Gia_Man_t * pNew, Vec_Int_t * vGates, int nVars, Vec_Int_t * vUsed, Vec_Int_t * vCopy, int fHash )
{
    int i, iLit0, iLit1, iLitRes, iTopLit = Vec_IntEntryLast( vGates );
    (void)iTopLit;
    assert( Vec_IntSize(vUsed) == nVars );
    assert( Vec_IntSize(vGates) > 1 );
    assert( Vec_IntSize(vGates) % 2 == 1 );
    assert( Abc_Lit2Var(iTopLit)-nVars == Vec_IntSize(vGates)/2-1 );
    Vec_IntClear( vCopy );
    Vec_IntForEachEntryDouble( vGates, iLit0, iLit1, i )
    {
        int iVar0 = Abc_Lit2Var(iLit0);
        int iVar1 = Abc_Lit2Var(iLit1);
        int iRes0 = iVar0 < nVars ? Vec_IntEntry(vUsed, iVar0) : Vec_IntEntry(vCopy, iVar0 - nVars);
        int iRes1 = iVar1 < nVars ? Vec_IntEntry(vUsed, iVar1) : Vec_IntEntry(vCopy, iVar1 - nVars);
        if ( iVar0 < iVar1 )
        {
            if ( fHash )
                iLitRes = Gia_ManHashAnd( pNew, Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)), Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) );
            else
                iLitRes = Gia_ManAppendAnd( pNew, Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)), Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) );
        }
        else if ( iVar0 > iVar1 )
        {
            assert( !Abc_LitIsCompl(iLit0) );
            assert( !Abc_LitIsCompl(iLit1) );
            if ( fHash )
                iLitRes = Gia_ManHashXor( pNew, Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)), Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) );
            else
                iLitRes = Gia_ManAppendXor( pNew, Abc_LitNotCond(iRes0, Abc_LitIsCompl(iLit0)), Abc_LitNotCond(iRes1, Abc_LitIsCompl(iLit1)) );
        }
        else { assert( 0 ); abort(); }
        Vec_IntPush( vCopy, iLitRes );
    }
    assert( Vec_IntSize(vCopy) == Vec_IntSize(vGates)/2 );
    iLitRes = Vec_IntEntry( vCopy, Vec_IntSize(vGates)/2-1 );
    return iLitRes;
}
Gia_Man_t * Gia_ManConstructFromGates( Vec_Wec_t * vFuncs, int nDivs )
{
    Vec_Int_t * vGates; int i, k, iLit;
    Vec_Int_t * vCopy = Vec_IntAlloc( 100 );
    Vec_Int_t * vUsed = Vec_IntStartFull( nDivs );
    Gia_Man_t * pNew = Gia_ManStart( 100 );
    pNew->pName = Abc_UtilStrsav( "resub" );
    Vec_WecForEachLevel( vFuncs, vGates, i )
    {
        assert( Vec_IntSize(vGates) % 2 == 1 );
        Vec_IntForEachEntry( vGates, iLit, k )
        {
            int iVar = Abc_Lit2Var(iLit);
            if ( iVar > 0 && iVar < nDivs && Vec_IntEntry(vUsed, iVar) == -1 )
                Vec_IntWriteEntry( vUsed, iVar, Gia_ManAppendCi(pNew) );
        }
    }
    Vec_WecForEachLevel( vFuncs, vGates, i )
    {
        int iLitRes, iTopLit = Vec_IntEntryLast( vGates );
        if ( Abc_Lit2Var(iTopLit) == 0 )
            iLitRes = 0;
        else if ( Abc_Lit2Var(iTopLit) < nDivs )
            iLitRes = Vec_IntEntry( vUsed, Abc_Lit2Var(iTopLit) );
        else
            iLitRes = Gia_ManConstructFromMap( pNew, vGates, nDivs, vUsed, vCopy, 0 );
        Gia_ManAppendCo( pNew, Abc_LitNotCond( iLitRes, Abc_LitIsCompl(iTopLit) ) );
    }
    Vec_IntFree( vCopy );
    Vec_IntFree( vUsed );
    return pNew;
}
Gia_Man_t * Gia_ManConstructFromGates2( Vec_Wec_t * vFuncs, Vec_Wec_t * vDivs, int nObjs, Vec_Int_t ** pvSupp )
{
    Vec_Int_t * vGates; int i, k, iVar, iLit;
    Vec_Int_t * vSupp  = Vec_IntAlloc( 100 );
    Vec_Int_t * vCopy  = Vec_IntAlloc( 100 );
    Vec_Wec_t * vUseds = Vec_WecStart( Vec_WecSize(vDivs) );
    Vec_Int_t * vMap   = Vec_IntStartFull( nObjs );
    Gia_Man_t * pNew   = Gia_ManStart( 100 );
    pNew->pName = Abc_UtilStrsav( "resub" );
    assert( Vec_WecSize(vFuncs) == Vec_WecSize(vDivs) );
    Vec_WecForEachLevel( vFuncs, vGates, i )
    {
        Vec_Int_t * vDiv = Vec_WecEntry( vDivs, i );
        assert( Vec_IntSize(vGates) % 2 == 1 );
        Vec_IntForEachEntry( vGates, iLit, k )
        {
            int iVar = Abc_Lit2Var(iLit);
            if ( iVar > 0 && iVar < Vec_IntSize(vDiv) && Vec_IntEntry(vMap, Vec_IntEntry(vDiv, iVar)) == -1 )
                Vec_IntWriteEntry( vMap, Vec_IntPushReturn(vSupp, Vec_IntEntry(vDiv, iVar)), 0 );
        }
    }
    Vec_IntSort( vSupp, 0 );
    Vec_IntForEachEntry( vSupp, iVar, k )
        Vec_IntWriteEntry( vMap, iVar, Gia_ManAppendCi(pNew) );
    Vec_WecForEachLevel( vFuncs, vGates, i )
    {
        Vec_Int_t * vDiv  = Vec_WecEntry( vDivs, i );
        Vec_Int_t * vUsed = Vec_WecEntry( vUseds, i );
        Vec_IntFill( vUsed, Vec_IntSize(vDiv), -1 );
        Vec_IntForEachEntry( vGates, iLit, k )
        {
            int iVar = Abc_Lit2Var(iLit);
            if ( iVar > 0 && iVar < Vec_IntSize(vDiv) )
            {
                assert( Vec_IntEntry(vMap, Vec_IntEntry(vDiv, iVar)) > 0 );
                Vec_IntWriteEntry( vUsed, iVar, Vec_IntEntry(vMap, Vec_IntEntry(vDiv, iVar)) );
            }
        }
    }
    Vec_WecForEachLevel( vFuncs, vGates, i )
    {
        Vec_Int_t * vDiv  = Vec_WecEntry( vDivs, i );
        Vec_Int_t * vUsed = Vec_WecEntry( vUseds, i );
        int iLitRes, iTopLit = Vec_IntEntryLast( vGates );
        if ( Abc_Lit2Var(iTopLit) == 0 )
            iLitRes = 0;
        else if ( Abc_Lit2Var(iTopLit) < Vec_IntSize(vDiv) )
            iLitRes = Vec_IntEntry( vUsed, Abc_Lit2Var(iTopLit) );
        else
            iLitRes = Gia_ManConstructFromMap( pNew, vGates, Vec_IntSize(vDiv), vUsed, vCopy, 0 );
        Gia_ManAppendCo( pNew, Abc_LitNotCond( iLitRes, Abc_LitIsCompl(iTopLit) ) );
    }
    Vec_IntFree( vMap );
    Vec_IntFree( vCopy );
    Vec_WecFree( vUseds );
    if ( pvSupp )
        *pvSupp = vSupp;
    else
        Vec_IntFree( vSupp );
    return pNew;
}
Vec_Int_t * Gia_ManToGates( Gia_Man_t * p )
{
    Vec_Int_t * vRes = Vec_IntAlloc( 2*Gia_ManAndNum(p) + 1 );
    Gia_Obj_t * pRoot = Gia_ManCo( p, 0 );
    int iRoot = Gia_ObjFaninId0p(p, pRoot) - 1;
    int nVars = Gia_ManCiNum(p);
    assert( Gia_ManCoNum(p) == 1 );
    if ( iRoot == -1 )
        Vec_IntPush( vRes, Gia_ObjFaninC0(pRoot) );
    else if ( iRoot < nVars )
        Vec_IntPush( vRes, 4 + Abc_Var2Lit(iRoot, Gia_ObjFaninC0(pRoot)) );
    else
    {
        Gia_Obj_t * pObj, * pLast = NULL; int i;
        Gia_ManForEachCi( p, pObj, i )
            assert( Gia_ObjId(p, pObj) == i+1 );
        Gia_ManForEachAnd( p, pObj, i )
        {
            int iLit0 = Abc_Var2Lit( Gia_ObjFaninId0(pObj, i) - 1, Gia_ObjFaninC0(pObj) );
            int iLit1 = Abc_Var2Lit( Gia_ObjFaninId1(pObj, i) - 1, Gia_ObjFaninC1(pObj) );
            if ( iLit0 > iLit1 )
                iLit0 ^= iLit1, iLit1 ^= iLit0, iLit0 ^= iLit1;
            Vec_IntPushTwo( vRes, 4 + iLit0, 4 + iLit1 );
            pLast = pObj;
        }
        assert( pLast == Gia_ObjFanin0(pRoot) );
        Vec_IntPush( vRes, 4 + Abc_Var2Lit(iRoot, Gia_ObjFaninC0(pRoot)) );
    }
    assert( Vec_IntSize(vRes) == 2*Gia_ManAndNum(p) + 1 );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Construct AIG manager from gates.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManInsertOrder_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vObjs, Vec_Wec_t * vFuncs, Vec_Int_t * vNodes )
{
    Gia_Obj_t * pObj = Gia_ManObj( p, iObj );
    if ( iObj == 0 )
        return;
    if ( pObj->fPhase )
    {
        int nVars = Gia_ManObjNum(p);
        int k, iLit, Index = Vec_IntFind( vObjs, iObj );
        Vec_Int_t * vGates = Vec_WecEntry( vFuncs, Index );
        assert( Gia_ObjIsCo(pObj) || Gia_ObjIsAnd(pObj) );
        Vec_IntForEachEntry( vGates, iLit, k )
            if ( Abc_Lit2Var(iLit) < nVars )
                Gia_ManInsertOrder_rec( p, Abc_Lit2Var(iLit), vObjs, vFuncs, vNodes );
    }
    else if ( Gia_ObjIsCo(pObj) )
        Gia_ManInsertOrder_rec( p, Gia_ObjFaninId0p(p, pObj), vObjs, vFuncs, vNodes );
    else if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_ManInsertOrder_rec( p, Gia_ObjFaninId0p(p, pObj), vObjs, vFuncs, vNodes );
        Gia_ManInsertOrder_rec( p, Gia_ObjFaninId1p(p, pObj), vObjs, vFuncs, vNodes );
    }
    else assert( Gia_ObjIsCi(pObj) );
    if ( !Gia_ObjIsCi(pObj) )
        Vec_IntPush( vNodes, iObj );
}
Vec_Int_t * Gia_ManInsertOrder( Gia_Man_t * p, Vec_Int_t * vObjs, Vec_Wec_t * vFuncs )
{
    int i, Id;
    Vec_Int_t * vNodes = Vec_IntAlloc( Gia_ManObjNum(p) );
    Gia_ManForEachCoId( p, Id, i )
        Gia_ManInsertOrder_rec( p, Id, vObjs, vFuncs, vNodes );
    return vNodes;
}
Gia_Man_t * Gia_ManInsertFromGates( Gia_Man_t * p, Vec_Int_t * vObjs, Vec_Wec_t * vFuncs )
{
    Gia_Man_t * pNew, * pTemp; 
    Gia_Obj_t * pObj; 
    int i, nVars = Gia_ManObjNum(p);
    Vec_Int_t * vUsed = Vec_IntStartFull( nVars );
    Vec_Int_t * vNodes, * vCopy = Vec_IntAlloc(100);
    Gia_ManForEachObjVec( vObjs, p, pObj, i )
        pObj->fPhase = 1;
    vNodes = Gia_ManInsertOrder( p, vObjs, vFuncs );
    pNew = Gia_ManStart( Gia_ManObjNum(p) + 1000 );
    Gia_ManHashStart( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        if ( !pObj->fPhase )
        {
            if ( Gia_ObjIsCo(pObj) )
                pObj->Value = Gia_ObjFanin0Copy(pObj);
            else if ( Gia_ObjIsAnd(pObj) )            
                pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
            else assert( 0 );
        }
        else
        {
            int k, iLit, Index = Vec_IntFind( vObjs, Gia_ObjId(p, pObj) );
            Vec_Int_t * vGates = Vec_WecEntry( vFuncs, Index );
            int iLitRes, iTopLit = Vec_IntEntryLast( vGates );
            if ( Abc_Lit2Var(iTopLit) == 0 )
                iLitRes = 0;
            else if ( Abc_Lit2Var(iTopLit) < nVars )
                iLitRes = Gia_ManObj(p, Abc_Lit2Var(iTopLit))->Value;
            else
            {
                Vec_IntForEachEntry( vGates, iLit, k )
                    Vec_IntWriteEntry( vUsed, Abc_Lit2Var(iLit), Gia_ManObj(p, Abc_Lit2Var(iLit))->Value );
                iLitRes = Gia_ManConstructFromMap( pNew, vGates, nVars, vUsed, vCopy, 1 );
                Vec_IntForEachEntry( vGates, iLit, k )
                    Vec_IntWriteEntry( vUsed, Abc_Lit2Var(iLit), -1 );
            }
            pObj->Value = Abc_LitNotCond( iLitRes, Abc_LitIsCompl(iTopLit) );
        }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, pObj->Value );
    Gia_ManForEachObjVec( vObjs, p, pObj, i )
        pObj->fPhase = 0;
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    Vec_IntFree( vNodes );
    Vec_IntFree( vUsed );
    Vec_IntFree( vCopy );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Perform resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// Returns the next common variable with opposite phases.  When piChoice is
// non-NULL, each such exact solution is counted and skipped until the
// requested choice reaches zero.  Skipped solutions are removed from both
// arrays so that the later cover stages cannot rediscover them.
static inline int Gia_ManFindFirstCommonLit( Vec_Int_t * vArr1, Vec_Int_t * vArr2, int fVerbose, int * piChoice )
{
    int * pBeg1 = vArr1->pArray;
    int * pBeg2 = vArr2->pArray;
    int * pEnd1 = vArr1->pArray + vArr1->nSize;
    int * pEnd2 = vArr2->pArray + vArr2->nSize;
    int * pStart1 = vArr1->pArray;
    int * pStart2 = vArr2->pArray;
    int nRemoved = 0;
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        if ( Abc_Lit2Var(*pBeg1) == Abc_Lit2Var(*pBeg2) )
        { 
            if ( *pBeg1 != *pBeg2 )
            {
                if ( piChoice == NULL || *piChoice == 0 )
                    return *pBeg1;
                (*piChoice)--;
                pBeg1++, pBeg2++;
            }
            else
                pBeg1++, pBeg2++;
            nRemoved++;
        }
        else if ( *pBeg1 < *pBeg2 )
            *pStart1++ = *pBeg1++;
        else 
            *pStart2++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 )
        *pStart1++ = *pBeg1++;
    while ( pBeg2 < pEnd2 )
        *pStart2++ = *pBeg2++;
    Vec_IntShrink( vArr1, pStart1 - vArr1->pArray );
    Vec_IntShrink( vArr2, pStart2 - vArr2->pArray );
    //if ( fVerbose ) printf( "Removed %d duplicated entries.  Array1 = %d.  Array2 = %d.\n", nRemoved, Vec_IntSize(vArr1), Vec_IntSize(vArr2) );
    return -1;
}

// Intern ids depend on which side first admitted a key and therefore are not
// themselves a sort key.  Pair arrays retain generator order by (lit1,lit0),
// so merge them using the underlying unrestricted literals.  Equality ignores
// only the descriptor phase, exactly like Gia_ManFindFirstCommonLit().
static inline int Gia_ResbPairCompare( Gia_ResbMan_t * p, int Pair0,
    int Pair1 )
{
    int Hi0 = Gia_ResbPairLit1(p, Pair0);
    int Hi1 = Gia_ResbPairLit1(p, Pair1);
    if ( Hi0 != Hi1 ) return Hi0 < Hi1 ? -1 : 1;
    {
        int Lo0 = Gia_ResbPairLit0(p, Pair0);
        int Lo1 = Gia_ResbPairLit0(p, Pair1);
        return Lo0 == Lo1 ? 0 : (Lo0 < Lo1 ? -1 : 1);
    }
}

// Vec_IntUniqify() sorts by the numeric descriptor.  That was also the
// historical packed-pair order, but an intern id is deliberately opaque and
// insertion-dependent.  Preserve the old (Hi, Lo, descriptor-phase) order
// explicitly so changing representation cannot change equal-score ties or a
// subsequently truncated frontier.
static inline int Gia_ResbPairCompareFull( Gia_ResbMan_t * p, int Pair0,
    int Pair1 )
{
    int Compare = Gia_ResbPairCompare( p, Pair0, Pair1 );
    if ( Compare )
        return Compare;
    return Abc_LitIsCompl(Pair0) - Abc_LitIsCompl(Pair1);
}

static int Gia_ResbPairUniqify( Gia_ResbMan_t * p, Vec_Int_t * vPairs )
{
    int nSize = Vec_IntSize(vPairs), Width, i, k, nUnique;
    int * pOriginal, * pSource, * pTarget, * pTemp;
    if ( nSize < 2 )
        return 0;
    pOriginal = Vec_IntArray(vPairs);
    pSource = pOriginal;
    pTemp = ABC_ALLOC( int, nSize );
    pTarget = pTemp;
    for ( Width = 1; Width < nSize;
          Width = Width > nSize / 2 ? nSize : 2 * Width )
    {
        int Span = Width > nSize - Width ? nSize : 2 * Width;
        for ( i = 0; i < nSize; i += Span )
        {
            int i0 = i, i1 = Width > nSize - i ? nSize : i + Width;
            int e0 = i1, e1 = Span > nSize - i ? nSize : i + Span;
            for ( k = i; k < e1; k++ )
                if ( i0 < e0 && (i1 == e1 ||
                     Gia_ResbPairCompareFull(p, pSource[i0],
                         pSource[i1]) <= 0) )
                    pTarget[k] = pSource[i0++];
                else
                    pTarget[k] = pSource[i1++];
        }
        {
            int * pSwap = pSource;
            pSource = pTarget;
            pTarget = pSwap;
        }
    }
    if ( pSource != pOriginal )
        memcpy( pOriginal, pSource, sizeof(int) * (size_t)nSize );
    ABC_FREE( pTemp );
    for ( i = nUnique = 1; i < nSize; i++ )
        if ( Gia_ResbPairCompareFull(p, pOriginal[i-1],
                pOriginal[i]) != 0 )
            pOriginal[nUnique++] = pOriginal[i];
    Vec_IntShrink( vPairs, nUnique );
    return nSize - nUnique;
}

static inline int Gia_ManFindFirstCommonPair( Gia_ResbMan_t * p,
    Vec_Int_t * vArr1, Vec_Int_t * vArr2, int fVerbose, int * piChoice )
{
    int * pBeg1 = vArr1->pArray, * pBeg2 = vArr2->pArray;
    int * pEnd1 = vArr1->pArray + vArr1->nSize;
    int * pEnd2 = vArr2->pArray + vArr2->nSize;
    int * pStart1 = vArr1->pArray, * pStart2 = vArr2->pArray;
    int nRemoved = 0;
    while ( pBeg1 < pEnd1 && pBeg2 < pEnd2 )
    {
        int Compare = Gia_ResbPairCompare( p, *pBeg1, *pBeg2 );
        if ( Compare == 0 )
        {
            if ( Abc_LitIsCompl(*pBeg1) != Abc_LitIsCompl(*pBeg2) )
            {
                if ( piChoice == NULL || *piChoice == 0 )
                    return *pBeg1;
                (*piChoice)--;
            }
            pBeg1++, pBeg2++;
            nRemoved++;
        }
        else if ( Compare < 0 )
            *pStart1++ = *pBeg1++;
        else
            *pStart2++ = *pBeg2++;
    }
    while ( pBeg1 < pEnd1 ) *pStart1++ = *pBeg1++;
    while ( pBeg2 < pEnd2 ) *pStart2++ = *pBeg2++;
    vArr1->nSize -= nRemoved;
    vArr2->nSize -= nRemoved;
    if ( fVerbose ) printf( "C = %d.  ", nRemoved );
    return -1;
}

// Empty OFF sets admit both polarities. The historical single-polarity
// classification is incomplete for sampled constant targets. Enable the full
// classification only for the opt-in strict SEQ constructor; other clients
// retain their existing policy. This follows the pass-owned resub manager.
static int s_ResubBothPolarities = 0;
void Abc_ResubSetBothPolarities( int Enable )
{
    assert( Enable == 0 || Enable == 1 );
    s_ResubBothPolarities = Enable;
}

void Gia_ManFindOneUnateInt( word * pOff, word * pOn, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vNotUnateVars )
{
    word * pDiv; int i;
    Vec_IntClear( vUnateLits );
    Vec_IntClear( vNotUnateVars );
    Vec_PtrForEachEntryStart( word *, vDivs, pDiv, i, 2 )
    {
        int Positive = !Abc_TtIntersectOne(pOff,0,pDiv,0,nWords);
        int Negative = (!Positive || s_ResubBothPolarities) &&
            !Abc_TtIntersectOne(pOff,0,pDiv,1,nWords);
        if(Positive) Vec_IntPush(vUnateLits,Abc_Var2Lit(i,0));
        if(Negative && (!Positive || s_ResubBothPolarities))
            Vec_IntPush(vUnateLits,Abc_Var2Lit(i,1));
        if(!Positive && !Negative) Vec_IntPush(vNotUnateVars,i);
    }
}
int Gia_ManFindOneUnate( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vNotUnateVars[2], int fVerbose, int * piChoice )
{
    int n;
    if ( fVerbose ) printf( "  " );
    for ( n = 0; n < 2; n++ )
    {
        Gia_ManFindOneUnateInt( pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vNotUnateVars[n] );
        if ( fVerbose ) printf( "U%d =%4d ", n, Vec_IntSize(vUnateLits[n]) );
    }
    return Gia_ManFindFirstCommonLit( vUnateLits[0], vUnateLits[1], fVerbose, piChoice );
}

static inline int Gia_ManDivCover( word * pOff, word * pOn, word * pDivA, int ComplA, word * pDivB, int ComplB, int nWords )
{
    //assert( !Abc_TtIntersectOne(pOff, 0, pDivA, ComplA, nWords) );
    //assert( !Abc_TtIntersectOne(pOff, 0, pDivB, ComplB, nWords) );
    return !Abc_TtIntersectTwo( pOn, 0, pDivA, !ComplA, pDivB, !ComplB, nWords );
}
int Gia_ManFindTwoUnateInt( Gia_ResbMan_t * p, word * pOff, word * pOn, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vUnateLitsW, int * pnPairs, int * piChoice )
{
    int i, k, iDiv0_, iDiv1_, Cover0, Cover1;
    int nTotal = Abc_TtCountOnesVec( pOn, nWords );
    (*pnPairs) = 0;
    Vec_IntForEachEntryTwo( vUnateLits, vUnateLitsW, iDiv0_, Cover0, i )
    {
        if ( 2*Cover0 < nTotal )
            break;
        Vec_IntForEachEntryTwoStart( vUnateLits, vUnateLitsW, iDiv1_, Cover1, k, i+1 )
        {
            int iDiv0 = Abc_MinInt( iDiv0_, iDiv1_ );
            int iDiv1 = Abc_MaxInt( iDiv0_, iDiv1_ );
            word * pDiv0 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
            word * pDiv1 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv1));
            if ( Cover0 + Cover1 < nTotal )
                break;
            (*pnPairs)++;
            if ( Gia_ManDivCover(pOff, pOn, pDiv1, Abc_LitIsCompl(iDiv1), pDiv0, Abc_LitIsCompl(iDiv0), nWords) )
            {
                if ( *piChoice == 0 )
                    return Gia_ResbPairIntern(p, Abc_LitNot(iDiv0), Abc_LitNot(iDiv1), 1);
                (*piChoice)--;
            }
        }
    }
    return -1;
}
int Gia_ManFindTwoUnate( Gia_ResbMan_t * p, word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnateLitsW[2], int fVerbose, int * piChoice )
{
    int n, iLit, nPairs;
    if ( fVerbose ) printf( "  " );
    for ( n = 0; n < 2; n++ )
    {
        //int nPairsAll = Vec_IntSize(vUnateLits[n])*(Vec_IntSize(vUnateLits[n])-1)/2;
        iLit = Gia_ManFindTwoUnateInt( p, pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vUnateLitsW[n], &nPairs, piChoice );
        if ( fVerbose ) printf( "UU%d =%5d ", n, nPairs );
        if ( iLit >= 0 )
            return Abc_LitNotCond(iLit, n);
    }
    return -1;
}

void Gia_ManFindXorInt( Gia_ResbMan_t * p, word * pOff, word * pOn, Vec_Int_t * vBinate, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs )
{
    int i, k, iDiv0_, iDiv1_;
    int Limit2 = Vec_IntSize(vBinate);//Abc_MinInt( Vec_IntSize(vBinate), 100 );
    Vec_IntForEachEntryStop( vBinate, iDiv1_, i, Limit2 )
    Vec_IntForEachEntryStop( vBinate, iDiv0_, k, i )
    {
        int iDiv0 = Abc_MinInt( iDiv0_, iDiv1_ );
        int iDiv1 = Abc_MaxInt( iDiv0_, iDiv1_ );
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, iDiv0);
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, iDiv1);
        if ( !Abc_TtIntersectXor( pOff, 0, pDiv0, pDiv1, 0, nWords ) )
            Vec_IntPush( vUnatePairs, Gia_ResbPairIntern(p, Abc_Var2Lit(iDiv1, 0), Abc_Var2Lit(iDiv0, 0), 0) );
        else if ( !Abc_TtIntersectXor( pOff, 0, pDiv0, pDiv1, 1, nWords ) )
            Vec_IntPush( vUnatePairs, Gia_ResbPairIntern(p, Abc_Var2Lit(iDiv1, 0), Abc_Var2Lit(iDiv0, 0), 1) );
    }
}
int Gia_ManFindXor( Gia_ResbMan_t * p, word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Int_t * vUnatePairs[2], int fVerbose, int * piChoice )
{
    int n;
    if ( fVerbose ) printf( "  " );
    for ( n = 0; n < 2; n++ )
    {
        Vec_IntClear( vUnatePairs[n] );
        Gia_ManFindXorInt( p, pSets[n], pSets[!n], vBinateVars, vDivs, nWords, vUnatePairs[n] );
        if ( fVerbose ) printf( "UX%d =%5d ", n, Vec_IntSize(vUnatePairs[n]) );
    }
    return Gia_ManFindFirstCommonPair( p, vUnatePairs[0], vUnatePairs[1], fVerbose, piChoice );
}

// Signatures identify repeated computations only. Physical divisor IDs and
// every ordered pair remain in the original domain and emitted recipe stream.
// A masked partition belongs to exactly one current OFF/ON call; full
// signatures may retain their partition only within a manager binding.
static int Gia_ResbPairSigClassesBuild( Gia_ResbMan_t * p,
    word * pCare, Vec_Int_t * vDomain )
{
    int nDivs = Vec_PtrSize(p->vDivs), nBins = 1, i, j, k, c, nDup = 0;
    int nInputs = vDomain ? Vec_IntSize(vDomain) : nDivs - 2;
    Vec_Int_t * vBins, * vFreq;
    Vec_Wrd_t * vHashes;
    assert( p->vPairSigClasses == NULL );
    while ( nBins < 2 * nInputs ) nBins <<= 1;
    vBins = Vec_IntStart( nBins );
    vFreq = Vec_IntAlloc( nDivs );
    vHashes = Vec_WrdAlloc( nDivs );
    p->vPairSigClasses = Vec_IntStartFull( nDivs );
    p->vPairSigReps = Vec_IntAlloc( nDivs );
    for ( j = 0; j < nInputs; j++ )
    {
        word * pSig;
        word Hash = 1469598103934665603ULL;
        int s;
        i = vDomain ? Vec_IntEntry(vDomain, j) : j + 2;
        assert( i >= 2 && i < nDivs );
        pSig = (word *)Vec_PtrEntry(p->vDivs, i);
        for ( s = 0; s < p->nWords; s++ )
            Hash = (Hash ^ (pCare ? pSig[s] & pCare[s] : pSig[s])) * 1099511628211ULL;
        k = (int)(Hash ^ (Hash >> 32)) & (nBins - 1);
        while ( Vec_IntEntry(vBins, k) )
        {
            c = Vec_IntEntry(vBins, k) - 1;
            if ( Vec_WrdEntry(vHashes, c) == Hash )
            {
                word * pRep = (word *)Vec_PtrEntry(p->vDivs, Vec_IntEntry(p->vPairSigReps, c));
                if ( pCare )
                {
                    for ( s = 0; s < p->nWords; s++ )
                        if ( (pSig[s] ^ pRep[s]) & pCare[s] ) break;
                    if ( s == p->nWords ) break;
                }
                else if ( !memcmp(pSig, pRep, sizeof(word) * p->nWords) )
                    break;
            }
            k = (k + 1) & (nBins - 1);
        }
        if ( !Vec_IntEntry(vBins, k) )
        {
            c = Vec_IntSize(p->vPairSigReps);
            Vec_IntWriteEntry( vBins, k, c + 1 );
            Vec_IntPush( p->vPairSigReps, i );
            Vec_IntPush( vFreq, 0 );
            Vec_WrdPush( vHashes, Hash );
        }
        c = Vec_IntEntry(vBins, k) - 1;
        Vec_IntWriteEntry( p->vPairSigClasses, i, c );
        Vec_IntAddToEntry( vFreq, c, 1 );
    }
    p->vPairSigDupRows = Vec_IntStartFull( Vec_IntSize(vFreq) );
    Vec_IntForEachEntry( vFreq, k, i )
        if ( k > 1 ) Vec_IntWriteEntry( p->vPairSigDupRows, i, nDup++ );
    Vec_IntFree( vBins ); Vec_IntFree( vFreq ); Vec_WrdFree( vHashes );
    p->nPairSigDup = nDup;
    return nDup;
}

static int Gia_ResbPairSigClasses( Gia_ResbMan_t * p )
{
    return p->vPairSigClasses ? p->nPairSigDup :
        Gia_ResbPairSigClassesBuild(p, NULL, NULL);
}

static void Gia_ResbPairSigClassesClear( Gia_ResbMan_t * p )
{
    assert( p->pPairClassMasks == NULL );
    Vec_IntFreeP( &p->vPairSigClasses );
    Vec_IntFreeP( &p->vPairSigReps );
    Vec_IntFreeP( &p->vPairSigDupRows );
    p->nPairSigDup = 0;
}

static int Gia_ResbPairClassMask( Gia_ResbMan_t * p, word * pOff,
    word * pOn, int iDiv0, int iDiv1 )
{
    int c0 = Vec_IntEntry(p->vPairSigClasses, iDiv0);
    int c1 = Vec_IntEntry(p->vPairSigClasses, iDiv1);
    assert( c0 >= 0 && c1 >= 0 );
    int r0 = Vec_IntEntry(p->vPairSigDupRows, c0);
    int r1 = Vec_IntEntry(p->vPairSigDupRows, c1);
    int fSwap = r0 < 0 || (r1 >= 0 && c1 < c0), n, Mask = 0;
    size_t Index;
    unsigned char * pEntry;
    word * pDiv0, * pDiv1;
    if ( r0 < 0 && r1 < 0 ) return -1; // both unique: no repeated computation
    if ( fSwap )
    {
        ABC_SWAP( int, c0, c1 );
        ABC_SWAP( int, r0, r1 );
    }
    assert( r0 >= 0 );
    Index = (size_t)r0 * Vec_IntSize(p->vPairSigReps) + c1;
    pEntry = p->pPairClassMasks + Index;
    if ( !*pEntry )
    {
        pDiv0 = (word *)Vec_PtrEntry(p->vDivs, Vec_IntEntry(p->vPairSigReps, c0));
        pDiv1 = (word *)Vec_PtrEntry(p->vDivs, Vec_IntEntry(p->vPairSigReps, c1));
        for ( n = 0; n < 4; n++ )
            if ( !Abc_TtIntersectTwo(pOff, 0, pDiv1, n>>1, pDiv0, n&1, p->nWords) &&
                   Abc_TtIntersectTwo(pOn, 0, pDiv1, n>>1, pDiv0, n&1, p->nWords) )
                Mask |= 1 << n;
        *pEntry = (unsigned char)(16 | Mask);
        p->nPairClassComputations++;
    }
    Mask = *pEntry & 15;
    // Swapping endpoints swaps the two phase bits (01 <-> 10).
    return fSwap ? (Mask & 9) | ((Mask & 2) << 1) | ((Mask & 4) >> 1) : Mask;
}

void Gia_ManFindUnatePairsInt( Gia_ResbMan_t * p, word * pOff, word * pOn, Vec_Int_t * vBinate, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs )
{
    int n, i, k, iDiv0_, iDiv1_;
    int Limit2 = Vec_IntSize(vBinate);//Abc_MinInt( Vec_IntSize(vBinate), 100 );
    Vec_IntForEachEntryStop( vBinate, iDiv1_, i, Limit2 )
    Vec_IntForEachEntryStop( vBinate, iDiv0_, k, i )
    {
        int iDiv0 = Abc_MinInt( iDiv0_, iDiv1_ );
        int iDiv1 = Abc_MaxInt( iDiv0_, iDiv1_ );
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, iDiv0);
        word * pDiv1 = (word *)Vec_PtrEntry(vDivs, iDiv1);
        int Mask = -1;
        p->nPairClassVisits++;
        if ( p->pPairClassMasks ) Mask = Gia_ResbPairClassMask(p, pOff, pOn, iDiv0, iDiv1);
        if ( Mask < 0 ) p->nPairClassComputations++;
        if ( Mask == 0 ) continue;
        for ( n = 0; n < 4; n++ )
        {
            int iLit0 = Abc_Var2Lit( iDiv0, n&1 );
            int iLit1 = Abc_Var2Lit( iDiv1, n>>1 );
            //if ( !Abc_TtIntersectTwo( pOff, 0, pDiv1, n>>1, pDiv0, n&1, nWords ) )
            if ( Mask >= 0 ? !!(Mask & (1 << n)) :
                 (!Abc_TtIntersectTwo( pOff, 0, pDiv1, n>>1, pDiv0, n&1, nWords ) && Abc_TtIntersectTwo( pOn, 0, pDiv1, n>>1, pDiv0, n&1, nWords )) )
                Vec_IntPush( vUnatePairs, Gia_ResbPairIntern(p, iLit0, iLit1, 0) );
        }
    }
}
void Gia_ManFindUnatePairs( Gia_ResbMan_t * p, word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Int_t * vUnatePairs[2], int fVerbose )
{
    int n, RetValue, nDup = 0, nCensusDivs = 0;
    long long nCareBits = 0;
    word * pCare = NULL;
    abctime clkClass = Abc_Clock();
    int fCensusNew = p->fPairClassCache &&
        (p->fPairClassCache == 2 || p->vPairSigClasses == NULL);
    for ( n = 0; n < nWords; n++ )
        nCareBits += Abc_TtCountOnes(pSets[0][n] | pSets[1][n]);
    if ( p->fPairClassCache == 2 )
    {
        assert( p->vPairSigClasses == NULL );
        pCare = ABC_ALLOC(word, nWords);
        for ( n = 0; n < nWords; n++ ) pCare[n] = pSets[0][n] | pSets[1][n];
        nDup = Gia_ResbPairSigClassesBuild(p, pCare, vBinateVars);
        nCensusDivs = Vec_IntSize(vBinateVars);
        ABC_FREE(pCare);
    }
    else if ( p->fPairClassCache )
    {
        nDup = Gia_ResbPairSigClasses(p);
        nCensusDivs = Vec_PtrSize(vDivs) - 2;
    }
    size_t nBytes = nDup ? (size_t)nDup * Vec_IntSize(p->vPairSigReps) : 0;
    abctime timeCensus = Abc_Clock() - clkClass, clkInit = Abc_Clock(), timeInit;
    assert( p->pPairClassMasks == NULL );
    if ( nBytes ) p->pPairClassMasks = ABC_CALLOC( unsigned char, nBytes );
    timeInit = Abc_Clock() - clkInit;
    p->nPairClassVisits = p->nPairClassComputations = 0;
    if ( fVerbose ) printf( "  " );
    for ( n = 0; n < 2; n++ )
    {
        if ( n && nBytes )
        {
            clkInit = Abc_Clock();
            memset( p->pPairClassMasks, 0, nBytes );
            timeInit += Abc_Clock() - clkInit;
        }
        int nBefore = Vec_IntSize(vUnatePairs[n]);
        Gia_ManFindUnatePairsInt( p, pSets[n], pSets[!n], vBinateVars, vDivs, nWords, vUnatePairs[n] );
        if ( fVerbose ) printf( "UP%d =%5d ", n, Vec_IntSize(vUnatePairs[n])-nBefore );
    }
    ABC_FREE( p->pPairClassMasks );
    if ( p->fProfilePivots && getenv("ABC_STRICT_PREPROOF_TRACE") && atoi(getenv("ABC_STRICT_PREPROOF_TRACE")) )
    {
        Abc_Print(1, "stran-resub pair-class-cache: schema=3 enabled=%d census=%d divs=%d unique=%d duplicate-classes=%d visits=%lld computations=%lld table-bytes=%llu census-new=%d census-words=%lld census-sec=%.6f table-init-sec=%.6f mode=%d census-divs=%d care-bits=%lld seconds=%.6f\n",
            !!p->fPairClassCache, !!p->fPairClassCache, Vec_PtrSize(vDivs)-2,
            p->vPairSigReps ? Vec_IntSize(p->vPairSigReps) : 0,
            nDup, p->nPairClassVisits, p->nPairClassComputations,
            (unsigned long long)nBytes, fCensusNew,
            fCensusNew ? (long long)nCensusDivs * nWords : 0,
            (double)timeCensus/CLOCKS_PER_SEC, (double)timeInit/CLOCKS_PER_SEC,
            p->fPairClassCache, nCensusDivs, nCareBits,
            (double)(Abc_Clock()-clkClass)/CLOCKS_PER_SEC );
        fflush(stdout);
    }
    if ( p->fPairClassCache == 2 ) Gia_ResbPairSigClassesClear(p);
    RetValue = Gia_ManFindFirstCommonPair( p, vUnatePairs[0], vUnatePairs[1], fVerbose, NULL );
    assert( RetValue == -1 );
}

void Gia_ManDeriveDivPair( Gia_ResbMan_t * p, int iDiv, Vec_Ptr_t * vDivs, int nWords, word * pRes )
{
    int fComp = Abc_LitIsCompl(iDiv);
    int iDiv0 = Gia_ResbPairLit0(p, iDiv);
    int iDiv1 = Gia_ResbPairLit1(p, iDiv);
    word * pDiv0 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
    word * pDiv1 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv1));
    if ( iDiv0 < iDiv1 )
    {
        assert( !fComp );
        Abc_TtAndCompl( pRes, pDiv0, Abc_LitIsCompl(iDiv0), pDiv1, Abc_LitIsCompl(iDiv1), nWords );
    }
    else 
    {
        assert( !Abc_LitIsCompl(iDiv0) );
        assert( !Abc_LitIsCompl(iDiv1) );
        Abc_TtXor( pRes, pDiv0, pDiv1, nWords, 0 );
    }
}

int Gia_ManFindDivGateInt( Gia_ResbMan_t * p, word * pOff, word * pOn, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vUnatePairs, Vec_Int_t * vUnateLitsW, Vec_Int_t * vUnatePairsW, word * pDivTemp, int * piChoice )
{
    int i, k, iDiv0, iDiv1, Cover0, Cover1;
    int nTotal = Abc_TtCountOnesVec( pOn, nWords );
    Vec_IntForEachEntryTwo( vUnateLits, vUnateLitsW, iDiv0, Cover0, i )
    {
        word * pDiv0 = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iDiv0));
        // The literal and pair frontiers have independent coverage orders.
        if ( Vec_IntSize(vUnatePairsW) == 0 ||
             Cover0 + Vec_IntEntry(vUnatePairsW, 0) < nTotal )
            break;
        Vec_IntForEachEntryTwo( vUnatePairs, vUnatePairsW, iDiv1, Cover1, k )
        {
            int fComp1 = Abc_LitIsCompl(iDiv1);
            if ( Cover0 + Cover1 < nTotal )
                break;
            Gia_ManDeriveDivPair( p, iDiv1, vDivs, nWords, pDivTemp );
            if ( Gia_ManDivCover(pOff, pOn, pDiv0, Abc_LitIsCompl(iDiv0), pDivTemp, fComp1, nWords) )
            {
                if ( *piChoice == 0 )
                    return Gia_ResbLegacyPackTwo15(Abc_LitNot(iDiv0), Abc_Var2Lit(k, 1), 1);
                (*piChoice)--;
            }
        }
    }
    return -1;
}
int Gia_ManFindDivGate( Gia_ResbMan_t * p, word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnatePairs[2], Vec_Int_t * vUnateLitsW[2], Vec_Int_t * vUnatePairsW[2], word * pDivTemp, int * piChoice )
{
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        iLit = Gia_ManFindDivGateInt( p, pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vUnatePairs[n], vUnateLitsW[n], vUnatePairsW[n], pDivTemp, piChoice );
        if ( iLit >= 0 )
            return Abc_LitNotCond( iLit, n );
    }
    return -1;
}

int Gia_ManFindGateGateInt( Gia_ResbMan_t * p, word * pOff, word * pOn, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs, Vec_Int_t * vUnatePairsW, word * pDivTempA, word * pDivTempB, int * piChoice )
{
    int i, k, iDiv0, iDiv1, Cover0, Cover1;
    int nTotal = Abc_TtCountOnesVec( pOn, nWords );
    Vec_IntForEachEntryTwo( vUnatePairs, vUnatePairsW, iDiv0, Cover0, k )
    {
        int fCompA = Abc_LitIsCompl(iDiv0);
        if ( 2*Cover0 < nTotal )
            break;
        Gia_ManDeriveDivPair( p, iDiv0, vDivs, nWords, pDivTempA );
        Vec_IntForEachEntryTwoStart( vUnatePairs, vUnatePairsW, iDiv1, Cover1, i, k+1 )
        {
            int fCompB = Abc_LitIsCompl(iDiv1);
            if ( Cover0 + Cover1 < nTotal )
                break;
            Gia_ManDeriveDivPair( p, iDiv1, vDivs, nWords, pDivTempB );
            if ( Gia_ManDivCover(pOff, pOn, pDivTempA, fCompA, pDivTempB, fCompB, nWords) )
            {
                if ( *piChoice == 0 )
                    return Gia_ResbLegacyPackTwo15(Abc_Var2Lit(k, 1), Abc_Var2Lit(i, 1), 1);
                (*piChoice)--;
            }
        }
    }
    return -1;
}
int Gia_ManFindGateGate( Gia_ResbMan_t * p, word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs[2], Vec_Int_t * vUnatePairsW[2], word * pDivTempA, word * pDivTempB, int * piChoice )
{
    int n, iLit;
    for ( n = 0; n < 2; n++ )
    {
        iLit = Gia_ManFindGateGateInt( p, pSets[n], pSets[!n], vDivs, nWords, vUnatePairs[n], vUnatePairsW[n], pDivTempA, pDivTempB, piChoice );
        if ( iLit >= 0 )
            return Abc_LitNotCond( iLit, n );
    }
    return -1;
}

// Preserve stable descending coverage order while visiting/clearing only
// occupied buckets. The extra bitmap word includes score 64*nWords.
static void Gia_ResbSortFinish( Vec_Wec_t * vSorter, word * pUsed,
    int nUsedWords, Vec_Int_t * vItems, Vec_Int_t * vWeights )
{
    int w, k, i, Item;
    Vec_IntClear( vItems );
    if ( vWeights ) Vec_IntClear( vWeights );
    for ( w = nUsedWords - 1; w >= 0; w-- )
        while ( pUsed[w] )
        {
            int Bit = Abc_Tt6LastBit( pUsed[w] );
            Vec_Int_t * vLevel;
            pUsed[w] ^= (word)1 << Bit;
            k = 64*w + Bit;
            vLevel = Vec_WecEntry( vSorter, k );
            Vec_IntForEachEntry( vLevel, Item, i )
            {
                Vec_IntPush( vItems, Item );
                if ( vWeights ) Vec_IntPush( vWeights, k );
            }
            Vec_IntClear( vLevel );
        }
    // All nonempty levels were cleared; preserve Vec_WecClear's empty state
    // without scanning the remaining empty levels again.
    vSorter->nSize = 0;
}
static inline void Gia_ResbSortPush( Vec_Wec_t * vSorter, word * pUsed,
    int Score, int Item )
{
    Vec_WecPush( vSorter, Score, Item );
    pUsed[Score >> 6] |= (word)1 << (Score & 63);
}

void Gia_ManSortUnatesInt( word * pOff, word * pOn, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits, Vec_Int_t * vUnateLitsW, Vec_Wec_t * vSorter )
{
    int i, iLit;
    word Used[65], * pUsed = nWords < 65 ? Used : ABC_ALLOC(word, nWords+1);
    memset( pUsed, 0, sizeof(word) * (nWords+1) );
    Vec_WecInit( vSorter, nWords*64 );
    Vec_IntForEachEntry( vUnateLits, iLit, i )
    {
        word * pDiv = (word *)Vec_PtrEntry(vDivs, Abc_Lit2Var(iLit));
        //assert( !Abc_TtIntersectOne( pOff, 0, pDiv, Abc_LitIsCompl(iLit), nWords ) );
        Gia_ResbSortPush( vSorter, pUsed, Abc_TtCountOnesVecMask(pDiv, pOn, nWords, Abc_LitIsCompl(iLit)), iLit );
    }
    Gia_ResbSortFinish( vSorter, pUsed, nWords+1, vUnateLits, vUnateLitsW );
    if ( pUsed != Used ) ABC_FREE( pUsed );
}
void Gia_ManSortUnates( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnateLitsW[2], Vec_Wec_t * vSorter )
{
    int n;
    for ( n = 0; n < 2; n++ )
        Gia_ManSortUnatesInt( pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vUnateLitsW[n], vSorter );
}

void Gia_ManSortPairsInt( Gia_ResbMan_t * p, word * pOff, word * pOn, Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnatePairs, Vec_Int_t * vUnatePairsW, Vec_Wec_t * vSorter )
{
    int i, iPair;
    word Used[65], * pUsed = nWords < 65 ? Used : ABC_ALLOC(word, nWords+1);
    memset( pUsed, 0, sizeof(word) * (nWords+1) );
    Vec_WecInit( vSorter, nWords*64 );
    Vec_IntForEachEntry( vUnatePairs, iPair, i )
    {
        int fComp = Abc_LitIsCompl(iPair);
        int iLit0 = Gia_ResbPairLit0(p, iPair);
        int iLit1 = Gia_ResbPairLit1(p, iPair);
        word * pDiv0 = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit0) );
        word * pDiv1 = (word *)Vec_PtrEntry( vDivs, Abc_Lit2Var(iLit1) );
        if ( iLit0 < iLit1 )
        {
            assert( !fComp );
            //assert( !Abc_TtIntersectTwo( pOff, 0, pDiv0, Abc_LitIsCompl(iLit0), pDiv1, Abc_LitIsCompl(iLit1), nWords ) );
            Gia_ResbSortPush( vSorter, pUsed, Abc_TtCountOnesVecMask2(pDiv0, pDiv1, Abc_LitIsCompl(iLit0), Abc_LitIsCompl(iLit1), pOn, nWords), iPair );
        }
        else
        {
            assert( !Abc_LitIsCompl(iLit0) );
            assert( !Abc_LitIsCompl(iLit1) );
            //assert( !Abc_TtIntersectXor( pOff, 0, pDiv0, pDiv1, fComp, nWords ) );
            Gia_ResbSortPush( vSorter, pUsed, Abc_TtCountOnesVecXorMask(pDiv0, pDiv1, fComp, pOn, nWords), iPair );
        }
    }
    Gia_ResbSortFinish( vSorter, pUsed, nWords+1, vUnatePairs, vUnatePairsW );
    if ( pUsed != Used ) ABC_FREE( pUsed );

}
void Gia_ManSortPairs( Gia_ResbMan_t * p, word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vUnateLits[2], Vec_Int_t * vUnateLitsW[2], Vec_Wec_t * vSorter )
{
    int n;
    for ( n = 0; n < 2; n++ )
        Gia_ManSortPairsInt( p, pSets[n], pSets[!n], vDivs, nWords, vUnateLits[n], vUnateLitsW[n], vSorter );
}

// Build exact top-level cover masks once for the ordered greedy frontier.
// Equal masks produce equal residual states because every pivot in this
// frontier updates the same OFF/ON side.  Novelty is measured against the
// union of all earlier (higher-ranked) masks, which exposes both exact
// duplicates and pivots adding no new simulated distinction at all.
static void Gia_ResbBuildTopFrontier( Gia_ResbMan_t * p, int fUseOr,
    int fPair )
{
    Vec_Int_t * vPivots = fPair ? p->vUnatePairs[!fUseOr] :
        p->vUnateLits[!fUseOr];
    int i, k, w, iPivot, nFrontier = p->fQualityNoTruncation ? Vec_IntSize(vPivots) :
        Abc_MinInt(Vec_IntSize(vPivots), p->nDivsMax);
    Vec_IntClear( p->vTopPivotNovel );
    Vec_IntClear( p->vTopPivotDuplicate );
    Vec_WrdFill( p->vTopPivotCovers, nFrontier * p->nWords, 0 );
    Abc_TtClear( p->pDivB, p->nWords );
    p->nTopFrontier = nFrontier;
    p->nTopFrontierUnique = 0;
    p->nTopFrontierZeroNovel = 0;
    p->nTopFrontierCoverSum = 0;
    p->nTopFrontierNovelSum = 0;
    for ( i = 0; i < nFrontier; i++ )
    {
        word * pSignal, * pCover = Vec_WrdEntryP(p->vTopPivotCovers,
            i * p->nWords);
        int fDuplicate = 0, Cover, Novel = 0;
        iPivot = Vec_IntEntry( vPivots, i );
        if ( fPair )
        {
            Gia_ManDeriveDivPair( p, iPivot, p->vDivs, p->nWords, p->pDivA );
            pSignal = p->pDivA;
        }
        else
            pSignal = (word *)Vec_PtrEntry(p->vDivs,
                Abc_Lit2Var(iPivot));
        for ( w = 0; w < p->nWords; w++ )
        {
            pCover[w] = p->pSets[fUseOr][w] &
                (Abc_LitIsCompl(iPivot) ? ~pSignal[w] : pSignal[w]);
            Novel += Abc_TtCountOnes(pCover[w] & ~p->pDivB[w]);
        }
        Cover = Abc_TtCountOnesVec( pCover, p->nWords );
        for ( k = 0; k < i; k++ )
            if ( !memcmp(pCover, Vec_WrdEntryP(p->vTopPivotCovers,
                    k * p->nWords), sizeof(word) * p->nWords) )
            {
                fDuplicate = 1;
                break;
            }
        for ( w = 0; w < p->nWords; w++ )
            p->pDivB[w] |= pCover[w];
        Vec_IntPush( p->vTopPivotNovel, Novel );
        Vec_IntPush( p->vTopPivotDuplicate, fDuplicate );
        p->nTopFrontierUnique += !fDuplicate;
        p->nTopFrontierZeroNovel += Novel == 0;
        p->nTopFrontierCoverSum += Cover;
        p->nTopFrontierNovelSum += Novel;
    }
    p->nTopPivotKind = fPair ? 2 : 1;
    p->nTopPivotTotal = Abc_TtCountOnesVec(p->pSets[fUseOr], p->nWords);
    p->fTopPivotProfileReady = 1;
}

static void Gia_ResbProfileTopChoice( Gia_ResbMan_t * p, int fUseOr,
    int fPair, int iChoice )
{
    word * pCover;
    if ( !p->fTopPivotProfileReady )
        Gia_ResbBuildTopFrontier( p, fUseOr, fPair );
    p->nTopPivotRank = iChoice + 1;
    if ( iChoice < 0 || iChoice >= p->nTopFrontier )
    {
        p->nTopPivotCover = p->nTopPivotNovel = 0;
        p->nTopPivotRemain = p->nTopPivotTotal;
        p->fTopPivotDuplicate = 0;
        return;
    }
    pCover = Vec_WrdEntryP(p->vTopPivotCovers, iChoice * p->nWords);
    p->nTopPivotCover = Abc_TtCountOnesVec( pCover, p->nWords );
    p->nTopPivotNovel = Vec_IntEntry( p->vTopPivotNovel, iChoice );
    p->nTopPivotRemain = p->nTopPivotTotal - p->nTopPivotCover;
    p->fTopPivotDuplicate = Vec_IntEntry(p->vTopPivotDuplicate, iChoice);
}

static void Gia_ResbSecondPivotCover( Gia_ResbMan_t * p, int fUseOr,
    int fPair, int iPivot, word * pCover )
{
    word * pSignal;
    int w;
    if ( fPair )
    {
        Gia_ManDeriveDivPair( p, iPivot, p->vDivs, p->nWords, p->pDivA );
        pSignal = p->pDivA;
    }
    else
        pSignal = (word *)Vec_PtrEntry(p->vDivs,
            Abc_Lit2Var(iPivot));
    for ( w = 0; w < p->nWords; w++ )
        pCover[w] = p->pSets[fUseOr][w] &
            (Abc_LitIsCompl(iPivot) ? ~pSignal[w] : pSignal[w]);
}

// Select one exact second-layer coverage representative for a Stage-5 path.
// Path one is the unchanged coverage-rank primary.  For each later path j,
// let S be the exact masks already chosen and rank every remaining C by the
// lexicographically descending tuple
//
//   ( |C \\ union(S)|, min_{D in S}|C xor D|, |C|, -original_rank(C) ).
//
// Equal masks are ineligible because they leave the identical residual.  The
// formula uses complete simulation masks (not adjacent coverage ranks), has a
// stable final tie-break, and is recomputed only at depth two.  Once this
// choice is consumed, all deeper recursion follows the original primary path.
static int Gia_ResbSecondDiverseChoice( Gia_ResbMan_t * p, int fUseOr,
    int fPair, int PathIndex )
{
    Vec_Int_t * vPivots = fPair ? p->vUnatePairs[!fUseOr] :
        p->vUnateLits[!fUseOr];
    int nPivots = p->fQualityNoTruncation ? Vec_IntSize(vPivots) :
        Abc_MinInt(Vec_IntSize(vPivots), p->nDivsMax);
    int Slot, i, k, w, iPivot, iBest;
    int BestNew = -1, BestSym = -1, BestCover = -1;
    assert( PathIndex >= 2 && PathIndex <= 4 );
    if ( nPivots < PathIndex )
        return -1;
    Vec_IntClear( p->vSecondPivotRanks );
    Vec_WrdFill( p->vSecondPivotCovers, PathIndex * p->nWords, 0 );
    Vec_IntPush( p->vSecondPivotRanks, 0 );
    Gia_ResbSecondPivotCover( p, fUseOr, fPair,
        Vec_IntEntry(vPivots, 0), Vec_WrdArray(p->vSecondPivotCovers) );
    for ( Slot = 1; Slot < PathIndex; Slot++ )
    {
        iBest = -1;
        BestNew = BestSym = BestCover = -1;
        for ( i = 1; i < nPivots; i++ )
        {
            int New = 0, MinSym = ABC_INFINITY, Cover = 0;
            int fSelected = 0, fDuplicate = 0;
            word * pCand = p->pDivB;
            Vec_IntForEachEntry( p->vSecondPivotRanks, k, w )
                if ( k == i )
                {
                    fSelected = 1;
                    break;
                }
            if ( fSelected )
                continue;
            iPivot = Vec_IntEntry( vPivots, i );
            Gia_ResbSecondPivotCover( p, fUseOr, fPair, iPivot, pCand );
            for ( k = 0; k < Slot; k++ )
            {
                word * pPrev = Vec_WrdEntryP(p->vSecondPivotCovers,
                    k * p->nWords);
                int Sym = 0;
                for ( w = 0; w < p->nWords; w++ )
                    Sym += Abc_TtCountOnes( pCand[w] ^ pPrev[w] );
                MinSym = Abc_MinInt( MinSym, Sym );
                fDuplicate |= Sym == 0;
            }
            if ( fDuplicate )
                continue;
            for ( w = 0; w < p->nWords; w++ )
            {
                word Union = 0;
                for ( k = 0; k < Slot; k++ )
                    Union |= Vec_WrdEntry(p->vSecondPivotCovers,
                        k * p->nWords + w);
                Cover += Abc_TtCountOnes( pCand[w] );
                New += Abc_TtCountOnes( pCand[w] & ~Union );
            }
            if ( New > BestNew ||
                 (New == BestNew && MinSym > BestSym) ||
                 (New == BestNew && MinSym == BestSym &&
                  Cover > BestCover) ||
                 (New == BestNew && MinSym == BestSym &&
                  Cover == BestCover && (iBest < 0 || i < iBest)) )
                iBest = i, BestNew = New, BestSym = MinSym,
                BestCover = Cover;
        }
        if ( iBest < 0 )
            return -1;
        Vec_IntPush( p->vSecondPivotRanks, iBest );
        Gia_ResbSecondPivotCover( p, fUseOr, fPair,
            Vec_IntEntry(vPivots, iBest),
            Vec_WrdEntryP(p->vSecondPivotCovers, Slot * p->nWords) );
    }
    p->fSecondPivotSelected = 1;
    p->nSecondPivotRank = iBest + 1;
    p->nSecondPivotCover = BestCover;
    p->nSecondPivotNew = BestNew;
    p->nSecondPivotSym = BestSym;
    return iBest;
}

// Estimate whether the exact residual left by one top pivot can be separated
// by the remaining recipe leaves.  Classes are signatures of the divisors
// selected so far.  Counting OFF/ON polarities inside each class computes the
// exact number of still-ambiguous cross-pairs without materializing the
// quadratic OFF x ON relation.
static void Gia_ResbSolvScorePivot( Gia_ResbMan_t * p, int fUseOr,
    int iPivot, int nLimit, int * pComplete, int * pDepth,
    word * pAmbiguity )
{
    word * pCover = Vec_WrdEntryP(p->vTopPivotCovers,
        iPivot * p->nWords);
    Vec_Wrd_t * vClasses = p->vSolvClassMasks[0];
    Vec_Wrd_t * vNext = p->vSolvClassMasks[1];
    Vec_Int_t * vCounts = p->vSolvClassCounts[0];
    Vec_Int_t * vCountsNext = p->vSolvClassCounts[1];
    long long Ambiguity;
    int nMints[2] = {0, 0};
    int nVars = Vec_PtrSize(p->vDivs);
    int nSelected = 0, nSelectMax = nLimit + 1;
    int w, c, iDiv;
    Vec_WrdClear( vClasses );
    for ( w = 0; w < p->nWords; w++ )
    {
        p->pDivA[w] = p->pSets[0][w] &
            (fUseOr == 0 ? ~pCover[w] : ~(word)0);
        p->pDivB[w] = p->pSets[1][w] &
            (fUseOr == 1 ? ~pCover[w] : ~(word)0);
        nMints[0] += Abc_TtCountOnes( p->pDivA[w] );
        nMints[1] += Abc_TtCountOnes( p->pDivB[w] );
        Vec_WrdPush( vClasses, p->pDivA[w] | p->pDivB[w] );
    }
    Vec_IntClear( vCounts );
    Vec_IntPushTwo( vCounts, nMints[0], nMints[1] );
    Vec_IntFill( p->vSolvSelected, nVars, 0 );
    Ambiguity = (long long)nMints[0] * nMints[1];
    while ( Ambiguity > 0 && nSelected < nSelectMax )
    {
        long long BestScore = 0;
        int iBest = -1;
        for ( iDiv = 2; iDiv < nVars; iDiv++ )
        {
            word * pDiv = (word *)Vec_PtrEntry( p->vDivs, iDiv );
            long long Score = 0;
            if ( Vec_IntEntry(p->vSolvSelected, iDiv) )
                continue;
            for ( c = 0; c < Vec_WrdSize(vClasses)/p->nWords; c++ )
            {
                word * pClass = Vec_WrdEntryP(vClasses, c * p->nWords);
                int Off1 = 0, On1 = 0;
                int OffTotal = Vec_IntEntry(vCounts, 2*c);
                int OnTotal = Vec_IntEntry(vCounts, 2*c+1);
                for ( w = 0; w < p->nWords; w++ )
                {
                    word Off = pClass[w] & p->pDivA[w];
                    word On  = pClass[w] & p->pDivB[w];
                    Off1 += Abc_TtCountOnes( Off & pDiv[w] );
                    On1  += Abc_TtCountOnes( On & pDiv[w] );
                }
                Score += (long long)(OffTotal-Off1) * On1 +
                    (long long)Off1 * (OnTotal-On1);
            }
            if ( Score > BestScore )
                BestScore = Score, iBest = iDiv;
        }
        if ( iBest < 0 || BestScore == 0 )
            break;
        Vec_IntWriteEntry( p->vSolvSelected, iBest, 1 );
        Vec_WrdClear( vNext );
        Vec_IntClear( vCountsNext );
        for ( c = 0; c < Vec_WrdSize(vClasses)/p->nWords; c++ )
        {
            word * pDiv = (word *)Vec_PtrEntry( p->vDivs, iBest );
            word * pClass = Vec_WrdEntryP(vClasses, c * p->nWords);
            int fOne;
            for ( fOne = 0; fOne < 2; fOne++ )
            {
                int iStart = Vec_WrdSize(vNext), nOff = 0, nOn = 0;
                for ( w = 0; w < p->nWords; w++ )
                {
                    word Mask = pClass[w] &
                        (fOne ? pDiv[w] : ~pDiv[w]);
                    nOff += Abc_TtCountOnes( Mask & p->pDivA[w] );
                    nOn  += Abc_TtCountOnes( Mask & p->pDivB[w] );
                    Vec_WrdPush( vNext, Mask );
                }
                if ( nOff == 0 || nOn == 0 )
                    Vec_WrdShrink( vNext, iStart );
                else
                    Vec_IntPushTwo( vCountsNext, nOff, nOn );
            }
        }
        { Vec_Wrd_t * vTemp = vClasses; vClasses = vNext; vNext = vTemp; }
        { Vec_Int_t * vTemp = vCounts; vCounts = vCountsNext;
          vCountsNext = vTemp; }
        Ambiguity -= BestScore;
        nSelected++;
    }
    *pComplete = Ambiguity == 0;
    *pDepth = *pComplete ? Abc_MaxInt(0, nSelected - 1) : nLimit + 1;
    *pAmbiguity = (word)Ambiguity;
}

static int Gia_ResbSolvPivotIsBetter( Gia_ResbMan_t * p, int iPivot0,
    int iPivot1 )
{
    int Complete0 = Vec_IntEntry(p->vSolvComplete, iPivot0);
    int Complete1 = Vec_IntEntry(p->vSolvComplete, iPivot1);
    int Depth0 = Vec_IntEntry(p->vSolvDepth, iPivot0);
    int Depth1 = Vec_IntEntry(p->vSolvDepth, iPivot1);
    word Amb0 = Vec_WrdEntry(p->vSolvAmbiguity, iPivot0);
    word Amb1 = Vec_WrdEntry(p->vSolvAmbiguity, iPivot1);
    int Cover0, Cover1;
    if ( Complete0 != Complete1 )
        return Complete0 > Complete1;
    if ( Depth0 != Depth1 )
        return Depth0 < Depth1;
    if ( Amb0 != Amb1 )
        return Amb0 < Amb1;
    Cover0 = Abc_TtCountOnesVec( Vec_WrdEntryP(p->vTopPivotCovers,
        iPivot0 * p->nWords), p->nWords );
    Cover1 = Abc_TtCountOnesVec( Vec_WrdEntryP(p->vTopPivotCovers,
        iPivot1 * p->nWords), p->nWords );
    // All entries of one schedule have the same literal/pair top cost, so
    // cover-per-gate reduces exactly to cover here.
    if ( Cover0 != Cover1 )
        return Cover0 > Cover1;
    return iPivot0 < iPivot1;
}

// Build a permutation of the original Stage-5 frontier.  Rank one is Alan's
// primary heuristic and remains first.  Exact-unique residual representatives
// are scored and sorted next; exact duplicates are stable fallback entries.
// Consequently unlimited enumeration retains every original pivot exactly
// once, while a finite accepted-candidate budget sees easier residuals first.
static void Gia_ResbBuildSolvSchedule( Gia_ResbMan_t * p, int fUseOr,
    int fPair, int nLimit )
{
    abctime clk = Abc_Clock();
    int i, k, iPivot, Complete, Depth;
    word Ambiguity;
    int fNeedScores;
    if ( p->fSolvScheduleReady )
        return;
    if ( !p->fTopPivotProfileReady )
        Gia_ResbBuildTopFrontier( p, fUseOr, fPair );
    Vec_IntFill( p->vSolvDepth, p->nTopFrontier, nLimit + 1 );
    Vec_IntFill( p->vSolvComplete, p->nTopFrontier, 0 );
    Vec_WrdFill( p->vSolvAmbiguity, p->nTopFrontier, ~(word)0 );
    Vec_IntClear( p->vSolvOrder );
    fNeedScores = p->nTopFrontierUnique > 2;
    if ( p->nTopFrontier > 0 )
        Vec_IntPush( p->vSolvOrder, 0 );
    for ( i = 1; i < p->nTopFrontier; i++ )
    {
        if ( Vec_IntEntry(p->vTopPivotDuplicate, i) )
            continue;
        if ( fNeedScores )
        {
            Gia_ResbSolvScorePivot( p, fUseOr, i, nLimit,
                &Complete, &Depth, &Ambiguity );
            Vec_IntWriteEntry( p->vSolvComplete, i, Complete );
            Vec_IntWriteEntry( p->vSolvDepth, i, Depth );
            Vec_WrdWriteEntry( p->vSolvAmbiguity, i, Ambiguity );
            p->nSolvSchedulePivots++;
            p->nSolvScheduleComplete += Complete;
        }
        Vec_IntPush( p->vSolvOrder, i );
        for ( k = Vec_IntSize(p->vSolvOrder) - 1;
              fNeedScores && k > 1; k-- )
        {
            int Prev = Vec_IntEntry(p->vSolvOrder, k-1);
            int This = Vec_IntEntry(p->vSolvOrder, k);
            if ( !Gia_ResbSolvPivotIsBetter(p, This, Prev) )
                break;
            Vec_IntWriteEntry( p->vSolvOrder, k-1, This );
            Vec_IntWriteEntry( p->vSolvOrder, k, Prev );
        }
    }
    for ( i = 1; i < p->nTopFrontier; i++ )
        if ( Vec_IntEntry(p->vTopPivotDuplicate, i) )
            Vec_IntPush( p->vSolvOrder, i );
    assert( Vec_IntSize(p->vSolvOrder) == p->nTopFrontier );
    Vec_IntForEachEntry( p->vSolvOrder, iPivot, i )
    {
        assert( iPivot >= 0 && iPivot < p->nTopFrontier );
        for ( k = 0; k < i; k++ )
            assert( Vec_IntEntry(p->vSolvOrder, k) != iPivot );
    }
    p->timeSolvSchedule = Abc_Clock() - clk;
    p->fSolvScheduleReady = 1;
}

static int Gia_ResbSolvScheduleChoice( Gia_ResbMan_t * p, int fUseOr,
    int fPair, int iChoice, int nLimit )
{
    // The primary pivot is fixed and needs no score.  Delay building the
    // alternative order until the iterator actually asks for rank two; a q
    // prefix that stops after the primary path therefore pays no scheduler
    // overhead at all.
    if ( iChoice == 0 )
        return 0;
    Gia_ResbBuildSolvSchedule( p, fUseOr, fPair, nLimit );
    return iChoice >= 0 && iChoice < Vec_IntSize(p->vSolvOrder) ?
        Vec_IntEntry(p->vSolvOrder, iChoice) : iChoice;
}

static void Gia_ManSortBinateQuality( word * pSets[2], Vec_Ptr_t * vDivs, int nWords, Vec_Int_t * vBinateVars, Vec_Wec_t * vSorter, int fNoTruncation )
{
    int nMints[2] = { Abc_TtCountOnesVec(pSets[0], nWords), Abc_TtCountOnesVec(pSets[1], nWords) };
    word * pBig = nMints[0] > nMints[1] ? pSets[0] : pSets[1];
    word * pSmo = nMints[0] > nMints[1] ? pSets[1] : pSets[0];
    int Big = Abc_MaxInt( nMints[0], nMints[1] );
    int Smo = Abc_MinInt( nMints[0], nMints[1] );
    int i, iDiv, Gain;
    word Used[65], * pUsed = nWords < 65 ? Used : ABC_ALLOC(word, nWords+1);

    memset( pUsed, 0, sizeof(word) * (nWords+1) );
    Vec_WecInit( vSorter, nWords*64 );
    Vec_IntForEachEntry( vBinateVars, iDiv, i )
    {
        word * pDiv = (word *)Vec_PtrEntry( vDivs, iDiv );
        int nInter[2] = { Abc_TtCountOnesVecMask(pBig, pDiv, nWords, 0), Abc_TtCountOnesVecMask(pSmo, pDiv, nWords, 0) };
        if ( nInter[0] < Big/2 ) // complement the divisor
        {
            nInter[0] = Big - nInter[0];
            nInter[1] = Smo - nInter[1];
        }
        assert( nInter[0] >= Big/2 );
        Gain = Abc_MaxInt( 0, nInter[0] - Big/2 + Smo/2 - nInter[1] );
        Gia_ResbSortPush( vSorter, pUsed, Gain, iDiv );
    }

    Gia_ResbSortFinish( vSorter, pUsed, nWords+1, vBinateVars, NULL );
    if ( pUsed != Used ) ABC_FREE( pUsed );

    if ( !fNoTruncation && Vec_IntSize(vBinateVars) > 2000 )
        Vec_IntShrink( vBinateVars, 2000 );
}

void Gia_ManSortBinate( word * pSets[2], Vec_Ptr_t * vDivs, int nWords,
    Vec_Int_t * vBinateVars, Vec_Wec_t * vSorter )
{
    Gia_ManSortBinateQuality( pSets, vDivs, nWords, vBinateVars,
        vSorter, Abc_ResubQualityNoTruncation() );
}

// Unateness on the opposite target side does not disqualify a material from
// an AND implicant. For example, removing one cared ON row can make d unate
// for OFF while a useful a & !d remains OFF-disjoint. Pair eligibility must
// test the pair itself. Keep the existing material ranking and B cap, then
// let Gia_ManFindUnatePairsInt test its four phases against current OFF/ON.
// A literal covering the same sampled rows is not a formal dominance proof;
// dropping its pair can lose a stronger, provable temporal relation.
static Vec_Int_t * Gia_ResbPairVars( Gia_ResbMan_t * p )
{
    int i;
    if ( !p->fCarePairTruth )
        return p->vBinateVars;
    Vec_IntClear( p->vPairVars );
    for ( i = 2; i < Vec_PtrSize(p->vDivs); i++ )
        Vec_IntPush( p->vPairVars, i );
    Gia_ManSortBinate( p->pSets, p->vDivs, p->nWords,
        p->vPairVars, p->vSorter );
    if ( Vec_IntSize(p->vPairVars) > p->nDivsMax )
        Vec_IntShrink( p->vPairVars, p->nDivsMax );
    return p->vPairVars;
}

/**Function*************************************************************

  Synopsis    [Perform resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#include "giaResubGreedyRank.h"

int Gia_ManResubFindBestBinate( Gia_ResbMan_t * p )
{
    int nMintsAll = Abc_TtCountOnesVec(p->pSets[0], p->nWords) + Abc_TtCountOnesVec(p->pSets[1], p->nWords);
    int i, iDiv, iLitBest = -1, CostBest = -1;
//Vec_IntPrint( p->vBinateVars );
//Dau_DsdPrintFromTruth( p->pSets[0], 6 );
//Dau_DsdPrintFromTruth( p->pSets[1], 6 );
    Vec_IntForEachEntry( p->vBinateVars, iDiv, i )
    {
        word * pDiv = (word *)Vec_PtrEntry(p->vDivs, iDiv);
        int nMints0 = Abc_TtCountOnesVecMask( pDiv, p->pSets[0], p->nWords, 0 );
        int nMints1 = Abc_TtCountOnesVecMask( pDiv, p->pSets[1], p->nWords, 0 );
        if ( CostBest < nMints0 + nMints1 ) 
        {
            CostBest = nMints0 + nMints1;
            iLitBest = Abc_Var2Lit( iDiv, 0 );
        }
        if ( CostBest < nMintsAll - nMints0 - nMints1 ) 
        {
            CostBest = nMintsAll - nMints0 - nMints1;
            iLitBest = Abc_Var2Lit( iDiv, 1 );
        }
    }
    return iLitBest;
}
int Gia_ManResubAddNode( Gia_ResbMan_t * p, int iLit0, int iLit1, int Type )
{
    int iNode = Vec_PtrSize(p->vDivs) + Vec_IntSize(p->vGates)/2;
    int fFlip = (Type == 2) ^ (iLit0 > iLit1);
    int iFan0 = fFlip ? iLit1 : iLit0;
    int iFan1 = fFlip ? iLit0 : iLit1;
    assert( iLit0 != iLit1 );
    if ( Type == 2 )
        assert( iFan0 > iFan1 );
    else
        assert( iFan0 < iFan1 );
    Vec_IntPushTwo( p->vGates, Abc_LitNotCond(iFan0, Type==1), Abc_LitNotCond(iFan1, Type==1) );
    return Abc_Var2Lit( iNode, Type==1 );
}
int Gia_ManResubPerformMux_rec( Gia_ResbMan_t * p, int nLimit, int Depth )
{
    extern int Gia_ManResubPerform_rec( Gia_ResbMan_t * p, int nLimit, int Depth, int fTop );
    int iDivBest, iResLit0, iResLit1, nNodes;
    word * pDiv, * pCopy[2];
    if ( Depth == 0 )
        return -1;
    if ( nLimit < 3 )
        return -1;
    iDivBest = Gia_ManResubFindBestBinate( p );
    if ( iDivBest == -1 )
        return -1;
    pCopy[0] = ABC_CALLOC( word, p->nWords );
    pCopy[1] = ABC_CALLOC( word, p->nWords );
    Abc_TtCopy( pCopy[0], p->pSets[0], p->nWords, 0 );
    Abc_TtCopy( pCopy[1], p->pSets[1], p->nWords, 0 );
    pDiv = (word *)Vec_PtrEntry( p->vDivs, Abc_Lit2Var(iDivBest) );
    Abc_TtAndSharp( p->pSets[0], pCopy[0], pDiv, p->nWords, !Abc_LitIsCompl(iDivBest) );
    Abc_TtAndSharp( p->pSets[1], pCopy[1], pDiv, p->nWords, !Abc_LitIsCompl(iDivBest) );
    nNodes = Vec_IntSize(p->vGates)/2;
    iResLit0 = Gia_ManResubPerform_rec( p, nLimit, 0, 0 );
    if ( iResLit0 == -1 )
        iResLit0 = Gia_ManResubPerformMux_rec( p, nLimit, Depth-1 );
    if ( iResLit0 == -1 )
    {
        ABC_FREE( pCopy[0] );
        ABC_FREE( pCopy[1] );
        return -1;
    }
    Abc_TtAndSharp( p->pSets[0], pCopy[0], pDiv, p->nWords,  Abc_LitIsCompl(iDivBest) );
    Abc_TtAndSharp( p->pSets[1], pCopy[1], pDiv, p->nWords,  Abc_LitIsCompl(iDivBest) );
    ABC_FREE( pCopy[0] );
    ABC_FREE( pCopy[1] );
    nNodes = Vec_IntSize(p->vGates)/2 - nNodes;
    if ( nLimit-nNodes < 3 )
        return -1;
    iResLit1 = Gia_ManResubPerform_rec( p, nLimit, 0, 0 );
    if ( iResLit1 == -1 )
        iResLit1 = Gia_ManResubPerformMux_rec( p, nLimit, Depth-1 );
    if ( iResLit1 == -1 )
        return -1;
    else
    {
        int iLit0 = Gia_ManResubAddNode( p, Abc_LitNot(iDivBest), iResLit0, 0 );
        int iLit1 = Gia_ManResubAddNode( p,            iDivBest,  iResLit1, 0 );
        return Gia_ManResubAddNode( p, iLit0, iLit1, 1 );
    }
}

static int Gia_ManResubPerform_rec_int( Gia_ResbMan_t * p, int nLimit,
    int Depth, int fTop );

// Stage-5 primary recursion is deterministic once the exact residual masks,
// remaining gate budget, and root-local divisor context are fixed.  Cache
// only FAIL internally: successful fragments contain path-relative gate IDs
// and continue through the ordinary recursion until a separately verified
// immutable representation is available.  A pending path 2..4 bypasses this
// primary memo until its one alternate second pivot has been consumed; deeper
// recursion then rejoins the primary memo domain.
int Gia_ManResubPerform_rec( Gia_ResbMan_t * p, int nLimit, int Depth,
    int fTop )
{
    int iEntry, fFound, Result, iMeta, Stored;
    int fMemo = p->fSkipTemplates && !fTop && Depth == 0 &&
        p->iChoice == 0 && p->nSecondPath <= 1 &&
        p->fUseRecursiveFailCache;
    abctime clk = 0, SolveTime = 0;
    if ( !fMemo )
        return Gia_ManResubPerform_rec_int( p, nLimit, Depth, fTop );
    p->nResidualRecCalls++;
    iEntry = Gia_ResbResidualCacheFindOrAdd( p, 0, 0, nLimit, 0,
        &fFound );
    iMeta = iEntry * GIA_RESUB_RESIDUAL_META_SIZE;
    if ( fFound )
    {
        Stored = Vec_IntEntry(p->vResidualCacheMeta,
            iMeta + GIA_RESUB_RESIDUAL_RESULT);
        assert( Stored == -1 || Stored == GIA_RESUB_RESIDUAL_SUCCESS_ONLY );
        if ( Stored == -1 )
        {
            p->nResidualRecFailHits++;
            p->timeResidualRecSaved +=
                (abctime)Vec_WrdEntry(p->vResidualCacheSolveTimes, iEntry);
            return -1;
        }
        p->nResidualRecSuccessDuplicate++;
    }
    if ( p->fProfilePivots )
        clk = Abc_Clock();
    p->nResidualRecDepth++;
    Result = Gia_ManResubPerform_rec_int( p, nLimit, Depth, fTop );
    p->nResidualRecDepth--;
    if ( p->fProfilePivots )
        SolveTime = Abc_Clock() - clk;
    if ( !fFound )
    {
        Vec_IntWriteEntry( p->vResidualCacheMeta,
            iMeta + GIA_RESUB_RESIDUAL_RESULT,
            Result < 0 ? -1 : GIA_RESUB_RESIDUAL_SUCCESS_ONLY );
        Vec_WrdWriteEntry( p->vResidualCacheSolveTimes, iEntry,
            (word)SolveTime );
    }
    else
        assert( Result >= 0 );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Perform resubstitution.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gia_ManResubPerform_rec_int( Gia_ResbMan_t * p, int nLimit,
    int Depth, int fTop )
{
    int TopOneW[2] = {0}, TopTwoW[2] = {0}, Max1, Max2, iChoice, iResLit;
    int fAllowZero = p->fUseZero || (!fTop && p->nSecondPath <= 1);
    int fUseTopCache = p->fSkipTemplates && fTop && !fAllowZero &&
        Depth == 0 && p->fTopCacheReady;
    int nVars = Vec_PtrSize(p->vDivs);
    if ( p->fVerbose )
    {
        int nMints[2] = { Abc_TtCountOnesVec(p->pSets[0], p->nWords), Abc_TtCountOnesVec(p->pSets[1], p->nWords) };
        printf( "      " ); 
        printf( "ISF: " ); 
        printf( "0=%5d (%5.2f %%) ",  nMints[0], 100.0*nMints[0]/(64*p->nWords) );
        printf( "1=%5d (%5.2f %%)  ", nMints[1], 100.0*nMints[1]/(64*p->nWords) );
    }
    if ( !p->fSkipTemplates && Abc_TtIsConst0( p->pSets[1], p->nWords ) )
    {
        if ( p->iChoice == 0 )
            return 0;
        p->iChoice--;
    }
    if ( !p->fSkipTemplates && Abc_TtIsConst0( p->pSets[0], p->nWords ) )
    {
        if ( p->iChoice == 0 )
            return 1;
        p->iChoice--;
    }
    if ( fAllowZero )
    {
        iResLit = Gia_ManFindOneUnate( p->pSets, p->vDivs, p->nWords,
            p->vUnateLits, p->vNotUnateVars, p->fVerbose, &p->iChoice );
        if ( iResLit >= 0 ) // buffer or recursive cover leaf
            return iResLit;
    }
    else if ( fUseTopCache )
        Gia_ResbLoadTopSummary( p );
    else
    {
        int n;
        // Do not return a zero-gate top-level answer, but keep exact literals
        // in the unate sets: several such literals may still form a useful
        // formally provable constructed recipe (for example, r & s).
        if ( p->fVerbose ) printf( "  " );
        for ( n = 0; n < 2; n++ )
        {
            Gia_ManFindOneUnateInt( p->pSets[n], p->pSets[!n],
                p->vDivs, p->nWords, p->vUnateLits[n],
                p->vNotUnateVars[n] );
            if ( p->fVerbose )
                printf( "U%d =%4d ", n, Vec_IntSize(p->vUnateLits[n]) );
        }
    }
    if ( nLimit == 0 )
        return -1;
    if ( !fUseTopCache )
        Gia_ManSortUnates( p->pSets, p->vDivs, p->nWords,
            p->vUnateLits, p->vUnateLitsW, p->vSorter );
    // Do not bypass a pending alternate pivot when closing a residual leaf.
    iResLit = p->fSkipTemplates && (fTop || nLimit != 1 || !fAllowZero) ? -1 :
        Gia_ManFindTwoUnate( p, p->pSets, p->vDivs, p->nWords,
            p->vUnateLits, p->vUnateLitsW, p->fVerbose, &p->iChoice );
    if ( iResLit >= 0 ) // and
    {
        int iNode = nVars + Vec_IntSize(p->vGates)/2;
        int fComp = Abc_LitIsCompl(iResLit);
        int iDiv0 = Gia_ResbPairLit0(p, iResLit);
        int iDiv1 = Gia_ResbPairLit1(p, iResLit);
        assert( iDiv0 < iDiv1 );
        Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
        return Abc_Var2Lit( iNode, fComp );
    }
    if ( !fUseTopCache )
    {
        Vec_IntTwoFindCommon( p->vNotUnateVars[0],
            p->vNotUnateVars[1], p->vBinateVars );
        if ( Depth )
            return Gia_ManResubPerformMux_rec( p, nLimit, Depth );
        if ( !p->fQualityNoTruncation && Vec_IntSize(p->vBinateVars) > p->nDivsMax )
            Vec_IntShrink( p->vBinateVars, p->nDivsMax );
        if ( p->fVerbose )
            printf( "  B = %3d", Vec_IntSize(p->vBinateVars) );
        // Rank binate variables before pair/template enumeration.  This
        // changes only heuristic order, never the finite candidate universe.
        Gia_ManSortBinate( p->pSets, p->vDivs, p->nWords,
            p->vBinateVars, p->vSorter );
    }
    if ( p->fUseXor && !p->fSkipTemplates )
    {
        iResLit = Gia_ManFindXor( p, p->pSets, p->vDivs, p->nWords, p->vBinateVars, p->vUnatePairs, p->fVerbose, &p->iChoice );
        if ( iResLit >= 0 ) // xor
        {
            int iNode = nVars + Vec_IntSize(p->vGates)/2;
            int fComp = Abc_LitIsCompl(iResLit);
            int iDiv0 = Gia_ResbPairLit0(p, iResLit);
            int iDiv1 = Gia_ResbPairLit1(p, iResLit);
            assert( !Abc_LitIsCompl(iDiv0) );
            assert( !Abc_LitIsCompl(iDiv1) );
            assert( iDiv0 > iDiv1 );
            Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
            return Abc_Var2Lit( iNode, fComp );
        }
    }
    if ( nLimit == 1 )
        return -1;
    if ( !fUseTopCache )
    {
        int Ranked = p->fGreedyPairRanked && p->fSkipTemplates &&
            !p->fQualityNoTruncation && !p->fUseXor;
        // Recursive greedy calls share one manager, but their pair
        // classification is a function of the current residual OFF/ON masks.
        // Do not retain pairs produced for an earlier residual: besides being
        // invalid for this state, that made a repeated exact-cache key depend
        // on traversal history (the first solve could succeed and the second
        // fail).  Rebuild the pair scratch from this residual only.
        if ( p->fSkipTemplates )
        {
            Vec_IntClear( p->vUnatePairs[0] );
            Vec_IntClear( p->vUnatePairs[1] );
            Vec_IntClear( p->vUnatePairsW[0] );
            Vec_IntClear( p->vUnatePairsW[1] );
        }
        if ( Ranked ) Gia_ResbFindRankedPairs(p, Gia_ResbPairVars(p), 1);
        else Gia_ManFindUnatePairs( p, p->pSets, p->vDivs, p->nWords,
            Gia_ResbPairVars(p), p->vUnatePairs, p->fVerbose );
        // Canonicalize the relation before ranking and keep the same B-wide
        // frontier as root discovery.
        if ( p->fSkipTemplates && !Ranked )
        {
            Gia_ResbPairUniqify( p, p->vUnatePairs[0] );
            Gia_ResbPairUniqify( p, p->vUnatePairs[1] );
        }
        if ( !Ranked ) Gia_ManSortPairs( p, p->pSets, p->vDivs, p->nWords,
            p->vUnatePairs, p->vUnatePairsW, p->vSorter );
        if ( p->fSkipTemplates )
        {
            int n;
            for ( n = 0; n < 2; n++ )
                if ( !p->fQualityNoTruncation && Vec_IntSize(p->vUnatePairs[n]) > p->nDivsMax )
                {
                    Vec_IntShrink( p->vUnatePairs[n], p->nDivsMax );
                    Vec_IntShrink( p->vUnatePairsW[n], p->nDivsMax );
                }
        }
    }
    // The first top-level greedy attempt follows the original classification
    // path and snapshots its ordered frontier immediately before recursion can
    // overwrite the shared scratch vectors.  Later pivots restore this exact
    // summary; recursive remainder calls still recompute from their own sets.
    if ( p->fSkipTemplates && fTop && !fUseTopCache )
        Gia_ResbSaveTopSummary( p );
    iResLit = p->fSkipTemplates ? -1 :
        Gia_ManFindDivGate( p, p->pSets, p->vDivs, p->nWords,
            p->vUnateLits, p->vUnatePairs, p->vUnateLitsW,
            p->vUnatePairsW, p->pDivA, &p->iChoice );
    if ( iResLit >= 0 ) // and(div,pair)
    {
        int iNode  = nVars + Vec_IntSize(p->vGates)/2;

        int fComp  = Abc_LitIsCompl(iResLit);
        int iDiv0  = Abc_Lit2Var(iResLit) & 0x7FFF; // div
        int iDiv1  = Abc_Lit2Var(iResLit) >> 15;    // pair

        int Div1   = Vec_IntEntry( p->vUnatePairs[!fComp], Abc_Lit2Var(iDiv1) );
        int fComp1 = Abc_LitIsCompl(Div1) ^ Abc_LitIsCompl(iDiv1);
        int iDiv10 = Gia_ResbPairLit0(p, Div1);
        int iDiv11 = Gia_ResbPairLit1(p, Div1);

        Vec_IntPushTwo( p->vGates, iDiv10, iDiv11 );
        Vec_IntPushTwo( p->vGates, iDiv0, Abc_Var2Lit(iNode, fComp1) );
        return Abc_Var2Lit( iNode+1, fComp );
    }
    if ( nLimit >= 3 && !p->fSkipTemplates )
    {
        iResLit = Gia_ManFindGateGate( p, p->pSets, p->vDivs, p->nWords, p->vUnatePairs, p->vUnatePairsW, p->pDivA, p->pDivB, &p->iChoice );
        if ( iResLit >= 0 ) // and(pair,pair)
        {
            int iNode  = nVars + Vec_IntSize(p->vGates)/2;

            int fComp  = Abc_LitIsCompl(iResLit);
            int iDiv0  = Abc_Lit2Var(iResLit) & 0x7FFF; // pair
            int iDiv1  = Abc_Lit2Var(iResLit) >> 15;    // pair

            int Div0   = Vec_IntEntry( p->vUnatePairs[!fComp], Abc_Lit2Var(iDiv0) );
            int fComp0 = Abc_LitIsCompl(Div0) ^ Abc_LitIsCompl(iDiv0);
            int iDiv00 = Gia_ResbPairLit0(p, Div0);
            int iDiv01 = Gia_ResbPairLit1(p, Div0);
        
            int Div1   = Vec_IntEntry( p->vUnatePairs[!fComp], Abc_Lit2Var(iDiv1) );
            int fComp1 = Abc_LitIsCompl(Div1) ^ Abc_LitIsCompl(iDiv1);
            int iDiv10 = Gia_ResbPairLit0(p, Div1);
            int iDiv11 = Gia_ResbPairLit1(p, Div1);
        
            Vec_IntPushTwo( p->vGates, iDiv00, iDiv01 );
            Vec_IntPushTwo( p->vGates, iDiv10, iDiv11 );
            Vec_IntPushTwo( p->vGates, Abc_Var2Lit(iNode, fComp0), Abc_Var2Lit(iNode+1, fComp1) );
            return Abc_Var2Lit( iNode+2, fComp );
        }
    }
    if ( Vec_IntSize(p->vUnateLits[0]) + Vec_IntSize(p->vUnateLits[1]) + Vec_IntSize(p->vUnatePairs[0]) + Vec_IntSize(p->vUnatePairs[1]) == 0 )
        return -1;

    TopOneW[0] = Vec_IntSize(p->vUnateLitsW[0]) ? Vec_IntEntry(p->vUnateLitsW[0], 0) : 0;
    TopOneW[1] = Vec_IntSize(p->vUnateLitsW[1]) ? Vec_IntEntry(p->vUnateLitsW[1], 0) : 0;

    TopTwoW[0] = Vec_IntSize(p->vUnatePairsW[0]) ? Vec_IntEntry(p->vUnatePairsW[0], 0) : 0;
    TopTwoW[1] = Vec_IntSize(p->vUnatePairsW[1]) ? Vec_IntEntry(p->vUnatePairsW[1], 0) : 0;

    Max1 = Abc_MaxInt(TopOneW[0], TopOneW[1]);
    Max2 = Abc_MaxInt(TopTwoW[0], TopTwoW[1]);
    if ( Abc_MaxInt(Max1, Max2) == 0 )
        return -1;

    // Exact templates above consume choices in increasing gate-count order.
    // Any remaining choice selects an alternate first greedy cover element;
    // the recursive remainder deliberately uses its primary choice.  This
    // gives finite ordered diversity without turning the cover recursion into
    // an exponential backtracking search.
    iChoice = p->iChoice;
    p->iChoice = 0;

    if ( Max1 > Max2/2 )
    {
        if ( nLimit >= 2 && (Max1 == TopOneW[0] || Max1 == TopOneW[1]) )
        {
            int fUseOr  = Max1 == TopOneW[0];
            int iDiv, iCacheEntry = -1, fCacheHit = 0;
            abctime clkCache = 0, timeSolve = 0;
            if ( fTop && p->fSkipTemplates && p->fUseSolvSched &&
                 p->nCurrentPath == 1 )
                iChoice = Gia_ResbSolvScheduleChoice( p, fUseOr, 0,
                    iChoice, nLimit-1 );
            if ( fTop && p->fProfilePivots )
                Gia_ResbProfileTopChoice( p, fUseOr, 0, iChoice );
            if ( fTop && p->fSkipTemplates )
                p->nStage5TopFrontier = p->fQualityNoTruncation ?
                    Vec_IntSize(p->vUnateLits[!fUseOr]) : Abc_MinInt(
                    Vec_IntSize(p->vUnateLits[!fUseOr]), p->nDivsMax);
            if ( !fTop && p->nSecondPath > 1 )
                iChoice = Gia_ResbSecondDiverseChoice( p, fUseOr, 0,
                    p->nSecondPath );
            if ( !fTop )
                p->nSecondPath = 0;
            if ( iChoice < 0 ||
                 iChoice >= Vec_IntSize(p->vUnateLits[!fUseOr]) )
                return -1;
            iDiv         = Vec_IntEntry( p->vUnateLits[!fUseOr], iChoice );
            if ( fTop )
                p->fChoiceSelected = 1;
            int fComp   = Abc_LitIsCompl(iDiv);
            word * pDiv = (word *)Vec_PtrEntry( p->vDivs, Abc_Lit2Var(iDiv) );
            Abc_TtAndSharp( p->pSets[fUseOr], p->pSets[fUseOr], pDiv, p->nWords, !fComp );
            if ( p->fVerbose )
                printf( "\n" ); 
            if ( fTop && p->fSkipTemplates && p->fUseResidualCache )
                iCacheEntry = Gia_ResbResidualCacheFindOrAdd( p, 1,
                    fUseOr, nLimit-1, p->nCurrentPath, &fCacheHit );
            p->nSecondPath = fTop ? p->nCurrentPath : 0;
            if ( fCacheHit )
                iResLit = Gia_ResbResidualCacheLoad( p, iCacheEntry, 1 );
            else
            {
                if ( p->fProfilePivots )
                    clkCache = Abc_Clock();
                iResLit = Gia_ManResubPerform_rec( p, nLimit-1, Depth, 0 );
                if ( p->fProfilePivots )
                    timeSolve = Abc_Clock() - clkCache;
                if ( iCacheEntry >= 0 )
                    Gia_ResbResidualCacheStore( p, iCacheEntry, iResLit,
                        timeSolve );
            }
            p->nSecondPath = 0;
            if ( iResLit >= 0 ) 
            {
                int iNode = nVars + Vec_IntSize(p->vGates)/2;
                if ( iDiv < iResLit )
                    Vec_IntPushTwo( p->vGates, Abc_LitNot(iDiv), Abc_LitNotCond(iResLit, fUseOr) );
                else
                    Vec_IntPushTwo( p->vGates, Abc_LitNotCond(iResLit, fUseOr), Abc_LitNot(iDiv) );
                return Abc_Var2Lit( iNode, fUseOr );
            }
        }
        if ( Max2 == 0 )
            return -1;
    }
    else
    {
        if ( nLimit >= 3 && (Max2 == TopTwoW[0] || Max2 == TopTwoW[1]) )
        {
            int fUseOr  = Max2 == TopTwoW[0];
            int iDiv, iCacheEntry = -1, fCacheHit = 0;
            abctime clkCache = 0, timeSolve = 0;
            if ( fTop && p->fSkipTemplates && p->fUseSolvSched &&
                 p->nCurrentPath == 1 )
                iChoice = Gia_ResbSolvScheduleChoice( p, fUseOr, 1,
                    iChoice, nLimit-2 );
            if ( fTop && p->fProfilePivots )
                Gia_ResbProfileTopChoice( p, fUseOr, 1, iChoice );
            if ( fTop && p->fSkipTemplates )
                p->nStage5TopFrontier = p->fQualityNoTruncation ?
                    Vec_IntSize(p->vUnatePairs[!fUseOr]) : Abc_MinInt(
                    Vec_IntSize(p->vUnatePairs[!fUseOr]), p->nDivsMax);
            if ( !fTop && p->nSecondPath > 1 )
                iChoice = Gia_ResbSecondDiverseChoice( p, fUseOr, 1,
                    p->nSecondPath );
            if ( !fTop )
                p->nSecondPath = 0;
            if ( iChoice < 0 ||
                 iChoice >= Vec_IntSize(p->vUnatePairs[!fUseOr]) )
                return -1;
            iDiv         = Vec_IntEntry( p->vUnatePairs[!fUseOr], iChoice );
            if ( fTop )
                p->fChoiceSelected = 1;
            int fComp   = Abc_LitIsCompl(iDiv);
            Gia_ManDeriveDivPair( p, iDiv, p->vDivs, p->nWords, p->pDivA );
            Abc_TtAndSharp( p->pSets[fUseOr], p->pSets[fUseOr], p->pDivA, p->nWords, !fComp );
            if ( p->fVerbose )
                printf( "\n" ); 
            if ( fTop && p->fSkipTemplates && p->fUseResidualCache )
                iCacheEntry = Gia_ResbResidualCacheFindOrAdd( p, 2,
                    fUseOr, nLimit-2, p->nCurrentPath, &fCacheHit );
            p->nSecondPath = fTop ? p->nCurrentPath : 0;
            if ( fCacheHit )
                iResLit = Gia_ResbResidualCacheLoad( p, iCacheEntry, 2 );
            else
            {
                if ( p->fProfilePivots )
                    clkCache = Abc_Clock();
                iResLit = Gia_ManResubPerform_rec( p, nLimit-2, Depth, 0 );
                if ( p->fProfilePivots )
                    timeSolve = Abc_Clock() - clkCache;
                if ( iCacheEntry >= 0 )
                    Gia_ResbResidualCacheStore( p, iCacheEntry, iResLit,
                        timeSolve );
            }
            p->nSecondPath = 0;
            if ( iResLit >= 0 ) 
            {
                int iNode = nVars + Vec_IntSize(p->vGates)/2;
                int iDiv0 = Gia_ResbPairLit0(p, iDiv);
                int iDiv1 = Gia_ResbPairLit1(p, iDiv);
                Vec_IntPushTwo( p->vGates, iDiv0, iDiv1 );
                Vec_IntPushTwo( p->vGates, Abc_LitNotCond(iResLit, fUseOr), Abc_Var2Lit(iNode, !fComp) );
                return Abc_Var2Lit( iNode+1, fUseOr );
            }
        }
        if ( Max1 == 0 )
            return -1;
    }
    return -1;
}
static void Gia_ManResubPerformProfile( Gia_ResbMan_t * p,
    Vec_Ptr_t * vDivs, int nWords, int nLimit, int nDivsMax, int iChoice,
    int fUseZero, int fUseXor, int fDebug, int fVerbose, int Depth,
    abctime * pTimeInit, abctime * pTimeSearch )
{
    int Res;
    abctime clk = (pTimeInit || pTimeSearch) ? Abc_Clock() : 0;
    Gia_ResbInit( p, vDivs, nWords, nLimit, nDivsMax, iChoice,
        fUseZero, fUseXor, fDebug, fVerbose, fVerbose );
    if ( pTimeInit )
        *pTimeInit += Abc_Clock() - clk;
    if ( pTimeInit || pTimeSearch )
        clk = Abc_Clock();
    Res = Gia_ManResubPerform_rec( p, nLimit, Depth, 1 );
    if ( pTimeSearch )
        *pTimeSearch += Abc_Clock() - clk;
    if ( Res >= 0 ) 
        Vec_IntPush( p->vGates, Res );
    else
        Vec_IntClear( p->vGates );
    if ( fVerbose )
        printf( "\n" );
}
void Gia_ManResubPerform( Gia_ResbMan_t * p, Vec_Ptr_t * vDivs, int nWords, int nLimit, int nDivsMax, int iChoice, int fUseXor, int fDebug, int fVerbose, int Depth )
{
    Gia_ManResubPerformProfile( p, vDivs, nWords, nLimit, nDivsMax,
        iChoice, 1, fUseXor, fDebug, fVerbose, Depth, NULL, NULL );
}
Vec_Int_t * Gia_ManResubOne( Vec_Ptr_t * vDivs, int nWords, int nLimit, int nDivsMax, int iChoice, int fUseXor, int fDebug, int fVerbose, word * pFunc, int Depth )
{
    Vec_Int_t * vRes;
    Gia_ResbMan_t * p = Gia_ResbAlloc( nWords );
    Gia_ManResubPerform( p, vDivs, nWords, nLimit, nDivsMax, iChoice, fUseXor, fDebug, fVerbose, Depth );
    if ( fVerbose )
        Gia_ManResubPrint( p->vGates, Vec_PtrSize(vDivs) );
    if ( !Gia_ManResubVerify(p, pFunc) )
    {
        Gia_ManResubPrint( p->vGates, Vec_PtrSize(vDivs) );
        printf( "Verification FAILED.\n" );
    }
    else if ( fDebug && fVerbose )
        printf( "Verification succeeded." );
    if ( fVerbose )
        printf( "\n" );
    vRes = Vec_IntDup( p->vGates );
    Gia_ResbFree( p );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_ResbMan_t * s_pResbMan = NULL;
void Abc_ResubPrepareManager( int nWords );

// Stateful finite recipe iterator used by &stran root discovery.  Exact
// templates keep nested-loop cursors, while greedy diversity advances one
// pivot at a time.  Thus Next(q) never asks the legacy iChoice engine to skip
// the first q-1 answers again.
#define GIA_RESUB_PIVOT_RANK_BINS 8
#define GIA_RESUB_PIVOT_RATIO_BINS 5
#define GIA_RESUB_PIVOT_KIND_BINS 2
#define GIA_RESUB_MULTIPATH_RANK_BINS 9
#define GIA_RESUB_MULTIPATH_PATH_BINS 4
#define GIA_RESUB_MULTIPATH_CELLS \
    (GIA_RESUB_MULTIPATH_RANK_BINS * GIA_RESUB_MULTIPATH_PATH_BINS)
enum
{
    GIA_RESUB_PIVOT_FRONTIER_FIRST = 0,
    GIA_RESUB_PIVOT_FRONTIER_SIZE,
    GIA_RESUB_PIVOT_FRONTIER_UNIQUE,
    GIA_RESUB_PIVOT_FRONTIER_ZERO_NOVEL,
    GIA_RESUB_PIVOT_FRONTIER_COVER_SUM,
    GIA_RESUB_PIVOT_FRONTIER_NOVEL_SUM,
    GIA_RESUB_PIVOT_ATTEMPT_TOTAL,
    GIA_RESUB_PIVOT_FOUND_TOTAL,
    GIA_RESUB_PIVOT_TIME_TOTAL,
    GIA_RESUB_PIVOT_SCHED_FRONTIERS,
    GIA_RESUB_PIVOT_SCHED_PIVOTS,
    GIA_RESUB_PIVOT_SCHED_COMPLETE,
    GIA_RESUB_PIVOT_SCHED_TIME,
    GIA_RESUB_CACHE_LOOKUPS,
    GIA_RESUB_CACHE_HITS,
    GIA_RESUB_CACHE_MISSES,
    GIA_RESUB_CACHE_SAME_PAGE_HITS,
    GIA_RESUB_CACHE_CROSS_PAGE_HITS,
    GIA_RESUB_CACHE_FAIL_HITS,
    GIA_RESUB_CACHE_SUCCESS_HITS,
    GIA_RESUB_CACHE_SAVED_TIME,
    GIA_RESUB_CACHE_LOOKUP_TIME,
    GIA_RESUB_CACHE_PAYLOAD_BYTES,
    GIA_RESUB_REC_CALLS,
    GIA_RESUB_REC_UNIQUE,
    GIA_RESUB_REC_DUPLICATE,
    GIA_RESUB_REC_SAME_PAGE,
    GIA_RESUB_REC_CROSS_PAGE,
    GIA_RESUB_REC_FAIL_HITS,
    GIA_RESUB_REC_SUCCESS_DUPLICATE,
    GIA_RESUB_REC_PAYLOAD_BYTES,
    GIA_RESUB_REC_SAVED_TIME,
    GIA_RESUB_REC_LOOKUP_TIME,
    GIA_RESUB_REC_DUP_DEPTH_0,
    GIA_RESUB_REC_DUP_DEPTH_1,
    GIA_RESUB_REC_DUP_DEPTH_2,
    GIA_RESUB_REC_DUP_DEPTH_3PLUS,
    GIA_RESUB_MULTIPATH_CACHE_ENTRIES,
    GIA_RESUB_MULTIPATH_CACHE_LOOKUPS,
    GIA_RESUB_MULTIPATH_CACHE_HITS,
    GIA_RESUB_MULTIPATH_CACHE_FAIL_HITS,
    GIA_RESUB_MULTIPATH_CACHE_SUCCESS_HITS,
    GIA_RESUB_MULTIPATH_CACHE_PAYLOAD_BYTES,
    GIA_RESUB_MULTIPATH_ATTEMPTS,
    GIA_RESUB_MULTIPATH_FOUND = GIA_RESUB_MULTIPATH_ATTEMPTS +
        GIA_RESUB_MULTIPATH_CELLS,
    GIA_RESUB_MULTIPATH_TIME = GIA_RESUB_MULTIPATH_FOUND +
        GIA_RESUB_MULTIPATH_CELLS,
    GIA_RESUB_MULTIPATH_SECOND_COVER = GIA_RESUB_MULTIPATH_TIME +
        GIA_RESUB_MULTIPATH_CELLS,
    GIA_RESUB_MULTIPATH_DIVERSITY_NEW =
        GIA_RESUB_MULTIPATH_SECOND_COVER + GIA_RESUB_MULTIPATH_CELLS,
    GIA_RESUB_MULTIPATH_DIVERSITY_SYM =
        GIA_RESUB_MULTIPATH_DIVERSITY_NEW + GIA_RESUB_MULTIPATH_CELLS,
    GIA_RESUB_PIVOT_CURRENT_PATH = GIA_RESUB_MULTIPATH_DIVERSITY_SYM +
        GIA_RESUB_MULTIPATH_CELLS,
    GIA_RESUB_PIVOT_CURRENT_SECOND_RANK,
    GIA_RESUB_PIVOT_CURRENT_SECOND_COVER,
    GIA_RESUB_PIVOT_CURRENT_DIVERSITY_NEW,
    GIA_RESUB_PIVOT_CURRENT_DIVERSITY_SYM,
    GIA_RESUB_PIVOT_CURRENT_VALID,
    GIA_RESUB_PIVOT_CURRENT_KIND,
    GIA_RESUB_PIVOT_CURRENT_RANK,
    GIA_RESUB_PIVOT_CURRENT_COVER,
    GIA_RESUB_PIVOT_CURRENT_TOTAL,
    GIA_RESUB_PIVOT_CURRENT_NOVEL,
    GIA_RESUB_PIVOT_CURRENT_REMAIN,
    GIA_RESUB_PIVOT_CURRENT_DUPLICATE,
    GIA_RESUB_PIVOT_RANK_ATTEMPTS,
    GIA_RESUB_PIVOT_RANK_FOUND = GIA_RESUB_PIVOT_RANK_ATTEMPTS +
        GIA_RESUB_PIVOT_RANK_BINS,
    GIA_RESUB_PIVOT_RANK_TIME = GIA_RESUB_PIVOT_RANK_FOUND +
        GIA_RESUB_PIVOT_RANK_BINS,
    GIA_RESUB_PIVOT_NOVEL_ATTEMPTS = GIA_RESUB_PIVOT_RANK_TIME +
        GIA_RESUB_PIVOT_RANK_BINS,
    GIA_RESUB_PIVOT_NOVEL_FOUND = GIA_RESUB_PIVOT_NOVEL_ATTEMPTS +
        GIA_RESUB_PIVOT_RATIO_BINS,
    GIA_RESUB_PIVOT_NOVEL_TIME = GIA_RESUB_PIVOT_NOVEL_FOUND +
        GIA_RESUB_PIVOT_RATIO_BINS,
    GIA_RESUB_PIVOT_COVER_ATTEMPTS = GIA_RESUB_PIVOT_NOVEL_TIME +
        GIA_RESUB_PIVOT_RATIO_BINS,
    GIA_RESUB_PIVOT_COVER_FOUND = GIA_RESUB_PIVOT_COVER_ATTEMPTS +
        GIA_RESUB_PIVOT_RATIO_BINS,
    GIA_RESUB_PIVOT_COVER_TIME = GIA_RESUB_PIVOT_COVER_FOUND +
        GIA_RESUB_PIVOT_RATIO_BINS,
    GIA_RESUB_PIVOT_KIND_ATTEMPTS = GIA_RESUB_PIVOT_COVER_TIME +
        GIA_RESUB_PIVOT_RATIO_BINS,
    GIA_RESUB_PIVOT_KIND_FOUND = GIA_RESUB_PIVOT_KIND_ATTEMPTS +
        GIA_RESUB_PIVOT_KIND_BINS,
    GIA_RESUB_PIVOT_KIND_TIME = GIA_RESUB_PIVOT_KIND_FOUND +
        GIA_RESUB_PIVOT_KIND_BINS,
    GIA_RESUB_PIVOT_STATE_ATTEMPTS = GIA_RESUB_PIVOT_KIND_TIME +
        GIA_RESUB_PIVOT_KIND_BINS,
    GIA_RESUB_PIVOT_STATE_FOUND = GIA_RESUB_PIVOT_STATE_ATTEMPTS + 2,
    GIA_RESUB_PIVOT_STATE_TIME = GIA_RESUB_PIVOT_STATE_FOUND + 2,
    GIA_RESUB_PIVOT_PROFILE_SIZE = GIA_RESUB_PIVOT_STATE_TIME + 2
};
typedef struct Gia_ResbIter_t_ Gia_ResbIter_t;
typedef struct Gia_ResbMemoEntry_t_ Gia_ResbMemoEntry_t;
struct Gia_ResbIter_t_
{
    Gia_ResbMan_t * p;
    int Stage;
    int n, i, k;
    int iGreedy;
    int nTotal[2];
    int fPreparedUnates;
    int fPreparedPairs;
    Gia_ResbMemoEntry_t * pMemo;
    int fMemoReplay, iMemo;
    long long PivotProfile[GIA_RESUB_PIVOT_PROFILE_SIZE];
    long long CacheProfileLast[GIA_RESUB_REC_DUP_DEPTH_3PLUS -
        GIA_RESUB_CACHE_LOOKUPS + 1];
    long long MultiPathCacheProfileLast[6];
};

// Legacy cursors retain their exact six scalar values. Care-pair cursors
// carry policy identity above the low stage bits, including pages that have
// not yet created a residual root cache.
#define GIA_RESUB_CURSOR_CARE_PAIR (1 << 16)

#include "giaResubMemo.h"

static int Gia_ResbPivotRankBin( int Rank )
{
    return Rank <= 1 ? 0 : Rank == 2 ? 1 : Rank <= 4 ? 2 :
        Rank <= 8 ? 3 : Rank <= 16 ? 4 : Rank <= 32 ? 5 :
        Rank <= 64 ? 6 : 7;
}

static int Gia_ResbPivotRatioBin( int Value, int Total )
{
    if ( Value <= 0 || Total <= 0 )
        return 0;
    return 100 * Value <= 25 * Total ? 1 :
        100 * Value <= 50 * Total ? 2 :
        100 * Value <= 75 * Total ? 3 : 4;
}

static void Gia_ResbIterProfilePivot( Gia_ResbIter_t * pIt, int fFound,
    abctime Time )
{
    Gia_ResbMan_t * p = pIt->p;
    long long * pProf = pIt->PivotProfile;
    int RankBin, NovelBin, CoverBin, KindBin, StateBin;
    int MultiRank, MultiPath, MultiCell;
    if ( !p->fProfilePivots || !p->fChoiceSelected )
        return;
    RankBin = Gia_ResbPivotRankBin( p->nTopPivotRank );
    NovelBin = Gia_ResbPivotRatioBin( p->nTopPivotNovel,
        p->nTopPivotCover );
    CoverBin = Gia_ResbPivotRatioBin( p->nTopPivotCover,
        p->nTopPivotTotal );
    KindBin = p->nTopPivotKind - 1;
    StateBin = p->fTopPivotDuplicate != 0;
    MultiRank = p->nTopPivotRank <= 8 ? p->nTopPivotRank - 1 : 8;
    MultiPath = Abc_MinInt(Abc_MaxInt(p->nCurrentPath, 1), 4) - 1;
    MultiCell = MultiRank * GIA_RESUB_MULTIPATH_PATH_BINS + MultiPath;
    assert( KindBin >= 0 && KindBin < GIA_RESUB_PIVOT_KIND_BINS );
    assert( MultiRank >= 0 &&
        MultiRank < GIA_RESUB_MULTIPATH_RANK_BINS );
    pProf[GIA_RESUB_PIVOT_ATTEMPT_TOTAL]++;
    pProf[GIA_RESUB_PIVOT_FOUND_TOTAL] += fFound;
    pProf[GIA_RESUB_PIVOT_TIME_TOTAL] += Time;
    pProf[GIA_RESUB_PIVOT_RANK_ATTEMPTS + RankBin]++;
    pProf[GIA_RESUB_PIVOT_RANK_FOUND + RankBin] += fFound;
    pProf[GIA_RESUB_PIVOT_RANK_TIME + RankBin] += Time;
    pProf[GIA_RESUB_PIVOT_NOVEL_ATTEMPTS + NovelBin]++;
    pProf[GIA_RESUB_PIVOT_NOVEL_FOUND + NovelBin] += fFound;
    pProf[GIA_RESUB_PIVOT_NOVEL_TIME + NovelBin] += Time;
    pProf[GIA_RESUB_PIVOT_COVER_ATTEMPTS + CoverBin]++;
    pProf[GIA_RESUB_PIVOT_COVER_FOUND + CoverBin] += fFound;
    pProf[GIA_RESUB_PIVOT_COVER_TIME + CoverBin] += Time;
    pProf[GIA_RESUB_PIVOT_KIND_ATTEMPTS + KindBin]++;
    pProf[GIA_RESUB_PIVOT_KIND_FOUND + KindBin] += fFound;
    pProf[GIA_RESUB_PIVOT_KIND_TIME + KindBin] += Time;
    pProf[GIA_RESUB_PIVOT_STATE_ATTEMPTS + StateBin]++;
    pProf[GIA_RESUB_PIVOT_STATE_FOUND + StateBin] += fFound;
    pProf[GIA_RESUB_PIVOT_STATE_TIME + StateBin] += Time;
    pProf[GIA_RESUB_MULTIPATH_ATTEMPTS + MultiCell]++;
    pProf[GIA_RESUB_MULTIPATH_FOUND + MultiCell] += fFound;
    pProf[GIA_RESUB_MULTIPATH_TIME + MultiCell] += Time;
    if ( p->fSecondPivotSelected )
    {
        pProf[GIA_RESUB_MULTIPATH_SECOND_COVER + MultiCell] +=
            p->nSecondPivotCover;
        pProf[GIA_RESUB_MULTIPATH_DIVERSITY_NEW + MultiCell] +=
            p->nSecondPivotNew;
        pProf[GIA_RESUB_MULTIPATH_DIVERSITY_SYM + MultiCell] +=
            p->nSecondPivotSym;
    }
    if ( fFound )
    {
        pProf[GIA_RESUB_PIVOT_CURRENT_PATH] = p->nCurrentPath;
        pProf[GIA_RESUB_PIVOT_CURRENT_SECOND_RANK] =
            p->nSecondPivotRank;
        pProf[GIA_RESUB_PIVOT_CURRENT_SECOND_COVER] =
            p->nSecondPivotCover;
        pProf[GIA_RESUB_PIVOT_CURRENT_DIVERSITY_NEW] =
            p->nSecondPivotNew;
        pProf[GIA_RESUB_PIVOT_CURRENT_DIVERSITY_SYM] =
            p->nSecondPivotSym;
        pProf[GIA_RESUB_PIVOT_CURRENT_VALID] = 1;
        pProf[GIA_RESUB_PIVOT_CURRENT_KIND] = p->nTopPivotKind;
        pProf[GIA_RESUB_PIVOT_CURRENT_RANK] = p->nTopPivotRank;
        pProf[GIA_RESUB_PIVOT_CURRENT_COVER] = p->nTopPivotCover;
        pProf[GIA_RESUB_PIVOT_CURRENT_TOTAL] = p->nTopPivotTotal;
        pProf[GIA_RESUB_PIVOT_CURRENT_NOVEL] = p->nTopPivotNovel;
        pProf[GIA_RESUB_PIVOT_CURRENT_REMAIN] = p->nTopPivotRemain;
        pProf[GIA_RESUB_PIVOT_CURRENT_DUPLICATE] =
            p->fTopPivotDuplicate;
    }
}

static void Gia_ResbIterProfileSchedule( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    if ( !p->fProfilePivots || !p->fSolvScheduleReady ||
         p->fSolvScheduleProfiled )
        return;
    pIt->PivotProfile[GIA_RESUB_PIVOT_SCHED_FRONTIERS]++;
    pIt->PivotProfile[GIA_RESUB_PIVOT_SCHED_PIVOTS] +=
        p->nSolvSchedulePivots;
    pIt->PivotProfile[GIA_RESUB_PIVOT_SCHED_COMPLETE] +=
        p->nSolvScheduleComplete;
    pIt->PivotProfile[GIA_RESUB_PIVOT_SCHED_TIME] +=
        p->timeSolvSchedule;
    p->fSolvScheduleProfiled = 1;
}

static void Gia_ResbIterProfileCache( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    long long Values[] = {
        p->nResidualCacheLookups,
        p->nResidualCacheHitsTotal,
        p->nResidualCacheMisses,
        p->nResidualCacheSamePageHits,
        p->nResidualCacheCrossPageHits,
        p->nResidualCacheFailHits,
        p->nResidualCacheSuccessHits,
        (long long)p->timeResidualCacheSaved,
        (long long)p->timeResidualCacheLookup,
        p->nResidualCachePayloadBytes,
        p->nResidualRecCalls,
        p->nResidualRecUnique,
        p->nResidualRecDuplicate,
        p->nResidualRecSamePage,
        p->nResidualRecCrossPage,
        p->nResidualRecFailHits,
        p->nResidualRecSuccessDuplicate,
        p->nResidualRecPayloadBytes,
        (long long)p->timeResidualRecSaved,
        (long long)p->timeResidualRecLookup,
        p->nResidualRecDuplicateDepth[0],
        p->nResidualRecDuplicateDepth[1],
        p->nResidualRecDuplicateDepth[2],
        p->nResidualRecDuplicateDepth[3]
    };
    int i, nSize = sizeof(Values) / sizeof(Values[0]);
    long long MultiPathValues[6] = {
        p->nMultiPathCacheEntries,
        p->nMultiPathCacheLookups,
        p->nMultiPathCacheHits,
        p->nMultiPathCacheFailHits,
        p->nMultiPathCacheSuccessHits,
        p->nMultiPathCachePayloadBytes
    };
    assert( nSize == GIA_RESUB_REC_DUP_DEPTH_3PLUS -
        GIA_RESUB_CACHE_LOOKUPS + 1 );
    if ( !p->fProfilePivots )
        return;
    for ( i = 0; i < nSize; i++ )
    {
        pIt->PivotProfile[GIA_RESUB_CACHE_LOOKUPS + i] +=
            Values[i] - pIt->CacheProfileLast[i];
        pIt->CacheProfileLast[i] = Values[i];
    }
    for ( i = 0; i < 6; i++ )
    {
        pIt->PivotProfile[GIA_RESUB_MULTIPATH_CACHE_ENTRIES + i] +=
            MultiPathValues[i] - pIt->MultiPathCacheProfileLast[i];
        pIt->MultiPathCacheProfileLast[i] = MultiPathValues[i];
    }
}

static void Gia_ResbIterEmitOne( Gia_ResbMan_t * p, int iLit0,
    int iLit1, int fCompl )
{
    int iNode = Vec_PtrSize(p->vDivs);
    Vec_IntClear( p->vGates );
    Vec_IntPushTwo( p->vGates, iLit0, iLit1 );
    Vec_IntPush( p->vGates, Abc_Var2Lit(iNode, fCompl) );
}

static void Gia_ResbPreproofEvent( Gia_ResbMan_t * p,
    char const * pStage, int fEnd, long long nWork )
{
    char const * pEnv = getenv("ABC_STRICT_PREPROOF_TRACE");
    if ( !p->fProfilePivots || !pEnv || !atoi(pEnv) ) return;
    Abc_Print( 1, "stran-resub preproof: schema=1 stage=%s event=%s divs=%d words=%d unate0=%d unate1=%d pairs0=%d pairs1=%d work=%lld since-sec=%.6f\n",
        pStage, fEnd ? "END" : "BEGIN", Vec_PtrSize(p->vDivs)-2,
        p->nWords, Vec_IntSize(p->vUnateLits[0]), Vec_IntSize(p->vUnateLits[1]),
        Vec_IntSize(p->vUnatePairs[0]), Vec_IntSize(p->vUnatePairs[1]), nWork,
        (double)Abc_Clock()/CLOCKS_PER_SEC );
    fflush( stdout );
}

static void Gia_ResbIterPrepareUnates( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    int n;
    if ( pIt->fPreparedUnates )
        return;
    Gia_ResbPreproofEvent( p, "prepare-unates", 0, 0 );
    for ( n = 0; n < 2; n++ )
    {
        pIt->nTotal[n] = Abc_TtCountOnesVec( p->pSets[!n], p->nWords );
        Gia_ManFindOneUnateInt( p->pSets[n], p->pSets[!n], p->vDivs,
            p->nWords, p->vUnateLits[n], p->vNotUnateVars[n] );
    }
    Gia_ManSortUnates( p->pSets, p->vDivs, p->nWords,
        p->vUnateLits, p->vUnateLitsW, p->vSorter );
    pIt->fPreparedUnates = 1;
    Gia_ResbPreproofEvent( p, "prepare-unates", 1, Vec_PtrSize(p->vDivs)-2 );
}

static void Gia_ResbIterPreparePairs( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    int n;
    if ( pIt->fPreparedPairs )
        return;
    Gia_ResbPreproofEvent( p, "prepare-pairs", 0, 0 );
    Gia_ResbIterPrepareUnates( pIt );
    Vec_IntTwoFindCommon( p->vNotUnateVars[0], p->vNotUnateVars[1],
        p->vBinateVars );
    if ( !p->fQualityNoTruncation && Vec_IntSize(p->vBinateVars) > p->nDivsMax )
        Vec_IntShrink( p->vBinateVars, p->nDivsMax );
    Gia_ManSortBinate( p->pSets, p->vDivs, p->nWords,
        p->vBinateVars, p->vSorter );
    Gia_ResbPreproofEvent( p, "find-pairs", 0, Vec_IntSize(Gia_ResbPairVars(p)) );
    Gia_ManFindUnatePairs( p, p->pSets, p->vDivs, p->nWords,
        Gia_ResbPairVars(p), p->vUnatePairs, 0 );
    Gia_ResbPreproofEvent( p, "find-pairs", 1,
        Vec_IntSize(p->vUnatePairs[0]) + Vec_IntSize(p->vUnatePairs[1]) );
    Gia_ResbPreproofEvent( p, "sort-pairs", 0, 0 );
    Gia_ManSortPairs( p, p->pSets, p->vDivs, p->nWords,
        p->vUnatePairs, p->vUnatePairsW, p->vSorter );
    Gia_ResbPreproofEvent( p, "sort-pairs", 1,
        Vec_IntSize(p->vUnatePairs[0]) + Vec_IntSize(p->vUnatePairs[1]) );
    // A physical B-wide divisor pool can induce O(B^2) pair literals.  Letting
    // the exact gate-gate stage take the Cartesian square of that entire list
    // turns one root into O(B^4) enumeration (loopv3 stalls at B=64).  The
    // ranked exact-pair frontier is itself B-wide.  The iterator exposes this
    // finite universe lazily; root discovery stops calling Next as soon as its
    // q canonical candidates have been retained.
    for ( n = 0; n < 2; n++ )
        if ( !p->fQualityNoTruncation && Vec_IntSize(p->vUnatePairs[n]) > p->nDivsMax )
        {
            Vec_IntShrink( p->vUnatePairs[n], p->nDivsMax );
            Vec_IntShrink( p->vUnatePairsW[n], p->nDivsMax );
        }
    pIt->fPreparedPairs = 1;
    Gia_ResbPreproofEvent( p, "prepare-pairs", 1,
        Vec_IntSize(p->vUnatePairs[0]) + Vec_IntSize(p->vUnatePairs[1]) );
}

static int Gia_ResbIterNextOneGate( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    int nTotal, iDiv0, iDiv1, Cover0, Cover1;
    // One-gate enumeration needs only literal coverage. Defer quadratic
    // binate-pair work until a later template stage actually consumes it.
    Gia_ResbIterPrepareUnates( pIt );
    for ( ; pIt->n < 2; pIt->n++, pIt->i = 0, pIt->k = 1 )
    {
        nTotal = pIt->nTotal[pIt->n];
        for ( ; pIt->i < Vec_IntSize(p->vUnateLits[pIt->n]);
              pIt->i++, pIt->k = pIt->i + 1 )
        {
            iDiv0 = Vec_IntEntry( p->vUnateLits[pIt->n], pIt->i );
            Cover0 = Vec_IntEntry( p->vUnateLitsW[pIt->n], pIt->i );
            if ( 2 * Cover0 < nTotal )
                break;
            for ( ; pIt->k < Vec_IntSize(p->vUnateLits[pIt->n]);
                  pIt->k++ )
            {
                word * pDiv0, * pDiv1;
                int a, b;
                iDiv1 = Vec_IntEntry( p->vUnateLits[pIt->n], pIt->k );
                Cover1 = Vec_IntEntry( p->vUnateLitsW[pIt->n], pIt->k );
                if ( Cover0 + Cover1 < nTotal )
                    break;
                pDiv0 = (word *)Vec_PtrEntry(p->vDivs, Abc_Lit2Var(iDiv0));
                pDiv1 = (word *)Vec_PtrEntry(p->vDivs, Abc_Lit2Var(iDiv1));
                if ( !Gia_ManDivCover(p->pSets[pIt->n],
                        p->pSets[!pIt->n], pDiv0,
                        Abc_LitIsCompl(iDiv0), pDiv1,
                        Abc_LitIsCompl(iDiv1), p->nWords) )
                    continue;
                a = Abc_LitNot( Abc_MinInt(iDiv0, iDiv1) );
                b = Abc_LitNot( Abc_MaxInt(iDiv0, iDiv1) );
                pIt->k++;
                Gia_ResbIterEmitOne( p, a, b, !pIt->n );
                return 1;
            }
        }
    }
    return 0;
}

static int Gia_ResbIterNextDivGate( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    int nTotal, iDiv0, iPair, Cover0, Cover1;
    Gia_ResbIterPreparePairs( pIt );
    for ( ; pIt->n < 2; pIt->n++, pIt->i = pIt->k = 0 )
    {
        nTotal = pIt->nTotal[pIt->n];
        for ( ; pIt->i < Vec_IntSize(p->vUnateLits[pIt->n]);
              pIt->i++, pIt->k = 0 )
        {
            iDiv0 = Vec_IntEntry( p->vUnateLits[pIt->n], pIt->i );
            Cover0 = Vec_IntEntry( p->vUnateLitsW[pIt->n], pIt->i );
            if ( Vec_IntSize(p->vUnatePairsW[pIt->n]) == 0 ||
                 Cover0 + Vec_IntEntry(p->vUnatePairsW[pIt->n], 0) < nTotal )
                break;
            for ( ; pIt->k < Vec_IntSize(p->vUnatePairs[pIt->n]);
                  pIt->k++ )
            {
                int iNode = Vec_PtrSize(p->vDivs), fPair, iLit0, iLit1;
                word * pDiv0;
                iPair = Vec_IntEntry( p->vUnatePairs[pIt->n], pIt->k );
                Cover1 = Vec_IntEntry( p->vUnatePairsW[pIt->n], pIt->k );
                if ( Cover0 + Cover1 < nTotal )
                    break;
                pDiv0 = (word *)Vec_PtrEntry(p->vDivs, Abc_Lit2Var(iDiv0));
                Gia_ManDeriveDivPair( p, iPair, p->vDivs, p->nWords,
                    p->pDivA );
                fPair = Abc_LitIsCompl( iPair );
                if ( !Gia_ManDivCover(p->pSets[pIt->n],
                        p->pSets[!pIt->n], pDiv0,
                        Abc_LitIsCompl(iDiv0), p->pDivA, fPair,
                        p->nWords) )
                    continue;
                iLit0 = Gia_ResbPairLit0(p, iPair);
                iLit1 = Gia_ResbPairLit1(p, iPair);
                Vec_IntClear( p->vGates );
                Vec_IntPushTwo( p->vGates, iLit0, iLit1 );
                Vec_IntPushTwo( p->vGates, Abc_LitNot(iDiv0),
                    Abc_Var2Lit(iNode, !fPair) );
                Vec_IntPush( p->vGates,
                    Abc_Var2Lit(iNode + 1, !pIt->n) );
                pIt->k++;
                return 1;
            }
        }
    }
    return 0;
}

static int Gia_ResbIterNextGateGate( Gia_ResbIter_t * pIt )
{
    Gia_ResbMan_t * p = pIt->p;
    int nTotal, iPair0, iPair1, Cover0, Cover1;
    Gia_ResbIterPreparePairs( pIt );
    for ( ; pIt->n < 2; pIt->n++, pIt->i = 0, pIt->k = 1 )
    {
        nTotal = pIt->nTotal[pIt->n];
        for ( ; pIt->i < Vec_IntSize(p->vUnatePairs[pIt->n]);
              pIt->i++, pIt->k = pIt->i + 1 )
        {
            iPair0 = Vec_IntEntry( p->vUnatePairs[pIt->n], pIt->i );
            Cover0 = Vec_IntEntry( p->vUnatePairsW[pIt->n], pIt->i );
            if ( 2 * Cover0 < nTotal )
                break;
            Gia_ManDeriveDivPair( p, iPair0, p->vDivs, p->nWords, p->pDivA );
            for ( ; pIt->k < Vec_IntSize(p->vUnatePairs[pIt->n]);
                  pIt->k++ )
            {
                int iNode = Vec_PtrSize(p->vDivs);
                int a0, a1, b0, b1, f0, f1;
                iPair1 = Vec_IntEntry( p->vUnatePairs[pIt->n], pIt->k );
                Cover1 = Vec_IntEntry( p->vUnatePairsW[pIt->n], pIt->k );
                if ( Cover0 + Cover1 < nTotal )
                    break;
                Gia_ManDeriveDivPair( p, iPair1, p->vDivs, p->nWords,
                    p->pDivB );
                f0 = Abc_LitIsCompl(iPair0);
                f1 = Abc_LitIsCompl(iPair1);
                if ( !Gia_ManDivCover(p->pSets[pIt->n],
                        p->pSets[!pIt->n], p->pDivA, f0,
                        p->pDivB, f1, p->nWords) )
                    continue;
                a0 = Gia_ResbPairLit0(p, iPair0);
                a1 = Gia_ResbPairLit1(p, iPair0);
                b0 = Gia_ResbPairLit0(p, iPair1);
                b1 = Gia_ResbPairLit1(p, iPair1);
                Vec_IntClear( p->vGates );
                Vec_IntPushTwo( p->vGates, a0, a1 );
                Vec_IntPushTwo( p->vGates, b0, b1 );
                Vec_IntPushTwo( p->vGates,
                    Abc_Var2Lit(iNode, !f0),
                    Abc_Var2Lit(iNode + 1, !f1) );
                Vec_IntPush( p->vGates,
                    Abc_Var2Lit(iNode + 2, !pIt->n) );
                pIt->k++;
                return 1;
            }
        }
    }
    return 0;
}

void * Abc_ResubIteratorStart( void ** ppDivs, int nDivs, int nWords,
    int nLimit, int nDivsMax, int fUseZero, int fUseXor )
{
    Gia_ResbIter_t * pIt = ABC_CALLOC( Gia_ResbIter_t, 1 );
    Vec_Ptr_t Divs = { nDivs, nDivs, ppDivs };
    pIt->p = Gia_ResbAlloc( nWords );
    Gia_ResbInit( pIt->p, &Divs, nWords, nLimit, nDivsMax, 0,
        fUseZero, fUseXor, 0, 0, 0 );
    // Root mode currently uses AND templates.  Preserve the legacy API for
    // XOR callers rather than silently changing their recipe universe.
    if ( fUseXor )
        pIt->Stage = 5;
    else
        pIt->Stage = 1;
    pIt->n = pIt->i = 0;
    pIt->k = 1;
    return pIt;
}

// Resume one iterator cursor on the pass-owned resubstitution manager.  The
// low stage bits and three loop cursors retain their original meaning. The
// stage word additionally records the captured care-pair policy. The fifth remains
// the historical Stage-5 rank cursor with paths=1; with paths>1 it is the
// documented flattened schedule slot.  The sixth stores only the classified
// Stage-5 top-frontier length needed to decode that slot after rebinding.  A
// separate opaque root slot owns only exact residual memo entries across
// pages; all sorting and recipe scratch remains shared.  Rebinding is
// deterministic because callers present the same ordered divisor set while
// the circuit snapshot is immutable.
void * Abc_ResubIteratorResumeStart( void ** ppDivs, int nDivs, int nWords,
    int nLimit, int nDivsMax, int fUseZero, int fUseXor,
    int fUseSolvSched, int nStage5Paths, int fProfilePivots, int * pCursor,
    void ** ppRootCache )
{
    Gia_ResbIter_t * pIt = ABC_CALLOC( Gia_ResbIter_t, 1 );
    Vec_Ptr_t Divs = { nDivs, nDivs, ppDivs };
    Gia_ResbRootCache_t * pCache = ppRootCache ?
        (Gia_ResbRootCache_t *)*ppRootCache : NULL;
    nStage5Paths = nStage5Paths <= 1 ? 1 : nStage5Paths;
    assert( nStage5Paths == 1 || nStage5Paths == 2 ||
        nStage5Paths == 4 );
    assert( s_pResbMan != NULL );
    assert( s_pResbMan->nWords == nWords );
    // Pair order is part of a live cursor's meaning. A fresh root binding
    // may discard incompatible cache state; continuing old indices under a
    // different policy violates the immutable root/page contract.
    assert( !pCursor[0] ||
        !!(pCursor[0] & GIA_RESUB_CURSOR_CARE_PAIR) ==
            (s_ResubCarePairTruth && !fUseXor) );
    if ( pCache && !Gia_ResbRootCacheCompatible(pCache, &Divs, nWords,
            nLimit, nDivsMax, fUseZero, fUseXor, nStage5Paths) )
    {
        Gia_ResbRootCacheFree( pCache );
        *ppRootCache = NULL;
        pCache = NULL;
    }
    pIt->p = s_pResbMan;
    Gia_ResbInit( pIt->p, &Divs, nWords, nLimit, nDivsMax, 0,
        fUseZero, fUseXor, 0, 0, 0 );
    pIt->p->ppRootCache = ppRootCache;
    if ( pCache )
    {
        pIt->p->pRootCache = pCache;
        pIt->p->iResidualCacheBind = ++pCache->nBinds;
        Gia_ResbRootCacheSwap( pIt->p, pCache );
    }
    pIt->p->fUseSolvSched = fUseSolvSched;
    pIt->p->nStage5Paths = nStage5Paths;
    pIt->p->fProfilePivots = fProfilePivots;
    pIt->p->fPairClassCache = Gia_ResbPairClassCacheMode();
    if ( pCursor[0] )
    {
        pIt->Stage = pCursor[0] & ~GIA_RESUB_CURSOR_CARE_PAIR;
        pIt->n = pCursor[1];
        pIt->i = pCursor[2];
        pIt->k = pCursor[3];
        pIt->iGreedy = pCursor[4];
        pIt->p->nStage5TopFrontier = pCursor[5];
        // Stages 3/4 index the deterministic exact-pair arrays prepared by
        // stage 1.  Reconstruct these arrays once after rebinding.
        if ( pIt->Stage == 3 || pIt->Stage == 4 )
            Gia_ResbIterPreparePairs( pIt );
    }
    else
    {
        pIt->Stage = fUseXor ? 5 : 1;
        pIt->n = pIt->i = 0;
        pIt->k = 1;
    }
    // The historical whole-iterator memo key has no quality mode field.
    if ( !pIt->p->fQualityNoTruncation )
        Gia_ResbMemoBind(pIt,ppDivs,nDivs,nWords,nLimit,nDivsMax,fUseZero,
        fUseXor,fUseSolvSched,nStage5Paths,fProfilePivots,pCursor,ppRootCache);
    return pIt;
}

void Abc_ResubIteratorResumeStop( void * pVoid, int * pCursor )
{
    Gia_ResbIter_t * pIt = (Gia_ResbIter_t *)pVoid;
    if ( pIt == NULL )
        return;
    Gia_ResbMemoUnbind(pIt);
    pCursor[0] = pIt->Stage |
        (pIt->p->fCarePairTruth ? GIA_RESUB_CURSOR_CARE_PAIR : 0);
    pCursor[1] = pIt->n;
    pCursor[2] = pIt->i;
    pCursor[3] = pIt->k;
    pCursor[4] = pIt->iGreedy;
    pCursor[5] = pIt->p->nStage5TopFrontier;
    if ( pIt->p->pRootCache )
    {
        Gia_ResbRootCacheSwap( pIt->p, pIt->p->pRootCache );
        pIt->p->pRootCache = NULL;
    }
    pIt->p->ppRootCache = NULL;
    // The manager belongs to Abc_ResubPrepareManager(), not this cursor.
    pIt->p = NULL;
    ABC_FREE( pIt );
}

#define GIA_RESUB_MULTIPATH_TOP_MAX 8

static int Gia_ResbIterStage5ScheduleSize( Gia_ResbMan_t * p )
{
    // One bootstrap attempt learns the finite actual pivot frontier.  Never
    // substitute INT_MAX, which would schedule empty work after exhaustion.
    int nFrontier = p->fQualityNoTruncation ?
        Abc_MaxInt(1, p->nStage5TopFrontier) :
        (p->nStage5Paths > 1 && p->nStage5TopFrontier ?
            p->nStage5TopFrontier : p->nDivsMax);
    int nEligible = p->fQualityNoTruncation ? nFrontier :
        Abc_MinInt(GIA_RESUB_MULTIPATH_TOP_MAX, nFrontier);
    return nFrontier + nEligible * (p->nStage5Paths - 1);
}

// Decode the flattened fifth cursor without changing the other four cursor
// meanings.  With paths=1 this is exactly the historical rank cursor.  With
// paths>1 it is a deterministic slot cursor over: eligible primaries,
// path-index diagonals, then all remaining original primaries.
static void Gia_ResbIterStage5Decode( Gia_ResbMan_t * p, int Slot,
    int * pTopChoice, int * pPathIndex )
{
    // One bootstrap attempt learns the finite actual pivot frontier.  Never
    // substitute INT_MAX, which would schedule empty work after exhaustion.
    int nFrontier = p->fQualityNoTruncation ?
        Abc_MaxInt(1, p->nStage5TopFrontier) :
        (p->nStage5Paths > 1 && p->nStage5TopFrontier ?
            p->nStage5TopFrontier : p->nDivsMax);
    int nEligible = p->fQualityNoTruncation ? nFrontier :
        Abc_MinInt(GIA_RESUB_MULTIPATH_TOP_MAX, nFrontier);
    if ( p->nStage5Paths == 1 || Slot < nEligible )
    {
        *pTopChoice = Slot;
        *pPathIndex = 1;
    }
    else if ( Slot < nEligible * p->nStage5Paths )
    {
        int Extra = Slot - nEligible;
        *pTopChoice = Extra % nEligible;
        *pPathIndex = 2 + Extra / nEligible;
    }
    else
    {
        *pTopChoice = nEligible +
            (Slot - nEligible * p->nStage5Paths);
        *pPathIndex = 1;
    }
}

static int Gia_ResbIteratorNextReal( void * pVoid, int ** ppArray,
    int * pnAttempt, int * pfExhausted, int * pfInvalid )
{
    Gia_ResbIter_t * pIt = (Gia_ResbIter_t *)pVoid;
    Gia_ResbMan_t * p = pIt->p;
    int Res, fFound;
    memset( pIt->PivotProfile, 0, sizeof(pIt->PivotProfile) );
    *pfExhausted = 0;
    *pfInvalid = 0;
    while ( 1 )
    {
        fFound = 0;
        if ( pIt->Stage == 1 )
        {
            Gia_ResbPreproofEvent( p, "one-gate", 0, 0 );
            if ( p->nLimit >= 1 && Gia_ResbIterNextOneGate(pIt) )
                fFound = 1;
            else
                pIt->Stage = 3, pIt->n = pIt->i = pIt->k = 0;
            Gia_ResbPreproofEvent( p, "one-gate", 1, fFound );
        }
        else if ( pIt->Stage == 3 )
        {
            Gia_ResbPreproofEvent( p, "div-gate", 0, 0 );
            if ( p->nLimit >= 2 && Gia_ResbIterNextDivGate(pIt) )
                fFound = 1;
            else
                pIt->Stage = 4, pIt->n = pIt->i = 0, pIt->k = 1;
            Gia_ResbPreproofEvent( p, "div-gate", 1, fFound );
        }
        else if ( pIt->Stage == 4 )
        {
            Gia_ResbPreproofEvent( p, "gate-gate", 0, 0 );
            if ( p->nLimit >= 3 && Gia_ResbIterNextGateGate(pIt) )
                fFound = 1;
            else
                pIt->Stage = 5;
            Gia_ResbPreproofEvent( p, "gate-gate", 1, fFound );
        }
        else if ( pIt->Stage == 5 )
        {
            abctime clkPivot;
            int fFirstPivot, iStage5Slot, iTopChoice, iPathIndex;
            // The ranked greedy pivot frontier is B-wide.  This is a finite
            // universe invariant, not a time/q cutoff, and guarantees that a
            // future scratch-state regression cannot make Next() nonterminating.
            if ( pIt->iGreedy >= Gia_ResbIterStage5ScheduleSize(p) )
            {
                pIt->Stage = 6;
                continue;
            }
            iStage5Slot = pIt->iGreedy++;
            Gia_ResbIterStage5Decode( p, iStage5Slot, &iTopChoice,
                &iPathIndex );
            // Reset only mutable search storage.  Configuration and the
            // monotonically increasing greedy pivot cursor remain intact.
            Abc_TtCopy( p->pSets[0], (word *)Vec_PtrEntry(p->vDivs, 0),
                p->nWords, 0 );
            Abc_TtCopy( p->pSets[1], (word *)Vec_PtrEntry(p->vDivs, 1),
                p->nWords, 0 );
            Vec_IntClear( p->vGates );
            // The first pivot rebuilds these arrays; later pivots restore the
            // cached top summary before using them.
            Vec_IntClear( p->vUnatePairs[0] );
            Vec_IntClear( p->vUnatePairs[1] );
            Vec_IntClear( p->vUnatePairsW[0] );
            Vec_IntClear( p->vUnatePairsW[1] );
            fFirstPivot = iStage5Slot == 0;
            p->iChoice = iTopChoice;
            p->nCurrentPath = iPathIndex;
            p->nSecondPath = 0;
            p->fSecondPivotSelected = 0;
            p->nSecondPivotRank = 0;
            p->nSecondPivotCover = 0;
            p->nSecondPivotNew = 0;
            p->nSecondPivotSym = 0;
            p->fChoiceSelected = 0;
            p->fSkipTemplates = 1;
            Gia_ResbPreproofEvent( p, "greedy", 0, iStage5Slot );
            if ( p->fProfilePivots )
            {
                clkPivot = Abc_Clock();
                Res = Gia_ManResubPerform_rec( p, p->nLimit, 0, 1 );
                Gia_ResbIterProfilePivot( pIt, Res >= 0,
                    Abc_Clock() - clkPivot );
                Gia_ResbIterProfileSchedule( pIt );
                Gia_ResbIterProfileCache( pIt );
                if ( fFirstPivot )
                {
                    pIt->PivotProfile[GIA_RESUB_PIVOT_FRONTIER_FIRST] = 1;
                    if ( p->fTopPivotProfileReady )
                    {
                        pIt->PivotProfile[GIA_RESUB_PIVOT_FRONTIER_SIZE] =
                            p->nTopFrontier;
                        pIt->PivotProfile[GIA_RESUB_PIVOT_FRONTIER_UNIQUE] =
                            p->nTopFrontierUnique;
                        pIt->PivotProfile[GIA_RESUB_PIVOT_FRONTIER_ZERO_NOVEL] =
                            p->nTopFrontierZeroNovel;
                        pIt->PivotProfile[GIA_RESUB_PIVOT_FRONTIER_COVER_SUM] =
                            p->nTopFrontierCoverSum;
                        pIt->PivotProfile[GIA_RESUB_PIVOT_FRONTIER_NOVEL_SUM] =
                            p->nTopFrontierNovelSum;
                    }
                }
            }
            else
                Res = Gia_ManResubPerform_rec( p, p->nLimit, 0, 1 );
            Gia_ResbPreproofEvent( p, "greedy", 1, iStage5Slot );
            if ( Res >= 0 )
                Vec_IntPush( p->vGates, Res );
            if ( Res >= 0 )
                fFound = 1;
            else if ( !p->fChoiceSelected )
                pIt->Stage = 6;
        }
        else
        {
            *pfExhausted = 1;
            *ppArray = NULL;
            return 0;
        }
        if ( !fFound )
            continue;
        // Check only recipe shape here.  Full OFF/ON simulation is performed
        // once after root-level canonicalization; repeating it in this hot
        // iterator loop makes medium benchmarks tens of times slower.
        if ( Gia_ManResubRecipeIsWellFormed(p) )
            break;
        Vec_IntClear( p->vGates );
        *pfInvalid = 1;
        *ppArray = NULL;
        return 0;
    }
    *ppArray = Vec_IntArray( p->vGates );
    // The caller uses this stage tag only for deterministic ranking: stages
    // 1/3/4 are finite exact templates and stage 5 is greedy diversity.
    if ( pnAttempt )
        *pnAttempt = pIt->Stage;
    return Vec_IntSize( p->vGates );
}

int Abc_ResubIteratorNext( void * pVoid, int ** ppArray,
    int * pnAttempt, int * pfExhausted, int * pfInvalid )
{
    Gia_ResbIter_t * pIt=(Gia_ResbIter_t *)pVoid;
    int Result, Attempt=0;
    if ( pIt->pMemo && pIt->fMemoReplay )
        return Gia_ResbMemoReplay(pIt,ppArray,pnAttempt,pfExhausted,pfInvalid);
    Result=Gia_ResbIteratorNextReal(pVoid,ppArray,&Attempt,pfExhausted,pfInvalid);
    // This is an output parameter, possibly uninitialized by the caller.
    // Preserve the original contract: only yielded recipes write the tag.
    if ( pnAttempt && Result ) *pnAttempt=Attempt;
    if ( pIt->pMemo && !pIt->pMemo->fComplete )
        Gia_ResbMemoRecord(pIt,*ppArray,Result,Attempt,*pfExhausted,*pfInvalid);
    return Result;
}

// Return profiling for all greedy pivots consumed by the most recent Next().
// One Next() may skip several failed pivots internally before yielding a
// recipe, so reporting only the yielded pivot would hide the expensive tail.
int Abc_ResubIteratorReadPivotProfile( void * pVoid, long long * pProfile )
{
    Gia_ResbIter_t * pIt = (Gia_ResbIter_t *)pVoid;
    memcpy( pProfile, pIt->PivotProfile, sizeof(pIt->PivotProfile) );
    return GIA_RESUB_PIVOT_PROFILE_SIZE;
}

void Abc_ResubIteratorStop( void * pVoid )
{
    Gia_ResbIter_t * pIt = (Gia_ResbIter_t *)pVoid;
    if ( pIt == NULL )
        return;
    Gia_ResbFree( pIt->p );
    ABC_FREE( pIt );
}

// A primary FAIL is evidence about path one only.  Exercise the cache key and
// payload directly so a future key simplification cannot suppress a later
// second-pivot variant, and so a successful variant recipe/metrics must survive
// an exact lookup independently of the primary entry.
// Focused invariant checks for the root-only iterator.  These truth tables
// encode the polarity example T=1101,d=1000 and a finite two-divisor cover.
// The helper is intentionally exported only to the in-repository regression
// command; production discovery uses the same Next implementation with a
// pass-owned manager and a resumable cursor whose first five integers retain
// their historical meanings.
// Every nonempty subset of the four two-input valuations, all 16 target
// truth tables, and all eight distinct one-AND/inverter functions. This checks
// representational completeness on partial observations, not just simulation
// consistency of whatever the iterator happens to emit.
// Independent truth evaluation uses the original bound OFF/ON words, not
// the manager's mutable residual sets. Check every yielded native recipe.
// Exhaust all constant/literal, one-AND and two-AND expressions over both
// material phases. The second gate combines the first with a literal; using
// its two phases together adds no new function. These fixtures have no such
// cheaper care completion, rather than just a differently named recipe.
// Compare full public Next streams with one-item pages, including exact
// stage pair rebuilding and complete-problem memo replay. Return actual
// stream counts, preserving duplicate recipes across exact/greedy stages.
// Exercise the public finite iterator rather than only the pair codec.  The
// first mode puts a high-numbered divisor inside the generated pair (the
// Rocket failure shape); the second makes the high divisor the literal that
// closes (a&b)|c.  Prefilling only the drain's intern table forces the real
// generated pair id beyond 15 bits.  A separately rebound paged iterator has
// different opaque ids but must emit the same raw recipe, proving that no
// handle escapes its binding through the cursor/root-cache boundary.
void Abc_ResubPrepareManager( int nWords )
{
    if ( s_pResbMan != NULL )
        Gia_ResbFree( s_pResbMan );
    s_pResbMan = NULL;
    if ( nWords > 0 )
        s_pResbMan = Gia_ResbAlloc( nWords );
}

int Abc_ResubComputeFunction( void ** ppDivs, int nDivs, int nWords, int nLimit, int nDivsMax, int iChoice, int fUseXor, int fDebug, int fVerbose, int ** ppArray )
{
    Vec_Ptr_t Divs = { nDivs, nDivs, ppDivs };
    assert( s_pResbMan != NULL ); // first call Abc_ResubPrepareManager()
    Gia_ManResubPerform( s_pResbMan, &Divs, nWords, nLimit, nDivsMax, iChoice, fUseXor, fDebug, fVerbose==2, 0 );
    if ( fVerbose )
    {
        int nGates = Vec_IntSize(s_pResbMan->vGates)/2;
        if ( nGates )
        {
            printf( "      Gain = %2d  Gates = %2d  __________  F = ", nLimit+1-nGates, nGates );
            Gia_ManResubPrint( s_pResbMan->vGates, nDivs );
            printf( "\n" );
        }
    }
    if ( fDebug )
    {
        if ( !Gia_ManResubVerify(s_pResbMan, NULL) )
        {
            Gia_ManResubPrint( s_pResbMan->vGates, nDivs );
            printf( "Verification FAILED.\n" );
        }
        //else
        //    printf( "Verification succeeded.\n" );
    }
    *ppArray = Vec_IntArray(s_pResbMan->vGates);
    assert( Vec_IntSize(s_pResbMan->vGates)/2 <= nLimit );
    return Vec_IntSize(s_pResbMan->vGates);
}

// Computes an ordered set of structurally distinct recipes.  With zero-gate
// answers enabled, choice zero is bit-for-bit the legacy search.  Additional
// attempts ask the same ordered engine to skip earlier exact solutions or to
// use a later greedy cover pivot.  The exhaustion result distinguishes an
// unavailable choice from an available greedy pivot whose recursive cover
// failed, so callers can enumerate the finite choice space without imposing
// an arbitrary recipe limit.
int Abc_ResubComputeFunctions( void ** ppDivs, int nDivs, int nWords,
    int nLimit, int nDivsMax, int nChoices, int iChoiceStart,
    int fUseZero, int fUseXor,
    int fDebug, int fVerbose, Vec_Wec_t * vResults, int * pnAttempts,
    abctime * pTimeInit, abctime * pTimeSearch,
    abctime * pTimeAttempts, int * pAttemptUnique, int * pfExhausted )
{
    Vec_Ptr_t Divs = { nDivs, nDivs, ppDivs };
    Vec_Int_t * vRecipe;
    int i, k, fDuplicate, nAttemptsMax;
    abctime timeInit, timeSearch;
    assert( s_pResbMan != NULL ); // first call Abc_ResubPrepareManager()
    assert( nChoices > 0 && iChoiceStart >= 0 );
    Vec_WecClear( vResults );
    nAttemptsMax = nChoices;
    if ( pTimeInit )
        *pTimeInit = 0;
    if ( pTimeSearch )
        *pTimeSearch = 0;
    if ( pTimeAttempts )
        memset( pTimeAttempts, 0, sizeof(abctime) * nAttemptsMax );
    if ( pAttemptUnique )
        memset( pAttemptUnique, 0, sizeof(int) * nAttemptsMax );
    if ( pfExhausted )
        *pfExhausted = 0;
    for ( i = 0; i < nAttemptsMax && Vec_WecSize(vResults) < nChoices; i++ )
    {
        timeInit = timeSearch = 0;
        Gia_ManResubPerformProfile( s_pResbMan, &Divs, nWords, nLimit,
            nDivsMax, iChoiceStart + i, fUseZero, fUseXor,
            fDebug, fVerbose==2, 0,
            pTimeInit ? &timeInit : NULL,
            pTimeSearch ? &timeSearch : NULL );
        if ( pTimeInit )
            *pTimeInit += timeInit;
        if ( pTimeSearch )
            *pTimeSearch += timeSearch;
        if ( Vec_IntSize(s_pResbMan->vGates) == 0 &&
             !s_pResbMan->fChoiceSelected )
        {
            if ( pfExhausted )
                *pfExhausted = 1;
            break;
        }
        if ( pTimeAttempts )
            pTimeAttempts[i] = timeInit + timeSearch;
        if ( Vec_IntSize(s_pResbMan->vGates) == 0 )
            continue;
        fDuplicate = 0;
        Vec_WecForEachLevel( vResults, vRecipe, k )
            if ( Vec_IntEqual(vRecipe, s_pResbMan->vGates) )
            {
                fDuplicate = 1;
                break;
            }
        if ( fDuplicate )
            continue;
        if ( pAttemptUnique )
            pAttemptUnique[i] = 1;
        vRecipe = Vec_WecPushLevel( vResults );
        Vec_IntAppend( vRecipe, s_pResbMan->vGates );
        assert( Vec_IntSize(vRecipe)/2 <= nLimit );
        if ( fDebug && !Gia_ManResubVerify(s_pResbMan, NULL) )
        {
            Gia_ManResubPrint( s_pResbMan->vGates, nDivs );
            printf( "Verification FAILED.\n" );
        }
        if ( fVerbose )
        {
            printf( "      Choice = %2d  Gain = %2d  Gates = %2d  __________  F = ",
                iChoiceStart + i, nLimit+1-Vec_IntSize(vRecipe)/2,
                Vec_IntSize(vRecipe)/2 );
            Gia_ManResubPrint( vRecipe, nDivs );
            printf( "\n" );
        }
    }
    if ( pnAttempts )
        *pnAttempts = i;
    return Vec_WecSize(vResults);
}

void Abc_ResubDumpProblem( char * pFileName, void ** ppDivs, int nDivs, int nWords )
{
    Vec_Wrd_t * vSims = Vec_WrdAlloc( nDivs * nWords );
    word ** pDivs = (word **)ppDivs;
    int d, w;
    for ( d = 0; d < nDivs;  d++ )
    for ( w = 0; w < nWords; w++ )
        Vec_WrdPush( vSims, pDivs[d][w] );
    Vec_WrdDumpHex( pFileName, vSims, nWords, 1 );
    Vec_WrdFree( vSims );
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

extern void Extra_PrintHex( FILE * pFile, unsigned * pTruth, int nVars );
extern void Dau_DsdPrintFromTruth2( word * pTruth, int nVarsInit );

void Gia_ManResubTest3()
{
    int nVars = 4;
    int fVerbose = 1;
    word Divs[6] = { 0, 0, 
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00) 
    };
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( 6 );
    Vec_Int_t * vRes = Vec_IntAlloc( 100 );
    int i, k, ArraySize, * pArray; 
    for ( i = 0; i < 6; i++ )
        Vec_PtrPush( vDivs, Divs+i );
    Abc_ResubPrepareManager( 1 );
    for ( i = 0; i < (1<<(1<<nVars)); i++ ) //if ( i == 0xCA ) 
    {
        word Truth = Abc_Tt6Stretch( i, nVars );
        Divs[0] = ~Truth;
        Divs[1] =  Truth;
        printf( "%3d : ", i );
        Extra_PrintHex( stdout, (unsigned*)&Truth, nVars );
        printf( " " );
        Dau_DsdPrintFromTruth2( &Truth, nVars );
        printf( "           " );

        //Abc_ResubDumpProblem( "temp.resub", (void **)Vec_PtrArray(vDivs), Vec_PtrSize(vDivs), 1 );
        ArraySize = Abc_ResubComputeFunction( (void **)Vec_PtrArray(vDivs), Vec_PtrSize(vDivs), 1, 16, 50, 0, 0, 1, fVerbose, &pArray );
        printf( "\n" );

        Vec_IntClear( vRes );
        for ( k = 0; k < ArraySize; k++ )
            Vec_IntPush( vRes, pArray[k] );

        if ( i == 1000 )
            break;
    }
    Abc_ResubPrepareManager( 0 );
    Vec_IntFree( vRes );
    Vec_PtrFree( vDivs );
}
void Gia_ManResubTest3_()
{
    Gia_ResbMan_t * p = Gia_ResbAlloc( 1 );
    word Divs[6] = { 0, 0, 
        ABC_CONST(0xAAAAAAAAAAAAAAAA),
        ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0),
        ABC_CONST(0xFF00FF00FF00FF00) 
    };
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( 6 );
    Vec_Int_t * vRes = Vec_IntAlloc( 100 );
    int i; 
    for ( i = 0; i < 6; i++ )
        Vec_PtrPush( vDivs, Divs+i );

    {
        word Truth = (Divs[2] | Divs[3]) & (Divs[4] & Divs[5]);
//        word Truth = (~Divs[2] | Divs[3]) | ~Divs[4];
        Divs[0] = ~Truth;
        Divs[1] =  Truth;
        Extra_PrintHex( stdout, (unsigned*)&Truth, 6 );
        printf( " " );
        Dau_DsdPrintFromTruth2( &Truth, 6 );
        printf( "       " );
        Gia_ManResubPerform( p, vDivs, 1, 100, 0, 50, 1, 1, 0, 0 );
    }
    Gia_ResbFree( p );
    Vec_IntFree( vRes );
    Vec_PtrFree( vDivs );
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManResubPair( Vec_Wrd_t * vOn, Vec_Wrd_t * vOff, int nWords, int nIns )
{
    Gia_ResbMan_t * p = Gia_ResbAlloc( nWords*2 );
    Vec_Ptr_t * vDivs = Vec_PtrAllocSimInfo( nIns+2, nWords*2 );
    word * pSim; int i;
    Vec_PtrForEachEntry( word *, vDivs, pSim, i )
    {
        if ( i == 0 )
        {
            memset( pSim,        0x00, sizeof(word)*nWords );
            memset( pSim+nWords, 0xFF, sizeof(word)*nWords );
        }
        else if ( i == 1 )
        {
            memset( pSim,        0xFF, sizeof(word)*nWords );
            memset( pSim+nWords, 0x00, sizeof(word)*nWords );
        }
        else
        {
            memmove( pSim,        Vec_WrdEntryP(vOn,  (i-2)*nWords), sizeof(word)*nWords );
            memmove( pSim+nWords, Vec_WrdEntryP(vOff, (i-2)*nWords), sizeof(word)*nWords );
        }
    }
    Gia_ManResubPerform( p, vDivs, nWords*2, 100, 0, 50, 1, 1, 0, 0 );
    Gia_ManResubPrint( p->vGates, Vec_PtrSize(vDivs) );
    printf( "\n" );
    //Vec_PtrFree( vDivs );
    Gia_ResbFree( p );
}

/**Function*************************************************************

  Synopsis    [Top level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCheckResub( Vec_Ptr_t * vDivs, int nWords )
{
    //int i, nVars = 6, pVarSet[10] = { 2, 189, 2127, 2125, 177, 178 };
    int i, nVars = 3, pVarSet[10] = { 2, 3, 4 };
    word * pOff = (word *)Vec_PtrEntry( vDivs, 0 );
    word * pOn  = (word *)Vec_PtrEntry( vDivs, 1 );
    Vec_Int_t * vValue = Vec_IntStartFull( 1 << 6 );
    printf( "Verifying resub:\n" );
    for ( i = 0; i < 64*nWords; i++ )
    {
        int v, Mint = 0, Value = Abc_TtGetBit(pOn, i);
        if ( !Abc_TtGetBit(pOff, i) && !Value )
            continue;
        for ( v = 0; v < nVars; v++ )
            if ( Abc_TtGetBit((word *)Vec_PtrEntry(vDivs, pVarSet[v]), i) )
                Mint |= 1 << v;
        if ( Vec_IntEntry(vValue, Mint) == -1 )
            Vec_IntWriteEntry(vValue, Mint, Value);
        else if ( Vec_IntEntry(vValue, Mint) != Value )
            printf( "Mismatch in pattern %d\n", i );
    }
    printf( "Finished verifying resub.\n" );
    Vec_IntFree( vValue );
}
Vec_Ptr_t * Gia_ManDeriveDivs( Vec_Wrd_t * vSims, int nWords )
{
    int i, nDivs = Vec_WrdSize(vSims)/nWords;
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( nDivs );
    for ( i = 0; i < nDivs; i++ )
        Vec_PtrPush( vDivs, Vec_WrdEntryP(vSims, nWords*i) );
    return vDivs;
}
Gia_Man_t * Gia_ManResub2( Gia_Man_t * pGia, int nNodes, int nSupp, int nDivs, int iChoice, int fUseXor, int fVerbose, int fVeryVerbose )
{
    return NULL;
}
Gia_Man_t * Gia_ManResub1( char * pFileName, int nNodes, int nSupp, int nDivs, int iChoice, int fUseXor, int fVerbose, int fVeryVerbose )
{
    int nWords = 0;
    Gia_Man_t * pMan   = NULL;
    Vec_Wrd_t * vSims  = Vec_WrdReadHex( pFileName, &nWords, 1 );
    Vec_Ptr_t * vDivs  = vSims ? Gia_ManDeriveDivs( vSims, nWords ) : NULL;
    Gia_ResbMan_t * p = Gia_ResbAlloc( nWords );
    //Gia_ManCheckResub( vDivs, nWords );
    if ( Vec_PtrSize(vDivs) >= (1<<14) )
    {
        printf( "Reducing all divs from %d to %d.\n", Vec_PtrSize(vDivs), (1<<14)-1 );
        Vec_PtrShrink( vDivs, (1<<14)-1 );
    }
    assert( Vec_PtrSize(vDivs) < (1<<14) );
    Gia_ManResubPerform( p, vDivs, nWords, 100, 50, iChoice, fUseXor, 1, 1, 0 );
    if ( Vec_IntSize(p->vGates) )
    {
        Vec_Wec_t * vGates = Vec_WecStart(1);
        Vec_IntAppend( Vec_WecEntry(vGates, 0), p->vGates );
        pMan = Gia_ManConstructFromGates( vGates, Vec_PtrSize(vDivs) );
        Vec_WecFree( vGates );
    }
    else
        printf( "Decomposition did not succeed.\n" );
    Gia_ResbFree( p );
    Vec_PtrFree( vDivs );
    Vec_WrdFree( vSims );
    return pMan;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManUnivTfo_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vNodes, Vec_Int_t * vPos )
{
    int i, iFan, Count = 1;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return 0;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    if ( vNodes && Gia_ObjIsCo(Gia_ManObj(p, iObj)) )
        Vec_IntPush( vNodes, iObj );    
    if ( vPos && Gia_ObjIsCo(Gia_ManObj(p, iObj)) )
        Vec_IntPush( vPos, iObj );
    Gia_ObjForEachFanoutStaticId( p, iObj, iFan, i )
        Count += Gia_ManUnivTfo_rec( p, iFan, vNodes, vPos );
    return Count;
}
int Gia_ManUnivTfo( Gia_Man_t * p, int * pObjs, int nObjs, Vec_Int_t ** pvNodes, Vec_Int_t ** pvPos )
{
    int i, Count = 0;
    if ( pvNodes )
    {
        if ( *pvNodes )
            Vec_IntClear( *pvNodes );
        else
            *pvNodes = Vec_IntAlloc( 100 );
    }
    if ( pvPos )
    {
        if ( *pvPos )
            Vec_IntClear( *pvPos );
        else
            *pvPos = Vec_IntAlloc( 100 );
    }
    Gia_ManIncrementTravId( p );
    for ( i = 0; i < nObjs; i++ )
        Count += Gia_ManUnivTfo_rec( p, pObjs[i], pvNodes ? *pvNodes : NULL, pvPos ? *pvPos : NULL );
    if ( pvNodes )
        Vec_IntSort( *pvNodes, 0 );
    if ( pvPos )
        Vec_IntSort( *pvPos, 0 );
    return Count;
}

/**Function*************************************************************

  Synopsis    [Tuning resub.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManTryResub( Gia_Man_t * p )
{
    int nLimit   =  20;
    int nDivsMax = 200;
    int iChoice  =   0;
    int fUseXor  =   1;
    int fDebug   =   1;
    int fVerbose =   0;
    abctime clk, clkResub = 0, clkStart = Abc_Clock();
    Vec_Ptr_t * vvSims = Vec_PtrAlloc( 100 );
    Vec_Wrd_t * vSims;
    word * pSets[2], * pFunc;
    Gia_Obj_t * pObj, * pObj2; 
    int i, i2, nWords, nNonDec = 0, nTotal = 0;
    assert( Gia_ManCiNum(p) < 16 );
    Vec_WrdFreeP( &p->vSimsPi );
    p->vSimsPi = Vec_WrdStartTruthTables( Gia_ManCiNum(p) );
    nWords = Vec_WrdSize(p->vSimsPi) / Gia_ManCiNum(p);
    //Vec_WrdPrintHex( p->vSimsPi, nWords );
    pSets[0] = ABC_CALLOC( word, nWords );
    pSets[1] = ABC_CALLOC( word, nWords );
    vSims = Gia_ManSimPatSim( p );
    Gia_ManLevelNum(p);
    Gia_ManCreateRefs(p);
    Abc_ResubPrepareManager( nWords );
    Gia_ManStaticFanoutStart( p );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Vec_Int_t vGates;
        int * pArray, nArray, nTfo, iObj = Gia_ObjId(p, pObj);
        int Level = Gia_ObjLevel(p, pObj);
        int nMffc = Gia_NodeMffcSizeMark(p, pObj);
        pFunc = Vec_WrdEntryP( vSims, nWords*iObj );
        Abc_TtCopy( pSets[0], pFunc, nWords, 1 );
        Abc_TtCopy( pSets[1], pFunc, nWords, 0 );
        Vec_PtrClear( vvSims );
        Vec_PtrPushTwo( vvSims, pSets[0], pSets[1] );
        nTfo = Gia_ManUnivTfo( p, &iObj, 1, NULL, NULL );
        Gia_ManForEachCi( p, pObj2, i2 )
            Vec_PtrPush( vvSims, Vec_WrdEntryP(vSims, nWords*Gia_ObjId(p, pObj2)) );
        Gia_ManForEachAnd( p, pObj2, i2 )
            if ( !Gia_ObjIsTravIdCurrent(p, pObj2) && !Gia_ObjIsTravIdPrevious(p, pObj2) && Gia_ObjLevel(p, pObj2) <= Level )
                Vec_PtrPush( vvSims, Vec_WrdEntryP(vSims, nWords*Gia_ObjId(p, pObj2)) );
        if ( fVerbose )
        printf( "%3d : Lev = %2d  Mffc = %2d  Divs = %3d  Tfo = %3d\n", iObj, Level, nMffc, Vec_PtrSize(vvSims)-2, nTfo );
        clk = Abc_Clock();
        nArray = Abc_ResubComputeFunction( (void **)Vec_PtrArray(vvSims), Vec_PtrSize(vvSims), nWords, Abc_MinInt(nMffc-1, nLimit), nDivsMax, iChoice, fUseXor, fDebug, fVerbose, &pArray );
        clkResub += Abc_Clock() - clk;
        vGates.nSize = vGates.nCap = nArray;
        vGates.pArray = pArray;
        assert( nMffc > Vec_IntSize(&vGates)/2 );
        if ( Vec_IntSize(&vGates) > 0 )
            nTotal += nMffc - Vec_IntSize(&vGates)/2;
        nNonDec += Vec_IntSize(&vGates) == 0;
    }
    printf( "Total nodes = %5d.  Non-realizable = %5d.  Gain = %6d.  ", Gia_ManAndNum(p), nNonDec, nTotal );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clkStart );
    Abc_PrintTime( 1, "Pure resub time", clkResub );
    Abc_ResubPrepareManager( 0 );
    Gia_ManStaticFanoutStop( p );
    Vec_PtrFree( vvSims );
    Vec_WrdFree( vSims );
    ABC_FREE( pSets[0] );
    ABC_FREE( pSets[1] );
}


/**Function*************************************************************

  Synopsis    [Deriving a subset.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManDeriveShrink( Vec_Wrd_t * vFuncs, int nWords )
{
    int i, k = 0, nFuncs = Vec_WrdSize(vFuncs) / nWords / 2;
    assert( 2 * nFuncs * nWords == Vec_WrdSize(vFuncs) );
    for ( i = 0; i < nFuncs; i++ )
    {
        word * pFunc0 = Vec_WrdEntryP(vFuncs, (2*i+0)*nWords);
        word * pFunc1 = Vec_WrdEntryP(vFuncs, (2*i+1)*nWords);
        if ( Abc_TtIsConst0(pFunc0, nWords) || Abc_TtIsConst0(pFunc1, nWords) )
            continue;
        if ( k < i ) Abc_TtCopy( Vec_WrdEntryP(vFuncs, (2*k+0)*nWords), pFunc0, nWords, 0 );
        if ( k < i ) Abc_TtCopy( Vec_WrdEntryP(vFuncs, (2*k+1)*nWords), pFunc1, nWords, 0 );
        k++;
    }
    Vec_WrdShrink( vFuncs, 2*k*nWords );
    return k;
}
void Gia_ManDeriveCounts( Vec_Wrd_t * vFuncs, int nWords, Vec_Int_t * vCounts )
{
    int i, nFuncs = Vec_WrdSize(vFuncs) / nWords / 2;
    assert( 2 * nFuncs * nWords == Vec_WrdSize(vFuncs) );
    Vec_IntClear( vCounts );
    for ( i = 0; i < 2*nFuncs; i++ )
        Vec_IntPush( vCounts, Abc_TtCountOnesVec(Vec_WrdEntryP(vFuncs, i*nWords), nWords) );
}
int Gia_ManDeriveCost( Vec_Wrd_t * vFuncs, int nWords, word * pMask, Vec_Int_t * vCounts )
{
    int i, Res = 0, nFuncs = Vec_WrdSize(vFuncs) / nWords / 2;
    assert( 2 * nFuncs * nWords == Vec_WrdSize(vFuncs) );
    assert( Vec_IntSize(vCounts) * nWords == Vec_WrdSize(vFuncs) );
    for ( i = 0; i < nFuncs; i++ )
    {
        int Total[2] = { Vec_IntEntry(vCounts, 2*i+0), Vec_IntEntry(vCounts, 2*i+1) };
        int This[2]  = { Abc_TtCountOnesVecMask(Vec_WrdEntryP(vFuncs, (2*i+0)*nWords), pMask, nWords, 0),
                         Abc_TtCountOnesVecMask(Vec_WrdEntryP(vFuncs, (2*i+1)*nWords), pMask, nWords, 0) };
        assert( Total[0] >= This[0] && Total[1] >= This[1] );
        Res += This[0] * This[1] + (Total[0] - This[0]) * (Total[1] - This[1]);
    }
    return Res;
}
int Gia_ManDeriveSimpleCost( Vec_Int_t * vCounts )
{
    int i, Ent1, Ent2, Res = 0;
    Vec_IntForEachEntryDouble( vCounts, Ent1, Ent2, i )
        Res += Ent1*Ent2;
    return Res;
}
void Gia_ManDeriveNext( Vec_Wrd_t * vFuncs, int nWords, word * pMask )
{
    int i, iStop = Vec_WrdSize(vFuncs); word Data;
    int nFuncs = Vec_WrdSize(vFuncs) / nWords / 2;
    assert( 2 * nFuncs * nWords == Vec_WrdSize(vFuncs) );
    Vec_WrdForEachEntryStop( vFuncs, Data, i, iStop )
        Vec_WrdPush( vFuncs, Data );
    for ( i = 0; i < nFuncs; i++ )
    {
        word * pFunc0n = Vec_WrdEntryP(vFuncs, (2*i+0)*nWords);
        word * pFunc1n = Vec_WrdEntryP(vFuncs, (2*i+1)*nWords);
        word * pFunc0p = Vec_WrdEntryP(vFuncs, (2*i+0)*nWords + iStop);
        word * pFunc1p = Vec_WrdEntryP(vFuncs, (2*i+1)*nWords + iStop);
        Abc_TtAnd( pFunc0p, pFunc0n, pMask, nWords, 0 );
        Abc_TtAnd( pFunc1p, pFunc1n, pMask, nWords, 0 );
        Abc_TtSharp( pFunc0n, pFunc0n, pMask, nWords );
        Abc_TtSharp( pFunc1n, pFunc1n, pMask, nWords );
    }
}
Vec_Int_t * Gia_ManDeriveSubset( Gia_Man_t * p, Vec_Wrd_t * vFuncs, Vec_Int_t * vObjs, Vec_Wrd_t * vSims, int nWords, int fVerbose )
{
    int i, k, iObj, CostBestPrev, nFuncs = Vec_WrdSize(vFuncs) / nWords;
    Vec_Int_t * vRes    = Vec_IntAlloc( 100 );
    Vec_Int_t * vCounts = Vec_IntAlloc( nFuncs * 2 );
    Vec_Wrd_t * vFSims  = Vec_WrdDup( vFuncs );
    assert( nFuncs * nWords == Vec_WrdSize(vFuncs) );
    assert( Gia_ManObjNum(p) * nWords == Vec_WrdSize(vSims) );
    assert( Vec_IntSize(vObjs) <= Gia_ManCandNum(p) );
    nFuncs = Gia_ManDeriveShrink( vFSims, nWords );
    Gia_ManDeriveCounts( vFSims, nWords, vCounts );
    assert( Vec_IntSize(vCounts) * nWords == Vec_WrdSize(vFSims) );
    CostBestPrev = Gia_ManDeriveSimpleCost( vCounts );
    if ( fVerbose )
    printf( "Processing %d functions and %d objects with cost %d\n", nFuncs, Vec_IntSize(vObjs), CostBestPrev );
    for ( i = 0; nFuncs > 0; i++ )
    {
        int iObjBest = -1, CountThis, Count0 = ABC_INFINITY, CountBest = ABC_INFINITY;
        Vec_IntForEachEntry( vObjs, iObj, k )
        {
            if ( Vec_IntFind(vRes, iObj) >= 0 )
                continue;
            CountThis = Gia_ManDeriveCost( vFSims, nWords, Vec_WrdEntryP(vSims, iObj*nWords), vCounts );
            if ( CountBest > CountThis )
            {
                CountBest = CountThis;
                iObjBest = iObj;
            }
            if ( !k ) Count0 = CountThis;
        }
        if ( Count0 < CostBestPrev )
        {
            CountBest = Count0;
            iObjBest = Vec_IntEntry(vObjs, 0);
        }
        Gia_ManDeriveNext( vFSims, nWords, Vec_WrdEntryP(vSims, iObjBest*nWords) );
        nFuncs = Gia_ManDeriveShrink( vFSims, nWords );
        Gia_ManDeriveCounts( vFSims, nWords, vCounts );
        assert( CountBest == Gia_ManDeriveSimpleCost(vCounts) );
        Vec_IntPush( vRes, iObjBest );
        CostBestPrev = CountBest;
        if ( fVerbose )
        printf( "Iter %2d :  Funcs = %6d.  Object %6d.  Cost %6d.\n", i, nFuncs, iObjBest, CountBest );
    }
    Vec_IntFree( vCounts );
    Vec_WrdFree( vFSims );
    return vRes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManResubFindUsed( Vec_Int_t * vRes, int nDivs, int nNodes, Vec_Int_t * vSupp )
{
    int i, k, iLit, Counter = 1;
    Vec_Int_t * vUsed = Vec_IntStartFull( nDivs );
    Vec_Int_t * vRes2 = Vec_IntDup( vRes );
    Vec_IntWriteEntry( vUsed, 0, 0 );
    assert( Vec_IntSize(vRes) % 2 == 1 );
    Vec_IntSort( vRes2, 0 );
    Vec_IntForEachEntry( vRes2, iLit, k )
    {
        int iVar = Abc_Lit2Var(iLit);
        if ( iVar > 0 && iVar < nDivs && Vec_IntEntry(vUsed, iVar) == -1 ) {
            Vec_IntWriteEntry( vUsed, iVar, Counter++ );
            Vec_IntPush( vSupp, iVar-2 );
        }
    }
    Vec_IntFree( vRes2 );
    for ( i = nDivs; i < nDivs + nNodes; i++ )
        Vec_IntPush( vUsed, Counter++ );
    return vUsed;
}
Vec_Int_t * Gia_ManResubRemapSolution( Vec_Int_t * vRes, Vec_Int_t * vUsed )
{
    int i, iLit;
    Vec_Int_t * vResNew = Vec_IntAlloc( Vec_IntSize(vRes) );
    Vec_IntForEachEntry( vRes, iLit, i )
        Vec_IntPush( vResNew, Abc_Lit2LitV(Vec_IntArray(vUsed), iLit) );
    return vResNew;
}
void Gia_ManResubRecordSolution( char * pFileName, Vec_Int_t * vRes, int nDivs )
{
    FILE * pFile = fopen( pFileName, "ab" );
    if ( pFile == NULL ) {
        printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        return;
    }
    Vec_Int_t * vSupp = Vec_IntAlloc( 100 );
    Vec_Int_t * vUsed = Gia_ManResubFindUsed( vRes, nDivs, Vec_IntSize(vRes)/2, vSupp );
    Vec_Int_t * vResN = Gia_ManResubRemapSolution( vRes, vUsed );

    int i, Temp;
    fprintf( pFile, "\n.s" );
    Vec_IntForEachEntry( vSupp, Temp, i )
        fprintf( pFile, " %d", Temp );
    fprintf( pFile, "\n.a" );
    Vec_IntForEachEntry( vResN, Temp, i )
        fprintf( pFile, " %d", Temp );
    fprintf( pFile, "\n" );
    fclose( pFile );

    Vec_IntFree( vUsed );
    Vec_IntFree( vSupp );
    Vec_IntFree( vResN );
}
Gia_Man_t * Gia_ManResubUnateOne( char * pFileName, int nLimit, int nDivMax, int fWriteSol, int fVerbose )
{
    Gia_Man_t * pNew = NULL;
    Abc_RData_t * p = Abc_ReadPla( pFileName ); 
    if ( p == NULL ) return NULL;
    assert( p->nOuts == 1 );
    Vec_Ptr_t * vDivs = Vec_PtrAlloc( 2+p->nIns );
    Vec_Int_t * vRes = Vec_IntAlloc( 100 );
    Vec_PtrPush( vDivs, Vec_WrdEntryP(p->vSimsOut, 0*p->nSimWords) );
    Vec_PtrPush( vDivs, Vec_WrdEntryP(p->vSimsOut, 1*p->nSimWords) );
    int i, k, ArraySize, * pArray; 
    for ( i = 0; i < p->nIns; i++ )
        Vec_PtrPush( vDivs, Vec_WrdEntryP(p->vSimsIn, i*p->nSimWords) );
    Abc_ResubPrepareManager( p->nSimWords );
    if ( fVerbose )
        printf( "The problem has %d divisors and %d outputs.\n", p->nIns, p->nOuts );
    ArraySize = Abc_ResubComputeFunction( (void **)Vec_PtrArray(vDivs), Vec_PtrSize(vDivs), p->nSimWords, nLimit, nDivMax, 0, 0, 1, fVerbose, &pArray );
    for ( k = 0; k < ArraySize; k++ )
        Vec_IntPush( vRes, pArray[k] );
    if ( ArraySize ) {
        //Vec_IntPrint( vRes );
        Vec_Wec_t * vGates = Vec_WecStart(1);
        Vec_IntAppend( Vec_WecEntry(vGates, 0), vRes );
        pNew = Gia_ManConstructFromGates( vGates, Vec_PtrSize(vDivs) );
        Vec_WecFree( vGates );
        if ( fVerbose )
            printf( "The solution has %d inputs and %d nodes.\n", Gia_ManCiNum(pNew), Gia_ManAndNum(pNew) );
    }
    if ( fWriteSol && ArraySize )
        Gia_ManResubRecordSolution( pFileName, vRes, Vec_PtrSize(vDivs) );
    Abc_ResubPrepareManager( 0 );
    Vec_IntFree( vRes );   
    Vec_PtrFree( vDivs );
    Abc_RDataStop( p );  
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
