// TFI/TFO divisor collection and ranking.
// Private implementation fragment included only by cecTrans.c.

// This mask is only a divisor-routing heuristic, not an MFFC computation.
// Following the initial ref==1 tree reaches the external boundary without
// excluding reconvergent internal nodes that are legal replacement supports.
// Candidate gain and selection always use the exact deref/ref MFFC above.
static void Cec_TranMarkDivExclusion_rec( Gia_Man_t * p, int iObj, int iRoot,
    char const * pCovered, char const * pUsed,
    char * pMark, Vec_Int_t * vMarked )
{
    Gia_Obj_t * pObj;
    int iFan;
    if ( Cec_TranMffcIsBoundary(iObj, iRoot, pCovered, pUsed, NULL) ||
         pMark[iObj] )
        return;
    pMark[iObj] = 1;
    Vec_IntPush( vMarked, iObj );
    pObj = Gia_ManObj( p, iObj );
    if ( !Gia_ObjIsAnd(pObj) )
        return;
    iFan = Gia_ObjFaninId0p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkDivExclusion_rec( p, iFan, iRoot, pCovered, pUsed,
            pMark, vMarked );
    iFan = Gia_ObjFaninId1p( p, pObj );
    if ( Gia_ObjIsAnd(Gia_ManObj(p, iFan)) &&
         Gia_ObjRefNumId(p, iFan) == 1 )
        Cec_TranMarkDivExclusion_rec( p, iFan, iRoot, pCovered, pUsed,
            pMark, vMarked );
}

static int Cec_TranCandDynamicGainWithRefs( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, int * pRefs, char * pMffc, Vec_Int_t * vMffc,
    Vec_Int_t * vSupport )
{
    int i, iObj;
    if ( (pCovered && pCovered[pCand->iTarget]) ||
         (pUsed && pUsed[pCand->iTarget]) )
        return -1;
    Cec_TranCandCollectSupport( pCand, vSupport );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pCovered && pCovered[iObj] )
            return -1;
    // The current recipe creates references to its support too.  Treat that
    // support as a boundary while computing this candidate's kill-set; this
    // is what makes an earlier equivalent inside the static MFFC legal.
    if ( pRefs )
        Cec_TranMarkDynamicMffcWithRefs( p, pCand->iTarget, pCovered,
            pUsed, vSupport, pRefs, pMffc, vMffc );
    else
        Cec_TranMarkDynamicMffc( p, pCand->iTarget, pCovered, pUsed,
            vSupport, pMffc, vMffc );
    Vec_IntForEachEntry( vSupport, iObj, i )
        if ( pMffc[iObj] )
            return -1;
    return Vec_IntSize(vMffc) - pCand->nGates;
}

static int Cec_TranCandDynamicGain( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    Vec_Int_t * vSupport )
{
    return Cec_TranCandDynamicGainWithRefs( p, pCand, pCovered, pUsed,
        NULL, pMffc, vMffc, vSupport );
}

static int Cec_TranCandFrozenGainWithRefs( Gia_Man_t * p,
    Cec_TranFrozenHash_t const * pHash, Cec_TranCand_t const * pCand,
    char const * pCovered, char const * pUsed, int * pRefs,
    char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vBoundary )
{
    int i, iObj, nNew;
    if ( (pCovered && pCovered[pCand->iTarget]) ||
         (pUsed && pUsed[pCand->iTarget]) )
        return -1;
    Cec_TranCandCollectSupport( pCand, vBoundary );
    Vec_IntForEachEntry( vBoundary, iObj, i )
        if ( pCovered && pCovered[iObj] )
            return -1;
    nNew = Cec_TranFrozenRecipeCost( p, pHash, pCand,
        pCovered, vBoundary );
    Cec_TranMarkDynamicMffcWithRefs( p, pCand->iTarget,
        pCovered, pUsed, vBoundary, pRefs, pMffc, vMffc );
    // A target used as its own replacement is the only boundary which the
    // MFFC traversal deliberately cannot cut.  Reject it as a cycle.
    Vec_IntForEachEntry( vBoundary, iObj, i )
        if ( pMffc[iObj] )
            return -1;
    return Vec_IntSize(vMffc) - nNew;
}

// Isolated scratch for the optional frozen-graph discovery gate.  This prices
// existing hash nodes and protected support; it gives no proof/commit right.
typedef struct Cec_TranQualityCost_t_
{
    Cec_TranFrozenHash_t Hash;
    int * pRefs;
    char * pMffc;
    Vec_Int_t * vMffc, * vBoundary;
} Cec_TranQualityCost_t;

static void Cec_TranQualityCostStart( Gia_Man_t * p,
    char const * pCovered, Cec_TranQualityCost_t * pCost )
{
    memset( pCost, 0, sizeof(*pCost) );
    Cec_TranFrozenHashStart( p, &pCost->Hash );
    pCost->pRefs = Cec_TranMffcRefsStart( p, pCovered );
    pCost->pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    pCost->vMffc = Vec_IntAlloc( 64 );
    pCost->vBoundary = Vec_IntAlloc( 32 );
}

static int Cec_TranQualityCostGain( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, Cec_TranQualityCost_t * pCost )
{
    return Cec_TranCandFrozenGainWithRefs( p, &pCost->Hash, pCand,
        pCovered, pUsed, pCost->pRefs, pCost->pMffc,
        pCost->vMffc, pCost->vBoundary );
}

static void Cec_TranQualityCostStop( Cec_TranQualityCost_t * pCost )
{
    Cec_TranFrozenHashStop( &pCost->Hash );
    ABC_FREE( pCost->pRefs );
    ABC_FREE( pCost->pMffc );
    Vec_IntFreeP( &pCost->vMffc );
    Vec_IntFreeP( &pCost->vBoundary );
}

static int Cec_TranQualityCostGainOne( Gia_Man_t * p,
    Cec_TranCand_t const * pCand, char const * pCovered,
    char const * pUsed, int * pnMffc )
{
    Cec_TranQualityCost_t Cost;
    int Gain;
    Cec_TranQualityCostStart( p, pCovered, &Cost );
    Gain = Cec_TranQualityCostGain( p, pCand, pCovered, pUsed, &Cost );
    if ( pnMffc ) *pnMffc = Vec_IntSize(Cost.vMffc);
    Cec_TranQualityCostStop( &Cost );
    return Gain;
}

// Collect physical divisor nodes by increasing TFI distance.  The routing mask
// skips only the initial exclusive tree; reconvergent nodes deeper inside the
// exact MFFC remain legal because replacement support keeps them alive.  Exact
// dynamic gain later recomputes the kill-set with that support as a boundary.
// PI and RO objects are legal CIs, and all retained nodes precede the target.
static Vec_Int_t * Cec_TranCollectDivPoolDomainCut( Gia_Man_t * p, int iTarget,
    int nDepthMax, int nNodesMax, int fUseMffcDivs, char const * pCovered,
    char const * pUsed, char * pMffc, Vec_Int_t * vMffc,
    int fUseTfoDivs, int nTfoMax, Vec_Int_t * vTfo,
    Cec_TranTfoStats_t * pTfoStats, int fGlobalEarlier, int fNoRouting,
    int nCutLeaves, int fCutTrace, int fMeasure, Cec_TranCutCache_t * pCutCache )
{
    Vec_Int_t * vPool = Vec_IntAlloc( nNodesMax ? nNodesMax : 64 );
    Vec_Int_t * vFront = Vec_IntAlloc( 32 );
    Vec_Int_t * vNext = Vec_IntAlloc( 32 );
    Vec_Int_t * vSeeds = fUseTfoDivs ? Vec_IntAlloc( 64 ) : NULL;
    Vec_Int_t * vLeaves = NULL;
    Gia_Obj_t * pObj, * pFan;
    int d, i, k, iObj, iFan, fFull = 0;
    abctime clkTfo = 0, clkPart = 0;
    assert( !fUseTfoDivs || (p->vFanoutNums && p->vFanout && vTfo) );
    if ( vTfo )
        Vec_IntClear( vTfo );
    if ( pTfoStats )
        memset( pTfoStats, 0, sizeof(*pTfoStats) );
    if ( nCutLeaves )
    {
        // ODC retains its existing depth cap in addition to the cut boundary.
        assert(!fGlobalEarlier);
        clkPart = fMeasure ? Abc_Clock() : 0;
        assert(!pCutCache || (pCutCache->pGia == p && pCutCache->Size == nCutLeaves));
        vLeaves = pCutCache ? Cec_TranCutCacheSelect(pCutCache,iTarget,fMeasure ? pTfoStats : NULL) :
            Cec_TranCutLeaves(p,iTarget,nCutLeaves,fMeasure ? pTfoStats : NULL);
        if ( fMeasure && pTfoStats ) pTfoStats->timeCut = Abc_Clock() - clkPart;
        if ( fCutTrace )
        {
            Abc_Print(1,"sresub cut leaves: root=%d leaves=",iTarget);
            Vec_IntForEachEntry(vLeaves,iObj,i) Abc_Print(1,"%s%d",i ? "," : "",iObj);
            Abc_Print(1,"\n");
        }
    }
    clkPart = fMeasure ? Abc_Clock() : 0;
    Cec_TranMffcScratchClear( pMffc, vMffc );
    if ( fNoRouting )
    {
        pMffc[iTarget] = 1;
        Vec_IntPush( vMffc, iTarget );
    }
    else if ( fUseMffcDivs )
        Cec_TranMarkDivExclusion_rec( p, iTarget, iTarget, pCovered, pUsed,
            pMffc, vMffc );
    else
        Cec_TranMarkDynamicMffc( p, iTarget, pCovered, pUsed, NULL,
            pMffc, vMffc );
    // The BFS used to allocate and clear one |G|-byte pSeen array per root.
    // Traversal IDs provide the same membership test with O(visited TFI)
    // writes and no per-root full-graph zeroing.
    Gia_ManIncrementTravId( p );
    Gia_ObjSetTravIdCurrentId( p, iTarget );
    Vec_IntPush( vFront, iTarget );
    for ( d = 1; Vec_IntSize(vFront) && (!nDepthMax || d <= nDepthMax); d++ )
    {
        Vec_IntClear( vNext );
        Vec_IntForEachEntry( vFront, iObj, i )
        {
            pObj = Gia_ManObj( p, iObj );
            if ( fMeasure && pTfoStats ) pTfoStats->nTfiNodes++;
            if ( vLeaves && Vec_IntFind(vLeaves,iObj) >= 0 ) continue;
            if ( !Gia_ObjIsAnd(pObj) )
                continue;
            for ( k = 0; k < 2; k++ )
            {
                if ( fMeasure && pTfoStats ) pTfoStats->nTfiEdges++;
                iFan = k ? Gia_ObjFaninId1p(p, pObj) :
                           Gia_ObjFaninId0p(p, pObj);
                if ( Gia_ObjIsTravIdCurrentId(p, iFan) )
                    continue;
                Gia_ObjSetTravIdCurrentId( p, iFan );
                if ( vSeeds )
                    Vec_IntPush( vSeeds, iFan );
                pFan = Gia_ManObj( p, iFan );
                if ( iFan != 0 && iFan < iTarget && Gia_ObjIsCand(pFan) &&
                     !pMffc[iFan] && !fFull )
                {
                    Vec_IntPush( vPool, iFan );
                    fFull = nNodesMax && Vec_IntSize(vPool) >= nNodesMax;
                }
                if ( Gia_ObjIsAnd(pFan) )
                    Vec_IntPush( vNext, iFan );
            }
        }
        // The ranked divisor reservoir and the structural TFI membership have
        // different purposes.  Once the reservoir is full, TFI-only mode can
        // stop as before.  Complete-fanin TFO mode must keep walking to the
        // requested depth so a fanout is not rejected merely because one of
        // its fanins appeared after the reservoir budget was exhausted.
        if ( fFull && !fUseTfoDivs )
            break;
        ABC_SWAP( Vec_Int_t, *vFront, *vNext );
    }
    if ( pTfoStats )
        pTfoStats->nTfi = Vec_IntSize(vPool);
    if ( fMeasure && pTfoStats ) pTfoStats->timeTfi = Abc_Clock() - clkPart;
    // Expand only through fanouts whose two physical AIG fanins are already
    // members of the root-local structural window.  The target and every true
    // target fanout are topologically later and are excluded by iFan<iTarget.
    // Additions never become membership witnesses: this is exactly the
    // one-hop shell requested by the complete-fanin rule, not a recursive
    // forward closure.  Legal-candidate filtering stays separate from
    // structural membership: MFFC nodes may justify completeness without
    // themselves entering the divisor reservoir.
    if ( fUseTfoDivs )
    {
        int nSeedSize = Vec_IntSize( vSeeds );
        int nTfoLimit = Abc_ResubQualityNoTruncation() ? 0 :
            (nTfoMax ? nTfoMax : (nNodesMax ? nNodesMax : 256));
        clkTfo = Abc_Clock();
        for ( i = 0; i < nSeedSize; i++ )
        {
            int f;
            iObj = Vec_IntEntry( vSeeds, i );
            if ( pTfoStats )
                pTfoStats->nScanned++;
            Gia_ObjForEachFanoutStaticId( p, iObj, iFan, f )
            {
                int iFan0, iFan1;
                if ( pTfoStats )
                    pTfoStats->nEdges++;
                if ( iFan >= iTarget ||
                     !Gia_ObjIsAndNotBuf(Gia_ManObj(p, iFan)) ||
                     Gia_ObjIsTravIdCurrentId(p, iFan) )
                    continue;
                pFan = Gia_ManObj( p, iFan );
                iFan0 = Gia_ObjFaninId0p( p, pFan );
                iFan1 = Gia_ObjFaninId1p( p, pFan );
                if ( !Gia_ObjIsTravIdCurrentId(p, iFan0) ||
                     !Gia_ObjIsTravIdCurrentId(p, iFan1) )
                    continue;
                // Additions are deliberately not marked, so suppress the
                // second encounter through the other fanin explicitly.
                if ( Vec_IntFind(vTfo, iFan) >= 0 )
                    continue;
                Vec_IntPush( vTfo, iFan );
                if ( pTfoStats )
                    pTfoStats->nAdded++;
                if ( nTfoLimit && Vec_IntSize(vTfo) >= nTfoLimit )
                {
                    if ( pTfoStats )
                        pTfoStats->fLimit = 1;
                    break;
                }
            }
            if ( nTfoLimit && Vec_IntSize(vTfo) >= nTfoLimit )
                break;
        }
        Vec_IntAppend( vPool, vTfo );
        if ( pTfoStats )
        {
            pTfoStats->nSeeds = nSeedSize;
            pTfoStats->Time = Abc_Clock() - clkTfo;
        }
    }
    // Route3's retained quality domain includes every legal earlier node.
    // Topological order prevents cycles; support-aware exact gain and proof
    // remain mandatory.  Do not propagate this domain into COM or ODC.
    if ( fGlobalEarlier )
    {
        Gia_ManIncrementTravId( p );
        Vec_IntForEachEntry( vPool, iObj, i )
            Gia_ObjSetTravIdCurrentId( p, iObj );
        for ( iObj = 1; iObj < iTarget; iObj++ )
            if ( Gia_ObjIsCand(Gia_ManObj(p, iObj)) &&
                 !pMffc[iObj] && !(pCovered && pCovered[iObj]) &&
                 !Gia_ObjIsTravIdCurrentId(p, iObj) )
            {
                Gia_ObjSetTravIdCurrentId( p, iObj );
                Vec_IntPush( vPool, iObj );
                if ( pTfoStats ) pTfoStats->nGlobal++;
            }
    }
    Vec_IntFreeP( &vSeeds );
    Vec_IntFreeP( &vLeaves );
    Vec_IntFree( vFront );
    Vec_IntFree( vNext );
    return vPool;
}

// Rank a physical divisor by the number of opposite-label simulation pairs
// it separates.  If O0/O1 and I0/I1 are the off/on-set counts in the two
// divisor cofactors, O0*I1 + O1*I0 is exactly the number of off/on pairs cut
// by this divisor.  The score is phase-independent and is therefore a cheap
// proxy for the reduction in the residual dependency ambiguity.
struct Cec_TranDivRank_t_
{
    word Score;
    int  CiOverlap;
    int  iPos;
};

// A paged iterator cursor is meaningful only for the exact ordered divisor
// set on which it was produced.  Freeze that set and its aligned rank metadata
// on page zero, then restore it verbatim before every continuation page.  This
// also keeps the root-batch teaching cache bound to the same object columns.
static void Cec_TranRootCursorBindBuildPool( Cec_TranRootCursor_t * pCursor,
    int iWave, Vec_Int_t * vPool, Cec_TranDivRank_t * pRanks )
{
    int i, nPool;
    if ( iWave == 0 )
    {
        assert( pCursor->vBuildPool == NULL );
        assert( pCursor->pBuildRanks == NULL );
        pCursor->vBuildPool = Vec_IntDup( vPool );
        nPool = Vec_IntSize( vPool );
        if ( nPool )
        {
            assert( pRanks != NULL );
            pCursor->pBuildRanks = ABC_ALLOC( Cec_TranDivRank_t, nPool );
            memcpy( pCursor->pBuildRanks, pRanks,
                sizeof(Cec_TranDivRank_t) * nPool );
        }
        return;
    }
    assert( pCursor->vBuildPool != NULL );
    nPool = Vec_IntSize( pCursor->vBuildPool );
    assert( nPool == 0 || (pRanks != NULL && pCursor->pBuildRanks != NULL) );
    Vec_IntClear( vPool );
    Vec_IntAppend( vPool, pCursor->vBuildPool );
    if ( nPool )
        memcpy( pRanks, pCursor->pBuildRanks,
            sizeof(Cec_TranDivRank_t) * nPool );
    for ( i = 0; i < nPool; i++ )
        assert( Vec_IntEntry(vPool, i) ==
                Vec_IntEntry(pCursor->vBuildPool, i) &&
                pRanks[i].iPos == i );
}

static void Cec_TranRootCursorStop( Cec_TranRootCursor_t * pCursor )
{
    Cec_TranSourceMacroStop(pCursor->pSourceMacro);
    pCursor->pSourceMacro = NULL;
    Cec_TranRootCursorCacheStop( pCursor );
    Cec_TranTeachCacheStop( pCursor->pTeachCache );
    pCursor->pTeachCache = NULL;
    Vec_IntFreeP( &pCursor->vBuildPool );
    ABC_FREE( pCursor->pBuildRanks );
    pCursor->pRankSource = NULL;
    pCursor->pRankSims = NULL;
}

static int Cec_TranDivRankCompare( const void * p1, const void * p2 )
{
    Cec_TranDivRank_t const * pR1 = (Cec_TranDivRank_t const *)p1;
    Cec_TranDivRank_t const * pR2 = (Cec_TranDivRank_t const *)p2;
    if ( pR1->Score > pR2->Score )
        return -1;
    if ( pR1->Score < pR2->Score )
        return 1;
    if ( pR1->CiOverlap != pR2->CiOverlap )
        return pR2->CiOverlap - pR1->CiOverlap;
    return pR1->iPos - pR2->iPos;
}

#include "cecTranRankThresholdSort.h"

// Local to one real rank call. Discarded nodes have no rank record: they are
// removed by stable compaction, never represented by a fabricated exact score.
// The unchanged collector's original size is retained by RootDiscoverOne.
typedef struct Cec_TranRankBound_t_
{
    Cec_TranRankThreshold_t Threshold;
    int fScope, Mode, Active, Profile, Trace, B, nHeap, OriginalPairs;
    int Root, Round, Wave, Scope, Slots;
    char const * pReason;
    Vec_Int_t * vTfo;  // borrowed legal rescue members, protected by object ID
    unsigned char * pProtected;
    word * pHeap, * pOracleScores;
    Vec_Int_t * vReference;
    Cec_TranDivRank_t * pReference;
    word N, RootOnes, BoundChecks, ScannedPairs, PrunedPairs, ProtectedPairs;
    word ActualWords, PrunedWords, HeapUpdates, HeapComparisons;
    word OracleWords, OracleChecks, OracleCiCalls, OracleRankChecks, OracleCoreChecks, OraclePoolChecks;
    word SetupWords, SetupPopcounts, ProtectedIndexBytes;
    abctime timeIndex, timeHeap, timeOracle, timeSetup;
    int Oracle, FinalMode, FinalProfile, FinalBefore, FinalAfter;
    int FinalSort1, FinalSort2, FinalCiItems;
    word FinalCutoff, FinalOracleChecks, FinalThresholdChecks, FinalCiHits, FinalCiMisses;
    abctime timeFinalFilter, timeFinalSort1, timeFinalSort2, timeFinalCi;
} Cec_TranRankBound_t;

static int Cec_TranRankBoundMode( void )
{
    static int Mode = -1;
    if ( Mode < 0 ) Mode = Cec_TranStrictCexOption("ABC_STRICT_RANK_BOUND", 0, 2);
    return Mode;
}

// The score is convex in intersection x, whose legal interval is determined
// by the two marginals. N <= UINT32_MAX keeps these nonnegative products and
// their sum in word; no signed or overflowing expanded polynomial is used.
static word Cec_TranRankBoundUpper( word N, word a, word b )
{
    word lo = a > N-b ? a-(N-b) : 0, hi = a < b ? a : b;
    word lOff1 = b-lo, hOff1 = b-hi;
    word l = (N-a-lOff1)*lo + lOff1*(a-lo);
    word h = (N-a-hOff1)*hi + hOff1*(a-hi);
    assert( a <= N && b <= N );
    return l > h ? l : h;
}

// Only genuinely evaluated scores enter this minheap. Its B-th threshold
// never decreases, and equal-score candidates are never pruned.
static void Cec_TranRankBoundHeap( Cec_TranRankBound_t * p, word Score )
{
    int i, j;
    abctime clk = 0;
    if ( p->nHeap == p->B )
    {
        ++p->HeapComparisons;
        if ( Score <= p->pHeap[0] ) return;
    }
    if ( p->Profile ) clk = Abc_Clock();
    ++p->HeapUpdates;
    if ( p->nHeap < p->B )
    {
        i = p->nHeap++;
        while ( i )
        {
            j = (i-1)/2;
            ++p->HeapComparisons;
            if ( p->pHeap[j] <= Score ) break;
            p->pHeap[i] = p->pHeap[j]; i = j;
        }
    }
    else
    {
        i = 0;
        while ( i < p->B/2 )
        {
            j = 2*i+1;
            if ( j+1 < p->B )
            {
                ++p->HeapComparisons;
                if ( p->pHeap[j+1] < p->pHeap[j] ) ++j;
            }
            ++p->HeapComparisons;
            if ( Score <= p->pHeap[j] ) break;
            p->pHeap[i] = p->pHeap[j]; i = j;
        }
    }
    p->pHeap[i] = Score;
    if ( p->Profile ) p->timeHeap += Abc_Clock()-clk;
}

// Diagnostic only: recompute every score using the complete original dense
// columns, then reproduce the original B-plus-ties CI scope without mutating
// the source CI cache or old profiling counters. Low-score TFOs retain CI=0.
static void Cec_TranRankBoundReference( Cec_TranRankBound_t * pBound,
    Cec_TranSim_t * pSim, int iTarget, Vec_Int_t * vReservoir )
{
    word * pRoot = Cec_TranSimObj(pSim, iTarget);
    word On = 0, Off = 0;
    int i, s, iObj, nKeep = pBound->B, n = Vec_IntSize(vReservoir);
    Vec_Int_t * vSupp = Vec_IntAlloc(32);
    abctime clk = Abc_Clock();
    pBound->vReference = Vec_IntDup(vReservoir);
    pBound->pReference = ABC_CALLOC(Cec_TranDivRank_t, n);
    pBound->pOracleScores = ABC_ALLOC(word, n);
    for ( s = 0; s < pSim->nSlots; ++s )
        On += Abc_TtCountOnes(pRoot[s]), Off += Abc_TtCountOnes(~pRoot[s]);
    assert( On == pBound->RootOnes && On+Off == pBound->N );
    Vec_IntForEachEntry(vReservoir, iObj, i)
    {
        word * pDiv = Cec_TranSimObj(pSim, iObj);
        word On1 = 0, Off1 = 0;
        for ( s = 0; s < pSim->nSlots; ++s )
        {
            On1 += Abc_TtCountOnes(pRoot[s] & pDiv[s]);
            Off1 += Abc_TtCountOnes(~pRoot[s] & pDiv[s]);
        }
        assert( On1+Off1 == pSim->pSigDot->pOnes[iObj] );
        pBound->pReference[i].Score = (Off-Off1)*On1 + Off1*(On-On1);
        pBound->pReference[i].iPos = i;
        pBound->pOracleScores[i] = pBound->pReference[i].Score;
    }
    pBound->OracleWords += ((word)n+1)*pSim->nSlots;
    qsort(pBound->pReference, n, sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare);
    while ( nKeep < n && pBound->pReference[nKeep].Score == pBound->pReference[nKeep-1].Score ) ++nKeep;
    for ( i = 0; i < nKeep; ++i )
    {
        iObj = Vec_IntEntry(vReservoir, pBound->pReference[i].iPos);
        Vec_IntClear(vSupp);
        Gia_ManCollectCis(pSim->pGia, &iObj, 1, vSupp);
        ++pBound->OracleCiCalls;
        pBound->pReference[i].CiOverlap = Vec_IntSize(vSupp);
    }
    qsort(pBound->pReference, n, sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare);
    Vec_IntFree(vSupp);
    pBound->timeOracle += Abc_Clock()-clk;
}

static void Cec_TranRankBoundStart( Cec_TranRankBound_t * pBound,
    Cec_TranSim_t * pSim, int iTarget, Vec_Int_t * vReservoir,
    Cec_ParTran_t * pPars, Cec_TranProf_t * pProf, word const * pCare )
{
    static int Profile = -1, Trace = -1, FinalMode = -1, FinalProfile = -1;
    Cec_TranSigDot_t * pDot = pSim->pSigDot;
    int i, iObj;
    abctime clk;
    if ( !pBound->fScope ) return;
    pBound->Mode = Cec_TranRankBoundMode();
    if ( Profile < 0 )
    {
        Profile = Cec_TranStrictCexOption("ABC_STRICT_RANK_BOUND_PROFILE", 0, 1);
        Trace = Cec_TranStrictCexOption("ABC_STRICT_RANK_BOUND_TRACE", 0, 1);
    }
    pBound->Profile = Profile;
    pBound->Trace = Trace;
    if ( FinalMode < 0 )
    {
        FinalMode = Cec_TranStrictCexOption("ABC_STRICT_RANK_FINAL_FILTER", 0, 2);
        FinalProfile = Cec_TranStrictCexOption("ABC_STRICT_RANK_FINAL_FILTER_PROFILE", 0, 1);
    }
    pBound->FinalMode = FinalMode;
    pBound->FinalProfile = FinalProfile;
    if ( !pBound->Mode && !Trace ) return;
    pBound->B = pPars->nConstrBaseMax;
    pBound->OriginalPairs = Vec_IntSize(vReservoir);
    pBound->N = (word)64*pSim->nSlots;
    pBound->Root = iTarget; pBound->Round = pProf->PreproofRound;
    pBound->Wave = pProf->PreproofWave; pBound->Scope = pDot ? pDot->Scope : -1;
    pBound->Slots = pSim->nSlots;
    if ( !pBound->Mode ) return; // explicit trace-only original path
    if ( pCare ) pBound->pReason = "care";
    else if ( !pDot || pDot->Mode != 2 || !pDot->pOnes ) pBound->pReason = "requires-dot2";
    else if ( !(pPars->nExplore & 1) ) pBound->pReason = "requires-lazy-CI";
    else if ( pBound->B <= 0 || pBound->B >= pBound->OriginalPairs ) pBound->pReason = "B-covers-or-unbounded";
    else if ( pSim->nSlots <= 0 || pBound->N > (word)0xffffffffu ) pBound->pReason = "word-range";
    if ( pBound->pReason ) return;
    clk = Abc_Clock();
    pBound->Active = 1;
    Cec_TranRankThresholdStart(&pBound->Threshold);
    // Keep the requested bound mode unchanged. Either diagnostic switch
    // enables the same independent full-domain reference and downstream checks.
    pBound->Oracle = pBound->Mode == 2 || pBound->FinalMode == 2;
    pBound->RootOnes = pDot->pOnes[iTarget];
    pBound->pHeap = ABC_ALLOC(word, pBound->B);
    if ( pBound->vTfo )
    {
        pBound->ProtectedIndexBytes = (word)Gia_ManObjNum(pSim->pGia);
        pBound->pProtected = ABC_CALLOC(unsigned char, Gia_ManObjNum(pSim->pGia));
        Vec_IntForEachEntry(pBound->vTfo, iObj, i)
        {
            assert( iObj >= 0 && iObj < Gia_ManObjNum(pSim->pGia) );
            pBound->pProtected[iObj] = 1;
        }
    }
    pBound->timeIndex += Abc_Clock()-clk;
    if ( pBound->Oracle )
        Cec_TranRankBoundReference(pBound, pSim, iTarget, vReservoir);
}

// Scores below the final B-th threshold cannot feed CI or top-B. Retain all
// ties and legal rescue TFOs. Compaction changes positions, never their order;
// final Select still normalizes the identical physical pool to iPos=i.
static void Cec_TranRankFinalFilter( Cec_TranRankBound_t * pBound,
    Vec_Int_t * vReservoir, Cec_TranDivRank_t * pRanks )
{
    int i, iObj, nKept = 0;
    abctime clk = 0;
    if ( !pBound->Active ) return;
    if ( !pBound->FinalMode && !pBound->FinalProfile ) return;
    pBound->FinalBefore = pBound->FinalAfter = Vec_IntSize(vReservoir);
    assert( (word)pBound->FinalBefore == pBound->ScannedPairs );
    pBound->FinalCutoff = pBound->pHeap[0];
    if ( !pBound->FinalMode ) return;
    assert( pBound->nHeap == pBound->B );
    if ( pBound->FinalProfile ) clk = Abc_Clock();
    Vec_IntForEachEntry(vReservoir, iObj, i)
    {
        assert( pRanks[i].iPos == i && pRanks[i].CiOverlap == 0 );
        if ( pRanks[i].Score < pBound->FinalCutoff &&
             !(pBound->pProtected && pBound->pProtected[iObj]) ) continue;
        Vec_IntWriteEntry(vReservoir, nKept, iObj);
        pRanks[nKept] = pRanks[i];
        pRanks[nKept].iPos = nKept;
        ++nKept;
    }
    assert( nKept >= pBound->B );
    Vec_IntShrink(vReservoir, nKept);
    pBound->FinalAfter = nKept;
    if ( pBound->FinalProfile ) pBound->timeFinalFilter += Abc_Clock()-clk;
    // Already-scored removals save downstream rank/selection work. Never
    // subtract already-paid DOT scoring from the actual pair/word counters.
    if ( pBound->Oracle )
    {
        int j = 0;
        word Cutoff = pBound->pReference[pBound->B-1].Score;
        clk = Abc_Clock();
        assert( Cutoff == pBound->FinalCutoff );
        ++pBound->FinalThresholdChecks;
        Vec_IntForEachEntry(pBound->vReference, iObj, i)
        {
            int fKeep = pBound->pOracleScores[i] >= Cutoff ||
                (pBound->pProtected && pBound->pProtected[iObj]);
            ++pBound->FinalOracleChecks;
            if ( !fKeep ) continue;
            assert( j < nKept && Vec_IntEntry(vReservoir, j) == iObj );
            assert( pRanks[j].Score == pBound->pOracleScores[i] &&
                    pRanks[j].CiOverlap == 0 && pRanks[j].iPos == j );
            ++j;
        }
        assert( j == nKept );
        pBound->timeOracle += Abc_Clock()-clk;
    }
}

static Cec_TranDivRank_t * Cec_TranRankDivReservoirBounded( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vReservoir, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, word const * pCare, int fGlobalDivs,
    Cec_TranRankBound_t * pBound )
{
    Gia_Man_t * p = pSim->pGia;
    Cec_TranDivRank_t * pRanks = ABC_CALLOC( Cec_TranDivRank_t,
        Vec_IntSize(vReservoir) );
    word * pTarget = Cec_TranSimObj( pSim, iTarget );
    word * pDiv;
    word nOff0, nOff1, nOn0, nOn1, nOff = 0, nOn = 0;
    Vec_Int_t * vRootSupp = Vec_IntAlloc( 32 );
    Vec_Int_t * vDivSupp = Vec_IntAlloc( 32 );
    int i, k, s, iObj, RootNode = iTarget;
    int nRank = Vec_IntSize(vReservoir), nKeep = nRank, nScored = 0;
    word DotPopcountsStart = 0, ExceptionStart = 0;
    long long RankWork = 2LL * pSim->nSlots * (nRank + 1);
    abctime clk = Abc_Clock(), clkFinal = 0;
    Cec_TranSigDot_t * pDot = pCare ? NULL : pSim->pSigDot;
    word SetupWords = pDot ? pDot->SetupWords : 0;
    word SetupPopcounts = pDot ? pDot->SetupPopcounts : 0;
    abctime timeSetup = pDot ? pDot->timeSetup : 0;
    Cec_TranPreproofEvent( pProf, p, "rank-score", 0, nRank, pSim->nSlots );
    // Target marginals are shared by every divisor. The two zero-divisor
    // quadrants are exact complements of the one-divisor quadrants, including
    // masked care. Preserve the score and all ranking ties with half as many
    // per-divisor popcounts; no cross-root signature cache is needed.
    if ( pDot )
    {
        DotPopcountsStart = pDot->DenseWords + pDot->ExceptionWords + pDot->SetupPopcounts +
            2*pDot->OraclePairWords + 2*pDot->OracleTargetWords;
        Cec_TranSigDotAssertOwner(pDot);
        ++pDot->Calls; pDot->Pairs += nRank;
        pDot->BaselineWords += (word)nRank*pSim->nSlots;
        if ( pDot->Mode )
        {
            Cec_TranSigDotPrepare(pDot);
            nOn = pDot->pOnes[iTarget];
            nOff = (word)64*pSim->nSlots - nOn;
            ++pDot->MarginalLookups;
        }
    }
    if ( !pDot || !pDot->Mode )
    for ( s = 0; s < pSim->nSlots; s++ )
    {
        word Care = pCare ? pCare[s] : ~(word)0;
        nOff += Abc_TtCountOnes( ~pTarget[s] & Care );
        nOn  += Abc_TtCountOnes(  pTarget[s] & Care );
    }
    if ( pDot && pDot->Mode == 3 )
    {
        word RawOn = 0, RawOff = 0;
        for ( s = 0; s < pSim->nSlots; ++s )
        {
            RawOn += Abc_TtCountOnes(pTarget[s]);
            RawOff += Abc_TtCountOnes(~pTarget[s]);
        }
        assert(RawOn == nOn && RawOff == nOff);
        pDot->OracleTargetWords += pSim->nSlots;
    }
    Cec_TranRankBoundStart(pBound, pSim, iTarget, vReservoir, pPars, pProf, pCare);
    if ( pBound->Active )
    {
        ExceptionStart = pDot->ExceptionWords;
        pBound->SetupWords = pDot->SetupWords-SetupWords;
        pBound->SetupPopcounts = pDot->SetupPopcounts-SetupPopcounts;
        pBound->timeSetup = pDot->timeSetup-timeSetup;
    }
    Vec_IntForEachEntry( vReservoir, iObj, i )
    {
        if ( pBound->Active )
        {
            word Words = (word)Abc_MinInt(pDot->pCounts[iTarget], pDot->pCounts[iObj]);
            word Upper = Cec_TranRankBoundUpper(pBound->N, nOn, pDot->pOnes[iObj]);
            int fProtected = pBound->pProtected && pBound->pProtected[iObj];
            ++pBound->BoundChecks;
            pBound->ProtectedPairs += fProtected;
            if ( pBound->Oracle )
            {
                assert( Upper >= pBound->pOracleScores[i] );
                ++pBound->OracleChecks;
            }
            if ( !fProtected && pBound->nHeap == pBound->B && Upper < pBound->pHeap[0] )
            {
                if ( pBound->Oracle ) assert( pBound->pOracleScores[i] < pBound->pHeap[0] );
                ++pBound->PrunedPairs; pBound->PrunedWords += Words;
                continue;
            }
            ++pBound->ScannedPairs; pBound->ActualWords += Words;
        }
        pDiv = Cec_TranSimObj( pSim, iObj );
        nOff1 = nOn1 = 0;
        if ( pDot && pDot->Mode )
        {
            nOn1 = Cec_TranSigDotIntersection(pDot, iTarget, iObj);
            assert(nOn1 <= pDot->pOnes[iObj]);
            nOff1 = pDot->pOnes[iObj] - nOn1;
            ++pDot->MarginalLookups;
        }
        else
        for ( s = 0; s < pSim->nSlots; s++ )
        {
            word Care = pCare ? pCare[s] : ~(word)0;
            nOff1 += Abc_TtCountOnes( ~pTarget[s] &  pDiv[s] & Care );
            nOn1  += Abc_TtCountOnes(  pTarget[s] &  pDiv[s] & Care );
        }
        if ( pDot && pDot->Mode == 3 )
        {
            word RawOn1 = 0, RawOff1 = 0;
            for ( s = 0; s < pSim->nSlots; ++s )
            {
                RawOn1 += Abc_TtCountOnes(pTarget[s] & pDiv[s]);
                RawOff1 += Abc_TtCountOnes(~pTarget[s] & pDiv[s]);
            }
            assert(RawOn1 == nOn1 && RawOff1 == nOff1);
            pDot->OraclePairWords += pSim->nSlots;
        }
        nOff0 = nOff - nOff1;
        nOn0 = nOn - nOn1;
        pRanks[nScored].Score = nOff0 * nOn1 + nOff1 * nOn0;
        pRanks[nScored].iPos = nScored;
        if ( pBound->Active )
        {
            if ( pBound->Oracle ) assert( pRanks[nScored].Score == pBound->pOracleScores[i] );
            Cec_TranRankBoundHeap(pBound, pRanks[nScored].Score);
            // Writes only to an already-consumed position; the remaining
            // reservoir traversal and the original iPos tie order are stable.
            Vec_IntWriteEntry(vReservoir, nScored, iObj);
        }
        ++nScored;
    }
    if ( pBound->Active )
    {
        assert( pBound->nHeap == pBound->B && nScored >= pBound->B );
        assert( pBound->ScannedPairs + pBound->PrunedPairs == (word)nRank );
        assert( pDot->ExceptionWords-ExceptionStart == pBound->ActualWords );
        Vec_IntShrink(vReservoir, nScored);
        // DOT work counters describe actual pair kernels, not skipped bounds.
        pDot->Pairs -= pBound->PrunedPairs;
        pDot->BaselineWords -= pBound->PrunedPairs*pSim->nSlots;
    }
    pProf->timeExpRankScore += Abc_Clock() - clk;
    if ( pDot ) pDot->timeRank += Abc_Clock() - clk;
    if ( pDot && pDot->Mode )
        RankWork = pDot->DenseWords + pDot->ExceptionWords + pDot->SetupPopcounts +
            2*pDot->OraclePairWords + 2*pDot->OracleTargetWords - DotPopcountsStart;
    // This old diagnostic is actual stage work.  Lazy setup occurs inside this
    // timed rank context; the new dot prefix separately identifies setup and
    // diagnostic oracle work instead of pretending these are raw baseline.
    Cec_TranPreproofEvent( pProf, p, "rank-score", 1, nRank, RankWork );
    Cec_TranRankFinalFilter(pBound, vReservoir, pRanks);
    nRank = nKeep = Vec_IntSize(vReservoir);
    clk = Abc_Clock();
    Cec_TranPreproofEvent( pProf, p, "rank-support", 0, nRank, 0 );
    if ( pPars->nExplore & 1 )
    {
        if ( pSim->pCiCounts == NULL )
            pSim->pCiCounts = ABC_CALLOC( int, Gia_ManObjNum(p) );
        if ( pBound->Active && pBound->FinalProfile ) clkFinal = Abc_Clock();
        if ( pBound->Active && pBound->Threshold.Enabled )
            Cec_TranRankThresholdFirst(&pBound->Threshold, pRanks, nRank,
                pBound->B, pBound->pHeap[0], pBound->FinalMode);
        else
            qsort( pRanks, nRank, sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare );
        if ( pBound->Active && pBound->FinalProfile )
        {
            pBound->timeFinalSort1 += Abc_Clock()-clkFinal;
            pBound->FinalSort1 = nRank;
        }
        if ( pPars->nConstrBaseMax && nKeep > pPars->nConstrBaseMax )
        {
            nKeep = pPars->nConstrBaseMax;
            while ( nKeep < nRank && pRanks[nKeep].Score == pRanks[nKeep-1].Score )
                nKeep++;
        }
    }
    if ( !fGlobalDivs && (!(pPars->nExplore & 1) || (pPars->nExplore & 8)) )
        Gia_ManCollectCis( p, &RootNode, 1, vRootSupp );
    if ( pBound->Active && pBound->FinalProfile )
    {
        pBound->FinalCiItems = nKeep;
        pBound->FinalCiHits = pProf->nExpCiHit;
        pBound->FinalCiMisses = pProf->nExpCiMiss;
        clkFinal = Abc_Clock();
    }
    for ( i = 0; i < nKeep; i++ )
    {
        iObj = Vec_IntEntry( vReservoir, pRanks[i].iPos );
        if ( (pPars->nExplore & 1) && pSim->pCiCounts[iObj] )
        {
            pRanks[i].CiOverlap = pSim->pCiCounts[iObj] - 1;
            pProf->nExpCiHit++;
            if ( !(pPars->nExplore & 8) )
                continue;
        }
        else
            pProf->nExpCiMiss++;
        Vec_IntClear( vDivSupp );
        Gia_ManCollectCis( p, &iObj, 1, vDivSupp );
        if ( (pPars->nExplore & 1) || fGlobalDivs )
        {
            // The frozen global-earlier quality configuration ranks ties by
            // support cardinality, not root-support intersection.  Cardinality
            // caching is valid for either domain; the subset assertion applies
            // only to the original TFI/complete-fanin domain.
            if ( (pPars->nExplore & 8) && pSim->pCiCounts &&
                 pSim->pCiCounts[iObj] )
                assert( pSim->pCiCounts[iObj] == Vec_IntSize(vDivSupp) + 1 );
            pRanks[i].CiOverlap = Vec_IntSize( vDivSupp );
            if ( pPars->nExplore & 1 )
                pSim->pCiCounts[iObj] = pRanks[i].CiOverlap + 1;
            if ( (pPars->nExplore & 8) && !fGlobalDivs )
                Vec_IntForEachEntry( vDivSupp, iObj, k )
                    assert( Vec_IntFind(vRootSupp, iObj) >= 0 );
        }
        else
        {
            pRanks[i].CiOverlap = 0;
            Vec_IntForEachEntry( vDivSupp, iObj, k )
                pRanks[i].CiOverlap += Vec_IntFind(vRootSupp, iObj) >= 0;
        }
    }
    if ( pBound->Active && pBound->FinalProfile )
    {
        pBound->timeFinalCi += Abc_Clock()-clkFinal;
        pBound->FinalCiHits = pProf->nExpCiHit-pBound->FinalCiHits;
        pBound->FinalCiMisses = pProf->nExpCiMiss-pBound->FinalCiMisses;
    }
    pProf->timeExpRankCi += Abc_Clock() - clk;
    Cec_TranPreproofEvent( pProf, p, "rank-support", 1, nKeep, nKeep );
    Cec_TranPreproofEvent( pProf, p, "rank-sort", 0, nRank, 0 );
    if ( pBound->Active && pBound->FinalProfile ) clkFinal = Abc_Clock();
    if ( pBound->Active && pBound->Threshold.Enabled )
        Cec_TranRankThresholdSecond(&pBound->Threshold, pRanks);
    else
        qsort( pRanks, Vec_IntSize(vReservoir),
            sizeof(Cec_TranDivRank_t), Cec_TranDivRankCompare );
    if ( pBound->Active && pBound->FinalProfile )
    {
        pBound->timeFinalSort2 += Abc_Clock()-clkFinal;
        pBound->FinalSort2 = Vec_IntSize(vReservoir);
    }
    Cec_TranPreproofEvent( pProf, p, "rank-sort", 1, nRank, nRank );
    if ( pBound->Oracle && pBound->Active )
    {
        unsigned char * pPresent = ABC_CALLOC(unsigned char, Gia_ManObjNum(pSim->pGia));
        int j = 0;
        abctime clkOracle = Abc_Clock();
        for ( i = 0; i < pBound->B; ++i )
        {
            assert( Vec_IntEntry(vReservoir, pRanks[i].iPos) ==
                    Vec_IntEntry(pBound->vReference, pBound->pReference[i].iPos) );
            assert( pRanks[i].Score == pBound->pReference[i].Score &&
                    pRanks[i].CiOverlap == pBound->pReference[i].CiOverlap );
        }
        Vec_IntForEachEntry(vReservoir, iObj, i) pPresent[iObj] = 1;
        // Check every exact survivor against the full original order, not
        // only top-B. This includes low-score TFOs which rescue may pin.
        for ( i = 0; i < pBound->OriginalPairs; ++i )
        {
            iObj = Vec_IntEntry(pBound->vReference, pBound->pReference[i].iPos);
            if ( pBound->pProtected && pBound->pProtected[iObj] ) assert(pPresent[iObj]);
            if ( !pPresent[iObj] ) continue;
            assert( j < nRank && Vec_IntEntry(vReservoir, pRanks[j].iPos) == iObj );
            assert( pRanks[j].Score == pBound->pReference[i].Score &&
                    pRanks[j].CiOverlap == pBound->pReference[i].CiOverlap );
            ++j; ++pBound->OracleRankChecks;
        }
        assert(j == nRank);
        ABC_FREE(pPresent);
        pBound->timeOracle += Abc_Clock()-clkOracle;
    }
    if ( Cec_TranSigDotTraceEnabled() && !pBound->Active )
    {
        Abc_Print(1, "stran-signature dot-trace rank: target=%d round=%d wave=%d count=%d ranks=",
            iTarget, pProf->PreproofRound, pProf->PreproofWave, nRank);
        for ( i = 0; i < nRank; ++i )
            Abc_Print(1, "%s%d:%llu:%d:%d", i ? "," : "",
                Vec_IntEntry(vReservoir, pRanks[i].iPos),
                (unsigned long long)pRanks[i].Score, pRanks[i].CiOverlap, pRanks[i].iPos);
        Abc_Print(1, "\n");
    }
    Vec_IntFree( vRootSupp );
    Vec_IntFree( vDivSupp );
    return pRanks;
}

// Preserve the original API for relational/trace callers.  With fScope=0,
// Start returns before reading bound options or allocating any bound state;
// this stack context owns no resources requiring Stop.
// Ranking must choose the actual iterator input, not merely annotate an
// already-truncated BFS prefix.  Rewrite the reservoir in rank order and only
// then shrink it to B.  B=0 intentionally keeps the complete allowed TFI.
static int Cec_TranSelectRankedDivPool( Vec_Int_t * vReservoir,
    Cec_TranDivRank_t * pRanks, int nPoolMax, Vec_Int_t * vPinned )
{
    Vec_Int_t * vRanked;
    int i, nKeep = nPoolMax ?
        Abc_MinInt(nPoolMax, Vec_IntSize(vReservoir)) :
        Vec_IntSize(vReservoir);
    int nRescued = 0;
    // Normally the globally ranked prefix is the final Build pool.  A
    // root-local exact core may pin a few complementary nodes which would
    // otherwise fall below B.  Preserve the global order among all retained
    // nodes and keep the final pool size unchanged.
    if ( vPinned && nPoolMax && Vec_IntSize(vPinned) <= nKeep )
    {
        Cec_TranDivRank_t * pKept = ABC_ALLOC( Cec_TranDivRank_t, nKeep );
        char * pChosen = ABC_CALLOC( char, Vec_IntSize(vReservoir) );
        int k, iObj, iPos, nChosen = 0;
        Vec_IntForEachEntry( vPinned, iObj, i )
        {
            iPos = Vec_IntFind( vReservoir, iObj );
            if ( iPos < 0 || pChosen[iPos] )
                continue;
            pChosen[iPos] = 1;
            nChosen++;
            for ( k = 0; k < nKeep; k++ )
                if ( pRanks[k].iPos == iPos )
                    break;
            nRescued += k == nKeep;
        }
        if ( nRescued )
        {
            for ( i = 0; i < Vec_IntSize(vReservoir) && nChosen < nKeep; i++ )
                if ( !pChosen[pRanks[i].iPos] )
                    pChosen[pRanks[i].iPos] = 1, nChosen++;
            vRanked = Vec_IntAlloc( nKeep );
            for ( i = k = 0; i < Vec_IntSize(vReservoir); i++ )
                if ( pChosen[pRanks[i].iPos] )
                {
                    Vec_IntPush( vRanked, Vec_IntEntry(vReservoir,
                        pRanks[i].iPos) );
                    pKept[k] = pRanks[i];
                    pKept[k].iPos = k;
                    k++;
                }
            assert( k == nKeep );
            Vec_IntClear( vReservoir );
            Vec_IntAppend( vReservoir, vRanked );
            memcpy( pRanks, pKept, sizeof(Cec_TranDivRank_t) * nKeep );
            Vec_IntFree( vRanked );
            ABC_FREE( pChosen );
            ABC_FREE( pKept );
            return nRescued;
        }
        ABC_FREE( pChosen );
        ABC_FREE( pKept );
    }
    vRanked = Vec_IntAlloc( Vec_IntSize(vReservoir) );
    for ( i = 0; i < nKeep; i++ )
        Vec_IntPush( vRanked, Vec_IntEntry(vReservoir, pRanks[i].iPos) );
    Vec_IntClear( vReservoir );
    Vec_IntAppend( vReservoir, vRanked );
    // pRanks is already sorted in exactly the order copied into vReservoir.
    // Normalize its positions so the selected pool and its rank metadata can
    // be reused by constructed discovery without ranking the same divisors a
    // second time.
    for ( i = 0; i < nKeep; i++ )
        pRanks[i].iPos = i;
    Vec_IntFree( vRanked );
    return 0;
}

// The oracle uses the full original ranking and the identical observed-core
// pins. Top-B was checked before rescue; all legal TFO members were protected,
// so rescue received the same top-B union TFO inputs in the same order.
static int Cec_TranRankBoundSelectPool( Vec_Int_t * vReservoir,
    Cec_TranDivRank_t * pRanks, int nPoolMax, Vec_Int_t * vPinned,
    Cec_TranRankBound_t * pBound )
{
    int nRescued = Cec_TranSelectRankedDivPool(vReservoir, pRanks, nPoolMax, vPinned);
    int i, nReference;
    abctime clk;
    if ( !pBound->Active || !pBound->Oracle ) return nRescued;
    clk = Abc_Clock();
    nReference = Cec_TranSelectRankedDivPool(pBound->vReference,
        pBound->pReference, nPoolMax, vPinned);
    assert( nRescued == nReference );
    assert( Vec_IntSize(vReservoir) == Vec_IntSize(pBound->vReference) );
    for ( i = 0; i < Vec_IntSize(vReservoir); ++i )
    {
        assert( Vec_IntEntry(vReservoir, i) == Vec_IntEntry(pBound->vReference, i) );
        assert( pRanks[i].Score == pBound->pReference[i].Score );
        assert( pRanks[i].CiOverlap == pBound->pReference[i].CiOverlap );
        assert( pRanks[i].iPos == i && pBound->pReference[i].iPos == i );
        ++pBound->OraclePoolChecks;
    }
    pBound->timeOracle += Abc_Clock()-clk;
    return nRescued;
}

// Validate rescue's complete ordered input before any core or pin is chosen.
static void Cec_TranRankBoundCheckCore( Cec_TranRankBound_t * pBound,
    Vec_Int_t * vCorePool )
{
    Vec_Int_t * vExpected;
    int i, iObj;
    abctime clk;
    if ( !pBound->Active || !pBound->Oracle ) return;
    clk = Abc_Clock();
    vExpected = Vec_IntAlloc(pBound->B);
    for ( i = 0; i < pBound->B; ++i )
        Vec_IntPush(vExpected, Vec_IntEntry(pBound->vReference, pBound->pReference[i].iPos));
    assert(pBound->vTfo != NULL);
    Vec_IntForEachEntry(pBound->vTfo, iObj, i)
        if ( Vec_IntFind(pBound->vReference, iObj) >= 0 && Vec_IntFind(vExpected, iObj) < 0 )
            Vec_IntPush(vExpected, iObj);
    assert(Vec_IntSize(vExpected) == Vec_IntSize(vCorePool));
    Vec_IntForEachEntry(vExpected, iObj, i)
    {
        assert(iObj == Vec_IntEntry(vCorePool, i));
        ++pBound->OracleCoreChecks;
    }
    Vec_IntFree(vExpected);
    pBound->timeOracle += Abc_Clock()-clk;
}

static void Cec_TranRankBoundStop( Cec_TranRankBound_t * pBound,
    Vec_Int_t * vPool, Cec_TranDivRank_t const * pRanks )
{
    int i;
    if ( pBound->Active )
        Cec_TranRankThresholdStop(&pBound->Threshold, pBound->Mode,
            pBound->FinalMode, pBound->Scope, pBound->Round, pBound->Wave, pBound->Root);
    if ( pBound->Active && pBound->FinalProfile )
        Abc_Print(1, "stran-rank-final-filter profile: schema=1 mode=%d bound-mode=%d status=%s source-scope=%d round=%d wave=%d root=%d B=%d slots=%d original-pairs=%d scanned-pairs=%llu rank-input=%d rank-output=%d filter-removed=%d cutoff=%llu sort1-records=%d sort2-records=%d ci-items=%d ci-hits=%llu ci-misses=%llu filter-sec=%.6f sort1-sec=%.6f ci-sec=%.6f sort2-sec=%.6f oracle-enabled=%d membership-checks=%llu threshold-checks=%llu oracle-rank-checks=%llu oracle-core-checks=%llu oracle-pool-checks=%llu retained-pool=%d\n",
            pBound->FinalMode, pBound->Mode, pBound->FinalMode ? "APPLIED" : "DISABLED",
            pBound->Scope, pBound->Round, pBound->Wave, pBound->Root,
            pBound->B, pBound->Slots, pBound->OriginalPairs, (unsigned long long)pBound->ScannedPairs,
            pBound->FinalBefore, pBound->FinalAfter, pBound->FinalBefore-pBound->FinalAfter,
            (unsigned long long)pBound->FinalCutoff, pBound->FinalSort1, pBound->FinalSort2,
            pBound->FinalCiItems, (unsigned long long)pBound->FinalCiHits,
            (unsigned long long)pBound->FinalCiMisses,
            (double)pBound->timeFinalFilter/CLOCKS_PER_SEC,
            (double)pBound->timeFinalSort1/CLOCKS_PER_SEC,
            (double)pBound->timeFinalCi/CLOCKS_PER_SEC,
            (double)pBound->timeFinalSort2/CLOCKS_PER_SEC, pBound->Oracle,
            (unsigned long long)pBound->FinalOracleChecks,
            (unsigned long long)pBound->FinalThresholdChecks,
            (unsigned long long)pBound->OracleRankChecks,
            (unsigned long long)pBound->OracleCoreChecks,
            (unsigned long long)pBound->OraclePoolChecks, Vec_IntSize(vPool));
    if ( pBound->Mode && pBound->Profile && !pBound->Active )
        Abc_Print(1, "stran-rank-bound profile: schema=1 mode=%d status=FALLBACK reason=%s source-scope=%d round=%d wave=%d root=%d B=%d slots=%d original-pairs=%d\n",
            pBound->Mode, pBound->pReason, pBound->Scope, pBound->Round,
            pBound->Wave, pBound->Root, pBound->B, pBound->Slots, pBound->OriginalPairs);
    if ( pBound->Active && pBound->Profile )
        Abc_Print(1, "stran-rank-bound profile: schema=1 mode=%d status=%s reason=%s source-scope=%d round=%d wave=%d root=%d B=%d slots=%d original-pairs=%d scanned-pairs=%llu pruned-pairs=%llu protected-pairs=%llu bound-checks=%llu bound-marginal-lookups=%llu actual-exception-words=%llu pruned-exception-words=%llu original-raw-pair-words=%llu heap-updates=%llu heap-comparisons=%llu heap-bytes=%llu protected-index-bytes=%llu heap-update-sec=%.6f index-sec=%.6f setup-word-visits=%llu setup-popcounts=%llu setup-sec=%.6f oracle-word-iterations=%llu oracle-popcounts=%llu oracle-ci-calls=%llu oracle-checks=%llu oracle-rank-checks=%llu oracle-core-checks=%llu oracle-pool-checks=%llu oracle-sec=%.6f retained-pool=%d\n",
            pBound->Mode, pBound->Active ? "APPLIED" : "FALLBACK",
            pBound->pReason ? pBound->pReason : "none", pBound->Scope,
            pBound->Round, pBound->Wave, pBound->Root, pBound->B, pBound->Slots,
            pBound->OriginalPairs, (unsigned long long)pBound->ScannedPairs,
            (unsigned long long)pBound->PrunedPairs, (unsigned long long)pBound->ProtectedPairs,
            (unsigned long long)pBound->BoundChecks,
            (unsigned long long)(pBound->Active ? 1+pBound->BoundChecks : 0),
            (unsigned long long)pBound->ActualWords,
            (unsigned long long)pBound->PrunedWords,
            (unsigned long long)((word)pBound->OriginalPairs*pBound->Slots),
            (unsigned long long)pBound->HeapUpdates, (unsigned long long)pBound->HeapComparisons,
            (unsigned long long)(pBound->Active ? (word)sizeof(word)*pBound->B : 0),
            (unsigned long long)pBound->ProtectedIndexBytes,
            (double)pBound->timeHeap/CLOCKS_PER_SEC, (double)pBound->timeIndex/CLOCKS_PER_SEC,
            (unsigned long long)pBound->SetupWords, (unsigned long long)pBound->SetupPopcounts,
            (double)pBound->timeSetup/CLOCKS_PER_SEC,
            (unsigned long long)pBound->OracleWords, (unsigned long long)(2*pBound->OracleWords),
            (unsigned long long)pBound->OracleCiCalls, (unsigned long long)pBound->OracleChecks,
            (unsigned long long)pBound->OracleRankChecks, (unsigned long long)pBound->OracleCoreChecks,
            (unsigned long long)pBound->OraclePoolChecks,
            (double)pBound->timeOracle/CLOCKS_PER_SEC, Vec_IntSize(vPool));
    if ( pBound->Trace )
    {
        Abc_Print(1, "stran-rank-bound trace: schema=1 source-scope=%d round=%d wave=%d root=%d count=%d pool=",
            pBound->Scope, pBound->Round, pBound->Wave, pBound->Root, Vec_IntSize(vPool));
        for ( i = 0; i < Vec_IntSize(vPool); ++i )
            Abc_Print(1, "%s%d:%llu:%d:%d", i ? "," : "", Vec_IntEntry(vPool, i),
                (unsigned long long)pRanks[i].Score, pRanks[i].CiOverlap, pRanks[i].iPos);
        Abc_Print(1, "\n");
    }
    ABC_FREE(pBound->pHeap);
    ABC_FREE(pBound->pProtected);
    ABC_FREE(pBound->pOracleScores);
    ABC_FREE(pBound->pReference);
    Vec_IntFreeP(&pBound->vReference);
}
