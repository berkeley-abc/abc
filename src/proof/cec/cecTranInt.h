// Shared internal types and profiling state.
// Private implementation fragment included only by cecTrans.c.

// Detailed progress is independent of the concise exact Build profile.
#define CEC_TRAN_VERBOSE( Enabled, ... ) \
    do { if ( Enabled ) Abc_Print( 1, __VA_ARGS__ ); } while ( 0 )

// COM is deliberately independent of the SEQ q/j experiment.  Arbitrary-
// state certificates do not use retained induction helpers, so COM submits
// one modest frontier and commits it immediately instead of accumulating
// proof micro-batches on the initial graph.
extern int Abc_ResubQualityOption( char const * pName );
extern int Abc_ResubQualityNoTruncation( void );
static int Cec_TranQualityActualCost( void )
{
    return Abc_ResubQualityOption( "ABC_STRAN_QUALITY_ACTUAL_COST" );
}

#define CEC_TRAN_COMB_BUILD_Q 4
#define CEC_TRAN_BUILD_MFFC_BINS 6
#define CEC_TRAN_PIVOT_RANK_BINS 8
#define CEC_TRAN_PIVOT_RATIO_BINS 5
#define CEC_TRAN_PIVOT_KIND_BINS 2
#define CEC_TRAN_MULTIPATH_RANK_BINS 9
#define CEC_TRAN_MULTIPATH_PATH_BINS 4
#define CEC_TRAN_MULTIPATH_CELLS \
    (CEC_TRAN_MULTIPATH_RANK_BINS * CEC_TRAN_MULTIPATH_PATH_BINS)

// Shared fixed-layout payload returned by giaResub.c.  Counts cover every
// greedy pivot consumed inside one Next(), including pivots whose recursive
// remainder failed and therefore never became a candidate.
enum
{
    CEC_TRAN_PIVOT_FRONTIER_FIRST = 0,
    CEC_TRAN_PIVOT_FRONTIER_SIZE,
    CEC_TRAN_PIVOT_FRONTIER_UNIQUE,
    CEC_TRAN_PIVOT_FRONTIER_ZERO_NOVEL,
    CEC_TRAN_PIVOT_FRONTIER_COVER_SUM,
    CEC_TRAN_PIVOT_FRONTIER_NOVEL_SUM,
    CEC_TRAN_PIVOT_ATTEMPT_TOTAL,
    CEC_TRAN_PIVOT_FOUND_TOTAL,
    CEC_TRAN_PIVOT_TIME_TOTAL,
    CEC_TRAN_PIVOT_SCHED_FRONTIERS,
    CEC_TRAN_PIVOT_SCHED_PIVOTS,
    CEC_TRAN_PIVOT_SCHED_COMPLETE,
    CEC_TRAN_PIVOT_SCHED_TIME,
    CEC_TRAN_CACHE_LOOKUPS,
    CEC_TRAN_CACHE_HITS,
    CEC_TRAN_CACHE_MISSES,
    CEC_TRAN_CACHE_SAME_PAGE_HITS,
    CEC_TRAN_CACHE_CROSS_PAGE_HITS,
    CEC_TRAN_CACHE_FAIL_HITS,
    CEC_TRAN_CACHE_SUCCESS_HITS,
    CEC_TRAN_CACHE_SAVED_TIME,
    CEC_TRAN_CACHE_LOOKUP_TIME,
    CEC_TRAN_CACHE_PAYLOAD_BYTES,
    CEC_TRAN_REC_CALLS,
    CEC_TRAN_REC_UNIQUE,
    CEC_TRAN_REC_DUPLICATE,
    CEC_TRAN_REC_SAME_PAGE,
    CEC_TRAN_REC_CROSS_PAGE,
    CEC_TRAN_REC_FAIL_HITS,
    CEC_TRAN_REC_SUCCESS_DUPLICATE,
    CEC_TRAN_REC_PAYLOAD_BYTES,
    CEC_TRAN_REC_SAVED_TIME,
    CEC_TRAN_REC_LOOKUP_TIME,
    CEC_TRAN_REC_DUP_DEPTH_0,
    CEC_TRAN_REC_DUP_DEPTH_1,
    CEC_TRAN_REC_DUP_DEPTH_2,
    CEC_TRAN_REC_DUP_DEPTH_3PLUS,
    CEC_TRAN_MULTIPATH_CACHE_ENTRIES,
    CEC_TRAN_MULTIPATH_CACHE_LOOKUPS,
    CEC_TRAN_MULTIPATH_CACHE_HITS,
    CEC_TRAN_MULTIPATH_CACHE_FAIL_HITS,
    CEC_TRAN_MULTIPATH_CACHE_SUCCESS_HITS,
    CEC_TRAN_MULTIPATH_CACHE_PAYLOAD_BYTES,
    CEC_TRAN_MULTIPATH_ATTEMPTS,
    CEC_TRAN_MULTIPATH_FOUND = CEC_TRAN_MULTIPATH_ATTEMPTS +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_TIME = CEC_TRAN_MULTIPATH_FOUND +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_SECOND_COVER = CEC_TRAN_MULTIPATH_TIME +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_DIVERSITY_NEW =
        CEC_TRAN_MULTIPATH_SECOND_COVER + CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_MULTIPATH_DIVERSITY_SYM =
        CEC_TRAN_MULTIPATH_DIVERSITY_NEW + CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_PIVOT_CURRENT_PATH = CEC_TRAN_MULTIPATH_DIVERSITY_SYM +
        CEC_TRAN_MULTIPATH_CELLS,
    CEC_TRAN_PIVOT_CURRENT_SECOND_RANK,
    CEC_TRAN_PIVOT_CURRENT_SECOND_COVER,
    CEC_TRAN_PIVOT_CURRENT_DIVERSITY_NEW,
    CEC_TRAN_PIVOT_CURRENT_DIVERSITY_SYM,
    CEC_TRAN_PIVOT_CURRENT_VALID,
    CEC_TRAN_PIVOT_CURRENT_KIND,
    CEC_TRAN_PIVOT_CURRENT_RANK,
    CEC_TRAN_PIVOT_CURRENT_COVER,
    CEC_TRAN_PIVOT_CURRENT_TOTAL,
    CEC_TRAN_PIVOT_CURRENT_NOVEL,
    CEC_TRAN_PIVOT_CURRENT_REMAIN,
    CEC_TRAN_PIVOT_CURRENT_DUPLICATE,
    CEC_TRAN_PIVOT_RANK_ATTEMPTS,
    CEC_TRAN_PIVOT_RANK_FOUND = CEC_TRAN_PIVOT_RANK_ATTEMPTS +
        CEC_TRAN_PIVOT_RANK_BINS,
    CEC_TRAN_PIVOT_RANK_TIME = CEC_TRAN_PIVOT_RANK_FOUND +
        CEC_TRAN_PIVOT_RANK_BINS,
    CEC_TRAN_PIVOT_NOVEL_ATTEMPTS = CEC_TRAN_PIVOT_RANK_TIME +
        CEC_TRAN_PIVOT_RANK_BINS,
    CEC_TRAN_PIVOT_NOVEL_FOUND = CEC_TRAN_PIVOT_NOVEL_ATTEMPTS +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_NOVEL_TIME = CEC_TRAN_PIVOT_NOVEL_FOUND +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_COVER_ATTEMPTS = CEC_TRAN_PIVOT_NOVEL_TIME +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_COVER_FOUND = CEC_TRAN_PIVOT_COVER_ATTEMPTS +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_COVER_TIME = CEC_TRAN_PIVOT_COVER_FOUND +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_KIND_ATTEMPTS = CEC_TRAN_PIVOT_COVER_TIME +
        CEC_TRAN_PIVOT_RATIO_BINS,
    CEC_TRAN_PIVOT_KIND_FOUND = CEC_TRAN_PIVOT_KIND_ATTEMPTS +
        CEC_TRAN_PIVOT_KIND_BINS,
    CEC_TRAN_PIVOT_KIND_TIME = CEC_TRAN_PIVOT_KIND_FOUND +
        CEC_TRAN_PIVOT_KIND_BINS,
    CEC_TRAN_PIVOT_STATE_ATTEMPTS = CEC_TRAN_PIVOT_KIND_TIME +
        CEC_TRAN_PIVOT_KIND_BINS,
    CEC_TRAN_PIVOT_STATE_FOUND = CEC_TRAN_PIVOT_STATE_ATTEMPTS + 2,
    CEC_TRAN_PIVOT_STATE_TIME = CEC_TRAN_PIVOT_STATE_FOUND + 2,
    CEC_TRAN_PIVOT_PROFILE_SIZE = CEC_TRAN_PIVOT_STATE_TIME + 2
};

enum
{
    CEC_TRAN_CAND_CONST = 0,
    CEC_TRAN_CAND_EXIST = 1,
    CEC_TRAN_CAND_CONSTR = 2
};
enum
{
    CEC_TRAN_STATE_CANDIDATE = 0,
    CEC_TRAN_STATE_STALE,
    CEC_TRAN_STATE_TRIED_SEQ,
    CEC_TRAN_STATE_PROVED_COMB,
    CEC_TRAN_STATE_PROVED_SEQ,
    CEC_TRAN_STATE_SELECTED
};

extern void Abc_ResubPrepareManager( int nWords );
extern void Abc_ResubProblemCacheStart( int nPayloadMiB );
extern void Abc_ResubProblemCacheStop( int fPrint );
extern void Abc_ResubSetBothPolarities( int Enable );
extern int Abc_ResubSetCarePairTruth( int Enable );
extern void * Abc_ResubIteratorResumeStart( void ** ppDivs, int nDivs,
    int nWords, int nLimit, int nDivsMax, int fUseZero, int fUseXor,
    int fUseSolvSched, int nStage5Paths, int fProfilePivots, int * pCursor,
    void ** ppRootCache );
extern void Abc_ResubRootCacheStop( void * pRootCache );
extern int Abc_ResubIteratorNext( void * pIter, int ** ppArray,
    int * pnAttempt, int * pfExhausted, int * pfInvalid );
extern int Abc_ResubIteratorReadPivotProfile( void * pIter,
    long long * pProfile );
extern void Abc_ResubIteratorResumeStop( void * pIter, int * pCursor );

typedef struct Cec_TranTfoStats_t_ Cec_TranTfoStats_t;
struct Cec_TranTfoStats_t_
{
    long long nSeeds;
    long long nScanned;
    long long nEdges;
    long long nAdded;
    long long nTfi;              // routed TFI reservoir, before covered filtering
    long long nGlobal;           // additional global-earlier nodes
    long long nTfiNodes, nTfiEdges, nCutCosts, nCutExpands, nCutLeaves;
    abctime   timeCut, timeTfi;
    int       fLimit;
    abctime   Time;
};
typedef struct Cec_TranProf_t_ Cec_TranProf_t;
// Diagnostic-only snapshot accounting.  None of these fields participates in
// generation, candidate identity, proof, or commit decisions.
typedef struct Cec_TranDiagBucket_t_ {
    long long Roots, Started, Exhausted, Next, Raw, Valid, Positive;
    long long Nonpositive, Duplicate, Collapsed, Invalid, Accepted, Pivots;
    abctime EnumTime, BuildTime;
} Cec_TranDiagBucket_t;
typedef struct Cec_TranDiagGate_t_ {
    long long Count, Accepted, Nonpositive, Boundary, Rescued;
    abctime Time;
} Cec_TranDiagGate_t;
static int Cec_TranDiagGateBin( int n )
{
    return n <= 4 ? n : n <= 8 ? 5 : n <= 16 ? 6 : 7;
}
typedef struct Cec_TranDiagMffc_t_ {
    long long Calls, Next, Accepted;
    abctime EnumTime, BuildTime;
} Cec_TranDiagMffc_t;
typedef struct Cec_TranStrictCex_t_ Cec_TranStrictCex_t;
struct Cec_TranProf_t_
{
    Cec_TranStrictCex_t * pStrictCex; // borrowed, strict SEQ proof observer only
    void * pRelObserve;             // borrowed immutable-source obligation counters only
    void * pRelClosed;              // borrowed complete closed-bundle scope, Strict only
    void * pStrictTemporalDomain;   // owned immutable Strict RootPass search domain
    int fVerbose;
    int DiagPhase;
    int PreproofTrace, PreproofRound, PreproofWave, PreproofRoot;
    int StrictLocalDomainMode, StrictLocalDomainProfile;
    int StrictCutSize, StrictCutTrace;
    void * pStrictCutCache;         // owned immutable-pass cut boundaries only
    int OdcCutSize;
    void * pOdcCutCache;            // owned by one immutable ODC discovery round
    long long nCutCalls, nCutCosts, nCutExpands, nCutLeaves, nCutTfiNodes, nCutTfiEdges;
    abctime timeCutSetup, timeCutBuild, timeCutTfi;
    long long nLocalDomainCalls, nLocalDomainFirst, nLocalDomainCont;
    long long nLocalDomainTfi, nLocalDomainTfo, nLocalDomainGlobal;
    long long nLocalDomainCollected, nLocalDomainRankInput;
    long long nLocalDomainRanked, nLocalDomainPostB, nLocalDomainBound;
    abctime PreproofStart;
    Cec_TranDiagMffc_t DiagMffc[8];
    int DiagRootAvailable;
    Cec_TranDiagBucket_t DiagRoots[8];
    Cec_TranDiagGate_t DiagGates[8][8], DiagReject[6][8];
    abctime DiagIteratorTime, DiagDecodeTime, DiagExhaustTime;

    long long nExpCiHit, nExpCiMiss, nExpObsRoots, nExpObsConflict;
    long long nExpFullRoots, nExpFullConflict, nExpObsTotal, nExpObsUnique;
    long long nExpPruned;
    abctime timeExpObs, timeExpRankScore, timeExpRankCi;
    abctime timeExpZeroBuild, timeExpPositiveBuild;
    abctime timeExpZeroRank, timeExpPositiveRank;
    abctime timeTotal;
    abctime timeGain;
    abctime timeShadow;
    abctime timeCombSolve;
    abctime timeFreeCexSim;
    abctime timeRootDivPool;
    // Diagnostic sub-buckets nested inside timeRootDivPool.  They are not
    // added to the top-level time total because that would double count.
    abctime timeRootDivCollect;
    abctime timeRootDivRank;
    abctime timeRootDivRankMffcOneFirst;
    abctime timeRootDivRankMffcOneCont;
    abctime timeRootDivRankEligibleFirst;
    abctime timeRootDivRankEligibleCont;
    long long nRootDivRankMffcOneFirstCalls;
    long long nRootDivRankMffcOneContCalls;
    long long nRootDivRankEligibleFirstCalls;
    long long nRootDivRankEligibleContCalls;
    long long nRootPageRankReuseCalls, nRootPageRankReuseNodes;
    long long nRootPageRankReusePopcounts, nRootPageRankReusePoolNodes;
    long long nRootPageRankOwnerBytes;
    abctime timeRootPageRankReuse;
    abctime timeRootDivSelect;
    abctime timeRootDivHash;
    abctime timeRootDivTfo;
    // Rescue selection is nested in divisor discovery.  ISF total is a
    // disjoint top-level bucket; its remaining fields are nested diagnostics.
    abctime timeRootTfoCoreSelect;
    abctime timeRootTfoCoreValue;
    abctime timeRootIsf;
    abctime timeRootIsfCoreSelect;
    abctime timeRootIsfProjection;
    abctime timeRootKitSynthesis;
    abctime timeRootBdcSynthesis;
    long long nRootTfoCalls;
    long long nRootTfoSeeds;
    long long nRootTfoScanned;
    long long nRootTfoEdges;
    long long nRootTfoAdded;
    long long nRootTfoSelected;
    long long nRootTfoCoreRescueCalls;
    long long nRootTfoCoreRescueNoExtra;
    long long nRootTfoCoreRescueExact;
    long long nRootTfoCoreRescueRoots;
    long long nRootTfoCoreRescueNodes;
    long long nRootTfoCoreValueTrials;
    long long nRootTfoCoreValueExact;
    long long nRootTfoCoreValueChanged;
    long long nRootTfoCoreValueUnlocked;
    long long nRootKitCoreCalls;
    long long nRootKitCoreSeparated;
    long long nRootKitSynthesized;
    long long nRootKitAccepted;
    long long nRootKitSubmitted;
    long long nRootBdcCoreCalls;
    long long nRootBdcCoreSeparated;
    long long nRootBdcSynthesized;
    long long nRootBdcAccepted;
    long long nRootBdcSubmitted;
    long long nRootTfoLimitHits;
    int       nRootTfoAddedMax;
    abctime timeRootDepInit;
    abctime timeRootDepSearch;
    // Root-only redesign: the following top-level buckets are disjoint.
    abctime timeRootSimSig;
    abctime timeRootRefresh;
    // Diagnostic sub-buckets nested inside timeRootRefresh.
    abctime timeRootFrontDead;
    abctime timeRootPotentialRefresh;
    abctime timeRootFrontLoop;
    abctime timeRootFrontLoopFirst;
    abctime timeRootFrontLoopCont;
    abctime timeRootFrontSupport;
    abctime timeRootFrontGain;
    abctime timeRootFrontSort;
    long long nRootFrontPairScans;
    long long nRootFrontPairScansFirst;
    long long nRootFrontPairScansCont;
    long long nRootFrontMatched;
    int nRootFrontCalls;
    long long nRootPageMffcOneSkipped;
    abctime timeRootDirect;
    abctime timeRootDivCi;
    abctime timeRootResubInit;
    abctime timeRootResubEnumCanon;
    abctime timeRootTeach;
    abctime timeRootCbsGraph;
    abctime timeRootCbsScreen;
    abctime timeRootCbsSolve;
    abctime timeRootScorrGraph;
    abctime timeRootScorrBmc;
    abctime timeRootScorrIndSat;
    abctime timeRootScorrResim;
    abctime timeRootScorrOther;
    abctime timeRootPostSelect;
    abctime timeRootBundleDup;
    abctime timeRootCleanup;
    abctime timeRootExactAudit;
    Cec_ProfCor_t Corr;
    long long nRootBundleAndGain;
    long long nRootBundleRegGain;
    // Exact proof-origin phase-by-kind contribution.  Phase 0 is the initial
    // COMB pass and phase 1 contains later SEQ passes.  Proof-engine lane
    // (CBS/scorr) is tracked separately below.
    long long nCombConfUsed;
    int       nRootBundleCommits;
    int       nStageKindGenerated[2][3];
    int       nStageKindSubmitted[2][3];
    int       nStageKindProved[2][3];
    int       nStageKindSelected[2][3];
    int       nLaneKindSubmitted[2][3]; // CBS/scorr proof-engine lanes
    int       nLaneKindProved[2][3];
    int       nLaneKindSelected[2][3];
    long long nStageKindMarginalAndGain[2][3];
    long long nStageKindMarginalRegGain[2][3];
    int     nGainCalls;
    int     nHistoryTriedRemapped;   // tried entries retained across successful commits
    int     nHistoryTriedInvalidated;// tried entries invalidated in committed TFO
    int     nQueueTriedSkipped;      // regenerated exact candidates skipped by history
    int     nRootBatchCalls;    // two-stage proof batches in root scope
    int     nRootBatchMax;      // largest submitted relation batch
    int     nCombProved;        // combinationally proved candidates
    int     nCombDisproved;     // candidates with a combinational counterexample
    int     nCombUnknown;       // candidates not decided by CBS
    long long nCombCubesSkippedUnknown;// cube calls avoided after the first UNKNOWN
    int     nCombFreeCexStored; // valid CBS models added to the batch signature bank
    int     nCombFreeCexInvalid;// partial CBS models that failed scalar validation
    int     nCombUnknownEarly;  // candidates stopped immediately on the first UNKNOWN cube
    int     nCombNoModelCalls;  // solve calls skipping unused model extraction
    int     nRootResubIterInit;  // local iterators initialized per root/wave
    int     nRootResubIterNext;  // total Next calls, including final exhaustion
    int     nRootResubIterExhausted;// routes reaching their finite end
    int     nRootResubIterCapped;// non-terminal per-root q wave stops
    int     nRootResubIterDiscarded;// live iterators invalidated by a commit
    int     nRootResubIterLive;  // roots currently bound to shared workspace
    int     nRootResubIterLiveMax;
    int     nRootResubInvalid;   // generated recipes rejected by semantic audit
    long long nRootDivReservoirCalls;
    long long nRootDivReservoirNodes;
    int       nRootDivReservoirMax;
    long long nRootDivPoolNodes;
    int       nRootDivPoolMax;
    int       nRootDivPoolEmpty;
    long long nRootBuildMffcSum;
    int       nRootBuildMffcMax;
    long long nRootBuildMffcOneSkipped;
    long long nRootBuildCollapsedDirect;
    long long nRootBuildRejectNonPositive;
    long long nRootBuildRejectKnown;
    long long nRootBuildRejectDirect;
    long long nRootBuildRejectPage;
    long long nRootBuildAccepted;
    long long nSourceMacroPrepared, nSourceMacroAtoms;
    long long nSourceMacroTemplates, nSourceMacroWords, nSourceMacroOuterReject;
    long long nSourceMacroSetupWords;
    long long nSourceMacroMatches, nSourceMacroAccepted;
    long long nSourceMacroZero, nSourceMacroN, nSourceMacroNonpositive;
    long long nSourceMacroDuplicate;
    long long nSourceMacroReservoirIds, nSourceMacroReservoirLive, nSourceMacroReservoirPeak;
    long long nSourceMacroSignatureBytes, nSourceMacroSignatureLive, nSourceMacroSignaturePeak;
    abctime timeSourceMacro;
    long long nRootTeachCalls;
    long long nRootTeachSelections;
    long long nRootTeachWithCex;
    long long nRootTeachCexSelected;
    long long nRootTeachHypotheses;
    long long nRootTeachHypCovered;
    long long nRootBuildStageValid[6];
    long long nRootBuildStageAccepted[6];
    abctime   timeRootBuildStage[6];
    long long nRootBuildMffcCalls[CEC_TRAN_BUILD_MFFC_BINS];
    long long nRootBuildMffcNext[CEC_TRAN_BUILD_MFFC_BINS];
    long long nRootBuildMffcAccepted[CEC_TRAN_BUILD_MFFC_BINS];
    abctime   timeRootBuildMffc[CEC_TRAN_BUILD_MFFC_BINS];
    long long nOdcWindowRoots, nOdcWindowNodes, nOdcWindowEnds;
    long long nOdcWindowOverflow, nOdcWindowCareBits, nOdcWindowBits;
    long long nOdcCoreVariants, nOdcCarePoolChanged;
    long long nRootGreedyPivotAttempts;
    long long nRootMultiPathFingerprintDuplicates;
    long long nRootMultiPathAccepted;
    long long nRootMultiPathQSlots;
    int     nRootWaveDepCalls[64];
    int     nRootWaveRecipes[64];
    int     nRootWaveSubmitted[64];
    int     nRootWaveProved[64];
    int     nRootWaveSelected[64];
    abctime timeRootWaveConstruct[64];
    // ODC proof-only CONST predicates are never edit candidates or area gain.
    int     nOdcConstScanned, nOdcConstZero, nOdcConstOne;
    int     nOdcConstInjected, nOdcConstChecked;
    int     nOdcConstSurvived, nOdcConstWithdrawn, nOdcConstUnknown;
    int     nSeqCands;          // unresolved candidates sent to scorr
    int     nSeqSeeded;         // endpoint relations actually seeded into scorr classes
    int     nSeqProved;         // candidates proved only by scorr
    int     nSeqSplit;          // seeded relations split by the fixed point
    int     nSeqUnknown;        // surviving relations under an incomplete oracle
    int     nSeqRoots;          // distinct roots seeded into shared scorr
    int     nSeqClassMax;       // largest root proof class (root plus candidates)
    long long nSeqClassSum;     // total class members over seeded roots
    int     nSeqFixedRounds;    // completed fixed-point refinement rounds
    int     nHelperRetained;    // valid formal certificates kept as metadata
    int     nHelperInjected;    // helper relations materialized across waves
    int     nHelperInactive;    // retained relations skipped only when helpers are off
    int     nHelperDedup;       // exact canonical duplicates suppressed
    int     nHelperInvalidated; // retained certificates invalid on this snapshot
    int     nHelperClasses;     // source-root helper classes represented
    int     nHelperEndpoints;   // maximum unique endpoints in one injected set
    int     nHelperMaterialGates;// recipe gates materialized across batches
    int     nRootProofWaves;    // proof waves consumed on one snapshot
    int     nRootWaveContinues; // waves after the first without iterator rebuild
    int     nRootSrmNodesMax;   // maximum temporary batch node count
    int     nRootNewProved;     // newly discharged obligations
    int     nRootHistorySelected;// selected relations proved on an older snapshot
    int     nDirtyRootFreed;    // cached relation whose root is already free/used
    int     nDirtySupportFreed; // cached relation whose external support was freed
    int     nDirtyMffcChanged;  // still-legal relation with changed marginal MFFC
};

static double Cec_TranTimeSec( abctime Time )
{
    return 1.0 * Time / CLOCKS_PER_SEC;
}

// Opt-in, flushed observations of the immutable Strict pre-proof path.
// Counts are stage-local actual work, never inferred from AIGER metadata.
static void Cec_TranPreproofEvent( Cec_TranProf_t * pProf, Gia_Man_t * p,
    char const * pStage, int fEnd, int nItems, long long nWork )
{
    if ( !pProf->PreproofTrace ) return;
    Abc_Print( 1, "stran-root preproof: schema=2 stage=%s event=%s round=%d wave=%d root=%d objects=%d ands=%d cis=%d regs=%d items=%d work=%lld since-sec=%.6f\n",
        pStage, fEnd ? "END" : "BEGIN", pProf->PreproofRound,
        pProf->PreproofWave, pProf->PreproofRoot, Gia_ManObjNum(p),
        Gia_ManAndNum(p), Gia_ManCiNum(p), Gia_ManRegNum(p), nItems, nWork,
        Cec_TranTimeSec(Abc_Clock() - pProf->PreproofStart) );
    fflush( stdout );
}
