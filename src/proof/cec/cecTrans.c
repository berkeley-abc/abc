/**CFile****************************************************************

  FileName    [cecTrans.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential Direct root resubstitution.]

  Synopsis    [Candidate-and-prove sequential root replacement.]

  Description [The active algorithm replaces an AND root by a constant,
  earlier literal, or dependency recipe.  Root candidates are discovered and
  proved on an immutable GIA, selected under bundle interactions, and committed
  together.  Optional ODC processing proves preservation at the exits of a
  bounded fanout window.]

***********************************************************************/

#include "cecInt.h"
#include "aig/gia/giaAig.h"
#include "bool/bdc/bdc.h"
#include "bool/kit/kit.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include "proof/pdr/pdr.h"
#include "opt/drw/drwGia.h"
#include <stddef.h>
#include <limits.h>

ABC_NAMESPACE_IMPL_START

#include "cecTranInt.h"

void Cec_ManTranSetDefaultParams( Cec_ParTran_t * p )
{
    memset( p, 0, sizeof(Cec_ParTran_t) );
    p->nFrames     = 1;
    p->nBTLimit    = 100;
    p->nStepsMax   = -1;
    p->nStrictSteps = -2; p->nStrictWaves = -1;
    p->nInitialFrames = p->nInitialConflicts = -1;
    p->nWindowFrames = p->nWindowConflicts = -1;
    p->nWindowDivs = p->nWindowCandidates = -1;
    p->nWindowSteps = -2;
    p->nWindowCacheMiB = 256;
    p->nConstrMax  = 8;
    p->nConstrBaseMax = 16;
    p->nKitCoreMax = 0;
    p->fBdcPortfolio = 0;
    p->nDepNodesMax = 20;
    p->nSimWords   = 4;
    p->nSimFrames  = 8;
    p->nRootWaves  = 8;
    p->nRootConstrTop = 1;
    p->nRootProofBatch = 0;
    p->nStage5Paths = 0;
    p->nOdcProofMax = 64;
    p->nOdcFanoutRounds = 0;
    // Use the same per-obligation conflict budget for the combinational CBS
    // certificate lane and the sequential scorr oracle by default.  The two
    // budgets remain independently configurable through -b and -C.
    p->nCombBTLimit = 100;
    p->nFreeWords  = 2;
    p->nFreeCexMax = 64;
    p->nHardConfTotal = 1000000;
    p->fUseExisting = 1;
    p->fUseMffcDivs = 1;
    p->fUseTfoDivs = 0;
    p->fUseOdc = 0;
    p->fOdcStrict = 0;
    p->fOdcFanout = 0;
    p->fUseConstr  = 1;
    p->fUseCbsMultiLit = 1;
    // A round owns one immutable proof snapshot.  Every successful COMB/SEQ
    // selection is committed before the next snapshot is rediscovered.
    p->fUseFreeSim = 1;
    p->fUseHelpers = 1;
    p->fBuildOnly = 0;
}

// Route3 consumes the currently loaded sequential graph directly.  Its
// Strict uses 64 simulation frames, a ranked B16 divisor pool and q2 Build
// candidates per root, with at most three graph epochs. Its proof uses F1/C100;
// the following ODC stage uses the reviewed route1 policy on that actual
// Strict result.  No initial scorr or arbitrary-state COM pass is implicit.
void Cec_ManTranSetRoute3Params( Cec_ParTran_t * p, int fOdc )
{
    Cec_ManTranSetDefaultParams(p);
    p->fRoute3 = 1;
    // Strict uses the same per-query conflict cap as default &scorr.
    // Reviewed ODC retains its stage-local nWindowConflicts below.
    p->nFrames = 1; p->nBTLimit = 100; p->nStepsMax = -1;
    p->nDepNodesMax = 100; p->nConstrBaseMax = 16; p->nConstrMax = 0;
    p->nKitCoreMax = 8; p->fBdcPortfolio = 1;
    p->nSimWords = 4; p->nSimFrames = 64; p->fResetNested = 1;
    p->nRootConstrTop = 2; p->nRootProofBatch = 16;
    p->nRootWaves = 3; p->nStage5Paths = 0;
    p->fUseHelpers = 0;
    p->nExplore = 747118613;
    p->fUseTfoDivs = 1; p->nCombBTLimit = 100;
    if ( fOdc )
    {
        p->fUseOdc = p->fOdcFanout = 1;
        p->nSignatureGuide = 2;
        p->nWindowFrames = 1; p->nWindowConflicts = 100;
        p->nWindowDivs = 64; p->nWindowCandidates = 80;
        p->fWindowCache = p->fWindowFactor = 1;
        p->nOdcProofMax = 0; p->nOdcFanoutRounds = 4;
    }
}

static int Cec_TranReviewedOdc( Cec_ParTran_t const * p )
{
    return p->fRoute1 || p->fRoute3 || p->fStran2Guide;
}

#include "cecTranCex.h"
#include "cecTranSignatureDot.h"
#include "cecTranCandidate.h"
#include "cecTranRelationalObserve.h"
#include "cecTranRelationalClosed.h"
#include "cecTranProof.h"
#include "cecTranGain.h"
#include "cecTranCut.h"
#include "cecTranTfo.h"
#include "cecTranLocalDomain.h"
#include "cecTranSourceMacro.h"
#include "cecTranTemporalDomain.h"
#include "cecTranBuild.h"
#include "cecTranCommit.h"
#include "cecTranProfile.h"
#include "cecTranRootFirstPage.h"

static inline int Cec_TranRootCandBucket( int sz )
{
    if ( sz <= 4 )  return sz;
    if ( sz <= 8 )  return 5;
    if ( sz <= 16 ) return 6;
    if ( sz <= 32 ) return 7;
    if ( sz <= 64 ) return 8;
    return 9;
}

static Gia_Man_t * Cec_ManSequentialRootPass( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars, int iRound, int fCombOnly,
    Cec_TranCandVec_t * pHistory, Cec_TranPatDb_t * pSharedDb,
    int fRootBatch, Cec_TranStrictCex_t * pStrictCex )
{
    Cec_ParTran_t QualityPars;
    Cec_TranProf_t Prof = {0};
    Cec_TranRootFirstPage_t FirstPage;
    Cec_TranRelObserve_t RelObserve;
    Cec_TranRelClosed_t RelClosed;
    Cec_TranCandVec_t Known = {0}, RootCands = {0}, Page = {0};
    Cec_TranCandVec_t ProofCands = {0};
    Cec_TranCandVec_t BatchProved = {0}, Proved = {0}, Selected = {0};
    Cec_TranCandVec_t HistoryLive = {0}, Active = {0}, Carry = {0};
    Cec_TranRoot_t * pRoots;
    Cec_TranRootCursor_t * pCursors;
    Cec_TranSim_t * pSim, * pSource;
    Cec_TranPatDb_t * pDb;
    Cec_TranDepScratch_t Dep;
    Gia_Man_t * p = Cec_TranDupProduct( pGia );
    Gia_Obj_t * pObj;
    Vec_Int_t * vMffc = Vec_IntAlloc( 128 );
    Vec_Int_t * vSupport = Vec_IntAlloc( 32 );
    char * pMffc = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pSolved = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pCovered = ABC_CALLOC( char, Gia_ManObjNum(p) );
    char * pUsed = ABC_CALLOC( char, Gia_ManObjNum(p) );
    int nRoots = 0, r, i, nSelected = 0;
    int nWaves = 0, fSnapshotExhausted = 0;
    int fMicroBatch = pPars->nRootProofBatch > 0;
    int fCommitHorizonReached = 0, fFirstPageGateStop = 0;
    int nBuildAcceptedTotal = 0, nBuildAcceptedMax = 0;
    int nBuildHorizonRoots = 0;
    int nBuildEligibleRoots = 0, nBuildAtQRoots = 0;
    int nBuildExhaustedBeforeQRoots = 0, nBuildUnfinishedBelowQRoots = 0;
    int nBuildZeroAcceptedRoots = 0;
    int nFrontierRefreshes = 0, nFrontierRefreshReuses = 0;
    long long nFrontierCandidates = 0, nKnownCandidateScansAvoided = 0;
    int iPhase = fCombOnly ? 0 : 1;
    int nCandCalls = 0, nCandSum = 0, nCandMax = 0;
    int nCandHist[10] = {0};
    // Keep &stran/&stran2's COMB pass on its historical TFI-only baseline.
    // The ordinary-resub adapter opts into the reviewed legal shell; existing
    // command profiles cannot consume or reclassify its gains.
    int fUseTfoDivs = pPars->fUseTfoDivs &&
        (!fCombOnly || pPars->fUseCombTfoDivs);
    int nTfoMax = pPars->nConstrBaseMax;
    int fOwnDb = pSharedDb == NULL;
    int nAndBefore = Gia_ManAndNum( p );
    abctime clkTotal = Abc_Clock(), clk;
    // Gia_ManDup() does not copy the AIGER output partition.  Keep it on
    // every pass result so typed constraints cannot silently become POs.
    p->nConstrs = pGia->nConstrs;
    // Only the Strict Route3 collector changes. ODC and COM retain their paths.
    if ( pPars->fRoute3 && !fCombOnly )
    {
        Prof.StrictLocalDomainMode = Cec_TranLocalDomainRead();
        Prof.StrictCutSize = Cec_TranCutSizeRead(pPars, Prof.StrictLocalDomainMode);
        Prof.StrictCutTrace = pPars->fProfile && getenv("ABC_SRESUB_CUT_TRACE") &&
            !strcmp(getenv("ABC_SRESUB_CUT_TRACE"),"1");
        Prof.StrictLocalDomainProfile = 0;
        if ( Prof.StrictLocalDomainMode )
            fUseTfoDivs = Prof.StrictLocalDomainMode == 2;
    }
    if ( Abc_ResubQualityNoTruncation() )
    {
        QualityPars = *pPars;
        QualityPars.nConstrMax = QualityPars.nConstrBaseMax = 0;
        // q is a total-search horizon; j only paginates the same stream.
        // Preserve the caller's j so proof can run before full enumeration.
        QualityPars.nRootConstrTop = 0;
        pPars = &QualityPars;
        nTfoMax = 0;
    }
    FirstPage = Cec_TranRootFirstPageStart( Gia_ManObjNum(p),
        Cec_TranRootFirstPageApplicable(pPars, fCombOnly) &&
        Cec_TranStrictCexOption("ABC_STRAN_ROOT_FIRST_PAGE_GATE", 0, 1) );
    Prof.fVerbose = pPars->fVerbose;
    Prof.DiagPhase = iPhase;
    Prof.PreproofTrace = !fCombOnly && pPars->fProfile &&
        getenv("ABC_STRICT_PREPROOF_TRACE") && atoi(getenv("ABC_STRICT_PREPROOF_TRACE"));
    Prof.PreproofRound = iRound + 1;
    Prof.PreproofRoot = -1;
    Prof.PreproofStart = Abc_Clock();
    if ( Prof.StrictLocalDomainProfile )
        Cec_TranLocalDomainConfig( pPars, &Prof, fUseTfoDivs, nTfoMax );
    Prof.pStrictTemporalDomain = Cec_TranTemporalDomainStart(p,pPars,&Prof,fCombOnly);
    Cec_TranTemporalDomainConfig((Cec_TranTemporalDomain_t *)Prof.pStrictTemporalDomain,pPars,fUseTfoDivs);
    Cec_TranPreproofEvent( &Prof, p, "initialization", 0, 0, 0 );
    RelObserve=Cec_TranRelObserveStart(p,pPars->fRoute3 && !fCombOnly && Cec_TranRelObserveEnabled());
    Prof.pRelObserve=RelObserve.Source ? &RelObserve : NULL;
    RelClosed=Cec_TranRelClosedStart(p,pPars->fRoute3 && !fCombOnly && Cec_TranRelClosedEnabled());
    Prof.pRelClosed=RelClosed.Source ? &RelClosed : NULL;
    if(Prof.pRelClosed)CEC_CLOSED_REQUIRE(Cec_TranRelationalBackend(pPars)==2 && !pPars->fOdcProofScope);
    Prof.pStrictCex = !fCombOnly && pStrictCex && pStrictCex->Mode <= 3 ? pStrictCex : NULL;
    pDb = fOwnDb ? Cec_TranPatDbStart( p, 0 ) : pSharedDb;
    Gia_ManCreateRefs( p );
    if ( Prof.StrictCutSize )
    {
        clk = Abc_Clock();
        Gia_ManLevelNum(p);
        Prof.pStrictCutCache = Cec_TranCutCacheStart(p,Prof.StrictCutSize);
        Prof.timeCutSetup = Abc_Clock() - clk;
    }
    if ( fUseTfoDivs )
        Gia_ManStaticFanoutStart( p );
    Gia_ManForEachAnd( p, pObj, i )
        nRoots++;
    pRoots = ABC_ALLOC( Cec_TranRoot_t, nRoots );
    nRoots = 0;
    Gia_ManForEachAnd( p, pObj, i )
        pRoots[nRoots].iObj = i,
        pRoots[nRoots].nMffc = Gia_NodeMffcSize( p, pObj ),
        nRoots++;
    qsort( pRoots, nRoots, sizeof(Cec_TranRoot_t), Cec_TranRootCompare );
    pCursors = ABC_CALLOC( Cec_TranRootCursor_t, Gia_ManObjNum(p) );
    Prof.nRootPageRankOwnerBytes = (long long)Gia_ManObjNum(p) *
        (2 * sizeof(void *) + 2 * sizeof(int));
    if ( Cec_TranSourceMacroEnabled() && pPars->fRoute3 && !fCombOnly )
    {
        int Owner = Cec_TranSourceMacroNewOwner();
        for ( i = 0; i < Gia_ManObjNum(p); i++ )
            pCursors[i].nSourceMacroOwner = Owner;
        if ( Cec_TranSourceMacroTraceEnabled() )
        {
            printf("stran-source-macro {\"event\":\"source\",\"source_owner\":%d,\"phase\":%d,\"round\":%d,\"objects\":%d,\"ands\":%d,\"registers\":%d,\"root_batch\":%d}\n",
                Owner, !fCombOnly, iRound, Gia_ManObjNum(p), Gia_ManAndNum(p),
                Gia_ManRegNum(p), fRootBatch);
            if ( Owner == 1 ) Cec_TranSourceMacroTraceGraph(p, Owner);
        }
    }
    clk = Abc_Clock();
    pSource = fCombOnly && pPars->fCombFreeDiscovery ?
        Cec_TranSimStartFreeCiDiscovery( p, pPars ) :
        Cec_TranSimStart( p, pPars, pDb );
    if ( !fCombOnly && pStrictCex && pStrictCex->Mode >= 4 &&
         Cec_TranStrictCexActive(pStrictCex, p, pSource, pRoots, nRoots) )
    {
        Cec_TranPatDb_t * pTeach = Cec_TranStrictCexTeach(pStrictCex, p, pDb);
        if ( pTeach )
        {
            if ( fOwnDb ) Cec_TranPatDbStop(pDb);
            pDb = pTeach; fOwnDb = 1;
            fRootBatch = Vec_PtrSize(pDb->vCexes) > 64 * pPars->nSimWords;
            Cec_TranSimStop(pSource);
            pSource = Cec_TranSimStart(p, pPars, pDb);
        }
    }
    pSim = fRootBatch ? Cec_TranSimStartRootBatch( p,
        pPars->nSimWords, pPars->nSimFrames ) : pSource;
    // Free-state rows are hard construction constraints and can exclude true
    // reset invariants.  Route1 keeps only its reset-reachable teacher/CEX.
    if ( !fCombOnly && pPars->fRoute1 && pPars->fProfile )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root route1 discovery: hard-constraints=reset-reachable free-state-guide=0\n");
    Abc_ResubSetBothPolarities( !fCombOnly &&
        Cec_TranStrictCexOption("ABC_STRICT_BOTH_POLARITIES",
            pPars->fRoute3, 1) );

    Prof.timeRootSimSig += Abc_Clock() - clk;
    // The original source is immutable throughout this Strict snapshot.  Its
    // teacher/build views and the separate serial ODC entry do not own a cache.
    if ( !fCombOnly && pPars->fRoute3 ) Cec_TranSigDotConfigure(pSource);
    Abc_ResubPrepareManager( pSim->nSlots );
    Cec_TranDepScratchStart( &Dep, pSim->nSlots,
        pPars->nConstrBaseMax ? pPars->nConstrBaseMax : 64, 1 );
    if ( Vec_PtrSize(pDb->vCexes) )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran2 CEX trace signature: mode=%s source-words=%d build-words=%d frames=%d source-slots=%d build-slots=%d reachable-cex=%d cex-capacity=%d.\n",
            fRootBatch ? "root-batch" : "direct", pSource->nWords,
            pSim->nWords, pSource->nFrames, pSource->nSlots,
            pSim->nSlots, Vec_PtrSize(pDb->vCexes),
            64 * pPars->nSimWords );
    if ( fCombOnly && pPars->fCombFreeDiscovery )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "resub-comb discovery-signature: source=independent-PI/RO slots=%d words=%d width-dimensions=%d cbs-conflicts=%d.\n",
            pSource->nSlots, pSource->nWords, pSource->nFrames,
            pPars->nCombBTLimit );
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root: round=%d phase=%s snapshot=immutable scheduler=serial-root-iterator/all-candidates pivot-order=%s stage5-paths=%d stage5-path-order=eligible-primary/diagonal-extra/fallback-primary selection=%s candidates=%s q-build-per-root=%d proof-build-batch-per-root=%d helpers=%s divisor-route=%s existing=%s mffc-divisors=%s.\n",
        iRound + 1, fCombOnly ? "comb" : "seq",
        pPars->fUseSolvSched ? "residual-solvability" : "original",
        pPars->nStage5Paths <= 1 ? 1 : pPars->nStage5Paths,
        fMicroBatch ? "deferred-q-horizon-root-loss-gwmin" :
            "commit-wave-root-loss-gwmin",
        pPars->fBuildOnly ? "build-only" : "constant/existing/build",
        pPars->nRootConstrTop, pPars->nRootProofBatch,
        pPars->fUseHelpers ? "on" : "off",
        fUseTfoDivs ? "ranked-TFI+complete-fanin-TFO-shell" :
            "ranked-TFI-only",
        fUseTfoDivs ? "TFI+complete-fanin-TFO-pool" : "TFI-pool",
        pPars->fUseMffcDivs ? "on" : "off" );
    if ( fUseTfoDivs )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root complete-fanin TFO: mode=shell added-cap=%s%d membership=complete-depth-K-TFI topology=fanin-id<root.\n",
            Abc_ResubQualityNoTruncation() ? "unlimited/" :
                (nTfoMax ? "" : "auto/"), nTfoMax );
    if ( pPars->nKitCoreMax )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root Kit portfolio: core-max=%d proof-policy=unchanged exact-bundle-audit=on.\n",
            pPars->nKitCoreMax );
    if ( fMicroBatch )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root proof micro-batching: enabled=yes build-per-root-per-proof=%d commit-build-horizon-per-root=%d horizon-zero=%s commit-policy=deferred-until-horizon.\n",
            pPars->nRootProofBatch, pPars->nRootConstrTop,
            pPars->nRootConstrTop ? "bounded" : "iterator-exhaustion" );

    // Reuse exact relations formally proved on an earlier snapshot.  They are
    // inserted into Known before discovery, so the iterator advances past the
    // duplicate and spends q on genuinely new Build candidates.  Failed and
    // UNKNOWN relations are absent from this cache and are intentionally
    // retried after a simplifying commit.
    for ( i = 0; i < pHistory->nSize; i++ )
    {
        Cec_TranCand_t Cand = pHistory->pArray[i];
        int Gain;
        if ( !Cec_TranProofHistoryTopoValid(p, &Cand) ||
             !Cec_TranRecipeStructurallyValid(pSource, &Cand) ||
             !Cec_TranRecipeMatchesRoot(pSource, &Cand, NULL) )
        {
            Prof.nHistoryTriedInvalidated++;
            continue;
        }
        Cand.nProofStage = pHistory->pArray[i].nProofStage;
        assert(Cand.nProofStage == 1 || Cand.nProofStage == 2);
        Cand.nStatus = Cand.nProofStage == 1 ?
            CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
        Gain = Cec_TranQualityActualCost() ?
            Cec_TranQualityCostGainOne(p, &Cand, pCovered, pUsed, &Cand.nMffc) :
            Cec_TranCandDynamicGain( p, &Cand, pCovered, pUsed,
                pMffc, vMffc, vSupport );
        Cand.Gain = Gain;
        if ( !Cec_TranQualityActualCost() )
            Cand.nMffc = Vec_IntSize( vMffc );
        if ( !Cec_TranCandVecContains(&HistoryLive, &Cand) )
            Cec_TranCandVecPush( &HistoryLive, Cand );
        if ( !Cec_TranCandVecContains(&Known, &Cand) )
            Cec_TranCandVecPush( &Known, Cand );
        if ( !Cec_TranCandVecContains(&Proved, &Cand) )
            Cec_TranCandVecPush( &Proved, Cand );
        Prof.nQueueTriedSkipped++;
    }
    Prof.nHelperInvalidated = Prof.nHistoryTriedInvalidated;
    Prof.nHelperRetained = HistoryLive.nSize;
    Cec_TranRootFirstPagePrime( &FirstPage, pRoots, nRoots, &HistoryLive );
    Cec_TranPreproofEvent( &Prof, p, "initialization", 1, nRoots, pSim->nSlots );

    // A positive retained certificate may become profitable after an earlier
    // commit.  It is eligible for commit without being re-proved.
    if ( Proved.nSize && !fMicroBatch )
    {
        clk = Abc_Clock();
        nSelected = Cec_TranRootConsumeProved( p, &Proved,
            pCovered, pUsed, pSolved, pMffc, vMffc,
            vSupport, &Selected, &Prof );
        Prof.timeRootPostSelect += Abc_Clock() - clk;
    }

    // Each page visits roots that still have discovery work.  A root owns its
    // heavyweight
    // iterator manager only for Cec_TranRootDiscoverOne(); a later no-commit
    // wave restores the root's scalar cursor onto the shared manager.
    // The all-root union is still submitted without any global truncation.
    while ( Selected.nSize == 0 )
    {
        int iWave = nWaves, iProfWave = Abc_MinInt(iWave, 63);
        int nLiveRoots = 0, nHorizonRoots = 0, nFirstPageSkipped = 0;
        Prof.PreproofWave = iWave;
        Prof.PreproofRoot = -1;
        Cec_TranPreproofEvent( &Prof, p, "discovery-page", 0, nRoots, 0 );
        Cec_TranCandVecClear( &Page );
        Cec_TranCandVecClear( &ProofCands );
        Cec_TranCandVecClear( &BatchProved );
        Cec_TranCandVecClear( &Active );
        for ( r = 0; r < nRoots; r++ )
        {
            int nGot;
            if ( pRoots[r].nMffc <= 0 )
                continue;
            nLiveRoots++;
            if ( Cec_TranRootDiscoveryFinished(pPars, pRoots + r,
                    pCursors + pRoots[r].iObj, iWave) )
            {
                nHorizonRoots++;
                if ( iWave > 0 && pPars->fUseConstr &&
                     !Cec_TranRootBuildEligible(pRoots + r) )
                    Prof.nRootPageMffcOneSkipped++;
                continue;
            }
            if ( Cec_TranRootFirstPageSkip(&FirstPage, pRoots[r].iObj, iWave) )
            {
                ++nFirstPageSkipped;
                continue;
            }
            Cec_TranRootDiscoverOne( p, pSim, pSource, pDb, fRootBatch,
                pPars, pRoots + r,
                pCursors + pRoots[r].iObj, iWave,
                fUseTfoDivs, nTfoMax, 0,
                &Known, pSolved,
                pCovered, pUsed, pMffc, vMffc, &Dep, &Prof,
                &RootCands, NULL );
            nGot = RootCands.nSize;
            Cec_TranPreproofEvent( &Prof, p, "page-copy", 0, nGot, 0 );
            for ( i = 0; i < RootCands.nSize; i++ )
                Cec_TranCandVecPush( &Page, RootCands.pArray[i] );
            Cec_TranPreproofEvent( &Prof, p, "page-copy", 1, nGot, nGot );
            nCandCalls++;
            nCandSum += nGot;
            nCandMax = Abc_MaxInt( nCandMax, nGot );
            nCandHist[Cec_TranRootCandBucket(nGot)]++;
        }
        Prof.PreproofRoot = -1;
        Cec_TranPreproofEvent( &Prof, p, "discovery-page", 1, Page.nSize, nLiveRoots );
        // Cumulative snapshot before potentially long proof work.  Consumers
        // use CLOSED or the last PROGRESS for each scope, never sum snapshots.
        Cec_TranSigDotSnapshot(pSource->pSigDot, "PROGRESS");
        if ( Page.nSize == 0 )
        {
            // Even an empty first discovery page has a completed feedback
            // boundary; ordinary no-candidate termination remains unchanged.
            if ( iWave == 0 )
                Cec_TranRootFirstPageSeal( &FirstPage, pCursors, pPars->nRootConstrTop );
            fFirstPageGateStop = nFirstPageSkipped > 0;
            fCommitHorizonReached = fMicroBatch && nLiveRoots > 0 &&
                nHorizonRoots == nLiveRoots;
            fSnapshotExhausted = !fCommitHorizonReached && !fFirstPageGateStop;
            break;
        }
        nWaves++;
        Prof.nRootProofWaves++;
        Prof.nRootWaveContinues += nWaves > 1;
        Cec_TranPreproofEvent( &Prof, p, "known-copy", 0, Page.nSize, 0 );
        for ( i = 0; i < Page.nSize; i++ )
        {
            Cec_TranCandVecPush( &Known, Page.pArray[i] );
            Prof.nStageKindGenerated[iPhase][Page.pArray[i].nKind]++;
        }
        Cec_TranPreproofEvent( &Prof, p, "known-copy", 1, Known.nSize, Page.nSize );
        // In micro-batch mode only Page can contain fresh obligations.  Every
        // older Known entry is already PROVED or TRIED_SEQ, and scanning it
        // again cannot change the frontier on this immutable snapshot.  Keep
        // the legacy Known scan byte-for-byte when -j is disabled.
        {
            Cec_TranCandVec_t const * pFrontier =
                fMicroBatch ? &Page : &Known;
            // MFFCs and root order were computed at pass initialization.
            // Before selection the graph, covered and used sets never change.
            // A successful selection exits discovery, including in -j0 mode;
            // a new committed graph gets fresh initialization in the next pass.
            int fRefreshRoots = 0;
            nFrontierRefreshes += fRefreshRoots;
            nFrontierRefreshReuses += !fRefreshRoots;
            nFrontierCandidates += pFrontier->nSize;
            if ( fMicroBatch )
                nKnownCandidateScansAvoided += Known.nSize - Page.nSize;
            clk = Abc_Clock();
            Cec_TranPreproofEvent( &Prof, p, "frontier", 0, pFrontier->nSize, 0 );
            Cec_TranRootPrepareSeqFrontier( p, pRoots, nRoots, pFrontier,
                pCovered, pUsed, pMffc, vMffc, vSupport,
                fRefreshRoots, &ProofCands, &Prof );
            Prof.timeRootRefresh += Abc_Clock() - clk;
            Cec_TranPreproofEvent( &Prof, p, "frontier", 1, ProofCands.nSize, pFrontier->nSize );
        }
        Cec_TranPreproofEvent( &Prof, p, "status-lookup", 0, ProofCands.nSize, 0 );
        for ( i = 0; i < ProofCands.nSize; i++ )
        {
            int iKnown = Cec_TranCandVecFind( &Known,
                ProofCands.pArray + i );
            assert( iKnown >= 0 );
            Known.pArray[iKnown].nStatus = CEC_TRAN_STATE_TRIED_SEQ;
        }
        Cec_TranPreproofEvent( &Prof, p, "status-lookup", 1, ProofCands.nSize, ProofCands.nSize );
        Prof.nRootWaveSubmitted[iProfWave] += ProofCands.nSize;
        if ( !fCombOnly )
        {
            Cec_TranPreproofEvent( &Prof, p, "helpers", 0, ProofCands.nSize, HistoryLive.nSize );
            Cec_TranPrepareHelpers( p, &HistoryLive, &ProofCands,
                pPars->fUseHelpers, pPars->fVerbose, &Prof, &Active );
            Cec_TranPreproofEvent( &Prof, p, "helpers", 1, Active.nSize, HistoryLive.nSize );
        }
        if ( ProofCands.nSize )
        {
            int nNewProved = Cec_TranRootProvePortfolio( p, &Active,
                &ProofCands, pPars, &Prof, &BatchProved, fCombOnly,
                iPhase );
            Prof.nRootWaveProved[iProfWave] += nNewProved;
            Prof.nRootNewProved += nNewProved;
            for ( i = 0; i < BatchProved.nSize; i++ )
            {
                if ( !Cec_TranCandVecContains(&HistoryLive,
                        BatchProved.pArray + i) )
                    Cec_TranCandVecPush( &HistoryLive,
                        BatchProved.pArray[i] );
                if ( !Cec_TranCandVecContains(&Proved,
                        BatchProved.pArray + i) )
                    Cec_TranCandVecPush( &Proved,
                        BatchProved.pArray[i] );
            }
        }
        Cec_TranRootFirstPageObserve( &FirstPage, &ProofCands, &BatchProved, iWave );
        if ( iWave == 0 )
            Cec_TranRootFirstPageSeal( &FirstPage, pCursors, pPars->nRootConstrTop );
        if ( Proved.nSize && !fMicroBatch )
        {
            clk = Abc_Clock();
            nSelected = Cec_TranRootConsumeProved( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc,
                vSupport, &Selected, &Prof );
            Prof.timeRootPostSelect += Abc_Clock() - clk;
            Prof.nRootWaveSelected[iProfWave] += nSelected;
        }
        if ( fCombOnly && !fMicroBatch )
            break;
    }

    // In opt-in micro-batch mode every proof result remains metadata on the
    // immutable snapshot until the per-root q horizon (or iterator end) is
    // reached.  HistoryLive was already passed to every later SEQ proof as H,
    // so this is the first selection point, not a second proof phase.
    if ( fMicroBatch && Proved.nSize )
    {
        int iProfWave = Abc_MinInt(Abc_MaxInt(nWaves - 1, 0), 63);
        clk = Abc_Clock();
        if ( pPars->fRoute3 && !fCombOnly && !pPars->fOdcProofScope )
            nSelected = Cec_TranRootConsumeProvedScoped( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc,
                vSupport, &Selected, &Prof, nWaves );
        else
            nSelected = Cec_TranRootConsumeProved( p, &Proved,
                pCovered, pUsed, pSolved, pMffc, vMffc,
                vSupport, &Selected, &Prof );
        Prof.timeRootPostSelect += Abc_Clock() - clk;
        Prof.nRootWaveSelected[iProfWave] += nSelected;
    }

    for ( i = 0; i < Selected.nSize; i++ )
        Prof.nRootHistorySelected +=
            Cec_TranCandVecContains(pHistory, Selected.pArray + i);

    Prof.DiagRootAvailable = fMicroBatch;
    if ( fMicroBatch )
        for ( r = 0; r < nRoots; r++ )
            if ( pRoots[r].nMffc > 0 )
            {
                Cec_TranRootCursor_t const * pCursor =
                    pCursors + pRoots[r].iObj;
                nBuildAcceptedTotal += pCursor->nBuildAccepted;
                nBuildAcceptedMax = Abc_MaxInt( nBuildAcceptedMax,
                    pCursor->nBuildAccepted );
                nBuildHorizonRoots += pPars->fUseConstr &&
                    Cec_TranRootBuildHorizonReached(pPars, pCursor);
                if ( pPars->fUseConstr &&
                     Cec_TranRootBuildEligible(pRoots + r) )
                {
                    nBuildEligibleRoots++;
                    if ( pPars->fProfile )
                    {
                        // These frozen-parser buckets describe the native
                        // iterator alone. q/horizon totals above include the
                        // separate macro supplier; never invent native Next
                        // calls or a second native exhaustion to balance them.
                        Cec_TranSourceMacro_t const * s = pCursor->pSourceMacro;
                        int fMacroStarted = s && s->fNativeExhausted;
                        int NativeYield = fMacroStarted ? s->nNativeYield : pCursor->nBuildYield;
                        int NativeAccepted = fMacroStarted ? s->nNativeAccepted : pCursor->nBuildAccepted;
                        int NativeExhausted = fMacroStarted ? 1 : pCursor->fExhausted;
                        // Raw includes canonical direct results; Valid is the
                        // historical nonzero-gate yield. Keep not-started
                        // separate from an iterator that searched unsuccessfully.
                        int c = NativeAccepted > 0 ?
                            (pPars->nRootConstrTop > 0 &&
                             NativeAccepted >= pPars->nRootConstrTop ? 7 : 6) :
                            pCursor->fExpConflict && (pPars->nExplore & 4) ? 0 :
                            !pCursor->nPages ? 1 :
                            !pCursor->nDiagRaw ? 2 :
                            !pCursor->nDiagPositive ? 3 :
                            NativeYield == pCursor->nDiagPositive &&
                            !pCursor->nDiagCollapsed && !pCursor->nDiagInvalid ? 4 : 5;
                        Cec_TranDiagBucket_t * d = &Prof.DiagRoots[c];
                        d->Roots++;
                        d->Started += pCursor->nPages > 0;
                        d->Exhausted += NativeExhausted && pCursor->nPages > 0;
                        d->Next += pCursor->nDiagNext;
                        d->Raw += pCursor->nDiagRaw;
                        d->Valid += NativeYield;
                        d->Positive += pCursor->nDiagPositive;
                        d->Nonpositive += NativeYield - pCursor->nDiagPositive;
                        d->Duplicate += pCursor->nDiagPositive - NativeAccepted;
                        d->Collapsed += pCursor->nDiagCollapsed;
                        d->Invalid += pCursor->nDiagInvalid;
                        d->Accepted += NativeAccepted;
                        d->Pivots += pCursor->nDiagPivots;
                        d->EnumTime += pCursor->timeDiagEnum;
                        d->BuildTime += fMacroStarted ? s->timeNativeBuild : pCursor->timeExpBuild;
                    }
                    if ( pCursor->nBuildAccepted == 0 )
                    {
                        Prof.timeExpZeroBuild += pCursor->timeExpBuild;
                        Prof.timeExpZeroRank += pCursor->timeExpRank;
                    }
                    else
                    {
                        Prof.timeExpPositiveBuild += pCursor->timeExpBuild;
                        Prof.timeExpPositiveRank += pCursor->timeExpRank;
                    }
                    nBuildZeroAcceptedRoots +=
                        pCursor->nBuildAccepted == 0;
                    if ( pPars->nRootConstrTop > 0 &&
                         pCursor->nBuildAccepted >=
                            pPars->nRootConstrTop )
                        nBuildAtQRoots++;
                    else if ( pCursor->fExhausted )
                        nBuildExhaustedBeforeQRoots++;
                    else
                        nBuildUnfinishedBelowQRoots++;
                }
            }

    // Keep every still-live old certificate and every newly proved relation
    // that was not consumed by this commit.  Selected relations map to their
    // replacement and are deliberately removed from the carry set.
    for ( i = 0; i < HistoryLive.nSize; i++ )
        if ( !Cec_TranCandVecContains(&Selected, HistoryLive.pArray + i) )
            Cec_TranCandVecPush( &Carry, HistoryLive.pArray[i] );

    // All proof and discovery data refer to the one immutable snapshot.  Tear
    // them down before the sole bundle duplication stops that snapshot.
    Cec_TranCutCacheStop((Cec_TranCutCache_t *)Prof.pStrictCutCache);
    Prof.pStrictCutCache = NULL;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Cec_TranRootCursorStop( pCursors + i );
    Cec_TranTemporalDomainStop((Cec_TranTemporalDomain_t *)Prof.pStrictTemporalDomain);
    Prof.pStrictTemporalDomain = NULL;
    Cec_TranDepScratchStop( &Dep );
    Abc_ResubPrepareManager( 0 );
    Abc_ResubSetBothPolarities( 0 );
    if ( pSim != pSource )
        Cec_TranSimStop( pSim );
    Cec_TranSimStop( pSource );
    if ( fOwnDb )
        Cec_TranPatDbStop( pDb );
    pSim = NULL;
    pSource = NULL;
    if ( fUseTfoDivs )
        Gia_ManStaticFanoutStop( p );
    Cec_TranRelObserveStop(&RelObserve);Prof.pRelObserve=NULL;
    Cec_TranRelClosedStop(&RelClosed);Prof.pRelClosed=NULL;
    p = Cec_TranCommitSelectedRootOnly( p, &Selected, pPars, &Prof,
        &Carry, pHistory );
    Cec_TranRootFirstPageFinish( &FirstPage, &Selected, iRound,
        nAndBefore, Gia_ManAndNum(p) );
    Prof.nHelperInvalidated = Prof.nHistoryTriedInvalidated;
    Prof.nHelperRetained = Abc_MaxInt(
        Prof.nHelperRetained, pHistory->nSize );
    Prof.timeRootDivCi = Prof.timeRootDivPool;
    Prof.timeRootResubInit = Prof.timeRootDepInit;
    Prof.timeRootResubEnumCanon = Prof.timeRootDepSearch;
    Prof.timeRootCbsSolve = Prof.timeCombSolve;
    Prof.timeTotal = Abc_Clock() - clkTotal;
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root summary: round=%d phase=%s roots=%d selected=%d comb-proved=%d seq-proved=%d unique-proved=%d AND=%d->%d exact-gain=%lld.\n",
        iRound + 1, fCombOnly ? "comb" : "seq", nRoots,
        Selected.nSize, Prof.nCombProved, Prof.nSeqProved,
        Proved.nSize, nAndBefore, Gia_ManAndNum(p),
        Prof.nRootBundleAndGain );
    if ( fCombOnly && pPars->fUseCombTfoDivs )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "resub-comb active-CEX: random-words=%d retained=%d invalid=%d unknown=%d proof=free-PI/RO-root-equality.\n",
            pPars->nFreeWords, Prof.nCombFreeCexStored,
            Prof.nCombFreeCexInvalid, Prof.nCombUnknown );
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root wave portfolio: waves=%d continuations=%d new-proved=%d history-proved-selected=%d unique-proved=%d proof-calls=%d exhausted=%s.\n",
        Prof.nRootProofWaves, Prof.nRootWaveContinues,
        Prof.nRootNewProved, Prof.nRootHistorySelected, Proved.nSize,
        Prof.nRootBatchCalls,
        fSnapshotExhausted ? "yes" : "no" );
    if ( fMicroBatch )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root proof micro-batch summary: proof-waves=%d proof-calls=%d build-accepted-total=%d build-accepted-max-per-root=%d roots-at-horizon=%d stop=%s selected-after-stop=%d.\n",
            Prof.nRootProofWaves, Prof.nRootBatchCalls,
            nBuildAcceptedTotal, nBuildAcceptedMax, nBuildHorizonRoots,
            fFirstPageGateStop ? "first-page-gate" :
                (fCommitHorizonReached ? "commit-horizon" : "no-new-candidate"),
            Selected.nSize );
    if ( fMicroBatch )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root immutable frontier reuse: refresh-calls=%d refresh-reuses=%d page-candidates=%lld known-candidate-scans-avoided=%lld.\n",
            nFrontierRefreshes, nFrontierRefreshReuses,
            nFrontierCandidates, nKnownCandidateScansAvoided );
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root cross-wave proof reuse: generation-skipped=%d remapped=%d invalidated=%d retained=%d.\n",
        Prof.nQueueTriedSkipped, Prof.nHistoryTriedRemapped,
        Prof.nHistoryTriedInvalidated, pHistory->nSize );
    if ( fRootBatch )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran2 root-batch summary: root-signatures=%lld selector-calls=%lld roots-with-cex=%lld selected-cex-traces=%lld distinguishable-proxies=%lld covered-proxies=%lld selection-and-gather=%.6f sec.\n",
            Prof.nRootTeachCalls, Prof.nRootTeachSelections,
            Prof.nRootTeachWithCex,
            Prof.nRootTeachCexSelected, Prof.nRootTeachHypotheses,
            Prof.nRootTeachHypCovered, Cec_TranTimeSec(Prof.timeRootTeach) );
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root per-root candidates: discover-calls=%d total=%d max=%d avg=%.2f hist(0,1,2,3,4,5-8,9-16,17-32,33-64,65+)=%d,%d,%d,%d,%d,%d,%d,%d,%d,%d.\n",
        nCandCalls, nCandSum, nCandMax,
        nCandCalls ? (float)nCandSum / nCandCalls : 0.0f,
        nCandHist[0], nCandHist[1], nCandHist[2], nCandHist[3], nCandHist[4],
        nCandHist[5], nCandHist[6], nCandHist[7], nCandHist[8], nCandHist[9] );
    ABC_FREE( p->pRefs );
    Cec_TranCandVecStop( &Known );
    Cec_TranCandVecStop( &RootCands );
    Cec_TranCandVecStop( &Page );
    Cec_TranCandVecStop( &ProofCands );
    Cec_TranCandVecStop( &BatchProved );
    Cec_TranCandVecStop( &Proved );
    Cec_TranCandVecStop( &Selected );
    Cec_TranCandVecStop( &HistoryLive );
    Cec_TranCandVecStop( &Active );
    Cec_TranCandVecStop( &Carry );
    Vec_IntFree( vMffc );
    Vec_IntFree( vSupport );
    ABC_FREE( pMffc );
    ABC_FREE( pSolved );
    ABC_FREE( pCovered );
    ABC_FREE( pUsed );
    ABC_FREE( pRoots );
    ABC_FREE( pCursors );
    Cec_TranAssertTypedInterface( pGia, p );
    return p;
}

#include "cecTranOdc.h"

static Gia_Man_t * Cec_ManSequentialTransductionInt( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars, Cec_TranPatDb_t * pDb, int fRootBatch )
{
    Cec_ParTran_t PassPars, StrictPars = *pPars, * pGlobalPars = pPars;
    Cec_TranSeqBudget_t Budget = Cec_TranSeqBudgetStart(pPars->fRoute3 ? Cec_TranSeqBudgetRead() : -1);
    Cec_TranSeqBudget_t * PreviousBudget = Cec_TranSeqBudgetCurrent;
    Cec_TranCandVec_t ProofHistory = {0};
    Gia_Man_t * p = Cec_TranDupProduct( pGia );
    Gia_Man_t * pNext;
    int iRound, nAndInitial = Gia_ManAndNum(p);
    int nCombPasses = 0, nCombCommits = 0;
    int nSeqPasses = 0, nSeqCommits = 0;
    Cec_TranStrictCex_t * pStrictCex = Cec_TranStrictCexStart( pGia, pPars );
    StrictPars.fOdcProofScope = 0;
    if ( Budget.Milliseconds >= 0 )
    {
        if ( Budget.Milliseconds > 0 && Cec_TranRelationalBackend(&StrictPars) != 2 )
        {
            Abc_Print(-1, "Finite sresub SEQ budget requires the lazy-basis backend (Route3 default or ABC_STRAN_RELATIONAL_BASIS=2)\n");
            exit(2);
        }
        if ( Budget.Milliseconds > 0 &&
             (Cec_TranFrozenCnfProbeOption("ABC_STRAN_FROZEN_CNF_SOLVER_ORACLE") ||
              Cec_TranFrozenCnfProbeOption("ABC_STRAN_FROZEN_CNF_QUOTIENT_PROBE")) )
        {
            Abc_Print(-1, "Finite sresub SEQ budget cannot run an unbounded CNF diagnostic oracle/probe\n");
            exit(2);
        }
        Cec_TranSeqBudgetCurrent = &Budget;
    }
    else Cec_TranSeqBudgetCurrent = NULL;
    if ( StrictPars.nStrictSteps >= -1 ) StrictPars.nStepsMax = StrictPars.nStrictSteps;
    if ( StrictPars.nStrictWaves >= 0 ) StrictPars.nRootWaves = StrictPars.nStrictWaves;
    if ( Abc_ResubQualityNoTruncation() )
    {
        StrictPars.nConstrMax = StrictPars.nConstrBaseMax = 0;
        StrictPars.nRootConstrTop = 0;
        StrictPars.nRootWaves = 0;
    }
    pPars = &StrictPars;
    if ( pPars->fRoute3 )
    {
        // Validate option combinations even when diagnostics are disabled.
        int LocalMode = Cec_TranLocalDomainRead();
        int ProofMode = Cec_TranRelChunkMode(pPars);
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub proof config: schema=1 strict-seq-C=%d odc=%d odc-window-C=%d local-domain=%d proof-mode=%d seq-wall-budget-ms=%d cbs-C=%d\n",
            pPars->nBTLimit, pGlobalPars->fUseOdc,
            pGlobalPars->nWindowConflicts >= 0 ? pGlobalPars->nWindowConflicts : pGlobalPars->nBTLimit,
            LocalMode, ProofMode, Budget.Milliseconds, pPars->nCombBTLimit);
    }
    if ( pPars->fRoute3 )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub Strict teacher config: active-cex=%d both-polarities=%d initial-scorr-cex=not-applicable.\n",
            pStrictCex ? pStrictCex->Mode : 0,
            Cec_TranStrictCexOption("ABC_STRICT_BOTH_POLARITIES", 1, 1) );
    if ( Abc_ResubQualityNoTruncation() || Cec_TranQualityActualCost() )
        Abc_Print(1, "stran-quality options: no-truncation=%d actual-cost=%d N=%d T=%d D=%d j=%d; finite grammar, unchanged proof/commit.\n",
            Abc_ResubQualityNoTruncation(), Cec_TranQualityActualCost(),
            pPars->nDepNodesMax, pPars->nKitCoreMax, pPars->fBdcPortfolio,
            pPars->nRootProofBatch);
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-strict options: S=%d w=%d.\n",pPars->nStepsMax,pPars->nRootWaves);
    // Run arbitrary-state combinational proof exactly once on the initial
    // graph.  COM owns a fixed q=4 frontier, ignores the SEQ proof micro-batch
    // control, and therefore reaches selection after one proof batch.  It then
    // drains every profitable proved certificate through as many conflict-free
    // commit waves as needed.  Opportunities exposed later belong to SEQ.
    if ( !pPars->fRoute3 && !pPars->fRoute1 && !pPars->fSeqOnly )
    {
        int nBefore = Gia_ManAndNum( p );
        int nAfterFirst, nAfter, nClosureBatches = 0;
        PassPars = *pPars;
        PassPars.nRootWaves = 1;
        PassPars.nRootConstrTop = CEC_TRAN_COMB_BUILD_Q;
        PassPars.nRootProofBatch = Abc_ResubQualityNoTruncation() ?
                pPars->nRootProofBatch : 0;
        pNext = Cec_ManSequentialRootPass( p, &PassPars,
            0, 1, &ProofHistory, pDb, fRootBatch, NULL );
        Gia_ManStop( p );
        p = pNext;
        nAfterFirst = Gia_ManAndNum( p );
        p = Cec_TranDrainProvedCommits( p, pPars, &ProofHistory,
            0, 0, &nClosureBatches );
        nAfter = Gia_ManAndNum( p );
        nCombPasses = 1;
        nCombCommits = (nAfterFirst < nBefore) + nClosureBatches;
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root initial commit closure: phase=comb batches=%d AND=%d->%d gain=%d.\n",
            nCombCommits, nBefore, nAfter, nBefore - nAfter );
    }
    else if ( pPars->fRoute3 )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub boundary: input=current-graph initial-scorr=0 comb-pass=0 strict-proof=relational reset-sampling=reachable-block8.\n" );
    else
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran2 seq-only boundary: input=current-graph initial-scorr=0 comb-pass=0 initial-scorr-cex=not-imported strict-proof=legacy.\n" );
    if ( pPars->fRoute3 && !Cec_TranTemporalDomainEnabled() )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub candidate domain: global-earlier=%d no-routing=%d rank-tie=support-cardinality scope=Strict.\n",
            !Cec_TranLocalDomainRead(), !Cec_TranLocalDomainRead() );
    if ( pPars->fRoute3 )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub typed-boundary: stage=input bad=%d constraints=%d po=%d regs=%d.\n",
            Gia_ManPoNum(p) - Gia_ManConstrNum(p), Gia_ManConstrNum(p),
            Gia_ManPoNum(p), Gia_ManRegNum(p) );

    // Every later epoch is sequential.  It may consume several no-commit
    // q-waves on one immutable proof snapshot.  Once it proves a profitable
    // pool, the pool is drained to a commit fixed point before any candidate
    // generation/proof state is rebuilt.  With -w 0, strict AND-count descent
    // across proof epochs is the termination measure.
    for ( iRound = 0; pPars->nRootWaves == 0 ||
         iRound < pPars->nRootWaves; iRound++ )
    {
        int nBefore, nAfterFirst, nAfter, nClosureBatches = 0;
        nBefore = Gia_ManAndNum( p );
        PassPars = *pPars;
        PassPars.nRootWaves = 1;
        {
        Cec_TranPatDb_t * pTeach = Cec_TranStrictCexTeach( pStrictCex, p, pDb );
        pNext = Cec_ManSequentialRootPass( p, &PassPars,
            iRound, 0, &ProofHistory, pTeach ? pTeach : pDb,
            pTeach ? Vec_PtrSize(pTeach->vCexes) > 64 * pPars->nSimWords : fRootBatch,
            pStrictCex );
        if ( pTeach ) Cec_TranPatDbStop( pTeach );
        if ( pPars->fVerbose || getenv("ABC_STRICT_CEX_MODE") )
            Cec_TranStrictCexPrint( pStrictCex, iRound + 1 );
        }
        Gia_ManStop( p );
        p = pNext;
        nAfterFirst = Gia_ManAndNum( p );
        p = Cec_TranDrainProvedCommits( p, pPars, &ProofHistory,
            iRound, 1, &nClosureBatches );
        nAfter = Gia_ManAndNum( p );
        nSeqPasses++;
        nSeqCommits += (nAfterFirst < nBefore) + nClosureBatches;
        CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root epoch commit closure: epoch=%d phase=seq batches=%d AND=%d->%d gain=%d.\n",
            iRound + 1, (nAfterFirst < nBefore) + nClosureBatches,
            nBefore, nAfter, nBefore - nAfter );
        if ( nAfter >= nBefore )
            break;
    }
    CEC_TRAN_VERBOSE( pPars->fVerbose, "stran-root epochs summary: configured=%d completed=%d comb-epochs=%d comb-batches=%d seq-epochs=%d seq-batches=%d AND=%d->%d gain=%d.\n",
        pPars->nRootWaves, nSeqPasses, nCombPasses, nCombCommits,
        nSeqPasses, nSeqCommits, nAndInitial, Gia_ManAndNum(p),
        nAndInitial - Gia_ManAndNum(p) );
    Cec_TranCandVecStop( &ProofHistory );
    Cec_TranStrictCexStop( pStrictCex );
    if ( Budget.Milliseconds >= 0 ) Cec_TranSeqBudgetPrint(&Budget);
    Cec_TranSeqBudgetCurrent = PreviousBudget;
    pPars = pGlobalPars;
    Cec_TranAssertTypedInterface( pGia, p );
    if ( pPars->fRoute3 )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub typed-boundary: stage=strict bad=%d constraints=%d po=%d regs=%d.\n",
            Gia_ManPoNum(p) - Gia_ManConstrNum(p), Gia_ManConstrNum(p),
            Gia_ManPoNum(p), Gia_ManRegNum(p) );
    if ( pPars->fUseOdc )
    {
        if ( pPars->fRoute3 )
            CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub boundary: strict-output-and=%d next=reviewed-odc.\n", Gia_ManAndNum(p) );
        p = Cec_TranRunOdcSerial( p, pPars, pDb );
        Cec_TranAssertTypedInterface( pGia, p );
        if ( pPars->fRoute3 )
            CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub typed-boundary: stage=odc bad=%d constraints=%d po=%d regs=%d.\n",
                Gia_ManPoNum(p) - Gia_ManConstrNum(p), Gia_ManConstrNum(p),
                Gia_ManPoNum(p), Gia_ManRegNum(p) );
    }
    Cec_TranAssertTypedInterface( pGia, p );
    if ( pPars->fRoute3 )
        CEC_TRAN_VERBOSE( pPars->fVerbose, "sresub typed-boundary: stage=output bad=%d constraints=%d po=%d regs=%d.\n",
            Gia_ManPoNum(p) - Gia_ManConstrNum(p), Gia_ManConstrNum(p),
            Gia_ManPoNum(p), Gia_ManRegNum(p) );
    CEC_TRAN_VERBOSE( pPars->fVerbose, "%s: AND=%d->%d gain=%d.\n",
        pPars->fRoute3 ? "sresub" : "stran", nAndInitial,
        Gia_ManAndNum(p), nAndInitial - Gia_ManAndNum(p) );
    return p;
}

Gia_Man_t * Cec_ManSequentialTransduction( Gia_Man_t * pGia,
    Cec_ParTran_t * pPars )
{
    if ( pPars->fRoute3 )
    {
        int Local = Cec_TranLocalDomainParse(getenv("ABC_SRESUB_LOCAL_DOMAIN"));
        int Temporal = Cec_TranTemporalDomainParse(getenv("ABC_STRAN_STRICT_TEMPORAL_DOMAIN"));
        int OdcFrames = pPars->nWindowFrames >= 0 ? pPars->nWindowFrames : pPars->nFrames;
        if ( !Cec_TranRelFramesSupported(pGia, pPars->nFrames) ||
             (pPars->fUseOdc && !Cec_TranRelFramesSupported(pGia, OdcFrames)) )
        {
            Abc_Print(-1, "&sresub: induction depth exceeds the supported graph unrolling size.\n");
            return NULL;
        }
        if ( pPars->fUseOdc && pPars->nSignatureGuide &&
             (Cec_TranStrictCexOption("ABC_CEX_MODE", 2, 3) != 2 ||
              Cec_TranStrictCexOption("ABC_CEX_COMPRESS", 4, 6) != 4) )
        {
            Abc_Print(-1, "&sresub: ODC signature guide requires ABC_CEX_MODE=2 and ABC_CEX_COMPRESS=4.\n");
            return NULL;
        }
        if ( Local < 0 || Temporal < 0 || (Temporal && Local != 0) )
        {
            Abc_Print(-1, "&sresub: ABC_SRESUB_LOCAL_DOMAIN must be 0, 1 or 2; "
                "ABC_STRAN_STRICT_TEMPORAL_DOMAIN must be 0 or 1 and requires local domain 0 when enabled.\n");
            return NULL;
        }
    }
    // Default behavior still rejects this pair before any graph copy/search.
    // The explicit B32 Strict experiment captures the complete collection-ID
    // stream before rank compaction; it does not expand macro's native scope.
    if ( pPars->fRoute3 && Cec_TranRankBoundMode() && Cec_TranSourceMacroEnabled() &&
         !(Cec_TranSourceMacroPreboundEnabled() &&
           Cec_TranSourceMacroPreboundScope(pPars, 0)) )
    {
        fprintf( stderr, "stran-option-conflict: ABC_STRICT_RANK_BOUND=%d cannot be combined with ABC_STRAN_SOURCE_MACRO=1: rank-bound prunes the pre-B reservoir required by source macro. Set ABC_STRAN_SOURCE_MACRO=0 or ABC_STRICT_RANK_BOUND=0.\n",
            Cec_TranRankBoundMode() );
        exit(2);
    }
    return Cec_ManSequentialTransductionInt( pGia, pPars, NULL, 0 );
}

#undef CEC_TRAN_VERBOSE

ABC_NAMESPACE_IMPL_END
