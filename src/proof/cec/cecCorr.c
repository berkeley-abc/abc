/**CFile****************************************************************

  FileName    [cecCorr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Latch/signal correspondence computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCorr.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

// A correspondence call may contain many BMC/induction SRMs, and every SRM
// may contain many SAT outputs.  These counters deliberately span all of
// them.  The existing -C limit remains per output; nConfTotal is an optional
// deterministic cap on the exact conflicts/backtracks consumed by the whole
// call.  &scorr leaves it at zero, so its legacy behavior is unchanged.
ABC_INT64_T Cec_ScorrConfLimit = 0;
ABC_INT64_T Cec_ScorrConfUsed  = 0;
int         Cec_ScorrConfStop  = 0;

static inline int Cec_ParCorShouldStop( Cec_ParCor_t * pPars )
{
    if ( pPars && pPars->nConfTotal > 0 && Cec_ScorrConfStop )
        return 1;
    if ( pPars == NULL || pPars->pFunc == NULL )
        return 0;
    return ((int (*)(void *))pPars->pFunc)( pPars->pData );
}


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Shared with cecCorrIncr.c (declared in cecInt.h).
extern void Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix );
extern int  Gia_ManCorrSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix );

////////////////////////////////////////////////////////////////////////
///        &scorr FINE-GRAINED PROFILING (enabled by -w)              ///
////////////////////////////////////////////////////////////////////////

// Per-proof SAT counters (see cecInt.h). Written by Cbs/Tas/Cec miter solvers.
int     Cec_ScorrProfOn    = 0;
int     Cec_ScorrProfCalls = 0;
abctime Cec_ScorrProfSetup = 0;
abctime Cec_ScorrProfSolve = 0;
abctime Cec_ScorrProfMax   = 0;

// Sim-phase split, filled inside Cec_ManResimulateCounterExamples (ns).
static abctime Cec_ScorrProfSimRemap = 0; // O(N) remapping + value-ref setup
static abctime Cec_ScorrProfSimRun   = 0; // actual bit-parallel resimulation
// Incremental local-sim cone measurement (counts, not times).
static int     Cec_ScorrProfIncrSrc   = 0; // # batches handled by local TFO sim
static int     Cec_ScorrProfIncrFull  = 0; // # batches that fell back to full sweep
static int     Cec_ScorrProfIncrTrunc = 0; // # local batches with optional TFO truncated
static int     Cec_ScorrProfIncrRollback = 0; // # diagnosis transactions rolled back
static int     Cec_ScorrProfIncrRollbackObjs = 0; // # class entries restored
static int     Cec_ScorrProfIncrCoverageMiss = 0; // # unexplained packed CEX lanes
static int     Cec_ScorrProfIncrFallbackPre = 0; // fallback before class mutation
static int     Cec_ScorrProfIncrFallbackProcess = 0; // diagnosis budget fallback
static int     Cec_ScorrProfIncrFallbackCoverage = 0; // diagnosis coverage fallback
static int     Cec_ScorrProfIncrFallbackCex = 0; // oversized packed CEX batch
static int     Cec_ScorrProfIncrFallbackBypass = 0; // repeated-fallback circuit breaker
static int     Cec_ScorrProfIncrTruncCone = 0; // optional TFO structural truncation
static int     Cec_ScorrProfIncrTruncEval = 0; // optional TFO evaluation truncation
static int     Cec_ScorrProfIncrBatchCex = 0; // total real CEX records across batches
static int     Cec_ScorrProfIncrBatchCexMax = 0; // largest packed-batch CEX count
static int     Cec_ScorrProfIncrDeferred = 0; // fixed-frontier splits left for later rounds
static int     Cec_ScorrProfIncrDirty = 0; // largest dirty cone across the call
static int     Cec_ScorrProfIncrConeKeys = 0; // active/class cone keys used by event resim
static int     Cec_ScorrProfIncrKeys  = 0; // nFrames * nObjs (cone-size denominator)
static abctime Cec_ScorrProfIncrTry = 0; // all incremental probes
static abctime Cec_ScorrProfIncrTryLocal = 0; // probes completed locally
static abctime Cec_ScorrProfIncrTryFallback = 0; // probes followed by full simulation
static abctime Cec_ScorrProfIncrDiagShape = 0; // dry-run TFI/shape admission
static abctime Cec_ScorrProfIncrDiagCollect = 0; // lane-aware TFI diagnosis
static abctime Cec_ScorrProfIncrDiagEval = 0; // diagnosis evaluation shape
static abctime Cec_ScorrProfIncrDiagSim = 0; // diagnosis value evaluation/refinement
static abctime Cec_ScorrProfIncrTfoBuild = 0; // split-driven TFO construction
static abctime Cec_ScorrProfIncrTfoSim = 0; // TFO value evaluation/refinement
static abctime Cec_ScorrProfIncrTxn = 0; // transaction begin/commit/rollback
static abctime Cec_ScorrProfIncrFullRun = 0; // full sweeps after local rejection/bypass
static int     Cec_ScorrProfEventLocal = 0;
static int     Cec_ScorrProfEventFallback = 0;
static int     Cec_ScorrProfEventPopsMax = 0;
static int     Cec_ScorrProfEventEdgesMax = 0;
static int     Cec_ScorrProfEventInputVarsMax = 0;
static int     Cec_ScorrProfEventInputWordsMax = 0;
static int     Cec_ScorrProfEventFallbackWork = 0;
static int     Cec_ScorrProfEventFallbackTime = 0;
static int     Cec_ScorrProfIncrAdaptLocal = 0;
static int     Cec_ScorrProfIncrAdaptFail = 0;
static int     Cec_ScorrProfIncrAdaptTrips = 0;
static int     Cec_ScorrProfIncrAdaptCooldown = 0;
static abctime Cec_ScorrProfEventLoad = 0;
static abctime Cec_ScorrProfEventProp = 0;
static abctime Cec_ScorrProfEventRefine = 0;
static abctime Cec_ScorrProfEventRollback = 0;
static abctime Cec_ScorrProfEventInit = 0;

// One iteration's wall-clock breakdown; all fields are nanoseconds.
typedef struct Cec_ScorrProf_t_ Cec_ScorrProf_t;
struct Cec_ScorrProf_t_
{
    abctime tWall;                              // whole iteration
    abctime tSeed, tNext, tTfo, tCnt;           // IFO sub-phases
    abctime tSnap;                              // class-state snapshot
    abctime tSrm;                               // SRM (re)construction
    abctime tSat, tSatSetup, tSatSolve, tSatMax;// miter solving
    abctime tSim, tSimRemap, tSimRun;           // counter-example resimulation
    abctime tChk;                               // Gia_ManCheckRefinements
    abctime tStats;                             // Cec_ManRefinedClassPrintStats
    int     nSatCalls;                          // # of per-PO solve calls
    int     nIterations;                        // iterations accumulated in a summary
    // CEX-store classification (set when vCexStore non-empty).
    // R = real SAT CEX (nLits > 0); T = trivial SAT (nLits == 0); F = timeout/fail (nLits == -1).
    int     nCexReal, nCexTriv, nCexFail;
    // Did we actually invoke Cec_ManResimulateCounterExamples this iter? (0 or 1)
    int     nSimCalls;
    // # of pairs forced split this iter because SAT returned trivial (nLits==0).
    // Resim cannot break those (no literals), so we directly demote them.
    int     nTrivSplits;
    // # of real SAT pairs still merged after counter-example resimulation.
    int     nCexPending;
    // Incremental local-sim stats for this resim call (only under -I):
    //   nIncrSrc   = #batches handled by local TFO sim
    //   nIncrFull  = #batches that fell back to the full sweep (cone too wide)
    //   nIncrDirty = largest dirty cone seen across the call's batches
    //   nIncrConeKeys = active/class cone keys used by event resim
    //   nIncrKeys  = nFrames*nObjs (the cone-size denominator)
    int     nIncrSrc, nIncrFull, nIncrTrunc, nIncrDirty, nIncrConeKeys, nIncrKeys;
    int     nIncrRollback, nIncrRollbackObjs, nIncrCoverageMiss;
    int     nIncrFallbackPre, nIncrFallbackProcess, nIncrFallbackCoverage;
    int     nIncrFallbackCex, nIncrFallbackBypass;
    int     nIncrTruncCone, nIncrTruncEval;
    int     nIncrBatchCex, nIncrBatchCexMax, nIncrDeferred;
    abctime tIncrTry, tIncrTryLocal, tIncrTryFallback, tIncrFullRun;
    abctime tIncrDiagShape, tIncrDiagCollect, tIncrDiagEval, tIncrDiagSim;
    abctime tIncrTfoBuild, tIncrTfoSim, tIncrTxn;
    int     nEventLocal, nEventFallback, nEventPopsMax, nEventEdgesMax;
    int     nEventInputVarsMax, nEventInputWordsMax;
    int     nEventFallbackWork, nEventFallbackTime;
    int     nIncrAdaptLocal, nIncrAdaptFail, nIncrAdaptTrips, nIncrAdaptCooldown;
    abctime tEventLoad, tEventProp, tEventRefine, tEventRollback, tEventInit;
    // Lit-count deltas around the two refinement stages.
    //   dSimLits = #pairs broken by the sim call (lits before sim - lits after sim).
    //   dChkLits = #pairs broken by Gia_ManCheckRefinements (lits after sim - lits after chk).
    // Lit-count = Gia_ManEquivCountLitsAll(pAig).  Captured only when -w (Cec_ScorrProfOn).
    int     dSimLits, dChkLits;
};

// Accumulate one iteration's profile into a running total.
static inline void Cec_ScorrProfAdd( Cec_ScorrProf_t * pT, Cec_ScorrProf_t * pI )
{
    pT->tWall+=pI->tWall; pT->tSeed+=pI->tSeed; pT->tNext+=pI->tNext;
    pT->tTfo+=pI->tTfo;   pT->tCnt+=pI->tCnt;   pT->tSnap+=pI->tSnap;
    pT->tSrm+=pI->tSrm;   pT->tSat+=pI->tSat;   pT->tSatSetup+=pI->tSatSetup;
    pT->tSatSolve+=pI->tSatSolve; pT->tSim+=pI->tSim; pT->tSimRemap+=pI->tSimRemap;
    pT->tSimRun+=pI->tSimRun; pT->tChk+=pI->tChk; pT->tStats+=pI->tStats;
    pT->nSatCalls+=pI->nSatCalls;
    pT->nIterations++;
    pT->nCexReal+=pI->nCexReal; pT->nCexTriv+=pI->nCexTriv; pT->nCexFail+=pI->nCexFail;
    pT->nSimCalls+=pI->nSimCalls; pT->nTrivSplits+=pI->nTrivSplits;
    pT->nCexPending+=pI->nCexPending;
    pT->dSimLits+=pI->dSimLits; pT->dChkLits+=pI->dChkLits;
    // local/full batch counts accumulate; dirty is a max; keys is constant
    pT->nIncrSrc+=pI->nIncrSrc; pT->nIncrFull+=pI->nIncrFull;
    pT->nIncrTrunc+=pI->nIncrTrunc;
    pT->nIncrRollback+=pI->nIncrRollback;
    pT->nIncrRollbackObjs+=pI->nIncrRollbackObjs;
    pT->nIncrCoverageMiss+=pI->nIncrCoverageMiss;
    pT->nIncrFallbackPre+=pI->nIncrFallbackPre;
    pT->nIncrFallbackProcess+=pI->nIncrFallbackProcess;
    pT->nIncrFallbackCoverage+=pI->nIncrFallbackCoverage;
    pT->nIncrFallbackCex+=pI->nIncrFallbackCex;
    pT->nIncrFallbackBypass+=pI->nIncrFallbackBypass;
    pT->nIncrTruncCone+=pI->nIncrTruncCone;
    pT->nIncrTruncEval+=pI->nIncrTruncEval;
    pT->nIncrBatchCex+=pI->nIncrBatchCex;
    pT->nIncrDeferred+=pI->nIncrDeferred;
    pT->tIncrTry+=pI->tIncrTry;
    pT->tIncrTryLocal+=pI->tIncrTryLocal;
    pT->tIncrTryFallback+=pI->tIncrTryFallback;
    pT->tIncrFullRun+=pI->tIncrFullRun;
    pT->tIncrDiagShape+=pI->tIncrDiagShape;
    pT->tIncrDiagCollect+=pI->tIncrDiagCollect;
    pT->tIncrDiagEval+=pI->tIncrDiagEval;
    pT->tIncrDiagSim+=pI->tIncrDiagSim;
    pT->tIncrTfoBuild+=pI->tIncrTfoBuild;
    pT->tIncrTfoSim+=pI->tIncrTfoSim;
    pT->tIncrTxn+=pI->tIncrTxn;
    pT->nEventLocal+=pI->nEventLocal;
    pT->nEventFallback+=pI->nEventFallback;
    pT->nEventFallbackWork+=pI->nEventFallbackWork;
    pT->nEventFallbackTime+=pI->nEventFallbackTime;
    pT->nIncrAdaptTrips+=pI->nIncrAdaptTrips;
    pT->tEventLoad+=pI->tEventLoad;
    pT->tEventProp+=pI->tEventProp;
    pT->tEventRefine+=pI->tEventRefine;
    pT->tEventRollback+=pI->tEventRollback;
    pT->tEventInit+=pI->tEventInit;
    if ( pI->nEventPopsMax > pT->nEventPopsMax )
        pT->nEventPopsMax = pI->nEventPopsMax;
    if ( pI->nEventEdgesMax > pT->nEventEdgesMax )
        pT->nEventEdgesMax = pI->nEventEdgesMax;
    if ( pI->nEventInputVarsMax > pT->nEventInputVarsMax )
        pT->nEventInputVarsMax = pI->nEventInputVarsMax;
    if ( pI->nEventInputWordsMax > pT->nEventInputWordsMax )
        pT->nEventInputWordsMax = pI->nEventInputWordsMax;
    if ( pI->nIncrAdaptLocal > pT->nIncrAdaptLocal )
        pT->nIncrAdaptLocal = pI->nIncrAdaptLocal;
    if ( pI->nIncrAdaptFail > pT->nIncrAdaptFail )
        pT->nIncrAdaptFail = pI->nIncrAdaptFail;
    if ( pI->nIncrAdaptCooldown > pT->nIncrAdaptCooldown )
        pT->nIncrAdaptCooldown = pI->nIncrAdaptCooldown;
    if ( pI->nIncrBatchCexMax > pT->nIncrBatchCexMax )
        pT->nIncrBatchCexMax = pI->nIncrBatchCexMax;
    if ( pI->nIncrDirty > pT->nIncrDirty ) pT->nIncrDirty = pI->nIncrDirty;
    if ( pI->nIncrConeKeys > pT->nIncrConeKeys ) pT->nIncrConeKeys = pI->nIncrConeKeys;
    if ( pI->nIncrKeys  > pT->nIncrKeys  ) pT->nIncrKeys  = pI->nIncrKeys;
    if ( pI->tSatMax > pT->tSatMax ) pT->tSatMax = pI->tSatMax;
}

static void Cec_ProfCorCountStatus( Cec_ParCor_t * pPars,
    Vec_Str_t * vStatus, int fBmc )
{
    Cec_ProfCor_t * p = pPars->pProfile;
    int i, Status;
    if ( p == NULL )
        return;
    Vec_StrForEachEntry( vStatus, Status, i )
    {
        if ( fBmc )
        {
            if ( Status == 1 )      p->nBmcUnsat++;
            else if ( Status == 0 ) p->nBmcSat++;
            else                    p->nBmcUnknown++;
        }
        else
        {
            if ( Status == 1 )      p->nIndUnsat++;
            else if ( Status == 0 ) p->nIndSat++;
            else                    p->nIndUnknown++;
        }
    }
}

static void Cec_ProfCorAddRounds( Cec_ParCor_t * pPars,
    Cec_ScorrProf_t * pTotal, int fBmc, abctime TimeWall )
{
    Cec_ProfCor_t * p = pPars->pProfile;
    if ( p == NULL )
        return;
    if ( fBmc )
    {
        p->timeBmc      += TimeWall;
        p->timeBmcSrm   += pTotal->tSrm;
        p->timeBmcSat   += pTotal->tSat;
        p->timeBmcSetup += pTotal->tSatSetup;
        p->timeBmcSolve += pTotal->tSatSolve;
        p->timeBmcSim   += pTotal->tSim;
        p->nBmcRounds   += pTotal->nIterations;
    }
    else
    {
        p->timeInd      += TimeWall;
        p->timeIndSrm   += pTotal->tSrm;
        p->timeIndSat   += pTotal->tSat;
        p->timeIndSetup += pTotal->tSatSetup;
        p->timeIndSolve += pTotal->tSatSolve;
        p->timeIndSim   += pTotal->tSim;
        p->nIndRounds   += pTotal->nIterations;
    }
    p->nCexReal    += pTotal->nCexReal;
    p->nCexTrivial += pTotal->nCexTriv;
    p->nCexFail    += pTotal->nCexFail;
}

static void Cec_ProfCorFinishClasses( Cec_ParCor_t * pPars,
    Cec_ScorrProf_t * pIndTotal, abctime clkClasses, abctime clkInd )
{
    pPars->nConfUsed = Cec_ScorrConfUsed;
    pPars->fConfStop = Cec_ScorrConfStop;
    if ( pPars->pProfile == NULL )
        return;
    if ( clkInd )
        Cec_ProfCorAddRounds( pPars, pIndTotal, 0, Abc_ClockHr() - clkInd );
    pPars->pProfile->timeClasses += Abc_ClockHr() - clkClasses;
    pPars->pProfile->nConfUsed += Cec_ScorrConfUsed;
    pPars->pProfile->nConfStops += Cec_ScorrConfStop;
}

// Print one iteration's (or the run total's) breakdown. Times shown in ms.
// "rest" is wall minus every accounted phase = pure loop/housekeeping overhead.
static void Cec_ScorrProfPrint( const char * pTag, int iIter, int nProofs, Cec_ScorrProf_t * p )
{
    double M = 1.0/1000000.0; // ns -> ms
    abctime tIfo  = p->tSeed + p->tNext + p->tTfo + p->tCnt;
    abctime tAcc  = tIfo + p->tSnap + p->tSrm + p->tSat + p->tSim + p->tChk + p->tStats;
    abctime tRest = p->tWall > tAcc ? p->tWall - tAcc : 0;
    if ( iIter >= 0 )
    {
        Abc_Print( 1, "[scorr2-profile] stage=%s iter=%d wall=%.3f ms\n",
            pTag, iIter, p->tWall*M );
        Abc_Print( 1, "  pipeline: frontier=%.3f -> srm=%.3f -> sat=%.3f -> resim=%.3f -> check=%.3f ms\n",
            tIfo*M, p->tSrm*M, p->tSat*M, p->tSim*M, p->tChk*M );
        Abc_Print( 1, "  proofs=%d cex(real/trivial/fail)=%d/%d/%d resim(local/full)=%d/%d split(sim/check)=%d/%d\n",
            nProofs, p->nCexReal, p->nCexTriv, p->nCexFail,
            p->nIncrSrc, p->nIncrFull, p->dSimLits, p->dChkLits );
        return;
    }

    Abc_Print( 1, "[scorr2-profile] stage=%s summary iterations=%d\n",
        pTag, p->nIterations );
    Abc_Print( 1, "  pipeline: frontier=%.3f -> snapshot=%.3f -> srm=%.3f -> sat=%.3f -> resim=%.3f -> check=%.3f ms\n",
        tIfo*M, p->tSnap*M, p->tSrm*M, p->tSat*M,
        p->tSim*M, p->tChk*M );
    Abc_Print( 1, "  wall=%.3f stats=%.3f other=%.3f ms\n",
        p->tWall*M, p->tStats*M, tRest*M );
    Abc_Print( 1, "  sat: proofs=%d setup_ms=%.3f solve_ms=%.3f max_proof_ms=%.3f\n",
        nProofs, p->tSatSetup*M, p->tSatSolve*M, p->tSatMax*M );
    Abc_Print( 1, "  cex: real=%d trivial=%d failed=%d resim_calls=%d trivial_splits=%d pending=%d\n",
        p->nCexReal, p->nCexTriv, p->nCexFail, p->nSimCalls,
        p->nTrivSplits, p->nCexPending );
    Abc_Print( 1, "  refinement: split_by_resim=%d split_by_check=%d local_batches=%d full_batches=%d truncated=%d deferred=%d\n",
        p->dSimLits, p->dChkLits, p->nIncrSrc, p->nIncrFull,
        p->nIncrTrunc, p->nIncrDeferred );
    Abc_Print( 1, "  incremental: max_dirty=%d cone_keys=%d/%d rollback=%d/%d coverage_miss=%d batch_cex=%d max_batch=%d\n",
        p->nIncrDirty, p->nIncrConeKeys, p->nIncrKeys,
        p->nIncrRollback, p->nIncrRollbackObjs, p->nIncrCoverageMiss,
        p->nIncrBatchCex, p->nIncrBatchCexMax );
    Abc_Print( 1, "  fallback: cex=%d precheck=%d processing=%d coverage=%d bypass=%d event_work=%d event_time=%d\n",
        p->nIncrFallbackCex, p->nIncrFallbackPre, p->nIncrFallbackProcess,
        p->nIncrFallbackCoverage, p->nIncrFallbackBypass,
        p->nEventFallbackWork, p->nEventFallbackTime );
    Abc_Print( 1, "  event: local=%d fallback=%d max_pops=%d max_edges=%d input_vars=%d input_words=%d\n",
        p->nEventLocal, p->nEventFallback, p->nEventPopsMax,
        p->nEventEdgesMax, p->nEventInputVarsMax, p->nEventInputWordsMax );
    Abc_Print( 1, "  event_time_ms: init=%.3f load=%.3f propagate=%.3f refine=%.3f rollback=%.3f full_fallback=%.3f\n",
        p->tEventInit*M, p->tEventLoad*M, p->tEventProp*M,
        p->tEventRefine*M, p->tEventRollback*M, p->tIncrFullRun*M );
}

static void Cec_SeedSimAdaptRecord( Cec_SeedSim_t * p, int fLocal )
{
    if ( fLocal )
        p->nAdaptLocal++;
    else
        p->nAdaptFail++;
    if ( p->nAdaptLocal + p->nAdaptFail > CEC_SEEDSIM_ADAPT_WINDOW )
    {
        p->nAdaptLocal = (p->nAdaptLocal + 1) >> 1;
        p->nAdaptFail  = (p->nAdaptFail  + 1) >> 1;
    }
}

static int Cec_SeedSimAdaptShouldCool( Cec_SeedSim_t * p )
{
    int nSamples = p->nAdaptLocal + p->nAdaptFail;
    if ( nSamples < CEC_SEEDSIM_ADAPT_MIN_SAMPLES )
        return 0;
    return p->nAdaptFail >= CEC_SEEDSIM_ADAPT_FAIL_MUL * p->nAdaptLocal +
                            CEC_SEEDSIM_ADAPT_FAIL_EXTRA;
}

static int Cec_SeedSimAdaptCooldown( Cec_SeedSim_t * p )
{
    int nExcess = Abc_MaxInt( 0, p->nAdaptFail - p->nAdaptLocal );
    return Abc_MinInt( CEC_SEEDSIM_ADAPT_MAX_COOLDOWN,
        CEC_SEEDSIM_MAX_FALLBACK_BACKOFF + 2 * nExcess );
}


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the real value of the literal w/o spec reduction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCorrSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    if ( Gia_ObjIsAnd(pObj) )
    {
        Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), f, nPrefix );
        Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin1(pObj), f, nPrefix );
        return Gia_ManHashAnd( pNew, Gia_ObjFanin0CopyF(p, f, pObj), Gia_ObjFanin1CopyF(p, f, pObj) );
    }
    if ( f == 0 )
    {
        assert( Gia_ObjIsRo(p, pObj) );
        return Gia_ObjCopyF(p, f, pObj);
    }
    assert( f && Gia_ObjIsRo(p, pObj) );
    pObj = Gia_ObjRoToRi( p, pObj );
    Gia_ManCorrSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), f-1, nPrefix );
    return Gia_ObjFanin0CopyF( p, f-1, pObj );
}

/**Function*************************************************************

  Synopsis    [Recursively performs speculative reduction for the object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix )
{
    Gia_Obj_t * pRepr;
    int iLitNew;
    if ( ~Gia_ObjCopyF(p, f, pObj) )
        return;
    if ( f >= nPrefix && (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        Gia_ManCorrSpecReduce_rec( pNew, p, pRepr, f, nPrefix );
        iLitNew = Abc_LitNotCond( Gia_ObjCopyF(p, f, pRepr), Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
        Gia_ObjSetCopyF( p, f, pObj, iLitNew );
        return;
    }
    assert( Gia_ObjIsCand(pObj) );
    iLitNew = Gia_ManCorrSpecReal( pNew, p, pObj, f, nPrefix );
    Gia_ObjSetCopyF( p, f, pObj, iLitNew );
}

/**Function*************************************************************

  Synopsis    [Derives SRM for signal correspondence.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduce( Gia_Man_t * p, int nFrames, int fScorr, Vec_Int_t ** pvOutputs, int fRings, Vec_Int_t ** pvOutLits )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrev, iObj, iPrevNew, iObjNew, iPrevRaw, iObjRaw;
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    Vec_IntFill( &p->vCopies, (nFrames+fScorr)*Gia_ManObjNum(p), -1 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ObjSetCopyF( p, 0, Gia_ManConst0(p), 0 );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetCopyF( p, 0, pObj, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p, pObj, i )
        if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
            Gia_ObjSetCopyF( p, 0, pObj, Gia_ObjCopyF(p, 0, pRepr) );
    for ( f = 0; f < nFrames+fScorr; f++ )
    { 
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    if ( pvOutLits )
        *pvOutLits = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                iObjRaw = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
                iObjNew = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    if ( pvOutLits )
                    {
                        Vec_IntPush( *pvOutLits, 0 );
                        Vec_IntPush( *pvOutLits, iObjRaw );
                    }
                    Vec_IntPush( vXorLits, iObjNew );
                }
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    iPrevRaw = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames, 0 );
                    iObjRaw  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames, 0 );
                    iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                    iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                    if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                    {
                        Vec_IntPush( *pvOutputs, iPrev );
                        Vec_IntPush( *pvOutputs, iObj );
                        if ( pvOutLits )
                        {
                            Vec_IntPush( *pvOutLits, iPrevRaw );
                            Vec_IntPush( *pvOutLits, iObjRaw );
                        }
                        Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
                    }
                    iPrev = iObj;
                }
                iObj = i;
                iPrevRaw = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames, 0 );
                iObjRaw  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames, 0 );
                iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                {
                    Vec_IntPush( *pvOutputs, iPrev );
                    Vec_IntPush( *pvOutputs, iObj );
                    if ( pvOutLits )
                    {
                        Vec_IntPush( *pvOutLits, iPrevRaw );
                        Vec_IntPush( *pvOutLits, iObjRaw );
                    }
                    Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            iPrevRaw = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, nFrames, 0 );
            iObjRaw  = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
            iPrevNew = iPrevRaw;
            iObjNew  = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                if ( pvOutLits )
                {
                    Vec_IntPush( *pvOutLits, iPrevRaw );
                    Vec_IntPush( *pvOutLits, iObjRaw );
                }
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->vCopies );
//Abc_Print( 1, "Before sweeping = %d\n", Gia_ManAndNum(pNew) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    if ( pvOutLits )
        Gia_ManDupRemapLiterals( *pvOutLits, pTemp );
//Abc_Print( 1, "After sweeping = %d\n", Gia_ManAndNum(pNew) );
    Gia_ManStop( pTemp );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Derives SRM for signal correspondence.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduceInit( Gia_Man_t * p, int nFrames, int nPrefix, int fScorr, Vec_Int_t ** pvOutputs, int fRings )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrevNew, iObjNew;
    assert( (!fScorr && nFrames > 1) || (fScorr && nFrames > 0) || nPrefix );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    Vec_IntFill( &p->vCopies, (nFrames+nPrefix+fScorr)*Gia_ManObjNum(p), -1 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( (nFrames+nPrefix) * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachRo( p, pObj, i )
    {
        Gia_ManAppendCi(pNew);
        Gia_ObjSetCopyF( p, 0, pObj, 0 );
    }
    for ( f = 0; f < nFrames+nPrefix+fScorr; f++ )
    { 
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    for ( f = nPrefix; f < nFrames+nPrefix; f++ )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, f, nPrefix );
            iObjNew  = Gia_ManCorrSpecReal( pNew, p, pObj, f, nPrefix );
            iObjNew  = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->vCopies );
//Abc_Print( 1, "Before sweeping = %d\n", Gia_ManAndNum(pNew) );
    pNew = Gia_ManCleanup( pTemp = pNew );
//Abc_Print( 1, "After sweeping = %d\n", Gia_ManAndNum(pNew) );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Initializes simulation info for lcorr/scorr counter-examples.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManStartSimInfo( Vec_Ptr_t * vInfo, int nFlops )
{
    unsigned * pInfo;
    int k, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    assert( nFlops <= Vec_PtrSize(vInfo) );
    for ( k = 0; k < nFlops; k++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = 0;
    }
    for ( k = nFlops; k < Vec_PtrSize(vInfo); k++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry( vInfo, k );
        for ( w = 0; w < nWords; w++ )
            pInfo[w] = Gia_ManRandom( 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Remaps simulation info from SRM to the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrRemapSimInfo( Gia_Man_t * p, Vec_Ptr_t * vInfo )
{
    Gia_Obj_t * pObj, * pRepr;
    unsigned * pInfoObj, * pInfoRepr;
    int i, w, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    Gia_ManForEachRo( p, pObj, i )
    {
        // skip ROs without representatives
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr == NULL || Gia_ObjFailed(p, Gia_ObjId(p,pObj)) )
            continue;
        pInfoObj = (unsigned *)Vec_PtrEntry( vInfo, i );
        for ( w = 0; w < nWords; w++ )
            assert( pInfoObj[w] == 0 );
        // skip ROs with constant representatives
        if ( Gia_ObjIsConst0(pRepr) )
            continue;
        assert( Gia_ObjIsRo(p, pRepr) );
//        Abc_Print( 1, "%d -> %d    ", i, Gia_ObjId(p, pRepr) );
        // transfer info from the representative
        pInfoRepr = (unsigned *)Vec_PtrEntry( vInfo, Gia_ObjCioId(pRepr) - Gia_ManPiNum(p) );
        for ( w = 0; w < nWords; w++ )
            pInfoObj[w] = pInfoRepr[w];
    }
//    Abc_Print( 1, "\n" );
}

/**Function*************************************************************

  Synopsis    [Collects information about remapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_ManCorrCreateRemapping( Gia_Man_t * p )
{
    Vec_Int_t * vPairs;
    Gia_Obj_t * pObj, * pRepr;
    int i;
    vPairs = Vec_IntAlloc( 100 );
    Gia_ManForEachRo( p, pObj, i )
    {
        // skip ROs without representatives
        pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
        if ( pRepr == NULL || Gia_ObjIsConst0(pRepr) || Gia_ObjFailed(p, Gia_ObjId(p,pObj)) )
//        if ( pRepr == NULL || Gia_ObjIsConst0(pRepr) || Gia_ObjIsFailedPair(p, Gia_ObjId(p, pRepr), Gia_ObjId(p, pObj)) )
            continue;
        assert( Gia_ObjIsRo(p, pRepr) );
//        Abc_Print( 1, "%d -> %d    ", Gia_ObjId(p,pObj), Gia_ObjId(p, pRepr) );
        // remember the pair
        Vec_IntPush( vPairs, Gia_ObjCioId(pRepr) - Gia_ManPiNum(p) );
        Vec_IntPush( vPairs, i );
    }
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Remaps simulation info from SRM to the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrPerformRemapping( Vec_Int_t * vPairs, Vec_Ptr_t * vInfo )
{
    unsigned * pInfoObj, * pInfoRepr;
    int w, i, iObj, iRepr, nWords;
    nWords = Vec_PtrReadWordsSimInfo( vInfo );
    Vec_IntForEachEntry( vPairs, iRepr, i )
    {
        iObj = Vec_IntEntry( vPairs, ++i );
        pInfoObj = (unsigned *)Vec_PtrEntry( vInfo, iObj );
        pInfoRepr = (unsigned *)Vec_PtrEntry( vInfo, iRepr );
        for ( w = 0; w < nWords; w++ )
        {
            assert( pInfoObj[w] == 0 );
            pInfoObj[w] = pInfoRepr[w];
        }
    }
}

/**Function*************************************************************

  Synopsis    [Packs one counter-examples into the array of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

*************************************`**********************************/
int Cec_ManLoadCounterExamplesTry( Vec_Ptr_t * vInfo, Vec_Ptr_t * vPres, int iBit, int * pLits, int nLits )
{
    unsigned * pInfo, * pPres;
    int i;
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry(vInfo, Abc_Lit2Var(pLits[i]));
        pPres = (unsigned *)Vec_PtrEntry(vPres, Abc_Lit2Var(pLits[i]));
        if ( Abc_InfoHasBit( pPres, iBit ) && 
             Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(pLits[i]) )
             return 0;
    }
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry(vInfo, Abc_Lit2Var(pLits[i]));
        pPres = (unsigned *)Vec_PtrEntry(vPres, Abc_Lit2Var(pLits[i]));
        Abc_InfoSetBit( pPres, iBit );
        if ( Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(pLits[i]) )
            Abc_InfoXorBit( pInfo, iBit );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamples( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart )
{ 
    Vec_Int_t * vPat;
    Vec_Ptr_t * vPres;
    int nWords = Vec_PtrReadWordsSimInfo(vInfo);
    int nBits = 32 * nWords; 
    int k, nSize, kMax = 0;//, iBit = 1;
    vPat  = Vec_IntAlloc( 100 );
    vPres = Vec_PtrAllocSimInfo( Vec_PtrSize(vInfo), nWords );
    Vec_PtrCleanSimInfo( vPres, 0, nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        // skip the output number
        iStart++;
        // get the number of items
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        // extract pattern
        Vec_IntClear( vPat );
        for ( k = 0; k < nSize; k++ )
            Vec_IntPush( vPat, Vec_IntEntry( vCexStore, iStart++ ) );
        // add pattern to storage
        for ( k = 1; k < nBits; k++ )
            if ( Cec_ManLoadCounterExamplesTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) ) )
                break;
        kMax = Abc_MaxInt( kMax, k );
        if ( k == nBits-1 )
            break;
    }
    Vec_PtrFree( vPres );
    Vec_IntFree( vPat );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples and records bit lanes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamplesMapped( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart, Vec_Int_t * vOutBits )
{
    Vec_Int_t * vPat;
    Vec_Ptr_t * vPres;
    int nWords = Vec_PtrReadWordsSimInfo(vInfo);
    int nBits = 32 * nWords;
    int k, nSize, Out;
    Vec_IntClear( vOutBits );
    vPat  = Vec_IntAlloc( 100 );
    vPres = Vec_PtrAllocSimInfo( Vec_PtrSize(vInfo), nWords );
    Vec_PtrCleanSimInfo( vPres, 0, nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Out = Vec_IntEntry( vCexStore, iStart++ );
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        Vec_IntClear( vPat );
        for ( k = 0; k < nSize; k++ )
            Vec_IntPush( vPat, Vec_IntEntry( vCexStore, iStart++ ) );
        for ( k = 1; k < nBits; k++ )
            if ( Cec_ManLoadCounterExamplesTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) ) )
                break;
        if ( k < nBits )
        {
            Vec_IntPush( vOutBits, Out );
            Vec_IntPush( vOutBits, k );
        }
        if ( k == nBits-1 )
            break;
    }
    Vec_PtrFree( vPres );
    Vec_IntFree( vPat );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Performs bitpacking of counter-examples.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLoadCounterExamples2( Vec_Ptr_t * vInfo, Vec_Int_t * vCexStore, int iStart )
{ 
    unsigned * pInfo;
    int nBits = 32 * Vec_PtrReadWordsSimInfo(vInfo); 
    int k, iLit, nLits, Out, iBit = 1;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        // skip the output number
//        iStart++;
        Out = Vec_IntEntry( vCexStore, iStart++ );
//        Abc_Print( 1, "iBit = %d. Out = %d.\n", iBit, Out );
        // get the number of items
        nLits = Vec_IntEntry( vCexStore, iStart++ );
        if ( nLits <= 0 )
            continue;
        // add pattern to storage
        for ( k = 0; k < nLits; k++ )
        {
            iLit = Vec_IntEntry( vCexStore, iStart++ );
            pInfo = (unsigned *)Vec_PtrEntry( vInfo, Abc_Lit2Var(iLit) );
            if ( Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(iLit) )
                Abc_InfoXorBit( pInfo, iBit );
        }
        if ( ++iBit == nBits )
            break;
    }
//    Abc_Print( 1, "added %d bits\n", iBit-1 );
    return iStart;
}

/**Function*************************************************************

  Synopsis    [Classifies vCexStore entries by SAT outcome.]

  Description [Each entry is (Out, nLits[, lit0, ..., lit{nLits-1}]).
                 nLits  > 0  -> real SAT CEX with usable literals;
                 nLits == 0  -> trivial SAT (e.g. SRM PO became const 1);
                 nLits == -1 -> timeout/fail, no CEX.
               Counts are written via the out-pointers (any may be NULL).
               Returns 1 iff there is at least one entry usable for resim
               (real or trivial), preserving the prior skip-failed-resim
               semantics where only timeout-only stores get skipped.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_ManCexStoreClassify( Vec_Int_t * vCexStore, int * pnReal, int * pnTriv, int * pnFail )
{
    int iStart = 0, nSize, nReal = 0, nTriv = 0, nFail = 0;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        iStart++; // output number
        assert( iStart < Vec_IntSize(vCexStore) );
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize > 0 )
        {
            nReal++;
            iStart += nSize;
        }
        else if ( nSize == 0 )
        {
            nTriv++;
        }
        else
        {
            assert( nSize == -1 );
            nFail++;
        }
    }
    if ( pnReal ) *pnReal = nReal;
    if ( pnTriv ) *pnTriv = nTriv;
    if ( pnFail ) *pnFail = nFail;
    return (nReal + nTriv) > 0;
}

/**Function*************************************************************

  Synopsis    [Resimulates counter-examples derived by the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManResimulateCounterExamples( Cec_ManSim_t * pSim,
    Vec_Int_t * vCexStore, int nFrames, Cec_SeedSim_t * pSeed,
    Vec_Int_t * vOutputs, Cec_ParCor_t * pCorPars, int fInduction )
{
    Vec_Int_t * vPairs = NULL;
    Vec_Int_t * vOutBits = NULL;
    Vec_Ptr_t * vSimInfo = NULL;
    int RetValue = 0, iStart = 0, fValueRefs = 0;
    abctime tH = Cec_ScorrProfOn ? Abc_ClockHr() : 0;
    Cec_ScorrProfSimRemap = Cec_ScorrProfSimRun = 0;
    Cec_ScorrProfIncrSrc = Cec_ScorrProfIncrFull = Cec_ScorrProfIncrTrunc = 0;
    Cec_ScorrProfIncrRollback = Cec_ScorrProfIncrRollbackObjs = 0;
    Cec_ScorrProfIncrCoverageMiss = 0;
    Cec_ScorrProfIncrFallbackPre = Cec_ScorrProfIncrFallbackProcess = 0;
    Cec_ScorrProfIncrFallbackCoverage = 0;
    Cec_ScorrProfIncrFallbackCex = Cec_ScorrProfIncrFallbackBypass = 0;
    Cec_ScorrProfIncrTruncCone = Cec_ScorrProfIncrTruncEval = 0;
    Cec_ScorrProfIncrBatchCex = Cec_ScorrProfIncrBatchCexMax = 0;
    Cec_ScorrProfIncrDeferred = 0;
    Cec_ScorrProfIncrDirty = Cec_ScorrProfIncrConeKeys = Cec_ScorrProfIncrKeys = 0;
    Cec_ScorrProfIncrTry = Cec_ScorrProfIncrTryLocal = 0;
    Cec_ScorrProfIncrTryFallback = Cec_ScorrProfIncrFullRun = 0;
    Cec_ScorrProfIncrDiagShape = Cec_ScorrProfIncrDiagCollect = 0;
    Cec_ScorrProfIncrDiagEval = Cec_ScorrProfIncrDiagSim = 0;
    Cec_ScorrProfIncrTfoBuild = Cec_ScorrProfIncrTfoSim = Cec_ScorrProfIncrTxn = 0;
    Cec_ScorrProfEventLocal = Cec_ScorrProfEventFallback = 0;
    Cec_ScorrProfEventPopsMax = Cec_ScorrProfEventEdgesMax = 0;
    Cec_ScorrProfEventInputVarsMax = Cec_ScorrProfEventInputWordsMax = 0;
    Cec_ScorrProfEventFallbackWork = Cec_ScorrProfEventFallbackTime = 0;
    Cec_ScorrProfIncrAdaptLocal = Cec_ScorrProfIncrAdaptFail = 0;
    Cec_ScorrProfIncrAdaptTrips = Cec_ScorrProfIncrAdaptCooldown = 0;
    Cec_ScorrProfEventLoad = Cec_ScorrProfEventProp = 0;
    Cec_ScorrProfEventRefine = Cec_ScorrProfEventRollback = 0;
    Cec_ScorrProfEventInit = 0;
    if ( pSeed || (pCorPars && pCorPars->pCexFunc) )
        vOutBits = Vec_IntAlloc( 1000 );
    if ( pSeed )
        Cec_SeedSimBeginCall( pSeed );  // reset per-call local/full/maxdirty counters
//    pSim->pPars->nWords  = 63;
    pSim->pPars->nFrames = nFrames;
    if ( pSeed )
    {
        Cec_SeedSimEnsurePersistent( pSeed, pSim );
        // Defer the (possibly full-unroll-sized) class cone: it is built lazily
        // inside Cec_SeedSimTryBatch() only once a batch passes the density gate,
        // so rounds that fall back to full resim never pay for it.
        pSeed->fUseCone = 0;
        vSimInfo = pSeed->vSimInfo;
    }
    else
    {
        Gia_ManCreateValueRefs( pSim->pAig );
        fValueRefs = 1;
        vSimInfo = Vec_PtrAllocSimInfo( Gia_ManRegNum(pSim->pAig) + Gia_ManPiNum(pSim->pAig) * nFrames, pSim->pPars->nWords );
    }
    vPairs = Gia_ManCorrCreateRemapping( pSim->pAig );
    if ( Cec_ScorrProfOn ) Cec_ScorrProfSimRemap = Abc_ClockHr() - tH;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        if ( pSeed )
        {
            int LocalStatus;
            abctime tR = Cec_ScorrProfOn ? Abc_ClockHr() : 0;
            iStart = Cec_SeedSimLoadPersistentBatch(
                pSeed, vCexStore, iStart, vPairs, vOutBits );
            if ( Cec_ScorrProfOn )
                Cec_ScorrProfSimRemap += Abc_ClockHr() - tR;
            // (-V) snapshot the pre-batch partition for the soundness oracle
            if ( pSeed->fVerify )
                Cec_SeedSimVerifySnapshot( pSeed );
            if ( pSeed->nFallbackCooldown > 0 )
            {
                Cec_SeedSimBypassBatch( pSeed, Vec_IntSize(vOutBits) / 2 );
                pSeed->nFallbackCooldown--;
            }
            else if ( (LocalStatus = Cec_SeedSimTryBatch(
                           pSeed, pSim, vSimInfo, vOutputs, vOutBits, nFrames )) ==
                      CEC_SEEDSIM_RESULT_LOCAL )
            {
                Cec_SeedSimAdaptRecord( pSeed, 1 );
                pSeed->nFallbackStreak = 0;
                pSeed->nFallbackCooldown = 0;
                if ( pSeed->fVerify )
                {
                    // strict oracle: check the value cache AND, decisively, that
                    // the committed partition has no split missed vs full resim
                    int nBad = Cec_SeedSimVerifyValues( pSeed );
                    nBad += Cec_SeedSimVerifyRefine( pSeed, pSim, vSimInfo, nFrames );
                    if ( nBad > 0 )
                    {
                        Abc_Print( -1, "[resim-oracle] FATAL: incremental resim "
                            "differs from full resim (%d violations); aborting -V verification.\n", nBad );
                        fflush( stdout );
                        assert( 0 );
                    }
                }
                continue;
            }
            else
            {
                Cec_SeedSimAdaptRecord( pSeed, 0 );
                if ( Cec_SeedSimAdaptShouldCool( pSeed ) )
                {
                    pSeed->nFallbackStreak++;
                    pSeed->nFallbackCooldown = Cec_SeedSimAdaptCooldown( pSeed );
                    pSeed->nAdaptTrips++;
                }
                else if ( LocalStatus == CEC_SEEDSIM_RESULT_FULL_WIDE )
                {
                    int Shift;
                    pSeed->nFallbackStreak++;
                    Shift = Abc_MinInt( pSeed->nFallbackStreak - 1, 3 );
                    pSeed->nFallbackCooldown =
                        Abc_MinInt( (1 << Shift) - 1,
                            CEC_SEEDSIM_MAX_FALLBACK_BACKOFF );
                }
                else
                {
                    pSeed->nFallbackStreak = 0;
                    pSeed->nFallbackCooldown = 0;
                }
            }
        }
        else
        {
            abctime tR = Cec_ScorrProfOn ? Abc_ClockHr() : 0;
            Cec_ManStartSimInfo( vSimInfo, Gia_ManRegNum(pSim->pAig) );
            if ( pCorPars && pCorPars->pCexFunc )
                iStart = Cec_ManLoadCounterExamplesMapped( vSimInfo,
                    vCexStore, iStart, vOutBits );
            else
                iStart = Cec_ManLoadCounterExamples( vSimInfo,
                    vCexStore, iStart );
            Gia_ManCorrPerformRemapping( vPairs, vSimInfo );
            if ( Cec_ScorrProfOn )
                Cec_ScorrProfSimRemap += Abc_ClockHr() - tR;
        }
        if ( !pSeed && pCorPars && pCorPars->pCexFunc &&
             Vec_IntSize(vOutBits) )
            pCorPars->pCexFunc( pCorPars->pCexData, pSim->pAig,
                vSimInfo, vOutBits, nFrames, fInduction );
        // The local path returned above.  Reaching here means standard full
        // resimulation, either without -I or as an incremental fallback.
        if ( pSeed )
        {
            abctime tF;
            if ( !fValueRefs )
            {
                Gia_ManCreateValueRefs( pSim->pAig );
                fValueRefs = 1;
            }
            tF = Abc_ClockHr();
            RetValue |= Cec_ManSeqResimulateSeed( pSim, vSimInfo, pSeed );
            {
                abctime Elapsed = Abc_ClockHr() - tF;
                if ( Cec_ScorrProfOn )
                    Cec_ScorrProfIncrFullRun += Elapsed;
            }
            Cec_SeedSimRestorePersistentInputs( pSeed );
        }
        else
            RetValue |= Cec_ManSeqResimulate( pSim, vSimInfo );
//        Cec_ManSeqResimulateInfo( pSim->pAig, vSimInfo, NULL );
    }
    if ( pSeed )
    {
        Cec_ScorrProfIncrSrc   = Cec_SeedSimNumLocal( pSeed );
        Cec_ScorrProfIncrFull  = Cec_SeedSimNumFull( pSeed );
        Cec_ScorrProfIncrTrunc = Cec_SeedSimNumTrunc( pSeed );
        Cec_ScorrProfIncrRollback = Cec_SeedSimNumRollback( pSeed );
        Cec_ScorrProfIncrRollbackObjs = Cec_SeedSimNumRollbackObjs( pSeed );
        Cec_ScorrProfIncrCoverageMiss = Cec_SeedSimNumCoverageMiss( pSeed );
        Cec_ScorrProfIncrFallbackPre = Cec_SeedSimNumFallbackPre( pSeed );
        Cec_ScorrProfIncrFallbackProcess = Cec_SeedSimNumFallbackProcess( pSeed );
        Cec_ScorrProfIncrFallbackCoverage = Cec_SeedSimNumFallbackCoverage( pSeed );
        Cec_ScorrProfIncrFallbackCex = Cec_SeedSimNumFallbackCex( pSeed );
        Cec_ScorrProfIncrFallbackBypass = Cec_SeedSimNumFallbackBypass( pSeed );
        Cec_ScorrProfIncrTruncCone = Cec_SeedSimNumTruncCone( pSeed );
        Cec_ScorrProfIncrTruncEval = Cec_SeedSimNumTruncEval( pSeed );
        Cec_ScorrProfIncrBatchCex = Cec_SeedSimNumBatchCex( pSeed );
        Cec_ScorrProfIncrBatchCexMax = Cec_SeedSimNumBatchCexMax( pSeed );
        Cec_ScorrProfIncrDeferred = Cec_SeedSimNumDeferredSplits( pSeed );
        Cec_ScorrProfIncrDirty = Cec_SeedSimNumDirty( pSeed );
        Cec_ScorrProfIncrConeKeys = Cec_SeedSimNumConeKeys( pSeed );
        Cec_ScorrProfIncrKeys  = Cec_SeedSimNumKeys( pSeed );
        Cec_ScorrProfIncrTry = Cec_SeedSimTimeTry( pSeed );
        Cec_ScorrProfIncrTryLocal = Cec_SeedSimTimeTryLocal( pSeed );
        Cec_ScorrProfIncrTryFallback = Cec_SeedSimTimeTryFallback( pSeed );
        Cec_ScorrProfIncrDiagShape = Cec_SeedSimTimeDiagShape( pSeed );
        Cec_ScorrProfIncrDiagCollect = Cec_SeedSimTimeDiagCollect( pSeed );
        Cec_ScorrProfIncrDiagEval = Cec_SeedSimTimeDiagEval( pSeed );
        Cec_ScorrProfIncrDiagSim = Cec_SeedSimTimeDiagSim( pSeed );
        Cec_ScorrProfIncrTfoBuild = Cec_SeedSimTimeTfoBuild( pSeed );
        Cec_ScorrProfIncrTfoSim = Cec_SeedSimTimeTfoSim( pSeed );
        Cec_ScorrProfIncrTxn = Cec_SeedSimTimeTxn( pSeed );
        Cec_ScorrProfEventLocal = Cec_SeedSimNumEventLocal( pSeed );
        Cec_ScorrProfEventFallback = Cec_SeedSimNumEventFallback( pSeed );
        Cec_ScorrProfEventPopsMax = Cec_SeedSimNumEventPopsMax( pSeed );
        Cec_ScorrProfEventEdgesMax = Cec_SeedSimNumEventEdgesMax( pSeed );
        Cec_ScorrProfEventInputVarsMax = Cec_SeedSimNumEventInputVarsMax( pSeed );
        Cec_ScorrProfEventInputWordsMax = Cec_SeedSimNumEventInputWordsMax( pSeed );
        Cec_ScorrProfEventFallbackWork = Cec_SeedSimNumEventFallbackWork( pSeed );
        Cec_ScorrProfEventFallbackTime = Cec_SeedSimNumEventFallbackTime( pSeed );
        Cec_ScorrProfIncrAdaptLocal = Cec_SeedSimNumAdaptLocal( pSeed );
        Cec_ScorrProfIncrAdaptFail = Cec_SeedSimNumAdaptFail( pSeed );
        Cec_ScorrProfIncrAdaptTrips = Cec_SeedSimNumAdaptTrips( pSeed );
        Cec_ScorrProfIncrAdaptCooldown = Cec_SeedSimNumAdaptCooldown( pSeed );
        Cec_ScorrProfEventLoad = Cec_SeedSimTimeEventLoad( pSeed );
        Cec_ScorrProfEventProp = Cec_SeedSimTimeEventProp( pSeed );
        Cec_ScorrProfEventRefine = Cec_SeedSimTimeEventRefine( pSeed );
        Cec_ScorrProfEventRollback = Cec_SeedSimTimeEventRollback( pSeed );
        Cec_ScorrProfEventInit = Cec_SeedSimTimeEventInit( pSeed );
    }
    if ( Cec_ScorrProfOn ) Cec_ScorrProfSimRun = Abc_ClockHr() - tH - Cec_ScorrProfSimRemap;
//Gia_ManEquivPrintOne( pSim->pAig, 85, 0 );
    assert( iStart == Vec_IntSize(vCexStore) );
    Vec_IntFreeP( &vOutBits );
    if ( !pSeed )
        Vec_PtrFree( vSimInfo );
    Vec_IntFreeP( &vPairs );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Resimulates counter-examples derived by the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManResimulateCounterExamplesComb( Cec_ManSim_t * pSim, Vec_Int_t * vCexStore )
{ 
    Vec_Ptr_t * vSimInfo; 
    int RetValue = 0, iStart = 0;
    Gia_ManCreateValueRefs( pSim->pAig );
    pSim->pPars->nFrames = 1;
    vSimInfo = Vec_PtrAllocSimInfo( Gia_ManCiNum(pSim->pAig), pSim->pPars->nWords );
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Cec_ManStartSimInfo( vSimInfo, 0 );
        iStart = Cec_ManLoadCounterExamples( vSimInfo, vCexStore, iStart );
        RetValue |= Cec_ManSeqResimulate( pSim, vSimInfo );
    }
    assert( iStart == Vec_IntSize(vCexStore) );
    Vec_PtrFree( vSimInfo );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Checks whether two endpoints are still in the same class.]

  Description [Ring mode needs special handling for the closing edge
               tail -> head because Gia_ObjHasSameRepr() compares raw
               representatives and the head stores GIA_VOID.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_ManObjsStillMerged( Gia_Man_t * p, int iRepr, int iObj, int fRings )
{
    int iReprRoot, iObjRoot;
    if ( !fRings )
        return Gia_ObjHasSameRepr( p, iRepr, iObj );
    if ( iRepr == 0 )
        return Gia_ObjIsConst( p, iObj );
    if ( iObj == 0 )
        return Gia_ObjIsConst( p, iRepr );
    if ( !Gia_ObjIsClass( p, iRepr ) || !Gia_ObjIsClass( p, iObj ) )
        return 0;
    iReprRoot = Gia_ObjIsHead( p, iRepr ) ? iRepr : Gia_ObjRepr( p, iRepr );
    iObjRoot  = Gia_ObjIsHead( p, iObj  ) ? iObj  : Gia_ObjRepr( p, iObj  );
    return iReprRoot == iObjRoot && iReprRoot != GIA_VOID;
}

static int Cec_ManObjToSplit( Gia_Man_t * p, int iRepr, int iObj, int fRings )
{
    // For the ring closing edge (tail, head), split the tail. Splitting the
    // head is also correct, but it changes the representative of the whole
    // remaining class and creates a much larger incremental seed set.
    if ( fRings && iObj > 0 && Gia_ObjIsHead( p, iObj ) && Gia_ObjIsClass( p, iRepr ) )
        return iRepr;
    return iObj;
}

/**Function*************************************************************

  Synopsis    [Directly splits pairs whose SAT result was trivial (nLits==0).]

  Description [A trivial SAT (e.g. SRM PO became const 1) is a real
  disproval but carries no CEX literals, so Cec_ManResimulateCounterExamples
  cannot break the pair -- only random filler can, and usually does not.
  Splitting these pairs directly is sound (SAT proved disequivalence) and
  recovers work that the standard resim path leaves on the table.

  Only nLits==0 entries are touched; nLits>0 entries are left for resim to
  refine, matching the established behaviour in Gia_ManCheckRefinements
  that avoids force-splitting CEX-bearing SAT pairs (token_ring regression).

  Returns the number of pairs actually split this call.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_ManTrivialSatSplit( Gia_Man_t * pAig, Cec_ManSim_t * pSim,
    Vec_Int_t * vCexStore, Vec_Str_t * vStatus, Vec_Int_t * vOutputs, int fRings )
{
    int iStart = 0, Out, nSize, iRepr, iObj, iSplit, Count = 0;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        Out = Vec_IntEntry( vCexStore, iStart++ );
        assert( iStart < Vec_IntSize(vCexStore) );
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize > 0 )
        {
            iStart += nSize;
            continue;
        }
        if ( nSize < 0 )
            continue;
        // nSize == 0 -> trivial SAT, no CEX literals.
        assert( Out < Vec_StrSize(vStatus) );
        assert( Vec_StrEntry(vStatus, Out) == 0 );
        iRepr = Vec_IntEntry( vOutputs, 2*Out );
        iObj  = Vec_IntEntry( vOutputs, 2*Out + 1 );
        if ( !Cec_ManObjsStillMerged( pAig, iRepr, iObj, fRings ) )
            continue;
        iSplit = Cec_ManObjToSplit( pAig, iRepr, iObj, fRings );
        if ( Cec_ManSimClassRemoveOne( pSim, iSplit ) )
            Count++;
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Updates equivalence classes by marking those that timed out.]

  Description [Returns 1 if all nodes are proved.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCheckRefinements( Gia_Man_t * p, Vec_Str_t * vStatus, Vec_Int_t * vOutputs, Cec_ManSim_t * pSim, int fRings )
{
    int i, status, iRepr, iObj;
    int Counter = 0;
    assert( 2 * Vec_StrSize(vStatus) == Vec_IntSize(vOutputs) );
    Vec_StrForEachEntry( vStatus, status, i )
    {
        iRepr = Vec_IntEntry( vOutputs, 2*i );
        iObj  = Vec_IntEntry( vOutputs, 2*i+1 );
        if ( status == 1 )
            continue;
        if ( status == 0 )
        {
            // Match upstream ABC: do not force-split when SAT returns a CEX.
            // Cec_ManResimulateCounterExamples replays the CEX and refines the
            // class; only a contrived pattern-packing conflict could leave the
            // pair merged (each lit must collide at every one of the 32*nWords
            // packed slots). Forcing a split here is sound but perturbs the
            // BMC/refinement trajectory and was the cause of the
            // Problem05_label47/49 + token_ring incremental regression.
            if ( Cec_ManObjsStillMerged( p, iRepr, iObj, fRings ) )
                Counter++;
            continue;
        }
        if ( status == -1 )
        {
//            if ( !Gia_ObjFailed( p, iObj ) )
//                Abc_Print( 1, "Gia_ManCheckRefinements(): Failed equivalence is not marked as failed!\n" );
//            Gia_ObjSetFailed( p, iRepr );
//            Gia_ObjSetFailed( p, iObj );
//            if ( fRings )
//            Cec_ManSimClassRemoveOne( pSim, iRepr );
            Cec_ManSimClassRemoveOne( pSim, iObj );
            continue;
        }
    }
//    if ( Counter )
//    Abc_Print( 1, "Gia_ManCheckRefinements(): Could not refine %d nodes.\n", Counter );
    return Counter;
}


/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManCorrReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pRepr;
    if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        Gia_ManCorrReduce_rec( pNew, p, pRepr );
        pObj->Value = Abc_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
        return;
    }
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCorrReduce_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManCorrReduce_rec( pNew, p, Gia_ObjFanin1(pObj) );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Reduces AIG using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManCorrReduce( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManCorrReduce_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Prints statistics during solving.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManRefinedClassPrintStats( Gia_Man_t * p, Vec_Str_t * vStatus, int iIter, abctime Time )
{ 
    int nLits, CounterX = 0, Counter0 = 0, Counter = 0;
    int i, Entry, nProve = 0, nDispr = 0, nFail = 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsHead(p, i) )
            Counter++;
    }
    CounterX -= Gia_ManCoNum(p);
    nLits = Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
    if ( iIter == -1 )
        Abc_Print( 1, "BMC : " );
    else
        Abc_Print( 1, "%3d : ", iIter );
    Abc_Print( 1, "c =%8d  cl =%7d  lit =%8d  ", Counter0, Counter, nLits );
    if ( vStatus )
    Vec_StrForEachEntry( vStatus, Entry, i )
    {
        if ( Entry == 1 )
            nProve++;
        else if ( Entry == 0 )
            nDispr++;
        else if ( Entry == -1 )
            nFail++;
    }
    Abc_Print( 1, "p =%6d  d =%6d  f =%6d  ", nProve, nDispr, nFail );
    Abc_Print( 1, "%c  ", Gia_ObjIsConst( p, Gia_ObjFaninId0p(p, Gia_ManPo(p, 0)) ) ? '+' : '-' );
    Abc_PrintTime( 1, "T", Time );
}
int Cec_ManCountLits( Gia_Man_t * p )
{ 
    int i, CounterX = 0, Counter0 = 0, Counter = 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsHead(p, i) )
            Counter++;
    }
    CounterX -= Gia_ManCoNum(p);
    return Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
}

/**Function*************************************************************

  Synopsis    [Runs BMC for the equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManLSCorrespondenceBmc( Gia_Man_t * pAig, Cec_ParCor_t * pPars, int nPrefs )
{
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Vec_Str_t * vStatus;
    Vec_Int_t * vOutputs;
    Vec_Int_t * vCexStore;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int fChanges, RetValue, i;
    int nBmcResimFrames = pPars->nFrames + 1 + nPrefs;
    int fBmcPersist = 0;
    // fine-grained profiling (-w only); zero-cost when fVeryVerbose is off
    Cec_ScorrProf_t Prof, Total; abctime tWall0 = 0, tH = 0;
    abctime clkProfBmc = pPars->pProfile ? Abc_ClockHr() : 0;
    memset( &Total, 0, sizeof(Total) );
    Cec_ScorrProfOn = pPars->fVeryVerbose || pPars->pProfile != NULL;
    // BMC SRM is keyed only on pReprs (Gia_ManCorrSpecReduceInit ignores
    // its fRings flag).  So the incremental filter only needs pReprs-based
    // seeds; pNexts changes cannot affect this SRM and there are no ring
    // closing edges to reprove -- BMC is structurally simpler than the
    // main inductive loop.
    Cec_IncrMgr_t * pBmcMgr = NULL;
    Cec_DynSrm_t * pBmcDynSrm = NULL;
    // prepare simulation manager
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords     = pPars->nWords;
    pParsSim->nFrames    = pPars->nRounds;
    pParsSim->fVerbose   = pPars->fVerbose;
    pParsSim->fLatchCorr = pPars->fLatchCorr;
    pParsSim->fSeqSimulate = 1;
    pSim = Cec_ManSimStart( pAig, pParsSim );
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    if ( pPars->fIncremental )
    {
        // Use the deepest BMC unrolling depth so the TFO BFS covers every
        // frame the SRM emits.  In practice nPrefs is 0 and this matches
        // the main loop's depth, but be defensive in case of non-default
        // nPrefs callers.
        pBmcMgr = Cec_IncrMgrAlloc( pAig, pPars->nFrames + nPrefs );
        Cec_IncrMgrSnapshotClasses( pBmcMgr );
    }
    if ( pPars->fDynSrm && pBmcMgr )
    {
        pBmcDynSrm = Cec_DynSrmAlloc( pAig, pBmcMgr, 0 );
        Cec_DynSrmSetParams( pBmcDynSrm, pPars );
    }
    fBmcPersist = ( pBmcDynSrm != NULL && pPars->fUseCSat );
    fChanges = 1;
    for ( i = 0; fChanges && (!pPars->nLimitMax || i < pPars->nLimitMax); i++ )
    {
        int * pTfoMask = NULL;
        int nReprSeeds = 0, nTotalPairs = 0, nActivePairs = 0;
        int nBmcPos = 0;
        if ( Cec_ParCorShouldStop( pPars ) )
            break;
        abctime clkBmc = Abc_Clock();
        tWall0 = Abc_ClockHr();
        memset( &Prof, 0, sizeof(Prof) );
        fChanges = 0;
        // Decide whether to apply incremental TFO mask this iteration.
        // Skip on i==0 because the first full BMC SRM establishes the cache.
        if ( pBmcMgr && i > 0 )
        {
            tH = Abc_ClockHr();
            nReprSeeds = Cec_IncrMgrComputeSeeds( pBmcMgr );
            Prof.tSeed = Abc_ClockHr() - tH;
            if ( nReprSeeds == 0 )
            {
                // No pReprs change.  BMC SRM topology is unchanged.
                break;
            }
            tH = Abc_ClockHr();
            Cec_IncrMgrComputeTfo( pBmcMgr );
            Prof.tTfo = Abc_ClockHr() - tH;
            // BMC SRM is non-ring; pass fRings=0 so we count (head, member)
            // pairs only and skip any ring-edge bookkeeping.
            tH = Abc_ClockHr();
            if ( pBmcDynSrm )
                Cec_DynSrmCountActivePairs( pBmcDynSrm, 0, pBmcMgr->pTfoMark, &nTotalPairs, &nActivePairs );
            else
                Cec_IncrMgrCountActivePairs( pBmcMgr, 0, pBmcMgr->pTfoMark, &nTotalPairs, &nActivePairs );
            Prof.tCnt = Abc_ClockHr() - tH;
            if ( nActivePairs == 0 )
                break;
            {
                int fIncrFallback = nTotalPairs > 0 &&
                    (ABC_INT64_T)100 * nActivePairs > (ABC_INT64_T)pPars->nIncrFallbackPct * nTotalPairs;
                int fDynRebuild = nTotalPairs > 0 &&
                    (ABC_INT64_T)100 * nActivePairs > (ABC_INT64_T)pPars->nDynSrmRebuildPct * nTotalPairs;
                if ( pBmcDynSrm && (fIncrFallback || fDynRebuild) )
                    Cec_DynSrmForceRebuild( pBmcDynSrm, fIncrFallback );
                // The -i fallback threshold controls whether to drop the
                // active mask.  The -D threshold only controls cold rebuild.
                if ( !fIncrFallback )
                    pTfoMask = pBmcMgr->pTfoMark;
            }
        }
        tH = Abc_ClockHr();
        pSrm = NULL;
        if ( fBmcPersist )
            Cec_DynSrmBuildCoreInit( pBmcDynSrm, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pTfoMask, pTfoMask ? CEC_EMIT_ACTIVE : CEC_EMIT_ALL );
        else if ( pBmcDynSrm )
            pSrm = Cec_DynSrmBuildInit( pBmcDynSrm, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pTfoMask, pTfoMask ? CEC_EMIT_ACTIVE : CEC_EMIT_ALL );
        else if ( pTfoMask )
            pSrm = Gia_ManCorrSpecReduceInit_Active( pAig, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pTfoMask );
        else
            pSrm = Gia_ManCorrSpecReduceInit( pAig, pPars->nFrames, nPrefs, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings );
        Prof.tSrm = Abc_ClockHr() - tH;
        nBmcPos = fBmcPersist ? Vec_IntSize(Cec_DynSrmOutLits(pBmcDynSrm)) : Gia_ManCoNum(pSrm);
        if ( pTfoMask && pPars->fVeryVerbose )
            Abc_Print( 1, "[scorr2-profile] stage=bmc frontier iter=%d repr_changes=%d active_pairs=%d/%d roots=%d\n",
                       i, nReprSeeds, nActivePairs, nTotalPairs, nBmcPos );
        // Snapshot after SRM construction, before SAT/refine: this is the
        // class state whose pairs were just emitted.  The next iteration's
        // diff vs this snapshot tells us which pairs are stale.
        if ( pBmcMgr )
        {
            tH = Abc_ClockHr();
            Cec_IncrMgrSnapshotClasses( pBmcMgr );
            Prof.tSnap = Abc_ClockHr() - tH;
        }
        if ( nBmcPos == 0 )
        {
            if ( pSrm )
                Gia_ManStop( pSrm );
            Vec_IntFree( vOutputs );
            break;
        }
        pParsSat->nBTLimit *= 10;
        tH = Abc_ClockHr();
        Cec_ScorrConfLimit = pPars->nConfTotal;
        if ( fBmcPersist && (pPars->fUseTas || pPars->fBmcTasAdaptive) )
            vCexStore = Cec_DynSrmSolveBmcAdaptive( pBmcDynSrm, pPars->nBTLimit, &vStatus, pPars->fUseTas );
        else if ( fBmcPersist )
            vCexStore = Cec_DynSrmSolve( pBmcDynSrm, pPars->nBTLimit, &vStatus, 0 );
        else if ( pPars->fUseCSat )
            vCexStore = Tas_ManSolveMiterNc( pSrm, pPars->nBTLimit, &vStatus, 0 );
        else
            vCexStore = Cec_ManSatSolveMiter( pSrm, pParsSat, &vStatus );
        Cec_ScorrConfLimit = 0;
        Prof.tSat = Abc_ClockHr() - tH;
        Cec_ProfCorCountStatus( pPars, vStatus, 1 );
        Prof.tSatSetup = Cec_ScorrProfSetup; Prof.tSatSolve = Cec_ScorrProfSolve;
        Prof.tSatMax   = Cec_ScorrProfMax;   Prof.nSatCalls = Cec_ScorrProfCalls;
        if ( pBmcDynSrm && Vec_IntSize(vCexStore) == 0 )
            Cec_DynSrmRecordSolveStats( pBmcDynSrm, Prof.nSatCalls, 0, 0, 0, Prof.tSat );
        // refine classes with these counter-examples
        if ( Vec_IntSize(vCexStore) )
        {
            int nLitsPre = 0, nLitsMid = 0, nLitsPost = 0;
            // classify CEX entries: real (nLits>0) / trivial (==0) / fail (==-1)
            Cec_ManCexStoreClassify( vCexStore, &Prof.nCexReal, &Prof.nCexTriv, &Prof.nCexFail );
            if ( pBmcDynSrm )
                Cec_DynSrmRecordSolveStats( pBmcDynSrm, Prof.nSatCalls,
                    Prof.nCexReal, Prof.nCexTriv, Prof.nCexFail, Prof.tSat );
            if ( Cec_ScorrProfOn ) nLitsPre = Gia_ManEquivCountLitsAll( pAig );
            // only invoke resim when there is a real CEX (nLits>0).  Trivial
            // (nLits==0) and fail (==-1) entries carry no literals; trivial
            // pairs are handled by direct split below, fail pairs by chk.
            if ( Prof.nCexReal > 0 || !pPars->fSkipFailResim )
            {
                tH = Abc_ClockHr();
                // Keep BMC/init CEX resimulation on the canonical full path even
                // when -I is requested.  BMC counterexamples are partial models
                // of frame/prefix-specific SAT obligations; retaining them as a
                // persistent simulation background over-refines classes and can
                // significantly hurt gate QoR.  The main correspondence loop
                // below still uses -I for its ordinary refinement batches.
                RetValue = Cec_ManResimulateCounterExamples( pSim,
                    vCexStore, nBmcResimFrames, NULL, vOutputs,
                    pPars, 0 );
                Prof.tSim = Abc_ClockHr() - tH;
                Prof.tSimRemap = Cec_ScorrProfSimRemap; Prof.tSimRun = Cec_ScorrProfSimRun;
                Prof.nIncrSrc = Cec_ScorrProfIncrSrc; Prof.nIncrFull = Cec_ScorrProfIncrFull;
                Prof.nIncrTrunc = Cec_ScorrProfIncrTrunc;
                Prof.nIncrRollback = Cec_ScorrProfIncrRollback;
                Prof.nIncrRollbackObjs = Cec_ScorrProfIncrRollbackObjs;
                Prof.nIncrCoverageMiss = Cec_ScorrProfIncrCoverageMiss;
                Prof.nIncrFallbackPre = Cec_ScorrProfIncrFallbackPre;
                Prof.nIncrFallbackProcess = Cec_ScorrProfIncrFallbackProcess;
                Prof.nIncrFallbackCoverage = Cec_ScorrProfIncrFallbackCoverage;
                Prof.nIncrFallbackCex = Cec_ScorrProfIncrFallbackCex;
                Prof.nIncrFallbackBypass = Cec_ScorrProfIncrFallbackBypass;
                Prof.nIncrTruncCone = Cec_ScorrProfIncrTruncCone;
                Prof.nIncrTruncEval = Cec_ScorrProfIncrTruncEval;
                Prof.nIncrBatchCex = Cec_ScorrProfIncrBatchCex;
                Prof.nIncrBatchCexMax = Cec_ScorrProfIncrBatchCexMax;
                Prof.nIncrDeferred = Cec_ScorrProfIncrDeferred;
                Prof.nIncrDirty = Cec_ScorrProfIncrDirty;
                Prof.nIncrConeKeys = Cec_ScorrProfIncrConeKeys;
                Prof.nIncrKeys = Cec_ScorrProfIncrKeys;
                Prof.tIncrTry = Cec_ScorrProfIncrTry;
                Prof.tIncrTryLocal = Cec_ScorrProfIncrTryLocal;
                Prof.tIncrTryFallback = Cec_ScorrProfIncrTryFallback;
                Prof.tIncrFullRun = Cec_ScorrProfIncrFullRun;
                Prof.tIncrDiagShape = Cec_ScorrProfIncrDiagShape;
                Prof.tIncrDiagCollect = Cec_ScorrProfIncrDiagCollect;
                Prof.tIncrDiagEval = Cec_ScorrProfIncrDiagEval;
                Prof.tIncrDiagSim = Cec_ScorrProfIncrDiagSim;
                Prof.tIncrTfoBuild = Cec_ScorrProfIncrTfoBuild;
                Prof.tIncrTfoSim = Cec_ScorrProfIncrTfoSim;
                Prof.tIncrTxn = Cec_ScorrProfIncrTxn;
                Prof.nEventLocal = Cec_ScorrProfEventLocal;
                Prof.nEventFallback = Cec_ScorrProfEventFallback;
                Prof.nEventPopsMax = Cec_ScorrProfEventPopsMax;
                Prof.nEventEdgesMax = Cec_ScorrProfEventEdgesMax;
                Prof.nEventInputVarsMax = Cec_ScorrProfEventInputVarsMax;
                Prof.nEventInputWordsMax = Cec_ScorrProfEventInputWordsMax;
                Prof.nEventFallbackWork = Cec_ScorrProfEventFallbackWork;
                Prof.nEventFallbackTime = Cec_ScorrProfEventFallbackTime;
                Prof.nIncrAdaptLocal = Cec_ScorrProfIncrAdaptLocal;
                Prof.nIncrAdaptFail = Cec_ScorrProfIncrAdaptFail;
                Prof.nIncrAdaptTrips = Cec_ScorrProfIncrAdaptTrips;
                Prof.nIncrAdaptCooldown = Cec_ScorrProfIncrAdaptCooldown;
                Prof.tEventLoad = Cec_ScorrProfEventLoad;
                Prof.tEventProp = Cec_ScorrProfEventProp;
                Prof.tEventRefine = Cec_ScorrProfEventRefine;
                Prof.tEventRollback = Cec_ScorrProfEventRollback;
                Prof.tEventInit = Cec_ScorrProfEventInit;
                Prof.nSimCalls = 1;
            }
            if ( Prof.nCexTriv > 0 )
                Prof.nTrivSplits = Cec_ManTrivialSatSplit( pAig, pSim, vCexStore, vStatus, vOutputs, pPars->fUseRings );
            if ( Cec_ScorrProfOn ) nLitsMid = Gia_ManEquivCountLitsAll( pAig );
            tH = Abc_ClockHr();
            Prof.nCexPending = Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, pPars->fUseRings );
            Prof.tChk = Abc_ClockHr() - tH;
            if ( Cec_ScorrProfOn ) nLitsPost = Gia_ManEquivCountLitsAll( pAig );
            Prof.dSimLits = nLitsPre - nLitsMid;
            Prof.dChkLits = nLitsMid - nLitsPost;
            fChanges = 1;
        }
        if ( pPars->fVerbose )
        {
            tH = Abc_ClockHr();
            Cec_ManRefinedClassPrintStats( pAig, vStatus, -1, Abc_Clock() - clkBmc );
            Prof.tStats = Abc_ClockHr() - tH;
        }
        // recycle
        Vec_IntFree( vCexStore );
        Vec_StrFree( vStatus );
        if ( pSrm )
            Gia_ManStop( pSrm );
        Vec_IntFree( vOutputs );
        Prof.tWall = Abc_ClockHr() - tWall0;
        if ( pPars->fVeryVerbose )
            Cec_ScorrProfPrint( "bmc", i, Prof.nSatCalls, &Prof );
        Cec_ScorrProfAdd( &Total, &Prof );
        if ( Cec_ParCorShouldStop( pPars ) )
            break;
    }
    if ( pPars->fVeryVerbose )
        Cec_ScorrProfPrint( "bmc", -1, Total.nSatCalls, &Total );
    if ( pPars->fVeryVerbose && pBmcDynSrm && pPars->fBmcTasAdaptive && !pPars->fUseTas )
        Cec_DynSrmPrintBmcSolverStats( pBmcDynSrm );
    Cec_ProfCorAddRounds( pPars, &Total, 1,
        pPars->pProfile ? Abc_ClockHr() - clkProfBmc : 0 );
    Cec_ScorrProfOn = 0;
    Cec_DynSrmFree( pBmcDynSrm );
    Cec_IncrMgrFree( pBmcMgr );
    Cec_ManSimStop( pSim );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLSCorrAnalyzeDependence( Gia_Man_t * p, Vec_Int_t * vEquivs, Vec_Str_t * vStatus )
{
    Gia_Obj_t * pObj, * pObjRo;
    int i, Iter, iObj, iRepr, fPrev, Total, Count0, Count1;
    assert( Vec_StrSize(vStatus) * 2 == Vec_IntSize(vEquivs) );
    Total = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        assert( pObj->fMark1 == 0 );
        if ( Gia_ObjHasRepr(p, i) )
            Total++;
    }
    Count0 = 0;
    for ( i = 0; i < Vec_StrSize(vStatus); i++ )
    {
        iRepr = Vec_IntEntry(vEquivs, 2*i);
        iObj = Vec_IntEntry(vEquivs, 2*i+1);
        assert( iRepr == Gia_ObjRepr(p, iObj) );
        if ( Vec_StrEntry(vStatus, i) != 1 ) // disproved or undecided
        {
            Gia_ManObj(p, iObj)->fMark1 = 1;
            Count0++;
        }
    }
    for ( Iter = 0; Iter < 100; Iter++ )
    {
        int fChanges = 0;
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsCi(pObj) )
                continue;
            assert( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) );
//            fPrev = pObj->fMark1;
            if ( Gia_ObjIsAnd(pObj) )
                pObj->fMark1 |= Gia_ObjFanin0(pObj)->fMark1 | Gia_ObjFanin1(pObj)->fMark1;
            else
                pObj->fMark1 |= Gia_ObjFanin0(pObj)->fMark1;
//            fChanges += fPrev ^ pObj->fMark1;
        }
        Gia_ManForEachRiRo( p, pObj, pObjRo, i )
        {
            fPrev = pObjRo->fMark1;
            pObjRo->fMark1 = pObj->fMark1;
            fChanges += fPrev ^ pObjRo->fMark1;
        }
        if ( fChanges == 0 )
            break;
    }
    Count1 = 0;
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( pObj->fMark1 && Gia_ObjHasRepr(p, i) )
            Count1++;
        pObj->fMark1 = 0;
    }
    printf( "%5d -> %5d (%3d)  ", Count0, Count1, Iter );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks incrementally skipped SRM outputs without a conflict limit.]

  Description [Uses a fresh SAT manager, so shadow learned clauses and
  solve order cannot affect the active solver.  Returns 1 iff every
  skipped output is UNSAT.  On SAT or UNKNOWN, prints the failing pair
  and the available counterexample assignments.]

  SideEffects []

  SeeAlso     [Gia_ManCorrSpecReduce_Emit]

***********************************************************************/
static int Cec_ManIncrOracleCheck( Gia_Man_t * pSrm, Vec_Int_t * vOutputs, int iIter )
{
    Cec_ParSat_t ParsSat;
    Vec_Str_t * vStatus = NULL;
    Vec_Int_t * vCexStore;
    int i, iStart, iChosen = -1, iChosenLits = -1;
    int Out, nLits, Lit, iRepr, iObj, nSat = 0, nUnknown = 0;
    int fProf = Cec_ScorrProfOn;
    assert( Vec_IntSize(vOutputs) == 2 * Gia_ManCoNum(pSrm) );
    Cec_ManSatSetDefaultParams( &ParsSat );
    ParsSat.nBTLimit = 0;
    ParsSat.fVerbose = 0;
    Cec_ScorrProfOn = 0;
    vCexStore = Cec_ManSatSolveMiter( pSrm, &ParsSat, &vStatus );
    Cec_ScorrProfOn = fProf;
    Vec_StrForEachEntry( vStatus, Lit, i )
    {
        nSat     += Lit == 0;
        nUnknown += Lit == -1;
    }
    if ( nSat == 0 && nUnknown == 0 )
    {
        Abc_Print( 1, "  [incr-oracle r=%d PASS skipped=%d all-UNSAT]\n",
                   iIter, Gia_ManCoNum(pSrm) );
        Vec_IntFree( vCexStore );
        Vec_StrFree( vStatus );
        return 1;
    }
    // Prefer a concrete SAT counterexample over UNKNOWN if both occurred.
    iStart = 0;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        int iEntry = iStart;
        Out = Vec_IntEntry( vCexStore, iStart++ );
        nLits = Vec_IntEntry( vCexStore, iStart++ );
        if ( iChosen == -1 || nLits >= 0 )
        {
            iChosen = iEntry;
            iChosenLits = iStart;
        }
        if ( nLits >= 0 )
            break;
        assert( nLits == -1 );
    }
    assert( iChosen >= 0 );
    Out = Vec_IntEntry( vCexStore, iChosen );
    nLits = Vec_IntEntry( vCexStore, iChosen + 1 );
    iRepr = Vec_IntEntry( vOutputs, 2*Out );
    iObj  = Vec_IntEntry( vOutputs, 2*Out + 1 );
    Abc_Print( -1, "\nINCR-ORACLE %s: round=%d output=%d pair=(%d,%d), SAT=%d UNKNOWN=%d\n",
               nLits >= 0 ? "BUG" : "UNKNOWN", iIter, Out, iRepr, iObj, nSat, nUnknown );
    if ( nLits >= 0 )
    {
        Abc_Print( -1, "Partial CEX over shadow-SRM CIs (%d assignments):", nLits );
        for ( i = 0; i < Abc_MinInt(nLits, 16); i++ )
        {
            Lit = Vec_IntEntry( vCexStore, iChosenLits + i );
            Abc_Print( -1, " ci%d=%d", Abc_Lit2Var(Lit), !Abc_LitIsCompl(Lit) );
        }
        if ( nLits > 16 )
            Abc_Print( -1, " ..." );
        Abc_Print( -1, "\n" );
    }
    Vec_IntFree( vCexStore );
    Vec_StrFree( vStatus );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Internal procedure for register correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManLSCorrespondenceClasses( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{  
    int nIterMax     = 100000;
    int nAddFrames   = 1; // additional timeframes to simulate
    int fRunBmcFirst = 1;
    Vec_Str_t * vStatus;
    Vec_Int_t * vOutputs;
    Vec_Int_t * vCexStore;
    Cec_ParSim_t ParsSim, * pParsSim = &ParsSim;
    Cec_ParSat_t ParsSat, * pParsSat = &ParsSat;
    Cec_ManSim_t * pSim;
    Gia_Man_t * pSrm;
    int r, RetValue, nPrev[4] = {0};
    int fCertFailed = 0;
    abctime clkTotal = Abc_Clock();
    abctime clkSat = 0, clkSim = 0, clkSrm = 0;
    abctime clk2, clk = Abc_Clock();
    // Incremental active-list manager (NULL if -i not set)
    Cec_IncrMgr_t * pMgr = NULL;
    // Persistent dynamic SRM construction manager (NULL without -D).
    // Resimulation is controlled only by -I: without -I, counterexamples are
    // replayed by the original host-AIG resimulation path.
    Cec_DynSrm_t * pDynSrm = NULL;
    int fPersist = 0;          // -D + circuit-SAT: solve persistent pCore directly
    // Unified CEX event-resimulation manager (NULL if -I not set).
    Cec_SeedSim_t * pSeedSim = NULL;
    abctime clkIncr = 0;
    int nIncrSkipped = 0, nIncrFallback = 0;
    // fine-grained profiling (-w only); zero-cost when fVeryVerbose is off
    Cec_ScorrProf_t Prof, Total; abctime tWall0 = 0, tH = 0;
    abctime clkProfClasses = pPars->pProfile ? Abc_ClockHr() : 0;
    abctime clkProfInit = clkProfClasses, clkProfInd = 0;
    memset( &Total, 0, sizeof(Total) );
    // The hook is enabled only around correspondence-owned solver calls, so
    // a later standalone CBS/TAS invocation cannot inherit this budget.
    Cec_ScorrConfLimit = 0;
    Cec_ScorrConfUsed  = 0;
    Cec_ScorrConfStop  = 0;
    pPars->nConfUsed   = 0;
    pPars->fConfStop   = 0;
    pPars->fIncomplete = 0;
    pPars->fCompleted  = 0;
    pPars->nRoundsDone = 0;
    if ( Gia_ManRegNum(pAig) == 0 )
    {
        Abc_Print( 1, "Cec_ManLatchCorrespondence(): Not a sequential AIG.\n" );
        return 0;
    }
    if ( pPars->pProfile )
        pPars->pProfile->nCalls++;
    Gia_ManRandom( 1 );
    // prepare simulation manager
    Cec_ManSimSetDefaultParams( pParsSim );
    pParsSim->nWords     = pPars->nWords;
    pParsSim->nFrames    = pPars->nFrames;
    pParsSim->fVerbose   = pPars->fVerbose;
    pParsSim->fLatchCorr = pPars->fLatchCorr;
    pParsSim->fConstCorr = pPars->fConstCorr;
    pParsSim->fSeqSimulate = 1;
    // create equivalence classes of registers
    pSim = Cec_ManSimStart( pAig, pParsSim );
    if ( pAig->pReprs == NULL )
    {
        Cec_ManSimClassesPrepare( pSim, pPars->nLevelMax );
        Cec_ManSimClassesRefine( pSim );
    }
    // prepare SAT solving
    Cec_ManSatSetDefaultParams( pParsSat );
    pParsSat->nBTLimit = pPars->nBTLimit;
    pParsSat->fVerbose = pPars->fVerbose;
    // limit the number of conflicts in the circuit-based solver
    if ( pPars->fUseCSat )
        pParsSat->nBTLimit = Abc_MinInt( pParsSat->nBTLimit, 1000 );
    if ( pPars->pProfile )
        pPars->pProfile->timeInit += Abc_ClockHr() - clkProfInit;
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "Obj = %7d. And = %7d. Conf = %5d. Fr = %d. Lcorr = %d. Ring = %d. CSat = %d. Oracle = %d. Dyn = %d. DynAdapt = %d. IncrFb = %d%%. DynRb = %d%%. DynCmp = %dx.\n",
            Gia_ManObjNum(pAig), Gia_ManAndNum(pAig), 
            pPars->nBTLimit, pPars->nFrames, pPars->fLatchCorr, pPars->fUseRings, pPars->fUseCSat, pPars->fIncrOracle, pPars->fDynSrm, pPars->fDynSrm && !pPars->fDynSrmNoAdapt, pPars->nIncrFallbackPct, pPars->nDynSrmRebuildPct, pPars->nDynSrmCompactMult );
        Cec_ManRefinedClassPrintStats( pAig, NULL, 0, Abc_Clock() - clk );
    }
    // check the base case
    if ( fRunBmcFirst && (!pPars->fLatchCorr || pPars->nFrames > 1) )
        Cec_ManLSCorrespondenceBmc( pAig, pPars, 0 );
    if ( Cec_ParCorShouldStop( pPars ) )
    {
        pPars->fIncomplete = 1;
        Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, 0 );
        Cec_ManSimStop( pSim );
        return 1;
    }
    if ( pPars->nStepsMax == 0 )
    {
        pPars->fIncomplete = 1;
        Abc_Print( 1, "Stopped signal correspondence after BMC.\n" );
        Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, 0 );
        Cec_ManSimStop( pSim );
        return 1;
    }
    // Initialise incremental manager (after BMC, before main refinement loop).
    // Works with both SAT and CBS solver paths: the active-list filter just
    // reduces the number of POs in the SRM, and both solvers iterate POs.
    if ( pPars->fIncremental )
    {
        pMgr = Cec_IncrMgrAlloc( pAig, pPars->nFrames );
        Cec_IncrMgrSnapshotClasses( pMgr );  // initial snapshot (post-BMC classes)
    }
    if ( pPars->fDynSrm && pMgr )
    {
        pDynSrm = Cec_DynSrmAlloc( pAig, pMgr, !pPars->fDynSrmNoAdapt );
        Cec_DynSrmSetParams( pDynSrm, pPars );
    }
    // -D persistence path: solve the persistent COless pCore directly (circuit
    // SAT only), skipping the per-round throwaway view that BuildView copies.
    fPersist = ( pDynSrm != NULL && pPars->fUseCSat );
    // Resident local-sim manager sized for the main-loop resim depth.
    if ( pPars->fIncrSim )
    {
        pSeedSim = Cec_SeedSimAlloc( pAig, pPars->nFrames + 1 + nAddFrames, pPars->nFrames, pParsSim->nWords );
        pSeedSim->fVerify = pPars->fVerifyResim;
    }
    Cec_ScorrProfOn = pPars->fVeryVerbose || pPars->pProfile != NULL;
    clkProfInd = pPars->pProfile ? Abc_ClockHr() : 0;
    // perform refinement of equivalence classes
    for ( r = 0; r < nIterMax; r++ )
    {
        if ( Cec_ParCorShouldStop( pPars ) )
        {
            pPars->fIncomplete = 1;
            Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
            Cec_ManSimStop( pSim );
            Cec_DynSrmFree( pDynSrm );
            Cec_IncrMgrFree( pMgr );
            Cec_SeedSimFree( pSeedSim );
            return 1;
        }
        if ( pPars->nStepsMax == r )
        {
            pPars->fIncomplete = 1;
            Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
            Cec_ManSimStop( pSim );
            Cec_DynSrmFree( pDynSrm );
            Cec_IncrMgrFree( pMgr );
            Cec_SeedSimFree( pSeedSim );
            Abc_Print( 1, "Stopped signal correspondence after %d refiment iterations.\n", r );
            return 1;
        }
        clk = Abc_Clock();
        tWall0 = Abc_ClockHr();
        memset( &Prof, 0, sizeof(Prof) );
        // perform speculative reduction (with optional active-list filter)
        clk2 = Abc_Clock();
        {
            int * pTfoMask = NULL;
            int nReprSeeds = 0, nNextChanges = 0;
            int nTotalPairs = 0, nActivePairs = 0;
            int fStopAfterOracle = 0;
            // Decide whether to apply incremental TFO mask this iteration.
            // Skip on r==0 because the first full SRM establishes the cache.
            if ( pMgr && r > 0 )
            {
                abctime clkI = Abc_Clock();
                tH = Abc_ClockHr();
                nReprSeeds = Cec_IncrMgrComputeSeeds( pMgr );
                Prof.tSeed = Abc_ClockHr() - tH;
                tH = Abc_ClockHr();
                nNextChanges = pPars->fUseRings ? Cec_IncrMgrCountNextChanges( pMgr ) : 0;
                Prof.tNext = Abc_ClockHr() - tH;
                if ( nReprSeeds == 0 && nNextChanges == 0 )
                {
                    if ( !pPars->fIncrOracle )
                    {
                        // No class-state change since the full/active SRM just
                        // proved these pairs; this is true convergence.
                        clkIncr += Abc_Clock() - clkI;
                        clkSrm  += Abc_Clock() - clk2;
                        break;
                    }
                    // Clear the previous TFO marks.  The skipped complement is
                    // now every current pair, providing a final certificate.
                    tH = Abc_ClockHr();
                    Cec_IncrMgrComputeTfo( pMgr );
                    Prof.tTfo = Abc_ClockHr() - tH;
                    tH = Abc_ClockHr();
                    if ( pDynSrm )
                        Cec_DynSrmCountActivePairs( pDynSrm, pPars->fUseRings, pMgr->pTfoMark, &nTotalPairs, &nActivePairs );
                    else
                        Cec_IncrMgrCountActivePairs( pMgr, pPars->fUseRings, pMgr->pTfoMark, &nTotalPairs, &nActivePairs );
                    Prof.tCnt = Abc_ClockHr() - tH;
                    assert( nActivePairs == 0 );
                    pTfoMask = pMgr->pTfoMark;
                    nIncrSkipped += nTotalPairs;
                    fStopAfterOracle = 1;
                }
                else
                {
                    tH = Abc_ClockHr();
                    Cec_IncrMgrComputeTfo( pMgr );
                    Prof.tTfo = Abc_ClockHr() - tH;
                    tH = Abc_ClockHr();
                    if ( pDynSrm )
                        Cec_DynSrmCountActivePairs( pDynSrm, pPars->fUseRings, pMgr->pTfoMark, &nTotalPairs, &nActivePairs );
                    else
                        Cec_IncrMgrCountActivePairs( pMgr, pPars->fUseRings, pMgr->pTfoMark, &nTotalPairs, &nActivePairs );
                    Prof.tCnt = Abc_ClockHr() - tH;
                    if ( nActivePairs == 0 )
                    {
                        if ( !pPars->fIncrOracle )
                        {
                            // Classes changed, but no remaining candidate pair
                            // depends on the changes and no new ring edge exists.
                            clkIncr += Abc_Clock() - clkI;
                            clkSrm  += Abc_Clock() - clk2;
                            break;
                        }
                        pTfoMask = pMgr->pTfoMark;
                        nIncrSkipped += nTotalPairs;
                        fStopAfterOracle = 1;
                    }
                    else
                    {
                        int fIncrFallback = nTotalPairs > 0 &&
                            (ABC_INT64_T)100 * nActivePairs > (ABC_INT64_T)pPars->nIncrFallbackPct * nTotalPairs;
                        int fDynRebuild = nTotalPairs > 0 &&
                            (ABC_INT64_T)100 * nActivePairs > (ABC_INT64_T)pPars->nDynSrmRebuildPct * nTotalPairs;
                        if ( pDynSrm && (fIncrFallback || fDynRebuild) )
                            Cec_DynSrmForceRebuild( pDynSrm, fIncrFallback );
                        // Fallback is based on emitted candidate pairs, not seed count.
                        // Above the configured -A percentage, full SRM is usually cheaper.
                        if ( fIncrFallback )
                            nIncrFallback++;
                        else
                        {
                            pTfoMask = pMgr->pTfoMark;
                            nIncrSkipped += nTotalPairs - nActivePairs;
                        }
                    }
                }
                clkIncr += Abc_Clock() - clkI;
            }

            if ( pTfoMask && pPars->fIncrOracle )
            {
                Gia_Man_t * pShadow;
                Vec_Int_t * vShadowOutputs;
                tH = Abc_ClockHr();
                if ( pDynSrm )
                    pShadow = Cec_DynSrmBuild( pDynSrm, pPars->nFrames, !pPars->fLatchCorr,
                        &vShadowOutputs, pPars->fUseRings, pTfoMask, CEC_EMIT_SKIPPED );
                else
                    pShadow = Gia_ManCorrSpecReduce_Emit( pAig, pPars->nFrames, !pPars->fLatchCorr,
                        &vShadowOutputs, pPars->fUseRings, pTfoMask, pMgr, CEC_EMIT_SKIPPED, NULL );
                if ( Gia_ManCoNum(pShadow) > 0 &&
                     !Cec_ManIncrOracleCheck( pShadow, vShadowOutputs, r ) )
                {
                    pPars->fIncomplete = 1;
                    Gia_ManStop( pShadow );
                    Vec_IntFree( vShadowOutputs );
                    Cec_ManSimStop( pSim );
                    Cec_DynSrmFree( pDynSrm );
                    Cec_IncrMgrFree( pMgr );
                    Cec_SeedSimFree( pSeedSim );
                    Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
                    Cec_ScorrProfOn = 0;
                    return 0;
                }
                if ( Gia_ManCoNum(pShadow) == 0 )
                    Abc_Print( 1, "  [incr-oracle r=%d PASS skipped=0 after-simplification]\n", r );
                Gia_ManStop( pShadow );
                Vec_IntFree( vShadowOutputs );
                if ( pPars->fVeryVerbose )
                    Abc_Print( 1, "  [incr-oracle r=%d checked=%d build+solve=%.3f sec]\n",
                               r, nTotalPairs - nActivePairs, 1.0e-9 * (Abc_ClockHr() - tH) );
            }
            if ( fStopAfterOracle )
            {
                clkSrm += Abc_Clock() - clk2;
                break;
            }

            tH = Abc_ClockHr();
            // -D persistence under circuit-SAT: build the COless pCore and solve
            // its root literals directly below; skip the per-round throwaway view.
            if ( fPersist )
            {
                Cec_DynSrmBuildCore( pDynSrm, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings, pTfoMask, pTfoMask ? CEC_EMIT_ACTIVE : CEC_EMIT_ALL );
                pSrm = NULL;
            }
            else if ( pDynSrm )
                pSrm = Cec_DynSrmBuild( pDynSrm, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings, pTfoMask, pTfoMask ? CEC_EMIT_ACTIVE : CEC_EMIT_ALL );
            else if ( pTfoMask )
                pSrm = Gia_ManCorrSpecReduce_Emit( pAig, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings, pTfoMask, pMgr, CEC_EMIT_ACTIVE, NULL );
            else
                pSrm = Gia_ManCorrSpecReduce( pAig, pPars->nFrames, !pPars->fLatchCorr, &vOutputs, pPars->fUseRings, NULL );
            Prof.tSrm = Abc_ClockHr() - tH;
            if ( pTfoMask && pPars->fVeryVerbose )
                Abc_Print( 1, "[scorr2-profile] stage=refine frontier iter=%d repr_changes=%d ring_changes=%d tfo_nodes=%d active_pairs=%d/%d roots=%d\n",
                           r, nReprSeeds, nNextChanges,
                           Vec_IntSize(pMgr->vTfoNodes), nActivePairs, nTotalPairs,
                           fPersist ? Vec_IntSize(Cec_DynSrmOutLits(pDynSrm)) : Gia_ManCoNum(pSrm) );
            // Snapshot after SRM construction: the active builder still needs
            // the old pNexts snapshot to recognize newly-created ring edges.
            // SAT/sim refinement below is what creates the next iteration's diff.
            if ( pMgr )
            {
                tH = Abc_ClockHr();
                Cec_IncrMgrSnapshotClasses( pMgr );
                Prof.tSnap = Abc_ClockHr() - tH;
            }
        }
        assert( fPersist || (Gia_ManRegNum(pSrm) == 0 && Gia_ManPiNum(pSrm) == Gia_ManRegNum(pAig)+(pPars->nFrames+!pPars->fLatchCorr)*Gia_ManPiNum(pAig)) );
        clkSrm += Abc_Clock() - clk2;
        if ( (fPersist ? Vec_IntSize(Cec_DynSrmOutLits(pDynSrm)) : Gia_ManCoNum(pSrm)) == 0 )
        {
            Vec_IntFree( vOutputs );
            if ( pSrm )
                Gia_ManStop( pSrm );
            break;
        }
//Gia_DumpAiger( pSrm, "corrsrm", r, 2 );
        // found counter-examples to speculation
        clk2 = Abc_Clock();
        tH = Abc_ClockHr();
        Cec_ScorrConfLimit = pPars->nConfTotal;
        if ( fPersist )
            vCexStore = Cec_DynSrmSolve( pDynSrm, pPars->nBTLimit, &vStatus, 0 );
        else if ( pPars->fUseCSat )
            vCexStore = Cbs_ManSolveMiterNc( pSrm, pPars->nBTLimit, &vStatus, 0, 0 );
        else
            vCexStore = Cec_ManSatSolveMiter( pSrm, pParsSat, &vStatus );
        Cec_ScorrConfLimit = 0;
        Prof.tSat = Abc_ClockHr() - tH;
        Cec_ProfCorCountStatus( pPars, vStatus, 0 );
        Prof.tSatSetup = Cec_ScorrProfSetup; Prof.tSatSolve = Cec_ScorrProfSolve;
        Prof.tSatMax   = Cec_ScorrProfMax;   Prof.nSatCalls = Cec_ScorrProfCalls;
        if ( pSrm )
            Gia_ManStop( pSrm );
        clkSat += Abc_Clock() - clk2;
        if ( Vec_IntSize(vCexStore) == 0 )
        {
            if ( pDynSrm )
                Cec_DynSrmRecordSolveStats( pDynSrm, Prof.nSatCalls, 0, 0, 0, Prof.tSat );
            Vec_IntFree( vCexStore );
            Vec_StrFree( vStatus );
            Vec_IntFree( vOutputs );
            Prof.tWall = Abc_ClockHr() - tWall0;
            if ( pPars->fVeryVerbose )
                Cec_ScorrProfPrint( "refine", r+1, Prof.nSatCalls, &Prof );
            Cec_ScorrProfAdd( &Total, &Prof );
            break;
        }
//        Cec_ManLSCorrAnalyzeDependence( pAig, vOutputs, vStatus );        

        // refine classes with these counter-examples
        clk2 = Abc_Clock();
        {
            int nLitsPre = 0, nLitsMid = 0, nLitsPost = 0;
            Cec_ManCexStoreClassify( vCexStore, &Prof.nCexReal, &Prof.nCexTriv, &Prof.nCexFail );
            if ( pDynSrm )
                Cec_DynSrmRecordSolveStats( pDynSrm, Prof.nSatCalls,
                    Prof.nCexReal, Prof.nCexTriv, Prof.nCexFail, Prof.tSat );
            if ( Cec_ScorrProfOn ) nLitsPre = Gia_ManEquivCountLitsAll( pAig );
            if ( Prof.nCexReal > 0 || !pPars->fSkipFailResim )
            {
                tH = Abc_ClockHr();
                RetValue = Cec_ManResimulateCounterExamples( pSim,
                    vCexStore, pPars->nFrames + 1 + nAddFrames,
                    pSeedSim, vOutputs, pPars, 1 );
                Prof.tSim = Abc_ClockHr() - tH;
                Prof.nSimCalls = 1;
                Prof.tSimRemap = Cec_ScorrProfSimRemap; Prof.tSimRun = Cec_ScorrProfSimRun;
                Prof.nIncrSrc = Cec_ScorrProfIncrSrc; Prof.nIncrFull = Cec_ScorrProfIncrFull;
                Prof.nIncrTrunc = Cec_ScorrProfIncrTrunc;
                Prof.nIncrRollback = Cec_ScorrProfIncrRollback;
                Prof.nIncrRollbackObjs = Cec_ScorrProfIncrRollbackObjs;
                Prof.nIncrCoverageMiss = Cec_ScorrProfIncrCoverageMiss;
                Prof.nIncrFallbackPre = Cec_ScorrProfIncrFallbackPre;
                Prof.nIncrFallbackProcess = Cec_ScorrProfIncrFallbackProcess;
                Prof.nIncrFallbackCoverage = Cec_ScorrProfIncrFallbackCoverage;
                Prof.nIncrFallbackCex = Cec_ScorrProfIncrFallbackCex;
                Prof.nIncrFallbackBypass = Cec_ScorrProfIncrFallbackBypass;
                Prof.nIncrTruncCone = Cec_ScorrProfIncrTruncCone;
                Prof.nIncrTruncEval = Cec_ScorrProfIncrTruncEval;
                Prof.nIncrBatchCex = Cec_ScorrProfIncrBatchCex;
                Prof.nIncrBatchCexMax = Cec_ScorrProfIncrBatchCexMax;
                Prof.nIncrDeferred = Cec_ScorrProfIncrDeferred;
                Prof.nIncrDirty = Cec_ScorrProfIncrDirty;
                Prof.nIncrConeKeys = Cec_ScorrProfIncrConeKeys;
                Prof.nIncrKeys = Cec_ScorrProfIncrKeys;
                Prof.tIncrTry = Cec_ScorrProfIncrTry;
                Prof.tIncrTryLocal = Cec_ScorrProfIncrTryLocal;
                Prof.tIncrTryFallback = Cec_ScorrProfIncrTryFallback;
                Prof.tIncrFullRun = Cec_ScorrProfIncrFullRun;
                Prof.tIncrDiagShape = Cec_ScorrProfIncrDiagShape;
                Prof.tIncrDiagCollect = Cec_ScorrProfIncrDiagCollect;
                Prof.tIncrDiagEval = Cec_ScorrProfIncrDiagEval;
                Prof.tIncrDiagSim = Cec_ScorrProfIncrDiagSim;
                Prof.tIncrTfoBuild = Cec_ScorrProfIncrTfoBuild;
                Prof.tIncrTfoSim = Cec_ScorrProfIncrTfoSim;
                Prof.tIncrTxn = Cec_ScorrProfIncrTxn;
                Prof.nEventLocal = Cec_ScorrProfEventLocal;
                Prof.nEventFallback = Cec_ScorrProfEventFallback;
                Prof.nEventPopsMax = Cec_ScorrProfEventPopsMax;
                Prof.nEventEdgesMax = Cec_ScorrProfEventEdgesMax;
                Prof.nEventInputVarsMax = Cec_ScorrProfEventInputVarsMax;
                Prof.nEventInputWordsMax = Cec_ScorrProfEventInputWordsMax;
                Prof.nEventFallbackWork = Cec_ScorrProfEventFallbackWork;
                Prof.nEventFallbackTime = Cec_ScorrProfEventFallbackTime;
                Prof.nIncrAdaptLocal = Cec_ScorrProfIncrAdaptLocal;
                Prof.nIncrAdaptFail = Cec_ScorrProfIncrAdaptFail;
                Prof.nIncrAdaptTrips = Cec_ScorrProfIncrAdaptTrips;
                Prof.nIncrAdaptCooldown = Cec_ScorrProfIncrAdaptCooldown;
                Prof.tEventLoad = Cec_ScorrProfEventLoad;
                Prof.tEventProp = Cec_ScorrProfEventProp;
                Prof.tEventRefine = Cec_ScorrProfEventRefine;
                Prof.tEventRollback = Cec_ScorrProfEventRollback;
                Prof.tEventInit = Cec_ScorrProfEventInit;
            }
            if ( Prof.nCexTriv > 0 )
                Prof.nTrivSplits = Cec_ManTrivialSatSplit( pAig, pSim, vCexStore, vStatus, vOutputs, pPars->fUseRings );
            Vec_IntFree( vCexStore );
            clkSim += Abc_Clock() - clk2;
            if ( Cec_ScorrProfOn ) nLitsMid = Gia_ManEquivCountLitsAll( pAig );
            tH = Abc_ClockHr();
            Prof.nCexPending = Gia_ManCheckRefinements( pAig, vStatus, vOutputs, pSim, pPars->fUseRings );
            Prof.tChk = Abc_ClockHr() - tH;
            if ( Cec_ScorrProfOn ) nLitsPost = Gia_ManEquivCountLitsAll( pAig );
            Prof.dSimLits = nLitsPre - nLitsMid;
            Prof.dChkLits = nLitsMid - nLitsPost;
        }
        if ( pPars->fVerbose )
        {
            tH = Abc_ClockHr();
            Cec_ManRefinedClassPrintStats( pAig, vStatus, r+1, Abc_Clock() - clk );
            Prof.tStats = Abc_ClockHr() - tH;
        }
        Prof.tWall = Abc_ClockHr() - tWall0;
        if ( pPars->fVeryVerbose )
            Cec_ScorrProfPrint( "refine", r+1, Prof.nSatCalls, &Prof );
        Cec_ScorrProfAdd( &Total, &Prof );
        Vec_StrFree( vStatus );
        Vec_IntFree( vOutputs );
//Gia_ManEquivPrintClasses( pAig, 1, 0 );
        if ( Cec_ParCorShouldStop( pPars ) )
        {
            pPars->fIncomplete = 1;
            Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
            Cec_ManSimStop( pSim );
            Cec_DynSrmFree( pDynSrm );
            Cec_IncrMgrFree( pMgr );
            Cec_SeedSimFree( pSeedSim );
            return 1;
        }
        // quit if const is no longer there
        if ( pPars->fStopWhenGone && Gia_ManPoNum(pAig) == 1 && !Gia_ObjIsConst( pAig, Gia_ObjFaninId0p(pAig, Gia_ManPo(pAig, 0)) ) )
        {
            pPars->fIncomplete = 1;
            printf( "Iterative refinement is stopped after iteration %d\n", r );
            printf( "because the property output is no longer a candidate constant.\n" );
            Cec_ManSimStop( pSim );
            Cec_DynSrmFree( pDynSrm );
            Cec_IncrMgrFree( pMgr );
            Cec_SeedSimFree( pSeedSim );
            Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
            return 0;
        }
        if ( pPars->nLimitMax )
        {
            int nCur = Cec_ManCountLits(pAig);
            if ( r > 4 && nPrev[0] - nCur <= 4*pPars->nLimitMax )
            {
                pPars->fIncomplete = 1;
                printf( "Iterative refinement is stopped after iteration %d\n", r );
                printf( "because refinement does not proceed quickly.\n" );
                Cec_ManSimStop( pSim );
                Cec_DynSrmFree( pDynSrm );
                Cec_IncrMgrFree( pMgr );
                Cec_SeedSimFree( pSeedSim );
                ABC_FREE( pAig->pReprs );
                ABC_FREE( pAig->pNexts );
                Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
                return 0;
            }
            nPrev[0] = nPrev[1];
            nPrev[1] = nPrev[2];
            nPrev[2] = nPrev[3];
            nPrev[3] = nCur;
        }
    }
    // Optional strict final oracle.  The ordinary loop may stop because an
    // incremental frontier is empty; rebuild the complete current SRM here so
    // no skipped pair can escape the audit.  This is deliberately a checker,
    // not a repair pass: SAT means the optimized run produced a wrong fixed
    // point, so report the bug and refuse to create a reduced network.
    if ( pPars->fKissatCert && r < nIterMax )
    {
        Vec_Int_t * vCertOutputs = NULL, * vCertCex = NULL;
        Vec_Str_t * vCertStatus = NULL;
        Gia_Man_t * pCertSrm;
        int iCertOut = -1, CertStatus;
        if ( Cec_ParCorShouldStop(pPars) )
            fCertFailed = 1;
        else
        {
            Abc_Print( 1, "[scorr2-audit] phase=inductive-step status=running\n" );
            pCertSrm = Gia_ManCorrSpecReduce( pAig, pPars->nFrames,
                !pPars->fLatchCorr, &vCertOutputs, pPars->fUseRings, NULL );
            CertStatus = Cec_ManCorrKissatCertify( pCertSrm, vCertOutputs,
                &vCertCex, &vCertStatus, &iCertOut, 1 );
            Gia_ManStop( pCertSrm );
            if ( CertStatus != 1 )
            {
                fCertFailed = 1;
                if ( CertStatus == 0 )
                    Abc_Print( -1, "[scorr2-audit] phase=inductive-step status=failed reason=non-inductive-equivalence\n" );
                else
                    Abc_Print( -1, "[scorr2-audit] phase=inductive-step status=unknown\n" );
            }
            Vec_IntFree( vCertCex );
            Vec_StrFree( vCertStatus );
            Vec_IntFree( vCertOutputs );
            vCertCex = NULL;
            vCertStatus = NULL;
            vCertOutputs = NULL;

            // Audit the base/init obligations on the final classes as well.
            // This is required to catch bugs in the optimized BMC phase; an
            // inductive relation alone need not hold in the initial behavior.
            if ( !fCertFailed )
            {
                iCertOut = -1;
                Abc_Print( 1, "[scorr2-audit] phase=base status=running\n" );
                pCertSrm = Gia_ManCorrSpecReduceInit( pAig, pPars->nFrames, 0,
                    !pPars->fLatchCorr, &vCertOutputs, pPars->fUseRings );
                CertStatus = Cec_ManCorrKissatCertify( pCertSrm, vCertOutputs,
                    &vCertCex, &vCertStatus, &iCertOut, 1 );
                Gia_ManStop( pCertSrm );
                if ( CertStatus != 1 )
                {
                    fCertFailed = 1;
                    if ( CertStatus == 0 )
                        Abc_Print( -1, "[scorr2-audit] phase=base status=failed reason=false-equivalence\n" );
                    else
                        Abc_Print( -1, "[scorr2-audit] phase=base status=unknown\n" );
                }
                Vec_IntFree( vCertCex );
                Vec_StrFree( vCertStatus );
                Vec_IntFree( vCertOutputs );
            }
            if ( !fCertFailed )
                Abc_Print( 1, "[scorr2-audit] status=pass obligations=base+inductive-step\n" );
            else
                Abc_Print( -1, "[scorr2-audit] status=failed action=reject-reduction\n" );
        }
    }
    if ( fCertFailed )
    {
        pPars->fIncomplete = 1;
        Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
        Cec_ScorrProfOn = 0;
        Cec_ManSimStop( pSim );
        Cec_IncrMgrFree( pMgr );
        Cec_DynSrmFree( pDynSrm );
        Cec_SeedSimFree( pSeedSim );
        return 0;
    }
    if ( pPars->fVerbose )
        Cec_ManRefinedClassPrintStats( pAig, NULL, r+1, Abc_Clock() - clk );
    if ( pPars->fVeryVerbose )
        Cec_ScorrProfPrint( "refine", -1, Total.nSatCalls, &Total );
    Cec_ProfCorFinishClasses( pPars, &Total, clkProfClasses, clkProfInd );
    Cec_ScorrProfOn = 0;
    // check the overflow
    if ( r == nIterMax )
        Abc_Print( 1, "The refinement was not finished. The result may be incorrect.\n" );
    Cec_ManSimStop( pSim );
    // check the base case
    if ( !fRunBmcFirst && (!pPars->fLatchCorr || pPars->nFrames > 1) )
        Cec_ManLSCorrespondenceBmc( pAig, pPars, 0 );
    clkTotal = Abc_Clock() - clkTotal;
    // report the results
    if ( pPars->fVerbose )
    {
        ABC_PRTP( "Srm  ", clkSrm,                        clkTotal );
        ABC_PRTP( "Sat  ", clkSat,                        clkTotal );
        ABC_PRTP( "Sim  ", clkSim,                        clkTotal );
        ABC_PRTP( "Other", clkTotal-clkSat-clkSrm-clkSim, clkTotal );
        if ( pMgr )
        {
            ABC_PRTP( "Incr ", clkIncr, clkTotal );
            Abc_Print( 1, "Incr: fallback rounds = %d, skipped candidate pairs = %d\n", nIncrFallback, nIncrSkipped );
        }
        Abc_PrintTime( 1, "TOTAL",  clkTotal );
    }
    if ( pPars->fVeryVerbose && pDynSrm )
        Cec_DynSrmPrintStats( pDynSrm );
    Cec_IncrMgrFree( pMgr );
    Cec_DynSrmFree( pDynSrm );
    Cec_SeedSimFree( pSeedSim );
    // Match ordinary &scorr semantics: SAT counterexamples refine the affected
    // classes, per-output UNKNOWN removes only its emitted candidate, and UNSAT
    // retains the relation.  Other classes continue through the fixed-point
    // loop.  fCompleted reports convergence and must not be cleared merely
    // because one solver output was UNKNOWN.
    pPars->fCompleted = !pPars->fIncomplete && r < nIterMax;
    pPars->nRoundsDone = r + 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes new initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Cec_ManComputeInitState( Gia_Man_t * pAig, int nFrames )
{  
    Gia_Obj_t * pObj, * pObjRo, * pObjRi;
    unsigned * pInitState;
    int i, f; 
    Gia_ManRandom( 1 );
//    Abc_Print( 1, "Simulating %d timeframes.\n", nFrames );
    Gia_ManForEachRo( pAig, pObj, i )
        pObj->fMark1 = 0;
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ManConst0(pAig)->fMark1 = 0;
        Gia_ManForEachPi( pAig, pObj, i )
            pObj->fMark1 = Gia_ManRandom(0) & 1;
        Gia_ManForEachAnd( pAig, pObj, i )
            pObj->fMark1 = (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) & 
                (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachRi( pAig, pObj, i )
            pObj->fMark1 = (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj));
        Gia_ManForEachRiRo( pAig, pObjRi, pObjRo, i )
            pObjRo->fMark1 = pObjRi->fMark1;
    }
    pInitState = ABC_CALLOC( unsigned, Abc_BitWordNum(Gia_ManRegNum(pAig)) );
    Gia_ManForEachRo( pAig, pObj, i )
    {
        if ( pObj->fMark1 )
            Abc_InfoSetBit( pInitState, i );
//        Abc_Print( 1, "%d", pObj->fMark1 );
    }
//    Abc_Print( 1, "\n" );
    Gia_ManCleanMark1( pAig );
    return pInitState;
}

/**Function*************************************************************

  Synopsis    [Prints flop equivalences.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPrintFlopEquivs( Gia_Man_t * p )
{
    Gia_Obj_t * pObj, * pRepr;
    int i;
    assert( p->vNamesIn != NULL );
    Gia_ManForEachRo( p, pObj, i )
    {
        if ( Gia_ObjIsConst(p, Gia_ObjId(p, pObj)) )
            Abc_Print( 1, "Original flop %s is proved equivalent to constant.\n", Vec_PtrEntry(p->vNamesIn, Gia_ObjCioId(pObj)) );
        else if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
        {
            if ( Gia_ObjIsCi(pRepr) )
                Abc_Print( 1, "Original flop %s is proved equivalent to flop %s.\n",
                    Vec_PtrEntry( p->vNamesIn, Gia_ObjCioId(pObj)  ),
                    Vec_PtrEntry( p->vNamesIn, Gia_ObjCioId(pRepr) ) );
            else
                Abc_Print( 1, "Original flop %s is proved equivalent to internal node %d.\n",
                    Vec_PtrEntry( p->vNamesIn, Gia_ObjCioId(pObj) ), Gia_ObjId(p, pRepr) );
        }
    }
}


/**Function*************************************************************

  Synopsis    [Top-level procedure for register correspondence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManLSCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{  
    Gia_Man_t * pNew, * pTemp;
    unsigned * pInitState;
    int RetValue;
    abctime clkProfReduce;
    ABC_FREE( pAig->pReprs );
    ABC_FREE( pAig->pNexts );
    if ( pPars->nPrefix == 0 )
    {
        RetValue = Cec_ManLSCorrespondenceClasses( pAig, pPars );
        if ( RetValue == 0 )
        {
            clkProfReduce = pPars->pProfile ? Abc_ClockHr() : 0;
            pNew = Gia_ManDup( pAig );
            if ( pPars->pProfile )
                pPars->pProfile->timeReduce += Abc_ClockHr() - clkProfReduce;
            return pNew;
        }
    }
    else
    {
        // compute the cycles AIG
        pInitState = Cec_ManComputeInitState( pAig, pPars->nPrefix );
        pTemp = Gia_ManDupFlip( pAig, (int *)pInitState );
        ABC_FREE( pInitState );
        // compute classes of this AIG
        RetValue = Cec_ManLSCorrespondenceClasses( pTemp, pPars );
        // transfer the class info
        pAig->pReprs = pTemp->pReprs; pTemp->pReprs = NULL;
        pAig->pNexts = pTemp->pNexts; pTemp->pNexts = NULL;
        // perform additional BMC
        pPars->fUseCSat = 0;
        pPars->nBTLimit = Abc_MaxInt( pPars->nBTLimit, 1000 );
        Cec_ManLSCorrespondenceBmc( pAig, pPars, pPars->nPrefix );
/*
        // transfer the class info back
        pTemp->pReprs = pAig->pReprs; pAig->pReprs = NULL;
        pTemp->pNexts = pAig->pNexts; pAig->pNexts = NULL;
        // continue refining
        RetValue = Cec_ManLSCorrespondenceClasses( pTemp, pPars );
        // transfer the class info
        pAig->pReprs = pTemp->pReprs; pTemp->pReprs = NULL;
        pAig->pNexts = pTemp->pNexts; pTemp->pNexts = NULL;
*/
        Gia_ManStop( pTemp );
    }
    // derive reduced AIG
    clkProfReduce = pPars->pProfile ? Abc_ClockHr() : 0;
    if ( pPars->fMakeChoices )
    {
        pNew = Gia_ManEquivToChoices( pAig, 1 );
//        Gia_ManHasChoices_very_old( pNew );
    }
    else
    {
//        Gia_ManEquivImprove( pAig );
        pNew = Gia_ManCorrReduce( pAig );
        pNew = Gia_ManSeqCleanup( pTemp = pNew );
        Gia_ManStop( pTemp );
        //Gia_AigerWrite( pNew, "reduced.aig", 0, 0, 0 );
    }
    if ( pPars->pProfile )
        pPars->pProfile->timeReduce += Abc_ClockHr() - clkProfReduce;
    // report the results
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "NBeg = %d. NEnd = %d. (Gain = %6.2f %%).  RBeg = %d. REnd = %d. (Gain = %6.2f %%).\n", 
            Gia_ManAndNum(pAig), Gia_ManAndNum(pNew), 
            100.0*(Gia_ManAndNum(pAig)-Gia_ManAndNum(pNew))/(Gia_ManAndNum(pAig)?Gia_ManAndNum(pAig):1), 
            Gia_ManRegNum(pAig), Gia_ManRegNum(pNew), 
            100.0*(Gia_ManRegNum(pAig)-Gia_ManRegNum(pNew))/(Gia_ManRegNum(pAig)?Gia_ManRegNum(pAig):1) );
    }
    if ( pPars->nPrefix && (Gia_ManAndNum(pNew) < Gia_ManAndNum(pAig) || Gia_ManRegNum(pNew) < Gia_ManRegNum(pAig)) )
        Abc_Print( 1, "The reduced AIG was produced using %d-th invariants and will not verify.\n", pPars->nPrefix );
    // print verbose info about equivalences
    if ( pPars->fVerboseFlops )
    {
        if ( pAig->vNamesIn == NULL )
            Abc_Print( 1, "Flop output names are not available. Use command \"&get -n\".\n" );
        else
            Cec_ManPrintFlopEquivs( pAig );
    }
    // copy names if present
    if ( pAig->vNamesIn )
    {
        char * pName; int i;
        pNew->vNamesIn = Vec_PtrDupStr( pAig->vNamesIn );
        Vec_PtrForEachEntryStart( char *, pNew->vNamesIn, pName, i, Gia_ManCiNum(pNew) )
            ABC_FREE( pName );
        Vec_PtrShrink( pNew->vNamesIn, Gia_ManCiNum(pNew) );
    }
    if ( pAig->vNamesOut )
    {
        char * pName; int i;
        pNew->vNamesOut = Vec_PtrDupStr( pAig->vNamesOut );
        Vec_PtrForEachEntryStart( char *, pNew->vNamesOut, pName, i, Gia_ManCoNum(pNew) )
            ABC_FREE( pName );
        Vec_PtrShrink( pNew->vNamesOut, Gia_ManCoNum(pNew) );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManStopFlopSuppAdd( int * pReg0, int * pReg1, int * pnRegs, int Reg )
{
    if ( *pnRegs == 3 )
        return;
    if ( *pnRegs == 0 )
    {
        *pReg0 = Reg;
        *pnRegs = 1;
        return;
    }
    if ( *pnRegs == 1 )
    {
        if ( *pReg0 == Reg )
            return;
        *pReg1 = Reg;
        *pnRegs = 2;
        return;
    }
    assert( *pnRegs == 2 );
    if ( *pReg0 == Reg || *pReg1 == Reg )
        return;
    *pnRegs = 3;
}
Vec_Int_t * Gia_ManFindStopFlops( Gia_Man_t * p, int nFlopIncFreq, int fVerbose )
{
    abctime clk = Abc_Clock();
    Gia_Obj_t * pObj;
    Vec_Int_t * vRes = NULL;
    Vec_Int_t * vNexts = Vec_IntStartFull( Gia_ManRegNum(p) );
    Vec_Int_t * vAvail = Vec_IntStart( Gia_ManRegNum(p) );
    Vec_Int_t * vHeads = Vec_IntAlloc( 10 );
    unsigned char * pSuppN = ABC_CALLOC( unsigned char, Gia_ManObjNum(p) );
    int * pSupp0 = ABC_ALLOC( int, Gia_ManObjNum(p) );
    int * pSupp1 = ABC_ALLOC( int, Gia_ManObjNum(p) );
    int i, k, Id, Fan0, Fan1, Count, Next, Spot, Temp, nItems = 0;

    // Track at most two distinct flop supports per node; value 3 means "many".
    Gia_ManForEachRo( p, pObj, i )
    {
        Id = Gia_ObjId( p, pObj );
        pSuppN[Id] = 1;
        pSupp0[Id] = i;
    }
    Gia_ManForEachAnd( p, pObj, Id )
    {
        int Reg0 = -1, Reg1 = -1, nRegs = 0;
        Fan0 = Gia_ObjFaninId0( pObj, Id );
        Fan1 = Gia_ObjFaninId1( pObj, Id );
        if ( pSuppN[Fan0] == 3 || pSuppN[Fan1] == 3 )
        {
            pSuppN[Id] = 3;
            continue;
        }
        if ( pSuppN[Fan0] > 0 )
        {
            Gia_ManStopFlopSuppAdd( &Reg0, &Reg1, &nRegs, pSupp0[Fan0] );
            if ( pSuppN[Fan0] > 1 )
                Gia_ManStopFlopSuppAdd( &Reg0, &Reg1, &nRegs, pSupp1[Fan0] );
        }
        if ( pSuppN[Fan1] > 0 )
        {
            Gia_ManStopFlopSuppAdd( &Reg0, &Reg1, &nRegs, pSupp0[Fan1] );
            if ( pSuppN[Fan1] > 1 )
                Gia_ManStopFlopSuppAdd( &Reg0, &Reg1, &nRegs, pSupp1[Fan1] );
        }
        pSuppN[Id] = nRegs;
        if ( nRegs > 0 )
            pSupp0[Id] = Reg0;
        if ( nRegs > 1 )
            pSupp1[Id] = Reg1;
    }
    if ( fVerbose )
    {
        Abc_PrintTime( 1, "Support computation", Abc_Clock() - clk );
        fflush( stdout );
    }

    Gia_ManForEachRi( p, pObj, i )
    {
        Id = Gia_ObjFaninId0p( p, pObj );
        Count = pSuppN[Id];
        Next = -1;
        if ( Count == 1 )
            Next = pSupp0[Id] == i ? -1 : pSupp0[Id];
        else if ( Count == 2 )
        {
            if ( pSupp0[Id] == i && pSupp1[Id] != i )
                Next = pSupp1[Id];
            else if ( pSupp1[Id] == i && pSupp0[Id] != i )
                Next = pSupp0[Id];
        }
        if ( Next >= 0 )
        {
            Vec_IntWriteEntry( vNexts, i, Next );
            Vec_IntWriteEntry( vAvail, Next, 1 );
        }
    }
    ABC_FREE( pSuppN );
    ABC_FREE( pSupp0 );
    ABC_FREE( pSupp1 );

    Vec_IntForEachEntry( vNexts, Spot, i )
        if ( Spot >= 0 && Vec_IntEntry(vAvail, i) == 0 )
            Vec_IntPush( vHeads, i );
    Vec_IntForEachEntry( vHeads, Spot, i ) {
        Gia_ManIncrementTravId( p );
        for ( k = 0, Temp = Spot; Vec_IntEntry(vNexts, Temp) >= 0; k++, Temp = Vec_IntEntry(vNexts, Temp) ) {
            if ( Gia_ObjUpdateTravIdCurrentId(p, Temp) )
                break;
            Vec_IntWriteEntry( vAvail, Temp, 1 );
        }
        if ( k > 100 )
        {
            nItems++;
            if ( vRes == NULL ) 
                vRes = Vec_IntAlloc( 100 );
            Gia_ManIncrementTravId( p );
            for ( k = 0, Temp = Spot; Vec_IntEntry(vNexts, Temp) >= 0; k++, Temp = Vec_IntEntry(vNexts, Temp) ) {
                if ( Gia_ObjUpdateTravIdCurrentId(p, Temp) )
                    break;            
                if ( k % nFlopIncFreq == 0 )
                    Vec_IntPush( vRes, Temp );
            }
        }
        while ( Vec_IntEntry(vNexts, Spot) >= 0 )
        {
            int Next = Vec_IntEntry(vNexts, Spot);
            Vec_IntWriteEntry( vNexts, Spot, -1 );
            Spot = Next;
        }
    }
    if ( fVerbose && vRes ) 
    {
        printf( "Detected %d sequence%s containing %d flops.\n", nItems, nItems > 1 ? "s":"", Vec_IntSize(vRes) );
        fflush( stdout );
    }
    Vec_IntFree( vNexts );
    Vec_IntFree( vAvail );
    Vec_IntFree( vHeads );
    return vRes;
}
Gia_Man_t * Gia_ManDupStopsAdd( Gia_Man_t * p, Vec_Int_t * vStops )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj; int i, Stop;
    Vec_Int_t * vExtras = Vec_IntAlloc( Vec_IntSize(vStops) );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Vec_IntForEachEntry( vStops, Stop, i )
        Vec_IntPush( vExtras, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Vec_IntForEachEntry( vStops, Stop, i ) 
    {
        int Lit = Gia_ManCi(p, Gia_ManPiNum(p)+Stop)->Value;
        Gia_ManCi(p, Gia_ManPiNum(p)+Stop)->Value = Vec_IntEntry(vExtras, i);
        Vec_IntWriteEntry( vExtras, i, Lit );
    }
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachPo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Vec_IntForEachEntry( vExtras, Stop, i )
        Gia_ManAppendCo( pNew, Stop );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Vec_IntFree( vExtras );
    return pNew;
}
void Gia_ManDupStopsRem_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin1(pObj) );
    pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}
Gia_Man_t * Gia_ManDupStopsRem( Gia_Man_t * p, Vec_Int_t * vStops )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj; int i;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachPi( p, pObj, i )
        if ( i < Gia_ManPiNum(p) - Vec_IntSize(vStops) )
            pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachRo( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachPo( p, pObj, i )
        if ( i >= Gia_ManPoNum(p) - Vec_IntSize(vStops) )
            Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachPi( p, pObj, i )
        if ( i >= Gia_ManPiNum(p) - Vec_IntSize(vStops) )
            pObj->Value = Gia_ObjFanin0Copy( Gia_ManPo(p, i - Gia_ManPiNum(p) + Gia_ManPoNum(p)) );
    Gia_ManForEachPo( p, pObj, i )
        if ( i < Gia_ManPoNum(p) - Vec_IntSize(vStops) )
            Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManDupStopsRem_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachPo( p, pObj, i )
        if ( i < Gia_ManPoNum(p) - Vec_IntSize(vStops) )
            Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}
Gia_Man_t * Gia_ManDupStopsTest( Gia_Man_t * p )
{
    Vec_Int_t * vStops = Gia_ManFindStopFlops( p, 1, 1 );
    if ( vStops == NULL )
        return Gia_ManDup(p);
    Gia_Man_t * pNew1 = Gia_ManDupStopsAdd( p, vStops );
    Gia_Man_t * pNew2 = Gia_ManDupStopsRem( pNew1, vStops );
    Gia_ManStop( pNew1 );    
    Vec_IntFree( vStops );
    return pNew2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
