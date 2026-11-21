/**CFile****************************************************************

  FileName    [giaRrr2.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Experimental redundancy removal and resubstitution.]

  Synopsis    [Experimental redundancy removal and resubstitution.]

  Author      [Yukio Miyasaka]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 1, 2026.]

  Description [Derived from the rrr package. The original command is unchanged.]

***********************************************************************/

#include "aig/gia/gia.h"

#include "opt/rrr2/rrr2.h"
#include "opt/rrr2/rrr2Abc.h"

#include <algorithm>
#include <random>
#include <utility>
#include <vector>

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Applies a configured RRR2 search and exports its result.]

***********************************************************************/
static Gia_Man_t *Gia_Rrr2Perform(Gia_Man_t *pGia, rrr2::Parameter &Par,
    Gia_Rrr2Pars_t const *pOptions, bool fBalancedExport) {
  if(Gia_ManXorNum(pGia) || Gia_ManMuxNum(pGia) || Gia_ManBufNum(pGia)) {
    Abc_Print(-1, "rrr2 requires a plain AIG without explicit XOR, MUX, or buffer nodes.\n");
    return NULL;
  }
  int nRegs = Gia_ManRegNum(pGia);
  rrr2::AndNetwork ntk;
  ntk.Read(pGia, rrr2::GiaReader<rrr2::AndNetwork>);
  if(pOptions) {
    Par.fDirectCnf = pOptions->fDirectCnf;
    Par.fGeneralize = pOptions->fGeneralize;
    Par.nCleanup = pOptions->nCleanup;
    Par.nNeutral = pOptions->nNeutral;
    Par.nCandidates = pOptions->nCandidates;
    Par.nFirstConflicts = pOptions->nFirstConflicts;
    Par.nWindow = pOptions->nWindow;
    if(pOptions->nDepthGrowth >= 0) {
      int nLevels = Gia_ManLevelNum(pGia);
      Par.nDepthLimit = nLevels + (int)((long long)nLevels * pOptions->nDepthGrowth / 100);
    }
  }
  Gia_Man_t *pFallback = Par.nDepthLimit >= 0 ? Gia_ManDup(pGia) : NULL;
  rrr2::Perform(&ntk, &Par);
  // Merge duplicate gates introduced by resubstitution and decomposition.
  Gia_Man_t *pNew;
  if(fBalancedExport || Par.nDepthLimit >= 0) {
    rrr2::BalancedAig binary;
    binary.Build(&ntk);
    pNew = rrr2::CreateBalancedGia(binary);
  } else pNew = rrr2::CreateGia(&ntk, true);
  Gia_ManSetRegNum(pNew, nRegs);
  if(pFallback) {
    if(Gia_ManLevelNum(pNew) > Par.nDepthLimit) {
      Gia_ManStop(pNew);
      pNew = pFallback;
    } else {
      Gia_ManStop(pFallback);
    }
  }
  return pNew;
}

/**Function*************************************************************

  Synopsis    [Runs experimental redundancy removal and resubstitution.]

  Description [Uses the original SAT backend and preserves register boundaries.]

  SideEffects [Updates scratch values in the input GIA.]

  SeeAlso     [Gia_ManRrr]

***********************************************************************/
Gia_Man_t *Gia_ManRrr2Ex(Gia_Man_t *pGia, int iSeed, int nWords, int nTimeout, int nSchedulerVerbose, int nPartitionerVerbose, int nOptimizerVerbose, int nAnalyzerVerbose, int nSimulatorVerbose, int nSatSolverVerbose, int fUseBddCspf, int fUseBddMspf, int nConflictLimit, int nSortType, int nOptimizerFlow, int nSchedulerFlow, int nPartitionType, int nDistance, int nJobs, int nThreads, int nPartitionSize, int nPartitionSizeMin, int fDeterministic, int nParallelPartitions, int fOptOnInsert, int fGreedy, Gia_Rrr2Pars_t const *pOptions) {
  rrr2::Parameter Par;
  Par.iSeed = iSeed;
  Par.nWords = nWords;
  Par.nTimeout = nTimeout;
  Par.nSchedulerVerbose = nSchedulerVerbose;
  Par.nPartitionerVerbose = nPartitionerVerbose;
  Par.nOptimizerVerbose = nOptimizerVerbose;
  Par.nAnalyzerVerbose = nAnalyzerVerbose;
  Par.nSimulatorVerbose = nSimulatorVerbose;
  Par.nSatSolverVerbose = nSatSolverVerbose;
  Par.fUseBddCspf = fUseBddCspf;
  Par.fUseBddMspf = fUseBddMspf;
  Par.nConflictLimit = nConflictLimit;
  Par.nSortType = nSortType;
  Par.nOptimizerFlow = nOptimizerFlow;
  Par.nSchedulerFlow = nSchedulerFlow;
  Par.nPartitionType = nPartitionType;
  Par.nDistance = nDistance;
  Par.nJobs = nJobs;
  Par.nThreads = nThreads;
  Par.nPartitionSize = nPartitionSize;
  Par.nPartitionSizeMin = nPartitionSizeMin;
  Par.fDeterministic = fDeterministic;
  Par.nParallelPartitions = nParallelPartitions;
  Par.fOptOnInsert = fOptOnInsert;
  Par.fGreedy = fGreedy;
  return Gia_Rrr2Perform(pGia, Par, pOptions, false);
}

/**Function*************************************************************

  Synopsis    [Runs one serial area pass with optional earliest-arrival export.]

***********************************************************************/
Gia_Man_t *Gia_ManRrr2Area(Gia_Man_t *pGia, int Seed, int fUseBddMspf,
    Gia_Rrr2Pars_t const *pOptions, int fBalancedExport) {
  rrr2::Parameter Par;
  Par.iSeed = Seed;
  Par.nTimeout = 1;
  Par.fUseBddMspf = fUseBddMspf != 0;
  Par.nConflictLimit = 1000;
  Par.nOptimizerFlow = 5;
  return Gia_Rrr2Perform(pGia, Par, pOptions, fBalancedExport != 0);
}

/**Function*************************************************************

  Synopsis    [Runs the reference policy of the experimental command.]

***********************************************************************/
Gia_Man_t *Gia_ManRrr2(Gia_Man_t *pGia, int iSeed, int nWords, int nTimeout, int nSchedulerVerbose, int nPartitionerVerbose, int nOptimizerVerbose, int nAnalyzerVerbose, int nSimulatorVerbose, int nSatSolverVerbose, int fUseBddCspf, int fUseBddMspf, int nConflictLimit, int nSortType, int nOptimizerFlow, int nSchedulerFlow, int nPartitionType, int nDistance, int nJobs, int nThreads, int nPartitionSize, int nPartitionSizeMin, int fDeterministic, int nParallelPartitions, int fOptOnInsert, int fGreedy) {
  return Gia_ManRrr2Ex(pGia, iSeed, nWords, nTimeout, nSchedulerVerbose, nPartitionerVerbose, nOptimizerVerbose, nAnalyzerVerbose, nSimulatorVerbose, nSatSolverVerbose, fUseBddCspf, fUseBddMspf, nConflictLimit, nSortType, nOptimizerFlow, nSchedulerFlow, nPartitionType, nDistance, nJobs, nThreads, nPartitionSize, nPartitionSizeMin, fDeterministic, nParallelPartitions, fOptOnInsert, fGreedy, NULL);
}

/**Function*************************************************************

  Synopsis    [Records a new area/depth pair if it improves the observed frontier.]

***********************************************************************/
static bool Gia_Rrr2RecordPoint(std::vector<std::pair<int, int>> &front, int area, int depth) {
  for(auto const &point : front)
    if(point.first <= area && point.second <= depth)
      return false;
  front.erase(std::remove_if(front.begin(), front.end(), [&](std::pair<int, int> const &point) {
    return area <= point.first && depth <= point.second;
  }), front.end());
  front.emplace_back(area, depth);
  return true;
}

/**Function*************************************************************

  Synopsis    [Traces area/depth improvements after completed serial resubstitution targets.]

  Description [Screens completed targets by reachable binary AND count and output
  depth using the same earliest-arrival realization as the depth bound. The visitor borrows a read-only AIG on the calling
  thread. A nonnegative MaxDepth bounds every callback and the returned AIG.
  If the final AIG exceeds the bound, returns a copy of the input if feasible,
  otherwise a feasible witness from the trace, or NULL if none was found.]

***********************************************************************/
static Gia_Man_t * Gia_ManRrr2TracePasses(Gia_Man_t *p, int Seed, int MaxDepth, int Seconds, abctime Deadline, int Passes,
    void (*pVisit)(void *, Gia_Man_t *, int), void *pContext) {
  using Network = rrr2::AndNetwork;
  using Analyzer = rrr2::Analyzer<Network, rrr2::Simulator<Network>, rrr2::SatSolver<Network>>;
  if(!p || !pVisit || Seconds < 0 || Passes < 1 || Gia_ManXorNum(p) || Gia_ManMuxNum(p) || Gia_ManBufNum(p))
    return NULL;
  Network ntk;
  rrr2::Parameter pars;
  pars.nOptimizerFlow = 5; pars.nCleanup = 2; pars.nCandidates = 48;
  pars.nNeutral = 8; pars.nConflictLimit = 1000; pars.nDepthLimit = MaxDepth; pars.fBalancedAig = true;
  ntk.Read(p, rrr2::GiaReader<Network>);
  rrr2::BalancedAig binary;
  auto realize = [&]() {
    Gia_Man_t *g = rrr2::CreateBalancedGia(binary);
    Gia_ManSetRegNum(g, Gia_ManRegNum(p));
    return g;
  };
  std::vector<std::pair<int, int>> measured;
  Gia_Man_t *witness = NULL;
  bool needWitness = MaxDepth >= 0 && Gia_ManLevelNum(p) > MaxDepth;
  rrr2::Optimizer<Network, Analyzer> opt(&pars, [](Network *work) {
    int area = 0;
    work->ForEachInt([&](int id) { area += std::max(0, work->GetNumFanins(id)-1); });
    return static_cast<double>(area);
  });
  opt.AssignNetwork(&ntk);
  auto observe = [&](Network *work) {
    binary.Build(work);
    if((MaxDepth >= 0 && binary.depth > MaxDepth) || !Gia_Rrr2RecordPoint(measured,binary.area,binary.depth)) return;
    Gia_Man_t *clean = realize();
    pVisit(pContext,clean,binary.depth);
    if(needWitness && (!witness || binary.area < Gia_ManAndNum(witness))) {
      Gia_ManStopP(&witness);
      witness = clean;
    } else Gia_ManStop(clean);
  };
  // Keep the analyzer and its simulation patterns across successful passes.
  auto topology = [&]() {
    std::vector<int> lits;
    auto append = [&](int id) {
      lits.push_back(id);
      lits.push_back(ntk.GetNumFanins(id));
      ntk.ForEachFanin(id, [&](int fi, bool c) { lits.push_back(2*fi+c); });
    };
    ntk.ForEachInt(append);
    ntk.ForEachPo(append);
    return lits;
  };
  std::vector<int> before;
  if(Passes > 1) before = topology();
  std::mt19937 seeds(Seed);
  for(int pass = 0; pass < Passes; ++pass) {
    double left = Deadline ? (Deadline-Abc_ClockHr())/1e9 : Seconds;
    if(Deadline && left <= 0) break;
    opt.Run(pass ? static_cast<int>(seeds() & 0x7fffffff) : Seed, left, observe);
    if(pass+1 == Passes || (Deadline && Abc_ClockHr() >= Deadline)) break;
    auto after = topology();
    if(before == after) break;
    before.swap(after);
  }
  binary.Build(&ntk);
  Gia_Man_t *result = realize();
  int depth = binary.depth;
  if(MaxDepth >= 0 && depth > MaxDepth) {
    Gia_ManStop(result);
    return needWitness ? witness : Gia_ManDup(p);
  }
  if(Gia_Rrr2RecordPoint(measured,binary.area,depth)) pVisit(pContext,result,depth);
  Gia_ManStopP(&witness);
  return result;
}

/**Function*************************************************************

  Synopsis    [Visits area and depth improvements during one time-limited RRR2 pass.]

***********************************************************************/
Gia_Man_t * Gia_ManRrr2Trace(Gia_Man_t *p, int Seed, int MaxDepth, int Seconds,
    void (*pVisit)(void *, Gia_Man_t *, int), void *pContext) {
  if(Seconds < 1) return NULL;
  return Gia_ManRrr2TracePasses(p, Seed, MaxDepth, Seconds, 0, 1, pVisit, pContext);
}

/**Function*************************************************************

  Synopsis    [Repeats up to eight changed RRR2 passes with one analyzer.]

  Description [Deadline is absolute wall time in nanoseconds. Zero leaves the
  passes untimed. The visitor and the result obey the same depth bound as the
  single-pass trace.]

***********************************************************************/
Gia_Man_t * Gia_ManRrr2TraceTimed(Gia_Man_t *p, int Seed, int MaxDepth, abctime Deadline,
    void (*pVisit)(void *, Gia_Man_t *, int), void *pContext) {
  if(Deadline && Abc_ClockHr() >= Deadline) return NULL;
  return Gia_ManRrr2TracePasses(p, Seed, MaxDepth, 0, Deadline, 8, pVisit, pContext);
}

ABC_NAMESPACE_IMPL_END
