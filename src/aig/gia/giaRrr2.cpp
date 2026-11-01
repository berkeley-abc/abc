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

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Runs experimental redundancy removal and resubstitution.]

  Description [Uses the original SAT backend and preserves register boundaries.]

  SideEffects [Updates scratch values in the input GIA.]

  SeeAlso     [Gia_ManRrr]

***********************************************************************/
Gia_Man_t *Gia_ManRrr2Ex(Gia_Man_t *pGia, int iSeed, int nWords, int nTimeout, int nSchedulerVerbose, int nPartitionerVerbose, int nOptimizerVerbose, int nAnalyzerVerbose, int nSimulatorVerbose, int nSatSolverVerbose, int fUseBddCspf, int fUseBddMspf, int nConflictLimit, int nSortType, int nOptimizerFlow, int nSchedulerFlow, int nPartitionType, int nDistance, int nJobs, int nThreads, int nPartitionSize, int nPartitionSizeMin, int fDeterministic, int nParallelPartitions, int fOptOnInsert, int fGreedy, Gia_Rrr2Pars_t const *pOptions) {
  if(Gia_ManXorNum(pGia) || Gia_ManMuxNum(pGia) || Gia_ManBufNum(pGia)) {
    Abc_Print(-1, "rrr2 requires a plain AIG without explicit XOR, MUX, or buffer nodes.\n");
    return NULL;
  }
  int nRegs = Gia_ManRegNum(pGia);
  rrr2::AndNetwork ntk;
  ntk.Read(pGia, rrr2::GiaReader<rrr2::AndNetwork>);
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
  Gia_Man_t *pNew = rrr2::CreateGia(&ntk, true);
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

  Synopsis    [Runs the reference policy of the experimental command.]

***********************************************************************/
Gia_Man_t *Gia_ManRrr2(Gia_Man_t *pGia, int iSeed, int nWords, int nTimeout, int nSchedulerVerbose, int nPartitionerVerbose, int nOptimizerVerbose, int nAnalyzerVerbose, int nSimulatorVerbose, int nSatSolverVerbose, int fUseBddCspf, int fUseBddMspf, int nConflictLimit, int nSortType, int nOptimizerFlow, int nSchedulerFlow, int nPartitionType, int nDistance, int nJobs, int nThreads, int nPartitionSize, int nPartitionSizeMin, int fDeterministic, int nParallelPartitions, int fOptOnInsert, int fGreedy) {
  return Gia_ManRrr2Ex(pGia, iSeed, nWords, nTimeout, nSchedulerVerbose, nPartitionerVerbose, nOptimizerVerbose, nAnalyzerVerbose, nSimulatorVerbose, nSatSolverVerbose, fUseBddCspf, fUseBddMspf, nConflictLimit, nSortType, nOptimizerFlow, nSchedulerFlow, nPartitionType, nDistance, nJobs, nThreads, nPartitionSize, nPartitionSizeMin, fDeterministic, nParallelPartitions, fOptOnInsert, fGreedy, NULL);
}

ABC_NAMESPACE_IMPL_END
