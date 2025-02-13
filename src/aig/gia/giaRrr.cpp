#include "aig/gia/gia.h"

#include "opt/rrr/rrr.h"
#include "opt/rrr/rrrAbc.h"

ABC_NAMESPACE_IMPL_START

Gia_Man_t *Gia_ManRrr(Gia_Man_t *pGia, int iSeed, int nWords, int nTimeout, int nSchedulerVerbose, int nOptimizerVerbose, int nAnalyzerVerbose, int nSimulatorVerbose, int nSatSolverVerbose, int fUseBddCspf, int fUseBddMspf, int nConflictLimit, int nSortType, int nOptimizerFlow, int nSchedulerFlow) {
  rrr::AndNetwork ntk;
  ntk.Read<Gia_Man_t>(pGia, rrr::GiaReader<rrr::AndNetwork>);
  rrr::Parameter Par;
  Par.iSeed = iSeed;
  Par.nWords = nWords;
  Par.nTimeout = nTimeout;
  Par.nSchedulerVerbose = nSchedulerVerbose;
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
  rrr::Perform(&ntk, &Par);
  Gia_Man_t *pNew = rrr::CreateGia(&ntk);
  return pNew;
}

ABC_NAMESPACE_IMPL_END
