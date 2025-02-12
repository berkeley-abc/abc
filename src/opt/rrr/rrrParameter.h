#pragma once

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  struct Parameter {
    int iSeed = 0;
    int nWords = 10;
    int nTimeout = 0;
    int nSchedulerVerbose = 1;
    int nOptimizerVerbose = 0;
    int nAnalyzerVerbose = 0;
    int nSimulatorVerbose = 0;
    int nSatSolverVerbose = 0;
    bool fUseBddCspf = false;
    bool fUseBddMspf = false;
    int nConflictLimit = 0;
    int nSortType = 0;
    int nOptimizerFlow = 0;
    int nSchedulerFlow = 0;
  };
  
}

ABC_NAMESPACE_CXX_HEADER_END
