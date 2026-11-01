/**HFile****************************************************************

  FileName    [rrr2Parameter.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Experimental redundancy removal and resubstitution.]

  Synopsis    [Redundancy analysis and optimization: Parameter.]

  Author      [Yukio Miyasaka]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 1, 2026.]

  Description [Derived from the rrr package. The original command is unchanged.]

***********************************************************************/

#pragma once

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr2 {

  struct Parameter {
    int iSeed = 0;
    int nWords = 10;
    int nTimeout = 0;
    int nSchedulerVerbose = 0;
    int nPartitionerVerbose = 0;
    int nOptimizerVerbose = 0;
    int nAnalyzerVerbose = 0;
    int nSimulatorVerbose = 0;
    int nSatSolverVerbose = 0;
    bool fUseBddCspf = false;
    bool fUseBddMspf = false;
    int nConflictLimit = 0;
    int nSortType = -1;
    int nOptimizerFlow = 0;
    int nSchedulerFlow = 0;
    int nPartitionType = 0;
    int nDistance = 0;
    int nJobs = 1;
    int nThreads = 1;
    int nPartitionSize = 0;
    int nPartitionSizeMin = 0;
    bool fDeterministic = true;
    int nParallelPartitions = 1;
    bool fOptOnInsert = false;
    bool fGreedy = true;
    bool fDirectCnf = false;
    bool fGeneralize = false;
    int nCleanup = 0;
    int nNeutral = -1;
    int nCandidates = 0;
    int nDepthLimit = -1;
    int nFirstConflicts = 0;
    int nWindow = 0;
  };

}

ABC_NAMESPACE_CXX_HEADER_END
