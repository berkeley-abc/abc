/**HFile****************************************************************

  FileName    [rrr2.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Experimental redundancy removal and resubstitution.]

  Synopsis    [Entry point for experimental redundancy analysis and optimization.]

  Author      [Yukio Miyasaka]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 1, 2026.]

  Description [Derived from the rrr package. The original command is unchanged.]

***********************************************************************/

#pragma once

// This header defines non-inline functions and must be included in only one
// translation unit (currently giaRrr2.cpp).

#include "rrr2AndNetwork.h"
#include "rrr2Scheduler.h"
#include "rrr2Optimizer.h"
#include "rrr2BddAnalyzer.h"
#include "rrr2BddMspfAnalyzer.h"
#include "rrr2Analyzer.h"
#include "rrr2SatSolver.h"
#include "rrr2Simulator.h"
#include "rrr2Partitioner.h"
#include "rrr2LevelBasePartitioner.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr2 {

  template <typename Ntk>
  void Perform(Ntk *pNtk, Parameter const *pPar) {
    assert(!pPar->fUseBddCspf || !pPar->fUseBddMspf);
    switch(pPar->nPartitionType) {
    case 0:
      if(pPar->fUseBddCspf) {
        Scheduler<Ntk, Optimizer<Ntk, BddAnalyzer<Ntk>>, Partitioner<Ntk>> sch(pNtk, pPar);
        sch.Run();
      } else if(pPar->fUseBddMspf) {
        Scheduler<Ntk, Optimizer<Ntk, BddMspfAnalyzer<Ntk>>, Partitioner<Ntk>> sch(pNtk, pPar);
        sch.Run();
      } else {
        Scheduler<Ntk, Optimizer<Ntk, Analyzer<Ntk, Simulator<Ntk>, SatSolver<Ntk>>>, Partitioner<Ntk>> sch(pNtk, pPar);
        sch.Run();
      }
      break;
    case 1:
      if(pPar->fUseBddCspf) {
        Scheduler<Ntk, Optimizer<Ntk, BddAnalyzer<Ntk>>, LevelBasePartitioner<Ntk>> sch(pNtk, pPar);
        sch.Run();
      } else if(pPar->fUseBddMspf) {
        Scheduler<Ntk, Optimizer<Ntk, BddMspfAnalyzer<Ntk>>, LevelBasePartitioner<Ntk>> sch(pNtk, pPar);
        sch.Run();
      } else {
        Scheduler<Ntk, Optimizer<Ntk, Analyzer<Ntk, Simulator<Ntk>, SatSolver<Ntk>>>, LevelBasePartitioner<Ntk>> sch(pNtk, pPar);
        sch.Run();
      }
      break;
    default:
      assert(0);
    }
  }

}

ABC_NAMESPACE_CXX_HEADER_END
