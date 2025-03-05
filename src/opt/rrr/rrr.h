#pragma once

#include "rrrAndNetwork.h"
#include "rrrScheduler.h"
#include "rrrOptimizer.h"
#include "rrrBddAnalyzer.h"
#include "rrrBddMspfAnalyzer.h"
#include "rrrAnalyzer.h"
#include "rrrSatSolver.h"
#include "rrrSimulator.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  template <typename Ntk>
  void Perform(Ntk *pNtk, Parameter const *pPar) {
    assert(!pPar->fUseBddCspf || !pPar->fUseBddMspf);
    if(pPar->fUseBddCspf) {
      Scheduler<Ntk, rrr::Optimizer<Ntk, rrr::BddAnalyzer<Ntk>>> sch(pNtk, pPar);
      sch.Run();
    } else if(pPar->fUseBddMspf) {
      Scheduler<Ntk, rrr::Optimizer<Ntk, rrr::BddMspfAnalyzer<Ntk>>> sch(pNtk, pPar);
      sch.Run();
    } else {
      Scheduler<Ntk, rrr::Optimizer<Ntk, rrr::Analyzer<Ntk, rrr::Simulator<Ntk>, rrr::SatSolver<Ntk>>>> sch(pNtk, pPar);
      sch.Run();
    }
  }
  
}

ABC_NAMESPACE_CXX_HEADER_END
