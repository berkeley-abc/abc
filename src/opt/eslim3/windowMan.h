/**CFile****************************************************************

  FileName    [windowMan.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Basic implementation of a window manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__WINDOWMAN_h
#define ABC__OPT__ESLIM3__WINDOWMAN_h

#include <vector>
#include <atomic>

#include "misc/util/abc_global.h"

#include "eslim3CirMan.h"
#include "utils.h"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  // Optimize independent windows with a bounded number of workers. In mode 1,
  // frozen boundary timing makes their replacements safe to compose.
  template <typename SynthesisEngine, typename SelectionStrategy>
  class WindowMan {

    public:
      void static applyeSLIM3(eSLIM3CirMan& es_man, eSLIM3Config& cfg, eSLIM3Log& log);

    private:
      friend struct eSLIM3TestAccess;

      WindowMan(eSLIM3CirMan& es_man, const eSLIM3Config& cfg, eSLIM3Log& log);
      void setupWindows();
      void computeWindow(const std::vector<int>& gate_ids, int node_begin, int node_end);
      void reorderCircuit();

      void runParallel();
      static void* runWorker(void* data);
      void runWindow(unsigned wid);
      void validateWindows();
      eSLIM3CirMan recombineWindows();
      void addEncompassing(eSLIM3CirMan& es_man, int node_begin, int node_end);
      void addWindow(eSLIM3CirMan& es_man, int wid);

      void combineLogs();
      static ABC_UINT64_T phaseTruth(ABC_UINT64_T truth, unsigned mask, unsigned fanins);


      int nwindows = 0;
      unsigned nworkers = 1;
      double window_timeout = 0;
      std::atomic<unsigned> next_window{0};
      std::chrono::steady_clock::time_point deadline;
      eSLIM3CirMan& es_man;
      const eSLIM3Config& cfg;
      eSLIM3Log& log;
      std::vector<eSLIM3Log> wlogs;
      std::mt19937 rng;

      std::vector<eSLIM3CirMan> windows;
      std::vector<Subcircuit> scirs;
      std::vector<int> node_ranges_begin;
      std::vector<int> node_ranges_end;
      std::vector<unsigned> phases;

  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "windowManImpl.h"

#endif
