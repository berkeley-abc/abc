/**CFile****************************************************************

  FileName    [windowMan.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Basic implementation of a window manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: windowMan.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__WINDOWMAN_hpp
#define ABC__OPT__ESLIM2__WINDOWMAN_hpp

#include <vector>
#include <atomic>

#include "misc/util/abc_global.h"

#include "eslim2CirMan.hpp"
#include "utils.hpp"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  // Optimize independent windows with a bounded number of workers. In mode 1,
  // frozen boundary timing makes their replacements safe to compose.
  template <typename SynthesisEngine, typename SelectionStrategy>
  class WindowMan {

    public:
      void static applyeSLIM2(eSLIM2CirMan& es_man, eSLIM2Config& cfg, eSLIM2Log& log);

    private:

      WindowMan(eSLIM2CirMan& es_man, const eSLIM2Config& cfg, eSLIM2Log& log);
      void setupWindows();
      void computeWindow(const std::vector<int>& gate_ids, int node_begin, int node_end);
      void reorderCircuit();

      void runParallel();
      static void* runWorker(void* data);
      void runWindow(unsigned wid);
      void validateWindows();
      eSLIM2CirMan recombineWindows();
      void addEncompassing(eSLIM2CirMan& es_man, int node_begin, int node_end);
      void addWindow(eSLIM2CirMan& es_man, int wid);

      void combineLogs();
      static ABC_UINT64_T phaseTruth(ABC_UINT64_T truth, unsigned mask, unsigned fanins);


      int nwindows = 0;
      unsigned nworkers = 1;
      unsigned window_timeout = 0;
      std::atomic<unsigned> next_window{0};
      std::chrono::steady_clock::time_point deadline;
      eSLIM2CirMan& es_man;
      const eSLIM2Config& cfg;
      eSLIM2Log& log;
      std::vector<eSLIM2Log> wlogs;
      std::mt19937 rng;

      std::vector<eSLIM2CirMan> windows;
      std::vector<Subcircuit> scirs;
      std::vector<int> node_ranges_begin;
      std::vector<int> node_ranges_end;
      std::vector<unsigned> phases;

  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "windowMan.tpp"

#endif
