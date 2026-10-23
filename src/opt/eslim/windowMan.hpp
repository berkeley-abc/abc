/**CFile****************************************************************

  FileName    [windowMan.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Basic implementation of a window manager.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM__WINDOWMAN_hpp
#define ABC__OPT__ESLIM__WINDOWMAN_hpp

#include <vector>

#include "misc/util/abc_global.h"

#include "eslimCirMan.hpp"
#include "utils.hpp"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  // The parallelisation strategy implemented in this class is rather easy and mainly intended to demonstrate
  // how the eslim package could make use of parallel computing
  template <typename SynthesisEngine, typename SelectionStrategy>
  class WindowMan {

    public:
      void static applyeSLIM(eSLIMCirMan& es_man, eSLIMConfig& cfg, eSLIMLog& log);

    private:

      WindowMan(eSLIMCirMan& es_man, const eSLIMConfig& cfg, eSLIMLog& log);
      // eSLIMCirMan getCircuit();

      void setupWindows();
      void computeWindow(const std::vector<int>& gate_ids, int node_begin, int node_end);
      void reorderCircuit();

      void runParallel();
      eSLIMCirMan recombineWindows();
      void addEncompassing(eSLIMCirMan& es_man, int node_begin, int node_end);
      void addWindow(eSLIMCirMan& es_man, int wid);
      
      void combineLogs();

    
      int nwindows = 0;
      eSLIMCirMan& es_man;
      const eSLIMConfig& cfg;
      eSLIMLog& log;
      std::vector<eSLIMLog> wlogs;
      std::mt19937 rng;

      std::vector<eSLIMCirMan> windows;
      std::vector<Subcircuit> scirs;
      std::vector<int> node_ranges_begin;
      std::vector<int> node_ranges_end;

  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "windowMan.tpp"

#endif