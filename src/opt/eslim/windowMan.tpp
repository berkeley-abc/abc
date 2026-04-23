/**CFile****************************************************************

  FileName    [windowMan.tpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Basic implementation of a window manager.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <random>
#include <algorithm>
#include <set>
#include <cmath>
#include <numeric>
#include <unordered_map>
#include <iostream>

#ifdef ABC_USE_PTHREADS
  #include <thread>
#endif

#include "windowMan.hpp"
#include "subcircuit.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM {

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::applyeSLIM(eSLIMCirMan& es_man, eSLIMConfig& cfg, eSLIMLog& log) {
    int v = cfg.verbosity_level;
    cfg.verbosity_level = 0;
    WindowMan win_man(es_man, cfg, log);
    win_man.setupWindows();
    win_man.runParallel();
    cfg.verbosity_level = v;
    // eSLIMCirMan combined = win_man.recombineWindows();
    // std::swap(es_man, combined);
    es_man = win_man.recombineWindows();
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  WindowMan<SynthesisEngine, SelectionStrategy>::WindowMan(eSLIMCirMan& es_man, const eSLIMConfig& cfg, eSLIMLog& log)
            : es_man(es_man), cfg(cfg), log(log) {
    if (cfg.fix_seed) {
      rng.seed(cfg.seed);
    }
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::setupWindows() {
    reorderCircuit();
    unsigned int nmax_windows = std::ceil(static_cast<double>(es_man.getNofGates()) / cfg.window_size);
    nwindows = std::min(nmax_windows, cfg.nwindows);
    std::vector<int> gate_ids(es_man.getNofGates());
    std::iota(gate_ids.begin(), gate_ids.end(), es_man.getNofPis() + 1);
    std::vector<int> window_ids (nmax_windows);
    std::iota(window_ids.begin(), window_ids.end(), 0);
    std::vector<int> selected_window_ids;
    selected_window_ids.reserve(nwindows);
    std::sample(window_ids.begin(), window_ids.end(), std::back_inserter(selected_window_ids), nwindows, rng);
    for (int i = 0; i < nwindows; i++) {
      int begin_idx = selected_window_ids[i]*cfg.window_size;
      // int end_idx = selected_window_ids[i] == nmax_windows ? gate_ids.size() : selected_window_ids[i+1]*cfg.window_size;
      // int end_idx = selected_window_ids[i] == nmax_windows - 1 ? gate_ids.size() : begin_idx + cfg.window_size;
      int end_idx = begin_idx + cfg.window_size;
      computeWindow(gate_ids, begin_idx, end_idx);
      wlogs.emplace_back(log.getSize());
    }
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::reorderCircuit() {
    std::vector<int> pos;
    pos.reserve(es_man.getNofPos());
    for (int i = es_man.getNofObjs() - es_man.getNofPos(); i < es_man.getNofObjs(); i++) {
      pos.push_back(i);
    }
    std::shuffle(pos.begin(), pos.end(), rng);
    es_man.applyDFSOrdering(pos);
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::computeWindow(const std::vector<int>& gate_ids, int node_begin, int node_end) {
    es_man.incrementTraversalId(); // needed for the insubcircuit marks
    int end_node;
    if (node_end >= gate_ids.size()) {
      node_end = gate_ids.size();
      end_node = gate_ids.back() + 1;
    } else {
      end_node = gate_ids[node_end];
    }
    Subcircuit scir = Subcircuit::getSubcircuitBare(es_man, gate_ids.begin() + node_begin, gate_ids.begin() + node_end);
    scirs.push_back(scir);
    windows.emplace_back(es_man, scir);
    node_ranges_begin.push_back(gate_ids[node_begin]);
    node_ranges_end.push_back(end_node);
  }


  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::runParallel() {
    #ifdef ABC_USE_PTHREADS
      std::vector<std::thread> eslim_threads;
      eslim_threads.reserve(nwindows);
      for (int i = 0; i < nwindows; i++) {
        std::thread esman_thread(eSLIM_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM, std::ref(windows[i]), std::ref(cfg), std::ref(wlogs[i]));
        eslim_threads.push_back(std::move(esman_thread));

      }
      for(auto& t: eslim_threads) {
        t.join();
      }
    #else
      std::cout << "PThreads not available, minimize random window.\n";
      std::uniform_int_distribution<> udist(0, windows.size() - 1);
      int wid = udist(rng);
      eSLIM_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM(windows[wid], cfg, wlogs[wid]);
    #endif
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIMCirMan WindowMan<SynthesisEngine, SelectionStrategy>::recombineWindows() {
    combineLogs();
    eSLIMCirMan combined(es_man.getNofObjs());
    for (int i = 1; i <= es_man.getNofPis(); i++) {
      es_man.nodes[i]->value1 = combined.addPi(); //node 0 is the constant node
    }
    int block_begin = es_man.getNofPis() + 1;
    for (int i = 0; i < nwindows; i++) {
      // windows[i].print();
      int block_end = node_ranges_begin[i];
      addEncompassing(combined, block_begin, block_end);
      addWindow(combined, i);
      block_begin = node_ranges_end[i];
    }
    if (node_ranges_end.back() < es_man.getNofObjs() - es_man.getNofPos()) {
      addEncompassing(combined, node_ranges_end.back(), es_man.getNofObjs() - es_man.getNofPos());
    }
    for (int i = 0; i < es_man.getNofPos(); i++) {
      int nd_id = es_man.getNofObjs() - es_man.getNofPos() + i;
      auto& nd = es_man.nodes[nd_id];
      bool is_negated = nd->tt == 1;
      combined.addPo(nd->fanins[0]->value1, is_negated);
    }
    return combined;
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::addEncompassing(eSLIMCirMan& combined, int node_begin, int node_end) {
    for (int i = node_begin; i < node_end; i++) {
      auto& nd = es_man.nodes[i];
      std::vector<int> fanins;
      fanins.reserve(nd->fanins.size());
      for (int i = 0; i < nd->fanins.size(); i++) {
        fanins.push_back(nd->fanins[i]->value1);
      }
      nd->value1 = combined.addNode(fanins, nd->tt);
    }
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::addWindow(eSLIMCirMan& combined, int wid) {
    for (int i = 1; i <= windows[wid].getNofPis(); i++) {
      windows[wid].nodes[i]->value1 = es_man.nodes[scirs[wid].inputs[i-1]]->value1;
    }
    for (int i = windows[wid].getNofPis() + 1; i < windows[wid].getNofObjs() - windows[wid].getNofPos(); i++) {
      auto& nd = windows[wid].nodes[i];
      std::vector<int> fanins;
      fanins.reserve(nd->fanins.size());
      for (int i = 0; i < nd->fanins.size(); i++) {
        fanins.push_back(nd->fanins[i]->value1);
      }
      nd->value1 = combined.addNode(fanins, nd->tt);
    }
    for (int i = 0; i < windows[wid].getNofPos(); i++) {
      auto& out_nd = windows[wid].nodes[windows[wid].getNofObjs() - windows[wid].getNofPos() + i];
      es_man.nodes[scirs[wid].outputs[i]]->value1 = out_nd->fanins[0]->value1;
    }
  }
  

  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::combineLogs() {
    for (const auto& wl : wlogs) {
      int wl_size = wl.getSize(); 
      if (log.getSize() < wl_size) {
        log.resize(wl_size);
      }
      log.iteration_count += wl.iteration_count;
      log.relation_generation_time += wl.relation_generation_time;
      log.synthesis_time += wl.synthesis_time;
      log.subcircuits_with_forbidden_pairs += wl.subcircuits_with_forbidden_pairs;

      for (int i = 0; i <= wl_size; i++) {
        log.nof_analyzed_circuits_per_size[i] += wl.nof_analyzed_circuits_per_size[i];
        log.nof_replaced_circuits_per_size[i] += wl.nof_replaced_circuits_per_size[i];
        log.nof_reduced_circuits_per_size[i] += wl.nof_reduced_circuits_per_size[i];
        log.cummulative_sat_runtimes_per_size[i] += wl.cummulative_sat_runtimes_per_size[i];
        log.nof_sat_calls_per_size[i] += wl.nof_sat_calls_per_size[i];
        log.cummulative_unsat_runtimes_per_size[i] += wl.cummulative_unsat_runtimes_per_size[i];
        log.nof_unsat_calls_per_size[i] += wl.nof_unsat_calls_per_size[i];
        log.cummulative_relation_generation_times_per_size[i] += wl.cummulative_relation_generation_times_per_size[i];
        log.nof_relation_generations_per_size[i] += wl.nof_relation_generations_per_size[i];
      }
    }
  }

}
ABC_NAMESPACE_IMPL_END