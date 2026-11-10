/**CFile****************************************************************

  FileName    [windowManImpl.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Basic implementation of a window manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__WINDOWMANIMPL_h
#define ABC__OPT__ESLIM3__WINDOWMANIMPL_h

#include <random>
#include <algorithm>
#include <numeric>
#include <iostream>
#include <cassert>

#ifdef ABC_USE_PTHREADS
  #if defined(_WIN32) && !defined(__MINGW32__)
    #include "../lib/pthread.h"
  #else
    #include <pthread.h>
  #endif
#endif

#include "windowMan.h"
#include "subcircuit.h"

ABC_NAMESPACE_IMPL_START
namespace eSLIM3 {

/**Function*************************************************************

  Synopsis    [Optimizes windows or falls back to the whole-circuit search.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::applyeSLIM3(eSLIM3CirMan& es_man, eSLIM3Config& cfg, eSLIM3Log& log) {
    assert(es_man.getNofGates() > 0);
    WindowMan win_man(es_man, cfg, log);
    win_man.setupWindows();
    if (!win_man.nwindows) {
      if (cfg.verbosity_level > 0)
        std::cout << "eSLIM3: using one core for the whole circuit.\n";
      eSLIM3_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM3(es_man, cfg, log);
      return;
    }
    win_man.runParallel();
    win_man.validateWindows();
    es_man = win_man.recombineWindows();
  }

/**Function*************************************************************

  Synopsis    [Initializes the shared wall-time budget and deterministic order.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  WindowMan<SynthesisEngine, SelectionStrategy>::WindowMan(eSLIM3CirMan& es_man, const eSLIM3Config& cfg, eSLIM3Log& log)
      : es_man(es_man), cfg(cfg), log(log), rng(cfg.seed) {
    deadline = std::min(cfg.deadline, std::chrono::steady_clock::now() + std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(cfg.timeout)));
  }

/**Function*************************************************************

  Synopsis    [Partitions the circuit or selects the explicitly requested windows.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::setupWindows() {
    unsigned requested = cfg.ncores;
#ifndef ABC_USE_PTHREADS
    if (requested > 1)
      std::cout << "eSLIM3: thread support is unavailable; using one core.\n";
    requested = 1;
#endif
    const unsigned gates = es_man.getNofGates();
    unsigned size = cfg.window_size;
    unsigned count = cfg.nwindows;
    if (!count) {
      // Leave enough gates in each automatic window to form useful cuts.
      const ABC_UINT64_T minimum = 4ull * std::max(1u, cfg.subcircuit_max_size);
      count = std::min(requested, unsigned(gates / minimum));
      if (count < 2)
        return;
      size = 1 + (gates - 1) / count;
    }
    assert(size > 0);
    reorderCircuit();
    const unsigned maximum = 1 + (gates - 1) / size;
    nwindows = std::min(maximum, count);
    nworkers = std::min(requested, unsigned(nwindows));
    std::vector<int> gate_ids(gates);
    std::iota(gate_ids.begin(), gate_ids.end(), es_man.getNofPis() + 1);
    std::vector<int> window_ids(maximum), selected;
    std::iota(window_ids.begin(), window_ids.end(), 0);
    selected.reserve(nwindows);
    std::sample(window_ids.begin(), window_ids.end(), std::back_inserter(selected), nwindows, rng);
    // Recombination visits windows in their original topological order.
    std::sort(selected.begin(), selected.end());
    for (int id : selected) {
      const unsigned begin = unsigned(id) * size;
      computeWindow(gate_ids, begin, begin + std::min(size, gates - begin));
      wlogs.emplace_back(log.getSize());
    }
  }

/**Function*************************************************************

  Synopsis    [Groups gates using a randomized output DFS order.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::reorderCircuit() {
    std::vector<int> pos;
    for (int i = es_man.getNofObjs() - es_man.getNofPos(); i < es_man.getNofObjs(); ++i)
      pos.push_back(i);
    std::shuffle(pos.begin(), pos.end(), rng);
    es_man.applyDFSOrdering(pos);
  }

/**Function*************************************************************

  Synopsis    [Extracts a window and freezes its boundary timing in mode 1.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::computeWindow(const std::vector<int>& gate_ids, int node_begin, int node_end) {
    es_man.incrementTraversalId();
    Subcircuit scir = Subcircuit::getSubcircuitBare(es_man, gate_ids.begin() + node_begin, gate_ids.begin() + node_end);
    scirs.push_back(scir);
    windows.emplace_back(es_man, scir);
    if constexpr (isDelayEngine<SynthesisEngine>::value) {
      auto& win = windows.back();
      win.window_delay_bound = es_man.getDepth();
      for (int id : scir.inputs)
        win.window_arrivals.push_back(es_man.nodes[id]->depth);
      for (int id : scir.outputs)
        win.window_required.push_back(es_man.nodes[id]->depth);
      for (int i = 1; i <= win.getNofPis(); ++i)
        win.nodes[i]->depth = win.window_arrivals[i-1];
      for (int i = win.getNofPis() + 1; i < win.getNofObjs(); ++i) {
        win.nodes[i]->depth = 0;
        for (auto* fanin : win.nodes[i]->fanins)
          win.nodes[i]->depth = std::max(win.nodes[i]->depth, fanin->depth + 1);
      }
      win.depth = 0;
      for (int i = win.getNofObjs() - win.getNofPos(); i < win.getNofObjs(); ++i)
        win.depth = std::max(win.depth, win.nodes[i]->depth);
    }
    node_ranges_begin.push_back(gate_ids[node_begin]);
    node_ranges_end.push_back(gate_ids[node_end - 1] + 1);
  }

/**Function*************************************************************

  Synopsis    [Runs at most ncores workers, including the calling thread.]

  Description [Every worker owns its circuit, solver, cache, and log. A
  failed thread creation leaves the remaining work to the active workers.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::runParallel() {
    const unsigned batches = 1 + (unsigned(nwindows) - 1) / nworkers;
    window_timeout = cfg.timeout / batches;
    unsigned active = 1;
#ifdef ABC_USE_PTHREADS
    std::vector<pthread_t> threads;
    for (unsigned i = 1; i < nworkers; ++i) {
      pthread_t thread;
      if (pthread_create(&thread, nullptr, &WindowMan::runWorker, this)) {
        std::cout << "eSLIM3: could not create another worker; continuing with " << active << " cores.\n";
        break;
      }
      threads.push_back(thread);
      ++active;
    }
#endif
    if (cfg.verbosity_level > 0)
      std::cout << "eSLIM3: optimizing " << nwindows << " windows on " << active << " cores.\n";
    runWorker(this);
#ifdef ABC_USE_PTHREADS
    for (auto thread : threads) {
      const int status = pthread_join(thread, nullptr);
      assert(!status);
      (void)status;
    }
#endif
  }

/**Function*************************************************************

  Synopsis    [Claims independent windows until the pass budget expires.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void* WindowMan<SynthesisEngine, SelectionStrategy>::runWorker(void* data) {
    auto& manager = *static_cast<WindowMan*>(data);
    while (std::chrono::steady_clock::now() < manager.deadline) {
      const unsigned wid = manager.next_window.fetch_add(1, std::memory_order_relaxed);
      if (wid >= unsigned(manager.nwindows))
        break;
      manager.runWindow(wid);
    }
    return nullptr;
  }

/**Function*************************************************************

  Synopsis    [Optimizes one window without invoking shared ABC infrastructure.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::runWindow(unsigned wid) {
    eSLIM3Config local = cfg;
    local.verbosity_level = 0;
    local.parallel_worker = nworkers > 1;
    local.deadline = deadline;
    local.timeout = window_timeout;
    // These rebuild the circuit and would discard its frozen boundary timing.
    // Inprocessing remains a sequential step after recombination.
    local.rewrite_mode = 0;
    local.apply_strash = false;
    if constexpr (isDelayEngine<SynthesisEngine>::value)
      local.setWindowDepthBound(windows[wid].window_delay_bound);
    eSLIM3_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM3(windows[wid], local, wlogs[wid]);
  }

/**Function*************************************************************

  Synopsis    [Checks size and compositional boundary timing before committing.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::validateWindows() {
    for (int wid = 0; wid < nwindows; ++wid) {
      auto& win = windows[wid];
      bool valid = unsigned(win.getNofGates()) <= scirs[wid].nodes.size();
      if constexpr (isDelayEngine<SynthesisEngine>::value) {
        std::vector<unsigned> arrival(win.getNofObjs(), 0);
        for (int i = 1; i <= win.getNofPis(); ++i)
          arrival[i] = es_man.nodes[scirs[wid].inputs[i-1]]->depth;
        for (int i = win.getNofPis() + 1; i < win.getNofObjs() - win.getNofPos(); ++i)
          for (auto* fanin : win.nodes[i]->fanins)
            arrival[i] = std::max(arrival[i], arrival[fanin->node_id] + 1);
        for (int i = 0; i < win.getNofPos(); ++i) {
          auto* driver = win.nodes[win.getNofObjs() - win.getNofPos() + i]->fanins[0];
          valid &= arrival[driver->node_id] <= unsigned(es_man.nodes[scirs[wid].outputs[i]]->depth);
        }
      }
      if (!valid) {
        if (cfg.verbosity_level > 0)
          std::cout << "eSLIM3: retaining original window " << wid << " to preserve its bounds.\n";
        win = eSLIM3CirMan(es_man, scirs[wid]);
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Recombines windows while preserving output inversions.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM3CirMan WindowMan<SynthesisEngine, SelectionStrategy>::recombineWindows() {
    combineLogs();
    eSLIM3CirMan combined(es_man.getNofObjs());
    phases.assign(es_man.getNofObjs(), 0);
    es_man.nodes[0]->value1 = 0;
    for (int i = 1; i <= es_man.getNofPis(); ++i)
      es_man.nodes[i]->value1 = combined.addPi();
    int begin = es_man.getNofPis() + 1;
    for (int i = 0; i < nwindows; ++i) {
      addEncompassing(combined, begin, node_ranges_begin[i]);
      addWindow(combined, i);
      begin = node_ranges_end[i];
    }
    addEncompassing(combined, begin, es_man.getNofObjs() - es_man.getNofPos());
    for (int i = es_man.getNofObjs() - es_man.getNofPos(); i < es_man.getNofObjs(); ++i) {
      auto& nd = es_man.nodes[i];
      const bool negated = (nd->tt == 1) != bool(phases[nd->fanins[0]->node_id]);
      combined.addPo(nd->fanins[0]->value1, negated);
    }
    return combined;
  }

/**Function*************************************************************

  Synopsis    [Absorbs input inversions into a gate truth table.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  ABC_UINT64_T WindowMan<SynthesisEngine, SelectionStrategy>::phaseTruth(ABC_UINT64_T truth, unsigned mask, unsigned fanins) {
    if (!mask)
      return truth;
    ABC_UINT64_T result = 0;
    for (unsigned m = 0; m < (1u << fanins); ++m)
      result |= ((truth >> (m ^ mask)) & 1) << m;
    return result;
  }

/**Function*************************************************************

  Synopsis    [Copies gates outside the selected windows.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::addEncompassing(eSLIM3CirMan& combined, int begin, int end) {
    for (int i = begin; i < end; ++i) {
      auto& nd = es_man.nodes[i];
      std::vector<int> fanins;
      unsigned mask = 0;
      for (unsigned j = 0; j < nd->fanins.size(); ++j) {
        fanins.push_back(nd->fanins[j]->value1);
        mask |= phases[nd->fanins[j]->node_id] << j;
      }
      ABC_UINT64_T truth = phaseTruth(nd->tt, mask, fanins.size());
      phases[i] = !eSLIM3CirMan::ttisnormal(truth);
      if (phases[i])
        truth = eSLIM3CirMan::negateTT(truth, fanins.size());
      nd->value1 = combined.addNode(fanins, truth);
    }
  }

/**Function*************************************************************

  Synopsis    [Copies an optimized window and maps its boundary outputs.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::addWindow(eSLIM3CirMan& combined, int wid) {
    auto& win = windows[wid];
    std::vector<unsigned> local_phases(win.getNofObjs(), 0);
    win.nodes[0]->value1 = 0;
    for (int i = 1; i <= win.getNofPis(); ++i) {
      win.nodes[i]->value1 = es_man.nodes[scirs[wid].inputs[i-1]]->value1;
      local_phases[i] = phases[scirs[wid].inputs[i-1]];
    }
    for (int i = win.getNofPis() + 1; i < win.getNofObjs() - win.getNofPos(); ++i) {
      auto& nd = win.nodes[i];
      std::vector<int> fanins;
      unsigned mask = 0;
      for (unsigned j = 0; j < nd->fanins.size(); ++j) {
        fanins.push_back(nd->fanins[j]->value1);
        mask |= local_phases[nd->fanins[j]->node_id] << j;
      }
      ABC_UINT64_T truth = phaseTruth(nd->tt, mask, fanins.size());
      local_phases[i] = !eSLIM3CirMan::ttisnormal(truth);
      if (local_phases[i])
        truth = eSLIM3CirMan::negateTT(truth, fanins.size());
      nd->value1 = combined.addNode(fanins, truth);
    }
    for (int i = 0; i < win.getNofPos(); ++i) {
      auto& out = win.nodes[win.getNofObjs() - win.getNofPos() + i];
      es_man.nodes[scirs[wid].outputs[i]]->value1 = out->fanins[0]->value1;
      phases[scirs[wid].outputs[i]] = (out->tt == 1) ^ local_phases[out->fanins[0]->node_id];
    }
  }

/**Function*************************************************************

  Synopsis    [Combines counters and times after all workers have joined.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void WindowMan<SynthesisEngine, SelectionStrategy>::combineLogs() {
    for (const auto& wl : wlogs) {
      int size = wl.getSize();
      if (log.getSize() < size)
        log.resize(size);
      log.iteration_count += wl.iteration_count;
      log.neighborhood_roots += wl.neighborhood_roots;
      log.failed_root_draws_skipped += wl.failed_root_draws_skipped;
      log.preferred_output_selections += wl.preferred_output_selections;
      log.preferred_output_hits += wl.preferred_output_hits;
      log.output_boundary_gates_added += wl.output_boundary_gates_added;
      log.mffc_gates_added += wl.mffc_gates_added;
      log.relation_generation_time += wl.relation_generation_time;
      log.synthesis_time += wl.synthesis_time;
      log.relation_window_time += wl.relation_window_time;
      log.relation_encoding_time += wl.relation_encoding_time;
      log.synthesis_encoding_time += wl.synthesis_encoding_time;
      log.synthesis_solving_time += wl.synthesis_solving_time;
      log.synthesis_checking_time += wl.synthesis_checking_time;
      log.subcircuits_with_forbidden_pairs += wl.subcircuits_with_forbidden_pairs;
      log.nof_sat_relations += wl.nof_sat_relations;
      log.relation_observed_exits += wl.relation_observed_exits;
      log.relation_max_exits = std::max(log.relation_max_exits, wl.relation_max_exits);
      log.relation_any_exit_queries += wl.relation_any_exit_queries;
      log.single_output_core_calls_skipped += wl.single_output_core_calls_skipped;
      log.nof_window_relations += wl.nof_window_relations;
      log.relation_cache_hits += wl.relation_cache_hits;
      log.nof_seeded_relations += wl.nof_seeded_relations;
      log.nof_sampled_relations += wl.nof_sampled_relations;
      log.sampled_relation_patterns += wl.sampled_relation_patterns;
      log.sampled_optimal_cuts += wl.sampled_optimal_cuts;
      log.relation_timeouts += wl.relation_timeouts;
      log.relation_retries += wl.relation_retries;
      log.relation_fallbacks += wl.relation_fallbacks;
      log.relation_context_reuses += wl.relation_context_reuses;
      log.relation_context_probes += wl.relation_context_probes;
      log.seeded_relation_tuples += wl.seeded_relation_tuples;
      log.relation_sampling_time += wl.relation_sampling_time;
      log.verified_replacements += wl.verified_replacements;
      log.unchanged_replacements += wl.unchanged_replacements;
      log.rejected_replacements += wl.rejected_replacements;
      log.verification_timeouts += wl.verification_timeouts;
      log.proven_optimal_cuts += wl.proven_optimal_cuts;
      log.cuts_with_divisors += wl.cuts_with_divisors;
      log.divisor_candidates += wl.divisor_candidates;
      log.divisor_signature_duplicates += wl.divisor_signature_duplicates;
      log.divisor_signature_time += wl.divisor_signature_time;
      log.max_relation_window_gates = std::max(log.max_relation_window_gates, wl.max_relation_window_gates);
      log.max_relation_window_inputs = std::max(log.max_relation_window_inputs, wl.max_relation_window_inputs);
      log.synthesis_cache_hits += wl.synthesis_cache_hits;
      log.synthesis_searches += wl.synthesis_searches;
      log.synthesis_sat_searches += wl.synthesis_sat_searches;
      log.normal_synthesis_budget.merge(wl.normal_synthesis_budget);
      log.extended_synthesis_budget.merge(wl.extended_synthesis_budget);
      log.synthesis_refinements += wl.synthesis_refinements;
      log.synthesis_small_hits += wl.synthesis_small_hits;
      log.synthesis_cache_permutations += wl.synthesis_cache_permutations;
      log.synthesis_cache_timing_improvements += wl.synthesis_cache_timing_improvements;
      log.depth_refinement_calls += wl.depth_refinement_calls;
      log.depth_refinement_improvements += wl.depth_refinement_improvements;
      log.synthesis_encoded_rows += wl.synthesis_encoded_rows;
      log.synthesis_total_rows += wl.synthesis_total_rows;
      log.untimed_syntheses += wl.untimed_syntheses;
      log.rewrite_calls += wl.rewrite_calls;
      log.rewrite_gain += wl.rewrite_gain;
      log.rewrite_no_gain += wl.rewrite_no_gain;
      log.rewriting_time += wl.rewriting_time;
      log.final_inprocessing_time += wl.final_inprocessing_time;
      log.resubstitution_calls += wl.resubstitution_calls;
      log.resubstitution_gain += wl.resubstitution_gain;
      log.resubstitution_time += wl.resubstitution_time;
      log.cummulative_sat_runtime_synthesis += wl.cummulative_sat_runtime_synthesis;
      log.max_sat_runtime_synthesis = std::max(log.max_sat_runtime_synthesis, wl.max_sat_runtime_synthesis);
      log.nof_sat_calls_synthesis += wl.nof_sat_calls_synthesis;
      log.cummulative_sat_runtime_relation_generation += wl.cummulative_sat_runtime_relation_generation;
      log.max_sat_runtime_relation_generation = std::max(log.max_sat_runtime_relation_generation, wl.max_sat_runtime_relation_generation);
      log.nof_sat_calls_relation_generation += wl.nof_sat_calls_relation_generation;
      for (int i = 0; i <= size; ++i) {
        log.nof_analyzed_circuits_per_size[i] += wl.nof_analyzed_circuits_per_size[i];
        log.nof_analyzed_circuits_per_output_count[i] += wl.nof_analyzed_circuits_per_output_count[i];
        log.nof_replaced_circuits_per_size[i] += wl.nof_replaced_circuits_per_size[i];
        log.nof_reduced_circuits_per_size[i] += wl.nof_reduced_circuits_per_size[i];
        log.cummulative_sat_runtimes_per_size[i] += wl.cummulative_sat_runtimes_per_size[i];
        log.nof_sat_calls_per_size[i] += wl.nof_sat_calls_per_size[i];
        log.cummulative_unsat_runtimes_per_size[i] += wl.cummulative_unsat_runtimes_per_size[i];
        log.nof_unsat_calls_per_size[i] += wl.nof_unsat_calls_per_size[i];
        log.nof_interrupted_calls_per_size[i] += wl.nof_interrupted_calls_per_size[i];
        log.cummulative_relation_generation_times_per_size[i] += wl.cummulative_relation_generation_times_per_size[i];
        log.nof_relation_generations_per_size[i] += wl.nof_relation_generations_per_size[i];
      }
    }
  }

}
ABC_NAMESPACE_IMPL_END

#endif
