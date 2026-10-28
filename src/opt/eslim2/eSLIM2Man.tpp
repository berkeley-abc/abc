/**CFile****************************************************************

  FileName    [eSLIM2Man.tpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [eSLIM2 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - March 2025.]

  Revision    [$Id: eSLIM2Man.hpp,v 1.00 2025/03/17 00:00:00 Exp $]

***********************************************************************/

#include <climits>

#include "eSLIM2Man.hpp"
#include "synthesisEngines.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM2(eSLIM2CirMan& cir, const eSLIM2Config& cfg, eSLIM2Log& log) {
    eSLIM2_Man eslim2(cir, cfg, log);
    eslim2.optimize();
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM2_Man<SynthesisEngine, SelectionStrategy>::eSLIM2_Man(eSLIM2CirMan& es_man, const eSLIM2Config& cfg, eSLIM2Log& log)
            : es_man(es_man), cfg(cfg), selection_strategy(this->es_man, this->cfg, log), log(log) {
    // if (cfg.fix_seed) {
    //   selection_strategy.setSeed(cfg.seed);
    // }
    selection_strategy.setSeed(cfg.seed);
    relation_generation_time = log.relation_generation_time;
    synthesis_time = log.synthesis_time;
    if (this->cfg.initial_depth_bound && this->cfg.area_depth_bound < 0)
      this->cfg.area_depth_bound = es_man.getDepth();
  }



  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::optimize() {
    abctime clkStart    = cfg.timeNow();
    cfg.deadline = std::min(cfg.deadline, std::chrono::steady_clock::now() + std::chrono::seconds(cfg.timeout));
    unsigned int iteration = 0;
    unsigned int iterMax = cfg.iterations ? cfg.iterations - 1 : UINT_MAX;
    int current_size = es_man.getNofGates();
    const char* node_type = cfg.aig ? "#and" : "#nd";
    // Count rewriting against the same deadline as SAT. Repeat only if the
    // first pass removed nodes; repeated rewriting can disrupt an already
    // optimized circuit's useful SAT restructuring without improving its area.
    const unsigned previous_rewrite_gain = log.rewrite_gain;
    if (cfg.rewrite_mode && cfg.aig && !cfg.expired())
      rewriteCircuit();
    const bool repeat_rewrite = cfg.rewrite_mode == 2 && log.rewrite_gain > previous_rewrite_gain;
    auto next_rewrite = std::chrono::steady_clock::now() + std::chrono::seconds(2);
    while (!cfg.expired() && iteration <= iterMax && !stopeSLIM2 && es_man.getNofGates() > 0) {
      iteration++;
      findReplacement();
      if (repeat_rewrite && !cfg.expired() && std::chrono::steady_clock::now() >= next_rewrite) {
        rewriteCircuit();
        next_rewrite = std::chrono::steady_clock::now() + std::chrono::seconds(2);
      }
      if (cfg.apply_strash && iteration % cfg.strash_intervall == 0) {
        Gia_Man_t* pTemp = es_man.eSLIM2CirManToGia();
        Gia_Man_t* gia_man = Gia_ManRehash( pTemp, 0 );
        Gia_ManStop( pTemp );
        es_man = eSLIM2CirMan(gia_man);
        Gia_ManStop( gia_man );
        selection_strategy.reset();
      }
      if (cfg.verbosity_level > 0) {
        int sz = es_man.getNofGates();
        if (sz < current_size) {
          current_size = sz;
          printf("\rIteration %8d : %s = %7d elapsed time = %7.2f sec\n", iteration, node_type, sz, (float)1.0*(cfg.timeNow() - clkStart)/CLOCKS_PER_SEC);
        } else {
          printf("\rIteration %8d", iteration);
          fflush(stdout);
        }
      }
    }
    log.iteration_count += iteration;
    if (cfg.verbosity_level > 0) {
      int sz = es_man.getNofGates();
      printf("\r#Iterations %8d %s = %7d elapsed time = %7.2f sec\n", iteration, node_type, sz, (float)1.0*(cfg.timeNow() - clkStart)/CLOCKS_PER_SEC);
      if (cfg.verbosity_level > 1) {
        printf("Relation generation time: %.2f sec\n", log.relation_generation_time - relation_generation_time);
        printf("Synthesis time: %.2f sec\n", log.synthesis_time - synthesis_time);
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Rewrites an AIG without increasing its size or depth.]

  Description [Uses an owned GIA and the native compression API, leaving
  the global ABC frame untouched. Accepting a rewritten graph resets the
  selection strategy because its node IDs may have changed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/

  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::rewriteCircuit() {
    Gia_Man_t* original = es_man.eSLIM2CirManToGia();
    Gia_Man_t* rewritten = Gia_ManCompress2(original, 1, 0);
    ++log.rewrite_calls;
    if (rewritten && Gia_ManAndNum(rewritten) <= Gia_ManAndNum(original) &&
        Gia_ManLevelNum(rewritten) <= Gia_ManLevelNum(original)) {
      log.rewrite_gain += Gia_ManAndNum(original) - Gia_ManAndNum(rewritten);
      es_man = eSLIM2CirMan(rewritten);
      selection_strategy.reset();
    }
    if (rewritten)
      Gia_ManStop(rewritten);
    Gia_ManStop(original);
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM2CirMan eSLIM2_Man<SynthesisEngine, SelectionStrategy>::computeReplacement(Subcircuit& subcir) {
    abctime relation_generation_start = cfg.timeNow();
    Relation rel = RelationGenerator::computeRelation(es_man, subcir, cfg, log);
    log.relation_generation_time += (double)1.0*(cfg.timeNow() - relation_generation_start)/CLOCKS_PER_SEC;
    log.cummulative_relation_generation_times_per_size[subcir.nodes.size()] += (double)1.0*(cfg.timeNow() - relation_generation_start) / CLOCKS_PER_SEC;
    log.nof_relation_generations_per_size[subcir.nodes.size()]++;
    if (!rel.getStatus()) {
      return eSLIM2CirMan(0);
    }
    abctime synthesis_start = cfg.timeNow();
    eSLIM2CirMan replacement = synthesiseRelation(subcir, rel);
    log.synthesis_time += (double)1.0*(cfg.timeNow() - synthesis_start)/CLOCKS_PER_SEC;
    return replacement;
  }


  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM2CirMan eSLIM2_Man<SynthesisEngine, SelectionStrategy>::synthesiseRelation(Subcircuit& subcir, const Relation& rel) {
    if constexpr (std::is_same_v<SynthesisEngine, AreaDelayConstraintMinimizer>) {
      // Cache only complete, minimum-area results. The key includes every
      // functional and timing constraint; node IDs themselves are irrelevant.
      if (subcir.outputs.size() <= 6 && subcir.forbidden_pairs.empty()) {
        std::vector<ABC_UINT64_T> key {subcir.inputs.size(), subcir.outputs.size(),
                                     subcir.nodes.size(), unsigned(cfg.gate_size), unsigned(cfg.aig)};
        unsigned max_arrival = 0, max_remaining = 0;
        for (int i : subcir.inputs)
          max_arrival = std::max(max_arrival, unsigned(es_man.getObj(i).depth));
        for (int o : subcir.outputs)
          max_remaining = std::max(max_remaining, unsigned(es_man.getObj(o).remaining_time));
        // If even a chain using all gates meets the bound, timing cannot
        // restrict a replacement. Such cuts can share an untimed cache key.
        const unsigned bound = cfg.area_depth_bound >= 0 ? unsigned(cfg.area_depth_bound) : unsigned(es_man.getDepth());
        const bool unrestricted = max_arrival + subcir.nodes.size() + max_remaining <= bound;
        key.push_back(unrestricted);
        if (!unrestricted) {
          key.push_back(bound);
          for (int i : subcir.inputs)
            key.push_back(es_man.getObj(i).depth);
          for (int o : subcir.outputs)
            key.push_back(es_man.getObj(o).remaining_time);
        }
        for (int row = 0; row < rel.getNPatterns(); ++row)
          key.push_back(rel.getForbiddenTuples(row, subcir.outputs.size()));
        auto found = synthesis_cache.find(key);
        if (found != synthesis_cache.end()) {
          ++log.synthesis_cache_hits;
          return found->second.duplicate();
        }
        bool complete;
        eSLIM2CirMan replacement = SynthesisEngine::optimize(es_man, rel, subcir, cfg, log, &complete);
        if (complete && replacement.getNofObjs() > 1) {
          // Limit both the number of saved graphs and the space used by keys.
          if (synthesis_cache.size() >= 4096 || cache_words + key.size() > (1u << 21)) {
            synthesis_cache.clear();
            cache_words = 0;
          }
          cache_words += key.size();
          synthesis_cache.emplace(std::move(key), replacement.duplicate());
        }
        return replacement;
      }
    }
    return SynthesisEngine::optimize(es_man, rel, subcir, cfg, log);
  }


  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::findReplacement() {
    bool status = true;
    if constexpr (SelectionStrategy::requiresRemainingTimes() || isDelayEngine<SynthesisEngine>::value) {
      es_man.setupTimings();
    }
    Subcircuit subcir = selection_strategy.getSubcircuit(status);
    if (!status) {
      if (cfg.trial_limit_active) {
        stopeSLIM2 = true;
      }
      return;
    }
    eSLIM2CirMan replacement = computeReplacement(subcir);

    if (log.nof_analyzed_circuits_per_size.size() < subcir.nodes.size() + 1) {
      log.nof_analyzed_circuits_per_size.resize(subcir.nodes.size() + 1, 0);
      log.nof_replaced_circuits_per_size.resize(subcir.nodes.size() + 1, 0);
      log.nof_reduced_circuits_per_size.resize(subcir.nodes.size() + 1, 0);
    }
    log.nof_analyzed_circuits_per_size[subcir.nodes.size()]++;
    log.subcircuits_with_forbidden_pairs += !subcir.forbidden_pairs.empty();
    if (replacement.getNofObjs() > 1) { //replacement found
      log.nof_replaced_circuits_per_size[subcir.nodes.size()]++;
      log.nof_reduced_circuits_per_size[subcir.nodes.size()] += (replacement.getNofGates() < subcir.nodes.size());
      es_man.replace(replacement, subcir);
    }
  }

}
ABC_NAMESPACE_CXX_HEADER_END
