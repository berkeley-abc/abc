/**CFile****************************************************************

  FileName    [eSLIM2ManImpl.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [eSLIM2 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - March 2025.]

  Revision    [$Id: eSLIM2ManImpl.h,v 1.00 2025/03/17 00:00:00 Exp $]

***********************************************************************/

#include <climits>
#include <algorithm>
#include <array>
#include <numeric>
#include <type_traits>

#include "eSLIM2Man.h"
#include "synthesisEngines.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM2(eSLIM2CirMan& cir, const eSLIM2Config& cfg, eSLIM2Log& log) {
    eSLIM2_Man eslim2(cir, cfg, log);
    eslim2.optimize();
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM2_Man<SynthesisEngine, SelectionStrategy>::eSLIM2_Man(eSLIM2CirMan& es_man, const eSLIM2Config& cfg, eSLIM2Log& log)
            : es_man(es_man), cfg(cfg), selection_strategy(this->es_man, this->cfg, log), log(log), cache_rng(cfg.seed) {
    // if (cfg.fix_seed) {
    //   selection_strategy.setSeed(cfg.seed);
    // }
    selection_strategy.setSeed(cfg.seed);
    relation_generation_time = log.relation_generation_time;
    synthesis_time = log.synthesis_time;
    this->cfg.setDepthTargets(es_man.getDepth());
  }



  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::optimize() {
    abctime clkStart    = cfg.timeNow();
    abctime next_progress = clkStart + CLOCKS_PER_SEC;
    cfg.deadline = std::min(cfg.deadline, std::chrono::steady_clock::now() + std::chrono::seconds(cfg.timeout));
    unsigned int iteration = 0;
    unsigned int iterMax = cfg.iterations ? cfg.iterations - 1 : UINT_MAX;
    int current_size = es_man.getNofGates();
    const char* node_type = cfg.aig ? "#and" : "#nd";
    // Count rewriting against the same deadline as SAT. Adaptive mode repeats
    // only after an initial gain; explicit periodic mode also revisits graphs
    // changed by SAT even when the original graph resisted rewriting.
    const unsigned previous_rewrite_gain = log.rewrite_gain;
    if (cfg.rewrite_mode && cfg.aig && !cfg.expired())
      rewriteCircuit();
    const bool repeat_rewrite = cfg.rewrite_mode >= 3 ||
                               (cfg.rewrite_mode == 2 && log.rewrite_gain > previous_rewrite_gain);
    auto next_rewrite = std::chrono::steady_clock::now() + std::chrono::seconds(rewrite_period_seconds);
    while (!cfg.expired() && iteration <= iterMax && !stopeSLIM2 && es_man.getNofGates() > 0) {
      iteration++;
      findReplacement();
      if (cfg.checkpoint && std::chrono::steady_clock::now() >= cfg.next_checkpoint)
        cfg.next_checkpoint = cfg.checkpoint(es_man);
      if (repeat_rewrite && !cfg.expired() && std::chrono::steady_clock::now() >= next_rewrite) {
        rewriteCircuit();
        next_rewrite = std::chrono::steady_clock::now() + std::chrono::seconds(rewrite_period_seconds);
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
        } else if (cfg.timeNow() >= next_progress) {
          printf("\rIteration %8d", iteration);
          fflush(stdout);
          next_progress = cfg.timeNow() + CLOCKS_PER_SEC;
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

  Synopsis    [Rewrites an AIG while respecting the selected objective.]

  Description [Uses an owned GIA and the native compression API, leaving
  the global ABC frame untouched. Accepting a rewritten graph resets the
  selection strategy because its node IDs may have changed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/

/**Function*************************************************************

  Synopsis    [Apply native rewriting when sufficient deadline reserve remains.]

  SideEffects [Replaces the owned circuit after checking size and depth bounds.]

  SeeAlso     []

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::rewriteCircuit() {
    const auto rewrite_start = std::chrono::steady_clock::now();
    // DC2, like native resubstitution, cannot be interrupted. Avoid starting
    // it near the deadline; retain twice the largest observed duration plus
    // a margin, counting export time as part of the indivisible operation.
    if (std::chrono::duration<double>(cfg.deadline - rewrite_start).count() <= rewrite_reserve)
      return;
    Gia_Man_t* original = es_man.eSLIM2CirManToGia();
    // Pure area optimization can trade levels for gates, just like its SAT
    // replacements. Delay-constrained engines retain the current depth.
    constexpr bool preserve_depth = !std::is_same_v<SynthesisEngine, AreaMinimizer>;
    Gia_Man_t* rewritten = Gia_ManCompress2(original, preserve_depth, 0);
    const double rewrite_elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - rewrite_start).count();
    rewrite_reserve = std::max(rewrite_reserve, 2 * rewrite_elapsed + native_reserve_margin);
    ++log.rewrite_calls;
    unsigned resubstitution_gain = 0;
    // Occasionally expose sharing outside the small SAT cuts. A single
    // native resubstitution pass uses exact full-circuit truth tables.
    // Bound both support and estimated pairwise truth-table work; larger
    // circuits retain the usual SAT/DC2 path. Leave time for the pass rather
    // than starting an indivisible native call at the end of the budget.
    if (rewritten && cfg.rewrite_mode == 4 && log.rewrite_calls % resubstitution_period == 1 &&
        std::chrono::duration<double>(cfg.deadline - std::chrono::steady_clock::now()).count() > resubstitution_reserve) {
      const unsigned inputs = Gia_ManCiNum(rewritten), gates = Gia_ManAndNum(rewritten);
      if (inputs <= 16 && gates > 0 && gates <= 512 &&
          ABC_UINT64_T(gates) * gates * (1u << (inputs > 6 ? inputs - 6 : 0)) <= (1u << 24)) {
        // Explicit sorting avoids changing the process-global C random seed.
        const auto resubstitution_start = std::chrono::steady_clock::now();
        Gia_Man_t* resub = Gia_ManTransductionTt(rewritten, 1, 0, 0,
            log.resubstitution_calls % 4, 0, 0, preserve_depth, nullptr, 0, 0);
        const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - resubstitution_start).count();
        // The native pass cannot be interrupted. Reserve twice its largest
        // observed duration before another pass, in addition to a margin.
        resubstitution_reserve = std::max(resubstitution_reserve, 2 * elapsed + native_reserve_margin);
        log.resubstitution_time += elapsed;
        ++log.resubstitution_calls;
        if (resub && Gia_ManAndNum(resub) <= Gia_ManAndNum(rewritten) &&
            (!preserve_depth || Gia_ManLevelNum(resub) <= Gia_ManLevelNum(rewritten))) {
          resubstitution_gain = Gia_ManAndNum(rewritten) - Gia_ManAndNum(resub);
          Gia_ManStop(rewritten);
          rewritten = resub;
        } else if (resub)
          Gia_ManStop(resub);
      }
    }
    if (rewritten && Gia_ManAndNum(rewritten) <= Gia_ManAndNum(original) &&
        (!preserve_depth || Gia_ManLevelNum(rewritten) <= Gia_ManLevelNum(original))) {
      log.rewrite_gain += Gia_ManAndNum(original) - Gia_ManAndNum(rewritten);
      log.resubstitution_gain += resubstitution_gain;
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


/**Function*************************************************************

  Synopsis    [Find a replacement using exact synthesis and the complete-query cache.]

  SideEffects [Updates the manager cache and search statistics.]

  SeeAlso     []

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM2CirMan eSLIM2_Man<SynthesisEngine, SelectionStrategy>::synthesiseRelation(Subcircuit& subcir, const Relation& rel) {
    if constexpr (std::is_same_v<SynthesisEngine, AreaDelayConstraintMinimizer> ||
                  std::is_same_v<SynthesisEngine, AreaMinimizer>) {
      // Only complete minimum-area results are reusable. The query contains
      // every functional, feedback and timing constraint in boundary indices.
      constexpr unsigned max_inputs = std::is_same_v<SynthesisEngine, AreaMinimizer> ?
          area_cache_max_inputs : timed_cache_max_inputs;
      // Large full-relation keys cost more than the small area cuts can save.
      // Keep timing-cache eligibility unchanged until measured separately.
      if (cfg.cache_synthesis && subcir.outputs.size() <= 6 && subcir.inputs.size() <= max_inputs) {
        auto query = buildCacheQuery(subcir, rel);
        auto found = synthesis_cache.find(query.words);
        if (found != synthesis_cache.end()) {
          ++log.synthesis_cache_hits;
          return reuseCachedReplacement(query, subcir, found->second);
        }
        bool complete;
        auto replacement = SynthesisEngine::optimize(es_man, rel, subcir, cfg, log, &complete);
        if (complete && replacement.getNofObjs() > 1)
          storeCachedReplacement(std::move(query), replacement);
        return replacement;
      }
    }
    return SynthesisEngine::optimize(es_man, rel, subcir, cfg, log);
  }

/**Function*************************************************************

  Synopsis    [Build a key containing all functional, feedback and timing constraints.]

  SideEffects [None.]

  SeeAlso     []

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  typename eSLIM2_Man<SynthesisEngine, SelectionStrategy>::CacheQuery
  eSLIM2_Man<SynthesisEngine, SelectionStrategy>::buildCacheQuery(const Subcircuit& subcir, const Relation& rel) const {
    CacheQuery query;
    auto& input_order = query.input_order;
    auto& key = query.words;
    std::vector<ABC_UINT64_T> truth;
    if constexpr (std::is_same_v<SynthesisEngine, AreaMinimizer>) {
      if (cfg.aig && subcir.outputs.size() == 1 && subcir.inputs.size() <= 6) {
        // Order inputs by cofactor care signatures. Ties need not be fully
        // canonical: the complete reordered relation and feedback mask
        // remain in the key, so an unresolved symmetry only loses a hit.
        ABC_UINT64_T on = 0, off = 0;
        for (unsigned row = 0; row < unsigned(rel.getNPatterns()); ++row) {
          const auto forbidden = rel.getForbiddenTuples(row, 1);
          truth.push_back(forbidden);
          if (forbidden & 1) on |= ABC_UINT64_T(1) << row;
          if (forbidden & 2) off |= ABC_UINT64_T(1) << row;
        }
        std::vector<std::array<unsigned, 5>> signatures;
        auto feedback = subcir.forbidden_pairs.find(subcir.outputs[0]);
        for (unsigned input = 0; input < subcir.inputs.size(); ++input)
          signatures.push_back({unsigned(popcount(on & ~truth_patterns[input])), unsigned(popcount(off & ~truth_patterns[input])),
                                unsigned(popcount(on & truth_patterns[input])), unsigned(popcount(off & truth_patterns[input])),
                                unsigned(feedback != subcir.forbidden_pairs.end() && feedback->second.count(subcir.inputs[input]))});
        input_order.resize(subcir.inputs.size());
        std::iota(input_order.begin(), input_order.end(), 0);
        std::stable_sort(input_order.begin(), input_order.end(),
                         [&](unsigned a, unsigned b) { return signatures[a] < signatures[b]; });
        if (std::is_sorted(input_order.begin(), input_order.end()))
          input_order.clear();
      }
    }
    key = {subcir.inputs.size(), subcir.outputs.size(),
           subcir.nodes.size(), unsigned(cfg.gate_size), unsigned(cfg.aig)};
    // Feedback constraints use boundary indices, never graph node IDs.
    // The entire output-to-input dependency matrix is needed: several
    // individual feedback paths can also combine into a cycle.
    for (int output : subcir.outputs) {
      ABC_UINT64_T dependencies = 0;
      auto pairs = subcir.forbidden_pairs.find(output);
      if (pairs != subcir.forbidden_pairs.end())
        for (unsigned j = 0; j < subcir.inputs.size(); ++j)
          if (pairs->second.count(subcir.inputs[input_order.empty() ? j : input_order[j]]))
            dependencies |= ABC_UINT64_T(1) << j;
      key.push_back(dependencies);
    }
    if constexpr (std::is_same_v<SynthesisEngine, AreaDelayConstraintMinimizer>) {
      unsigned max_arrival = 0, max_remaining = 0;
      for (int i : subcir.inputs)
        max_arrival = std::max(max_arrival, unsigned(es_man.getObj(i).depth));
      for (int o : subcir.outputs)
        max_remaining = std::max(max_remaining, unsigned(es_man.getObj(o).remaining_time));
      // If even a chain using all gates meets the bound, timing cannot
      // restrict a replacement. Such cuts can share an untimed cache key.
      const unsigned bound = cfg.areaDepthBound(es_man.getDepth());
      const unsigned neutral_bound = cfg.protect_neutral_depth ? unsigned(es_man.getDepth()) : bound;
      const bool unrestricted = !cfg.refine_depth &&
          max_arrival + subcir.nodes.size() + max_remaining <= std::min(bound, neutral_bound);
      key.push_back(unrestricted);
      if (!unrestricted) {
        key.push_back(bound);
        if (cfg.protect_neutral_depth)
          key.push_back(neutral_bound);
        for (int i : subcir.inputs)
          key.push_back(es_man.getObj(i).depth);
        for (int o : subcir.outputs)
          key.push_back(es_man.getObj(o).remaining_time);
      }
    }
    query.relation_offset = key.size();
    for (unsigned row = 0; row < unsigned(rel.getNPatterns()); ++row) {
      unsigned original_row = row;
      if (!input_order.empty()) {
        original_row = 0;
        for (unsigned input = 0; input < input_order.size(); ++input)
          original_row |= ((row >> input) & 1) << input_order[input];
      }
      key.push_back(truth.empty() ? rel.getForbiddenTuples(original_row, subcir.outputs.size()) : truth[original_row]);
    }
    return query;
  }

/**Function*************************************************************

  Synopsis    [Return a cached replacement with any verified safe input permutation.]

  SideEffects [Updates cache permutation statistics.]

  SeeAlso     []

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM2CirMan eSLIM2_Man<SynthesisEngine, SelectionStrategy>::reuseCachedReplacement(
      const CacheQuery& query, const Subcircuit& subcir, const eSLIM2CirMan& cached) {
    const auto& key = query.words;
    const auto& input_order = query.input_order;
    if constexpr (std::is_same_v<SynthesisEngine, AreaDelayConstraintMinimizer>) {
      // Occasionally vary a cached implementation without another SAT
      // search. Accept a swap only if the entire correlated relation is
      // invariant. With unequal arrivals, explicitly require the
      // maximum crossing delay not to increase. This preserves the
      // cached size and all global/neutral timing bounds, and can adapt
      // an unrestricted cache entry to a new arrival-time context.
      const unsigned n = subcir.inputs.size();
      if (cfg.permute_cache && n >= 2 && n <= 6 && subcir.forbidden_pairs.empty() &&
          log.synthesis_cache_hits % cache_permutation_interval == 0) {
        const unsigned random = cache_rng();
        const unsigned a = random % n;
        unsigned b = (random / n) % (n - 1);
        b += b >= a;
        {
          const unsigned rows = key.size() - query.relation_offset;
          const size_t offset = query.relation_offset;
          bool invariant = true;
          for (unsigned row = 0; row < rows && invariant; ++row) {
            const unsigned different = ((row >> a) ^ (row >> b)) & 1;
            const unsigned swapped = row ^ (different << a) ^ (different << b);
            invariant = key[offset + row] == key[offset + swapped];
          }
          if (invariant && es_man.getObj(subcir.inputs[a]).depth != es_man.getObj(subcir.inputs[b]).depth) {
            auto crossing = [&](bool swap) {
              std::vector<unsigned> arrivals(cached.getNofObjs(), 0);
              for (unsigned input = 0; input < n; ++input) {
                const unsigned mapped = swap && input == a ? b : swap && input == b ? a : input;
                arrivals[input + 1] = es_man.getObj(subcir.inputs[mapped]).depth;
              }
              unsigned result = 0, output = 0;
              for (int node = n + 1; node < cached.getNofObjs(); ++node) {
                for (auto* fanin : cached.getObj(node).fanins)
                  arrivals[node] = std::max(arrivals[node], arrivals[fanin->node_id]);
                if (cached.isPo(node))
                  result = std::max(result, arrivals[node] + unsigned(es_man.getObj(subcir.outputs[output++]).remaining_time));
                else
                  ++arrivals[node];
              }
              return result;
            };
            const unsigned before = crossing(false), after = crossing(true);
            invariant = after <= before;
            log.synthesis_cache_timing_improvements += after < before;
          }
          if (invariant) {
            std::vector<unsigned> permutation(n);
            std::iota(permutation.begin(), permutation.end(), 0);
            std::swap(permutation[a], permutation[b]);
            ++log.synthesis_cache_permutations;
            return cached.permuteInputs(permutation);
          }
        }
      }
    }
    return input_order.empty() ? cached.duplicate() : cached.permuteInputs(input_order);
  }

/**Function*************************************************************

  Synopsis    [Store a complete minimum-area result within the bounded cache.]

  SideEffects [May clear older entries when a storage limit is reached.]

  SeeAlso     []

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM2_Man<SynthesisEngine, SelectionStrategy>::storeCachedReplacement(
      CacheQuery&& query, const eSLIM2CirMan& replacement) {
    auto& key = query.words;
    const auto& input_order = query.input_order;
    // Limit both the number of saved graphs and the space used by keys.
    if (synthesis_cache.size() >= max_cache_entries || cache_words + key.size() > max_cache_words) {
      synthesis_cache.clear();
      cache_words = 0;
    }
    cache_words += key.size();
    if (input_order.empty())
      synthesis_cache.emplace(std::move(key), replacement.duplicate());
    else {
      std::vector<unsigned> inverse(input_order.size());
      for (unsigned input = 0; input < input_order.size(); ++input)
        inverse[input_order[input]] = input;
      synthesis_cache.emplace(std::move(key), replacement.permuteInputs(inverse));
    }
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
