/**CFile****************************************************************

  FileName    [eSLIM3ManImpl.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [eSLIM3 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__ESLIM3MANIMPL_h
#define ABC__OPT__ESLIM3__ESLIM3MANIMPL_h

#include <climits>
#include <algorithm>
#include <array>
#include <numeric>
#include <type_traits>

#include "eSLIM3Man.h"
#include "synthesisEngines.h"
#include "rewrite.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

/**Function*************************************************************

  Synopsis    [Optimizes the supplied circuit with the configured eSLIM3 search.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM3(eSLIM3CirMan& cir, const eSLIM3Config& cfg, eSLIM3Log& log) {
    eSLIM3_Man eslim3(cir, cfg, log);
    eslim3.optimize();
  }

/**Function*************************************************************

  Synopsis    [Initializes search state, random selection and the original depth target.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM3_Man<SynthesisEngine, SelectionStrategy>::eSLIM3_Man(eSLIM3CirMan& es_man, const eSLIM3Config& cfg, eSLIM3Log& log)
            : es_man(es_man), cfg(cfg), selection_strategy(this->es_man, this->cfg, log), log(log), cache_rng(cfg.seed) {
    selection_strategy.setSeed(cfg.seed);
    relation_generation_time = log.relation_generation_time;
    synthesis_time = log.synthesis_time;
    this->cfg.setDepthTargets(es_man.getDepth());
  }



/**Function*************************************************************

  Synopsis    [Searches for local replacements until an iteration or time limit is reached.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::optimize() {
    abctime clkStart    = cfg.timeNow();
    abctime next_progress = clkStart + CLOCKS_PER_SEC;
    cfg.deadline = std::min(cfg.deadline, std::chrono::steady_clock::now() + std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(cfg.timeout)));
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
    auto next_rewrite = std::chrono::steady_clock::now() + std::chrono::seconds(rewritePeriod());
    while (!cfg.expired() && iteration <= iterMax && !stopeSLIM3 && es_man.getNofGates() > 0) {
      iteration++;
      const int previous_size = es_man.getNofGates(), previous_depth = es_man.getDepth();
      findReplacement();
      if (rewrite_no_gain_calls &&
          (es_man.getNofGates() < previous_size || es_man.getDepth() < previous_depth)) {
        // SAT progress creates new native opportunities; restore the base cadence.
        rewrite_no_gain_calls = 0;
        next_rewrite = std::min(next_rewrite,
            std::chrono::steady_clock::now() + std::chrono::seconds(rewritePeriod()));
      }
      if (cfg.checkpoint && std::chrono::steady_clock::now() >= cfg.next_checkpoint)
        cfg.next_checkpoint = cfg.checkpoint(es_man);
      if (repeat_rewrite && !cfg.expired() && std::chrono::steady_clock::now() >= next_rewrite) {
        rewriteCircuit();
        next_rewrite = std::chrono::steady_clock::now() + std::chrono::seconds(rewritePeriod());
      }
      if (cfg.apply_strash && iteration % cfg.strash_intervall == 0) {
        Gia_Man_t* pTemp = es_man.eSLIM3CirManToGia();
        Gia_Man_t* gia_man = Gia_ManRehash( pTemp, 0 );
        Gia_ManStop( pTemp );
        es_man = eSLIM3CirMan(gia_man);
        Gia_ManStop( gia_man );
        invalidateGraphState();
        selection_strategy.reset();
      }
      if (cfg.verbosity_level > 0) {
        int sz = es_man.getNofGates();
        if (sz < current_size) {
          current_size = sz;
          printf("\rIteration %8u : %s = %7d elapsed time = %7.2f sec\n", iteration, node_type, sz, (float)1.0*(cfg.timeNow() - clkStart)/CLOCKS_PER_SEC);
        } else if (cfg.timeNow() >= next_progress) {
          printf("\rIteration %8u", iteration);
          fflush(stdout);
          next_progress = cfg.timeNow() + CLOCKS_PER_SEC;
        }
      }
    }
    log.iteration_count += iteration;
    if (cfg.verbosity_level > 0) {
      int sz = es_man.getNofGates();
      printf("\r#Iterations %8u %s = %7d elapsed time = %7.2f sec\n", iteration, node_type, sz, (float)1.0*(cfg.timeNow() - clkStart)/CLOCKS_PER_SEC);
      if (cfg.verbosity_level > 1) {
        printf("Relation generation time: %.2f sec\n", log.relation_generation_time - relation_generation_time);
        printf("Synthesis time: %.2f sec\n", log.synthesis_time - synthesis_time);
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Returns the native rewrite interval after consecutive calls without gain.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  unsigned eSLIM3_Man<SynthesisEngine, SelectionStrategy>::rewritePeriod() const {
    const unsigned base = cfg.rewrite_mode == 5 ? 10 : cfg.rewrite_mode == 6 ? 5 : rewrite_period_seconds;
    return std::min(max_rewrite_period_seconds, base << rewrite_no_gain_calls);
  }

/**Function*************************************************************

  Synopsis    [Backs off ineffective native calls and restores cadence after improvement.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::recordRewriteOutcome(bool improved) {
    if (improved) rewrite_no_gain_calls = 0;
    else {
      rewrite_no_gain_calls = std::min(max_rewrite_backoff, rewrite_no_gain_calls + 1);
      ++log.rewrite_no_gain;
    }
  }

/**Function*************************************************************

  Synopsis    [Apply native rewriting when sufficient deadline reserve remains.]

  Description [Uses owned graphs and native compression/mapping APIs.
  Accepting a rewritten graph resets selection because node IDs can change.]

  SideEffects [Replaces the owned circuit after checking size and depth bounds.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::rewriteCircuit() {
    const auto rewrite_start = std::chrono::steady_clock::now();
    // DC2, like native resubstitution, cannot be interrupted. Avoid starting
    // it near the deadline; retain twice the largest observed duration plus
    // a margin, counting export time as part of the indivisible operation.
    if (std::chrono::duration<double>(cfg.deadline - rewrite_start).count() <= rewrite_reserve)
      return;
    Gia_Man_t* original = es_man.eSLIM3CirManToGia();
    // Pure area optimization can trade levels for gates, just like its SAT
    // replacements. Delay-constrained engines honor the active bound: -L or
    // -l may permit returning depth gains in exchange for a smaller circuit.
    constexpr bool preserve_depth = !std::is_same_v<SynthesisEngine, AreaMinimizer>;
    const unsigned bound = preserve_depth ? cfg.areaDepthBound(es_man.getDepth()) - 1 : UINT_MAX;
    const unsigned target = cfg.depth_floor > 0 ? unsigned(cfg.depth_floor - 1) :
        unsigned(Gia_ManLevelNum(original)) * 4 / 5;
    Gia_Man_t* rewritten = cfg.rewrite_mode >= 5 ?
        rewriteWithChoices(original, target, bound, log.rewrite_calls, cfg.deadline, cfg.rewrite_mode == 6) :
        Gia_ManCompress2(original, preserve_depth, 0);
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
    bool improved = false;
    if (rewritten && Gia_ManAndNum(rewritten) <= Gia_ManAndNum(original) &&
        (!preserve_depth || unsigned(Gia_ManLevelNum(rewritten)) <= bound)) {
      improved = Gia_ManAndNum(rewritten) < Gia_ManAndNum(original) ||
                 Gia_ManLevelNum(rewritten) < Gia_ManLevelNum(original);
      log.rewrite_gain += Gia_ManAndNum(original) - Gia_ManAndNum(rewritten);
      log.resubstitution_gain += resubstitution_gain;
      es_man = eSLIM3CirMan(rewritten);
      invalidateGraphState();
      selection_strategy.reset();
    }
    if (rewritten)
      Gia_ManStop(rewritten);
    Gia_ManStop(original);
    log.rewriting_time += std::chrono::duration<double>(std::chrono::steady_clock::now() - rewrite_start).count();
    recordRewriteOutcome(improved);
  }

/**Function*************************************************************

  Synopsis    [Discard graph-dependent state after an accepted graph mutation.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::invalidateGraphState() {
    timings_dirty = true;
    divisor_signatures_dirty = true;
    relation_cache.clear();
    relation_cache_units = 0;
    // Context caps are a search policy, not graph-dependent cached facts.
    // Retain successful caps; periodic probes reconsider the full context.
  }

/**Function*************************************************************

  Synopsis    [Reuse complete local relations while the enclosing graph is unchanged.]

  Description [The key fixes cut gates, boundary order and added divisors.
  All graph mutations clear this manager-owned cache. Timed-out relations
  are never cached. Entry and row/pattern limits bound storage independently
  of the number of inputs in the enclosing circuit.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  std::shared_ptr<const Relation> eSLIM3_Man<SynthesisEngine, SelectionStrategy>::getRelation(
      const Subcircuit& subcir) {
    const bool eligible = cfg.cache_relations && cfg.local_relations && cfg.aig &&
        subcir.inputs.size() <= relation_cache_max_inputs && subcir.outputs.size() <= 6 && !cfg.expired();
    std::vector<int> key;
    if (eligible) {
      for (const auto* ids : {&subcir.nodes, &subcir.inputs, &subcir.outputs, &subcir.divisors}) {
        key.push_back(static_cast<int>(ids->size()));
        key.insert(key.end(), ids->begin(), ids->end());
      }
      const auto found = relation_cache.find(key);
      if (found != relation_cache.end()) {
        ++log.relation_cache_hits;
        return found->second;
      }
    }
    RelationGenerator::OptimalityCheck optimal;
    if constexpr (std::is_same_v<SynthesisEngine, AreaDelayConstraintMinimizer>) {
      if (cfg.skip_optimal_cuts && cfg.aig && cfg.gate_size == 2 && subcir.outputs.size() <= 6)
        optimal = [this, &subcir](const Relation& witnesses) { return provesOptimal(subcir, witnesses); };
    }
    auto relation = std::make_shared<Relation>(RelationGenerator::computeRelation(es_man, subcir, cfg, log, optimal, &relation_context));
    if (relation->isProvenOptimal()) {
      ++log.proven_optimal_cuts;
      ++log.sampled_optimal_cuts;
    }
    if (eligible && relation->getStatus()) {
      // A row owns a vector; each pattern owns another vector and packed bits.
      // Bound both counts instead of assuming one pattern per input row.
      size_t units = relation->getNPatterns();
      for (int row = 0; row < relation->getNPatterns(); ++row)
        units += 2 * relation->getPattern(row).size();
      if (units <= max_relation_cache_units) {
        if (relation_cache.size() >= max_relation_cache_entries ||
            relation_cache_units + units > max_relation_cache_units) {
          relation_cache.clear();
          relation_cache_units = 0;
        }
        relation_cache_units += units;
        relation_cache.emplace(std::move(key), relation);
      }
    }
    return relation;
  }

/**Function*************************************************************

  Synopsis    [Computes a complete relation and synthesizes a verified replacement.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM3CirMan eSLIM3_Man<SynthesisEngine, SelectionStrategy>::computeReplacement(Subcircuit& subcir) {
    abctime relation_generation_start = cfg.timeNow();
    const auto owned_relation = getRelation(subcir);
    const Relation& rel = *owned_relation;
    log.relation_generation_time += (double)1.0*(cfg.timeNow() - relation_generation_start)/CLOCKS_PER_SEC;
    log.cummulative_relation_generation_times_per_size[subcir.nodes.size()] += (double)1.0*(cfg.timeNow() - relation_generation_start) / CLOCKS_PER_SEC;
    log.nof_relation_generations_per_size[subcir.nodes.size()]++;
    if (!rel.getStatus()) {
      return eSLIM3CirMan(0);
    }
    abctime synthesis_start = cfg.timeNow();
    eSLIM3CirMan replacement = synthesiseRelation(subcir, rel);
    log.synthesis_time += (double)1.0*(cfg.timeNow() - synthesis_start)/CLOCKS_PER_SEC;
    if (replacement.getNofObjs() > 1) {
      if (!RelationGenerator::verifyReplacement(replacement, subcir, rel, cfg)) {
        if (cfg.expired()) ++log.verification_timeouts;
        else ++log.rejected_replacements;
        return eSLIM3CirMan(0);
      }
      ++log.verified_replacements;
    }
    return replacement;
  }


/**Function*************************************************************

  Synopsis    [Proves that a relation admits no area or per-output arrival improvement.]

  Description [For witnessed subsets of the forbidden tuples, these necessary
  support bounds are weaker than for the complete relation. A tight bound on
  such a relaxation is sufficient to skip the cut, without treating the sample
  as a complete relation. Window boundary order preserves the enclosing cut's
  input arrivals and output depths used here.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  bool eSLIM3_Man<SynthesisEngine, SelectionStrategy>::provesOptimal(
      const Subcircuit& subcir, const Relation& relation) const {
    if constexpr (std::is_same_v<SynthesisEngine, AreaDelayConstraintMinimizer>) {
      if (cfg.skip_optimal_cuts && cfg.aig && cfg.gate_size == 2 && subcir.outputs.size() <= 6) {
        const auto bounds = relation.analyseSupport(subcir.outputs.size(), 2);
        if (bounds.minimum_gates == subcir.nodes.size()) {
          std::vector<unsigned> arrivals;
          for (int input : subcir.inputs) arrivals.push_back(es_man.getObj(input).depth);
          for (unsigned output = 0; output < subcir.outputs.size(); ++output)
            if (bounds.minimumArrival(output, arrivals) < unsigned(es_man.getObj(subcir.outputs[output]).depth))
              return false;
          return true;
        }
      }
    }
    return false;
  }

/**Function*************************************************************

  Synopsis    [Find a replacement using exact synthesis and the complete-query cache.]

  SideEffects [Updates the manager cache and search statistics.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM3CirMan eSLIM3_Man<SynthesisEngine, SelectionStrategy>::synthesiseRelation(Subcircuit& subcir, const Relation& rel) {
    if (provesOptimal(subcir, rel)) {
      ++log.proven_optimal_cuts;
      return eSLIM3CirMan(0);
    }
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

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  typename eSLIM3_Man<SynthesisEngine, SelectionStrategy>::CacheQuery
  eSLIM3_Man<SynthesisEngine, SelectionStrategy>::buildCacheQuery(const Subcircuit& subcir, const Relation& rel) const {
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
      const bool refine = AreaDelayConstraintMinimizer::refineDepthForCut(es_man, subcir, cfg);
      // The same functional/timing query can become critical after another
      // replacement. Do not reuse its unrefined result as a refined query.
      key.push_back(refine);
      const bool unrestricted = !refine &&
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

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM3CirMan eSLIM3_Man<SynthesisEngine, SelectionStrategy>::reuseCachedReplacement(
      const CacheQuery& query, const Subcircuit& subcir, const eSLIM3CirMan& cached) {
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

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::storeCachedReplacement(
      CacheQuery&& query, const eSLIM3CirMan& replacement) {
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

/**Function*************************************************************

  Synopsis    [Refreshes sampled gate signatures after the owned graph changes.]

  Description [These 256 concrete assignments rank divisors only. They do not
  define a relation, prove equivalence or authorize a replacement. Keep the
  generator independent of the existing cut-selection random stream.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  bool eSLIM3_Man<SynthesisEngine, SelectionStrategy>::updateDivisorSignatures() {
    if (!cfg.aig) return false;
    if (!divisor_signatures_dirty) return !divisor_signatures.empty();
    ScopedPhaseTimer timer(log.divisor_signature_time, cfg);
    divisor_signatures.assign(es_man.getNofObjs(), {});
    std::mt19937_64 random(static_cast<ABC_UINT64_T>(cfg.seed) ^ 0x9e3779b97f4a7c15ull);
    for (int i = 1; i <= es_man.getNofPis(); ++i)
      for (unsigned word = 0; word < divisor_signature_words; ++word)
        divisor_signatures[i][word] = random();
    const int end = es_man.getNofObjs() - es_man.getNofPos();
    for (int i = es_man.getNofPis() + 1; i < end; ++i) {
      const auto& node = es_man.getObj(i);
      if (node.fanins.size() != 2 || ((i & 1023) == 0 && cfg.expired())) {
        divisor_signatures.clear();
        return false;
      }
      const auto& a = divisor_signatures[node.fanins[0]->node_id];
      const auto& b = divisor_signatures[node.fanins[1]->node_id];
      const ABC_UINT64_T m0 = -ABC_UINT64_T((node.tt >> 0) & 1);
      const ABC_UINT64_T m1 = -ABC_UINT64_T((node.tt >> 1) & 1);
      const ABC_UINT64_T m2 = -ABC_UINT64_T((node.tt >> 2) & 1);
      const ABC_UINT64_T m3 = -ABC_UINT64_T((node.tt >> 3) & 1);
      for (unsigned word = 0; word < divisor_signature_words; ++word)
        divisor_signatures[i][word] = (~a[word] & ~b[word] & m0) | (a[word] & ~b[word] & m1) |
                                     (~a[word] & b[word] & m2) | (a[word] & b[word] & m3);
    }
    divisor_signatures_dirty = false;
    return true;
  }

/**Function*************************************************************

  Synopsis    [Counts sampled differences modulo a complemented divisor.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  unsigned eSLIM3_Man<SynthesisEngine, SelectionStrategy>::signatureDistance(int left, int right) const {
    unsigned distance = 0;
    for (unsigned word = 0; word < divisor_signature_words; ++word)
      distance += popcount(divisor_signatures[left][word] ^ divisor_signatures[right][word]);
    return std::min(distance, 64 * divisor_signature_words - distance);
  }

/**Function*************************************************************

  Synopsis    [Offers nearby existing signals as free divisors to local synthesis.]

  Description [Only signals outside the cut's transitive fanout are eligible,
  so their reuse cannot create a cycle. Their defining gates are included in
  the relation context. They are not replacement gates and are not charged
  again to its area. The input cap bounds exponential relation work.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::addDivisors(Subcircuit& subcir) {
    if (!cfg.max_divisors || !cfg.local_relations || subcir.inputs.size() >= cfg.cut_input_limit)
      return;
    std::set<int> boundary(subcir.inputs.begin(), subcir.inputs.end()), candidates;
    unsigned latest = 0;
    for (int output : subcir.outputs) latest = std::max(latest, unsigned(es_man.getObj(output).depth));
    auto consider = [&](int id) {
      const auto& node = es_man.getObj(id);
      if (!es_man.isPi(id) && !es_man.isPo(id) && !es_man.inSubcircuit(node) &&
          !es_man.inTFO(node) && !boundary.count(id) &&
          (!isDelayEngine<SynthesisEngine>::value || unsigned(node.depth) < latest))
        candidates.insert(id);
    };
    for (int input : subcir.inputs) {
      const auto& node = es_man.getObj(input);
      for (auto* fanin : node.fanins) consider(fanin->node_id);
      unsigned visited = 0;
      for (auto* fanout : node.fanouts) {
        if (++visited > 64) break;
        consider(fanout->node_id);
      }
    }
    const bool signatures = !candidates.empty() && updateDivisorSignatures();
    // Sample agreement only changes search priority. A coincidental match may
    // lose an opportunity, but complete SAT relations and independent checks
    // still decide whether any resulting replacement is valid.
    std::vector<std::array<int, 3>> ranked;
    for (int id : candidates) {
      ++log.divisor_candidates;
      const auto& node = es_man.getObj(id);
      if (signatures && std::any_of(subcir.inputs.begin(), subcir.inputs.end(),
          [&](int input) { return signatureDistance(id, input) == 0; })) {
        ++log.divisor_signature_duplicates;
        continue;
      }
      int score = 0;
      for (auto* fanin : node.fanins) score += boundary.count(fanin->node_id) ? 4 : 0;
      score += es_man.inTFI(node) ? 2 : 0;
      unsigned distance = 64 * divisor_signature_words;
      if (signatures)
        for (int target : subcir.nodes) distance = std::min(distance, signatureDistance(id, target));
      ranked.push_back({int(distance), -score, id});
    }
    std::sort(ranked.begin(),ranked.end());
    for (const auto& entry : ranked) {
      if (subcir.divisors.size() >= cfg.max_divisors || subcir.inputs.size() >= cfg.cut_input_limit) break;
      const int id = entry[2];
      if (signatures && std::any_of(subcir.divisors.begin(), subcir.divisors.end(),
          [&](int divisor) { return signatureDistance(id, divisor) == 0; })) {
        ++log.divisor_signature_duplicates;
        continue;
      }
      subcir.inputs.push_back(id);
      subcir.divisors.push_back(id);
    }
    log.cuts_with_divisors += !subcir.divisors.empty();
  }

/**Function*************************************************************

  Synopsis    [Recognize a replacement that reproduces the existing cut topology.]

  Description [Match a bijection of gates while fixing boundary signals and
  output phases. Swapping the two pins also swaps their truth-table bits.
  This only skips an identical graph; distinct equivalent decompositions
  remain available for neutral restructuring.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  bool eSLIM3_Man<SynthesisEngine, SelectionStrategy>::isUnchangedReplacement(
      const Subcircuit& subcir, const eSLIM3CirMan& replacement) const {
    if (!cfg.aig || cfg.gate_size != 2 ||
        unsigned(replacement.getNofGates()) != subcir.nodes.size() ||
        unsigned(replacement.getNofPis()) != subcir.inputs.size() ||
        unsigned(replacement.getNofPos()) != subcir.outputs.size())
      return false;
    std::vector<int> mapping(replacement.getNofObjs(), -1);
    std::vector<bool> used(subcir.nodes.size(), false);
    mapping[0] = 0;
    for (unsigned i = 0; i < subcir.inputs.size(); ++i)
      mapping[i + 1] = subcir.inputs[i];
    for (int i = replacement.getNofPis() + 1;
         i < replacement.getNofObjs() - replacement.getNofPos(); ++i) {
      const auto& node = replacement.getObj(i);
      if (node.fanins.size() != 2) return false;
      const int a = mapping[node.fanins[0]->node_id], b = mapping[node.fanins[1]->node_id];
      const ABC_UINT64_T swapped = (node.tt & 9) | ((node.tt & 2) << 1) | ((node.tt & 4) >> 1);
      for (unsigned j = 0; j < subcir.nodes.size(); ++j) {
        const auto& original = es_man.getObj(subcir.nodes[j]);
        if (used[j] || original.fanins.size() != 2) continue;
        const int x = original.fanins[0]->node_id, y = original.fanins[1]->node_id;
        if ((a == x && b == y && node.tt == original.tt) ||
            (a == y && b == x && swapped == original.tt)) {
          mapping[i] = subcir.nodes[j];
          used[j] = true;
          break;
        }
      }
      if (mapping[i] < 0) return false;
    }
    for (unsigned i = 0; i < subcir.outputs.size(); ++i) {
      const auto& output = replacement.getObj(replacement.getNofObjs() - replacement.getNofPos() + i);
      if (output.tt != 2 || output.fanins.size() != 1 ||
          mapping[output.fanins[0]->node_id] != subcir.outputs[i])
        return false;
    }
    return true;
  }

/**Function*************************************************************

  Synopsis    [Selects a cut and installs a verified replacement when its structure changes.]

***********************************************************************/
  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM3_Man<SynthesisEngine, SelectionStrategy>::findReplacement() {
    bool status = true;
    if constexpr (SelectionStrategy::requiresRemainingTimes() || isDelayEngine<SynthesisEngine>::value) {
      // Failed and rejected candidates do not alter topology or arrivals.
      // Reuse remaining times until a replacement, rewrite or strash changes
      // the owned graph; each new manager starts with invalid timing data.
      if (timings_dirty) {
        es_man.setupTimings();
        timings_dirty = false;
      }
    }
    Subcircuit subcir = selection_strategy.getSubcircuit(status);
    if (!status) {
      if (cfg.trial_limit_active) {
        stopeSLIM3 = true;
      }
      return;
    }
    addDivisors(subcir);
    if (log.nof_analyzed_circuits_per_size.size() < subcir.nodes.size() + 1)
      log.resize(subcir.nodes.size());
    const unsigned previous_optimal = log.proven_optimal_cuts;
    eSLIM3CirMan replacement = computeReplacement(subcir);
    if (log.proven_optimal_cuts > previous_optimal) selection_strategy.recordFailure();

    log.nof_analyzed_circuits_per_size[subcir.nodes.size()]++;
    log.nof_analyzed_circuits_per_output_count[subcir.outputs.size()]++;
    log.subcircuits_with_forbidden_pairs += !subcir.forbidden_pairs.empty();
    if (replacement.getNofObjs() > 1) { //replacement found
      if (isUnchangedReplacement(subcir, replacement)) {
        ++log.unchanged_replacements;
        selection_strategy.recordFailure();
        return;
      }
      log.nof_replaced_circuits_per_size[subcir.nodes.size()]++;
      log.nof_reduced_circuits_per_size[subcir.nodes.size()] += (replacement.getNofGates() < subcir.nodes.size());
      es_man.replace(replacement, subcir);
      invalidateGraphState();
    }
  }

}
ABC_NAMESPACE_CXX_HEADER_END

#endif
