/**CFile****************************************************************

  FileName    [utils.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Utilities]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__UTILS_h
#define ABC__OPT__ESLIM3__UTILS_h

#include <algorithm>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <chrono>
#include <functional>

#include "misc/util/abc_global.h"
#include "misc/util/utilTruth.h"

#if __cplusplus >= 202002L
  // C++20 (and later) code
  #include <bit>
#elif defined(_WIN64)
  #include <intrin.h>
#endif

#if __cplusplus >= 202002L
  // // C++20 (and later) code
  // #include <bit>
  #define popcount(x) std::popcount(x)
#elif defined(__GNUC__)
  #define popcount(x) __builtin_popcountll(x)
// #elif defined(_MSC_VER)
#elif defined(_WIN64)
  #define popcount(x) __popcnt64(x)
#else
  #define popcount(x) Abc_TtCountOnes(x)
#endif

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class eSLIM3CirMan;

  inline constexpr ABC_UINT64_T truth_patterns[6] = {
    ABC_CONST(0xaaaaaaaaaaaaaaaa), ABC_CONST(0xcccccccccccccccc),
    ABC_CONST(0xf0f0f0f0f0f0f0f0), ABC_CONST(0xff00ff00ff00ff00),
    ABC_CONST(0xffff0000ffff0000), ABC_CONST(0xffffffff00000000)
  };

/**Function*************************************************************

  Synopsis    [Returns the least significant set-bit index, or -1 for a zero word.]

***********************************************************************/
  inline int lsb(ABC_UINT64_T tt) {
    #if __cplusplus >= 202002L
      if (tt == 0) {
        return -1;
      }
      return std::countr_zero(tt);
    #elif defined(__GNUC__)
      return __builtin_ffsll(tt) - 1;
    #else
      return Abc_Tt6FirstBit(tt);
    #endif
  }

  struct eSLIM3Config {
    // The serial command owns the writer; managers only call it at safe
    // circuit boundaries. A null callback leaves checkpointing disabled.
    std::function<std::chrono::steady_clock::time_point(eSLIM3CirMan&)> checkpoint;
    std::chrono::steady_clock::time_point next_checkpoint = std::chrono::steady_clock::time_point::max();
    // Each manager owns its deadline, including managers running in windows.
    std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();
/**Function*************************************************************

  Synopsis    [Tests whether the overall elapsed-time deadline has been reached.]

***********************************************************************/
    bool expired() const { return std::chrono::steady_clock::now() >= deadline; }
    // Some platforms implement Abc_Clock with process CPU time (Linux already
    // uses a monotonic clock). Always use elapsed time inside parallel windows.
    bool parallel_worker = false;
/**Function*************************************************************

  Synopsis    [Returns the configured elapsed-time or CPU-time clock in ABC ticks.]

***********************************************************************/
    abctime timeNow() const {
      if (!parallel_worker)
        return Abc_Clock();
      return abctime(std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count() * CLOCKS_PER_SEC);
    }

    bool aig = true;
    int gate_size = 2;

    bool apply_strash = true;
    // bool fix_seed = false;
    bool fill_subcircuits = false;
    bool grow_mffcs = false;
    unsigned preferred_outputs = 0;
    unsigned cut_input_limit = 10;
    bool trial_limit_active = true;
    bool allow_xors = false;
    bool tune_relation_solver = true;
    // Specialized gate evaluation and Gray-code traversal for sampled witnesses.
    bool fast_simulation = true;
    bool sample_relations = true;
    ABC_UINT64_T relation_sample_salt = 0;
    bool mux_consensus = false;
    // Short SAT budgets apply to area optimization with or without a depth bound.
    unsigned int synthesis_timeout_ms = 5;
    unsigned int synthesis_solver_mode = 6;
    bool synthesis_cegar = true;
    bool cache_synthesis = true;
    bool cache_relations = false;
    bool permute_cache = false;
    bool small_synthesis = true;
    bool compact_timing = true;
    unsigned int aig_encoding = 3;
    // Keep the original timing allowance even after an intermediate depth gain.
    bool initial_depth_bound = false;
    bool protect_neutral_depth = false;
    bool refine_depth = false;
    unsigned int depth_target_percent = 0;
    int depth_floor = -1;
    int area_depth_bound = -1;
/**Function*************************************************************

  Synopsis    [Freeze the serial depth bound and percentage floor at run initialization.]

  SideEffects [Updates this manager configuration.]

***********************************************************************/
    void setDepthTargets(unsigned initial_depth) {
      if (initial_depth_bound && area_depth_bound < 0)
        area_depth_bound = initial_depth;
      // Internal depth includes one level for the primary output. Keep an
      // already frozen target when a manager is rebuilt after inprocessing.
      if (depth_target_percent && depth_floor < 0)
        depth_floor = initial_depth ? 1 + ABC_UINT64_T(initial_depth - 1) * depth_target_percent / 100 : 0;
    }
/**Function*************************************************************

  Synopsis    [Use the compositional window bound and clear serial depth targets.]

  SideEffects [Updates this manager configuration.]

***********************************************************************/
    void setWindowDepthBound(unsigned bound) {
      // Window timing includes the frozen paths outside the window. A target
      // derived from local depth cannot replace that compositional bound.
      depth_target_percent = 0;
      depth_floor = -1;
      area_depth_bound = bound;
    }
/**Function*************************************************************

  Synopsis    [Return the active serial or window depth bound for area synthesis.]

  SideEffects [None.]

***********************************************************************/
    unsigned areaDepthBound(unsigned current_depth) const {
      if (depth_floor >= 0)
        return std::max(current_depth, unsigned(depth_floor));
      return area_depth_bound >= 0 ? unsigned(area_depth_bound) : current_depth;
    }
    // AIG rewriting: 0 = off, 1 = once, 2 = adaptive, 3 = periodic (also D0),
    // 4 = periodic with bounded truth-table resubstitution,
    // 5/6 = periodic choice mapping for delay/area followed by area recovery.
    unsigned int rewrite_mode = 0;
    // Optional serial mode-1 area phase, before restoring the frozen -L target.
    unsigned int area_phase_percent = 0;

    double timeout = 3600;
    unsigned int iterations = 0;
    unsigned int subcircuit_max_size = 5;
    unsigned int additional_gates = 0;
    unsigned int strash_intervall = 100;
    int seed = 0;
    unsigned int nselection_trials = 120;
    double expansion_probability = 0.5;
    unsigned int bias = 2;
    unsigned int ncores = 1;
    unsigned int nwindows = 0;
    unsigned int window_size = 500;

    unsigned int taboo_time = 100;
    double taboo_ratio = 0.5;

    // times given in sec
    int minimum_sat_timeout = 1;
    int base_sat_timeout = 120;
    int minimum_dynamic_timeout_sample_size = 50;
    double dynamic_timeout_buffer_factor = 1.4;

    double relation_generation_timeout = 1.0;
    bool local_relations = true;
    bool skip_optimal_cuts = true;
    unsigned max_divisors = 3;
    unsigned relation_window_gates = 4096;
    unsigned relation_window_inputs = 256;
    unsigned relation_window_fanout = 24;
    unsigned relation_window_fanin = 24;
    bool approximate_relation = false; // Compute an overapproximation of the relation that may not use all don't cares by limiting the tfo of the subcircuit
    bool generate_relation_with_tfi_limit = false; // If approximate_relation is true, also limit the tfi of the subcircuit
    unsigned int relation_tfi_bound = 0;
    unsigned int relation_tfo_bound = 0;

    int verbosity_level = 0;
  };

  class ScopedPhaseTimer {
    const eSLIM3Config& cfg;
    double& total;
    abctime started;
  public:
/**Function*************************************************************

  Synopsis    [Starts an instance-owned diagnostic timer without affecting search budgets.]

***********************************************************************/
    ScopedPhaseTimer(double& total, const eSLIM3Config& cfg)
        : cfg(cfg), total(total), started(cfg.timeNow()) {}
/**Function*************************************************************

  Synopsis    [Accumulates the completed diagnostic phase, including early returns.]

***********************************************************************/
    ~ScopedPhaseTimer() { total += double(cfg.timeNow() - started) / CLOCKS_PER_SEC; }
    ScopedPhaseTimer(const ScopedPhaseTimer&) = delete;
    ScopedPhaseTimer& operator=(const ScopedPhaseTimer&) = delete;
  };

  struct SynthesisBudgetStats {
    ABC_UINT64_T searches = 0;
    ABC_UINT64_T sat = 0;
    ABC_UINT64_T unsat = 0;
    ABC_UINT64_T interrupted = 0;
    ABC_UINT64_T errors = 0;
    ABC_UINT64_T reduction_queries = 0;
    ABC_UINT64_T reduction_interruptions = 0;
    ABC_UINT64_T searches_with_smaller_model = 0;
    double elapsed = 0;

/**Function*************************************************************

  Synopsis    [Merges query outcomes after independently owned workers finish.]

***********************************************************************/
    void merge(const SynthesisBudgetStats& other) {
      searches += other.searches;
      sat += other.sat;
      unsat += other.unsat;
      interrupted += other.interrupted;
      errors += other.errors;
      reduction_queries += other.reduction_queries;
      reduction_interruptions += other.reduction_interruptions;
      searches_with_smaller_model += other.searches_with_smaller_model;
      elapsed += other.elapsed;
    }
  };

  class eSLIM3Log {

    public:
      unsigned int iteration_count = 0;
      ABC_UINT64_T neighborhood_roots = 0;
      ABC_UINT64_T failed_root_draws_skipped = 0;
      ABC_UINT64_T preferred_output_selections = 0;
      ABC_UINT64_T preferred_output_hits = 0;
      ABC_UINT64_T output_boundary_gates_added = 0;
      ABC_UINT64_T mffc_gates_added = 0;
      double relation_generation_time = 0;
      double synthesis_time = 0;
      double relation_window_time = 0;
      double relation_encoding_time = 0;
      double synthesis_encoding_time = 0;
      double synthesis_solving_time = 0;
      double synthesis_checking_time = 0;
      unsigned int subcircuits_with_forbidden_pairs = 0;
      unsigned int nof_sat_relations = 0;
      ABC_UINT64_T relation_observed_exits = 0;
      unsigned int relation_max_exits = 0;
      ABC_UINT64_T relation_any_exit_queries = 0;
      ABC_UINT64_T single_output_core_calls_skipped = 0;
      unsigned int nof_window_relations = 0;
      unsigned int relation_cache_hits = 0;
      unsigned int nof_seeded_relations = 0;
      unsigned int nof_sampled_relations = 0;
      ABC_UINT64_T sampled_relation_patterns = 0;
      unsigned int sampled_optimal_cuts = 0;
      unsigned int relation_timeouts = 0;
      unsigned int relation_retries = 0;
      unsigned int relation_fallbacks = 0;
      unsigned int relation_context_reuses = 0;
      unsigned int relation_context_probes = 0;
      ABC_UINT64_T seeded_relation_tuples = 0;
      double relation_sampling_time = 0;
      unsigned int max_relation_window_gates = 0;
      unsigned int max_relation_window_inputs = 0;
      unsigned int verified_replacements = 0;
      unsigned int unchanged_replacements = 0;
      unsigned int rejected_replacements = 0;
      unsigned int verification_timeouts = 0;
      unsigned int proven_optimal_cuts = 0;
      unsigned int cuts_with_divisors = 0;
      ABC_UINT64_T divisor_candidates = 0;
      ABC_UINT64_T divisor_signature_duplicates = 0;
      double divisor_signature_time = 0;
      unsigned int synthesis_cache_hits = 0;
      unsigned int synthesis_searches = 0;
      unsigned int synthesis_sat_searches = 0;
      SynthesisBudgetStats normal_synthesis_budget;
      SynthesisBudgetStats extended_synthesis_budget;
      unsigned int synthesis_refinements = 0;
      unsigned int synthesis_small_hits = 0;
      unsigned int synthesis_cache_permutations = 0;
      unsigned int synthesis_cache_timing_improvements = 0;
      unsigned int depth_refinement_calls = 0;
      unsigned int depth_refinement_improvements = 0;
      ABC_UINT64_T synthesis_encoded_rows = 0;
      ABC_UINT64_T synthesis_total_rows = 0;
      unsigned int untimed_syntheses = 0;
      unsigned int rewrite_calls = 0;
      unsigned int rewrite_gain = 0;
      unsigned int rewrite_no_gain = 0;
      double rewriting_time = 0;
      double final_inprocessing_time = 0;
      unsigned int resubstitution_calls = 0;
      unsigned int resubstitution_gain = 0;
      double resubstitution_time = 0;

      std::vector<int> nof_analyzed_circuits_per_size;
      std::vector<int> nof_analyzed_circuits_per_output_count;
      std::vector<int> nof_replaced_circuits_per_size;
      std::vector<int> nof_reduced_circuits_per_size;

      std::vector<double> cummulative_sat_runtimes_per_size;
      std::vector<int> nof_sat_calls_per_size;
      std::vector<double> cummulative_unsat_runtimes_per_size;
      std::vector<int> nof_unsat_calls_per_size;
      std::vector<int> nof_interrupted_calls_per_size;
      std::vector<double> cummulative_relation_generation_times_per_size;
      std::vector<int> nof_relation_generations_per_size;

      double cummulative_sat_runtime_synthesis = 0; // msec
      double max_sat_runtime_synthesis = 0; // msec
      ABC_UINT64_T nof_sat_calls_synthesis = 0;

      double cummulative_sat_runtime_relation_generation = 0; // sec
      double max_sat_runtime_relation_generation = 0; // sec
      ABC_UINT64_T nof_sat_calls_relation_generation = 0;

      eSLIM3Log(int size);
      int getSize() const;
      void resize(int size);
  };


/**Function*************************************************************

  Synopsis    [Allocates per-size counters for an independently owned optimization log.]

***********************************************************************/
  inline eSLIM3Log::eSLIM3Log(int size)
          : nof_analyzed_circuits_per_size(size + 1, 0), nof_analyzed_circuits_per_output_count(size + 1, 0),
            nof_replaced_circuits_per_size(size + 1, 0),
            nof_reduced_circuits_per_size(size + 1, 0),
            cummulative_sat_runtimes_per_size(size + 1, 0), nof_sat_calls_per_size(size + 1, 0),
            cummulative_unsat_runtimes_per_size(size + 1, 0), nof_unsat_calls_per_size(size + 1, 0),
            nof_interrupted_calls_per_size(size + 1, 0),
            cummulative_relation_generation_times_per_size(size + 1, 0), nof_relation_generations_per_size(size + 1, 0) {
  }

/**Function*************************************************************

  Synopsis    [Returns the largest gate count represented by the log.]

***********************************************************************/
  inline int eSLIM3Log::getSize() const {
    return nof_analyzed_circuits_per_size.size() - 1;
  }

/**Function*************************************************************

  Synopsis    [Extends the per-size counters to include the requested gate count.]

***********************************************************************/
  inline void eSLIM3Log::resize(int size) {
    int sz = size + 1;
    nof_analyzed_circuits_per_size.resize(sz);
    nof_analyzed_circuits_per_output_count.resize(sz);
    nof_replaced_circuits_per_size.resize(sz);
    nof_reduced_circuits_per_size.resize(sz);
    cummulative_sat_runtimes_per_size.resize(sz);
    nof_sat_calls_per_size.resize(sz);
    cummulative_unsat_runtimes_per_size.resize(sz);
    nof_unsat_calls_per_size.resize(sz);
    nof_interrupted_calls_per_size.resize(sz);
    cummulative_relation_generation_times_per_size.resize(sz);
    nof_relation_generations_per_size.resize(sz);
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
