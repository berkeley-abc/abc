/**CFile****************************************************************

  FileName    [utils.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Utilities]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: utils.h,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__UTILS_h
#define ABC__OPT__ESLIM2__UTILS_h

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
namespace eSLIM2 {

  class eSLIM2CirMan;

  inline constexpr ABC_UINT64_T truth_patterns[6] = {
    ABC_CONST(0xaaaaaaaaaaaaaaaa), ABC_CONST(0xcccccccccccccccc),
    ABC_CONST(0xf0f0f0f0f0f0f0f0), ABC_CONST(0xff00ff00ff00ff00),
    ABC_CONST(0xffff0000ffff0000), ABC_CONST(0xffffffff00000000)
  };

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

  struct eSLIM2Config {
    // The serial command owns the writer; managers only call it at safe
    // circuit boundaries. A null callback leaves checkpointing disabled.
    std::function<std::chrono::steady_clock::time_point(eSLIM2CirMan&)> checkpoint;
    std::chrono::steady_clock::time_point next_checkpoint = std::chrono::steady_clock::time_point::max();
    // Each manager owns its deadline, including managers running in windows.
    std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();
    bool expired() const { return std::chrono::steady_clock::now() >= deadline; }
    // Some platforms implement Abc_Clock with process CPU time (Linux already
    // uses a monotonic clock). Always use elapsed time inside parallel windows.
    bool parallel_worker = false;
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
    bool trial_limit_active = true;
    bool allow_xors = false;
    bool tune_relation_solver = true;
    bool fast_simulation = true;
    bool mux_consensus = false;
    // Short SAT budgets apply to area optimization with or without a depth bound.
    unsigned int synthesis_timeout_ms = 0;
    unsigned int synthesis_solver_mode = 0;
    bool synthesis_cegar = false;
    bool cache_synthesis = true;
    bool permute_cache = false;
    bool small_synthesis = true;
    bool compact_timing = false;
    unsigned int aig_encoding = 0;
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

  SeeAlso     []

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

  SeeAlso     []

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

  SeeAlso     []

***********************************************************************/
    unsigned areaDepthBound(unsigned current_depth) const {
      if (depth_floor >= 0)
        return std::max(current_depth, unsigned(depth_floor));
      return area_depth_bound >= 0 ? unsigned(area_depth_bound) : current_depth;
    }
    // AIG rewriting: 0 = off, 1 = once, 2 = adaptive, 3 = periodic (also D0),
    // 4 = periodic with bounded truth-table resubstitution.
    unsigned int rewrite_mode = 0;

    unsigned int timeout = 3600;
    unsigned int iterations = 0;
    unsigned int subcircuit_max_size = 6;
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

    int relation_generation_timeout = 180;
    bool approximate_relation = false; // Compute an overapproximation of the relation that may not use all don't cares by limiting the tfo of the subcircuit
    bool generate_relation_with_tfi_limit = false; // If approximate_relation is true, also limit the tfi of the subcircuit
    unsigned int relation_tfi_bound = 0;
    unsigned int relation_tfo_bound = 0;

    int verbosity_level = 0;
  };

  class eSLIM2Log {

    public:
      unsigned int iteration_count = 0;
      double relation_generation_time = 0;
      double synthesis_time = 0;
      unsigned int subcircuits_with_forbidden_pairs = 0;
      unsigned int nof_simulated_relations = 0;
      unsigned int nof_sat_relations = 0;
      unsigned int synthesis_cache_hits = 0;
      unsigned int synthesis_searches = 0;
      unsigned int synthesis_sat_searches = 0;
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
      unsigned int resubstitution_calls = 0;
      unsigned int resubstitution_gain = 0;
      double resubstitution_time = 0;

      std::vector<int> nof_analyzed_circuits_per_size;
      std::vector<int> nof_replaced_circuits_per_size;
      std::vector<int> nof_reduced_circuits_per_size;

      std::vector<ABC_UINT64_T> cummulative_sat_runtimes_per_size;
      std::vector<int> nof_sat_calls_per_size;
      std::vector<ABC_UINT64_T> cummulative_unsat_runtimes_per_size;
      std::vector<int> nof_unsat_calls_per_size;
      std::vector<double> cummulative_relation_generation_times_per_size;
      std::vector<int> nof_relation_generations_per_size;

      double cummulative_sat_runtime_synthesis = 0; // msec
      double max_sat_runtime_synthesis = 0; // msec
      ABC_UINT64_T nof_sat_calls_synthesis = 0;

      double cummulative_sat_runtime_relation_generation = 0; // sec
      double max_sat_runtime_relation_generation = 0; // sec
      ABC_UINT64_T nof_sat_calls_relation_generation = 0;

      eSLIM2Log(int size);
      int getSize() const;
      void resize(int size);
  };


  inline eSLIM2Log::eSLIM2Log(int size)
          : nof_analyzed_circuits_per_size(size + 1, 0), nof_replaced_circuits_per_size(size + 1, 0),
            nof_reduced_circuits_per_size(size + 1, 0),
            cummulative_sat_runtimes_per_size(size + 1, 0), nof_sat_calls_per_size(size + 1, 0),
            cummulative_unsat_runtimes_per_size(size + 1, 0), nof_unsat_calls_per_size(size + 1, 0),
            cummulative_relation_generation_times_per_size(size + 1, 0), nof_relation_generations_per_size(size + 1, 0) {
  }

  inline int eSLIM2Log::getSize() const {
    return nof_analyzed_circuits_per_size.size() - 1;
  }

  inline void eSLIM2Log::resize(int size) {
    int sz = size + 1;
    nof_analyzed_circuits_per_size.resize(sz);
    nof_replaced_circuits_per_size.resize(sz);
    nof_reduced_circuits_per_size.resize(sz);
    cummulative_sat_runtimes_per_size.resize(sz);
    nof_sat_calls_per_size.resize(sz);
    cummulative_unsat_runtimes_per_size.resize(sz);
    nof_unsat_calls_per_size.resize(sz);
    cummulative_relation_generation_times_per_size.resize(sz);
    nof_relation_generations_per_size.resize(sz);
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
