/**CFile****************************************************************

  FileName    [eSLIM3.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Interface to the eSLIM3 package.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__ESLIM3_h
#define ABC__OPT__ESLIM3__ESLIM3_h

#include "misc/util/abc_namespaces.h"
#include "aig/gia/gia.h"
#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START

  typedef struct eSLIM3_ParamStruct_ eSLIM3_ParamStruct;
  struct eSLIM3_ParamStruct_ {
    int fill_subcircuits;                               // If a subcircuit has fewer than subcircuit_max_size gates, try to fill it with rejected gates.
    int grow_mffcs;
    unsigned int preferred_outputs;
    unsigned int cut_input_limit;
    int apply_strash;
    int fix_seed;
    int trial_limit_active;
    int apply_inprocessing;
    int synthesis_approach;
    unsigned int synthesis_timeout_ms;
    unsigned int synthesis_solver_mode;
    int synthesis_cegar;
    int cache_synthesis;
    int cache_relations;
    int small_synthesis;
    int compact_timing;
    unsigned int aig_encoding;
    int mux_consensus;
    int tune_relation_solver;
    int fast_simulation;
    int sample_relations;
    double relation_generation_timeout;
    int initial_depth_bound;
    int protect_neutral_depth;
    int refine_depth;
    unsigned int depth_target_percent;
    int permute_cache;
    unsigned int rewrite_mode;
    unsigned int area_phase_percent;
    const char* checkpoint_prefix;
    const char* checkpoint_times;
    int seed;
    int verbosity_level;
    int local_relations;
    int skip_optimal_cuts;
    unsigned int max_divisors;
    unsigned int relation_window_gates;
    unsigned int relation_window_inputs;
    unsigned int relation_window_fanin;
    unsigned int relation_window_fanout;
    int approximate_relation;
    int relation_tfo_bound;
    int generate_relation_with_tfi_limit;
    int relation_tfi_bound;
    int use_taboo_list;
    int forward_search;
    unsigned int ncores;
    int nWindows;
    int window_size;

    int criticial_path_selection_bias;


    double timeout;                                     // available elapsed seconds, including fractional seconds
    unsigned int iterations;                            // maximal number of iterations. No limit if 0
    unsigned int subcircuit_max_size;                   // upper bound for the subcircuit sizes
    unsigned int additional_gates;                      // number of gates that may be introduced to reduce delay

    double expansion_probability;                       // the probability that a node is added to the subcircuit
    unsigned int nruns;

    unsigned int strash_intervall;
    unsigned int nselection_trials;


    int gate_size;
    int aig;
  };

  void seteSLIM3Params(eSLIM3_ParamStruct* params);

  Gia_Man_t* applyeSLIM3(Gia_Man_t * pGia, const eSLIM3_ParamStruct* params);
  // Library entry for combinational SOP/LUT networks; no command is registered.
  Abc_Ntk_t* applyelSLIM3(Abc_Ntk_t * ntk, const eSLIM3_ParamStruct* params);


ABC_NAMESPACE_HEADER_END

#endif
