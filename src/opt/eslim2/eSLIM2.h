/**CFile****************************************************************

  FileName    [eSLIM2.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Interface to the eSLIM2 package.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM2.h,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__ESLIM2_h
#define ABC__OPT__ESLIM2__ESLIM2_h

#include "misc/util/abc_namespaces.h"
#include "aig/gia/gia.h"
#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START

  typedef struct eSLIM2_ParamStruct_ eSLIM2_ParamStruct;
  struct eSLIM2_ParamStruct_ {
    int fill_subcircuits;                               // If a subcircuit has fewer than subcircuit_max_size gates, try to fill it with rejected gates.
    int apply_strash;
    int fix_seed;
    int trial_limit_active;
    int apply_inprocessing;
    int synthesis_approach;
    unsigned int synthesis_timeout_ms;
    int compact_timing;
    unsigned int aig_encoding;
    int mux_consensus;
    int tune_relation_solver;
    int fast_simulation;
    int initial_depth_bound;
    unsigned int rewrite_mode;
    int seed;
    int verbosity_level;
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


    unsigned int timeout;                               // available time in seconds (soft limit)
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

  void seteSLIM2Params(eSLIM2_ParamStruct* params);

  Gia_Man_t* applyeSLIM2(Gia_Man_t * pGia, const eSLIM2_ParamStruct* params);
  Abc_Ntk_t* applyelSLIM2(Abc_Ntk_t * ntk, const eSLIM2_ParamStruct* params); //LUT-eSLIM2


ABC_NAMESPACE_HEADER_END

#endif
