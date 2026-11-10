/**CFile****************************************************************

  FileName    [eSLIM3.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Interface to the eSLIM3 package.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#include <random>
#include <memory>
#include <cstdio>
#include <climits>

#include "utils.h"
#include "checkpoint.h"
#include "eSLIM3Man.h"
#include "relationGeneration.h"
#include "selectionStrategies.h"
#include "windowMan.h"

#include "misc/util/abc_namespaces.h"
#include "opt/mfs/mfs.h"
#include "base/main/main.h"

#include "eSLIM3.h"
#include "eslim3CirMan.h"
#include "synthesisEngines.h"

ABC_NAMESPACE_HEADER_START
  Gia_Man_t * Gia_ManDeepSyn( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose );
  int Abc_NtkMfs( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars );
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Translates public options into an independently owned search configuration.]

***********************************************************************/
static eSLIM3::eSLIM3Config eSLIM3_GetCfg(const eSLIM3_ParamStruct* params) {
  eSLIM3::eSLIM3Config config;
  config.apply_strash = params->apply_strash;
  config.mux_consensus = params->mux_consensus != 0;
  config.tune_relation_solver = params->tune_relation_solver != 0;
  config.fast_simulation = params->fast_simulation != 0;
  config.sample_relations = params->sample_relations != 0;
  config.relation_generation_timeout = params->relation_generation_timeout;
  config.cache_synthesis = params->cache_synthesis != 0;
  config.cache_relations = params->cache_relations != 0;
  config.small_synthesis = params->small_synthesis != 0;
  if (params->synthesis_approach == 1 && params->ncores == 1 &&
      !params->nWindows && params->nruns == 1)
    config.area_phase_percent = params->area_phase_percent;
  config.synthesis_solver_mode = params->synthesis_solver_mode;
  config.synthesis_cegar = params->synthesis_approach <= 1 && params->synthesis_cegar;
  if (params->synthesis_approach <= 1) {
    config.synthesis_timeout_ms = params->synthesis_timeout_ms;
    config.aig_encoding = params->aig_encoding;
  } else {
    // Modes 2/3 retain legacy budgets and encoding; -B/-A apply only to 0/1.
    config.synthesis_timeout_ms = 0;
    config.aig_encoding = 0;
  }
  config.compact_timing = params->synthesis_approach == 1 && params->compact_timing != 0;
  if (params->synthesis_approach == 1) {
    config.initial_depth_bound = params->initial_depth_bound != 0;
    config.protect_neutral_depth = params->protect_neutral_depth != 0;
    config.refine_depth = params->refine_depth != 0;
    config.depth_target_percent = params->depth_target_percent;
    config.permute_cache = params->permute_cache != 0;
    config.rewrite_mode = params->apply_inprocessing ? params->rewrite_mode : 0;
  }
  if (params->synthesis_approach == 0 && params->rewrite_mode >= 3)
    config.rewrite_mode = params->apply_inprocessing ? params->rewrite_mode : 0;
  config.fill_subcircuits = params->fill_subcircuits;
  config.grow_mffcs = params->grow_mffcs != 0;
  config.preferred_outputs = params->preferred_outputs;
  config.cut_input_limit = params->cut_input_limit;
  config.trial_limit_active = params->trial_limit_active;
  config.timeout = params->timeout;
  config.iterations = params->iterations;
  config.subcircuit_max_size = params->subcircuit_max_size;
  config.additional_gates = params->additional_gates;
  config.strash_intervall = params->strash_intervall;
  config.nselection_trials = params->nselection_trials;
  config.seed = params->seed;
  config.verbosity_level = params->verbosity_level;
  config.expansion_probability = params->expansion_probability;
  config.local_relations = params->local_relations != 0;
  config.skip_optimal_cuts = params->skip_optimal_cuts != 0;
  config.max_divisors = params->max_divisors;
  config.relation_window_gates = params->relation_window_gates;
  config.relation_window_inputs = params->relation_window_inputs;
  config.relation_window_fanin = params->relation_window_fanin;
  config.relation_window_fanout = params->relation_window_fanout;
  config.approximate_relation = params->approximate_relation;
  config.relation_tfo_bound = params->relation_tfo_bound;
  config.generate_relation_with_tfi_limit = params->generate_relation_with_tfi_limit;
  config.relation_tfi_bound = params->relation_tfi_bound;
  config.nwindows = params->nWindows;
  config.ncores = params->ncores;
  config.window_size = params->window_size;

  config.aig = params->aig;
  config.gate_size = params->gate_size;

  if (params->use_taboo_list) {
    config.apply_strash = false;
  }

  return config;
}

/**Function*************************************************************

  Synopsis    [Initializes every public option to the documented eSLIM3 defaults.]

***********************************************************************/
void seteSLIM3Params(eSLIM3_ParamStruct* params) {
  params->checkpoint_prefix = nullptr;
  params->checkpoint_times = nullptr;
  params->synthesis_timeout_ms = 5;
  params->synthesis_solver_mode = 6;
  params->synthesis_cegar = 1;
  params->cache_synthesis = 1;
  params->cache_relations = 0;
  params->small_synthesis = 1;
  params->compact_timing = 1;
  params->aig_encoding = 3;
  params->mux_consensus = 0;
  params->tune_relation_solver = 1;
  params->fast_simulation = 1;
  params->sample_relations = 1;
  params->relation_generation_timeout = 1.0;
  params->initial_depth_bound = 0;
  params->protect_neutral_depth = 0;
  params->refine_depth = 0;
  params->depth_target_percent = 80;
  params->permute_cache = 0;
  params->rewrite_mode = 5;
  params->area_phase_percent = 0;

  params->fill_subcircuits = 0;
  params->grow_mffcs = 0;
  params->preferred_outputs = 0;
  params->cut_input_limit = 10;
  params->apply_strash = 1;
  params->fix_seed = 0;
  params->trial_limit_active = 1;
  params->apply_inprocessing = 1;
  params->synthesis_approach = 1;
  params->seed = 0;
  params->verbosity_level = 1;
  params->use_taboo_list = 1;
  params->forward_search = 1;

  params->ncores = 1;
  params->nWindows = 0;
  params->window_size = 500;

  params->criticial_path_selection_bias = 0;

  params->timeout = 1800;
  params->iterations = 0;
  params->subcircuit_max_size = 5;
  params->additional_gates = 0;
  params->strash_intervall = 100;
  params->nselection_trials = 100;
  params->nruns = 1;

  params->expansion_probability = 0.5;
  params->local_relations = 1;
  params->skip_optimal_cuts = 1;
  params->max_divisors = 3;
  params->relation_window_gates = 4096;
  params->relation_window_inputs = 256;
  params->relation_window_fanin = 24;
  params->relation_window_fanout = 24;
  params->approximate_relation = 0;
  params->relation_tfo_bound = 0;
  params->generate_relation_with_tfi_limit = 0;
  params->relation_tfi_bound = 0;

  params->aig = 1;
  params->gate_size = 2;
}

namespace eSLIM3 {

  class DeepsynInprocessor {
    public:
      DeepsynInprocessor(eSLIM3Config& config);
      // Deepsyn interprets a timeout==0 as no timeout
      void setTimeout(int timeout) {this->timeout = timeout < 1 ? 1 : timeout;}
      void runInprocessing(eSLIM3CirMan& es_man);
    private:
      eSLIM3Config& config;
      int timeout;
  };

  class MfsInprocessor {
    public:
      MfsInprocessor(eSLIM3Config& config) {}
      void runInprocessing(eSLIM3CirMan& es_man);
  };

  class EmptyInprocessor {
    public:
      EmptyInprocessor(eSLIM3Config& config) {}
      void runInprocessing(eSLIM3CirMan& es_man) {}
  };

  template <bool IncreaseSize>
  class DelayInprocessor {
    public:
      DelayInprocessor(eSLIM3Config& config);
      void setTimeout(int timeout) {this->timeout = timeout;}
      void runInprocessing(eSLIM3CirMan& es_man);
    private:
      eSLIM3Config& config;
      int timeout;
  };

  class Resyn2Inprocessor {
    public:
      Resyn2Inprocessor(eSLIM3Config& config);
      void runInprocessing(eSLIM3CirMan& es_man);
    private:
      // eSLIM3Config& config;
  };


  template <typename Approach, typename Inprocessor>
  class eSLIM3Run {

    public:
      static Gia_Man_t* runeSLIM3(Gia_Man_t* cir, const eSLIM3_ParamStruct* params);
      static Abc_Ntk_t * runeSLIM3(Abc_Ntk_t * cir, const eSLIM3_ParamStruct* params);
      static Abc_Ntk_t * runeSLIM3Cells(Abc_Ntk_t * cir, const eSLIM3_ParamStruct* params);

    private:
      eSLIM3CirMan es_man;
      eSLIM3Config config;
      eSLIM3Log log;
      Inprocessor inprocessor;

      int initial_area;
      int initial_delay;

      int area_change_eslim3 = 0;
      int area_change_inprocessing = 0;

      int delay_change_eslim3 = 0;
      int delay_change_inprocessing = 0;

      int nruns = 0;

      eSLIM3Run(Gia_Man_t* cir, const eSLIM3_ParamStruct* params);
      eSLIM3Run(Abc_Ntk_t* cir, const eSLIM3_ParamStruct* params, bool simplify);

      void setUpInprocessor();
      void runInprocessing();

      void printSettings();
      void printLog();

      void run();
  };


/**Function*************************************************************

  Synopsis    [Initializes the owned circuit, search configuration and inprocessor.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  eSLIM3Run<Approach, Inprocessor>::eSLIM3Run(Abc_Ntk_t* cir, const eSLIM3_ParamStruct* params, bool simplify_circuit)
                            : es_man(cir, simplify_circuit), config(eSLIM3_GetCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
    config.aig = false;
    config.apply_strash = false;
    if (!params->fix_seed) {
      config.seed = std::random_device{}();
      if (config.verbosity_level > 0) {
        std::cout << "Set seed: " << config.seed << "\n";
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Initializes the owned circuit, search configuration and inprocessor.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  eSLIM3Run<Approach, Inprocessor>::eSLIM3Run(Gia_Man_t* cir, const eSLIM3_ParamStruct* params)
                            : es_man(cir), config(eSLIM3_GetCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
    if (!params->fix_seed) {
      config.seed = std::random_device{}();
      if (config.verbosity_level > 0) {
        std::cout << "Set seed: " << config.seed << "\n";
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Runs the configured optimizer and returns an independently owned result.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  Gia_Man_t* eSLIM3Run<Approach, Inprocessor>::runeSLIM3(Gia_Man_t* cir, const eSLIM3_ParamStruct* params) {
    const auto started = std::chrono::steady_clock::now();
    eSLIM3Run<Approach, Inprocessor> eslim3_run(cir, params);
    // Conversion and the final checkpoint scale with graph size, not with
    // the requested search time. Retain the small-budget percentage reserve
    // without wasting minutes when a small graph gets a long SAT budget.
    const double finalization_allowance = 0.05 + 0.00005 * Gia_ManObjNum(cir);
    const double reserve = std::max(0.001, std::min(params->timeout * 0.05, finalization_allowance));
    eslim3_run.config.deadline = started + std::chrono::duration_cast<std::chrono::steady_clock::duration>(
        std::chrono::duration<double>(std::max(0.0, params->timeout - reserve)));
    // It seems like the variables are freed by abc during preprocessing. Thus,we copy them
    char* name = Abc_UtilStrsav( cir->pName );
    char* spec = Abc_UtilStrsav( cir->pSpec );
    std::unique_ptr<CheckpointWriter> checkpoints;
    if (params->checkpoint_prefix) {
      std::vector<unsigned> times;
      readCheckpointTimes(params->checkpoint_times, params->timeout, times);
      checkpoints = std::make_unique<CheckpointWriter>(params->checkpoint_prefix, times, params->timeout);
      if (!checkpoints->prepare()) {
        ABC_FREE(name);
        ABC_FREE(spec);
        return nullptr;
      }
      eslim3_run.config.checkpoint = [&](eSLIM3CirMan& circuit) { return checkpoints->write(circuit); };
      eslim3_run.config.next_checkpoint = checkpoints->nextTime();
    }
    eslim3_run.run();
    if (checkpoints) {
      checkpoints->write(eslim3_run.es_man, true);
      if (checkpoints->failed())
        std::fprintf(stderr, "eSLIM3: checkpoint output is incomplete; returning the optimized circuit.\n");
    }
    Gia_Man_t* gia_res = eslim3_run.es_man.eSLIM3CirManToGia();
    gia_res->pName = name;
    gia_res->pSpec = spec;
    return gia_res;
  }

/**Function*************************************************************

  Synopsis    [Runs the configured optimizer and returns an independently owned result.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t* eSLIM3Run<Approach, Inprocessor>::runeSLIM3(Abc_Ntk_t* cir, const eSLIM3_ParamStruct* params) {
    bool simplify_circuit = true;
    eSLIM3Run<Approach, Inprocessor> eslim3_run(cir, params, simplify_circuit);
    eslim3_run.config.aig = false;
    eslim3_run.config.apply_strash = false;
    eslim3_run.run();
    Abc_Ntk_t* ntk_res = eslim3_run.es_man.eSLIM3CirManToNtk();
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

/**Function*************************************************************

  Synopsis    [Optimizes a mapped network and reconstructs its cell implementation.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t * eSLIM3Run<Approach, Inprocessor>::runeSLIM3Cells(Abc_Ntk_t * cir, const eSLIM3_ParamStruct* params) {
    bool simplify_circuit = false;
    eSLIM3Run<Approach, Inprocessor> eslim3_run(cir, params, simplify_circuit);
    eslim3_run.config.aig = false;
    eslim3_run.config.apply_strash = false;
    eslim3_run.run();
    Abc_Ntk_t* ntk_res = eslim3_run.es_man.eSLIM3CirManToMappedNtk();
    if (!ntk_res) {
      return ntk_res;
    }
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

/**Function*************************************************************

  Synopsis    [Executes the requested search phases and repetitions within their shared deadline.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  void eSLIM3Run<Approach, Inprocessor>::run() {
    initial_area = es_man.getNofGates();
    initial_delay = es_man.getDepth();
    config.setDepthTargets(initial_delay);
    printSettings();
    const auto overall_deadline = config.deadline;
    for (int i = 0; i < nruns && !config.expired(); i++) {
      if (nruns > 1) {
        // Reserve a fair share of the remaining overall budget for each
        // requested run. Otherwise the first unrestricted search consumes
        // the entire deadline and -R has no effect without an iteration cap.
        const auto now = std::chrono::steady_clock::now();
        config.deadline = now + (overall_deadline - now) / (nruns - i);
      }
      const auto run_deadline = config.deadline;
      if constexpr (!std::is_same_v<EmptyInprocessor, Inprocessor>) {
        // Keep a bounded tail for final processing even with no iteration cap.
        // Very short runs retain opportunistic processing only: an allowance
        // smaller than the native call's entry guard cannot do useful work.
        constexpr double final_fraction = 0.05;
        constexpr double final_cap = 10.0;
        constexpr bool timed_native = std::is_same_v<DeepsynInprocessor, Inprocessor> ||
            std::is_same_v<DelayInprocessor<true>, Inprocessor> ||
            std::is_same_v<DelayInprocessor<false>, Inprocessor>;
        constexpr double minimum_allowance = timed_native ? 3.5 : 2.5;
        const double remaining = std::chrono::duration<double>(run_deadline - std::chrono::steady_clock::now()).count();
        const double allowance = std::min(final_cap, remaining * final_fraction);
        if (allowance >= minimum_allowance)
          config.deadline -= std::chrono::duration_cast<std::chrono::steady_clock::duration>(
              std::chrono::duration<double>(allowance));
      }

      int size_iteration_start = es_man.getNofGates();
      int delay_iteration_start = es_man.getDepth();
      if (config.verbosity_level > 0) {
        std::cout << "Start eslim3 run " << i + 1 << "\n";
      }
      if (es_man.getNofGates() == 0) {
        std::cout << "Cannot further reduce the given circuit.\n";
        printLog();
        return;
      }
      if (config.area_phase_percent && config.timeout >= 4) {
        // Use the original depth allowance to recover area first. Both
        // phases share one circuit, log, checkpoint writer and deadline.
        // The original -L target is already frozen in config.depth_floor;
        // it must not be recomputed from the first phase's improved depth.
        // The copied checkpoint time may be stale after this phase. The shared
        // writer advances its own schedule, so the next callback only refreshes
        // the manager's cached deadline and cannot duplicate a snapshot.
        eSLIM3Config area = config;
        const auto now = std::chrono::steady_clock::now();
        const double remaining = std::chrono::duration<double>(config.deadline-now).count();
        area.deadline = now + std::chrono::duration_cast<std::chrono::steady_clock::duration>(
            std::chrono::duration<double>(std::max(0.0, remaining) * config.area_phase_percent / 100));
        area.depth_target_percent = 0;
        area.depth_floor = -1;
        area.initial_depth_bound = true;
        area.area_depth_bound = initial_delay;
        area.refine_depth = false;
        if (area.rewrite_mode) area.rewrite_mode = area.rewrite_mode >= 5 ? 6 : 4;
        Approach::applyeSLIM3(es_man, area, log);
      }
      if (!config.expired() && es_man.getNofGates())
        Approach::applyeSLIM3(es_man, config, log);
      int size_eslim3 = es_man.getNofGates();
      int delay_eslim3 = es_man.getDepth();
      area_change_eslim3 += size_eslim3 - size_iteration_start;
      delay_change_eslim3 += delay_eslim3 - delay_iteration_start;
      if (config.verbosity_level > 0) {
        std::cout << "eslim3 -- size: " << size_eslim3 << " delay: " << delay_eslim3 << "\n";
      }
      config.deadline = run_deadline;
      runInprocessing();
      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
        int size_inprocessing = es_man.getNofGates();
        int delay_inprocessing = es_man.getDepth();
        area_change_inprocessing += size_inprocessing - size_eslim3;
        delay_change_inprocessing += delay_inprocessing - delay_eslim3;
        if (config.verbosity_level > 0) {
          std::cout << "inprocessing -- size: " << size_inprocessing << " delay: " << delay_inprocessing << "\n";
        }
      }
      config.seed = config.seed == INT_MAX ? INT_MIN : config.seed + 1;
      config.deadline = overall_deadline;
    }
    printLog();
  }

/**Function*************************************************************

  Synopsis    [Prints the active search configuration.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  void eSLIM3Run<Approach, Inprocessor>::printSettings() {
    std::cout << "Apply eSLIM3 (overall timeout: " << config.timeout << ") ";
    std::cout << nruns << " times.\n";
    if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
      std::cout << "Apply inprocessing\n";
    }
    if (config.iterations > 0) {
      std::cout << "Stop eSLIM3 runs after " << config.iterations << " iterations.\n";
    }
    std::cout << "Consider subcircuits with up to " << config.subcircuit_max_size << " gates.\n";
    if (config.depth_floor >= 0)
      std::cout << "Protect depth gains down to " << config.depth_target_percent << "% of input levels (target " << config.depth_floor - 1 << ").\n";
    printf("When expanding subcircuits, select gates with a probability of %.2f %%.\n", 100 * config.expansion_probability);
  }

/**Function*************************************************************

  Synopsis    [Prints accumulated search, synthesis, relation and rewriting statistics.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  void eSLIM3Run<Approach, Inprocessor>::printLog() {
    if (config.verbosity_level > 0) {
      int size = es_man.getNofGates();
      int delay = es_man.getDepth();
      int total_area_change = area_change_eslim3 + area_change_inprocessing;
      int total_delay_change = delay_change_eslim3 + delay_change_inprocessing;
      std::cout << "Final size: " << size << " change: " << total_area_change << "\n";
      std::cout << "Final depth: " << delay << " change: " << total_delay_change << "\n";


      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {

        if (area_change_eslim3 <= 0) {
          std::cout << "#Gates reduced by eSLIM3: " << -area_change_eslim3 << "\n";
        } else {
          std::cout << "#Gates introduced by eSLIM3: " << area_change_eslim3 << "\n";
        }
        if (area_change_inprocessing <= 0) {
          std::cout << "#Gates reduced by inprocessing: " << -area_change_inprocessing << "\n";
        } else {
          std::cout << "#Gates introduced by inprocessing: " << area_change_inprocessing << "\n";
        }
        if (delay_change_eslim3 <= 0) {
          std::cout << "Delay reduction eSLIM3: " << -delay_change_eslim3 << "\n";
        } else {
          std::cout << "Delay increase eSLIM3: " << delay_change_eslim3 << "\n";
        }
        if (delay_change_inprocessing <= 0) {
          std::cout << "Delay reduction inprocessing: " << -delay_change_inprocessing << "\n";
        } else {
          std::cout << "Delay increase inprocessing: " << delay_change_inprocessing << "\n";
        }
      }
    }
    if (config.verbosity_level > 0) {
      std::cout << "Total #iterations: " << log.iteration_count << "\n";
      std::cout << "Neighborhood roots/unproductive root draws skipped: " << log.neighborhood_roots << "/"
                << log.failed_root_draws_skipped << "\n";
      std::cout << "Preferred-output selections/hits; MFFC gates added: " << log.preferred_output_selections << "/"
                << log.preferred_output_hits << "; " << log.mffc_gates_added << "\n";
      std::cout << "Gates added to approach preferred outputs: " << log.output_boundary_gates_added << "\n";
      std::cout << "Total relation generation time (s): " << log.relation_generation_time << "\n";
      std::cout << "Total synthesis time (s): " << log.synthesis_time << "\n";
      std::cout << "Relation phases window/sampling/encoding/SAT/other (s): "
                << log.relation_window_time << "/" << log.relation_sampling_time << "/"
                << log.relation_encoding_time << "/" << log.cummulative_sat_runtime_relation_generation << "/"
                << std::max(0.0, log.relation_generation_time - log.relation_window_time -
                    log.relation_sampling_time - log.relation_encoding_time - log.cummulative_sat_runtime_relation_generation) << "\n";
      std::cout << "Synthesis phases encoding/SAT/refinement-check/other (s): "
                << log.synthesis_encoding_time << "/" << log.synthesis_solving_time << "/"
                << log.synthesis_checking_time << "/"
                << std::max(0.0, log.synthesis_time - log.synthesis_encoding_time -
                    log.synthesis_solving_time - log.synthesis_checking_time) << "\n";
      std::cout << "Total native rewrite time (s): " << log.rewriting_time << "\n";
      std::cout << "Total final inprocessing time (s): " << log.final_inprocessing_time << "\n";
      std::cout << "Relation SAT attempts: " << log.nof_sat_relations << "\n";
      std::cout << "Relation exits total/max/any-exit queries: " << log.relation_observed_exits << "/"
                << log.relation_max_exits << "/" << log.relation_any_exit_queries << "\n";
      std::cout << "Single-output core SAT calls avoided: " << log.single_output_core_calls_skipped << "\n";
      std::cout << "Relation incomplete attempts/retries/completed fallbacks: " << log.relation_timeouts << "/" << log.relation_retries << "/" << log.relation_fallbacks << "\n";
      std::cout << "Sampled relations/patterns: " << log.nof_sampled_relations << "/" << log.sampled_relation_patterns << "\n";
      std::cout << "Cuts proven optimal before relation SAT: " << log.sampled_optimal_cuts << "\n";
      std::cout << "Local relations: " << log.nof_window_relations << "; max window gates/inputs: " << log.max_relation_window_gates << "/" << log.max_relation_window_inputs << "\n";
      std::cout << "Sampled relation seeds/tuples/time (s): " << log.nof_seeded_relations << "/" << log.seeded_relation_tuples << "/" << log.relation_sampling_time << "\n";
      std::cout << "Replacement checks passed/rejected/timed out: " << log.verified_replacements << "/" << log.rejected_replacements << "/" << log.verification_timeouts << "\n";
      std::cout << "Structurally unchanged replacements skipped: " << log.unchanged_replacements << "\n";
      std::cout << "Complete local relation cache hits: " << log.relation_cache_hits << "\n";
      std::cout << "Relation context reuse/full-cap probes: " << log.relation_context_reuses << "/" << log.relation_context_probes << "\n";
      std::cout << "Synthesis cache hits: " << log.synthesis_cache_hits << "\n";
      std::cout << "Cuts proven area/arrival optimal: " << log.proven_optimal_cuts << "\n";
      std::cout << "Cuts with existing divisors: " << log.cuts_with_divisors << "\n";
      std::cout << "Divisor candidates/sample duplicates/signature time (s): " << log.divisor_candidates << "/"
                << log.divisor_signature_duplicates << "/" << log.divisor_signature_time << "\n";
      std::cout << "Synthesis refinement rounds: " << log.synthesis_refinements << "\n";
      std::cout << "Synthesis small exact replacements: " << log.synthesis_small_hits << "\n";
      std::cout << "Synthesis cache input permutations: " << log.synthesis_cache_permutations << "\n";
      std::cout << "Synthesis cache timing improvements: " << log.synthesis_cache_timing_improvements << "\n";
      std::cout << "Synthesis depth refinement improvements/calls: " << log.depth_refinement_improvements << "/" << log.depth_refinement_calls << "\n";
      std::cout << "Synthesis relation rows encoded/available: " << log.synthesis_encoded_rows << "/" << log.synthesis_total_rows << "\n";
      std::cout << "Rewriting calls/gain: " << log.rewrite_calls << "/" << log.rewrite_gain << "\n";
      std::cout << "Rewriting calls without area/depth gain: " << log.rewrite_no_gain << "\n";
      std::cout << "Resubstitution calls/gain within rewriting: " << log.resubstitution_calls << "/" << log.resubstitution_gain << "\n";
      std::cout << "Resubstitution time (s): " << log.resubstitution_time << "\n";
      std::cout << "Synthesis searches with unrestricted timing: " << log.untimed_syntheses << "/" << log.synthesis_searches << "\n";
      std::cout << "Synthesis SAT searches: " << log.synthesis_sat_searches << "\n";
      std::cout << "Analyzed cuts by gate count:";
      for (int i = 0; i <= log.getSize(); ++i)
        if (log.nof_analyzed_circuits_per_size[i])
          std::cout << " " << i << ":" << log.nof_analyzed_circuits_per_size[i];
      std::cout << "\nAnalyzed cuts by output count:";
      for (int i = 0; i <= log.getSize(); ++i)
        if (log.nof_analyzed_circuits_per_output_count[i])
          std::cout << " " << i << ":" << log.nof_analyzed_circuits_per_output_count[i];
      std::cout << "\nSAT calls by gate count (SAT/UNSAT/interrupted):";
      for (int i = 0; i <= log.getSize(); ++i)
        if (log.nof_sat_calls_per_size[i] || log.nof_unsat_calls_per_size[i] || log.nof_interrupted_calls_per_size[i])
          std::cout << " " << i << ":" << log.nof_sat_calls_per_size[i] << "/"
                    << log.nof_unsat_calls_per_size[i] << "/" << log.nof_interrupted_calls_per_size[i];
      std::cout << "\n";
      for (int extended = 0; extended < 2; ++extended) {
        const auto& budget = extended ? log.extended_synthesis_budget : log.normal_synthesis_budget;
        std::cout << "Synthesis " << (extended ? "extended" : "normal")
                  << " budget searches/smaller models: " << budget.searches << "/" << budget.searches_with_smaller_model
                  << "; queries SAT/UNSAT/interrupted/error: " << budget.sat << "/" << budget.unsat << "/"
                  << budget.interrupted << "/" << budget.errors
                  << "; reduction queries/interrupted: " << budget.reduction_queries << "/" << budget.reduction_interruptions
                  << "; query time (s): " << budget.elapsed << "\n";
      }
      std::cout << "#Iterations with forbidden pairs: " << log.subcircuits_with_forbidden_pairs << "\n";
    }
    if (config.verbosity_level > 1) {
      printf("Relation generation: #SAT-calls: %llu, Total SAT-time: %.2f sec, Max SAT-time: %.4f sec ",
            static_cast<unsigned long long>(log.nof_sat_calls_relation_generation), log.cummulative_sat_runtime_relation_generation, log.max_sat_runtime_relation_generation);
      if (log.nof_sat_calls_relation_generation > 0) {
        printf("Avg. SAT-time: %.4f sec\n", log.cummulative_sat_runtime_relation_generation/log.nof_sat_calls_relation_generation);
      } else {
        std::cout << "Avg. SAT-time: -\n";
      }
      printf("Synthesis: #SAT-calls: %llu, Total SAT-time: %.2f sec, Max SAT-time: %.4f sec ",
            static_cast<unsigned long long>(log.nof_sat_calls_synthesis), log.cummulative_sat_runtime_synthesis / 1000, log.max_sat_runtime_synthesis / 1000);
      if (log.nof_sat_calls_synthesis > 0) {
        printf("Avg. SAT-time: %.4f sec\n", log.cummulative_sat_runtime_synthesis / (1000.0 * log.nof_sat_calls_synthesis));
      } else {
        std::cout << "Avg. SAT-time: -\n";
      }
    }
    if (config.verbosity_level > 2) {
      for (int i = 2; i < log.nof_analyzed_circuits_per_size.size(); i++) {
        int replaced = log.nof_replaced_circuits_per_size.size() > i ? log.nof_replaced_circuits_per_size[i] : 0;
        int reduced = log.nof_reduced_circuits_per_size.size() > i ? log.nof_reduced_circuits_per_size[i] : 0;
        std::cout << "#gates: " << i << " - #analysed: " << log.nof_analyzed_circuits_per_size[i] << " - #replaced: " << replaced << " - #reduced: " << reduced;
        std::cout << " - avg. relation time: ";
        if (log.nof_relation_generations_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_relation_generation_times_per_size[i]) / (log.nof_relation_generations_per_size[i]));
        }
        std::cout << "\n";
      }
      for (int i = 0; i < log.nof_sat_calls_per_size.size(); i++) {
        std::cout << "#gates: " << i << " - avg. sat time: ";
        if (log.nof_sat_calls_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_sat_runtimes_per_size[i]) / (1000.0 * log.nof_sat_calls_per_size[i]));
        }
        std::cout << " / avg. unsat time: ";
        if (log.nof_unsat_calls_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_unsat_runtimes_per_size[i]) / (1000.0 * log.nof_unsat_calls_per_size[i]));
        }
        std::cout << "\n";
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Runs the selected native optimization within its remaining-time allowance.]

***********************************************************************/
  template <typename Approach, typename Inprocessor>
  void eSLIM3Run<Approach, Inprocessor>::runInprocessing() {
    if constexpr (std::is_same_v<EmptyInprocessor, Inprocessor>) return;
    const double remaining = std::chrono::duration<double>(config.deadline - std::chrono::steady_clock::now()).count();
    if (remaining <= 2.0) return;
    if constexpr (std::is_same_v<DeepsynInprocessor, Inprocessor> ||
                  std::is_same_v<DelayInprocessor<true>, Inprocessor> ||
                  std::is_same_v<DelayInprocessor<false>, Inprocessor>) {
      const int available = int(std::min(remaining - 2.0, config.timeout * 0.1));
      if (available < 1) return;
      inprocessor.setTimeout(available);
    }
    if (config.verbosity_level > 0)
      std::cout << "Start final inprocessing (remaining: " << remaining << " sec).\n";
    const auto started = std::chrono::steady_clock::now();
    inprocessor.runInprocessing(es_man);
    log.final_inprocessing_time += std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
  }

/**Function*************************************************************

  Synopsis    [Retains the configuration for native AIG compression.]

***********************************************************************/
  DeepsynInprocessor::DeepsynInprocessor(eSLIM3Config& config)
                    : config(config) {
  }

/**Function*************************************************************

  Synopsis    [Runs the selected native optimization within its remaining-time allowance.]

***********************************************************************/
  void DeepsynInprocessor::runInprocessing(eSLIM3CirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIM3CirManToGia();
    Gia_Man_t* tmp = Gia_ManDeepSyn( pGia, 1, ABC_INFINITY, timeout, 0, config.seed , 0, 0, 0);
    if ( Gia_ManAndNum(pGia) > Gia_ManAndNum(tmp) ) {
      es_man = eSLIM3CirMan(tmp);
    }
    Gia_ManStop( tmp );
    Gia_ManStop( pGia );
  }

/**Function*************************************************************

  Synopsis    [Runs the selected native optimization within its remaining-time allowance.]

***********************************************************************/
  void MfsInprocessor::runInprocessing(eSLIM3CirMan& es_man) {
    Abc_Ntk_t* pNtk = es_man.eSLIM3CirManToNtk();
    int nnodes = Abc_NtkNodeNum(pNtk);
    Mfs_Par_t Pars, * pPars = &Pars;
    Abc_NtkMfsParsDefault( pPars );
    if ( Abc_NtkMfs( pNtk, pPars ) ) {
      Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
      if (Abc_NtkNodeNum(pNtk) <= nnodes) {
        es_man = eSLIM3CirMan(pNtk, true);
      }
    }
    Abc_NtkDelete(pNtk);
  }

/**Function*************************************************************

  Synopsis    [Retains the configuration for native depth optimization.]

***********************************************************************/
  template <bool IncreaseSize>
  DelayInprocessor<IncreaseSize>::DelayInprocessor(eSLIM3Config& config)
                                : config(config) {
  }

/**Function*************************************************************

  Synopsis    [Runs the selected native optimization within its remaining-time allowance.]

***********************************************************************/
  template <bool IncreaseSize>
  void DelayInprocessor<IncreaseSize>::runInprocessing(eSLIM3CirMan& es_man) {
    const auto started = std::chrono::steady_clock::now();
    const auto stop = std::min(config.deadline, started + std::chrono::seconds(timeout));
    if (timeout <= 0 || stop <= started) return;
    Gia_Man_t* pGia = es_man.eSLIM3CirManToGia();
    Gia_Man_t* tmp = nullptr;
    int nand = Gia_ManAndNum(pGia);
    int nlevel = Gia_ManLevelNum(pGia);
    const char * resyn2 = "balance; rewrite; rewrite -z; balance; rewrite -z; balance";
    char Command[2000];
    sprintf( Command, "strash; if -g -K 6; %s; if -K 6", resyn2 );
    bool reset_batch_mode = false ;
    if ( !Abc_FrameIsBatchMode() ) {
      reset_batch_mode = true;
      Abc_FrameSetBatchMode( 1 );
    }
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pGia );
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&put") ) {
      goto cleanup;
    }
    // Native mapping is uninterruptible. Limit final inprocessing to one
    // pass instead of repeatedly starting a pass near the deadline.
    if (std::chrono::steady_clock::now() >= stop) goto cleanup;
    {
      if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) ) {
        Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
        goto cleanup;
      }
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&get") ) {
      goto cleanup;
    }

    tmp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if constexpr (!IncreaseSize) {
      if (Gia_ManAndNum(tmp) > nand) {
        goto cleanup;
      }
    }
    if (Gia_ManLevelNum(tmp) <= nlevel) {
      es_man = eSLIM3CirMan(tmp);
    }
cleanup:
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
  }

/**Function*************************************************************

  Synopsis    [Initializes native AIG rewriting and balancing.]

***********************************************************************/
  Resyn2Inprocessor::Resyn2Inprocessor(eSLIM3Config& config)
                    // : config(config)
                    {
  }

/**Function*************************************************************

  Synopsis    [Runs the selected native optimization within its remaining-time allowance.]

***********************************************************************/
  void Resyn2Inprocessor::runInprocessing(eSLIM3CirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIM3CirManToGia();
    Gia_Man_t* tmp = nullptr;
    int nand = Gia_ManAndNum(pGia);
    int nlevel = Gia_ManLevelNum(pGia);
    const char * resyn2 = "balance; rewrite; rewrite -z; balance; rewrite -z; balance";
    bool reset_batch_mode = false ;
    if ( !Abc_FrameIsBatchMode() ) {
      reset_batch_mode = true;
      Abc_FrameSetBatchMode( 1 );
    }
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pGia );
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&put") ) {
      goto cleanup;
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), resyn2) ) {
      Abc_Print( 1, "Something did not work out with the command \"%s\".\n", resyn2 );
      goto cleanup;
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&get") ) {
      goto cleanup;
    }
    tmp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if (Gia_ManAndNum(tmp) <= nand && Gia_ManLevelNum(tmp) <= nlevel) {
      es_man = eSLIM3CirMan(tmp);
    }
cleanup:
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
  }



/**Function*************************************************************

  Synopsis    [Runs the configured optimizer and returns an independently owned result.]

***********************************************************************/
  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Approach>
  Circuitrepresentation* runeSLIM3(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
    return eSLIM3Run<Approach, Inprocessor>::runeSLIM3(cir, params);
  }

/**Function*************************************************************

  Synopsis    [Chooses serial search or partitioned windows for the requested worker count.]

***********************************************************************/
  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector, typename RootSelector>
  Circuitrepresentation* toggleWindowing(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
    if (params->nWindows > 0 || params->ncores > 1) {
      return runeSLIM3<Circuitrepresentation, Inprocessor, Minimizer, WindowMan<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    } else {
      return runeSLIM3<Circuitrepresentation, Inprocessor, Minimizer, eSLIM3_Man<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    }
  }


/**Function*************************************************************

  Synopsis    [Selects the configured root-selection policy.]

***********************************************************************/
  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector>
  Circuitrepresentation* setTabooApproach(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
    if (params->use_taboo_list) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, TabooRootSelector>(cir, params);
    } else {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, BaseRootSelector>(cir, params);
    }
  }

/**Function*************************************************************

  Synopsis    [Selects uniform or critical-path-biased root and cut growth.]

***********************************************************************/
  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection>
  Circuitrepresentation* setBiasApproach(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
    if (params->criticial_path_selection_bias) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, CriticalPathBiasSelector, CriticalPathSelector>(cir, params);
    } else {
      return setTabooApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, NoBiasSelector>(cir, params);
    }
  }



/**Function*************************************************************

  Synopsis    [Selects forward or backward subcircuit growth.]

***********************************************************************/
  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator>
  Circuitrepresentation* setSearchDirection(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
    if (params->forward_search) {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, ForwardSearch>(cir, params);
    } else {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, BackwardSearch>(cir, params);
    }
  }

/**Function*************************************************************

  Synopsis    [Selects the area or delay synthesis engine and its inprocessor.]

***********************************************************************/
  template <typename Circuitrepresentation>
  Circuitrepresentation* setMinimizer(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
    switch (params->synthesis_approach) {
      case 0:
        if (params->apply_inprocessing) {
          if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
            return setSearchDirection<Circuitrepresentation, DeepsynInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
          } else {
            return setSearchDirection<Circuitrepresentation, MfsInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
          }
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
      case 1:
        if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
          if (params->apply_inprocessing) {
            return setSearchDirection<Circuitrepresentation, Resyn2Inprocessor, AreaDelayConstraintMinimizer, SubcircuitNoFBValidator>(cir, params);
          }
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaDelayConstraintMinimizer, SubcircuitNoFBValidator>(cir, params);
      case 2:
        if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
          if (params->apply_inprocessing) {
            return setSearchDirection<Circuitrepresentation, DelayInprocessor<false>, AreaDelayMinimizer, SubcircuitNoFBValidator>(cir, params);
          }
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaDelayMinimizer, SubcircuitNoFBValidator>(cir, params);
      case 3:
        if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
          if (params->apply_inprocessing) {
            return setSearchDirection<Circuitrepresentation, DelayInprocessor<false>, DelayMinimizer, SubcircuitNoFBValidator>(cir, params);
          }
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, DelayMinimizer, SubcircuitNoFBValidator>(cir, params);
      default:
        assert(false);
        return nullptr;
    }
  }
}

/**Function*************************************************************

  Synopsis    [Runs the configured optimizer and returns an independently owned result.]

***********************************************************************/
template <typename Circuitrepresentation,
          typename std::enable_if_t<std::is_same_v<Circuitrepresentation, Gia_Man_t> ||
                                    std::is_same_v<Circuitrepresentation, Abc_Ntk_t>, int> = 0>
Circuitrepresentation* runeSLIM3(Circuitrepresentation * cir, const eSLIM3_ParamStruct* params) {
  if (params->synthesis_approach < 0 || params->synthesis_approach > 3 ||
      params->verbosity_level < 0 || params->verbosity_level > 3) {
    Abc_Print(-1, "eSLIM3: mode and verbosity must be between 0 and 3.\n");
    return NULL;
  }
  if (params->subcircuit_max_size < 2 || params->subcircuit_max_size >= unsigned(INT_MAX) ||
      params->additional_gates >= unsigned(INT_MAX) - params->subcircuit_max_size) {
    Abc_Print(-1, "eSLIM3: cut size must be at least two and the expanded size must fit an int.\n");
    return NULL;
  }
  if (!(params->expansion_probability > 0 && params->expansion_probability <= 1) ||
      params->nWindows < 0 || (params->nWindows && params->window_size < 1) ||
      (params->apply_strash && !params->use_taboo_list && !params->strash_intervall)) {
    Abc_Print(-1, "eSLIM3: invalid selection, window, or strash parameters.\n");
    return NULL;
  }
  if (params->gate_size < 2 || params->gate_size > 6 ||
      (params->aig && params->gate_size != 2) ||
      params->relation_tfo_bound < 0 || params->relation_tfi_bound < 0) {
    Abc_Print(-1, "eSLIM3: invalid gate size or relation bounds.\n");
    return NULL;
  }
  if (params->preferred_outputs > 16 || params->cut_input_limit < unsigned(params->gate_size) || params->cut_input_limit > 16) {
    Abc_Print(-1, "eSLIM3: preferred outputs must be 0 to 16 and cut inputs must be between the gate size and 16.\n");
    return NULL;
  }
  if (!params->nruns || params->nruns > unsigned(INT_MAX)) {
    Abc_Print(-1, "eSLIM3: the run count must fit a positive int.\n");
    return NULL;
  }
  if (!(params->timeout > 0 && params->timeout <= UINT_MAX)) {
    Abc_Print(-1, "eSLIM3: timeout must be positive and finite.\n");
    return NULL;
  }
  if (!(params->relation_generation_timeout > 0 && params->relation_generation_timeout <= INT_MAX)) {
    Abc_Print(-1, "eSLIM3: relation SAT budget must be positive, finite and at most INT_MAX seconds.\n");
    return NULL;
  }
  if (params->checkpoint_prefix || params->checkpoint_times) {
    if (params->timeout != unsigned(params->timeout)) {
      Abc_Print(-1, "eSLIM3: checkpoints require an integer -T timeout.\n");
      return NULL;
    }
    std::vector<unsigned> times;
    if (!params->checkpoint_prefix || !*params->checkpoint_prefix ||
        !eSLIM3::readCheckpointTimes(params->checkpoint_times, params->timeout, times)) {
      Abc_Print(-1, "eSLIM3: -O requires -K with strictly increasing positive times at most -T.\n");
      return NULL;
    }
    if (!std::is_same_v<Circuitrepresentation, Gia_Man_t> || !params->aig ||
        params->ncores != 1 || params->nWindows || params->nruns != 1 || params->synthesis_approach > 1) {
      Abc_Print(-1, "eSLIM3: checkpoints require serial AIG mode 0/1 with -R 1.\n");
      return NULL;
    }
  }
  if (params->area_phase_percent > 90) {
    Abc_Print(-1, "eSLIM3: the initial area phase must be between 0 and 90 percent.\n");
    return NULL;
  }
  if (params->rewrite_mode > 6) {
    Abc_Print(-1, "eSLIM3: rewriting mode must be between 0 and 6.\n");
    return NULL;
  }
  if (params->depth_target_percent > 100) {
    Abc_Print(-1, "eSLIM3: depth target percentage must be between 0 and 100.\n");
    return NULL;
  }
  if (params->max_divisors > 8 || params->relation_window_inputs < 2 || params->relation_window_inputs > 1024 ||
      !params->relation_window_gates || params->relation_window_gates > 16384 ||
      params->relation_window_fanin > 64 || params->relation_window_fanout > 64) {
    Abc_Print(-1, "eSLIM3: invalid local relation window limits.\n");
    return NULL;
  }
  if (params->aig_encoding > 3) {
    Abc_Print(-1, "eSLIM3: AIG encoding must be between 0 and 3.\n");
    return NULL;
  }
  if (params->synthesis_solver_mode > 6) {
    Abc_Print(-1, "eSLIM3: synthesis SAT settings must be between 0 and 6.\n");
    return NULL;
  }
  // Parallel windows support area optimization, with or without a depth bound.
  if (!params->ncores) {
    Abc_Print(-1, "eSLIM3: the worker-core limit must be positive.\n");
    return NULL;
  }
  if ((params->nWindows || params->ncores > 1) && params->synthesis_approach > 1) {
    Abc_Print(-1, "eSLIM3: windows require area optimization, with or without a depth bound.\n");
    return NULL;
  }
  return eSLIM3::setMinimizer(cir, params);
}


/**Function*************************************************************

  Synopsis    [Optimizes the supplied circuit with the configured eSLIM3 search.]

***********************************************************************/
Gia_Man_t* applyeSLIM3(Gia_Man_t * pGia, const eSLIM3_ParamStruct* params) {
  if (params->synthesis_approach == 1 && !params->aig) {
    Abc_Print(-1, "Mode 1 requires AND gates; XOR node counts do not reflect the exported AIG cost.\n");
    return NULL;
  }
  if (Gia_ManHasDangling(pGia)) {
    std::cout << "Warning: Circuit must not contain dangling nodes.\n";
    return NULL;
  }
  if (Gia_ManRegNum(pGia) > 0) {
    std::cout << "Warning: Only combinatorial circuits are supported.\n";
    return NULL;
  }
  if (Gia_ManMuxNum(pGia) > 0) {
    std::cout << "Warning: Structural Muxes are not supported.\n";
    return NULL;
  }
  if (Gia_ManXorNum(pGia) > 0) {
    std::cout << "Warning: Structural XORs are not supported.\n";
    return NULL;
  }

  // Inprocessing can replace the frame's GIA, so keep an independent backup.
  Gia_Man_t* backup = params->synthesis_approach == 1 ? Gia_ManDup(pGia) : NULL;
  Gia_Man_t* result = runeSLIM3(pGia, params);
  if (backup) {
    if (result && (Gia_ManAndNum(result) > Gia_ManAndNum(backup) ||
                   Gia_ManLevelNum(result) > Gia_ManLevelNum(backup))) {
      Abc_Print(1, "eSLIM3: rejecting a result that increases AIG size or depth.\n");
      Gia_ManStop(result);
      return backup;
    }
    Gia_ManStop(backup);
  }
  return result;
}

/**Function*************************************************************

  Synopsis    [Validates and optimizes a combinational SOP network.]

***********************************************************************/
Abc_Ntk_t* applyelSLIM3(Abc_Ntk_t * ntk, const eSLIM3_ParamStruct* params) {
  assert (Abc_NtkIsLogic(ntk));
  assert (Abc_NtkHasSop(ntk));

  // We restrict the number of fanins in order to represent truth tables by single 64-bit integers.
  // Using more fanins would also make the synthesis encoding harder, and thus larger gates would likely not be helpful anyway.
  // We might generalise the implementation to support gates with more fanins in the future.
  if (Abc_NtkGetFaninMax(ntk) > 6) {
    std::cout << "Warning: Currently only networks whose gates have at most 6 fanins are supported.\n";
    return NULL;
  }
  if (!Abc_NtkIsComb(ntk)) {
    std::cout << "Warning: Only combinatorial circuits are supported.\n";
    return NULL;
  }
  return runeSLIM3(ntk, params);
}




ABC_NAMESPACE_IMPL_END
