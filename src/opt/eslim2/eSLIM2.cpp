/**CFile****************************************************************

  FileName    [eSLIM2.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Interface to the eSLIM2 package.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM2.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <random>

#include "utils.hpp"
#include "eSLIM2Man.hpp"
#include "relationGeneration.hpp"
#include "selectionStrategies.hpp"
#include "windowMan.hpp"

#include "misc/util/abc_namespaces.h"
#include "opt/mfs/mfs.h"
#include "base/main/main.h"

#include "eSLIM2.h"
#include "eslim2CirMan.hpp"
#include "synthesisEngines.hpp"
#include "selectionStrategies.hpp"

ABC_NAMESPACE_HEADER_START
  Gia_Man_t * Gia_ManDeepSyn( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose );
  int Abc_NtkMfs( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars );
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

static eSLIM2::eSLIM2Config eSLIM2_GetCfg(const eSLIM2_ParamStruct* params) {
  eSLIM2::eSLIM2Config config;
  config.apply_strash = params->apply_strash;
  config.mux_consensus = params->mux_consensus != 0;
  config.tune_relation_solver = params->tune_relation_solver != 0;
  config.fast_simulation = params->fast_simulation != 0;
  if (params->synthesis_approach == 1) {
    config.synthesis_timeout_ms = params->synthesis_timeout_ms;
    config.compact_timing = params->compact_timing != 0;
    config.aig_encoding = params->aig_encoding;
    config.initial_depth_bound = params->initial_depth_bound != 0;
    config.rewrite_mode = params->apply_inprocessing ? params->rewrite_mode : 0;
  }
  config.fill_subcircuits = params->fill_subcircuits;
  // config.fix_seed = params->fix_seed;
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

void seteSLIM2Params(eSLIM2_ParamStruct* params) {
  params->synthesis_timeout_ms = 50;
  params->compact_timing = 1;
  params->aig_encoding = 0;
  params->mux_consensus = 0;
  params->tune_relation_solver = 1;
  params->fast_simulation = 1;
  params->initial_depth_bound = 1;
  params->rewrite_mode = 2;

  params->fill_subcircuits = 0;
  params->apply_strash = 1;
  params->fix_seed = 0;
  params->trial_limit_active = 1;
  params->apply_inprocessing = 1;
  params->synthesis_approach = 0;
  params->seed = 0;
  params->verbosity_level = 1;
  params->use_taboo_list = 0;
  params->forward_search = 0;

  params->ncores = 1;
  params->nWindows = 0;
  params->window_size = 500;

  params->criticial_path_selection_bias = 0;

  params->timeout = 1800;
  params->iterations = 0;
  params->subcircuit_max_size = 6;
  params->additional_gates = 0;
  params->strash_intervall = 100;
  params->nselection_trials = 100;
  params->nruns = 1;

  params->expansion_probability = 0.5;
  params->approximate_relation = 0;
  params->relation_tfo_bound = 0;
  params->generate_relation_with_tfi_limit = 0;
  params->relation_tfi_bound = 0;

  params->aig = 1;
  params->gate_size = 2;
}

namespace eSLIM2 {

  class DeepsynInprocessor {
    public:
      DeepsynInprocessor(eSLIM2Config& config);
      // Deepsyn interprets a timeout==0 as no timeout
      void setTimeout(int timeout) {this->timeout = timeout < 1 ? 1 : timeout;}
      void runInprocessing(eSLIM2CirMan& es_man);
    private:
      eSLIM2Config& config;
      int timeout;
  };

  class MfsInprocessor {
    public:
      MfsInprocessor(eSLIM2Config& config) {}
      void runInprocessing(eSLIM2CirMan& es_man);
  };

  class EmptyInprocessor {
    public:
      EmptyInprocessor(eSLIM2Config& config) {}
      void runInprocessing(eSLIM2CirMan& es_man) {}
  };

  template <bool IncreaseSize>
  class DelayInprocessor {
    public:
      DelayInprocessor(eSLIM2Config& config);
      void setTimeout(int timeout) {this->timeout = timeout;}
      void runInprocessing(eSLIM2CirMan& es_man);
    private:
      eSLIM2Config& config;
      int timeout;
  };

  class Resyn2Inprocessor {
    public:
      Resyn2Inprocessor(eSLIM2Config& config);
      void runInprocessing(eSLIM2CirMan& es_man);
    private:
      // eSLIM2Config& config;
  };


  template <typename Approach, typename Inprocessor>
  class eSLIM2Run {

    public:
      static Gia_Man_t* runeSLIM2(Gia_Man_t* cir, const eSLIM2_ParamStruct* params);
      static Abc_Ntk_t * runeSLIM2(Abc_Ntk_t * cir, const eSLIM2_ParamStruct* params);
      static Abc_Ntk_t * runeSLIM2Cells(Abc_Ntk_t * cir, const eSLIM2_ParamStruct* params);

    private:
      eSLIM2CirMan es_man;
      eSLIM2Config config;
      eSLIM2Log log;
      Inprocessor inprocessor;

      int initial_area;
      int initial_delay;

      int area_change_eslim2 = 0;
      int area_change_inprocessing = 0;

      int delay_change_eslim2 = 0;
      int delay_change_inprocessing = 0;

      int nruns = 0;

      eSLIM2Run(Gia_Man_t* cir, const eSLIM2_ParamStruct* params);
      eSLIM2Run(Abc_Ntk_t* cir, const eSLIM2_ParamStruct* params, bool simplify);

      void setUpInprocessor();
      void runInprocessing();

      void printSettings();
      void printLog();

      void run();
  };


  template <typename Approach, typename Inprocessor>
  eSLIM2Run<Approach, Inprocessor>::eSLIM2Run(Abc_Ntk_t* cir, const eSLIM2_ParamStruct* params, bool simplify_circuit)
                            : es_man(cir, simplify_circuit), config(eSLIM2_GetCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
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

  template <typename Approach, typename Inprocessor>
  eSLIM2Run<Approach, Inprocessor>::eSLIM2Run(Gia_Man_t* cir, const eSLIM2_ParamStruct* params)
                            : es_man(cir), config(eSLIM2_GetCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
    if (!params->fix_seed) {
      config.seed = std::random_device{}();
      if (config.verbosity_level > 0) {
        std::cout << "Set seed: " << config.seed << "\n";
      }
    }
  }

  template <typename Approach, typename Inprocessor>
  Gia_Man_t* eSLIM2Run<Approach, Inprocessor>::runeSLIM2(Gia_Man_t* cir, const eSLIM2_ParamStruct* params) {
    eSLIM2Run<Approach, Inprocessor> eslim2_run(cir, params);
    // It seems like the variables are freed by abc during preprocessing. Thus,we copy them
    char* name = Abc_UtilStrsav( cir->pName );
    char* spec = Abc_UtilStrsav( cir->pSpec );
    eslim2_run.run();
    Gia_Man_t* gia_res = eslim2_run.es_man.eSLIM2CirManToGia();
    gia_res->pName = name;
    gia_res->pSpec = spec;
    return gia_res;
  }

  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t* eSLIM2Run<Approach, Inprocessor>::runeSLIM2(Abc_Ntk_t* cir, const eSLIM2_ParamStruct* params) {
    bool simplify_circuit = true;
    eSLIM2Run<Approach, Inprocessor> eslim2_run(cir, params, simplify_circuit);
    eslim2_run.config.aig = false;
    eslim2_run.config.apply_strash = false;
    eslim2_run.run();
    Abc_Ntk_t* ntk_res = eslim2_run.es_man.eSLIM2CirManToNtk();
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t * eSLIM2Run<Approach, Inprocessor>::runeSLIM2Cells(Abc_Ntk_t * cir, const eSLIM2_ParamStruct* params) {
    bool simplify_circuit = false;
    eSLIM2Run<Approach, Inprocessor> eslim2_run(cir, params, simplify_circuit);
    eslim2_run.config.aig = false;
    eslim2_run.config.apply_strash = false;
    eslim2_run.run();
    Abc_Ntk_t* ntk_res = eslim2_run.es_man.eSLIM2CirManToMappedNtk();
    if (!ntk_res) {
      return ntk_res;
    }
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

  template <typename Approach, typename Inprocessor>
  void eSLIM2Run<Approach, Inprocessor>::run() {
    if constexpr ( std::is_same_v<DeepsynInprocessor, Inprocessor> || std::is_same_v<DelayInprocessor<true>, Inprocessor> || std::is_same_v<DelayInprocessor<false>, Inprocessor> ) {
      int time_out_inprocessing;
      if constexpr ( std::is_same_v<DeepsynInprocessor, Inprocessor> ) {
        time_out_inprocessing = config.timeout * 0.1;
      } else {
        time_out_inprocessing = config.timeout * 0.02;
      }
      config.timeout -= time_out_inprocessing;
      inprocessor.setTimeout(time_out_inprocessing);
    }

    initial_area = es_man.getNofGates();
    initial_delay = es_man.getDepth();
    if (config.initial_depth_bound)
      config.area_depth_bound = initial_delay;
    printSettings();
    for (int i = 0; i < nruns; i++) {

      int size_iteration_start = es_man.getNofGates();
      int delay_iteration_start = es_man.getDepth();
      if (config.verbosity_level > 0) {
        std::cout << "Start eslim2 run " << i + 1 << "\n";
      }
      if (es_man.getNofGates() == 0) {
        std::cout << "Cannot further reduce the given circuit.\n";
        printLog();
        return;
      }
      Approach::applyeSLIM2(es_man, config, log);
      int size_eslim2 = es_man.getNofGates();
      int delay_eslim2 = es_man.getDepth();
      area_change_eslim2 += size_eslim2 - size_iteration_start;
      delay_change_eslim2 += delay_eslim2 - delay_iteration_start;
      if (config.verbosity_level > 0) {
        std::cout << "eslim2 -- size: " << size_eslim2 << " delay: " << delay_eslim2 << "\n";
      }
      runInprocessing();
      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
        int size_inprocessing = es_man.getNofGates();
        int delay_inprocessing = es_man.getDepth();
        area_change_inprocessing += size_inprocessing - size_eslim2;
        delay_change_inprocessing += delay_inprocessing - delay_eslim2;
        if (config.verbosity_level > 0) {
          std::cout << "inprocessing -- size: " << size_inprocessing << " delay: " << delay_inprocessing << "\n";
        }
      }
      // if (config.fix_seed) {
      //   config.seed++;
      // }
      config.seed++;
    }
    printLog();
  }

  template <typename Approach, typename Inprocessor>
  void eSLIM2Run<Approach, Inprocessor>::printSettings() {
    std::cout << "Apply eSLIM2 (timeout: " << config.timeout << ") ";
    std::cout << nruns << " times.\n";
    if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
      std::cout << "Apply inprocessing\n";
    }
    if (config.iterations > 0) {
      std::cout << "Stop eSLIM2 runs after " << config.iterations << " iterations.\n";
    }
    std::cout << "Consider subcircuits with up to " << config.subcircuit_max_size << " gates.\n";
    printf("When expanding subcircuits, select gates with a probability of %.2f %%.\n", 100 * config.expansion_probability);
  }

  template <typename Approach, typename Inprocessor>
  void eSLIM2Run<Approach, Inprocessor>::printLog() {
    if (config.verbosity_level > 0) {
      int size = es_man.getNofGates();
      int delay = es_man.getDepth();
      int total_area_change = area_change_eslim2 + area_change_inprocessing;
      int total_delay_change = delay_change_eslim2 + delay_change_inprocessing;
      std::cout << "Final size: " << size << " change: " << total_area_change << "\n";
      std::cout << "Final depth: " << delay << " change: " << total_delay_change << "\n";


      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {

        if (area_change_eslim2 <= 0) {
          std::cout << "#Gates reduced by eSLIM2: " << -area_change_eslim2 << "\n";
        } else {
          std::cout << "#Gates introduced by eSLIM2: " << area_change_eslim2 << "\n";
        }
        if (area_change_inprocessing <= 0) {
          std::cout << "#Gates reduced by inprocessing: " << -area_change_inprocessing << "\n";
        } else {
          std::cout << "#Gates introduced by inprocessing: " << area_change_inprocessing << "\n";
        }
        if (delay_change_eslim2 <= 0) {
          std::cout << "Delay reduction eSLIM2: " << -delay_change_eslim2 << "\n";
        } else {
          std::cout << "Delay increase eSLIM2: " << delay_change_eslim2 << "\n";
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
      std::cout << "Total relation generation time (s): " << log.relation_generation_time << "\n";
      std::cout << "Total synthesis time (s): " << log.synthesis_time << "\n";
      std::cout << "Relations: " << log.nof_simulated_relations << " simulated, " << log.nof_sat_relations << " SAT-generated\n";
      std::cout << "Synthesis cache hits: " << log.synthesis_cache_hits << "\n";
      std::cout << "Rewriting calls/gain: " << log.rewrite_calls << "/" << log.rewrite_gain << "\n";
      std::cout << "Synthesis searches with unrestricted timing: " << log.untimed_syntheses << "/" << log.synthesis_searches << "\n";
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
        printf("Avg. SAT-time: %.4f sec\n", log.cummulative_sat_runtime_synthesis / (log.nof_sat_calls_synthesis*1000));
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
          printf("%.2f sec",  static_cast<double>(log.cummulative_sat_runtimes_per_size[i]) / (1000 * log.nof_sat_calls_per_size[i]));
        }
        std::cout << " / avg. unsat time: ";
        if (log.nof_unsat_calls_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_unsat_runtimes_per_size[i]) / (1000 * log.nof_unsat_calls_per_size[i]));
        }
        std::cout << "\n";
      }
    }
  }

  template <typename Approach, typename Inprocessor>
  void eSLIM2Run<Approach, Inprocessor>::runInprocessing() {
    inprocessor.runInprocessing(es_man);
  }

  template <typename Approach, typename Inprocessor>
  void setUpInprocessor();

  DeepsynInprocessor::DeepsynInprocessor(eSLIM2Config& config)
                    : config(config) {
  }

  void DeepsynInprocessor::runInprocessing(eSLIM2CirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIM2CirManToGia();
    Gia_Man_t* tmp = Gia_ManDeepSyn( pGia, 1, ABC_INFINITY, timeout, 0, config.seed , 0, 0, 0);
    if ( Gia_ManAndNum(pGia) > Gia_ManAndNum(tmp) ) {
      es_man = eSLIM2CirMan(tmp);
    }
    Gia_ManStop( tmp );
    Gia_ManStop( pGia );
  }

  void MfsInprocessor::runInprocessing(eSLIM2CirMan& es_man) {
    Abc_Ntk_t* pNtk = es_man.eSLIM2CirManToNtk();
    int nnodes = Abc_NtkNodeNum(pNtk);
    Mfs_Par_t Pars, * pPars = &Pars;
    Abc_NtkMfsParsDefault( pPars );
    if ( Abc_NtkMfs( pNtk, pPars ) ) {
      Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
      if (Abc_NtkNodeNum(pNtk) <= nnodes) {
        es_man = eSLIM2CirMan(pNtk, true);
      }
    }
    Abc_NtkDelete(pNtk);
  }

  template <bool IncreaseSize>
  DelayInprocessor<IncreaseSize>::DelayInprocessor(eSLIM2Config& config)
                                : config(config) {
  }

  template <bool IncreaseSize>
  void DelayInprocessor<IncreaseSize>::runInprocessing(eSLIM2CirMan& es_man) {
    abctime clkStart    = Abc_Clock();
    abctime nTimeToStop = clkStart + timeout * CLOCKS_PER_SEC;
    Gia_Man_t* pGia = es_man.eSLIM2CirManToGia();
    Gia_Man_t* tmp = nullptr;
    int nand = Gia_ManAndNum(pGia);
    int nlevel = Gia_ManLevelNum(pGia);
    char * resyn2 = "balance; rewrite; rewrite -z; balance; rewrite -z; balance";
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
    while (Abc_Clock() <= nTimeToStop) {
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
      es_man = eSLIM2CirMan(tmp);
    }
cleanup:
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
  }

  Resyn2Inprocessor::Resyn2Inprocessor(eSLIM2Config& config)
                    // : config(config)
                    {
  }

  void Resyn2Inprocessor::runInprocessing(eSLIM2CirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIM2CirManToGia();
    Gia_Man_t* tmp = nullptr;
    int nand = Gia_ManAndNum(pGia);
    int nlevel = Gia_ManLevelNum(pGia);
    char * resyn2 = "balance; rewrite; rewrite -z; balance; rewrite -z; balance";
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
      es_man = eSLIM2CirMan(tmp);
    }
cleanup:
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
  }



  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Approach>
  Circuitrepresentation* runeSLIM2(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
    return eSLIM2Run<Approach, Inprocessor>::runeSLIM2(cir, params);
  }

  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector, typename RootSelector>
  Circuitrepresentation* toggleWindowing(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
    if (params->nWindows > 0 || params->ncores > 1) {
      return runeSLIM2<Circuitrepresentation, Inprocessor, Minimizer, WindowMan<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    } else {
      return runeSLIM2<Circuitrepresentation, Inprocessor, Minimizer, eSLIM2_Man<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    }
  }


  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector>
  Circuitrepresentation* setTabooApproach(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
    if (params->use_taboo_list) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, TabooRootSelector>(cir, params);
    } else {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, BaseRootSelector>(cir, params);
    }
  }

  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection>
  Circuitrepresentation* setBiasApproach(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
    if (params->criticial_path_selection_bias) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, CriticalPathBiasSelector, CriticalPathSelector>(cir, params);
    } else {
      return setTabooApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, NoBiasSelector>(cir, params);
    }
  }



  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator>
  Circuitrepresentation* setSearchDirection(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
    if (params->forward_search) {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, ForwardSearch>(cir, params);
    } else {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, BackwardSearch>(cir, params);
    }
  }

  template <typename Circuitrepresentation>
  Circuitrepresentation* setMinimizer(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
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

template <typename Circuitrepresentation,
          typename std::enable_if_t<std::is_same_v<Circuitrepresentation, Gia_Man_t> ||
                                    std::is_same_v<Circuitrepresentation, Abc_Ntk_t>, int> = 0>
Circuitrepresentation* runeSLIM2(Circuitrepresentation * cir, const eSLIM2_ParamStruct* params) {
  // Parallel windows support area optimization, with or without a depth bound.
  if (!params->ncores) {
    Abc_Print(-1, "eSLIM2: the worker-core limit must be positive.\n");
    return NULL;
  }
  if ((params->nWindows || params->ncores > 1) && params->synthesis_approach > 1) {
    Abc_Print(-1, "eSLIM2: windows require area optimization, with or without a depth bound.\n");
    return NULL;
  }
  return eSLIM2::setMinimizer(cir, params);
}


Gia_Man_t* applyeSLIM2(Gia_Man_t * pGia, const eSLIM2_ParamStruct* params) {
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
  Gia_Man_t* result = runeSLIM2(pGia, params);
  if (backup) {
    if (result && (Gia_ManAndNum(result) > Gia_ManAndNum(backup) ||
                   Gia_ManLevelNum(result) > Gia_ManLevelNum(backup))) {
      Abc_Print(1, "eSLIM2: rejecting a result that increases AIG size or depth.\n");
      Gia_ManStop(result);
      return backup;
    }
    Gia_ManStop(backup);
  }
  return result;
}

Abc_Ntk_t* applyelSLIM2(Abc_Ntk_t * ntk, const eSLIM2_ParamStruct* params) {
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
  return runeSLIM2(ntk, params);
}




ABC_NAMESPACE_IMPL_END
