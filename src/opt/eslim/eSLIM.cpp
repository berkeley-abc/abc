/**CFile****************************************************************

  FileName    [eSLIM.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Interface to the eSLIM package.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/


#include "utils.hpp"
#include "eSLIMMan.hpp"
#include "relationGeneration.hpp"
#include "selectionStrategies.hpp"
#include "windowMan.hpp"

#include "misc/util/abc_namespaces.h"
#include "opt/mfs/mfs.h"
#include "base/main/main.h"

#include "eSLIM.h"
#include "eslimCirMan.hpp"
#include "synthesisEngines.hpp"
#include "selectionStrategies.hpp"

ABC_NAMESPACE_HEADER_START
  Gia_Man_t * Gia_ManDeepSyn( Gia_Man_t * pGia, int nIters, int nNoImpr, int TimeOut, int nAnds, int Seed, int fUseTwo, int fChoices, int fVerbose );
  int Abc_NtkMfs( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars );
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

eSLIM::eSLIMConfig getCfg(const eSLIM_ParamStruct* params) {
  eSLIM::eSLIMConfig config;
  config.apply_strash = params->apply_strash;
  config.fill_subcircuits = params->fill_subcircuits;
  config.fix_seed = params->fix_seed;
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
  config.window_size = params->window_size;

  config.aig = params->aig;
  config.gate_size = params->gate_size;

  if (params->use_taboo_list) {
    config.apply_strash = false;
  }

  return config;
}

void seteSLIMParams(eSLIM_ParamStruct* params) {

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

namespace eSLIM {

  class DeepsynInprocessor {
    public:
      DeepsynInprocessor(eSLIMConfig& config);
      void setTimeout(int timeout) {this->timeout = timeout;}
      void runInprocessing(eSLIMCirMan& es_man);
    private:
      eSLIMConfig& config;
      int timeout;
  };

  class MfsInprocessor {
    public:
      MfsInprocessor(eSLIMConfig& config) {}
      void runInprocessing(eSLIMCirMan& es_man);
  };

  class EmptyInprocessor {
    public:
      EmptyInprocessor(eSLIMConfig& config) {}
      void runInprocessing(eSLIMCirMan& es_man) {}
  };

  template <bool IncreaseSize>
  class DelayInprocessor {
    public:
      DelayInprocessor(eSLIMConfig& config);
      void setTimeout(int timeout) {this->timeout = timeout;}
      void runInprocessing(eSLIMCirMan& es_man);
    private:
      eSLIMConfig& config;
      int timeout;
  };

  class Resyn2Inprocessor {
    public:
      Resyn2Inprocessor(eSLIMConfig& config);
      void runInprocessing(eSLIMCirMan& es_man);
    private:
      // eSLIMConfig& config;
  };


  template <typename Approach, typename Inprocessor>
  class eSLIMRun {

    public:
      static Gia_Man_t* runeSLIM(Gia_Man_t* cir, const eSLIM_ParamStruct* params);
      static Abc_Ntk_t * runeSLIM(Abc_Ntk_t * cir, const eSLIM_ParamStruct* params);
      static Abc_Ntk_t * runeSLIMCells(Abc_Ntk_t * cir, const eSLIM_ParamStruct* params);

    private:
      eSLIMCirMan es_man;
      eSLIMConfig config;
      eSLIMLog log;
      Inprocessor inprocessor;

      int initial_area;
      int initial_delay;

      int area_change_eslim = 0;
      int area_change_inprocessing = 0;

      int delay_change_eslim = 0;
      int delay_change_inprocessing = 0;

      int nruns = 0;

      eSLIMRun(Gia_Man_t* cir, const eSLIM_ParamStruct* params);
      eSLIMRun(Abc_Ntk_t* cir, const eSLIM_ParamStruct* params, bool simplify);

      void setUpInprocessor();
      void runInprocessing();

      void printSettings();
      void printLog();

      void run();
  };


  template <typename Approach, typename Inprocessor>
  eSLIMRun<Approach, Inprocessor>::eSLIMRun(Abc_Ntk_t* cir, const eSLIM_ParamStruct* params, bool simplify_circuit)
                            : es_man(cir, simplify_circuit), config(getCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
    config.aig = false;
    config.apply_strash = false;
  }

  template <typename Approach, typename Inprocessor>
  eSLIMRun<Approach, Inprocessor>::eSLIMRun(Gia_Man_t* cir, const eSLIM_ParamStruct* params)
                            : es_man(cir), config(getCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
  }

  template <typename Approach, typename Inprocessor>
  Gia_Man_t* eSLIMRun<Approach, Inprocessor>::runeSLIM(Gia_Man_t* cir, const eSLIM_ParamStruct* params) {

    eSLIMRun<Approach, Inprocessor> eslim_run(cir, params);
    // It seems like the variables are freed by abc during preprocessing. Thus,we copy them
    char* name = Abc_UtilStrsav( cir->pName );
    char* spec = Abc_UtilStrsav( cir->pSpec );
    eslim_run.run();
    Gia_Man_t* gia_res = eslim_run.es_man.eSLIMCirManToGia();
    gia_res->pName = name;
    gia_res->pSpec = spec;
    return gia_res;
  }

  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t* eSLIMRun<Approach, Inprocessor>::runeSLIM(Abc_Ntk_t* cir, const eSLIM_ParamStruct* params) {
    bool simplify_circuit = true;
    eSLIMRun<Approach, Inprocessor> eslim_run(cir, params, simplify_circuit);
    eslim_run.config.aig = false;
    eslim_run.config.apply_strash = false;
    eslim_run.run();
    Abc_Ntk_t* ntk_res = eslim_run.es_man.eSLIMCirManToNtk();
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t * eSLIMRun<Approach, Inprocessor>::runeSLIMCells(Abc_Ntk_t * cir, const eSLIM_ParamStruct* params) {
    bool simplify_circuit = false;
    eSLIMRun<Approach, Inprocessor> eslim_run(cir, params, simplify_circuit);
    eslim_run.config.aig = false;
    eslim_run.config.apply_strash = false;
    eslim_run.run();
    Abc_Ntk_t* ntk_res = eslim_run.es_man.eSLIMCirManToMappedNtk();
    if (!ntk_res) {
      return ntk_res;
    }
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::run() {
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
    printSettings();
    for (int i = 0; i < nruns; i++) {

      int size_iteration_start = es_man.getNofGates();
      int delay_iteration_start = es_man.getDepth();
      if (config.verbosity_level > 0) {
        std::cout << "Start eslim run " << i + 1 << "\n";
      }
      Approach::applyeSLIM(es_man, config, log);
      int size_eslim = es_man.getNofGates();
      int delay_eslim = es_man.getDepth();
      area_change_eslim += size_eslim - size_iteration_start;
      delay_change_eslim += delay_eslim - delay_iteration_start;
      if (config.verbosity_level > 0) {
        std::cout << "eslim -- size: " << size_eslim << " delay: " << delay_eslim << "\n";
      }
      runInprocessing();
      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
        int size_inprocessing = es_man.getNofGates();
        int delay_inprocessing = es_man.getDepth();
        area_change_inprocessing += size_inprocessing - size_eslim;
        delay_change_inprocessing += delay_inprocessing - delay_eslim;
        if (config.verbosity_level > 0) {
          std::cout << "inprocessing -- size: " << size_inprocessing << " delay: " << delay_inprocessing << "\n";
        }
      }
      if (config.fix_seed) {
        config.seed++;
      }
    }
    printLog();
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::printSettings() {
    std::cout << "Apply eSLIM (timeout: " << config.timeout << ") ";
    std::cout << nruns << " times.\n";
    if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
      std::cout << "Apply inprocessing\n";
    }
    if (config.iterations > 0) {
      std::cout << "Stop eSLIM runs after " << config.iterations << " iterations.\n";
    }
    std::cout << "Consider subcircuits with up to " << config.subcircuit_max_size << " gates.\n";
    printf("When expanding subcircuits, select gates with a probability of %.2f %%.\n", 100 * config.expansion_probability);
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::printLog() {
    if (config.verbosity_level > 0) {
      int size = es_man.getNofGates();
      int delay = es_man.getDepth();
      int total_area_change = area_change_eslim + area_change_inprocessing;
      int total_delay_change = delay_change_eslim + delay_change_inprocessing;
      std::cout << "Final size: " << size << " change: " << total_area_change << "\n";
      std::cout << "Final depth: " << delay << " change: " << total_delay_change << "\n";


      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {

        if (area_change_eslim <= 0) {
          std::cout << "#Gates reduced by eSLIM: " << -area_change_eslim << "\n";
        } else {
          std::cout << "#Gates introduced by eSLIM: " << area_change_eslim << "\n";
        }
        if (area_change_inprocessing <= 0) {
          std::cout << "#Gates reduced by inprocessing: " << -area_change_inprocessing << "\n";
        } else {
          std::cout << "#Gates introduced by inprocessing: " << area_change_inprocessing << "\n";
        }
        if (delay_change_eslim <= 0) {
          std::cout << "Delay reduction eSLIM: " << -delay_change_eslim << "\n";
        } else {
          std::cout << "Delay increase eSLIM: " << delay_change_eslim << "\n";
        }
        if (delay_change_inprocessing <= 0) {
          std::cout << "Delay reduction inprocessing: " << -delay_change_inprocessing << "\n";
        } else {
          std::cout << "Delay increase inprocessing: " << delay_change_inprocessing << "\n";
        }
      }
    }
    if (config.verbosity_level > 1) {
      std::cout << "Total #iterations: " << log.iteration_count << "\n";
      std::cout << "Total relation generation time (s): " << log.relation_generation_time << "\n";
      std::cout << "Total synthesis time (s): " << log.synthesis_time << "\n";
      std::cout << "#Iterations with forbidden pairs: " << log.subcircuits_with_forbidden_pairs << "\n";
      printf("Relation generation: #SAT-calls: %lu, Total SAT-time: %.2f sec, Max SAT-time: %.4f sec, Avg. SAT-time: %.4f sec\n",  
            log.nof_sat_calls_relation_generation, log.cummulative_sat_runtime_relation_generation, log.max_sat_runtime_relation_generation, 
            log.cummulative_sat_runtime_relation_generation/log.nof_sat_calls_relation_generation);
      printf("Synthesis: #SAT-calls: %lu, Total SAT-time: %.2f sec, Max SAT-time: %.4f sec, Avg. SAT-time: %.4f sec\n",  
            log.nof_sat_calls_synthesis, log.cummulative_sat_runtime_synthesis / 1000, log.max_sat_runtime_synthesis / 1000,
            log.cummulative_sat_runtime_synthesis / (log.nof_sat_calls_synthesis*1000));
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
  void eSLIMRun<Approach, Inprocessor>::runInprocessing() {
    inprocessor.runInprocessing(es_man);
  }

  template <typename Approach, typename Inprocessor>
  void setUpInprocessor();

  DeepsynInprocessor::DeepsynInprocessor(eSLIMConfig& config)
                    : config(config) {
  }

  void DeepsynInprocessor::runInprocessing(eSLIMCirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIMCirManToGia();
    Gia_Man_t* tmp = Gia_ManDeepSyn( pGia, 1, ABC_INFINITY, timeout, 0, config.seed , 0, 0, 0);
    if ( Gia_ManAndNum(pGia) > Gia_ManAndNum(tmp) ) {
      es_man = eSLIMCirMan(tmp);
    }
    Gia_ManStop( tmp );
    Gia_ManStop( pGia );
  }

  void MfsInprocessor::runInprocessing(eSLIMCirMan& es_man) {
    Abc_Ntk_t* pNtk = es_man.eSLIMCirManToNtk();
    int nnodes = Abc_NtkNodeNum(pNtk);
    Mfs_Par_t Pars, * pPars = &Pars;
    Abc_NtkMfsParsDefault( pPars );
    if ( Abc_NtkMfs( pNtk, pPars ) ) {
      Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
      if (Abc_NtkNodeNum(pNtk) <= nnodes) {
        es_man = eSLIMCirMan(pNtk, true);
      }
    }
    Abc_NtkDelete(pNtk);
  }

  template <bool IncreaseSize>
  DelayInprocessor<IncreaseSize>::DelayInprocessor(eSLIMConfig& config)
                                : config(config) {
  }

  template <bool IncreaseSize>
  void DelayInprocessor<IncreaseSize>::runInprocessing(eSLIMCirMan& es_man) {
    abctime clkStart    = Abc_Clock();
    abctime nTimeToStop = clkStart + timeout * CLOCKS_PER_SEC;
    Gia_Man_t* pGia = es_man.eSLIMCirManToGia();
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
      return;
    }
    while (Abc_Clock() <= nTimeToStop) {
      if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) ) {
        Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
        return;
      }
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&get") ) {
      return;
    }
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
    Gia_Man_t* tmp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if constexpr (!IncreaseSize) {
      if (Gia_ManAndNum(tmp) > nand) {
        return;
      }
    }
    if (Gia_ManLevelNum(tmp) <= nlevel) {
      es_man = eSLIMCirMan(tmp);
    }
  }

  Resyn2Inprocessor::Resyn2Inprocessor(eSLIMConfig& config)
                    // : config(config) 
                    {
  }

  void Resyn2Inprocessor::runInprocessing(eSLIMCirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIMCirManToGia();
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
      return;
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), resyn2) ) {
      Abc_Print( 1, "Something did not work out with the command \"%s\".\n", resyn2 );
      return;
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&get") ) {
      return;
    }
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
    Gia_Man_t* tmp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if (Gia_ManAndNum(tmp) <= nand && Gia_ManLevelNum(tmp) <= nlevel) {
      es_man = eSLIMCirMan(tmp);
    }
  }



  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Approach>
  Circuitrepresentation* runeSLIM(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    return eSLIMRun<Approach, Inprocessor>::runeSLIM(cir, params); 
  }

  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector, typename RootSelector>
  Circuitrepresentation* toggleWindowing(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->nWindows > 0) {
      return runeSLIM<Circuitrepresentation, Inprocessor, Minimizer, WindowMan<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    } else {
      return runeSLIM<Circuitrepresentation, Inprocessor, Minimizer, eSLIM_Man<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    }
  }


  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector>
  Circuitrepresentation* setTabooApproach(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->use_taboo_list) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, TabooRootSelector>(cir, params);
    } else {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, BaseRootSelector>(cir, params);
    }
  }

  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection>
  Circuitrepresentation* setBiasApproach(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->criticial_path_selection_bias) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, CriticalPathBiasSelector, CriticalPathSelector>(cir, params);
    } else {
      return setTabooApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, NoBiasSelector>(cir, params);
    }
  }



  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator>
  Circuitrepresentation* setSearchDirection(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->forward_search) {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, ForwardSearch>(cir, params);
    } else {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, BackwardSearch>(cir, params);
    }
  }

  template <typename Circuitrepresentation>  
  Circuitrepresentation* setMinimizer(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
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
        return NULL;
    }
  }
}

template <typename Circuitrepresentation> 
Circuitrepresentation* runeSLIM(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
  // Windowing does currently not support Deleyconstraints/Delayoptimisation
  if (params->nWindows && params->synthesis_approach != 0) {
    return NULL;
  }
  return eSLIM::setMinimizer(cir, params);
}


Gia_Man_t* applyeSLIM(Gia_Man_t * pGia, const eSLIM_ParamStruct* params) {
  if (Gia_ManHasDangling(pGia)) {
    std::cout << "Warning: Circuit must not contain dangling nodes.\n";
    return pGia;
  }
  return runeSLIM(pGia, params);
}

Abc_Ntk_t* applyelSLIM(Abc_Ntk_t * ntk, const eSLIM_ParamStruct* params) {
  return runeSLIM(ntk, params);
}




ABC_NAMESPACE_IMPL_END
