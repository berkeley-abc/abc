/**CFile****************************************************************

  FileName    [eSLIMMan.tpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [eSLIM manager.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - March 2025.]

  Revision    [$Id: eSLIMMan.hpp,v 1.00 2025/03/17 00:00:00 Exp $]

***********************************************************************/

#include <climits>

#include "eSLIMMan.hpp"
#include "synthesisEngines.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM_Man<SynthesisEngine, SelectionStrategy>::applyeSLIM(eSLIMCirMan& cir, const eSLIMConfig& cfg, eSLIMLog& log) {
    eSLIM_Man eslim(cir, cfg, log);
    eslim.optimize();
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIM_Man<SynthesisEngine, SelectionStrategy>::eSLIM_Man(eSLIMCirMan& es_man, const eSLIMConfig& cfg, eSLIMLog& log)
            : es_man(es_man), selection_strategy(this->es_man, cfg, log), cfg(cfg), log(log) {
    // if (cfg.fix_seed) {
    //   selection_strategy.setSeed(cfg.seed);
    // }
    selection_strategy.setSeed(cfg.seed);
    relation_generation_time = log.relation_generation_time;
    synthesis_time = log.synthesis_time;
  }



  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM_Man<SynthesisEngine, SelectionStrategy>::optimize() {
    abctime clkStart    = Abc_Clock();
    abctime nTimeToStop = clkStart + cfg.timeout * CLOCKS_PER_SEC;
    unsigned int iteration = 0;
    unsigned int iterMax = cfg.iterations ? cfg.iterations - 1 : UINT_MAX;
    int current_size = es_man.getNofGates();
    const char* node_type = cfg.aig ? "#and" : "#nd"; 
    while (Abc_Clock() <= nTimeToStop && iteration <= iterMax && !stopeSLIM && es_man.getNofGates() > 0) {
      iteration++;
      findReplacement();
      if (cfg.apply_strash && iteration % cfg.strash_intervall == 0) {
        Gia_Man_t* pTemp = es_man.eSLIMCirManToGia();
        Gia_Man_t* gia_man = Gia_ManRehash( pTemp, 0 );
        Gia_ManStop( pTemp );
        es_man = eSLIMCirMan(gia_man);
        Gia_ManStop( gia_man );
        selection_strategy.reset();
      }
      if (cfg.verbosity_level > 0) {
        int sz = es_man.getNofGates();
        if (sz < current_size) {
          current_size = sz;
          printf("\rIteration %8d : %s = %7d elapsed time = %7.2f sec\n", iteration, node_type, sz, (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC);
        } else {
          printf("\rIteration %8d", iteration);
          fflush(stdout);
        }
      }
    }
    log.iteration_count += iteration;
    if (cfg.verbosity_level > 0) {
      int sz = es_man.getNofGates();
      printf("\r#Iterations %8d %s = %7d elapsed time = %7.2f sec\n", iteration, node_type, sz, (float)1.0*(Abc_Clock() - clkStart)/CLOCKS_PER_SEC);
      if (cfg.verbosity_level > 1) {
        printf("Relation generation time: %.2f sec\n", log.relation_generation_time - relation_generation_time);
        printf("Synthesis time: %.2f sec\n", log.synthesis_time - synthesis_time);
      } 
    }
  }

  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIMCirMan eSLIM_Man<SynthesisEngine, SelectionStrategy>::computeReplacement(Subcircuit& subcir) {
    abctime relation_generation_start = Abc_Clock();
    Relation rel = RelationGenerator::computeRelation(es_man, subcir, cfg, log);
    log.relation_generation_time += (double)1.0*(Abc_Clock() - relation_generation_start)/CLOCKS_PER_SEC;
    log.cummulative_relation_generation_times_per_size[subcir.nodes.size()] += (double)1.0*(Abc_Clock() - relation_generation_start) / CLOCKS_PER_SEC;
    log.nof_relation_generations_per_size[subcir.nodes.size()]++;
    if (!rel.getStatus()) {
      return eSLIMCirMan(0);
    }
    abctime synthesis_start = Abc_Clock();
    eSLIMCirMan replacement = synthesiseRelation(subcir, rel);
    log.synthesis_time += (double)1.0*(Abc_Clock() - synthesis_start)/CLOCKS_PER_SEC;
    return replacement;
  }


  template <typename SynthesisEngine, typename SelectionStrategy>
  eSLIMCirMan eSLIM_Man<SynthesisEngine, SelectionStrategy>::synthesiseRelation(Subcircuit& subcir, const Relation& rel) {
    return SynthesisEngine::optimize(es_man, rel, subcir, cfg, log);
  }


  template <typename SynthesisEngine, typename SelectionStrategy>
  void eSLIM_Man<SynthesisEngine, SelectionStrategy>::findReplacement() {
    bool status = true;
    if constexpr (SelectionStrategy::requiresRemainingTimes() || isDelayEngine<SynthesisEngine>::value) {
      es_man.setupTimings();
    }
    Subcircuit subcir = selection_strategy.getSubcircuit(status);
    if (!status) {
      if (cfg.trial_limit_active) {
        stopeSLIM = true;
      }
      return;
    }
    eSLIMCirMan replacement = computeReplacement(subcir);

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