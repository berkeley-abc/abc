/**CFile****************************************************************

  FileName    [delayEngine.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Implementation of delay based SAT encoding.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include "delayEngine.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM {

  DelayEngine::DelayEngine( const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log) 
                          : RelationSynthesiser(relation, subcir, max_size, cfg, log) {
    assert (subcir.forbidden_pairs.empty());
    symmetry_selector = getNewVariable();
    symmetry_selector_assignment = symmetry_selector;
    std::set<int> unique_ats_set (subcir.arrival_times.begin(), subcir.arrival_times.end());
    unique_arrival_times = std::vector<int> (unique_ats_set.begin(), unique_ats_set.end());
    for (int i : subcir.arrival_times) {
      auto it = unique_ats_set.find(i);
      int idx = std::distance(unique_ats_set.begin(), it);
      inputid2uniqueid.push_back(idx);
    }
    setupVariables();
    constrainDelayVariables();
    setupDelayConstraints();
    max_delay = delay_selectors.begin()->first;
  }

  // do not enfore activation variables -> a minimum nof gates might forbid a realization with a certain depth.
  eSLIMCirMan DelayEngine::synthesizeMinimumDelayCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log) {
    DelayEngine synth(relation, subcir, max_size, cfg, log);
    std::vector<bool> last_model = synth.reduceDelay(max_size, delay);
    if (last_model.empty()) {
      // no replacement found
      return eSLIMCirMan(0);
    } else {
      int replacement_size = synth.getSizeFromActivationVars(last_model);
      return synth.getReplacement(last_model, replacement_size);
    }
  }

  eSLIMCirMan DelayEngine::synthesizeMinimumDelayAreaCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log) {
    DelayEngine synth(relation, subcir, max_size, cfg, log);
    std::vector<bool> last_model = synth.reduceDelay(max_size, delay);
    if (last_model.empty()) {
      // We could not even find a replacement with the same delay as the original circuit (timeout)
      // Hence, it is unlikely that we find a circuit that has the same delay but fewer gates
      return eSLIMCirMan(0); 
    } 
    int replacement_size = synth.getSizeFromActivationVars(last_model);
    int replacement_delay = synth.getDelayFromDelayVariables(last_model);
    std::vector<bool> model = synth.reduceArea(replacement_delay, replacement_size - 1);
    if (model.size() > 0) {
      replacement_size = synth.getSizeFromActivationVars(model);
      std::swap(last_model, model);
    }
    return synth.getReplacement(last_model, replacement_size);
  }

  eSLIMCirMan DelayEngine::synthesizeMinimumAreaDelayCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIMConfig& cfg, eSLIMLog& log) {
    DelayEngine synth(relation, subcir, subcir.nodes.size(), cfg, log);
    std::vector<bool> last_model = synth.reduceArea(synth.max_delay, subcir.nodes.size());
    if (last_model.empty()) {
      // We could not even find a replacement with the same area as the original circuit (timeout)
      // Hence, it is unlikely that we find a circuit that has the same area and a causes a smaller delay
      return eSLIMCirMan(0); 
    } 
    int replacement_size = synth.getSizeFromActivationVars(last_model);
    int replacement_delay = synth.getDelayFromDelayVariables(last_model);
    assert (replacement_delay > 0 || replacement_size == 0);
    if (replacement_delay > 0) { // a constant circuit has already optimal depth
      std::vector<bool> model = synth.reduceDelay(replacement_size, replacement_delay - 1);
      if (model.size() > 0) {
        replacement_size = synth.getSizeFromActivationVars(model);
        std::swap(last_model, model);
      }
    }
    return synth.getReplacement(last_model, replacement_size);
  }
    
  eSLIMCirMan DelayEngine::synthesizeMinimumAreaDelayConstraintCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, const eSLIMConfig& cfg, eSLIMLog& log) {
    DelayEngine synth(relation, subcir, subcir.nodes.size(), cfg, log);
    std::vector<bool> last_model = synth.reduceArea(delay, subcir.nodes.size());
    if (last_model.empty()) {
      return eSLIMCirMan(0); 
    } else {
      int replacement_size = synth.getSizeFromActivationVars(last_model);
      return synth.getReplacement(last_model, replacement_size);
    }
  }

  std::vector<bool> DelayEngine::reduceArea(unsigned int max_delay, unsigned int initial_area) {
    std::vector<bool> last_model;
    for (int i = initial_area; i>=0; i--) {
      double timeout = getDynamicTimeout(i);
      int status = existsReplacement(i, max_delay, timeout);
      if (status == 10) {
        last_model = solver.getModel();
        i = getSizeFromActivationVars(last_model); // it is possible that more than one gate is reduced in an iteration
      } else {
        break;
      }
    }
    return last_model;
  }
  
  std::vector<bool> DelayEngine::reduceDelay(unsigned int max_size, unsigned int initial_delay) {
    assert (delay_selectors.find(initial_delay) != delay_selectors.end());
    std::vector<bool> last_model;
    for( auto it = delay_selectors.find(initial_delay); it != delay_selectors.end(); ++it ) {
      int d = it->first;
      double timeout = getDynamicTimeout(max_size);
      int status = existsReplacement(max_size, d, timeout);
      if (status == 10) {
        last_model = solver.getModel();
      } else {
        break;
      }
    }
    return last_model;
  }

  std::vector<int> DelayEngine::getAssumptions(unsigned int delay) {
    std::vector<int> assumptions;
    for (auto const& [d, ds] : delay_selectors) {
      if (d > delay) {
        assumptions.push_back(-ds);
      }
    }
    return assumptions;
  }
  
  std::vector<int> DelayEngine::getAssumptions(unsigned int size, unsigned int delay) {
    std::vector<int> assumptions = getAssumptions(delay);
    std::vector<int> area_assumptions = getSizeAssumption(size);
    assumptions.insert(assumptions.end(), area_assumptions.begin(), area_assumptions.end());
    return assumptions;
  }

  unsigned int DelayEngine::getDelayFromDelayVariables(const std::vector<bool>& model) {
    unsigned int delay = 0;
    for (auto const& [d, dvars] : delays2delay_variables) {
      for (int v : dvars) {
        if (model[v]) {
          return d;
        }
      }
    }
    return delay;
  }

  int DelayEngine::existsReplacement(unsigned int delay, double timeout) {
    std::vector<int> assumptions = getAssumptions(delay);
    int status = timeout == 0 ? solver.solve(assumptions) : solver.solve(timeout, assumptions);
    unsigned int size = status == 10 ? getSizeFromActivationVars() : max_size;
    logRun(status, size);
    return status;
  }

  int DelayEngine::existsReplacement(unsigned int size, unsigned int delay, double timeout) {
    std::vector<int> assumptions = getAssumptions(size, delay);
    int status = timeout == 0 ? solver.solve(assumptions) : solver.solve(timeout, assumptions);
    logRun(status, size);
    return status;
  }

  void DelayEngine::setupVariables() {
    for (int i = 0; i < max_size; i++) {
      std::vector<std::vector<int>> dvars;
      for (int j = 0; j < unique_arrival_times.size(); j++) {
        dvars.push_back(getNewVariableVector(i + 1));
      }
      delay_variables.push_back(dvars);
    }
    for (int i = 0; i < subcir.outputs.size(); i++) {
      std::vector<std::vector<int>> dvars;
      for (int j = 0; j < unique_arrival_times.size(); j++) {
        dvars.push_back(getNewVariableVector(max_size + 1));
      }
      output_delays.push_back(dvars);
    }
  }

  int DelayEngine::getDelaySelector(int delay) {
    if (delay_selectors.find(delay) == delay_selectors.end()) {
      delay_selectors[delay] = getNewVariable();
    }
    return delay_selectors[delay];
  }


  void DelayEngine::constrainDelayVariables() {
    for (int i = 0; i < max_size; i++) {
      int activation_variable = gate_activation_variables[i];
      for (int j = 0; j < subcir.inputs.size(); j++) {
        solver.addClause({-activation_variable, -selection_variables[i][j], delay_variables[i][inputid2uniqueid[j]][0]});
      }
      for (int j = 0; j < unique_arrival_times.size(); j++) {
        for (int k = 0; k < i; k++) {
          int node_id = subcir.inputs.size() + k;
          for (int l = 0; l <= k; l++) {
            solver.addClause({-activation_variable, -selection_variables[i][node_id], -delay_variables[k][j][l], delay_variables[i][j][l+1]});
          }
          solver.addClause({-activation_variable, -delay_variables[i][j][k+1], delay_variables[i][j][k]});
        }
      }
    }
    for (int i = 0; i < subcir.outputs.size(); i++) {
      for (int j = 0; j < subcir.inputs.size(); j++) {
        solver.addClause({-gate_output_variables[max_size + j][i], output_delays[i][inputid2uniqueid[j]][0]});
      }
      for (int j = 0; j < unique_arrival_times.size(); j++) {
        for (int k = 0; k < max_size; k++) {
          solver.addClause({-output_delays[i][j][k+1], output_delays[i][j][k]});
          for (int l = 0; l <= k; l++) {
            solver.addClause({-gate_output_variables[k][i], -delay_variables[k][j][l], output_delays[i][j][l+1]});
          }
        }
      }
    }
  }

  void DelayEngine::setupDelayConstraints() {
    for (int i = 0; i < unique_arrival_times.size(); i++) {
      for (int o = 0; o < subcir.outputs.size(); o++) {
        for (int d = 0; d <= max_size; d++) {
          int delay = unique_arrival_times[i] + subcir.remaining_times[o] + d;
          int ds = getDelaySelector(delay);
          solver.addClause({ds, -output_delays[o][i][d]});

          delays2delay_variables[delay].push_back(output_delays[o][i][d]);
        }
      }
    }
  }

}
ABC_NAMESPACE_IMPL_END