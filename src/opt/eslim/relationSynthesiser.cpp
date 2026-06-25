/**CFile****************************************************************

  FileName    [relationSynthesiser.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Base class for SAT-based synthesis]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <cassert>

#include "relationSynthesiser.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM {

  RelationSynthesiser::RelationSynthesiser(const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log)
                                          : subcir(subcir), max_size(max_size),
                                            relation(relation), config(cfg), log(log) {
    setupEncoding();
  }

  double RelationSynthesiser::getDynamicTimeout(int size) {
    if (log.nof_sat_calls_per_size[size] > config.minimum_dynamic_timeout_sample_size) {
      return std::max(static_cast<double>(config.minimum_sat_timeout), static_cast<double>(log.cummulative_sat_runtimes_per_size[size]) / (1000*log.nof_sat_calls_per_size[size])); //logged timings are given in ms
    } else {
      return config.base_sat_timeout;
    }
  }

  unsigned int RelationSynthesiser::getSizeFromActivationVars(const std::vector<bool>& model) {
    unsigned int sz = 0;
    for (int i = 0; i < max_size; i++) {
      if (model[gate_activation_variables[i]]) {
        sz++;
      } else {
        break;
      }
    }
    return sz;
  }

  unsigned int RelationSynthesiser::getSizeFromActivationVars() {
    unsigned int sz = 0;
    for (int i = 0; i < max_size; i++) {
      if (solver.getValue(gate_activation_variables[i])) {
        sz++;
      } else {
        break;
      }
    }
    return sz;
  }

  void RelationSynthesiser::logRun(int status, unsigned int size) {
    log.cummulative_sat_runtime_synthesis += solver.getRunTime();
    log.max_sat_runtime_synthesis = std::max(log.max_sat_runtime_synthesis, solver.getRunTime());

    log.nof_sat_calls_synthesis++;
    if (status == 10) {
      log.cummulative_sat_runtimes_per_size[size] += solver.getRunTime();
      log.nof_sat_calls_per_size[size] ++;
    } else if (status == 20) { //if the solver does not report sat the formula is unsat or there was a timeout
      log.cummulative_unsat_runtimes_per_size[size] += solver.getRunTime();
      log.nof_unsat_calls_per_size[size] ++;
    }
  }

  std::vector<int> RelationSynthesiser::getSizeAssumption(int size) {
    std::vector<int> assumptions;
    assumptions.reserve(max_size - size);
    for (int i = size; i < max_size; i++) {
      assumptions.push_back(-gate_activation_variables[i]);
    }
    return assumptions;
  }

  eSLIMCirMan RelationSynthesiser::getReplacement(const std::vector<bool>& model, int size) {
    assert (model.size() > 0);
    eSLIMCirMan circ(subcir.inputs.size() + subcir.outputs.size() + size);
    for (int i = 0; i < subcir.inputs.size(); i++) {
      circ.addPi();
    }
    
    for (int i = 0; i < size; i++) {
      std::vector<int> fanins;
      for (int j = 0; j < selection_variables[i].size(); j++) {
        if (model[selection_variables[i][j]]) {
          fanins.push_back(j+1);
        }
      }
      ABC_UINT64_T tt = 0;
      for (int j = 0; j < gate_definition_variables[i].size(); j++) {
        int idx = j + 1;
        if (model[gate_definition_variables[i][j]]) {
          tt |= static_cast<ABC_UINT64_T>(1) << idx;
        }
      }
      circ.addNode(fanins, tt);
    }

    // outputs
    for (int i = 0; i < subcir.outputs.size(); i++) {
      for (int j = 0; j < max_size; j++) {
        if (model[gate_output_variables[j][i]]) {
          circ.addPo(subcir.inputs.size() + j + 1, false);
          goto end;
        }
      }
      for (int j = 0; j < subcir.inputs.size(); j++) {
        if (model[gate_output_variables[max_size + j][i]]) {
          circ.addPo(j + 1, false);
          goto end;
        }
      }
      if (model[gate_output_variables.back()[i]]) {
        circ.addPo(0, false);
      }
      end:;
    }
    return circ;
  }

  void RelationSynthesiser::setupEncoding() {
    setupVariables();
    setupStructuralConstraints();
    setupSymmetryBreaking();
    setupEquivalenceConstraints();
  }

  void RelationSynthesiser::setupVariables() {
    gate_activation_variables.reserve(max_size);
    selection_variables.reserve(max_size);
    gate_definition_variables.reserve(max_size);
    gate_variables.reserve(max_size);
    is_ith_fanin_variable.reserve(max_size);
    for (int i = 0; i < max_size; i++) {
      gate_activation_variables.push_back(getNewVariable());
      selection_variables.push_back(getNewVariableVector(subcir.inputs.size() + i));
      gate_definition_variables.push_back(getNewVariableVector(pow2(config.gate_size) - 1));
      // The replacement circuit shall be normal so we ignore the all-false-behaviour
      int normality_offset = relation.getPatternSize(0) > 0;
      gate_variables.push_back(getNewVariableVector(relation.getNLinesWithPattern() - normality_offset));

      std::vector<std::vector<int>> fanin_vars;
      for (int j = 0; j < config.gate_size; j++) {
        std::vector<int> fvs(subcir.inputs.size() + i, 0);
        for (int k = j; k < subcir.inputs.size() + i - config.gate_size + j + 1; k++) {
          fvs[k] = getNewVariable();
        }
        fanin_vars.push_back(fvs);
      }
      is_ith_fanin_variable.push_back(fanin_vars);
    }
    gate_output_variables.reserve(max_size + subcir.inputs.size() + 1);
    for (int i = 0; i < max_size + subcir.inputs.size() + 1; i++) {
      gate_output_variables.push_back(getNewVariableVector(subcir.outputs.size()));
    }
  }

  void RelationSynthesiser::setupStructuralConstraints() {
    constrainSelectionVariables();
    constraintGateOutputVariables();
    setupActivationCompatibilityConstraints();
    if (config.aig) {
      setupAigerConstraints();
    }
  }

  void RelationSynthesiser::setupSymmetryBreaking() {
    addNonTrivialConstraint();
    addUseAllStepsConstraint();
    // addNoReapplicationConstraint();
    // addOrderedStepsConstraint();    
  }

  void RelationSynthesiser::setupIsFaninVariables(int gtidx, const std::vector<std::vector<int>>& counter_vars) {
    // If we have 3 inputs and gates with two fanins then the first fanin of the first gate can be input 1 or 2 but not input 3.
    int noptions = subcir.inputs.size() + gtidx - config.gate_size + 1;
    for (int i = 0; i < config.gate_size; i++) {
      solver.addClause({-counter_vars[i][i], is_ith_fanin_variable[gtidx][i][i]});
      solver.addClause({counter_vars[i][i], -is_ith_fanin_variable[gtidx][i][i]});
      int offset = (i == config.gate_size - 1); // we do not use block variables for the last selection variables
      for (int j = i + 1; j < i + noptions - offset; j++) {
        solver.addClause({counter_vars[j - 1][i], counter_vars[j][i], -is_ith_fanin_variable[gtidx][i][j]});
        solver.addClause({counter_vars[j - 1][i], -counter_vars[j][i], is_ith_fanin_variable[gtidx][i][j]});
      }
    }
    solver.addClause({selection_variables[gtidx].back(), -is_ith_fanin_variable[gtidx].back().back()});
    solver.addClause({-selection_variables[gtidx].back(), is_ith_fanin_variable[gtidx].back().back()});
  }

  void RelationSynthesiser::constrainSelectionVariables() {
    int start = 0;
    // if the subcircuit has k inputs and gates have k fanins each input is a fanin of the first gate
    if (selection_variables[0].size() == config.gate_size) {
      start = 1;
      for (int j = 0; j < config.gate_size; j++) {
        solver.addClause({selection_variables[0][j]});
        solver.addClause({is_ith_fanin_variable[0][j][j]});
      }
    }
    for (int i = start; i < max_size; i++) {
      std::vector<std::vector<int>> counter_vars = addSequentialCounter(selection_variables[i], config.gate_size);
      setupIsFaninVariables(i, counter_vars);
    }
  }

  void RelationSynthesiser::constraintGateOutputVariables() {
    // If the activation variable is false then the gate must not be an output
    for (int i = 0; i < max_size; i++) {
      for (int v : gate_output_variables[i]) {
        solver.addClause({gate_activation_variables[i], -v});
      }
    }
    for (int i = 0; i < subcir.outputs.size(); i++) {
      std::vector<int> clause;
      clause.reserve(max_size + subcir.inputs.size() + 1);
      for (int j = 0; j < max_size + subcir.inputs.size() + 1; j++) {
        clause.push_back(gate_output_variables[j][i]);
      }
      addCardinalityConstraint(clause, 1);
    }
  }

  void RelationSynthesiser::addGateValueConstraint(int gtidx, int gt_val, const std::vector<int>& fanin_variables) {
    // If all fanins are 0, then the gate yields 0
    std::vector<int> clause {-gate_activation_variables[gtidx]};
    clause.reserve(config.gate_size + 3);
    for (int j = 0; j < config.gate_size; j++) {
      clause.push_back(fanin_variables[j]);
    }
    clause.push_back(-gt_val);
    solver.addClause(clause);
    clause.push_back(0);
    
    for (int i = 1; i < pow2(config.gate_size); i++) { // we consider normal gates -> the all-0-behaviour does not need to be considered
      for (int j = 0; j < config.gate_size; j++) {
        clause[j + 1] = abs(clause[j + 1]) * (1-2*getTTValue(i, j));
      }
      int gdv = gate_definition_variables[gtidx][i - 1]; // we do not use a gdv for the all-0-behaviour
      clause[config.gate_size + 1] = -gdv;
      clause[config.gate_size + 2] = gt_val;
      solver.addClause(clause);
      clause[config.gate_size + 1] = gdv;
      clause[config.gate_size + 2] = -gt_val;
      solver.addClause(clause);
    }
  }

  std::vector<int> RelationSynthesiser::setupFaninVariables(int gtidx, int tt_line, int pidx) {
    int noptions = subcir.inputs.size() + gtidx - config.gate_size + 1;
    std::vector<int> fanin_variables = getNewVariableVector(config.gate_size);
    for (int i = 0; i < config.gate_size; i++) {
      int bound = i + noptions < subcir.inputs.size() ? i + noptions : subcir.inputs.size();
      for (int j = i; j < bound; j++) {
        if (getTTValue(tt_line, j)) {
          solver.addClause({-is_ith_fanin_variable[gtidx][i][j], fanin_variables[i]});
        } else {
          solver.addClause({-is_ith_fanin_variable[gtidx][i][j], -fanin_variables[i]});
        }
      }
      for (int j = subcir.inputs.size(); j < i + noptions; j++) {
        solver.addClause({-is_ith_fanin_variable[gtidx][i][j], gate_variables[j - subcir.inputs.size()][pidx], -fanin_variables[i]});
        solver.addClause({-is_ith_fanin_variable[gtidx][i][j], -gate_variables[j - subcir.inputs.size()][pidx], fanin_variables[i]});
      }
    }
    return fanin_variables;
  }

  void RelationSynthesiser::setupGateValues() {
    int pidx = 0;
    for (int i = 1; i < relation.getNPatterns(); i++) {
      if (relation.getPatternSize(i) > 0) {
        for (int j = 0; j < max_size; j++) {
          std::vector<int> fanin_variables = setupFaninVariables(j, i, pidx);   
          addGateValueConstraint(j, gate_variables[j][pidx], fanin_variables);
        }
        pidx++;
      }
    }
  }

  void RelationSynthesiser::setupEquivalenceConstraints() {
    setupGateValues();
    // normal circuit: all-0-behaviour is ignored
    int pidx = 0;
    for (int i = 1; i < relation.getNPatterns(); i++) {
      std::vector<int> output_vars (subcir.outputs.size(), 0);
      const auto& patterns = relation.getPattern(i);
      for (const auto& p : patterns) {
        assert(2 * subcir.outputs.size() == p.size());
        std::vector<int> cl;
        for (int j = 0; j < subcir.outputs.size(); j++) { 
          if (p[2*j]) {
            if (output_vars[j] == 0) {
              output_vars[j] = setupOutputVariable(j, i, pidx);
            }
            if (p[2*j + 1]) {
              cl.push_back(output_vars[j]);
            } else {
              cl.push_back(-output_vars[j]);
            }
          }
        }
        solver.addClause(cl);
      }
      pidx += !patterns.empty();
    }
  }

  void RelationSynthesiser::setupActivationCompatibilityConstraints() {
    for (int i = 1; i < max_size; i++) {
      solver.addClause({-gate_activation_variables[i], gate_activation_variables[i-1]});
    }
  }

  int RelationSynthesiser::setupOutputVariable(int output_index, int tt_index, int pattern_idx) {
    int var = getNewVariable();
    std::vector<int> clause;
    for (int i = 0; i < max_size; i++) {
      clause.assign({-gate_activation_variables[i], -gate_output_variables[i][output_index], -gate_variables[i][pattern_idx], var});
      solver.addClause(clause);
      clause[2] = -clause[2];
      clause[3] = -clause[3];
      solver.addClause(clause);
    }
    
    for (int i = 0; i < subcir.inputs.size(); i++) {
      if (getTTValue(tt_index, i)) {
        clause.assign({-gate_output_variables[i + max_size][output_index], var});
      } else {
        clause.assign({-gate_output_variables[i + max_size][output_index], -var});
      }
      solver.addClause(clause);
    }

    clause.assign({-gate_output_variables.back()[output_index], -var});
    solver.addClause(clause);
    return var;
  }

  void RelationSynthesiser::setupAigerConstraints() {
    assert (config.gate_size == 2);
    for (int i = 0; i < max_size; i++) {
      solver.addClause({-gate_definition_variables[i][0], -gate_definition_variables[i][1], gate_definition_variables[i][2]});
    }
  }

  void RelationSynthesiser::addCardinalityConstraint(const std::vector<int>& vars, unsigned int cardinality, int activator) {
    assert (cardinality > 0);
    assert (vars.size() >= cardinality);
    if (vars.size() == cardinality) {
      std::vector<int> clause;
      if (activator != 0) {
        clause.push_back(activator);
      }
      for (int var : vars) {
        clause.push_back(var);
        solver.addClause(clause);
        clause.pop_back();
      }
    } else {
      // CHECK: is the naive encoding better?
      if (activator == 0) {
        if (cardinality == 1) {
          addNaiveIs1CardinalityConstraint(vars);
        } else if (cardinality == 2) {
          addNaiveIs2CardinalityConstraint(vars);
        } else {
          addSequentialCounter(vars, cardinality, activator);
        }
      } else {
        addSequentialCounter(vars, cardinality, activator);
      }
    }
  }

  // see Carsten Sinz: Towards an Optimal CNF Encoding of Boolean Cardinality Constraints
  // As we want that exactly cardinality many variables are set to true we need additional constraints.
  // Because of this reason we cannot use the single polarity encoding presented in the paper
  std::vector<std::vector<int>> RelationSynthesiser::addSequentialCounter(const std::vector<int>& vars, unsigned int cardinality, int activator) {
    std::vector<std::vector<int>> component_outputs;
    component_outputs.push_back({vars.front()});
    assert (vars.size() > cardinality);
    for (int i = 1; i < vars.size() - 1; i++) {
      std::vector<int> current_component_outputs;
      int v = vars[i];
      int in_var = v;
      for (int j = 0; j < component_outputs.back().size(); j++) {
        int orv  = getNewVariable();
        defineDisjunction(orv, {in_var, component_outputs.back()[j]}, activator);
        current_component_outputs.push_back(orv);
        if (j < cardinality - 1) {
          in_var = getNewVariable();
          defineConjunction(in_var, {v, component_outputs.back()[j]}, activator);
        } else {
          solver.addClause({-component_outputs.back().back(), -v});
        }
      }
      if (component_outputs.back().size() < cardinality) {
        current_component_outputs.push_back(in_var);
      }
      component_outputs.push_back(current_component_outputs);
    }

    solver.addClause({-component_outputs.back().back(), -vars.back()});

    // Either subcircuit_outputs.back() is true or subcircuit_outputs[-2] and vars.back() is true
    std::vector<int> clause {component_outputs.back().back(), vars.back()};
    solver.addClause(clause);
    if (cardinality > 1) {
      clause.pop_back();
      clause.push_back(component_outputs.back()[component_outputs.back().size() - 2]);
      solver.addClause(clause);
    }
    return component_outputs;
  }

  void RelationSynthesiser::addNaiveIs1CardinalityConstraint(const std::vector<int>& vars) {
    solver.addClause(vars);
    for (int i = 0; i < vars.size(); i++) {
      for (int j = i + 1; j < vars.size(); j++) {
        solver.addClause({-vars[i], -vars[j]});
      }
    }
  }

  void RelationSynthesiser::addNaiveIs2CardinalityConstraint(const std::vector<int>& vars) {
    std::vector<int> cl;
    cl.reserve(vars.size() - 1);
    for (int i = 0; i < vars.size(); i++) {
      for (int j = 0; j < i; j++) {
        cl.push_back(vars[j]);
      }
      for (int j = i + 1; j < vars.size(); j++) {
        cl.push_back(vars[j]);
      }
      solver.addClause(cl);
      cl.clear();

      for (int j = i + 1; j < vars.size(); j++) {
        for (int k = j + 1; k < vars.size(); k++) {
          solver.addClause({-vars[i], -vars[j], -vars[k]});
        }
      }
    }
  }

  void RelationSynthesiser::defineConjunction(int var, std::vector<int>&& literals, int activator) {
    std::vector<int> big_clause, small_clause;
    if (activator != 0) {
      big_clause.reserve(literals.size() + 2);
      small_clause.reserve(3);
      big_clause.push_back(activator);
      small_clause.push_back(activator);
    } else {
      big_clause.reserve(literals.size() + 1);
      small_clause.reserve(2);
    }
    big_clause.push_back(var);
    small_clause.push_back(-var);
    for (int lit : literals) {
      big_clause.push_back(-lit);
      small_clause.push_back(lit);
      solver.addClause(small_clause);
      small_clause.pop_back();
    }
    solver.addClause(big_clause);
  }

  void RelationSynthesiser::defineDisjunction(int var, std::vector<int>&& literals, int activator) {
    std::vector<int> clause;
    literals.push_back(-var);
    if (activator != 0) {
      literals.push_back(activator);
      solver.addClause(literals);
      literals.pop_back();
      clause.reserve(3);
      clause.push_back(activator);
    } else {
      clause.reserve(2);
      solver.addClause(literals);
    }
    literals.pop_back();
    clause.push_back(var);
    for (int lit : literals) {
      clause.push_back(-lit);
      solver.addClause(clause);
      clause.pop_back();
    }
  }

  void RelationSynthesiser::addNonTrivialConstraint() {
    for (int i = 0; i < max_size; i++) {
      // We do not allow constant gates
      solver.addClause(gate_definition_variables[i]);
      // We exclude gates representing the projection to one of its inputs
      for (int j = 0; j < config.gate_size; j++) {
        int start = pow2(config.gate_size - j);
        int block_length = pow2(config.gate_size - j - 1);
        std::vector<int> clause;
        clause.reserve(pow2(config.gate_size) - 1);
        for (int k = 0; k < pow2(j); k++) {
          for (int l = k * start - (k == 0 ? 0 : 1); l < k * start + block_length -1; l++) {
            clause.push_back(gate_definition_variables[i][l]);
          }
          for (int l = k * start + block_length - 1; l < (k + 1) * start - 1; l++) {
            clause.push_back(-gate_definition_variables[i][l]);
          }
        }
        solver.addClause(clause);
      }
    }
  }

  // Every gate is either an output or an input of another gate
  void RelationSynthesiser::addUseAllStepsConstraint() {
    for (int i = 0; i < max_size; i++) {
      std::vector<int> clause (gate_output_variables[i].begin(), gate_output_variables[i].end());
      clause.reserve(max_size - i + 1);
      for (int j = i + 1; j < max_size; j++) {
        // clause.push_back(selection_variables[j][subcir.inputs.size() + i]);
        int isused = getNewVariable();
        // The gate is used by another (active) gate.
        solver.addClause({-isused, selection_variables[j][subcir.inputs.size() + i]});
        solver.addClause({-isused, gate_activation_variables[j]});
        clause.push_back(isused);
      }
      clause.push_back(-gate_activation_variables[i]);
      solver.addClause(clause);
    }
  }


  // Suppose gate i has inputs i1,...,in and gate j uses i as an input.
  // Then the other n-1 inputs of j shall not be contained in the inputs of i.
  // Otherwise j could be directly represented by a gate with inputs i1,...,in
  void RelationSynthesiser::addNoReapplicationConstraint() {
    std::vector<bool> filter(config.gate_size, 1);
    // A 1 at index i indicates that the ith node is used as an input.
    // By using prev_permutation we get all possible permutations of the filter
    filter.resize(subcir.inputs.size() + max_size - 1);
    std::vector<int> indices(config.gate_size,0);
    // int tt_size = RelationSynthesiser::pow2(subcir.inputs.size()) - 1;
    do {
      indices.clear();
      for (int i = 0; i < subcir.inputs.size() + max_size - 1; i++) {
        if (filter[i]) {
          indices.push_back(i);
        }
      }
      int first_gate = getPotentialSuccessors(indices);
      for (int i = first_gate; i < max_size; i++) {
        std::vector<int> clause;
        clause.reserve(subcir.inputs.size() + max_size);
        for (int idx : indices) {
          clause.push_back(-selection_variables[i][idx]);
        }
        int start_with = clause.size();
        for (int j = i + 1; j < max_size; j++) {
          // gate j has inputs.size() + j potential inputs
          clause.resize(subcir.inputs.size() + j + 1, 0);
          clause[start_with] = -selection_variables[j][subcir.inputs.size() + i];
          clause[start_with + 1] = -gate_activation_variables[j];
          int k = 0, l = 0, m = 0;
          // while (k < inputs.size() + j && l < indices.size()) {
          while (k < subcir.inputs.size() + j) {
            if (l >= indices.size() || k < indices[l]) {
              if (k != subcir.inputs.size() + i) {
                clause[start_with + m + 2] = selection_variables[j][k];
                m++;
              }
              k++;
            } else if (k > indices[l]) {
              l++;
            } else {
              k++;
              l++;
            }
          }
          solver.addClause(clause);
        }
      }
    } while (std::prev_permutation(filter.begin(), filter.end()));
  }

  // Order steps according to their inputs.
  // If step i has input j then step i+1 must have an input >=j
  void RelationSynthesiser::addOrderedStepsConstraint() {
    for (int i = 0; i < max_size - 1; i++) {
      for (int j = 0; j < subcir.inputs.size() + i; j++) {
        std::vector<int> clause {-gate_activation_variables[i+1], -selection_variables[i][j]};
        clause.reserve(subcir.inputs.size() + i - j + 3);
        for (int k = j; k < subcir.inputs.size() + i + 1; k++) {
          clause.push_back(selection_variables[i+1][k]);
        }
        solver.addClause(clause);
      }
    }
  }


}
ABC_NAMESPACE_IMPL_END
