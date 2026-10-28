/**CFile****************************************************************

  FileName    [eslim2Area.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Implementation of area based SAT encoding.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eslim2Area.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include "areaEngine.hpp"

ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {

  AreaEngine::AreaEngine(const Relation& relation, const Subcircuit& subcir, const eSLIM2Config& cfg, eSLIM2Log& log)
            : RelationSynthesiser(relation, subcir, subcir.nodes.size(), cfg, log) {
    for (int i = 0; i < subcir.inputs.size(); i++) {
      input_index_map[subcir.inputs[i]] = i;
    }
    for (int i = 0; i < subcir.outputs.size(); i++) {
      output_index_map[subcir.outputs[i]] = i;
    }
    if (subcir.forbidden_pairs.size() > 0) {
      setupCycleConstraints();
    }
  }

/**Function*************************************************************

  Synopsis    [Searches for a minimum-area implementation of the relation.]

***********************************************************************/
  eSLIM2CirMan AreaEngine::synthesiseMinimumSizeCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIM2Config& cfg, eSLIM2Log& log) {
    AreaEngine synth(relation, subcir, cfg, log);
    std::vector<bool> last_model;
    int replacement_size = 0;
    for (int i = synth.max_size; i>=0; i--) {
      double timeout = synth.getDynamicTimeout(i);
      int status = synth.checkSize(i, timeout);
      if (status == 10) {
        last_model = synth.solver.getModel();
        i = synth.getSizeFromActivationVars(last_model);
        replacement_size = i;
      } else {
        break;
      }
    }
    if (last_model.empty()) {
      // no replacement found
      return eSLIM2CirMan(0);
    } else {
      return synth.getReplacement(last_model, replacement_size);
    }
  }

  int AreaEngine::checkSize(unsigned int size) {
    return checkSize(size, 0);
  }

  int AreaEngine::checkSize(unsigned int size, double timeout) {
    std::vector<int> assumptions = getSizeAssumption(size);
    int status = timeout == 0 ? solver.solve(assumptions) : solver.solve(timeout, assumptions);
    logRun(status, size);
    return status;
  }

  void AreaEngine::setupCycleConstraints() {
    assert (!subcir.forbidden_pairs.empty());
    setupConnectionVariables();
    if (subcir.forbidden_pairs.size() > 1) {
      connectionVariablesForCombinedCycles();
    }
    addCycleConstraints();
  }

  void AreaEngine::addCycleConstraints() {
    for (auto const& [outp, inputs] : subcir.forbidden_pairs) {
      for (int inp : inputs) {
        int output_idx = output_index_map.at(outp);
        for (int i = 0; i < max_size; i++) {
          solver.addClause({-gate_activation_variables[i], -gate_output_variables[i][output_idx], -connection_variables.at(inp)[i + subcir.inputs.size()]});
        }
        for (int i = 0; i < subcir.inputs.size(); i++) {
          solver.addClause({-gate_output_variables[max_size + i][output_idx], -connection_variables.at(inp)[i]});
        }
      }
    }
  }

  void AreaEngine::setupConnectionVariables() {
    for (auto const& [out, inputs] : subcir.forbidden_pairs) {
      for (int in : inputs) {
        if (connection_variables.find(in) == connection_variables.end()) {
          connection_variables[in] = getNewVariableVector(max_size + subcir.inputs.size());
        }
      }
    }

    for (const auto& [input_var, connection_vars] : connection_variables) {
      int input_idx = input_index_map.at(input_var);
      // An input is connected to itself
      solver.addClause({connection_vars[input_idx]});
      for (int i = 0; i < max_size; i++) {
        int activation_variable = gate_activation_variables[i];
        for (int j = 0; j < subcir.inputs.size(); j++) {
          // if gate i uses input j and input j is connected to input_var then also gate i is connected to input_var
          solver.addClause({-activation_variable, -selection_variables[i][j], -connection_vars[j], connection_vars[subcir.inputs.size() + i]});
        }
        for (int j = 0; j < i; j++) {
          // if gate i uses gate j and gate j is connected to input_var then also gate i is connected to input_var
          solver.addClause({-activation_variable, -selection_variables[i][subcir.inputs.size() + j], -connection_vars[subcir.inputs.size() + j], connection_vars[subcir.inputs.size() + i]});
        }
      }
    }
  }


  void AreaEngine::connectionVariablesForCombinedCycles() {
    assert (subcir.forbidden_pairs.size() > 1);
    // Inputs are assigned to the outputs on which they depend
    std::unordered_map<int, std::unordered_set<int>> inputs_per_output;
    // Inputs in pairs
    std::unordered_set<int> inputs_in_pairs;
    for (auto const& [outp, inputs] : subcir.forbidden_pairs) {
      for (int inp : inputs) {
        if (inputs_per_output.find(outp) == inputs_per_output.end()) {
          inputs_per_output[outp] = {inp};
        } else {
          inputs_per_output[outp].insert(inp);
        }
        inputs_in_pairs.insert(inp);
      }
    }
    for (const auto& [ov, inp] : inputs_per_output) {
      for (int iv : inputs_in_pairs) {
        if (inp.find(iv) == inp.end()) {
          for (int k : inputs_per_output.at(ov)) {
            for (int i = 0; i < max_size; i++) {
              // Input k depends on output ov.
              // If gate i represents output ov and gate i is connected to iv then also gate k is connected to iv.
              solver.addClause({-gate_activation_variables[i], -gate_output_variables[i][output_index_map.at(ov)],
                              -connection_variables.at(iv)[subcir.inputs.size() + i], connection_variables.at(iv)[input_index_map.at(k)]});
            }
            for (int i = 0; i < subcir.inputs.size(); i++) {
              // Input k depends on output ov.
              // If input i represents output ov and input i is connected to iv then gate k shall be connected to iv too.
              solver.addClause({-gate_output_variables[max_size + i][output_index_map.at(ov)], -connection_variables.at(iv)[i], connection_variables.at(iv)[input_index_map.at(k)]});
            }
          }
        }
      }
    }
  }


}
ABC_NAMESPACE_IMPL_END
