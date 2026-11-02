/**CFile****************************************************************

  FileName    [eslim2Delay.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Implementation of delay based SAT encoding.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eslim2Delay.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <set>

#include "delayEngine.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {

  DelayEngine::DelayEngine( const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIM2Config& cfg, eSLIM2Log& log, int fixed_bound)
                          : RelationSynthesiser(relation, subcir, max_size, cfg, log) {
    assert (subcir.forbidden_pairs.empty());
    if (fixed_bound >= 0 && setupFixedDelay(fixed_bound, log)) {
      fixed_delay = fixed_bound;
      max_delay = fixed_bound;
      return;
    }
    symmetry_selector = getNewVariable();
    symmetry_selector_assignment = symmetry_selector;
    std::set<int> unique_ats_set (subcir.arrival_times.begin(), subcir.arrival_times.end());
    unique_arrival_times.assign(unique_ats_set.begin(), unique_ats_set.end());
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
  eSLIM2CirMan DelayEngine::synthesizeMinimumDelayCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIM2Config& cfg, eSLIM2Log& log) {
    DelayEngine synth(relation, subcir, max_size, cfg, log);
    std::vector<bool> last_model = synth.reduceDelay(max_size, delay);
    if (last_model.empty()) {
      // no replacement found
      return eSLIM2CirMan(0);
    } else {
      int replacement_size = synth.getSizeFromActivationVars(last_model);
      return synth.getReplacement(last_model, replacement_size);
    }
  }

  eSLIM2CirMan DelayEngine::synthesizeMinimumDelayAreaCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIM2Config& cfg, eSLIM2Log& log) {
    DelayEngine synth(relation, subcir, max_size, cfg, log);
    std::vector<bool> last_model = synth.reduceDelay(max_size, delay);
    if (last_model.empty()) {
      // We could not even find a replacement with the same delay as the original circuit (timeout)
      // Hence, it is unlikely that we find a circuit that has the same delay but fewer gates
      return eSLIM2CirMan(0);
    }
    int replacement_size = synth.getSizeFromActivationVars(last_model);
    // int replacement_delay = synth.getDelayFromDelayVariables(last_model);
    int replacement_delay = synth.computeDelay(last_model);
    std::vector<bool> model = synth.reduceArea(replacement_delay, replacement_size - 1);
    if (model.size() > 0) {
      replacement_size = synth.getSizeFromActivationVars(model);
      std::swap(last_model, model);
    }
    return synth.getReplacement(last_model, replacement_size);
  }

  eSLIM2CirMan DelayEngine::synthesizeMinimumAreaDelayCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIM2Config& cfg, eSLIM2Log& log) {
    DelayEngine synth(relation, subcir, subcir.nodes.size(), cfg, log);
    std::vector<bool> last_model = synth.reduceArea(synth.max_delay, subcir.nodes.size());
    if (last_model.empty()) {
      // We could not even find a replacement with the same area as the original circuit (timeout)
      // Hence, it is unlikely that we find a circuit that has the same area and a causes a smaller delay
      return eSLIM2CirMan(0);
    }
    int replacement_size = synth.getSizeFromActivationVars(last_model);
    // int replacement_delay = synth.getDelayFromDelayVariables(last_model);
    int replacement_delay = synth.computeDelay(last_model);
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

/**Function*************************************************************

  Synopsis    [Minimizes area subject to the specified delay bound.]

***********************************************************************/
  eSLIM2CirMan DelayEngine::synthesizeMinimumAreaDelayConstraintCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, const eSLIM2Config& cfg, eSLIM2Log& log, bool* complete) {
    ++log.synthesis_searches;
    DelayEngine synth(relation, subcir, subcir.nodes.size(), cfg, log, cfg.compact_timing ? int(delay) : -1);
    std::vector<bool> last_model = synth.reduceArea(delay, subcir.nodes.size(), complete);
    if (last_model.empty()) {
      return eSLIM2CirMan(0);
    } else {
      int replacement_size = synth.getSizeFromActivationVars(last_model);
      return synth.getReplacement(last_model, replacement_size);
    }
  }

  std::vector<bool> DelayEngine::reduceArea(unsigned int max_delay, unsigned int initial_area, bool* complete) {
    if (complete)
      *complete = false;
    std::vector<bool> last_model;
    for (int i = initial_area; i >= int(min_size); i--) {
      double timeout = getDynamicTimeout(i);
      int status = existsReplacement(i, max_delay, timeout);
      if (status == 10) {
        last_model = solver.getModel();
        i = getSizeFromActivationVars(last_model); // it is possible that more than one gate is reduced in an iteration
        assert(unsigned(i) >= min_size);
        if (complete && unsigned(i) == min_size)
          *complete = true;
      } else {
        if (complete)
          *complete = status == 20;
        break;
      }
    }
    return last_model;
  }

  std::vector<bool> DelayEngine::reduceDelay(unsigned int max_size, unsigned int initial_delay) {
    std::vector<bool> last_model;
    unsigned int current_delay = initial_delay;
    for( auto it = delay_selectors.lower_bound(initial_delay); it != delay_selectors.end(); ++it ) {
      int d = it->first;
      if (current_delay < d) {
        continue;
      }
      double timeout = getDynamicTimeout(max_size);
      int status = existsReplacement(max_size, d, timeout);
      if (status == 10) {
        last_model = solver.getModel();
        current_delay = getDelayFromDelayVariables(last_model);
      } else {
        break;
      }
    }
    return last_model;
  }

  std::vector<int> DelayEngine::getAssumptions(unsigned int delay) {
    std::vector<int> assumptions;
    if (fixed_delay >= 0) {
      assert(delay == unsigned(fixed_delay));
      return assumptions;
    }
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

  // getDelayFromDelayVariables only gives an upper bound for the delay of the encoded circuit.
  // We also compute the exact delay value.
  // Note: When considering circuit that have already been optimised to a certain degree it is unlikely
  // that this function gives smaller values than getDelayFromDelayVariables.
  unsigned int DelayEngine::computeDelay(const std::vector<bool>& model) {
    const unsigned int ninputs = subcir.inputs.size();
    const unsigned int ngates = getSizeFromActivationVars(model);
    std::vector<unsigned int> current_delays(ninputs + ngates, 0);
    for (std::size_t i = 0; i < subcir.inputs.size(); i++) {
      current_delays[i] = subcir.arrival_times[i];
    }
    for (std::size_t i = 0; i < ngates; i++) {
      for (std::size_t j = 0; j < selection_variables[i].size(); j++) {
        // Gate values follow the primary inputs in the combined index space.
        if (model[selection_variables[i][j]])
          current_delays[ninputs + i] = std::max(current_delays[ninputs + i], current_delays[j] + 1);
      }
    }
    unsigned int delay = 0;
    for (std::size_t i = 0; i < subcir.outputs.size(); i++) {
      for (std::size_t j = 0; j < ngates; j++) {
        if (model[gate_output_variables[j][i]]) {
          delay = std::max(delay, current_delays[ninputs + j] + subcir.remaining_times[i]);
        }
      }
      for (std::size_t j = 0; j < ninputs; j++)
        if (model[gate_output_variables[max_size + j][i]])
          delay = std::max(delay, current_delays[j] + subcir.remaining_times[i]);
      if (model[gate_output_variables.back()[i]])
        delay = std::max(delay, subcir.remaining_times[i]);
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

/**Function*************************************************************

  Synopsis    [Encodes one depth bound using unary gate arrival levels.]

  Description [Shifts levels by the earliest input arrival. Returns false
               when the generic path-length encoding should be used.]

  SideEffects [Adds timing constraints, unless every replacement fits.]

***********************************************************************/

  bool DelayEngine::setupFixedDelay(unsigned bound, eSLIM2Log& log) {
    const unsigned earliest = *std::min_element(subcir.arrival_times.begin(), subcir.arrival_times.end());
    const unsigned latest = *std::max_element(subcir.arrival_times.begin(), subcir.arrival_times.end());
    const unsigned remaining = *std::max_element(subcir.remaining_times.begin(), subcir.remaining_times.end());
    if (ABC_UINT64_T(latest) + max_size + remaining <= bound) {
      ++log.untimed_syntheses;
      return true;
    }
    const ABC_UINT64_T span = ABC_UINT64_T(latest) - earliest + max_size;
    // Keep the generic encoding for widely separated input arrival times.
    if (span > 128)
      return false;
    const unsigned depth = unsigned(span);
    std::vector<std::vector<int>> levels;
    for (unsigned i = 0; i < max_size; ++i) {
      levels.push_back(getNewVariableVector(depth));
      solver.addClause({-gate_activation_variables[i], levels[i][0]});
      for (unsigned d = 1; d < depth; ++d)
        solver.addClause({-levels[i][d], levels[i][d-1]});
      for (unsigned j = 0; j < subcir.inputs.size(); ++j) {
        const unsigned d = subcir.arrival_times[j] - earliest;
        solver.addClause({-gate_activation_variables[i], -selection_variables[i][j], levels[i][d]});
      }
      for (unsigned j = 0; j < i; ++j) {
        const int selected = selection_variables[i][subcir.inputs.size() + j];
        for (unsigned d = 0; d + 1 < depth; ++d)
          solver.addClause({-gate_activation_variables[i], -selected, -levels[j][d], levels[i][d+1]});
        solver.addClause({-gate_activation_variables[i], -selected, -levels[j].back()});
      }
    }
    for (unsigned o = 0; o < subcir.outputs.size(); ++o) {
      const long long required = static_cast<long long>(bound) - subcir.remaining_times[o];
      const long long shifted = required - earliest;
      for (unsigned i = 0; i < max_size; ++i) {
        if (shifted < 1)
          solver.addClause({-gate_output_variables[i][o]});
        else if (shifted < depth)
          solver.addClause({-gate_output_variables[i][o], -levels[i][unsigned(shifted)]});
      }
      for (unsigned j = 0; j < subcir.inputs.size(); ++j)
        if (static_cast<long long>(subcir.arrival_times[j]) > required)
          solver.addClause({-gate_output_variables[max_size + j][o]});
      if (required < 0)
        solver.addClause({-gate_output_variables.back()[o]});
    }
    return true;
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
