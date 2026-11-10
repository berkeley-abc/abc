/**CFile****************************************************************

  FileName    [eslim2Synth.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Base class for SAT-based synthesis]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eslim2Synth.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <cassert>

#include "relationSynthesiser.h"


ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {


  RelationSynthesiser::RelationSynthesiser(const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIM2Config& cfg, eSLIM2Log& log, bool refine)
                                          : subcir(subcir), max_size(max_size),
                                            relation(relation), config(cfg), log(log),
                                            refine(refine && cfg.aig && cfg.gate_size == 2 &&
                                                   subcir.outputs.size() <= 6 && relation.getNLinesWithPattern() >= minimum_refinement_rows),
                                            encoded_rows(relation.getNPatterns(), false) {
    ++log.synthesis_sat_searches;
    solver.setDeadline(cfg.deadline);
    // Select only documented CaDiCaL configurations before adding clauses.
    // These affect search effort, not the relation or timing constraints.
    bool configured = true;
    switch (cfg.synthesis_solver_mode) {
      case 0: break;
      case 1: configured = solver.setOption("lucky", 0); break;
      case 2: configured = solver.configure("plain"); break;
      case 3: configured = solver.configure("sat"); break;
      case 4: configured = solver.configure("unsat"); break;
      case 5: configured = solver.setOption("phase", 0); break;
      default: configured = false; break;
    }
    assert(configured);
    (void)configured;
    analyseMandatorySupport();
    setupEncoding();
  }

/**Function*************************************************************

  Synopsis    [Derive necessary input supports and area lower bounds from the relation.]

  SideEffects [Initializes per-search support data.]

  SeeAlso     []

***********************************************************************/
  void RelationSynthesiser::analyseMandatorySupport() {
    const auto& cfg = config;
    if (subcir.outputs.size() <= 6 && cfg.gate_size > 1) {
      auto& forbidden = forbidden_tuples;
      for (int row = 0; row < relation.getNPatterns(); ++row)
        forbidden.push_back(relation.getForbiddenTuples(row, subcir.outputs.size()));
      const unsigned noutputs = subcir.outputs.size();
      const ABC_UINT64_T all = noutputs == 6 ? ~ABC_UINT64_T(0) : (ABC_UINT64_T(1) << (1u << noutputs)) - 1;
      // Project the allowed tuples only to derive necessary conditions. The
      // synthesis encoding still enforces the entire correlated relation.
      std::vector<unsigned> forced_zero(forbidden.size(), 0), forced_one(forbidden.size(), 0);
      output_mandatory_inputs.resize(noutputs);
      for (unsigned row = 0; row < forbidden.size(); ++row) {
        const ABC_UINT64_T allowed = all & ~forbidden[row];
        for (unsigned output = 0; output < noutputs; ++output) {
          if (!(allowed & truth_patterns[output]))
            forced_zero[row] |= 1u << output;
          if (!(allowed & ~truth_patterns[output]))
            forced_one[row] |= 1u << output;
        }
      }
      for (unsigned j = 0; j < subcir.inputs.size(); ++j) {
        bool mandatory = false;
        unsigned dependent_outputs = 0;
        for (unsigned row = 0; row < forbidden.size(); ++row)
          if (!(row & (1u << j))) {
            const unsigned other = row | (1u << j);
            // Disjoint allowed output tuples force input j into the support
            // of every implementation of this relation.
            mandatory |= (forbidden[row] | forbidden[other]) == all;
            dependent_outputs |= (forced_zero[row] & forced_one[other]) |
                                 (forced_one[row] & forced_zero[other]);
          }
        if (mandatory)
          mandatory_inputs.push_back(j);
        for (unsigned output = 0; output < noutputs; ++output)
          if ((dependent_outputs >> output) & 1)
            output_mandatory_inputs[output].push_back(j);
      }
      // A circuit with M K-input gates and O outputs can depend on at most
      // M*(K-1)+O distinct inputs, counting direct PI-to-PO connections too.
      if (mandatory_inputs.size() > noutputs)
        min_size = (mandatory_inputs.size() - noutputs + cfg.gate_size - 2) / (cfg.gate_size - 1);
      // Independently, an output whose support MUST contain I inputs needs
      // at least ceil((I-1)/(K-1)) gates in its cone. Taking the maximum avoids
      // double-counting gates shared by multiple outputs.
      for (const auto& inputs : output_mandatory_inputs) {
        const unsigned support = inputs.size();
        if (support > 1)
          min_size = std::max(min_size, (support + cfg.gate_size - 3) / (cfg.gate_size - 1));
      }
    }
  }

  double RelationSynthesiser::getDynamicTimeout(int size) {
    // The existing-size search also provides equal-area restructuring. Give
    // it more time than attempts to reduce the gate count. Periodic longer
    // attempts retain a chance to solve harder cuts within the run deadline.
    if (config.synthesis_timeout_ms) {
      const double budget = (size == int(max_size) ? 0.004 : 0.001) * config.synthesis_timeout_ms;
      return (log.synthesis_sat_searches % long_budget_interval == 0 ? long_budget_multiplier : 1) * budget;
    }
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

  eSLIM2CirMan RelationSynthesiser::getReplacement(const std::vector<bool>& model, int size) {
    assert (model.size() > 0);
    eSLIM2CirMan circ(subcir.inputs.size() + subcir.outputs.size() + size);
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

/**Function*************************************************************

  Synopsis    [Builds the exact-synthesis constraints for the selected gate model.]

***********************************************************************/
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
      gate_variables.push_back(refine ? std::vector<int>() :
                               getNewVariableVector(relation.getNLinesWithPattern() - normality_offset));

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
    constrainMandatorySupport();
  }

  // These are consequences of the FULL relation, even while only a few rows
  // have been added to the SAT instance. Make mandatory support explicit so
  // the solver need not rediscover it from truth-table clauses on every cut.
/**Function*************************************************************

  Synopsis    [Require every mandatory input to occur in the synthesized circuit.]

  SideEffects [Adds necessary support clauses to the solver.]

  SeeAlso     []

***********************************************************************/
  void RelationSynthesiser::constrainMandatorySupport() {
    if (min_size && min_size <= max_size)
      solver.addClause({gate_activation_variables[min_size - 1]});
    for (unsigned input : mandatory_inputs) {
      std::vector<int> clause = gate_output_variables[max_size + input];
      for (unsigned gate = 0; gate < max_size; ++gate) {
        const int used = getNewVariable();
        solver.addClause({-used, gate_activation_variables[gate]});
        solver.addClause({-used, selection_variables[gate][input]});
        clause.push_back(used);
      }
      solver.addClause(clause);
    }
  }

  void RelationSynthesiser::setupSymmetryBreaking() {
    addNonTrivialConstraint();
    addUseAllStepsConstraint();
    if (config.aig && config.aig_encoding >= 2)
      addOrderedStepsConstraint();
    // addNoReapplicationConstraint();
  }

/**Function*************************************************************

  Synopsis    [Exclude gate patterns that cannot occur in a minimum-area AIG.]

  SideEffects [Adds area-only pruning clauses.]

  SeeAlso     []

***********************************************************************/
  void RelationSynthesiser::constrainIrredundantAigArea() {
    assert(config.aig && config.gate_size == 2);
    auto forbidFold = [&](unsigned next, unsigned gate, unsigned input) {
      solver.addClause({-gate_activation_variables[next],
                        -selection_variables[next][subcir.inputs.size() + gate],
                        -selection_variables[gate][input],
                        -selection_variables[next][input]});
    };
    for (unsigned output = 0; output < output_mandatory_inputs.size(); ++output) {
      const auto& required = output_mandatory_inputs[output];
      if (required.empty())
        continue;
      // An output with mandatory support cannot be a constant. A direct PI
      // connection is possible only when that PI is its entire required set.
      solver.addClause({-gate_output_variables.back()[output]});
      for (unsigned input = 0; input < subcir.inputs.size(); ++input)
        if (required.size() != 1 || required.front() != input)
          solver.addClause({-gate_output_variables[max_size + input][output]});
      // A gate at index g can reach at most g+2 distinct PIs. Rule out output
      // sources that are too early to contain the output's mandatory support.
      for (unsigned gate = 0; gate < max_size && gate + 2 < required.size(); ++gate)
        solver.addClause({-gate_output_variables[gate][output]});
    }
    for (unsigned gate = 0; gate < max_size; ++gate) {
      const int active = gate_activation_variables[gate];
      // Inactive suffix gates have no observable use. Give them a canonical
      // function and fanins instead of searching their irrelevant choices.
      solver.addClause({active, selection_variables[gate][0]});
      solver.addClause({active, selection_variables[gate][1]});
      solver.addClause({active, -gate_definition_variables[gate][0]});
      solver.addClause({active, -gate_definition_variables[gate][1]});
      solver.addClause({active, gate_definition_variables[gate][2]});
      // Combining f(a,b) with a or b using another normal AND-family gate
      // collapses to a constant, projection, or one AND-family gate on a,b.
      // Folding this pair preserves every output and cannot add dependencies.
      // Thus every minimum-area solution has an equivalent form without it,
      // even if the predecessor also drives other gates or cut outputs.
      // The folded gate uses the predecessor's inputs directly, so this
      // transformation also cannot increase any output arrival time.
      for (unsigned next = gate + 1; next < max_size; ++next)
        for (unsigned input = 0; input < subcir.inputs.size() + gate; ++input)
          forbidFold(next, gate, input);
    }
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
    if (config.aig && config.gate_size == 2 && config.aig_encoding != 0) {
      constrainAigSelectionVariables();
      return;
    }
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

  // The two fanins are ordered by source index. The selected-source variables
  // remain available to the timing encoding and the active-gate constraints.
  void RelationSynthesiser::constrainAigSelectionVariables() {
    for (unsigned i = 0; i < max_size; ++i) {
      const unsigned n = selection_variables[i].size();
      const auto& pins = is_ith_fanin_variable[i];
      std::vector<int> first(pins[0].begin(), pins[0].end() - 1);
      std::vector<int> second(pins[1].begin() + 1, pins[1].end());
      addNaiveIs1CardinalityConstraint(first);
      addNaiveIs1CardinalityConstraint(second);
      for (unsigned a = 1; a + 1 < n; ++a)
        for (unsigned b = 1; b <= a; ++b)
          solver.addClause({-pins[0][a], -pins[1][b]});
      for (unsigned j = 0; j < n; ++j) {
        const int selected = selection_variables[i][j];
        std::vector<int> clause {-selected};
        for (unsigned pin = 0; pin < 2; ++pin)
          if (pins[pin][j]) {
            solver.addClause({-pins[pin][j], selected});
            clause.push_back(pins[pin][j]);
          }
        solver.addClause(clause);
      }
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
    if (config.mux_consensus && config.gate_size == 2) {
      // The first fanin is the low address bit; table[0] is fixed to zero.
      // Equal entries in a cofactor imply the output without the other fanin.
      const int active = gate_activation_variables[gtidx];
      const int a = fanin_variables[0], b = fanin_variables[1];
      const int t1 = gate_definition_variables[gtidx][0];
      const int t2 = gate_definition_variables[gtidx][1];
      const int t3 = gate_definition_variables[gtidx][2];
      solver.addClause({-active, a, t2, -gt_val});
      solver.addClause({-active, -a, t1, t3, -gt_val});
      solver.addClause({-active, -a, -t1, -t3, gt_val});
      solver.addClause({-active, b, t1, -gt_val});
      solver.addClause({-active, -b, t2, t3, -gt_val});
      solver.addClause({-active, -b, -t2, -t3, gt_val});
      // Uniform-table clauses add nothing: table[0]=0 rules out all ones,
      // and addNonTrivialConstraint already rules out all zeros.
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

  void RelationSynthesiser::setupEquivalenceConstraints() {
    // Normal circuits always implement the all-zero row. Seed a larger
    // relation with a few dispersed rows; subsequent SAT models are checked
    // against ALL rows, and counterexamples are added to this same solver.
    std::vector<unsigned> rows;
    for (unsigned row = 1; row < unsigned(relation.getNPatterns()); ++row)
      if (relation.getPatternSize(row))
        rows.push_back(row);
    log.synthesis_total_rows += rows.size();
    if (refine) {
      assert(!(forbidden_tuples[0] & 1));
      for (unsigned i = 0; i < refinement_seed_rows; ++i)
        addRelationRow(rows[i * (rows.size() - 1) / (refinement_seed_rows - 1)]);
    } else {
      for (unsigned row : rows)
        addRelationRow(row);
    }
  }

/**Function*************************************************************

  Synopsis    [Encode one previously unencoded row of the complete relation.]

  SideEffects [Adds clauses and records the encoded row.]

  SeeAlso     []

***********************************************************************/
  void RelationSynthesiser::addRelationRow(unsigned row) {
    assert(row && !encoded_rows[row] && relation.getPatternSize(row));
    encoded_rows[row] = true;
    const unsigned pidx = encoded_count++;
    ++log.synthesis_encoded_rows;
    for (unsigned gate = 0; gate < max_size; ++gate) {
      if (refine)
        gate_variables[gate].push_back(getNewVariable());
      auto fanins = setupFaninVariables(gate, row, pidx);
      addGateValueConstraint(gate, gate_variables[gate][pidx], fanins);
    }
    std::vector<int> output_vars(subcir.outputs.size(), 0);
    for (const auto& pattern : relation.getPattern(row)) {
      assert(2 * subcir.outputs.size() == pattern.size());
      std::vector<int> clause;
      for (unsigned j = 0; j < subcir.outputs.size(); ++j)
        if (pattern[2*j]) {
          if (!output_vars[j])
            output_vars[j] = setupOutputVariable(j, row, pidx);
          clause.push_back(pattern[2*j + 1] ? output_vars[j] : -output_vars[j]);
        }
      solver.addClause(clause);
    }
  }

  // Exact bit-parallel validation of a normal two-input replacement against
  // the complete relation, including its don't-cares and correlated outputs.
/**Function*************************************************************

  Synopsis    [Sample violations of the complete relation in a candidate model.]

  SideEffects [Returns row indices without modifying the solver.]

  SeeAlso     []

***********************************************************************/
  std::vector<unsigned> RelationSynthesiser::findCounterexamples(const std::vector<bool>& model) const {
    typedef ABC_UINT64_T Word;
    const unsigned ninputs = subcir.inputs.size(), noutputs = subcir.outputs.size();
    unsigned size = 0;
    while (size < max_size && model[gate_activation_variables[size]])
      ++size;
    std::vector<std::vector<unsigned>> fanins(size);
    std::vector<unsigned> functions(size, 0), outputs(noutputs, ninputs + size);
    for (unsigned gate = 0; gate < size; ++gate) {
      for (unsigned j = 0; j < selection_variables[gate].size(); ++j)
        if (model[selection_variables[gate][j]])
          fanins[gate].push_back(j);
      assert(fanins[gate].size() == 2);
      for (unsigned j = 0; j < 3; ++j)
        functions[gate] |= unsigned(model[gate_definition_variables[gate][j]]) << (j + 1);
    }
    for (unsigned output = 0; output < noutputs; ++output) {
      for (unsigned gate = 0; gate < size; ++gate)
        if (model[gate_output_variables[gate][output]])
          outputs[output] = ninputs + gate;
      for (unsigned input = 0; input < ninputs; ++input)
        if (model[gate_output_variables[max_size + input][output]])
          outputs[output] = input;
    }
    std::vector<unsigned> counterexamples;
    std::vector<Word> values(ninputs + size + 1, 0);
    for (unsigned base = 0; base < forbidden_tuples.size(); base += 64) {
      for (unsigned j = 0; j < ninputs; ++j)
        values[j] = j < 6 ? truth_patterns[j] : ((base >> j) & 1 ? ~Word(0) : Word(0));
      for (unsigned gate = 0; gate < size; ++gate) {
        const Word a = values[fanins[gate][0]], b = values[fanins[gate][1]];
        const unsigned tt = functions[gate];
        values[ninputs + gate] = (a & ~b & -Word((tt >> 1) & 1)) |
                                 (~a & b & -Word((tt >> 2) & 1)) |
                                 (a & b & -Word((tt >> 3) & 1));
      }
      for (unsigned bit = 0; bit < 64 && base + bit < forbidden_tuples.size(); ++bit) {
        const unsigned row = base + bit;
        if (encoded_rows[row] || !forbidden_tuples[row])
          continue;
        unsigned tuple = 0;
        for (unsigned output = 0; output < noutputs; ++output)
          tuple |= unsigned((values[outputs[output]] >> bit) & 1) << output;
        if ((forbidden_tuples[row] >> tuple) & 1) {
          counterexamples.push_back(row);
        }
      }
    }
    // Sample the full violating set rather than repeatedly selecting nearby
    // low-numbered rows. Every selected row is an actual counterexample; an
    // empty result still means that the entire relation has been validated.
    if (counterexamples.size() > refinement_batch_rows) {
      const size_t last = counterexamples.size() - 1;
      for (unsigned i = 0; i < refinement_batch_rows; ++i)
        counterexamples[i] = counterexamples[i * last / (refinement_batch_rows - 1)];
      counterexamples.resize(refinement_batch_rows);
    }
    return counterexamples;
  }

/**Function*************************************************************

  Synopsis    [Solve and refine the sampled relation within the remaining deadline.]

  SideEffects [Adds counterexample rows and updates search statistics.]

  SeeAlso     []

***********************************************************************/
  int RelationSynthesiser::solveRelation(const std::vector<int>& assumptions, double timeout, unsigned size) {
    const auto start = std::chrono::steady_clock::now();
    while (!config.expired()) {
      // Refinement must share a single per-size allowance, not restart it.
      const double remaining = timeout ? timeout - std::chrono::duration<double>(
          std::chrono::steady_clock::now() - start).count() : std::numeric_limits<double>::infinity();
      if (remaining <= 0)
        return 0;
      const int status = solver.solve(remaining, assumptions);
      logRun(status, size);
      if (status != 10 || !refine)
        return status;
      auto counterexamples = findCounterexamples(solver.getModel());
      if (counterexamples.empty())
        return 10;
      ++log.synthesis_refinements;
      for (unsigned row : counterexamples)
        addRelationRow(row);
    }
    return 0;
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
  // A suitable numbering exists for every DAG: repeatedly choose a ready
  // gate with the smallest largest-fanin index. Newly ready gates use the
  // gate just numbered, so they cannot precede an already ready gate.
  // Relabeling internal gates preserves both output functions and timing.
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
