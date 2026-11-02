/**CFile****************************************************************

  FileName    [relationGeneration.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [SAT-based computation of Boolean relations.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <cassert>
#include <algorithm>

#include "misc/util/abc_global.h"

#include "relationGeneration.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM {


  Relation::Relation(int nfanins) : output_patterns(1 << nfanins) {

  }

  void Relation::addOutputPattern(int inputidx, std::vector<bool>&& pattern) {
    lines_with_pattern += output_patterns[inputidx].empty();
    output_patterns[inputidx].push_back(std::move(pattern));
  }

  RelationGenerator::RelationGenerator( const eSLIMCirMan& cir, const Subcircuit& subcir, 
                                        const eSLIMConfig& cfg, eSLIMLog& log) 
                    : cir(cir), subcir(subcir), cfg(cfg), log(log), 
                      gate2varref(cir.getNofObjs() - cir.getNofPos()), 
                      gate2varcone(cir.getNofObjs() - cir.getNofPos()) {
    setupEncoding();
  }

  Relation RelationGenerator::computeRelation(const eSLIMCirMan& cir, const Subcircuit& subcir, 
                                              const eSLIMConfig& cfg, eSLIMLog& log) {
    RelationGenerator rgen(cir, subcir, cfg, log);
    return rgen.getRelation();
  }

  int RelationGenerator::getNewVar() {
    return max_var++;
  }

  void RelationGenerator::setupEncoding() {
    if (cfg.approximate_relation) {
      if (cfg.generate_relation_with_tfi_limit) {
        encodeCircuitApproximativeBoundedTFI();
      } else {
        encodeCircuitApproximative();
      }
    } else {
      // encodeCircuitFull();
      encodeCircuitAffected();
    }
  }

  void RelationGenerator::encodeGate(const eSLIMCirObj& obj, int var, const std::vector<int>& gate2var) {
    int bc = popcount(obj.tt);
    int tt_length = obj.getTTLength();
    if (bc == 0) {
      solver.addClause({-var});
    } else if (bc == tt_length) {
      solver.addClause({var});
    } else if (bc == 1) {
      return getGateEncodingUnique(obj, var, gate2var, true);
    } else if (bc == tt_length - 1) {
      return getGateEncodingUnique(obj, var, gate2var, false);
    } else {
      return getGateEncodingNaive(obj, var, gate2var);
    }
  }

  void RelationGenerator::getGateEncodingUnique(const eSLIMCirObj& obj, int var, const std::vector<int>& gate2var, bool unique_bit) {
    ABC_UINT64_T tt = obj.tt;
    if (!unique_bit) {
      tt = eSLIMCirMan::negateTT(tt, obj.getNFanins());
    }
    int bit_index = lsb(tt); 
    std::vector<int> clause;
    int lit = unique_bit ? -var : var;
    for (int i = 0; i < obj.getNFanins(); i++) {
      if ((bit_index >> i) & 1 ) {
        clause.push_back(-gate2var[obj.fanins[i]->node_id]);
        solver.addClause({gate2var[obj.fanins[i]->node_id], lit});
      } else {
        clause.push_back(gate2var[obj.fanins[i]->node_id]);
        solver.addClause({-gate2var[obj.fanins[i]->node_id], lit});
      }
    }
    clause.push_back(-lit);
    solver.addClause(clause);
  }
  
  void RelationGenerator::getGateEncodingNaive(const eSLIMCirObj& obj, int var, const std::vector<int>& gate2var) {
    int tt_length = obj.getTTLength();
    int nfans = obj.getNFanins();
    std::vector<int> clause;
    clause.reserve(nfans+1);
    for (int i = 0; i < tt_length; i++) {
      clause.clear();
      for (int j = 0; j < nfans; j++) {
        if ((i >> j) & 1 ) {
          clause.push_back(-gate2var[obj.fanins[j]->node_id]);
        } else {
          clause.push_back(gate2var[obj.fanins[j]->node_id]);
        }
      }
      bool polarity = (obj.tt >> i) & 1;
      if (polarity) {
        clause.push_back(var);
      } else {
        clause.push_back(-var);
      }
      solver.addClause(clause);
    }
  }


  void RelationGenerator::encodeCircuitAffected() {
    setupConstantGate();
    std::vector<int> compare_nodes;
    for (int i = cir.getNofObjs() - cir.getNofPos(); i < cir.getNofObjs(); i++) {
      const auto& obj = cir.getObj(i);
      int fid = obj.fanins[0]->node_id;
      // multiple POs can use the same fanin
      // if gate2varref[fid] is not 0 we have already seen it
      if (cir.inTFO(obj) && !gate2varref[fid]) {
        gate2varref[fid] = getNewVar();
        gate2varcone[fid] = getNewVar();
        compare_nodes.push_back(fid);
      }
    }
    setupEqualityConstraints(compare_nodes);

    for (int i = cir.getNofObjs() - cir.getNofPos() - 1; i > cir.getNofPis(); i--) {
      if (gate2varref[i]) { // the gate is connected to a PO that is in the TFO of the subcircuit
        const auto& obj = cir.getObj(i);
        for (const auto& f : obj.fanins) {
          int fid = f->node_id;
          if (gate2varref[fid] == 0) {
            gate2varref[fid] = getNewVar();
          }
        }
        encodeGate(obj, gate2varref[i], gate2varref);
        
        if (cir.inTFO(obj) && !cir.inSubcircuit(obj)) {
          // For an input in a forbidden pair no successors needs to be processed before
          gate2varcone[i] = gate2varcone[i] ? gate2varcone[i] : getNewVar();
          for (const auto& f : obj.fanins) {
            int fid = f->node_id;
            if (cir.inSubcircuit(*f) || cir.inTFO(*f)) {
              if (gate2varcone[fid] == 0) {
                gate2varcone[fid] = getNewVar();
              }
            } else {
              gate2varcone[fid] = gate2varref[fid];
            }
          }
          encodeGate(obj, gate2varcone[i], gate2varcone);
        } else if (gate2varcone[i] == 0) {
          gate2varcone[i] = gate2varref[i];
        }
      }
    }
    
    for (int i = 1; i <= cir.getNofPis(); i++) {
      if (gate2varref[i] != 0) {
        cone_input_variables.push_back(gate2varref[i]);
        // Simplifies handling of variables
        if (gate2varcone[i] == 0) {
          gate2varcone[i] = gate2varref[i];
        }
      }
    }
  }
  

  void RelationGenerator::encodeCircuitApproximative() {
    setupConstantGate();
    std::vector<int> compare_nodes = markRestrictedCone();
    int max_node = *std::max_element(compare_nodes.begin(), compare_nodes.end());
    for (int i = max_node; i > cir.getNofPis(); i--) {
      const auto& obj = cir.getObj(i);
      if (gate2varref[i] != 0) {
        for (auto& f : obj.fanins ) {
          if (gate2varref[f->node_id] == 0) {
            gate2varref[f->node_id] = getNewVar();
            gate2varcone[f->node_id] = gate2varref[f->node_id];
          }
        }
        encodeGate(obj, gate2varref[i], gate2varref);
        if (!cir.inSubcircuit(obj) && gate2varcone[i] != gate2varref[i]) {
          encodeGate(obj, gate2varcone[i], gate2varcone);
        }
      }
    }
    for (int i = 1; i <= cir.getNofPis(); i++) {
      if (gate2varref[i] != 0) {
        cone_input_variables.push_back(gate2varref[i]);
      }
    }
    setupEqualityConstraints(compare_nodes);
  }

  void RelationGenerator::encodeCircuitApproximativeBoundedTFI() {
    setupConstantGate();
    std::vector<int> compare_nodes = markRestrictedCone();
    std::vector<unsigned char> counts(cir.getNofObjs() - cir.getNofPos());
    int max_node = *std::max_element(compare_nodes.begin(), compare_nodes.end());
    for (int i = max_node; i > cir.getNofPis(); i--) {
      const auto& obj = cir.getObj(i);
      if (gate2varref[i] != 0) {
        if (cir.inTFO(obj) || cir.inSubcircuit(obj)) {
          counts[i] = cfg.relation_tfi_bound + 1;
        } else if (counts[i] == 0) { 
          cone_input_variables.push_back(gate2varref[i]);
          continue;
        }
        for (auto& f : obj.fanins ) {
          if (gate2varref[f->node_id] == 0) {
            gate2varref[f->node_id] = getNewVar();
            gate2varcone[f->node_id] = gate2varref[f->node_id];
            counts[f->node_id] = std::max(counts[f->node_id], static_cast<unsigned char>(counts[i] - 1));
          }
        }
        encodeGate(obj, gate2varref[i], gate2varref);
        if (!cir.inSubcircuit(obj) && gate2varcone[i] != gate2varref[i]) {
          encodeGate(obj, gate2varcone[i], gate2varcone);
        }
      }
    }
    for (int i = 1; i <= cir.getNofPis(); i++) {
      if (gate2varref[i] != 0) {
        cone_input_variables.push_back(gate2varref[i]);
      }
    }
    setupEqualityConstraints(compare_nodes);
  }

  std::vector<int> RelationGenerator::markRestrictedCone() {
    std::vector<unsigned char> counts(cir.getNofObjs() - cir.getNofPos());
    for (int i : subcir.outputs) {
      gate2varref[i] = getNewVar();
      gate2varcone[i] = getNewVar();
      counts[i] = cfg.relation_tfo_bound;
    }
    if (cfg.relation_tfo_bound == 0) {
      std::vector<int> nodes(subcir.outputs.begin(), subcir.outputs.end());
      return nodes;
    }
    std::vector<int> nodes;
    for (int i = subcir.outputs[0] + 1; i < cir.getNofObjs() - cir.getNofPos(); i++) { //outputs are ordered
      const auto& obj = cir.getObj(i);
      if (!cir.inTFO(obj) || cir.inSubcircuit(obj)) {
        continue;
      }
      unsigned char x = 0;
      for (auto& f : obj.fanins) {
        x = std::max(x, counts[f->node_id]);
      }
      if (x > 0) {
        gate2varcone[i] = getNewVar();
        gate2varref[i] = getNewVar();
        counts[i] = x - 1;
        if (x == 1) {
          nodes.push_back(i);
        }
      }
    }
    std::set<int> used;
    for (int i = cir.getNofObjs() - cir.getNofPos(); i < cir.getNofObjs(); i++) {
      const auto& obj = cir.getObj(i);
      if (cir.inTFO(obj) && counts[obj.fanins[0]->node_id] > 0 && used.find(obj.fanins[0]->node_id) == used.end()) {
        nodes.push_back(obj.fanins[0]->node_id);
        used.insert(obj.fanins[0]->node_id);
      }
    }
    return nodes;
  }

  void RelationGenerator::setupConstantGate() {
    int const_var = getNewVar();
    gate2varref[0] = const_var;
    gate2varcone[0] = const_var;
    solver.addClause({-const_var});
  }

  void RelationGenerator::setupEqualityConstraints(const std::vector<int>& nodes) {
    mode_selection_variable = getNewVar();
    std::vector<int> one_different {-mode_selection_variable};
    for (int cnd : nodes) {
      int eq_var = getNewVar();
      equality_variables.push_back(eq_var);
      getEqualityClauses(gate2varref[cnd], gate2varcone[cnd], eq_var);
      one_different.push_back(-eq_var);
    }
    solver.addClause(one_different);
  }


  void RelationGenerator::getEqualityClauses(int x, int y, int aux) {
    solver.addClause({x, -y, -aux});
    solver.addClause({-x, y, -aux});
    solver.addClause({x, y, aux});
    solver.addClause({-x, -y, aux});
  }

  int RelationGenerator::findConflict(double& timeout, int mode_selection) {
    abctime time_start = Abc_Clock();
    int solver_status = solver.solve(timeout, {mode_selection});
    double solver_time = (double)1.0*(Abc_Clock() - time_start)/CLOCKS_PER_SEC;
    log.cummulative_sat_runtime_relation_generation += solver_time;
    log.max_sat_runtime_relation_generation = std::max(log.max_sat_runtime_relation_generation, solver_time);
    // log.cummulative_sat_runtime_relation_generation += solver.getRunTime();
    log.nof_sat_calls_relation_generation++;
    return solver_status;
  }
  
  int RelationGenerator::reduceConflict(double& timeout, const std::vector<int>& cone_input, 
                                        const std::vector<int>& subcircuit_output, const std::vector<int>& equality) {
    solver.assume(cone_input);
    solver.assume(subcircuit_output);
    solver.assume(equality);
    abctime time_start = Abc_Clock();
    int status = solver.solve(timeout);
    double solver_time = (double)1.0*(Abc_Clock() - time_start)/CLOCKS_PER_SEC;
    log.cummulative_sat_runtime_relation_generation += solver_time;
    log.max_sat_runtime_relation_generation = std::max(log.max_sat_runtime_relation_generation, solver_time);
    // log.cummulative_sat_runtime_relation_generation += solver.getRunTime();
    log.nof_sat_calls_relation_generation++;
    return status;
  }

  Relation RelationGenerator::getRelation() {    
    std::vector<int> subcircuit_input_variables;
    subcircuit_input_variables.reserve(subcir.inputs.size());
    for (int sin : subcir.inputs) {
      int var = gate2varcone[sin];
      subcircuit_input_variables.push_back(var);
    }
    std::vector<int> subcircuit_output_variables;
    subcircuit_output_variables.reserve(subcir.outputs.size());
    // outputs in forbidden pairs must not removed
    std::vector<bool> outputs_to_keep(subcir.outputs.size(), false);
    for (int i = 0; i < subcir.outputs.size(); i++) {
      int sout = subcir.outputs[i];
      int var = gate2varcone[sout];
      subcircuit_output_variables.push_back(var);
      if (subcir.forbidden_pairs.find(sout) != subcir.forbidden_pairs.end()) {
        outputs_to_keep[i] = true;
      }
    }

    Relation rel(subcir.inputs.size());

    int solver_status;
    double timeout = cfg.relation_generation_timeout;
    abctime time_start = Abc_Clock();
    while( (solver_status=findConflict(timeout, mode_selection_variable)) == 10) {
      timeout -= (double)1.0*(Abc_Clock() - time_start)/CLOCKS_PER_SEC;
      time_start = Abc_Clock();
      if (timeout <= 0) {
        rel.status = false;
        return rel;
      }
      std::vector<int> cone_in_assm = solver.getValues(cone_input_variables);
      std::vector<int> sin_assm = solver.getValues(subcircuit_input_variables);
      std::vector<int> sout_assm = solver.getValues(subcircuit_output_variables);
      int status = reduceConflict(timeout, cone_in_assm, sout_assm, equality_variables);
      if (status != 20) {
        assert (status != 10);
        rel.status = false;
        return rel;
      }
      assert (status == 20);
      std::vector<int> blocking_clause {-mode_selection_variable};
      for (int i = 0; i < subcir.inputs.size(); i++) {
        blocking_clause.push_back(-sin_assm[i]);
      }
      std::vector<bool> pattern (2*subcir.outputs.size(), false);
      for (int i = 0; i < subcir.outputs.size(); i++) {
        if (solver.isFailed(sout_assm[i]) || outputs_to_keep[i]) {
          pattern[2*i] = true;
          pattern[2*i + 1] = sout_assm[i] < 0; // at least one output must be assigned differently in order to preserve the function
          blocking_clause.push_back(-sout_assm[i]);
        } 
      }
      solver.addClause(blocking_clause);
      rel.addOutputPattern(assignment2bvindex(sin_assm), std::move(pattern));
    }
    if (solver_status != 20) {
      rel.status = false;
    }
    return rel;
  }

  int RelationGenerator::assignment2bvindex(const std::vector<int>& assm) {
    int idx = 0;
    for (int i = 0; i < assm.size(); i++) {
      if (assm[i] > 0) {
        idx |= 1 << i;
      }
    }
    return idx;
  }

}
ABC_NAMESPACE_IMPL_END