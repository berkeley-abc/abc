/**CFile****************************************************************

  FileName    [relationSynthesiser.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Base class for SAT-based synthesis]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: relationSynthesiser.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__RELATIONSYNTHESISER_hpp
#define ABC__OPT__ESLIM2__RELATIONSYNTHESISER_hpp

#include <vector>
#include <unordered_map>

#include "misc/util/abc_global.h"

#include "relationGeneration.hpp"
#include "subcircuit.hpp"
#include "cadicalSolver.hpp"
#include "utils.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  class RelationSynthesiser {

    protected:
      CadicalSolver solver;
      const Subcircuit& subcir;
      unsigned int max_size; // The maximal circuit size that can be checked
      unsigned int min_size = 0; // A structural lower bound from mandatory input support.

      std::vector<int> gate_activation_variables;
      std::vector<std::vector<int>> selection_variables;
      std::vector<std::vector<int>> gate_output_variables;

      RelationSynthesiser(const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIM2Config& cfg, eSLIM2Log& log);
      int getNewVariable();
      std::vector<int> getNewVariableVector(unsigned int size);

      std::vector<int> getSizeAssumption(int size);
      double getDynamicTimeout(int size);
      unsigned int getSizeFromActivationVars(const std::vector<bool>& model);
      unsigned int getSizeFromActivationVars();
      void logRun(int status, unsigned int size);
      eSLIM2CirMan getReplacement(const std::vector<bool>& model, int size);


    private:
      const Relation& relation;
      const eSLIM2Config& config;
      eSLIM2Log& log;

      int max_var = 0;  // The maximal variable occurring in inputs/outputs

      std::vector<std::vector<std::vector<int>>> is_ith_fanin_variable;
      std::vector<std::vector<int>> gate_definition_variables;
      std::vector<std::vector<int>> gate_variables;


      void setupEncoding();
      void setupVariables();
      void setupStructuralConstraints();

      void setupSymmetryBreaking();
      void setupGateValues();
      std::vector<int> setupFaninVariables(int gtidx, int tt_line, int pidx);
      void setupEquivalenceConstraints();
      void setupActivationCompatibilityConstraints();
      void setupIsFaninVariables(int gtidx, const std::vector<std::vector<int>>& counter_vars);

      void constrainSelectionVariables();
      void constrainAigSelectionVariables();
      void constraintGateOutputVariables();
      void addGateValueConstraint(int gtidx, int gt_val, const std::vector<int>& fanin_variables);
      void setupCycleConstraints();
      void setupAigerConstraints();

      int setupOutputVariable(int output_index, int tt_index, int pattern_idx);

      void addNonTrivialConstraint();
      void addUseAllStepsConstraint();
      void addNoReapplicationConstraint();
      void addOrderedStepsConstraint();

      // activator = 0: do not use an activation variable
      void addCardinalityConstraint(const std::vector<int>& vars, unsigned int cardinality, int activator = 0);
      std::vector<std::vector<int>> addSequentialCounter(const std::vector<int>& vars, unsigned int cardinality, int activator = 0);

      void addNaiveIs1CardinalityConstraint(const std::vector<int>& vars);
      void addNaiveIs2CardinalityConstraint(const std::vector<int>& vars);

      void defineConjunction(int var, std::vector<int>&& literals, int activator);
      void defineDisjunction(int var, std::vector<int>&& literals, int activator);

      // computes the index of the first gate that can used the indexed nodes as inputs
      // indices must be ordered
      int getPotentialSuccessors(const std::vector<int>& indices) const;

      static bool getTTValue(int tt_line, int var);
      static unsigned int pow2(int x);

  };

  inline int RelationSynthesiser::getNewVariable() {
    return ++max_var;
  }

  inline std::vector<int> RelationSynthesiser::getNewVariableVector(unsigned int size) {
    std::vector<int> vars;
    vars.reserve(size);
    for (int i = 0; i < size; i++) {
      vars.push_back(getNewVariable());
    }
    return vars;
  }

  inline int RelationSynthesiser::getPotentialSuccessors(const std::vector<int>& indices) const {
    if (indices.back() < subcir.inputs.size()) {
      return 0;
    }
    return indices.back() - subcir.inputs.size() + 1;
  }

  inline bool RelationSynthesiser::getTTValue(int tt_line, int var) {
    return (tt_line >> var) & 1;
  }

  inline unsigned int RelationSynthesiser::pow2(int x) {
    return 1u << x;
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
