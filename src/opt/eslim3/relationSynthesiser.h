/**CFile****************************************************************

  FileName    [relationSynthesiser.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Base class for SAT-based synthesis]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__RELATIONSYNTHESISER_h
#define ABC__OPT__ESLIM3__RELATIONSYNTHESISER_h

#include <vector>
#include <cstddef>
#include <unordered_map>

#include "misc/util/abc_global.h"

#include "relationGeneration.h"
#include "subcircuit.h"
#include "synthesisSolver.h"
#include "utils.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class RelationSynthesiser {
    friend struct eSLIM3TestAccess;

    protected:
      SynthesisSolver solver;
      const Subcircuit& subcir;
      unsigned int max_size; // The maximal circuit size that can be checked
      unsigned int min_size = 0; // A structural lower bound from mandatory input support.

      std::vector<int> gate_activation_variables;
      std::vector<std::vector<int>> selection_variables;
      std::vector<std::vector<int>> gate_output_variables;

      RelationSynthesiser(const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIM3Config& cfg, eSLIM3Log& log, bool refine = false);
      int getNewVariable();
      std::vector<bool> getModel();
      std::vector<int> getNewVariableVector(unsigned int size);

      std::vector<int> getSizeAssumption(int size);
      double getDynamicTimeout(int size);
      bool retrySmallerAfterTimeout(int status, unsigned size) const;
      unsigned int getSizeFromActivationVars(const std::vector<bool>& model);
      unsigned int getSizeFromActivationVars();
      void logRun(int status, unsigned int size);
      eSLIM3CirMan getReplacement(const std::vector<bool>& model, int size);
      int solveRelation(const std::vector<int>& assumptions, double timeout, unsigned size, bool log_model_size = false);
      void constrainIrredundantAigArea();


    private:
      const Relation& relation;
      const eSLIM3Config& config;
      eSLIM3Log& log;
      bool logged_smaller_model = false;

      int max_var = 0;  // The maximal variable occurring in inputs/outputs
      bool refine;
      static constexpr unsigned minimum_refinement_rows = 32;
      static constexpr unsigned refinement_seed_rows = 32;
      static constexpr unsigned refinement_batch_rows = 8;
      static constexpr unsigned long_budget_interval = 16;
      static constexpr unsigned long_budget_multiplier = 10;
      static constexpr unsigned large_cut_threshold = 5;
      unsigned encoded_count = 0;
      std::vector<bool> encoded_rows;
      std::vector<ABC_UINT64_T> forbidden_tuples;
      std::vector<unsigned> mandatory_inputs;
      std::vector<std::vector<unsigned>> output_mandatory_inputs;

      std::vector<std::vector<std::vector<int>>> is_ith_fanin_variable;
      std::vector<std::vector<int>> gate_definition_variables;
      std::vector<std::vector<int>> gate_variables;


      void setupEncoding();
      SynthesisBudgetStats& budgetStats();
      void analyseMandatorySupport();
      void setupVariables();
      void setupStructuralConstraints();
      void constrainMandatorySupport();
      void constrainOutputSupports();
      void constrainSupportTrees();

      void setupSymmetryBreaking();
      void addRelationRow(unsigned row);
      std::vector<unsigned> findCounterexamples(const std::vector<bool>& model) const;
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

/**Function*************************************************************

  Synopsis    [Allocates the next synthesis SAT variable.]

***********************************************************************/
  inline int RelationSynthesiser::getNewVariable() {
    return ++max_var;
  }

/**Function*************************************************************

  Synopsis    [Allocates a vector of fresh synthesis SAT variables.]

***********************************************************************/
  inline std::vector<int> RelationSynthesiser::getNewVariableVector(unsigned int size) {
    std::vector<int> vars;
    vars.reserve(size);
    for (unsigned int i = 0; i < size; i++) {
      vars.push_back(getNewVariable());
    }
    return vars;
  }

/**Function*************************************************************

  Synopsis    [Returns the first gate index that can use all selected predecessors.]

***********************************************************************/
  inline int RelationSynthesiser::getPotentialSuccessors(const std::vector<int>& indices) const {
    if (static_cast<std::size_t>(indices.back()) < subcir.inputs.size()) {
      return 0;
    }
    return indices.back() - subcir.inputs.size() + 1;
  }

/**Function*************************************************************

  Synopsis    [Reads one variable value from a truth-table row index.]

***********************************************************************/
  inline bool RelationSynthesiser::getTTValue(int tt_line, int var) {
    return (tt_line >> var) & 1;
  }

/**Function*************************************************************

  Synopsis    [Returns a power of two for a valid unsigned shift count.]

***********************************************************************/
  inline unsigned int RelationSynthesiser::pow2(int x) {
    return 1u << x;
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
