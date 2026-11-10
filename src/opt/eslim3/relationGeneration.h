/**CFile****************************************************************

  FileName    [relationGeneration.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [SAT-based computation of Boolean relations.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__RELATIONGENERATION_h
#define ABC__OPT__ESLIM3__RELATIONGENERATION_h

#include <vector>
#include <unordered_map>
#include <functional>
#include <algorithm>
#include <utility>

#include "misc/util/abc_namespaces.h"

#include "eslim3CirMan.h"
#include "cadicalSolver.h"
#include "subcircuit.h"
#include "utils.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class RelationGenerator;

  struct RelationContextState {
    enum class Start { Initial, Reused, Probe };
    static constexpr unsigned probe_interval = 32;
    unsigned requests = 0;
    unsigned gates = 0, inputs = 0, fanin = 0, fanout = 0;
    bool valid = false;

/**Function*************************************************************

  Synopsis    [Starts from successful context caps and periodically probes the configured caps.]

***********************************************************************/
    Start prepare(eSLIM3Config& attempt) {
      ++requests;
      if (!valid) return Start::Initial;
      if (requests % probe_interval == 0) return Start::Probe;
      restrictToRemembered(attempt);
      return Start::Reused;
    }

/**Function*************************************************************

  Synopsis    [Restricts a fresh or failed-probe attempt to the last successful caps.]

***********************************************************************/
    bool restrictToRemembered(eSLIM3Config& attempt) const {
      if (!valid) return false;
      const bool smaller = gates < attempt.relation_window_gates || inputs < attempt.relation_window_inputs ||
          fanin < attempt.relation_window_fanin || fanout < attempt.relation_window_fanout;
      attempt.relation_window_gates = std::min(attempt.relation_window_gates, gates);
      attempt.relation_window_inputs = std::min(attempt.relation_window_inputs, inputs);
      attempt.relation_window_fanin = std::min(attempt.relation_window_fanin, fanin);
      attempt.relation_window_fanout = std::min(attempt.relation_window_fanout, fanout);
      return smaller;
    }

/**Function*************************************************************

  Synopsis    [Remembers caps only after a complete relation or a witnessed optimality proof.]

***********************************************************************/
    void remember(const eSLIM3Config& attempt) {
      gates = attempt.relation_window_gates;
      inputs = attempt.relation_window_inputs;
      fanin = attempt.relation_window_fanin;
      fanout = attempt.relation_window_fanout;
      valid = true;
    }
  };

  struct SupportBounds {
    unsigned minimum_gates = 0;
    std::vector<ABC_UINT64_T> forbidden;
    std::vector<unsigned> inputs;
    std::vector<std::vector<unsigned>> output_inputs;
    unsigned minimumArrival(unsigned output, const std::vector<unsigned>& arrivals) const;
  };

  class Relation{
    friend struct eSLIM3TestAccess;

    public:
      Relation(int nfanins);
      const std::vector<std::vector<bool>>& getPattern(int id) const {return output_patterns[id];}
      int getNPatterns() const {return output_patterns.size();}
      int getPatternSize(int id) const {return output_patterns[id].size();}
      unsigned int getNLinesWithPattern() const {return lines_with_pattern;}
      bool getStatus() const {return status;}
      bool isProvenOptimal() const { return proven_optimal; }
      ABC_UINT64_T getForbiddenTuples(unsigned row, unsigned noutputs) const;
      SupportBounds analyseSupport(unsigned noutputs, unsigned gate_size) const;


    private:

      // Each entry of the first vector level corresponds to an input assignment.
      // The second level lists all conflicting output assignments.
      // The third lists the individual conflicting output assignments.
      // One output is represented by two bits, the first bit determines if this output is present the conflicting output assignments
      // and the second indicate if it is true or false
      void addOutputPattern(int inputidx, std::vector<bool>&& pattern);
      std::vector<std::vector<std::vector<bool>>> output_patterns;

      unsigned int lines_with_pattern = 0;
      bool status = true;
      bool proven_optimal = false;


    friend RelationGenerator;
  };

  class RelationGenerator {
    friend struct eSLIM3TestAccess;

    public:
      using OptimalityCheck = std::function<bool(const Relation&)>;
      static Relation computeRelation(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, const OptimalityCheck& optimal = {}, RelationContextState* context = nullptr);
      static bool verifyReplacement(const eSLIM3CirMan& replacement, const Subcircuit& subcir, const Relation& relation, const eSLIM3Config& cfg);

    private:
      static Relation computeWindowRelation(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, const OptimalityCheck& optimal, RelationContextState* context);
      static Relation computeWindowAttempt(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, const OptimalityCheck& optimal, bool& has_context);
      static bool collectWitnesses(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, Relation& rel);
      static bool sampleRelation(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg, Relation& rel, unsigned* patterns = nullptr);
      static ABC_UINT64_T samplingSeed(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg);
      const eSLIM3CirMan& cir;
      const Subcircuit& subcir;

      const eSLIM3Config& cfg;
      eSLIM3Log& log;

      int max_var = 1;

      std::vector<int> gate2varref;
      std::vector<int> gate2varcone;
      std::vector<int> equality_variables;
      std::vector<int> compared_nodes;
      unsigned current_exit = 0;
      std::vector<int> cone_input_variables;
      int mode_selection_variable;

      using WitnessWord = ABC_UINT64_T;
      using WitnessRow = std::pair<unsigned, std::vector<WitnessWord>>;
      using WitnessRows = std::vector<WitnessRow>;
      bool witness_simulation = false;
      std::vector<int> affected_nodes;
      std::vector<WitnessWord> witness_support, witness_values;


      CadicalSolver solver;

      RelationGenerator(const eSLIM3CirMan& cir, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log);
      void setupEncoding();
      void strengthenMiter();
      void prepareWitnessSimulation();
      void preserveFeedbackOutputs(std::vector<bool>& outputs_to_keep) const;
      bool justifyConflict(WitnessWord& required_outputs);
      WitnessRows sampleConflict();
      void addConflictSamples(Relation& relation, const WitnessRows& samples,
                              const std::vector<int>& inputs, const std::vector<int>& outputs);

      void encodeCircuitAffected();
      void encodeCircuitApproximative();
      void encodeCircuitApproximativeBoundedTFI();
      std::vector<int> markRestrictedCone();
      void setupConstantGate();
      void setupEqualityConstraints(const std::vector<int>& nodes);

      Relation getRelation();
      Relation getRelation(Relation relation, bool sampled);
      void seedRelation(Relation& relation, const std::vector<int>& input_variables,
                        const std::vector<int>& output_variables);

      void encodeGate(const eSLIM3CirObj& obj, int var, const std::vector<int>& gate2var);
      void getGateEncodingUnique(const eSLIM3CirObj& obj, int var, const std::vector<int>& gate2var, bool unique_bit);
      void getGateEncodingNaive(const eSLIM3CirObj& obj, int var, const std::vector<int>& gate2var);
      void getEqualityClauses(int x, int y, int aux);
      int assignment2bvindex(const std::vector<int>& assm);

      int findConflict(double& timeout, int mode_selection);
      int reduceConflict(double& timeout, const std::vector<int>& cone_input, const std::vector<int>& subcircuit_output, const std::vector<int>& equality);


      int getNewVar();

  };

}
ABC_NAMESPACE_CXX_HEADER_END

#endif
