/**CFile****************************************************************

  FileName    [relationGeneration.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [SAT-based computation of Boolean relations.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: relationGeneration.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__RELATIONGENERATION_hpp
#define ABC__OPT__ESLIM2__RELATIONGENERATION_hpp

#include <vector>
#include <unordered_map>

#include "misc/util/abc_namespaces.h"

#include "eslim2CirMan.hpp"
#include "cadicalSolver.hpp"
#include "subcircuit.hpp"
#include "utils.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  class RelationGenerator;

  class Relation{

    public:
      Relation(int nfanins);
      const std::vector<std::vector<bool>>& getPattern(int id) const {return output_patterns[id];}
      int getNPatterns() const {return output_patterns.size();}
      int getPatternSize(int id) const {return output_patterns[id].size();}
      unsigned int getNLinesWithPattern() const {return lines_with_pattern;}
      bool getStatus() const {return status;}
      ABC_UINT64_T getForbiddenTuples(unsigned row, unsigned noutputs) const;


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


    friend RelationGenerator;
  };

  class RelationGenerator {

    public:
      static Relation computeRelation(const eSLIM2CirMan& cir, const Subcircuit& subcir, const eSLIM2Config& cfg, eSLIM2Log& log);

    private:
      static bool simulateRelation(const eSLIM2CirMan& cir, const Subcircuit& subcir, const eSLIM2Config& cfg, Relation& rel);
      const eSLIM2CirMan& cir;
      const Subcircuit& subcir;

      const eSLIM2Config& cfg;
      eSLIM2Log& log;

      int max_var = 1;

      std::vector<int> gate2varref;
      std::vector<int> gate2varcone;
      std::vector<int> equality_variables;
      std::vector<int> cone_input_variables;
      int mode_selection_variable;


      CadicalSolver solver;

      RelationGenerator(const eSLIM2CirMan& cir, const Subcircuit& subcir, const eSLIM2Config& cfg, eSLIM2Log& log);
      void setupEncoding();

      void encodeCircuitAffected();
      void encodeCircuitApproximative();
      void encodeCircuitApproximativeBoundedTFI();
      std::vector<int> markRestrictedCone();
      void setupConstantGate();
      void setupEqualityConstraints(const std::vector<int>& nodes);

      Relation getRelation();

      void encodeGate(const eSLIM2CirObj& obj, int var, const std::vector<int>& gate2var);
      void getGateEncodingUnique(const eSLIM2CirObj& obj, int var, const std::vector<int>& gate2var, bool unique_bit);
      void getGateEncodingNaive(const eSLIM2CirObj& obj, int var, const std::vector<int>& gate2var);
      void getEqualityClauses(int x, int y, int aux);
      int assignment2bvindex(const std::vector<int>& assm);

      int findConflict(double& timeout, int mode_selection);
      int reduceConflict(double& timeout, const std::vector<int>& cone_input, const std::vector<int>& subcircuit_output, const std::vector<int>& equality);


      int getNewVar();

  };

}
ABC_NAMESPACE_CXX_HEADER_END

#endif
