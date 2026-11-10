/**CFile****************************************************************

  FileName    [areaEngine.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Implementation of area based SAT encoding.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__AREAENGINE_h
#define ABC__OPT__ESLIM3__AREAENGINE_h

#include "misc/util/abc_global.h"

#include "relationSynthesiser.h"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class AreaEngine : private RelationSynthesiser {

    public:
      static eSLIM3CirMan synthesiseSmall(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, int delay_bound = -1);
      static eSLIM3CirMan synthesiseWideSmall(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, int delay_bound);
      static eSLIM3CirMan synthesiseMinimumSizeCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, bool* complete = nullptr);

    private:

      std::unordered_map<int, std::vector<int>> connection_variables;
      std::unordered_map<int,int> input_index_map;
      std::unordered_map<int,int> output_index_map;

      AreaEngine(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log);

      int checkSize(unsigned int size, double timeout);
      int checkSize(unsigned int size);

      void setupCycleConstraints();
      void setupConnectionVariables();
      // If we have multiple cyclic pairs, different pairs may form form a cycle together
      // Assume we have two different pairs (x,y) and (a,b) in potential_cycles.
      // It can be the case that x is connected to b and a is connected to y.
      // To rule out cycles of this kind we make use of the following idea:
      // If (x,y) is in self.potential_cycles then there is a path from x to y that is not part of the current subcircuit.
      // Now if b is connected to x, this means that y is also connected to b.
      // Thus, all gates that use y as an input are connected to b.
      void connectionVariablesForCombinedCycles();
      void addCycleConstraints();
  };

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
