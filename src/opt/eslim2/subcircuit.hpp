/**CFile****************************************************************

  FileName    [subcircuit.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Subcircuit representation]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: subcircuit.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__SUBCIRCUIT_hpp
#define ABC__OPT__ESLIM2__SUBCIRCUIT_hpp

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <set>

#include "misc/util/abc_namespaces.h"

#include "eslim2CirMan.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  class Subcircuit {

    public:
      template <typename It>
      static Subcircuit getSubcircuitBare(eSLIM2CirMan& es_man, It begin, It end);
      static Subcircuit getSubcircuitBare(eSLIM2CirMan& es_man, const std::set<int>& nodes);
      static Subcircuit getEmptySubcircuit();

      // Marks the TFI/TFO cones of the subcircuit and derives the forbidden pairs.
      // Requires that the subcircuit nodes are marked (inSubcircuit) and the IOs are set,
      // i.e. the subcircuit was created by getSubcircuitBare.
      void markCones(eSLIM2CirMan& es_man);

      int setupTimings(eSLIM2CirMan& es_man);

      std::vector<int> nodes;
      std::vector<int> inputs;
      std::vector<int> outputs;
      // Assigns the inputs of the subcircuit that can be reached from an output x to x.
      std::unordered_map<int, std::set<int>> forbidden_pairs;

      std::vector<unsigned int> arrival_times;
      std::vector<unsigned int> remaining_times;

      void print() const;

    private:
      template <typename It>
      Subcircuit(eSLIM2CirMan& es_man, It begin, It end);
      Subcircuit() = default;
      void setIO(eSLIM2CirMan& es_man);
      void setForbiddenPairs(const eSLIM2CirMan& es_man);
      void getForbiddenPairsRec(int inp, std::unordered_set<int>& seen, const eSLIM2CirObj& obj, const eSLIM2CirMan& es_man);
  };

  template <typename It>
  Subcircuit::Subcircuit(eSLIM2CirMan& es_man, It begin, It end) : nodes(begin, end) {
    es_man.markSubcircuit(this->nodes);
    setIO(es_man);
  }

  template <typename It>
  Subcircuit Subcircuit::getSubcircuitBare(eSLIM2CirMan& es_man, It begin, It end) {
    Subcircuit scir(es_man, begin, end);
    return scir;
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
