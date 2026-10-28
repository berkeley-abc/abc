/**CFile****************************************************************

  FileName    [eSLIM2Man.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [eSLIM2 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - March 2025.]

  Revision    [$Id: eSLIM2Man.hpp,v 1.00 2025/03/17 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__ESLIM2MAN_h
#define ABC__OPT__ESLIM2__ESLIM2MAN_h

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <map>

#include "misc/util/abc_namespaces.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"


#include "eslim2CirMan.hpp"
#include "relationGeneration.hpp"
#include "selectionStrategies.hpp"
#include "subcircuit.hpp"
#include "utils.hpp"



ABC_NAMESPACE_CXX_HEADER_START

namespace eSLIM2 {


  template <typename SynthesisEngine, typename SelectionStrategy>
  class eSLIM2_Man {
    public:
      static void applyeSLIM2(eSLIM2CirMan& cir, const eSLIM2Config& cfg, eSLIM2Log& log);
    private:

      eSLIM2_Man(eSLIM2CirMan& es_man, const eSLIM2Config& cfg, eSLIM2Log& log);

      void optimize();

      void findReplacement();
      void rewriteCircuit();
      eSLIM2CirMan computeReplacement(Subcircuit& subcir);
      eSLIM2CirMan synthesiseRelation(Subcircuit& subcir, const Relation& rel);


      eSLIM2CirMan& es_man;
      eSLIM2Config cfg;
      SelectionStrategy selection_strategy;
      eSLIM2Log& log;
      std::map<std::vector<ABC_UINT64_T>, eSLIM2CirMan> synthesis_cache;
      size_t cache_words = 0;

      double relation_generation_time ;
      double synthesis_time ;

      bool stopeSLIM2 = false;


  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "eSLIM2Man.tpp"

#endif
