/**CFile****************************************************************

  FileName    [eSLIM2Man.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [eSLIM2 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - March 2025.]

  Revision    [$Id: eSLIM2Man.h,v 1.00 2025/03/17 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__ESLIM2MAN_h
#define ABC__OPT__ESLIM2__ESLIM2MAN_h

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <random>

#include "misc/util/abc_namespaces.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"


#include "eslim2CirMan.h"
#include "relationGeneration.h"
#include "selectionStrategies.h"
#include "subcircuit.h"
#include "utils.h"



ABC_NAMESPACE_CXX_HEADER_START

namespace eSLIM2 {


  template <typename SynthesisEngine, typename SelectionStrategy>
  class eSLIM2_Man {
    friend struct eSLIM2TestAccess;
    public:
      static void applyeSLIM2(eSLIM2CirMan& cir, const eSLIM2Config& cfg, eSLIM2Log& log);
    private:

      eSLIM2_Man(eSLIM2CirMan& es_man, const eSLIM2Config& cfg, eSLIM2Log& log);

      void optimize();

      void findReplacement();
      void rewriteCircuit();
      eSLIM2CirMan computeReplacement(Subcircuit& subcir);
      eSLIM2CirMan synthesiseRelation(Subcircuit& subcir, const Relation& rel);

      struct CacheQuery {
        std::vector<ABC_UINT64_T> words;
        std::vector<unsigned> input_order;
        size_t relation_offset = 0;
      };
      CacheQuery buildCacheQuery(const Subcircuit& subcir, const Relation& rel) const;
      eSLIM2CirMan reuseCachedReplacement(const CacheQuery& query, const Subcircuit& subcir,
                                         const eSLIM2CirMan& cached);
      void storeCachedReplacement(CacheQuery&& query, const eSLIM2CirMan& replacement);

      static constexpr size_t max_cache_entries = 4096;
      static constexpr size_t max_cache_words = 1u << 21;
      static constexpr unsigned area_cache_max_inputs = 10;
      static constexpr unsigned timed_cache_max_inputs = 16;
      static constexpr unsigned cache_permutation_interval = 32;
      static constexpr unsigned rewrite_period_seconds = 2;
      static constexpr unsigned resubstitution_period = 5;
      static constexpr double initial_native_reserve = 2.0;
      static constexpr double native_reserve_margin = 0.5;


      eSLIM2CirMan& es_man;
      eSLIM2Config cfg;
      SelectionStrategy selection_strategy;
      eSLIM2Log& log;
      std::map<std::vector<ABC_UINT64_T>, eSLIM2CirMan> synthesis_cache;
      size_t cache_words = 0;
      std::mt19937 cache_rng;
      double resubstitution_reserve = initial_native_reserve;
      double rewrite_reserve = initial_native_reserve;

      double relation_generation_time ;
      double synthesis_time ;

      bool stopeSLIM2 = false;


  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "eSLIM2ManImpl.h"

#endif
