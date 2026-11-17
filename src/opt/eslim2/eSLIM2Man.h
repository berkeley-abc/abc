/**CFile****************************************************************

  FileName    [eSLIM2Man.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [eSLIM2 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__ESLIM2MAN_h
#define ABC__OPT__ESLIM2__ESLIM2MAN_h

#include <vector>
#include <array>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <memory>
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

      bool findReplacement();
      void addDivisors(Subcircuit& subcir);
      bool updateDivisorSignatures();
      unsigned signatureDistance(int left, int right) const;
      void rewriteCircuit();
      void rewriteLutCircuit();
      bool isUnchangedReplacement(const Subcircuit& subcir, const eSLIM2CirMan& replacement) const;
      std::shared_ptr<const Relation> getRelation(const Subcircuit& subcir);
      bool provesOptimal(const Subcircuit& subcir, const Relation& relation) const;
      unsigned rewritePeriod() const;
      void recordRewriteOutcome(bool improved);
      void invalidateGraphState(bool full = true);
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
      static constexpr size_t max_relation_cache_entries = 512;
      static constexpr size_t max_relation_cache_units = 1u << 17;
      static constexpr unsigned relation_cache_max_inputs = 10;
      static constexpr unsigned area_cache_max_inputs = 10;
      static constexpr unsigned timed_cache_max_inputs = 16;
      static constexpr unsigned cache_permutation_interval = 32;
      static constexpr unsigned rewrite_period_seconds = 2;
      static constexpr unsigned max_rewrite_period_seconds = 120;
      static constexpr unsigned max_rewrite_backoff = 6;
      static constexpr unsigned resubstitution_period = 5;
      static constexpr double initial_native_reserve = 2.0;
      static constexpr double native_reserve_margin = 0.5;
      static constexpr unsigned divisor_signature_words = 4;


      eSLIM2CirMan& es_man;
      eSLIM2Config cfg;
      SelectionStrategy selection_strategy;
      eSLIM2Log& log;
      std::map<std::vector<ABC_UINT64_T>, eSLIM2CirMan> synthesis_cache;
      std::map<std::vector<int>, std::shared_ptr<const Relation>> relation_cache;
      RelationContextState relation_context;
      size_t relation_cache_units = 0;
      // Zero records a complete no-change result; nonzero records the tried
      // budget scale. Graph mutation invalidates every topology/context key.
      std::map<std::vector<int>, unsigned> failed_cuts;
      bool last_search_complete = true;
      bool evaluated_cut = false;
      std::map<std::vector<ABC_UINT64_T>, unsigned> semantic_failures;
      size_t cache_words = 0;
      std::mt19937 cache_rng;
      double resubstitution_reserve = initial_native_reserve;
      double rewrite_reserve = initial_native_reserve;
      unsigned rewrite_no_gain_calls = 0;
      bool timings_dirty = true;
      bool strash_pending = false;
      bool divisor_signatures_dirty = true;
      std::vector<std::array<ABC_UINT64_T, divisor_signature_words>> divisor_signatures;

      double relation_generation_time ;
      double synthesis_time ;

      bool stopeSLIM2 = false;


  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "eSLIM2ManImpl.h"

#endif
