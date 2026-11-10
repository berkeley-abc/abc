/**CFile****************************************************************

  FileName    [eSLIM3Man.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [eSLIM3 manager.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__ESLIM3MAN_h
#define ABC__OPT__ESLIM3__ESLIM3MAN_h

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


#include "eslim3CirMan.h"
#include "relationGeneration.h"
#include "selectionStrategies.h"
#include "subcircuit.h"
#include "utils.h"



ABC_NAMESPACE_CXX_HEADER_START

namespace eSLIM3 {


  template <typename SynthesisEngine, typename SelectionStrategy>
  class eSLIM3_Man {
    friend struct eSLIM3TestAccess;
    public:
      static void applyeSLIM3(eSLIM3CirMan& cir, const eSLIM3Config& cfg, eSLIM3Log& log);
    private:

      eSLIM3_Man(eSLIM3CirMan& es_man, const eSLIM3Config& cfg, eSLIM3Log& log);

      void optimize();

      void findReplacement();
      void addDivisors(Subcircuit& subcir);
      bool updateDivisorSignatures();
      unsigned signatureDistance(int left, int right) const;
      void rewriteCircuit();
      bool isUnchangedReplacement(const Subcircuit& subcir, const eSLIM3CirMan& replacement) const;
      std::shared_ptr<const Relation> getRelation(const Subcircuit& subcir);
      bool provesOptimal(const Subcircuit& subcir, const Relation& relation) const;
      unsigned rewritePeriod() const;
      void recordRewriteOutcome(bool improved);
      void invalidateGraphState();
      eSLIM3CirMan computeReplacement(Subcircuit& subcir);
      eSLIM3CirMan synthesiseRelation(Subcircuit& subcir, const Relation& rel);

      struct CacheQuery {
        std::vector<ABC_UINT64_T> words;
        std::vector<unsigned> input_order;
        size_t relation_offset = 0;
      };
      CacheQuery buildCacheQuery(const Subcircuit& subcir, const Relation& rel) const;
      eSLIM3CirMan reuseCachedReplacement(const CacheQuery& query, const Subcircuit& subcir,
                                         const eSLIM3CirMan& cached);
      void storeCachedReplacement(CacheQuery&& query, const eSLIM3CirMan& replacement);

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


      eSLIM3CirMan& es_man;
      eSLIM3Config cfg;
      SelectionStrategy selection_strategy;
      eSLIM3Log& log;
      std::map<std::vector<ABC_UINT64_T>, eSLIM3CirMan> synthesis_cache;
      std::map<std::vector<int>, std::shared_ptr<const Relation>> relation_cache;
      RelationContextState relation_context;
      size_t relation_cache_units = 0;
      size_t cache_words = 0;
      std::mt19937 cache_rng;
      double resubstitution_reserve = initial_native_reserve;
      double rewrite_reserve = initial_native_reserve;
      unsigned rewrite_no_gain_calls = 0;
      bool timings_dirty = true;
      bool divisor_signatures_dirty = true;
      std::vector<std::array<ABC_UINT64_T, divisor_signature_words>> divisor_signatures;

      double relation_generation_time ;
      double synthesis_time ;

      bool stopeSLIM3 = false;


  };

}
ABC_NAMESPACE_CXX_HEADER_END

#include "eSLIM3ManImpl.h"

#endif
