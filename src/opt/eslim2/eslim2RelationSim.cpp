/**CFile****************************************************************

  FileName    [eslim2RelationSim.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Bounded exhaustive relation computation with manager-owned caching.]

  Author      [Franz-Xaver Reichl and ABC contributors; adapted from eSLIM2.]

  Date        [Ver. 1.0. Started - November 15, 2026.]

***********************************************************************/

#include <limits>
#include "relationGeneration.h"

ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {

/**Function*************************************************************

  Synopsis    [Enumerates all context assignments and forced cut-output tuples.]

  Description [The context is fixed by the caller. Forbidden tuples use cut
  input values from the changed circuit, including feedback-related divisors.
  Only a complete result may be passed to synthesis or a relation cache.]

***********************************************************************/
  RelationSimulationStatus RelationGenerator::simulateRelation(const eSLIM2CirMan& cir, const Subcircuit& subcir,
      const eSLIM2Config& cfg, Relation& rel, eSLIM2Log& log) {
    typedef ABC_UINT64_T Word;
    using Status = RelationSimulationStatus;
    using Rejection = RelationSimulationRejection;
    auto reject = [&](Rejection reason) {
      ++log.simulation.rejected[unsigned(reason)];
      return Status::Ineligible;
    };
    auto interrupt = [&]() {
      rel.status = false;
      ++log.simulation.interrupted;
      return Status::Interrupted;
    };
    // Capacities, hash buckets and conservative allocation metadata are charged
    // to simulation. Relation cubes are reported separately from this budget.
    const Word entryBytes = sizeof(std::pair<const unsigned, eSLIM2CirMan::SimulationEntry>) +
                            3 * sizeof(void*) + 2 * sizeof(Word);
    auto cacheBytes = [&]() -> Word {
      if (!cir.simulation_cache) return 0;
      const auto& cache = *cir.simulation_cache;
      Word bytes = sizeof(cache) + Word(cache.reference.capacity() + cache.versions.capacity()) * sizeof(Word) +
                   Word(cache.input_domain.capacity()) * sizeof(unsigned) +
                   Word(cache.entries.bucket_count()) * sizeof(void*);
      for (const auto& item : cache.entries)
        bytes += entryBytes + Word(item.second.values.capacity()) * sizeof(Word);
      return bytes;
    };
    struct StorageReport {
      std::function<void()> finish;
      ~StorageReport() { finish(); }
    } report{[&]() {
      const Word retained = cacheBytes();
      log.simulation.retained_bytes = retained;
      log.simulation.cache_peak_bytes = std::max(log.simulation.cache_peak_bytes, retained);
    }};
    const unsigned nPis = cir.getNofPis();
    const unsigned nInputs = subcir.inputs.size();
    const unsigned nOutputs = subcir.outputs.size();
    if (cir.simulation_cache && cir.simulation_cache->input_domain.size() != nPis)
      cir.simulation_cache.reset();
    if (cfg.approximate_relation) return reject(Rejection::Unsupported);
    if (nPis > 20) return reject(Rejection::ContextInputs);
    if (nInputs > 10) return reject(Rejection::CutInputs);
    if (!nOutputs || nOutputs > 6) return reject(Rejection::CutOutputs);
    if (cfg.expired()) return interrupt();
    const unsigned nWords = 1u << (nPis > 6 ? nPis - 6 : 0);
    const unsigned nRows = 1u << nInputs;
    const unsigned nTuples = 1u << nOutputs;
    const unsigned nNodes = cir.getNofObjs() - cir.getNofPos();
    const Word memoryLimit = Word(32) << 20;
    const Word baseWords = (2ull * nNodes + nRows + 1) * nWords + nRows;
    // These counts are bounded before conversion to size_t or allocation.
    if (nNodes > std::numeric_limits<size_t>::max() / nWords)
      return reject(Rejection::Memory);
    // Include geometric capacities of affected-cone vectors, Gray-code maps,
    // temporary versions, domain IDs, vector headers and allocation metadata.
    const Word auxiliaryBytes = (Word(5 + 2 * nOutputs) * nNodes + 2ull * cir.getNofPos() +
                                 2ull * nInputs + nPis) * sizeof(unsigned) +
                                Word(nNodes) * sizeof(Word) + 4096;
    if (baseWords > memoryLimit / sizeof(Word) ||
        auxiliaryBytes > memoryLimit - baseWords * sizeof(Word))
      return reject(Rejection::Memory);
    const Word tableBytes = baseWords * sizeof(Word) + auxiliaryBytes;
    // Retained cache storage must also leave room for admission scratch.
    if (cir.simulation_cache && cacheBytes() + auxiliaryBytes > memoryLimit) {
      auto& cache = *cir.simulation_cache;
      std::vector<Word>().swap(cache.reference);
      std::vector<Word>().swap(cache.versions);
      Word retained = cacheBytes();
      while (!cache.entries.empty() && retained + auxiliaryBytes > memoryLimit) {
        auto entry = cache.entries.begin();
        retained -= entryBytes + Word(entry->second.values.capacity()) * sizeof(Word);
        cache.entries.erase(entry);
      }
      if (cache.entries.empty()) decltype(cache.entries)().swap(cache.entries);
    }
    std::vector<int> affected, compared;
    std::vector<unsigned> feedback_inputs;
    unsigned feedback_mask = 0;
    for (unsigned j = 0; j < nInputs; ++j)
      if (cir.inTFO(cir.getObj(subcir.inputs[j]))) {
        feedback_inputs.push_back(j);
        feedback_mask |= 1u << j;
      }
    Word gate_work = 0, affected_work = 0;
    for (unsigned i = nPis + 1; i < nNodes; ++i) {
      const auto& obj = cir.getObj(i);
      if (!(i & 255) && cfg.expired()) return interrupt();
      if (obj.getNFanins() > 6) return reject(Rejection::Unsupported);
      const Word cost = obj.getNFanins() == 2 ? 1 : (Word(1) << obj.getNFanins());
      gate_work += cost;
      if (cir.inTFO(obj) && !cir.inSubcircuit(obj)) {
        affected.push_back(i);
        affected_work += cost;
      }
    }
    for (int i = nNodes; i < cir.getNofObjs(); ++i) {
      if (!(i & 255) && cfg.expired()) return interrupt();
      if (cir.inTFO(cir.getObj(i)))
        compared.push_back(cir.getObj(i).fanins[0]->node_id);
    }
    const Word estimatedWork = (nPis + 1 + gate_work + Word(nRows) * nInputs +
        Word(nTuples) * (affected_work + compared.size() +
                        Word(nRows) * (1ull + feedback_inputs.size()))) * nWords;
    if (estimatedWork > (Word(1) << 26)) return reject(Rejection::Work);
    std::vector<unsigned> domain;
    domain.reserve(nPis);
    for (unsigned i = 1; i <= nPis; ++i) domain.push_back(cir.getObj(i).getId());
    if (cir.simulation_cache && (cir.simulation_cache->words != nWords ||
        cir.simulation_cache->input_domain != domain ||
        cir.simulation_cache->next_version > std::numeric_limits<Word>::max() - nNodes))
      cir.simulation_cache.reset();
    const Word tableWords = (tableBytes + sizeof(Word) - 1) / sizeof(Word);
    const Word memoryWords = memoryLimit / sizeof(Word);
    // Count cached vectors, retained reference capacity, and metadata against
    // the same allowance. A cut that cannot populate a full cache can still
    // use fast simulation and retain existing entries for later, smaller cuts.
    bool persistent = cfg.cache_simulation && cfg.fast_simulation && nWords >= 64;
    Word estimatedBytes = tableBytes;
    if (persistent) {
      const auto* previous = cir.simulation_cache.get();
      const ABC_UINT64_T gates = nNodes - nPis - 1;
      const ABC_UINT64_T referenceWords = ABC_UINT64_T(nNodes) * nWords;
      const ABC_UINT64_T retainedReference = previous ? std::max(referenceWords, ABC_UINT64_T(previous->reference.capacity())) : referenceWords;
      const ABC_UINT64_T retainedVersions = previous ? std::max(ABC_UINT64_T(nNodes), ABC_UINT64_T(previous->versions.capacity())) : nNodes;
      const ABC_UINT64_T buckets = previous ? std::max(2 * (gates + 1), ABC_UINT64_T(previous->entries.bucket_count())) : 2 * (gates + 1);
      const ABC_UINT64_T metadataWords = (gates * entryBytes + buckets * sizeof(void*) + sizeof(Word) - 1) / sizeof(Word);
      const Word estimate = tableWords + gates * nWords + retainedReference - referenceWords +
                            nNodes + retainedVersions + metadataWords + 64;
      persistent = estimate <= memoryWords;
      if (persistent) estimatedBytes = estimate * sizeof(Word);
    }
    log.simulation.estimated_peak_bytes = std::max(log.simulation.estimated_peak_bytes, estimatedBytes);
    if (persistent && !cir.simulation_cache)
      cir.simulation_cache = std::make_unique<eSLIM2CirMan::SimulationCache>();
    auto* storage = cir.simulation_cache.get();
    auto* cache = persistent ? storage : nullptr;
    std::vector<Word> temporary_reference;
    std::vector<Word>& reference = storage ? storage->reference : temporary_reference;
    auto observeStorage = [&](Word extra) {
      const Word cached = storage ? cacheBytes() : 0;
      log.simulation.cache_peak_bytes = std::max(log.simulation.cache_peak_bytes, cached);
      Word allocated = storage ? cached : Word(reference.capacity()) * sizeof(Word);
      allocated += Word(affected.capacity() + compared.capacity()) * sizeof(int) +
                   Word(feedback_inputs.capacity() + domain.capacity()) * sizeof(unsigned) + extra;
      log.simulation.allocated_peak_bytes = std::max(log.simulation.allocated_peak_bytes, allocated);
      assert(allocated <= memoryLimit);
    };
    if (storage) {
      storage->words = nWords;
      storage->input_domain = domain;
      // Remove dead rows before inserting replacement gates, so cached vectors
      // never outnumber the live gates included in the admission calculation.
      for (unsigned i = nPis + 1; i < nNodes; ++i) {
        auto entry = storage->entries.find(cir.getObj(i).getId());
        if (entry != storage->entries.end())
          entry->second.live = true;
      }
      for (auto entry = storage->entries.begin(); entry != storage->entries.end(); ) {
        if (!entry->second.live)
          entry = storage->entries.erase(entry);
        else {
          entry->second.live = false;
          ++entry;
        }
      }
      // Avoid geometric capacity growth outside the accounted reference size.
      // New zero-filled rows must not retain the old per-row version tags.
      if (persistent && reference.capacity() < size_t(nNodes) * nWords) {
        std::vector<Word>().swap(reference);
        std::vector<Word>().swap(storage->versions);
        reference.resize(size_t(nNodes) * nWords, 0);
      }
      if (!persistent) {
        // Borrow the reference buffer instead of allocating a second one.
        // Uncached evaluation overwrites its rows without updating their tags;
        // retained entries remain valid, but the dense-row tags must be cleared.
        std::vector<Word>().swap(storage->versions);
        if (reference.capacity() != size_t(nNodes) * nWords) {
          std::vector<Word>().swap(reference);
          reference.resize(size_t(nNodes) * nWords, 0);
        }
        observeStorage(0);
        const Word entryWords = (entryBytes + sizeof(Word) - 1) / sizeof(Word);
        ABC_UINT64_T retainedWords = (storage->entries.bucket_count() * sizeof(void*) + sizeof(Word) - 1) / sizeof(Word);
        for (const auto& entry : storage->entries)
          retainedWords += entryWords + entry.second.values.capacity();
        // Keeping all entries can itself exceed the allowance on a large cut.
        // Evict only enough rows to fit, preserving the other value versions.
        while (!storage->entries.empty() && tableWords + retainedWords + 64 > memoryWords) {
          auto entry = storage->entries.begin();
          retainedWords -= entryWords + entry->second.values.capacity();
          storage->entries.erase(entry);
        }
        if (storage->entries.empty()) {
          // Release the bucket array too; an uncached cut may use the full budget.
          decltype(storage->entries)().swap(storage->entries);
        }
      }
    }
    reference.resize(size_t(nNodes) * nWords, 0);
    observeStorage(0);
    if (cfg.expired()) return interrupt();
    for (unsigned i = 0; i < nPis; ++i)
      for (unsigned w = 0; w < nWords; ++w)
        reference[size_t(i + 1) * nWords + w] = i < 6 ? truth_patterns[i] :
            ((w >> (i - 6)) & 1 ? ~Word(0) : Word(0));
    auto evaluate = [nWords, &cir, &cfg, &log](std::vector<Word>& values, int i) {
      ++log.simulation.evaluated_gates;
      const auto& obj = cir.getObj(i);
      if (obj.fanins.size() != 2) {
        std::array<Word, 6> inputs{};
        for (unsigned w = 0; w < nWords; ++w) {
          for (unsigned pin = 0; pin < obj.fanins.size(); ++pin)
            inputs[pin] = values[size_t(obj.fanins[pin]->node_id) * nWords + w];
          values[size_t(i) * nWords + w] = evaluateLutWord(obj.tt, inputs.data(), obj.fanins.size());
        }
        return;
      }
      const Word* a = &values[size_t(obj.fanins[0]->node_id) * nWords];
      const Word* b = &values[size_t(obj.fanins[1]->node_id) * nWords];
      Word* out = &values[size_t(i) * nWords];
      // Select the Boolean operation once per gate, outside the word loop.
      if (cfg.fast_simulation) {
        switch (unsigned(obj.tt) & 15u) {
          case 0: for (unsigned w = 0; w < nWords; ++w) out[w] = Word(0); break;
          case 1: for (unsigned w = 0; w < nWords; ++w) out[w] = ~(a[w] | b[w]); break;
          case 2: for (unsigned w = 0; w < nWords; ++w) out[w] = a[w] & ~b[w]; break;
          case 3: for (unsigned w = 0; w < nWords; ++w) out[w] = ~b[w]; break;
          case 4: for (unsigned w = 0; w < nWords; ++w) out[w] = ~a[w] & b[w]; break;
          case 5: for (unsigned w = 0; w < nWords; ++w) out[w] = ~a[w]; break;
          case 6: for (unsigned w = 0; w < nWords; ++w) out[w] = a[w] ^ b[w]; break;
          case 7: for (unsigned w = 0; w < nWords; ++w) out[w] = ~(a[w] & b[w]); break;
          case 8: for (unsigned w = 0; w < nWords; ++w) out[w] = a[w] & b[w]; break;
          case 9: for (unsigned w = 0; w < nWords; ++w) out[w] = ~(a[w] ^ b[w]); break;
          case 10: for (unsigned w = 0; w < nWords; ++w) out[w] = a[w]; break;
          case 11: for (unsigned w = 0; w < nWords; ++w) out[w] = a[w] | ~b[w]; break;
          case 12: for (unsigned w = 0; w < nWords; ++w) out[w] = b[w]; break;
          case 13: for (unsigned w = 0; w < nWords; ++w) out[w] = ~a[w] | b[w]; break;
          case 14: for (unsigned w = 0; w < nWords; ++w) out[w] = a[w] | b[w]; break;
          case 15: for (unsigned w = 0; w < nWords; ++w) out[w] = ~Word(0); break;
        }
        return;
      }
      const Word m0 = -Word((obj.tt >> 0) & 1), m1 = -Word((obj.tt >> 1) & 1);
      const Word m2 = -Word((obj.tt >> 2) & 1), m3 = -Word((obj.tt >> 3) & 1);
      for (unsigned w = 0; w < nWords; ++w)
        out[w] = (~a[w] & ~b[w] & m0) | (a[w] & ~b[w] & m1) |
                 (~a[w] & b[w] & m2) | (a[w] & b[w] & m3);
    };
    if (cache) {
      std::vector<Word> versions(nNodes, 0);
      for (unsigned i = 0; i <= nPis; ++i)
        versions[i] = i + 1;
      if (cache->versions.capacity() < nNodes) {
        std::vector<Word>().swap(cache->versions);
        cache->versions.resize(nNodes, 0);
      } else
        cache->versions.resize(nNodes, 0);
      observeStorage(Word(versions.capacity()) * sizeof(Word));
      for (unsigned i = nPis + 1; i < nNodes; ++i) {
        if (!(i & 31) && cfg.expired()) {
          observeStorage(Word(versions.capacity()) * sizeof(Word));
          return interrupt();
        }
        const auto& obj = cir.getObj(i);
        auto& entry = cache->entries[obj.getId()];
        std::array<Word, 6> inputs{};
        for (unsigned pin = 0; pin < obj.fanins.size(); ++pin)
          inputs[pin] = versions[obj.fanins[pin]->node_id];
        const auto begin = reference.begin() + size_t(i) * nWords;
        if (entry.version && entry.inputs == inputs && entry.fanins == obj.fanins.size() && entry.truth == obj.tt) {
          ++log.simulation.cache_hits;
          if (cache->versions[i] != entry.version)
            std::copy(entry.values.begin(), entry.values.end(), begin);
        } else {
          ++log.simulation.cache_misses;
          evaluate(reference, i);
          entry.inputs = inputs;
          entry.fanins = obj.fanins.size();
          entry.truth = obj.tt;
          // Equal truth tables stop invalidation, even after a structural change.
          if (!entry.version || entry.values.size() != nWords ||
              !std::equal(entry.values.begin(), entry.values.end(), begin))
            entry.version = ++cache->next_version;
          entry.values.assign(begin, begin + nWords);
        }
        versions[i] = entry.version;
        cache->versions[i] = entry.version;
      }
      observeStorage(Word(versions.capacity()) * sizeof(Word));
    } else {
      for (unsigned i = nPis + 1; i < nNodes; ++i) {
        if (!(i & 31) && cfg.expired()) return interrupt();
        evaluate(reference, i);
      }
    }
    // Account for the actual retained capacities before allocating the other
    // tables. Hash implementation growth must not bypass the admission bound.
    auto projectedBytes = [&]() -> Word {
      return tableBytes + (storage ? cacheBytes() - Word(reference.size()) * sizeof(Word) : 0);
    };
    if (storage) {
      Word projected = projectedBytes();
      while (!storage->entries.empty() && projected > memoryLimit) {
        auto entry = storage->entries.begin();
        projected -= entryBytes + Word(entry->second.values.capacity()) * sizeof(Word);
        storage->entries.erase(entry);
      }
      if (storage->entries.empty()) decltype(storage->entries)().swap(storage->entries);
    }
    const Word projected = projectedBytes();
    if (projected > memoryLimit) return reject(Rejection::Memory);
    log.simulation.estimated_peak_bytes = std::max(log.simulation.estimated_peak_bytes, projected);
    if (cfg.expired()) return interrupt();
    // Precompute the part of the input partition unaffected by cut outputs.
    // Feedback inputs are intersected below after simulating each tuple.
    std::vector<Word> rows(size_t(nRows) * nWords, ~Word(0));
    for (unsigned r = 0; r < nRows; ++r) {
      if (!(r & 7) && cfg.expired()) return interrupt();
      for (unsigned j = 0; j < nInputs; ++j) {
        if ((feedback_mask >> j) & 1)
          continue;
        const Word* input = &reference[size_t(subcir.inputs[j]) * nWords];
        const Word polarity = (r >> j) & 1 ? Word(0) : ~Word(0);
        for (unsigned w = 0; w < nWords; ++w)
          rows[size_t(r) * nWords + w] &= input[w] ^ polarity;
      }
    }
    if (cfg.expired()) return interrupt();
    std::vector<Word> changed(reference), difference(nWords), forbidden(nRows, 0);
    const bool gray = cfg.fast_simulation;
    std::vector<std::vector<int>> affected_by_output;
    auto tableStorage = [&]() -> Word {
      Word allocated = Word(rows.capacity() + changed.capacity() + difference.capacity() + forbidden.capacity()) * sizeof(Word);
      allocated += Word(affected_by_output.capacity()) * sizeof(std::vector<int>);
      for (const auto& cone : affected_by_output) allocated += Word(cone.capacity()) * sizeof(int);
      return allocated;
    };
    observeStorage(tableStorage());
    if (gray) {
      affected_by_output.resize(nOutputs);
      std::vector<unsigned> depends(nNodes, 0);
      for (unsigned j = 0; j < nOutputs; ++j)
        depends[subcir.outputs[j]] = 1u << j;
      for (int i : affected) {
        if (!(i & 255) && cfg.expired()) {
          observeStorage(tableStorage() + Word(depends.capacity()) * sizeof(unsigned));
          return interrupt();
        }
        const auto& obj = cir.getObj(i);
        for (auto* input : obj.fanins) depends[i] |= depends[input->node_id];
        for (unsigned j = 0; j < nOutputs; ++j)
          if (depends[i] & (1u << j))
            affected_by_output[j].push_back(i);
      }
      observeStorage(tableStorage() + Word(depends.capacity()) * sizeof(unsigned));
    }
    // Consecutive Gray-code tuples change one cut output. After the first
    // tuple, only its affected cone needs reevaluation; other values remain valid.
    unsigned previous_tuple = 0;
    for (unsigned ordinal = 0; ordinal < nTuples; ++ordinal) {
      const unsigned tuple = gray ? ordinal ^ (ordinal >> 1) : ordinal;
      const unsigned changed_pin = ordinal && gray ? unsigned(lsb(tuple ^ previous_tuple)) : 0;
      previous_tuple = tuple;
      if (cfg.expired()) return interrupt();
      for (unsigned j = 0; j < nOutputs; ++j) {
        if (gray && ordinal && j != changed_pin)
          continue;
        Word* output = &changed[size_t(subcir.outputs[j]) * nWords];
        std::fill(output, output + nWords, (tuple >> j) & 1 ? ~Word(0) : Word(0));
      }
      const auto& to_evaluate = gray && ordinal ? affected_by_output[changed_pin] : affected;
      unsigned polled = 0;
      for (int i : to_evaluate) {
        if (!(polled++ & 31) && cfg.expired()) return interrupt();
        evaluate(changed, i);
      }
      std::fill(difference.begin(), difference.end(), Word(0));
      for (int i : compared) {
        if (!(polled++ & 31) && cfg.expired()) return interrupt();
        for (unsigned w = 0; w < nWords; ++w)
          difference[w] |= changed[size_t(i) * nWords + w] ^ reference[size_t(i) * nWords + w];
      }
      for (unsigned r = 0; r < nRows; ++r) {
        if (!(r & 7) && cfg.expired()) return interrupt();
        for (unsigned w = 0; w < nWords; ++w) {
          Word mismatches = rows[size_t(r) * nWords + w] & difference[w];
          for (unsigned j : feedback_inputs) {
            const Word polarity = (r >> j) & 1 ? Word(0) : ~Word(0);
            mismatches &= changed[size_t(subcir.inputs[j]) * nWords + w] ^ polarity;
          }
          if (mismatches) {
            forbidden[r] |= Word(1) << tuple;
            break;
          }
        }
      }
    }
    // Owned capacities are measured separately from the conservative admission
    // estimate. The cache includes its dense reference vector, counted once.
    observeStorage(tableStorage());
    // Cover forbidden tuples with cubes. Dropping a literal is legal only if
    // every tuple in the enlarged cube is forbidden, so the relation is exact.
    for (unsigned r = 0; r < nRows; ++r) {
      if (!(r & 15) && cfg.expired()) return interrupt();
      Word uncovered = forbidden[r];
      while (uncovered) {
        const unsigned tuple = lsb(uncovered);
        Word cube = Word(1) << tuple;
        unsigned care = nTuples - 1;
        for (unsigned j = 0; j < nOutputs; ++j) {
          const unsigned shift = 1u << j;
          Word expanded = cube | ((cube & ~truth_patterns[j]) << shift) | ((cube & truth_patterns[j]) >> shift);
          if (!(expanded & ~forbidden[r])) {
            cube = expanded;
            care &= ~(1u << j);
          }
        }
        std::vector<bool> pattern(2 * nOutputs, false);
        for (unsigned j = 0; j < nOutputs; ++j) {
          pattern[2*j] = (care >> j) & 1;
          pattern[2*j + 1] = !((tuple >> j) & 1);
        }
        rel.addOutputPattern(r, std::move(pattern));
        uncovered &= ~cube;
      }
    }
    Word relationBytes = Word(rel.output_patterns.capacity()) * sizeof(std::vector<std::vector<bool>>);
    for (const auto& row : rel.output_patterns) {
      relationBytes += Word(row.capacity()) * sizeof(std::vector<bool>);
      for (const auto& cube : row) relationBytes += (cube.capacity() + 7) / 8 + 2 * sizeof(void*);
    }
    log.simulation.relation_peak_bytes = std::max(log.simulation.relation_peak_bytes, relationBytes);
    if (cfg.expired()) return interrupt();
    ++log.simulation.complete;
    return Status::Complete;
  }

}
ABC_NAMESPACE_IMPL_END
