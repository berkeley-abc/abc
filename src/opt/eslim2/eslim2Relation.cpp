/**CFile****************************************************************

  FileName    [eslim2Relation.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [SAT-based computation of Boolean relations.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eslim2Relation.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <cassert>
#include <algorithm>

#include "misc/util/abc_global.h"

#include "relationGeneration.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {

  static const ABC_UINT64_T s_SimulationPatterns[6] = {
    ABC_CONST(0xaaaaaaaaaaaaaaaa), ABC_CONST(0xcccccccccccccccc),
    ABC_CONST(0xf0f0f0f0f0f0f0f0), ABC_CONST(0xff00ff00ff00ff00),
    ABC_CONST(0xffff0000ffff0000), ABC_CONST(0xffffffff00000000)
  };

  ABC_UINT64_T Relation::getForbiddenTuples(unsigned row, unsigned noutputs) const {
    assert(noutputs <= 6);
    ABC_UINT64_T forbidden = 0;
    for (const auto& pattern : output_patterns[row]) {
      ABC_UINT64_T cube = noutputs == 6 ? ~ABC_UINT64_T(0) : (ABC_UINT64_T(1) << (1u << noutputs)) - 1;
      for (unsigned j = 0; j < noutputs; ++j)
        if (pattern[2*j])
          cube &= pattern[2*j + 1] ? ~s_SimulationPatterns[j] : s_SimulationPatterns[j];
      forbidden |= cube;
    }
    return forbidden;
  }

  Relation::Relation(int nfanins) : output_patterns(1 << nfanins) {

  }

  void Relation::addOutputPattern(int inputidx, std::vector<bool>&& pattern) {
    lines_with_pattern += output_patterns[inputidx].empty();
    output_patterns[inputidx].push_back(std::move(pattern));
  }

  RelationGenerator::RelationGenerator( const eSLIM2CirMan& cir, const Subcircuit& subcir,
                                        const eSLIM2Config& cfg, eSLIM2Log& log)
                    : cir(cir), subcir(subcir), cfg(cfg), log(log),
                      gate2varref(cir.getNofObjs() - cir.getNofPos()),
                      gate2varcone(cir.getNofObjs() - cir.getNofPos()) {
    solver.setDeadline(cfg.deadline);
    // Lucky phases are costly for the repeated incremental relation queries.
    // Configure only this solver; exact synthesis keeps its solver defaults.
    if (cfg.tune_relation_solver) {
      const bool configured = solver.setOption("lucky", 0);
      if (!configured)
        std::cerr << "eSLIM2: cannot disable CaDiCaL lucky phases; using solver defaults.\n";
      assert(configured);
    }
    setupEncoding();
  }

/**Function*************************************************************

  Synopsis    [Computes a cut relation by exhaustive simulation or a SAT encoding.]

***********************************************************************/
  Relation RelationGenerator::computeRelation(const eSLIM2CirMan& cir, const Subcircuit& subcir,
                                              const eSLIM2Config& cfg, eSLIM2Log& log) {
    Relation simulated(subcir.inputs.size());
    if (simulateRelation(cir, subcir, cfg, simulated)) {
      log.nof_simulated_relations++;
      return simulated;
    }
    log.nof_sat_relations++;
    RelationGenerator rgen(cir, subcir, cfg, log);
    return rgen.getRelation();
  }


  // Simulate every primary-input assignment and every value at the cut outputs.
  // With no feedback to cut inputs, an output tuple is forbidden for a cut-input
  // row exactly when some primary-input assignment makes a primary output differ.
/**Function*************************************************************

  Synopsis    [Simulates cut-output tuples using bounded storage and a content-validated cache.]

***********************************************************************/
  bool RelationGenerator::simulateRelation(const eSLIM2CirMan& cir, const Subcircuit& subcir,
                                           const eSLIM2Config& cfg, Relation& rel) {
    typedef ABC_UINT64_T Word;
    const unsigned nPis = cir.getNofPis();
    const unsigned nInputs = subcir.inputs.size();
    const unsigned nOutputs = subcir.outputs.size();
    if (cfg.approximate_relation || !subcir.forbidden_pairs.empty() ||
        nPis > 16 || nInputs > 10 || nOutputs == 0 || nOutputs > 6)
      return false;
    const unsigned nWords = 1u << (nPis > 6 ? nPis - 6 : 0);
    const unsigned nRows = 1u << nInputs;
    const unsigned nTuples = 1u << nOutputs;
    const unsigned nNodes = cir.getNofObjs() - cir.getNofPos();
    std::vector<int> affected, compared;
    for (unsigned i = nPis + 1; i < nNodes; ++i) {
      const auto& obj = cir.getObj(i);
      if (obj.getNFanins() != 2)
        return false;
      if (cir.inTFO(obj) && !cir.inSubcircuit(obj))
        affected.push_back(i);
    }
    for (int i = nNodes; i < cir.getNofObjs(); ++i)
      if (cir.inTFO(cir.getObj(i)))
        compared.push_back(cir.getObj(i).fanins[0]->node_id);
    // Bound simulation storage and work independently of circuit size. Include
    // the difference and forbidden-row vectors as well as the large tables.
    const ABC_UINT64_T memoryLimit = 1u << 22; // 32 MiB, in 64-bit words
    const ABC_UINT64_T tableWords = (2ull * nNodes + nRows + 1) * nWords + nRows;
    if (tableWords > memoryLimit ||
        (nNodes + 1ull * nRows * nInputs +
         1ull * nTuples * (affected.size() + compared.size() + nRows)) * nWords > (1u << 26))
      return false;
    const Word* patterns = s_SimulationPatterns;
    if (cir.simulation_cache && cir.simulation_cache->words != nWords)
      cir.simulation_cache.reset();
    // Count cached vectors, retained reference capacity, and metadata against
    // the same allowance. A cut that cannot populate a full cache can still
    // use fast simulation and retain existing entries for later, smaller cuts.
    bool persistent = cfg.fast_simulation && nWords >= 64;
    if (persistent) {
      const auto* previous = cir.simulation_cache.get();
      const ABC_UINT64_T gates = nNodes - nPis - 1;
      const ABC_UINT64_T referenceWords = ABC_UINT64_T(nNodes) * nWords;
      const ABC_UINT64_T retainedReference = previous ? std::max(referenceWords, ABC_UINT64_T(previous->reference.capacity())) : referenceWords;
      const ABC_UINT64_T retainedVersions = previous ? std::max(ABC_UINT64_T(nNodes), ABC_UINT64_T(previous->versions.capacity())) : nNodes;
      const ABC_UINT64_T buckets = previous ? std::max(2 * (gates + 1), ABC_UINT64_T(previous->entries.bucket_count())) : 2 * (gates + 1);
      const ABC_UINT64_T entryBytes = sizeof(eSLIM2CirMan::SimulationEntry) + sizeof(unsigned) + 3 * sizeof(void*);
      const ABC_UINT64_T metadataWords = (gates * entryBytes + buckets * sizeof(void*) + sizeof(Word) - 1) / sizeof(Word);
      persistent = tableWords + gates * nWords + retainedReference - referenceWords +
                   nNodes + retainedVersions + metadataWords <= memoryLimit;
    }
    if (persistent && !cir.simulation_cache)
      cir.simulation_cache = std::make_unique<eSLIM2CirMan::SimulationCache>();
    auto* storage = cir.simulation_cache.get();
    auto* cache = persistent ? storage : nullptr;
    std::vector<Word> temporary_reference;
    std::vector<Word>& reference = storage ? storage->reference : temporary_reference;
    if (storage) {
      storage->words = nWords;
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
        std::vector<Word>(size_t(nNodes) * nWords, 0).swap(reference);
        storage->versions.clear();
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
        const ABC_UINT64_T entryWords = (sizeof(eSLIM2CirMan::SimulationEntry) + sizeof(unsigned) +
                                       3 * sizeof(void*) + sizeof(Word) - 1) / sizeof(Word);
        ABC_UINT64_T retainedWords = (storage->entries.bucket_count() * sizeof(void*) + sizeof(Word) - 1) / sizeof(Word);
        for (const auto& entry : storage->entries)
          retainedWords += entryWords + entry.second.values.capacity();
        // Keeping all entries can itself exceed the allowance on a large cut.
        // Evict only enough rows to fit, preserving the other value versions.
        while (!storage->entries.empty() && tableWords + retainedWords > memoryLimit) {
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
    for (unsigned i = 0; i < nPis; ++i)
      for (unsigned w = 0; w < nWords; ++w)
        reference[size_t(i + 1) * nWords + w] = i < 6 ? patterns[i] :
            ((w >> (i - 6)) & 1 ? ~Word(0) : Word(0));
    auto evaluate = [nWords, &cir, &cfg](std::vector<Word>& values, int i) {
      const auto& obj = cir.getObj(i);
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
      if (cache->versions.capacity() < nNodes)
        std::vector<Word>(nNodes, 0).swap(cache->versions);
      else
        cache->versions.resize(nNodes, 0);
      for (unsigned i = nPis + 1; i < nNodes; ++i) {
        const auto& obj = cir.getObj(i);
        auto& entry = cache->entries[obj.getId()];
        const Word first = versions[obj.fanins[0]->node_id];
        const Word second = versions[obj.fanins[1]->node_id];
        const auto begin = reference.begin() + size_t(i) * nWords;
        if (entry.version && entry.first == first && entry.second == second && entry.truth == obj.tt) {
          if (cache->versions[i] != entry.version)
            std::copy(entry.values.begin(), entry.values.end(), begin);
        } else {
          evaluate(reference, i);
          entry.first = first;
          entry.second = second;
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
    } else {
      for (unsigned i = nPis + 1; i < nNodes; ++i)
        evaluate(reference, i);
    }
    // Partition primary-input assignments by their values at the cut inputs.
    std::vector<Word> rows(size_t(nRows) * nWords, ~Word(0));
    for (unsigned r = 0; r < nRows; ++r)
      for (unsigned j = 0; j < nInputs; ++j) {
        const Word* input = &reference[size_t(subcir.inputs[j]) * nWords];
        const Word polarity = (r >> j) & 1 ? Word(0) : ~Word(0);
        for (unsigned w = 0; w < nWords; ++w)
          rows[size_t(r) * nWords + w] &= input[w] ^ polarity;
      }
    std::vector<Word> changed(reference), difference(nWords), forbidden(nRows, 0);
    const bool gray = cfg.fast_simulation;
    std::vector<std::vector<int>> affected_by_output;
    if (gray) {
      affected_by_output.resize(nOutputs);
      std::vector<unsigned> depends(nNodes, 0);
      for (unsigned j = 0; j < nOutputs; ++j)
        depends[subcir.outputs[j]] = 1u << j;
      for (int i : affected) {
        const auto& obj = cir.getObj(i);
        depends[i] = depends[obj.fanins[0]->node_id] | depends[obj.fanins[1]->node_id];
        for (unsigned j = 0; j < nOutputs; ++j)
          if (depends[i] & (1u << j))
            affected_by_output[j].push_back(i);
      }
    }
    // Consecutive Gray-code tuples change one cut output. After the first
    // tuple, only its affected cone needs reevaluation; other values remain valid.
    unsigned previous_tuple = 0;
    for (unsigned ordinal = 0; ordinal < nTuples; ++ordinal) {
      const unsigned tuple = gray ? ordinal ^ (ordinal >> 1) : ordinal;
      const unsigned changed_pin = ordinal && gray ? unsigned(lsb(tuple ^ previous_tuple)) : 0;
      previous_tuple = tuple;
      if (cfg.expired()) {
        rel.status = false;
        return true;
      }
      for (unsigned j = 0; j < nOutputs; ++j) {
        if (gray && ordinal && j != changed_pin)
          continue;
        Word* output = &changed[size_t(subcir.outputs[j]) * nWords];
        std::fill(output, output + nWords, (tuple >> j) & 1 ? ~Word(0) : Word(0));
      }
      const auto& to_evaluate = gray && ordinal ? affected_by_output[changed_pin] : affected;
      for (int i : to_evaluate)
        evaluate(changed, i);
      std::fill(difference.begin(), difference.end(), Word(0));
      for (int i : compared)
        for (unsigned w = 0; w < nWords; ++w)
          difference[w] |= changed[size_t(i) * nWords + w] ^ reference[size_t(i) * nWords + w];
      for (unsigned r = 0; r < nRows; ++r)
        for (unsigned w = 0; w < nWords; ++w)
          if (rows[size_t(r) * nWords + w] & difference[w]) {
            forbidden[r] |= Word(1) << tuple;
            break;
          }
    }
    // Cover forbidden tuples with cubes. Dropping a literal is legal only if
    // every tuple in the enlarged cube is forbidden, so the relation is exact.
    for (unsigned r = 0; r < nRows; ++r) {
      Word uncovered = forbidden[r];
      while (uncovered) {
        const unsigned tuple = lsb(uncovered);
        Word cube = Word(1) << tuple;
        unsigned care = nTuples - 1;
        for (unsigned j = 0; j < nOutputs; ++j) {
          const unsigned shift = 1u << j;
          Word expanded = cube | ((cube & ~patterns[j]) << shift) | ((cube & patterns[j]) >> shift);
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
    return true;
  }

  int RelationGenerator::getNewVar() {
    return max_var++;
  }

  void RelationGenerator::setupEncoding() {
    if (cfg.approximate_relation) {
      if (cfg.generate_relation_with_tfi_limit) {
        encodeCircuitApproximativeBoundedTFI();
      } else {
        encodeCircuitApproximative();
      }
    } else {
      // encodeCircuitFull();
      encodeCircuitAffected();
    }
  }

  void RelationGenerator::encodeGate(const eSLIM2CirObj& obj, int var, const std::vector<int>& gate2var) {
    int bc = popcount(obj.tt);
    int tt_length = obj.getTTLength();
    if (bc == 0) {
      solver.addClause({-var});
    } else if (bc == tt_length) {
      solver.addClause({var});
    } else if (bc == 1) {
      return getGateEncodingUnique(obj, var, gate2var, true);
    } else if (bc == tt_length - 1) {
      return getGateEncodingUnique(obj, var, gate2var, false);
    } else {
      return getGateEncodingNaive(obj, var, gate2var);
    }
  }

  void RelationGenerator::getGateEncodingUnique(const eSLIM2CirObj& obj, int var, const std::vector<int>& gate2var, bool unique_bit) {
    ABC_UINT64_T tt = obj.tt;
    if (!unique_bit) {
      tt = eSLIM2CirMan::negateTT(tt, obj.getNFanins());
    }
    int bit_index = lsb(tt);
    std::vector<int> clause;
    int lit = unique_bit ? -var : var;
    for (int i = 0; i < obj.getNFanins(); i++) {
      if ((bit_index >> i) & 1 ) {
        clause.push_back(-gate2var[obj.fanins[i]->node_id]);
        solver.addClause({gate2var[obj.fanins[i]->node_id], lit});
      } else {
        clause.push_back(gate2var[obj.fanins[i]->node_id]);
        solver.addClause({-gate2var[obj.fanins[i]->node_id], lit});
      }
    }
    clause.push_back(-lit);
    solver.addClause(clause);
  }

  void RelationGenerator::getGateEncodingNaive(const eSLIM2CirObj& obj, int var, const std::vector<int>& gate2var) {
    int tt_length = obj.getTTLength();
    int nfans = obj.getNFanins();
    std::vector<int> clause;
    clause.reserve(nfans+1);
    for (int i = 0; i < tt_length; i++) {
      clause.clear();
      for (int j = 0; j < nfans; j++) {
        if ((i >> j) & 1 ) {
          clause.push_back(-gate2var[obj.fanins[j]->node_id]);
        } else {
          clause.push_back(gate2var[obj.fanins[j]->node_id]);
        }
      }
      bool polarity = (obj.tt >> i) & 1;
      if (polarity) {
        clause.push_back(var);
      } else {
        clause.push_back(-var);
      }
      solver.addClause(clause);
    }
  }


/**Function*************************************************************

  Synopsis    [Encodes the reference circuit and the affected transitive fanout cone.]

***********************************************************************/
  void RelationGenerator::encodeCircuitAffected() {
    setupConstantGate();
    std::vector<int> compare_nodes;
    for (int i = cir.getNofObjs() - cir.getNofPos(); i < cir.getNofObjs(); i++) {
      const auto& obj = cir.getObj(i);
      int fid = obj.fanins[0]->node_id;
      // multiple POs can use the same fanin
      // if gate2varref[fid] is not 0 we have already seen it
      if (cir.inTFO(obj) && !gate2varref[fid]) {
        gate2varref[fid] = getNewVar();
        gate2varcone[fid] = getNewVar();
        compare_nodes.push_back(fid);
      }
    }
    setupEqualityConstraints(compare_nodes);

    for (int i = cir.getNofObjs() - cir.getNofPos() - 1; i > cir.getNofPis(); i--) {
      if (gate2varref[i]) { // the gate is connected to a PO that is in the TFO of the subcircuit
        const auto& obj = cir.getObj(i);
        for (const auto& f : obj.fanins) {
          int fid = f->node_id;
          if (gate2varref[fid] == 0) {
            gate2varref[fid] = getNewVar();
          }
        }
        encodeGate(obj, gate2varref[i], gate2varref);

        if (cir.inTFO(obj) && !cir.inSubcircuit(obj)) {
          // For an input in a forbidden pair no successors needs to be processed before
          gate2varcone[i] = gate2varcone[i] ? gate2varcone[i] : getNewVar();
          for (const auto& f : obj.fanins) {
            int fid = f->node_id;
            if (cir.inSubcircuit(*f) || cir.inTFO(*f)) {
              if (gate2varcone[fid] == 0) {
                gate2varcone[fid] = getNewVar();
              }
            } else {
              gate2varcone[fid] = gate2varref[fid];
            }
          }
          encodeGate(obj, gate2varcone[i], gate2varcone);
        } else if (gate2varcone[i] == 0) {
          gate2varcone[i] = gate2varref[i];
        }
      }
    }

    for (int i = 1; i <= cir.getNofPis(); i++) {
      if (gate2varref[i] != 0) {
        cone_input_variables.push_back(gate2varref[i]);
        // Simplifies handling of variables
        if (gate2varcone[i] == 0) {
          gate2varcone[i] = gate2varref[i];
        }
      }
    }
  }


  void RelationGenerator::encodeCircuitApproximative() {
    setupConstantGate();
    std::vector<int> compare_nodes = markRestrictedCone();
    int max_node = *std::max_element(compare_nodes.begin(), compare_nodes.end());
    for (int i = max_node; i > cir.getNofPis(); i--) {
      const auto& obj = cir.getObj(i);
      if (gate2varref[i] != 0) {
        for (auto& f : obj.fanins ) {
          if (gate2varref[f->node_id] == 0) {
            gate2varref[f->node_id] = getNewVar();
            gate2varcone[f->node_id] = gate2varref[f->node_id];
          }
        }
        encodeGate(obj, gate2varref[i], gate2varref);
        if (!cir.inSubcircuit(obj) && gate2varcone[i] != gate2varref[i]) {
          encodeGate(obj, gate2varcone[i], gate2varcone);
        }
      }
    }
    for (int i = 1; i <= cir.getNofPis(); i++) {
      if (gate2varref[i] != 0) {
        cone_input_variables.push_back(gate2varref[i]);
      }
    }
    setupEqualityConstraints(compare_nodes);
  }

/**Function*************************************************************

  Synopsis    [Encodes a restricted context with bounded transitive fanin.]

***********************************************************************/
  void RelationGenerator::encodeCircuitApproximativeBoundedTFI() {
    setupConstantGate();
    std::vector<int> compare_nodes = markRestrictedCone();
    std::vector<unsigned char> counts(cir.getNofObjs() - cir.getNofPos());
    int max_node = *std::max_element(compare_nodes.begin(), compare_nodes.end());
    for (int i = max_node; i > cir.getNofPis(); i--) {
      const auto& obj = cir.getObj(i);
      if (gate2varref[i] != 0) {
        if (cir.inTFO(obj) || cir.inSubcircuit(obj)) {
          counts[i] = cfg.relation_tfi_bound + 1;
        } else if (counts[i] == 0) {
          cone_input_variables.push_back(gate2varref[i]);
          continue;
        }
        for (auto& f : obj.fanins ) {
          if (gate2varref[f->node_id] == 0) {
            gate2varref[f->node_id] = getNewVar();
            gate2varcone[f->node_id] = gate2varref[f->node_id];
            counts[f->node_id] = std::max(counts[f->node_id], static_cast<unsigned char>(counts[i] - 1));
          }
        }
        encodeGate(obj, gate2varref[i], gate2varref);
        if (!cir.inSubcircuit(obj) && gate2varcone[i] != gate2varref[i]) {
          encodeGate(obj, gate2varcone[i], gate2varcone);
        }
      }
    }
    for (int i = 1; i <= cir.getNofPis(); i++) {
      if (gate2varref[i] != 0) {
        cone_input_variables.push_back(gate2varref[i]);
      }
    }
    setupEqualityConstraints(compare_nodes);
  }

  std::vector<int> RelationGenerator::markRestrictedCone() {
    std::vector<unsigned char> counts(cir.getNofObjs() - cir.getNofPos());
    for (int i : subcir.outputs) {
      gate2varref[i] = getNewVar();
      gate2varcone[i] = getNewVar();
      counts[i] = cfg.relation_tfo_bound;
    }
    if (cfg.relation_tfo_bound == 0) {
      std::vector<int> nodes(subcir.outputs.begin(), subcir.outputs.end());
      return nodes;
    }
    std::vector<int> nodes;
    for (int i = subcir.outputs[0] + 1; i < cir.getNofObjs() - cir.getNofPos(); i++) { //outputs are ordered
      const auto& obj = cir.getObj(i);
      if (!cir.inTFO(obj) || cir.inSubcircuit(obj)) {
        continue;
      }
      unsigned char x = 0;
      for (auto& f : obj.fanins) {
        x = std::max(x, counts[f->node_id]);
      }
      if (x > 0) {
        gate2varcone[i] = getNewVar();
        gate2varref[i] = getNewVar();
        counts[i] = x - 1;
        if (x == 1) {
          nodes.push_back(i);
        }
      }
    }
    std::set<int> used;
    for (int i = cir.getNofObjs() - cir.getNofPos(); i < cir.getNofObjs(); i++) {
      const auto& obj = cir.getObj(i);
      if (cir.inTFO(obj) && counts[obj.fanins[0]->node_id] > 0 && used.find(obj.fanins[0]->node_id) == used.end()) {
        nodes.push_back(obj.fanins[0]->node_id);
        used.insert(obj.fanins[0]->node_id);
      }
    }
    return nodes;
  }

  void RelationGenerator::setupConstantGate() {
    int const_var = getNewVar();
    gate2varref[0] = const_var;
    gate2varcone[0] = const_var;
    solver.addClause({-const_var});
  }

  void RelationGenerator::setupEqualityConstraints(const std::vector<int>& nodes) {
    mode_selection_variable = getNewVar();
    std::vector<int> one_different {-mode_selection_variable};
    for (int cnd : nodes) {
      int eq_var = getNewVar();
      equality_variables.push_back(eq_var);
      getEqualityClauses(gate2varref[cnd], gate2varcone[cnd], eq_var);
      one_different.push_back(-eq_var);
    }
    solver.addClause(one_different);
  }


  void RelationGenerator::getEqualityClauses(int x, int y, int aux) {
    solver.addClause({x, -y, -aux});
    solver.addClause({-x, y, -aux});
    solver.addClause({x, y, aux});
    solver.addClause({-x, -y, aux});
  }

  int RelationGenerator::findConflict(double& timeout, int mode_selection) {
    abctime time_start = cfg.timeNow();
    int solver_status = solver.solve(timeout, {mode_selection});
    double solver_time = (double)1.0*(cfg.timeNow() - time_start)/CLOCKS_PER_SEC;
    log.cummulative_sat_runtime_relation_generation += solver_time;
    log.max_sat_runtime_relation_generation = std::max(log.max_sat_runtime_relation_generation, solver_time);
    // log.cummulative_sat_runtime_relation_generation += solver.getRunTime();
    log.nof_sat_calls_relation_generation++;
    return solver_status;
  }

  int RelationGenerator::reduceConflict(double& timeout, const std::vector<int>& cone_input,
                                        const std::vector<int>& subcircuit_output, const std::vector<int>& equality) {
    solver.assume(cone_input);
    solver.assume(subcircuit_output);
    solver.assume(equality);
    abctime time_start = cfg.timeNow();
    int status = solver.solve(timeout);
    double solver_time = (double)1.0*(cfg.timeNow() - time_start)/CLOCKS_PER_SEC;
    log.cummulative_sat_runtime_relation_generation += solver_time;
    log.max_sat_runtime_relation_generation = std::max(log.max_sat_runtime_relation_generation, solver_time);
    // log.cummulative_sat_runtime_relation_generation += solver.getRunTime();
    log.nof_sat_calls_relation_generation++;
    return status;
  }

  Relation RelationGenerator::getRelation() {
    std::vector<int> subcircuit_input_variables;
    subcircuit_input_variables.reserve(subcir.inputs.size());
    for (int sin : subcir.inputs) {
      int var = gate2varcone[sin];
      subcircuit_input_variables.push_back(var);
    }
    std::vector<int> subcircuit_output_variables;
    subcircuit_output_variables.reserve(subcir.outputs.size());
    // outputs in forbidden pairs must not removed
    std::vector<bool> outputs_to_keep(subcir.outputs.size(), false);
    for (int i = 0; i < subcir.outputs.size(); i++) {
      int sout = subcir.outputs[i];
      int var = gate2varcone[sout];
      subcircuit_output_variables.push_back(var);
      if (subcir.forbidden_pairs.find(sout) != subcir.forbidden_pairs.end()) {
        outputs_to_keep[i] = true;
      }
    }

    Relation rel(subcir.inputs.size());

    int solver_status;
    double timeout = cfg.relation_generation_timeout;
    abctime time_start = cfg.timeNow();
    while( (solver_status=findConflict(timeout, mode_selection_variable)) == 10) {
      timeout -= (double)1.0*(cfg.timeNow() - time_start)/CLOCKS_PER_SEC;
      time_start = cfg.timeNow();
      if (timeout <= 0) {
        rel.status = false;
        return rel;
      }
      std::vector<int> cone_in_assm = solver.getValues(cone_input_variables);
      std::vector<int> sin_assm = solver.getValues(subcircuit_input_variables);
      std::vector<int> sout_assm = solver.getValues(subcircuit_output_variables);
      int status = reduceConflict(timeout, cone_in_assm, sout_assm, equality_variables);
      if (status != 20) {
        assert (status != 10);
        rel.status = false;
        return rel;
      }
      assert (status == 20);
      std::vector<int> blocking_clause {-mode_selection_variable};
      for (int i = 0; i < subcir.inputs.size(); i++) {
        blocking_clause.push_back(-sin_assm[i]);
      }
      std::vector<bool> pattern (2*subcir.outputs.size(), false);
      for (int i = 0; i < subcir.outputs.size(); i++) {
        if (solver.isFailed(sout_assm[i]) || outputs_to_keep[i]) {
          pattern[2*i] = true;
          pattern[2*i + 1] = sout_assm[i] < 0; // at least one output must be assigned differently in order to preserve the function
          blocking_clause.push_back(-sout_assm[i]);
        }
      }
      solver.addClause(blocking_clause);
      rel.addOutputPattern(assignment2bvindex(sin_assm), std::move(pattern));
    }
    if (solver_status != 20) {
      rel.status = false;
    }
    return rel;
  }

  int RelationGenerator::assignment2bvindex(const std::vector<int>& assm) {
    int idx = 0;
    for (int i = 0; i < assm.size(); i++) {
      if (assm[i] > 0) {
        idx |= 1 << i;
      }
    }
    return idx;
  }

}
ABC_NAMESPACE_IMPL_END
