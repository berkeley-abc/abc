/**CFile****************************************************************

  FileName    [eslim3Relation.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [SAT-based computation of Boolean relations.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#include <cassert>
#include <climits>
#include <algorithm>
#include <map>
#include <random>

#include "misc/util/abc_global.h"

#include "relationGeneration.h"


ABC_NAMESPACE_IMPL_START
namespace eSLIM3 {


/**Function*************************************************************

  Synopsis    [Simulates a two-input gate with one operation selected for all words.]

***********************************************************************/
  static inline void simulateTwoInputGate(unsigned function, const ABC_UINT64_T* a,
      const ABC_UINT64_T* b, ABC_UINT64_T* out, unsigned nWords) {
    switch (function & 15u) {
      case 0: for (unsigned w = 0; w < nWords; ++w) out[w] = ABC_UINT64_T(0); break;
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
      case 15: for (unsigned w = 0; w < nWords; ++w) out[w] = ~ABC_UINT64_T(0); break;
    }
  }

/**Function*************************************************************

  Synopsis    [Returns packed forbidden output tuples for one input assignment.]

***********************************************************************/
  ABC_UINT64_T Relation::getForbiddenTuples(unsigned row, unsigned noutputs) const {
    assert(noutputs <= 6);
    ABC_UINT64_T forbidden = 0;
    for (const auto& pattern : output_patterns[row]) {
      ABC_UINT64_T cube = noutputs == 6 ? ~ABC_UINT64_T(0) : (ABC_UINT64_T(1) << (1u << noutputs)) - 1;
      for (unsigned j = 0; j < noutputs; ++j)
        if (pattern[2*j])
          cube &= pattern[2*j + 1] ? ~truth_patterns[j] : truth_patterns[j];
      forbidden |= cube;
    }
    return forbidden;
  }

/**Function*************************************************************

  Synopsis    [Derives necessary supports and an implementation-independent gate bound.]

***********************************************************************/
  SupportBounds Relation::analyseSupport(unsigned noutputs, unsigned gate_size) const {
    SupportBounds bounds;
    unsigned ninputs = 0;
    while ((1u << ninputs) < unsigned(getNPatterns())) ++ninputs;
    if (noutputs <= 6 && gate_size > 1) {
      auto& forbidden = bounds.forbidden;
      for (int row = 0; row < getNPatterns(); ++row)
        forbidden.push_back(getForbiddenTuples(row, noutputs));
      const ABC_UINT64_T all = noutputs == 6 ? ~ABC_UINT64_T(0) : (ABC_UINT64_T(1) << (1u << noutputs)) - 1;
      // Project the allowed tuples only to derive necessary conditions. The
      // synthesis encoding still enforces the entire correlated relation.
      std::vector<unsigned> forced_zero(forbidden.size(), 0), forced_one(forbidden.size(), 0);
      bounds.output_inputs.resize(noutputs);
      for (unsigned row = 0; row < forbidden.size(); ++row) {
        const ABC_UINT64_T allowed = all & ~forbidden[row];
        for (unsigned output = 0; output < noutputs; ++output) {
          if (!(allowed & truth_patterns[output]))
            forced_zero[row] |= 1u << output;
          if (!(allowed & ~truth_patterns[output]))
            forced_one[row] |= 1u << output;
        }
      }
      for (unsigned j = 0; j < unsigned(ninputs); ++j) {
        bool mandatory = false;
        unsigned dependent_outputs = 0;
        for (unsigned row = 0; row < forbidden.size(); ++row)
          if (!(row & (1u << j))) {
            const unsigned other = row | (1u << j);
            // Disjoint allowed output tuples force input j into the support
            // of every implementation of this relation.
            mandatory |= (forbidden[row] | forbidden[other]) == all;
            dependent_outputs |= (forced_zero[row] & forced_one[other]) |
                                 (forced_one[row] & forced_zero[other]);
          }
        if (mandatory)
          bounds.inputs.push_back(j);
        for (unsigned output = 0; output < noutputs; ++output)
          if ((dependent_outputs >> output) & 1)
            bounds.output_inputs[output].push_back(j);
      }
      // A circuit with M K-input gates and O outputs can depend on at most
      // M*(K-1)+O distinct inputs, counting direct PI-to-PO connections too.
      if (bounds.inputs.size() > noutputs)
        bounds.minimum_gates = (bounds.inputs.size() - noutputs + gate_size - 2) / (gate_size - 1);
      // Independently, an output whose support MUST contain I inputs needs
      // at least ceil((I-1)/(K-1)) gates in its cone. Taking the maximum avoids
      // double-counting gates shared by multiple outputs.
      for (const auto& inputs : bounds.output_inputs) {
        const unsigned support = inputs.size();
        if (support > 1)
          bounds.minimum_gates = std::max(bounds.minimum_gates, (support + gate_size - 3) / (gate_size - 1));
      }
    }
    return bounds;
  }

/**Function*************************************************************

  Synopsis    [Bounds output arrival using an optimal binary tree of mandatory inputs.]

  Description [Unfolding any binary DAG into a tree cannot remove a mandatory
  input. Repeatedly joining the two earliest inputs gives a lower bound on
  the root arrival of every such tree, irrespective of its Boolean function.]

***********************************************************************/
  unsigned SupportBounds::minimumArrival(unsigned output, const std::vector<unsigned>& arrivals) const {
    std::vector<unsigned> times;
    for (unsigned input : output_inputs[output]) times.push_back(arrivals[input]);
    if (times.empty()) return 0;
    while (times.size() > 1) {
      std::sort(times.begin(), times.end());
      const unsigned joined = 1 + times[1];
      times.erase(times.begin(), times.begin() + 2);
      times.push_back(joined);
    }
    return times.front();
  }

/**Function*************************************************************

  Synopsis    [Allocates forbidden-pattern rows for every boundary-input assignment.]

***********************************************************************/
  Relation::Relation(int nfanins) : output_patterns(1 << nfanins) {

  }

/**Function*************************************************************

  Synopsis    [Adds a forbidden output pattern to the selected input row.]

***********************************************************************/
  void Relation::addOutputPattern(int inputidx, std::vector<bool>&& pattern) {
    lines_with_pattern += output_patterns[inputidx].empty();
    output_patterns[inputidx].push_back(std::move(pattern));
  }

/**Function*************************************************************

  Synopsis    [Initializes SAT relation extraction for the selected subcircuit.]

***********************************************************************/
  RelationGenerator::RelationGenerator( const eSLIM3CirMan& cir, const Subcircuit& subcir,
                                        const eSLIM3Config& cfg, eSLIM3Log& log)
                    : cir(cir), subcir(subcir), cfg(cfg), log(log),
                      gate2varref(cir.getNofObjs() - cir.getNofPos()),
                      gate2varcone(cir.getNofObjs() - cir.getNofPos()) {
    ScopedPhaseTimer encoding_timer(log.relation_encoding_time, cfg);
    const double allowance = std::max(0.0, std::min(cfg.relation_generation_timeout, double(INT_MAX)));
    const auto cutoff = std::chrono::steady_clock::now() +
        std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(allowance));
    solver.setDeadline(std::min(cfg.deadline, cutoff));
    // Repeated incremental relation queries favor propagation over internal
    // preprocessing and lucky phases. Configure only this solver; exact
    // synthesis retains its separately selected solver settings.
    if (cfg.tune_relation_solver) {
      const bool configured = solver.configure("plain") && solver.setOption("lucky", 0);
      if (!configured)
        std::cerr << "eSLIM3: cannot configure relation SAT tuning; using supported settings.\n";
      assert(configured);
    }
    setupEncoding();
    strengthenMiter();
  }

/**Function*************************************************************

  Synopsis    [Adds propagation clauses between corresponding miter gates.]

  Description [Equal fanins imply equal outputs. Also, an observed mismatch
  requires a changed cut output. These are consequences of the complete
  miter, not restrictions on its assignments. Reuse the exit indicators.]

***********************************************************************/
  void RelationGenerator::strengthenMiter() {
    if (cfg.approximate_relation) return;
    std::vector<int> same(gate2varref.size(), 0);
    for (unsigned i = 0; i < compared_nodes.size(); ++i)
      same[compared_nodes[i]] = equality_variables[i];
    for (unsigned id = 0; id < same.size(); ++id)
      if (!same[id] && gate2varref[id] && gate2varcone[id] && gate2varref[id] != gate2varcone[id]) {
        same[id] = getNewVar();
        getEqualityClauses(gate2varref[id], gate2varcone[id], same[id]);
      }
    std::vector<int> changed {-mode_selection_variable};
    for (int id : subcir.outputs)
      if (same[id]) changed.push_back(-same[id]);
    solver.addClause(changed);
    for (int id = cir.getNofPis() + 1; id < cir.getNofObjs() - cir.getNofPos(); ++id) {
      if (!same[id] || cir.inSubcircuit(cir.getObj(id))) continue;
      std::vector<int> clause {same[id]};
      for (const auto* fanin : cir.getObj(id).fanins) {
        const int f = fanin->node_id;
        assert(gate2varref[f] && gate2varcone[f]);
        if (same[f]) clause.push_back(-same[f]);
      }
      solver.addClause(clause);
    }
  }

/**Function*************************************************************

  Synopsis    [Prepares simulation of the affected cone at SAT witnesses.]

***********************************************************************/
  void RelationGenerator::prepareWitnessSimulation() {
    witness_simulation = !cfg.approximate_relation && subcir.outputs.size() <= 64;
    if (!witness_simulation) return;
    witness_support.assign(gate2varcone.size(), 0);
    for (unsigned i = 0; i < subcir.outputs.size(); ++i)
      witness_support[subcir.outputs[i]] = WitnessWord(1) << i;
    for (int id = cir.getNofPis() + 1; id < cir.getNofObjs() - cir.getNofPos(); ++id)
      if (gate2varcone[id] && cir.inTFO(cir.getObj(id)) && !cir.inSubcircuit(cir.getObj(id)))
        affected_nodes.push_back(id);
    if (subcir.outputs.size() >= 2 && subcir.outputs.size() <= 8 && subcir.inputs.size() <= 16)
      witness_values.resize(gate2varref.size());
  }

/**Function*************************************************************

  Synopsis    [Preserves cut outputs that determine a feedback input or divisor.]

  Description [Additional divisors need not have been present when the cut's
  forbidden-pair map was built. Keeping these outputs fixed ensures that a
  generalized conflict still belongs to the same cut-input row.]

***********************************************************************/
  void RelationGenerator::preserveFeedbackOutputs(std::vector<bool>& outputs_to_keep) const {
    std::vector<int> pending;
    for (int id : subcir.inputs)
      if (cir.inTFO(cir.getObj(id))) pending.push_back(id);
    if (pending.empty()) return;
    std::vector<int> output_index(cir.getNofObjs(), -1);
    std::vector<unsigned char> seen(cir.getNofObjs(), 0);
    for (unsigned i = 0; i < subcir.outputs.size(); ++i)
      output_index[subcir.outputs[i]] = int(i);
    while (!pending.empty()) {
      const int id = pending.back();
      pending.pop_back();
      if (seen[id]) continue;
      seen[id] = 1;
      if (output_index[id] >= 0) {
        outputs_to_keep[output_index[id]] = true;
        continue;
      }
      if (cir.inTFO(cir.getObj(id)))
        for (const auto* fanin : cir.getObj(id).fanins)
          pending.push_back(fanin->node_id);
    }
  }

/**Function*************************************************************

  Synopsis    [Justifies one mismatch using values from the SAT witness.]

  Description [Fix the context inputs to the witness. A controlling fanin
  suffices for an AND or OR; other gates keep all fanins. Thus fixing the
  returned cut outputs preserves an observed mismatch without a second SAT
  query. Wider or approximate relations retain the original core query.]

***********************************************************************/
  bool RelationGenerator::justifyConflict(WitnessWord& required_outputs) {
    if (!witness_simulation) return false;
    for (int id : affected_nodes) {
      const auto& obj = cir.getObj(id);
      WitnessWord needed = 0;
      for (const auto* fanin : obj.fanins)
        needed |= witness_support[fanin->node_id];
      if (obj.fanins.size() == 2) {
        const int x = obj.fanins[0]->node_id, y = obj.fanins[1]->node_id;
        const bool a = solver.getValue(gate2varcone[x]), b = solver.getValue(gate2varcone[y]);
        bool use_a = false, use_b = false;
        switch (unsigned(obj.tt) & 15u) {
          case 2: use_a = !a; use_b = b; break;
          case 4: use_a = a; use_b = !b; break;
          case 8: use_a = !a; use_b = !b; break;
          case 14: use_a = a; use_b = b; break;
        }
        if (use_a && (!use_b || popcount(witness_support[x]) <= popcount(witness_support[y])))
          needed = witness_support[x];
        else if (use_b)
          needed = witness_support[y];
      }
      witness_support[id] = needed;
    }
    bool found = false;
    for (int id : compared_nodes)
      if (solver.getValue(gate2varref[id]) != solver.getValue(gate2varcone[id]))
        if (!found || popcount(witness_support[id]) < popcount(required_outputs)) {
          required_outputs = witness_support[id];
          found = true;
        }
    return found;
  }

/**Function*************************************************************

  Synopsis    [Collects more conflicts at one SAT-provided context assignment.]

  Description [Simulate cut-output interventions at this one context witness,
  up to eight cut outputs in four machine words. Feedback inputs are read in
  the changed circuit. This only supplies witnessed conflicts; a final SAT
  UNSAT answer is still required to prove relation completeness.]

***********************************************************************/
  RelationGenerator::WitnessRows RelationGenerator::sampleConflict() {
    WitnessRows result;
    if (witness_values.empty()) return result;
    const unsigned nOutputs = subcir.outputs.size();
    const unsigned tuples = 1u << nOutputs, words = (tuples + 63) / 64;
    for (unsigned word = 0; word < words; ++word) {
      if (cfg.expired()) return result;
      for (unsigned id = 0; id < gate2varref.size(); ++id)
        witness_values[id] = gate2varref[id] && solver.getValue(gate2varref[id]) ? ~WitnessWord(0) : WitnessWord(0);
      for (unsigned i = 0; i < nOutputs; ++i)
        witness_values[subcir.outputs[i]] = i < 6 ? truth_patterns[i] :
            ((word >> (i - 6)) & 1 ? ~WitnessWord(0) : WitnessWord(0));
      for (int id : affected_nodes) {
        const auto& obj = cir.getObj(id);
        WitnessWord value = 0;
        if (obj.fanins.size() == 2 && cfg.fast_simulation) {
          const WitnessWord a = witness_values[obj.fanins[0]->node_id];
          const WitnessWord b = witness_values[obj.fanins[1]->node_id];
          simulateTwoInputGate(unsigned(obj.tt), &a, &b, &value, 1);
        } else {
          for (unsigned row = 0; row < (1u << obj.fanins.size()); ++row)
            if ((obj.tt >> row) & 1) {
              WitnessWord term = ~WitnessWord(0);
              for (unsigned pin = 0; pin < obj.fanins.size(); ++pin)
                term &= (row >> pin) & 1 ? witness_values[obj.fanins[pin]->node_id] : ~witness_values[obj.fanins[pin]->node_id];
              value |= term;
            }
        }
        witness_values[id] = value;
      }
      WitnessWord mismatches = 0;
      for (int id : compared_nodes)
        mismatches |= witness_values[id] ^ (solver.getValue(gate2varref[id]) ? ~WitnessWord(0) : WitnessWord(0));
      if (nOutputs < 6) mismatches &= (WitnessWord(1) << tuples) - 1;
      while (mismatches) {
        const unsigned bit = lsb(mismatches);
        unsigned row = 0;
        mismatches &= mismatches - 1;
        for (unsigned i = 0; i < subcir.inputs.size(); ++i)
          row |= unsigned((witness_values[subcir.inputs[i]] >> bit) & 1) << i;
        auto it = std::find_if(result.begin(), result.end(), [row](const WitnessRow& entry) { return entry.first == row; });
        if (it == result.end()) {
          result.emplace_back(row, std::vector<WitnessWord>(words, 0));
          it = result.end() - 1;
        }
        it->second[word] |= WitnessWord(1) << bit;
      }
    }
    return result;
  }

/**Function*************************************************************

  Synopsis    [Covers witnessed tuples with cubes and blocks them in SAT.]

  Description [A cube can grow only within the union of already known and
  newly witnessed conflicts in the same boundary-input row. These clauses
  are guarded by the mismatch mode and do not constrain core reduction.]

***********************************************************************/
  void RelationGenerator::addConflictSamples(Relation& relation, const WitnessRows& samples,
      const std::vector<int>& inputs, const std::vector<int>& outputs) {
    const unsigned nOutputs = outputs.size();
    for (const auto& witness : samples) {
      const unsigned row = witness.first, words = witness.second.size();
      std::vector<WitnessWord> known(words, 0), forbidden(witness.second), uncovered(witness.second);
      std::vector<WitnessWord> cube(words), expanded(words);
      for (const auto& old : relation.getPattern(row))
        for (unsigned w = 0; w < words; ++w) {
          WitnessWord value = nOutputs < 6 ? (WitnessWord(1) << (1u << nOutputs)) - 1 : ~WitnessWord(0);
          for (unsigned j = 0; j < nOutputs; ++j)
            if (old[2*j]) {
              const WitnessWord pattern = j < 6 ? truth_patterns[j] :
                  ((w >> (j - 6)) & 1 ? ~WitnessWord(0) : WitnessWord(0));
              value &= old[2*j + 1] ? ~pattern : pattern;
            }
          known[w] |= value;
        }
      for (unsigned w = 0; w < words; ++w) {
        forbidden[w] |= known[w];
        uncovered[w] &= ~known[w];
      }
      for (unsigned w = 0; w < words; ++w)
        while (uncovered[w]) {
          const unsigned tuple = 64 * w + lsb(uncovered[w]);
          unsigned care = (1u << nOutputs) - 1;
          std::fill(cube.begin(), cube.end(), 0);
          cube[w] = WitnessWord(1) << (tuple % 64);
          for (unsigned j = 0; j < nOutputs; ++j) {
            for (unsigned k = 0; k < words; ++k)
              if (j < 6)
                expanded[k] = cube[k] | ((cube[k] & ~truth_patterns[j]) << (1u << j)) |
                                       ((cube[k] & truth_patterns[j]) >> (1u << j));
              else
                expanded[k] = cube[k] | cube[k ^ (1u << (j - 6))];
            bool valid = true;
            for (unsigned k = 0; k < words; ++k)
              if (expanded[k] & ~forbidden[k]) { valid = false; break; }
            if (valid) {
              cube.swap(expanded);
              care &= ~(1u << j);
            }
          }
          std::vector<bool> pattern(2 * nOutputs, false);
          std::vector<int> clause {-mode_selection_variable};
          for (unsigned i = 0; i < inputs.size(); ++i)
            clause.push_back((row >> i) & 1 ? -inputs[i] : inputs[i]);
          for (unsigned i = 0; i < nOutputs; ++i)
            if ((care >> i) & 1) {
              pattern[2*i] = true;
              pattern[2*i + 1] = !((tuple >> i) & 1);
              clause.push_back(pattern[2*i + 1] ? outputs[i] : -outputs[i]);
            }
          solver.addClause(clause);
          relation.addOutputPattern(row, std::move(pattern));
          for (unsigned k = 0; k < words; ++k)
            uncovered[k] &= ~cube[k];
        }
    }
  }

/**Function*************************************************************

  Synopsis    [Computes a cut relation by SAT, optionally seeded with sampled witnesses.]

***********************************************************************/
  Relation RelationGenerator::computeRelation(const eSLIM3CirMan& cir, const Subcircuit& subcir,
                                              const eSLIM3Config& cfg, eSLIM3Log& log, const OptimalityCheck& optimal,
                                              RelationContextState* context) {
    if (cfg.expired()) {
      Relation incomplete(subcir.inputs.size());
      incomplete.status = false;
      return incomplete;
    }
    if (cfg.local_relations)
      return computeWindowRelation(cir, subcir, cfg, log, optimal, context);
    Relation witnesses(subcir.inputs.size());
    const bool sampled = collectWitnesses(cir, subcir, cfg, log, witnesses);
    if (!witnesses.getStatus()) return witnesses;
    // Witnessed conflicts form a subset of the complete forbidden sets. A
    // lower-bound proof already tight on this relaxation needs no relation SAT.
    if (sampled && optimal && optimal(witnesses)) {
      witnesses.status = false; // a skip proof, never a complete synthesis relation
      witnesses.proven_optimal = true;
      return witnesses;
    }
    log.nof_sat_relations++;
    RelationGenerator rgen(cir, subcir, cfg, log);
    return rgen.getRelation(std::move(witnesses), sampled);
  }

/**Function*************************************************************

  Synopsis    [Retries incomplete local SAT relations with successively smaller contexts.]

  Description [Each attempt observes every exit of its own region and treats
  boundary inputs as free. Shrinking may remove don't-cares, but cannot permit
  an incorrect replacement. Stop at the bare cut and divisors or the overall
  deadline; partial relations are never used for synthesis.]

***********************************************************************/
  Relation RelationGenerator::computeWindowRelation(const eSLIM3CirMan& cir,
      const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, const OptimalityCheck& optimal,
      RelationContextState* context) {
    eSLIM3Config attempt = cfg;
    bool full_probe = false;
    if (context) {
      const auto start = context->prepare(attempt);
      full_probe = start == RelationContextState::Start::Probe;
      log.relation_context_reuses += start == RelationContextState::Start::Reused;
      log.relation_context_probes += start == RelationContextState::Start::Probe;
    }
    bool retried = false;
    for (;;) {
      bool has_context = false;
      Relation relation = computeWindowAttempt(cir, subcir, attempt, log, optimal, has_context);
      if (relation.getStatus() || relation.isProvenOptimal()) {
        if (context) context->remember(attempt);
        if (retried && relation.getStatus()) ++log.relation_fallbacks;
        return relation;
      }
      ++log.relation_timeouts;
      if (cfg.expired() || !has_context) return relation;
      // A failed full probe returns directly to the remembered successful
      // caps instead of repeating the intermediate contexts already rejected.
      if (!(full_probe && context->restrictToRemembered(attempt))) {
        attempt.relation_window_gates = std::max(1u, attempt.relation_window_gates / 2);
        attempt.relation_window_inputs = std::max(2u, attempt.relation_window_inputs / 2);
        attempt.relation_window_fanin /= 2;
        attempt.relation_window_fanout /= 2;
      }
      full_probe = false;
      ++log.relation_retries;
      retried = true;
    }
  }

/**Function*************************************************************

  Synopsis    [Computes a conservative relation in a bounded local context.]

  Description [Every edge leaving the region is observed. Region inputs are
  independent, so preserving all region outputs for every input assignment
  is sufficient for preserving the surrounding circuit. In particular, a
  path that exits and reenters the region cannot hide a changed value: its
  first exit is observed. The original cut order is retained for synthesis.]

***********************************************************************/
  Relation RelationGenerator::computeWindowAttempt(const eSLIM3CirMan& cir,
      const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log,
      const OptimalityCheck& optimal, bool& has_context) {
    const abctime extraction_start = cfg.timeNow();
    if (!cir.relation_window_scratch)
      cir.relation_window_scratch = std::make_unique<eSLIM3CirMan::RelationWindowScratch>();
    auto& scratch = *cir.relation_window_scratch;
    scratch.begin(cir.getNofObjs());
    auto& region = scratch.region;
    auto& frontier = scratch.frontier;
    auto& next = scratch.next;
    auto orderedUnique = [](std::vector<int>& ids) {
      std::sort(ids.begin(), ids.end());
      ids.erase(std::unique(ids.begin(), ids.end()), ids.end());
    };
    region.assign(subcir.nodes.begin(), subcir.nodes.end());
    // Define divisors inside the window so the relation sees their correlations.
    region.insert(region.end(), subcir.divisors.begin(), subcir.divisors.end());
    orderedUnique(region);
    const size_t mandatory_gates = region.size();
    for (int id : region) scratch.get(id).inside = true;
    unsigned boundary_size = 0;
    auto addBoundary = [&](int id) {
      if (!id) return;
      auto& entry = scratch.get(id);
      if (entry.inside) return;
      if (!entry.references++) ++boundary_size;
      if (!entry.listed) {
        entry.listed = true;
        scratch.boundary.push_back(id);
      }
    };
    for (int id : region)
      for (auto* fanin : cir.getObj(id).fanins)
        addBoundary(fanin->node_id);
    auto boundaryInputs = [&]() {
      std::vector<int> inputs;
      inputs.reserve(boundary_size);
      for (int id : scratch.boundary)
        if (scratch.get(id).references) inputs.push_back(id);
      std::sort(inputs.begin(), inputs.end());
      assert(inputs.size() == boundary_size);
      return inputs;
    };
    auto addContext = [&](int id) {
      auto& entry = scratch.get(id);
      if (cir.isPi(id) || cir.isPo(id) || entry.inside ||
          region.size() >= cfg.relation_window_gates)
        return false;
      const unsigned old_refs = entry.references;
      if (old_refs) --boundary_size;
      entry.references = 0;
      entry.inside = true;
      for (auto* fanin : cir.getObj(id).fanins)
        addBoundary(fanin->node_id);
      if (boundary_size > cfg.relation_window_inputs) {
        for (auto* fanin : cir.getObj(id).fanins)
          if (fanin->node_id) {
            auto& input = scratch.get(fanin->node_id);
            if (!input.inside) {
              assert(input.references);
              if (!--input.references) --boundary_size;
            }
          }
        entry.inside = false;
        entry.references = old_refs;
        if (old_refs) ++boundary_size;
        return false;
      }
      region.push_back(id);
      return true;
    };

    // Sorted frontiers preserve the old set-based growth order when a cap is
    // reached. Membership and boundary updates use constant-time indexed marks.
    frontier.assign(subcir.outputs.begin(), subcir.outputs.end());
    orderedUnique(frontier);
    for (unsigned level = 0; level < cfg.relation_window_fanout && !frontier.empty(); ++level) {
      next.clear();
      for (int id : frontier)
        for (auto* fanout : cir.getObj(id).fanouts)
          if (addContext(fanout->node_id)) next.push_back(fanout->node_id);
      orderedUnique(next);
      frontier.swap(next);
    }
    frontier = boundaryInputs();
    for (unsigned level = 0; level < cfg.relation_window_fanin && !frontier.empty(); ++level) {
      next.clear();
      for (int id : frontier)
        if (addContext(id))
          for (auto* fanin : cir.getObj(id).fanins)
            if (fanin->node_id && !scratch.get(fanin->node_id).inside)
              next.push_back(fanin->node_id);
      orderedUnique(next);
      frontier.swap(next);
    }

    has_context = region.size() > mandatory_gates;
    const auto inputs = boundaryInputs();
    // Node indices are topological. Sorting restores the original node and
    // output order, independently of the order in which context was admitted.
    std::sort(region.begin(), region.end());
    eSLIM3CirMan window(int(region.size() + inputs.size() + region.size()));
    for (int id : inputs) scratch.get(id).local_id = window.addPi();
    auto localId = [&](int id) {
      const int mapped = scratch.get(id).local_id;
      assert(!id || mapped);
      return mapped;
    };
    for (int id : region) {
      const auto& node = cir.getObj(id);
      std::vector<int> fanins;
      fanins.reserve(node.fanins.size());
      for (auto* fanin : node.fanins) fanins.push_back(localId(fanin->node_id));
      scratch.get(id).local_id = window.addNode(fanins, node.tt);
    }
    for (int id : region)
      for (auto* fanout : cir.getObj(id).fanouts)
        if (!scratch.get(fanout->node_id).inside) {
          window.addPo(localId(id), false);
          break;
        }
    Subcircuit cut = Subcircuit::getEmptySubcircuit();
    for (int id : subcir.nodes) cut.nodes.push_back(localId(id));
    for (int id : subcir.inputs) cut.inputs.push_back(localId(id));
    for (int id : subcir.outputs) cut.outputs.push_back(localId(id));
    window.incrementTraversalId();
    window.markSubcircuit(cut.nodes);
    cut.markCones(window);
    eSLIM3Config local = cfg;
    local.local_relations = false;
    local.relation_sample_salt = samplingSeed(cir, subcir, cfg);
    // The extracted boundary itself defines the approximation. A second
    // truncation could miss exits, so use the complete local miter.
    local.approximate_relation = false;
    ++log.nof_window_relations;
    log.max_relation_window_gates = std::max(log.max_relation_window_gates, unsigned(region.size()));
    log.max_relation_window_inputs = std::max(log.max_relation_window_inputs, unsigned(inputs.size()));
    log.relation_window_time += double(cfg.timeNow() - extraction_start) / CLOCKS_PER_SEC;
    return computeRelation(window, cut, local, log, optimal);
  }


/**Function*************************************************************

  Synopsis    [Independently validates a replacement against the local relation.]

  Description [Checks every cut-input assignment using scalar evaluation,
  rather than the synthesis encoding or its bit-parallel simulation. Also
  checks forbidden structural dependencies to exclude replacement cycles.]

***********************************************************************/
  bool RelationGenerator::verifyReplacement(const eSLIM3CirMan& replacement,
      const Subcircuit& subcir, const Relation& relation, const eSLIM3Config& cfg) {
    const unsigned inputs = subcir.inputs.size(), outputs = subcir.outputs.size();
    if (replacement.getNofPis() != int(inputs) || replacement.getNofPos() != int(outputs) ||
        !relation.getStatus())
      return false;
    const int first_output = replacement.getNofObjs() - outputs;
    std::vector<std::vector<bool>> dependencies(replacement.getNofObjs(), std::vector<bool>(inputs));
    for (unsigned i = 0; i < inputs; ++i) dependencies[i+1][i] = true;
    for (int id = inputs + 1; id < replacement.getNofObjs(); ++id) {
      const auto& node = replacement.getObj(id);
      if (node.fanins.size() > 6) return false;
      for (auto* fanin : node.fanins) {
        if (fanin->node_id < 0 || fanin->node_id >= id) return false;
        for (unsigned i = 0; i < inputs; ++i)
          dependencies[id][i] = dependencies[id][i] || dependencies[fanin->node_id][i];
      }
    }
    for (unsigned out = 0; out < outputs; ++out) {
      auto forbidden = subcir.forbidden_pairs.find(subcir.outputs[out]);
      if (forbidden == subcir.forbidden_pairs.end()) continue;
      for (unsigned in = 0; in < inputs; ++in)
        if (forbidden->second.count(subcir.inputs[in]) && dependencies[first_output + out][in])
          return false;
    }
    std::vector<unsigned char> values(replacement.getNofObjs());
    for (int row = 0; row < relation.getNPatterns(); ++row) {
      if (!(row & 63) && cfg.expired()) return false;
      for (unsigned in = 0; in < inputs; ++in) values[in+1] = (unsigned(row) >> in) & 1;
      for (int id = inputs + 1; id < replacement.getNofObjs(); ++id) {
        const auto& node = replacement.getObj(id);
        unsigned index = 0;
        for (unsigned pin = 0; pin < node.fanins.size(); ++pin)
          index |= unsigned(values[node.fanins[pin]->node_id]) << pin;
        values[id] = (node.tt >> index) & 1;
      }
      for (const auto& pattern : relation.getPattern(row)) {
        bool conflict = true;
        for (unsigned out = 0; out < outputs; ++out)
          if (pattern[2*out] && bool(values[first_output + out]) == pattern[2*out+1]) {
            conflict = false;
            break;
          }
        if (conflict) return false;
      }
    }
    return true;
  }

/**Function*************************************************************

  Synopsis    [Mixes the run seed with stable cut identities for repeatable sampling.]

  Description [Window extraction carries the original cut identity as a salt,
  so renumbering similar windows does not give every cut the same patterns.]

***********************************************************************/
  ABC_UINT64_T RelationGenerator::samplingSeed(const eSLIM3CirMan& cir,
      const Subcircuit& subcir, const eSLIM3Config& cfg) {
    ABC_UINT64_T seed = ABC_CONST(0xcbf29ce484222325) ^ unsigned(cfg.seed);
    auto mix = [&](ABC_UINT64_T value) { seed = (seed ^ value) * ABC_CONST(0x100000001b3); };
    mix(cfg.relation_sample_salt);
    for (const auto* ids : {&subcir.nodes, &subcir.inputs, &subcir.outputs}) {
      mix(ids->size());
      for (int id : *ids) mix(cir.getObj(id).getId());
    }
    return seed;
  }

  // Test cut-output tuples on concrete PI assignments. With feedback through
  // the surrounding DAG, partition by cut inputs in the CHANGED circuit,
  // matching the SAT encoding rather than the original circuit's partition.
/**Function*************************************************************

  Synopsis    [Collects witnessed conflicts with a sample sized to the cut's input rows.]

  Description [Each forbidden tuple has a concrete witness. Sampling only
  seeds the relation; SAT must still prove that no further conflict exists.
  Use four patterns per cut-input row, bounded to 256--4096 patterns and
  reduced if needed to fit the work/memory allowance. Context PI count does
  not determine the sample size; this never enumerates all PI assignments.]

***********************************************************************/
  bool RelationGenerator::sampleRelation(const eSLIM3CirMan& cir, const Subcircuit& subcir,
                                         const eSLIM3Config& cfg, Relation& rel, unsigned* patterns) {
    typedef ABC_UINT64_T Word;
    const unsigned nPis = cir.getNofPis();
    const unsigned nInputs = subcir.inputs.size();
    const unsigned nOutputs = subcir.outputs.size();
    if (cfg.approximate_relation || nInputs > 16 || nOutputs == 0 || nOutputs > 6)
      return false;
    const unsigned nRows = 1u << nInputs;
    const unsigned nTuples = 1u << nOutputs;
    const unsigned nNodes = cir.getNofObjs() - cir.getNofPos();
    std::vector<int> affected, compared;
    std::vector<unsigned> feedback_inputs;
    unsigned feedback_mask = 0;
    for (unsigned j = 0; j < nInputs; ++j)
      if (cir.inTFO(cir.getObj(subcir.inputs[j]))) {
        feedback_inputs.push_back(j);
        feedback_mask |= 1u << j;
      }
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
    constexpr unsigned minimum_words = 4, maximum_words = 64;
    unsigned nWords = std::min(maximum_words, std::max(minimum_words, nRows / 16));
    const ABC_UINT64_T tableFactor = 2ull * nNodes + nRows + 1;
    const ABC_UINT64_T workFactor = nNodes + 1ull * nRows * nInputs +
        1ull * nTuples * (affected.size() + compared.size() +
                         nRows * (1ull + feedback_inputs.size()));
    auto fits = [&](unsigned words) {
      return tableFactor * words + nRows <= memoryLimit && workFactor * words <= (1u << 26);
    };
    while (nWords > minimum_words && !fits(nWords)) nWords /= 2;
    if (!fits(nWords)) return false;
    if (patterns) *patterns = 64 * nWords;
    std::vector<Word> reference(size_t(nNodes) * nWords, 0);
    std::mt19937_64 random {samplingSeed(cir, subcir, cfg)};
    for (unsigned i = 0; i < nPis; ++i)
      for (unsigned w = 0; w < nWords; ++w) {
        Word value = random();
        // Include all-zero and all-one assignments to expose deep AND/OR cones.
        if (!w) value = (value & ~Word(3)) | Word(2);
        reference[size_t(i + 1) * nWords + w] = value;
      }
    auto evaluate = [nWords, &cir, &cfg](std::vector<Word>& values, int i) {
      const auto& obj = cir.getObj(i);
      const Word* a = &values[size_t(obj.fanins[0]->node_id) * nWords];
      const Word* b = &values[size_t(obj.fanins[1]->node_id) * nWords];
      Word* out = &values[size_t(i) * nWords];
      // Select the Boolean operation once per gate, outside the word loop.
      if (cfg.fast_simulation) {
        simulateTwoInputGate(unsigned(obj.tt), a, b, out, nWords);
        return;
      }
      const Word m0 = -Word((obj.tt >> 0) & 1), m1 = -Word((obj.tt >> 1) & 1);
      const Word m2 = -Word((obj.tt >> 2) & 1), m3 = -Word((obj.tt >> 3) & 1);
      for (unsigned w = 0; w < nWords; ++w)
        out[w] = (~a[w] & ~b[w] & m0) | (a[w] & ~b[w] & m1) |
                 (~a[w] & b[w] & m2) | (a[w] & b[w] & m3);
    };
    for (unsigned i = nPis + 1; i < nNodes; ++i)
      evaluate(reference, i);
    // Precompute the part of the input partition unaffected by cut outputs.
    // Feedback inputs are intersected below after simulating each tuple.
    std::vector<Word> rows(size_t(nRows) * nWords, ~Word(0));
    for (unsigned r = 0; r < nRows; ++r)
      for (unsigned j = 0; j < nInputs; ++j) {
        if ((feedback_mask >> j) & 1)
          continue;
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
      if (cfg.expired()) {
        rel.status = false;
        return true;
      }
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
    // Cover forbidden tuples with cubes. Dropping a literal is legal only if
    // every tuple in the enlarged cube has a witness. SAT must still complete
    // the relation, even if these samples happened to cover every PI assignment.
    for (unsigned r = 0; r < nRows; ++r) {
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
    return true;
  }

/**Function*************************************************************

  Synopsis    [Allocates the next SAT variable in the relation miter.]

***********************************************************************/
  int RelationGenerator::getNewVar() {
    return max_var++;
  }

/**Function*************************************************************

  Synopsis    [Builds the SAT variables and constraints for the selected problem.]

***********************************************************************/
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

/**Function*************************************************************

  Synopsis    [Encodes a gate truth table using the selected circuit-variable map.]

***********************************************************************/
  void RelationGenerator::encodeGate(const eSLIM3CirObj& obj, int var, const std::vector<int>& gate2var) {
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

/**Function*************************************************************

  Synopsis    [Encodes a gate by its unique truth-table value.]

***********************************************************************/
  void RelationGenerator::getGateEncodingUnique(const eSLIM3CirObj& obj, int var, const std::vector<int>& gate2var, bool unique_bit) {
    ABC_UINT64_T tt = obj.tt;
    if (!unique_bit) {
      tt = eSLIM3CirMan::negateTT(tt, obj.getNFanins());
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

/**Function*************************************************************

  Synopsis    [Encodes a gate by enumerating its truth-table rows.]

***********************************************************************/
  void RelationGenerator::getGateEncodingNaive(const eSLIM3CirObj& obj, int var, const std::vector<int>& gate2var) {
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

    // Additional divisors need definitions even when they do not feed an
    // affected output in the original graph. They are unchanged in the miter.
    for (int id : subcir.inputs) {
      if (!gate2varref[id]) gate2varref[id] = getNewVar();
      if (!cir.inTFO(cir.getObj(id))) gate2varcone[id] = gate2varref[id];
    }

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


/**Function*************************************************************

  Synopsis    [Builds a relation miter with bounded fanout context.]

***********************************************************************/
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

/**Function*************************************************************

  Synopsis    [Marks the restricted fanout cone and its required fanins.]

***********************************************************************/
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

/**Function*************************************************************

  Synopsis    [Assigns the SAT variable representing the circuit constant.]

***********************************************************************/
  void RelationGenerator::setupConstantGate() {
    int const_var = getNewVar();
    gate2varref[0] = const_var;
    gate2varcone[0] = const_var;
    solver.addClause({-const_var});
  }

/**Function*************************************************************

  Synopsis    [Connects corresponding circuit signals through equality indicators.]

***********************************************************************/
  void RelationGenerator::setupEqualityConstraints(const std::vector<int>& nodes) {
    compared_nodes = nodes;
    log.relation_observed_exits += nodes.size();
    log.relation_max_exits = std::max(log.relation_max_exits, unsigned(nodes.size()));
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


/**Function*************************************************************

  Synopsis    [Defines an auxiliary literal for equality of two SAT variables.]

***********************************************************************/
  void RelationGenerator::getEqualityClauses(int x, int y, int aux) {
    solver.addClause({x, -y, -aux});
    solver.addClause({-x, y, -aux});
    solver.addClause({x, y, aux});
    solver.addClause({-x, -y, aux});
  }

/**Function*************************************************************

  Synopsis    [Searches for an output mismatch under the selected miter mode.]

  Description [Focus on one exit until exhausted, then query all remaining
  exits together. Exhausted exits stay exhausted as blocking clauses are
  added. Only a global UNSAT result establishes relation completeness.]

***********************************************************************/
  int RelationGenerator::findConflict(double& timeout, int mode_selection) {
    const auto query = [&](std::initializer_list<int> assumptions) {
      if (timeout <= 0 || cfg.expired()) return 0;
      const abctime start = cfg.timeNow();
      const int status = solver.solve(timeout, std::vector<int>(assumptions));
      const double elapsed = double(cfg.timeNow() - start) / CLOCKS_PER_SEC;
      timeout -= elapsed;
      log.cummulative_sat_runtime_relation_generation += elapsed;
      log.max_sat_runtime_relation_generation = std::max(log.max_sat_runtime_relation_generation, elapsed);
      ++log.nof_sat_calls_relation_generation;
      return status;
    };
    if (cfg.approximate_relation) return query({mode_selection});
    if (current_exit >= equality_variables.size()) return 20;
    const int focused = query({mode_selection, -equality_variables[current_exit]});
    if (focused != 20) return focused;
    // Blocking only shrinks the mismatch set. Exhausted exits cannot differ
    // in a later model, so the existing global mismatch clause is exactly an
    // "any remaining exit" query; no fresh selector or growing clause is needed.
    ++log.relation_any_exit_queries;
    const int status = query({mode_selection});
    if (status == 10) {
      for (current_exit = 0; current_exit < equality_variables.size(); ++current_exit)
        if (!solver.getValue(equality_variables[current_exit])) break;
      assert(current_exit < equality_variables.size());
    } else if (status == 20)
      current_exit = equality_variables.size();
    return status;
  }

/**Function*************************************************************

  Synopsis    [Minimizes a conflicting output assignment under fixed cone inputs.]

***********************************************************************/
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

/**Function*************************************************************

  Synopsis    [Times one witness sample shared by the early proof and SAT enumeration.]

***********************************************************************/
  bool RelationGenerator::collectWitnesses(const eSLIM3CirMan& cir, const Subcircuit& subcir,
      const eSLIM3Config& cfg, eSLIM3Log& log, Relation& relation) {
    if (!cfg.sample_relations || cfg.approximate_relation) return false;
    unsigned patterns = 0;
    const abctime start = cfg.timeNow();
    const bool sampled = sampleRelation(cir, subcir, cfg, relation, &patterns);
    log.relation_sampling_time += double(cfg.timeNow() - start) / CLOCKS_PER_SEC;
    if (sampled && relation.getStatus()) {
      ++log.nof_sampled_relations;
      log.sampled_relation_patterns += patterns;
    }
    return sampled;
  }

/**Function*************************************************************

  Synopsis    [Seeds the SAT enumeration with forbidden tuples witnessed by simulation.]

  Description [Only the conflicting-tuple search sees the blocking clauses.
  The equality query used for core reduction is unchanged. Every blocked
  cube is recorded in the relation, and each tuple in it has a concrete
  witness. A final UNSAT result is still required for completeness.]

***********************************************************************/
  void RelationGenerator::seedRelation(Relation& relation,
      const std::vector<int>& input_variables, const std::vector<int>& output_variables) {
    ScopedPhaseTimer encoding_timer(log.relation_encoding_time, cfg);
    ++log.nof_seeded_relations;
    for (unsigned row = 0; row < unsigned(relation.getNPatterns()); ++row) {
      log.seeded_relation_tuples += popcount(relation.getForbiddenTuples(row, output_variables.size()));
      for (const auto& pattern : relation.getPattern(row)) {
        std::vector<int> clause {-mode_selection_variable};
        for (unsigned input = 0; input < input_variables.size(); ++input)
          clause.push_back((row >> input) & 1 ? -input_variables[input] : input_variables[input]);
        for (unsigned output = 0; output < output_variables.size(); ++output)
          if (pattern[2*output])
            clause.push_back(pattern[2*output+1] ? output_variables[output] : -output_variables[output]);
        solver.addClause(clause);
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Enumerates forbidden boundary tuples until completion or timeout.]

***********************************************************************/
  Relation RelationGenerator::getRelation() {
    Relation relation(subcir.inputs.size());
    const bool sampled = collectWitnesses(cir, subcir, cfg, log, relation);
    if (!relation.getStatus()) return relation;
    return getRelation(std::move(relation), sampled);
  }

/**Function*************************************************************

  Synopsis    [Completes a previously sampled relation with guarded SAT enumeration.]

***********************************************************************/
  Relation RelationGenerator::getRelation(Relation rel, bool sampled) {
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
    for (int i = 0; std::size_t(i) < subcir.outputs.size(); i++) {
      int sout = subcir.outputs[i];
      int var = gate2varcone[sout];
      subcircuit_output_variables.push_back(var);
      if (subcir.forbidden_pairs.find(sout) != subcir.forbidden_pairs.end()) {
        outputs_to_keep[i] = true;
      }
    }

    preserveFeedbackOutputs(outputs_to_keep);

    if (sampled) seedRelation(rel, subcircuit_input_variables, subcircuit_output_variables);
    if (!rel.getStatus()) return rel;
    if (subcir.outputs.size() > 1) prepareWitnessSimulation();

    int solver_status;
    double timeout = cfg.relation_generation_timeout;
    while( (solver_status=findConflict(timeout, mode_selection_variable)) == 10) {
      const abctime time_start = cfg.timeNow();
      if (timeout <= 0) {
        rel.status = false;
        return rel;
      }
      std::vector<int> sin_assm = solver.getValues(subcircuit_input_variables);
      std::vector<int> sout_assm = solver.getValues(subcircuit_output_variables);
      const bool single_output = sout_assm.size() == 1;
      WitnessWord required_outputs = 0;
      const bool justified = !single_output && justifyConflict(required_outputs);
      const WitnessRows samples = sampleConflict();
      if (single_output) {
        // A mismatch cannot omit its only output. Retain the earlier fast
        // path and its statistics without a second solve or justification.
        ++log.single_output_core_calls_skipped;
      } else if (!justified) {
        const std::vector<int> cone_in_assm = solver.getValues(cone_input_variables);
        double reduction_timeout = timeout - double(cfg.timeNow() - time_start) / CLOCKS_PER_SEC;
        const int status = reduceConflict(reduction_timeout, cone_in_assm, sout_assm, equality_variables);
        if (status != 20) {
          assert(status != 10);
          rel.status = false;
          return rel;
        }
      }
      ScopedPhaseTimer encoding_timer(log.relation_encoding_time, cfg);
      std::vector<int> blocking_clause {-mode_selection_variable};
      for (int i = 0; std::size_t(i) < subcir.inputs.size(); i++) {
        blocking_clause.push_back(-sin_assm[i]);
      }
      std::vector<bool> pattern (2*subcir.outputs.size(), false);
      for (int i = 0; std::size_t(i) < subcir.outputs.size(); i++) {
        if (single_output || (justified ? ((required_outputs >> i) & 1) : solver.isFailed(sout_assm[i])) || outputs_to_keep[i]) {
          pattern[2*i] = true;
          pattern[2*i + 1] = sout_assm[i] < 0; // at least one output must be assigned differently in order to preserve the function
          blocking_clause.push_back(-sout_assm[i]);
        }
      }
      solver.addClause(blocking_clause);
      rel.addOutputPattern(assignment2bvindex(sin_assm), std::move(pattern));
      addConflictSamples(rel, samples, subcircuit_input_variables, subcircuit_output_variables);
      timeout -= double(cfg.timeNow() - time_start) / CLOCKS_PER_SEC;
    }
    if (solver_status != 20) {
      rel.status = false;
    }
    return rel;
  }

/**Function*************************************************************

  Synopsis    [Converts a signed literal assignment into its input-row index.]

***********************************************************************/
  int RelationGenerator::assignment2bvindex(const std::vector<int>& assm) {
    int idx = 0;
    for (int i = 0; std::size_t(i) < assm.size(); i++) {
      if (assm[i] > 0) {
        idx |= 1 << i;
      }
    }
    return idx;
  }

}
ABC_NAMESPACE_IMPL_END
