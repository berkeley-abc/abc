/**CFile****************************************************************

  FileName    [eslim3Area.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Implementation of area based SAT encoding.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#include "areaEngine.h"
#include <climits>
#include <array>
#include <cstdint>
#include <mutex>
#include <unordered_map>

ABC_NAMESPACE_IMPL_START
namespace eSLIM3 {

  namespace {
    struct SmallCandidate {
      ABC_UINT64_T truth;
      std::array<uint16_t, 3> gates;
      uint8_t support;
    };
    static_assert(sizeof(SmallCandidate) == 16);
    using SmallCandidates = std::array<std::vector<SmallCandidate>, 3>;

    // Only the truth/care constraints and arrivals vary between calls. Build
    // the useful one-, two-, and three-gate DAGs once for each PI count,
    // preserving the previous enumeration order exactly. Four-bit fanin
    // indices and truth tables fit each gate descriptor in twelve bits.
/**Function*************************************************************

  Synopsis    [Build and share the ordered tables of small AIG candidates.]

  SideEffects [Initializes each immutable table once under call_once.]

***********************************************************************/
    const SmallCandidates& smallCandidates(unsigned n) {
      static std::array<SmallCandidates, 7> tables;
      static std::array<std::once_flag, 7> initialized;
      std::call_once(initialized[n], [n] {
        auto code = [](unsigned a, unsigned b, unsigned function) {
          return uint16_t(a | (b << 4) | (function << 8));
        };
        auto evaluate = [](ABC_UINT64_T a, ABC_UINT64_T b, unsigned function) {
          switch (function) {
            case 2: return a & ~b;
            case 4: return ~a & b;
            case 8: return a & b;
            default: return a | b;
          }
        };
        auto& table = tables[n];
        const unsigned singles = n * (n ? n - 1 : 0) * 2;
        table[0].reserve(singles);
        table[1].reserve(singles * n * 4);
        table[2].reserve(singles * n * 4 * (n + 1) * 4 + singles * (singles ? singles - 1 : 0) * 2);
        for (unsigned a = 0; a < n; ++a)
          for (unsigned b = a + 1; b < n; ++b)
            for (unsigned function : {2u, 4u, 8u, 14u})
              table[0].push_back({evaluate(truth_patterns[a], truth_patterns[b], function),
                                  {code(a, b, function), 0, 0}, uint8_t((1u << a) | (1u << b))});
        for (const auto& first : table[0])
          for (unsigned input = 0; input < n; ++input)
            for (unsigned function : {2u, 4u, 8u, 14u}) {
              const ABC_UINT64_T second = evaluate(truth_patterns[input], first.truth, function);
              const uint8_t support = first.support | (1u << input);
              table[1].push_back({second, {first.gates[0], code(input, n, function), 0}, support});
              for (unsigned last = 0; last <= n; ++last)
                for (unsigned last_function : {2u, 4u, 8u, 14u})
                  table[2].push_back({evaluate(last == n ? first.truth : truth_patterns[last], second, last_function),
                      {first.gates[0], code(input, n, function), code(last, n + 1, last_function)},
                      uint8_t(support | (last == n ? 0u : 1u << last))});
            }
        for (unsigned a = 0; a < table[0].size(); ++a)
          for (unsigned b = a + 1; b < table[0].size(); ++b)
            for (unsigned function : {2u, 4u, 8u, 14u})
              table[2].push_back({evaluate(table[0][a].truth, table[0][b].truth, function),
                  {table[0][a].gates[0], table[0][b].gates[0], code(n, n + 1, function)},
                  uint8_t(table[0][a].support | table[0][b].support)});
        // Keep the first candidate of each useful timing profile. A prior
        // implementation of the identical full function dominates a later
        // one if every PI-to-output distance is no greater (unused = -1).
        // This also makes its structural support a subset, so any feedback
        // restriction satisfied by the later graph is satisfied by the
        // earlier graph. Process gate counts in order: the retained circuit
        // has no greater area and is never slower for any input arrivals.
        // Do not remove earlier entries when a later one dominates them:
        // area-only synthesis deliberately keeps its original first choice.
        using Profile = std::array<int8_t, 6>;
        std::unordered_map<ABC_UINT64_T, std::vector<Profile>> seen;
        Profile unused;
        unused.fill(-1);
        seen[0].push_back(unused);
        for (unsigned input = 0; input < n; ++input) {
          Profile projection = unused;
          projection[input] = 0;
          seen[truth_patterns[input]].push_back(projection);
        }
        for (unsigned size = 1; size <= 3; ++size) {
          auto& candidates = table[size - 1];
          size_t kept = 0;
          for (const auto& candidate : candidates) {
            std::array<int8_t, 9> distance;
            distance.fill(-1);
            distance[n + size - 1] = 0;
            for (unsigned gate = size; gate-- > 0;) {
              const unsigned code = candidate.gates[gate];
              const int8_t next = distance[n + gate] + 1;
              distance[code & 15] = std::max(distance[code & 15], next);
              distance[(code >> 4) & 15] = std::max(distance[(code >> 4) & 15], next);
            }
            Profile profile = unused;
            for (unsigned input = 0; input < n; ++input)
              profile[input] = distance[input];
            auto& prior = seen[candidate.truth];
            bool dominated = false;
            for (const auto& previous : prior) {
              bool no_slower = true;
              for (unsigned input = 0; input < n; ++input)
                no_slower &= previous[input] <= profile[input];
              if (no_slower) {
                dominated = true;
                break;
              }
            }
            if (!dominated) {
              prior.push_back(profile);
              candidates[kept++] = candidate;
            }
          }
          candidates.resize(kept);
          candidates.shrink_to_fit();
        }
      });
      return tables[n];
    }
  }

  // Exhaust all normal, single-output AIGs of up to three gates.
  // Enumerate the possible useful-gate DAGs, including reconvergent shapes.
  // Don't-cares stay exact: a truth table must satisfy every constrained row.
  // A timed search also minimizes arrival time among equal-size solutions.
/**Function*************************************************************

  Synopsis    [Find an exact small replacement satisfying care, feedback and timing constraints.]

  SideEffects [Returns an independently owned replacement circuit.]

***********************************************************************/
  eSLIM3CirMan AreaEngine::synthesiseSmall(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, int delay_bound) {
    typedef ABC_UINT64_T Word;
    if (subcir.inputs.size() > 6)
      return synthesiseWideSmall(relation, subcir, cfg, delay_bound);
    if (!cfg.small_synthesis || !cfg.aig || cfg.gate_size != 2 ||
        subcir.outputs.size() != 1 || subcir.inputs.size() > 6)
      return eSLIM3CirMan(0);
    const bool timed = delay_bound >= 0;
    assert(!timed || (subcir.arrival_times.size() == subcir.inputs.size() && subcir.remaining_times.size() == 1));
    const unsigned remaining = timed ? subcir.remaining_times[0] : 0;
    if (timed && remaining > unsigned(delay_bound))
      return eSLIM3CirMan(0);
    auto arrival = [&](unsigned input) { return timed ? unsigned(subcir.arrival_times[input]) : 0u; };
    eSLIM3CirMan best(0);
    unsigned best_arrival = UINT_MAX;
    auto improves = [&](unsigned value) {
      return !timed || (value <= unsigned(delay_bound) - remaining && value < best_arrival);
    };
    Word on = 0, off = 0;
    for (unsigned row = 0; row < unsigned(relation.getNPatterns()); ++row) {
      Word forbidden = relation.getForbiddenTuples(row, 1);
      if (forbidden & 1) on |= Word(1) << row;
      if (forbidden & 2) off |= Word(1) << row;
    }
    auto matches = [on, off](Word truth) { return !(truth & off) && !(~truth & on); };
    auto empty = [&subcir]() {
      eSLIM3CirMan circuit(subcir.inputs.size() + 3);
      for (unsigned input = 0; input < subcir.inputs.size(); ++input)
        circuit.addPi();
      return circuit;
    };
    if (matches(0)) {
      auto circuit = empty();
      circuit.addPo(0, false);
      return circuit;
    }
    std::vector<unsigned> inputs;
    auto forbidden = subcir.forbidden_pairs.find(subcir.outputs[0]);
    for (unsigned input = 0; input < subcir.inputs.size(); ++input) {
      if (forbidden != subcir.forbidden_pairs.end() && forbidden->second.count(subcir.inputs[input]))
        continue;
      inputs.push_back(input);
      if (improves(arrival(input)) && matches(truth_patterns[input])) {
        auto circuit = empty();
        circuit.addPo(input + 1, false);
        if (!timed) return circuit;
        best = std::move(circuit);
        best_arrival = arrival(input);
      }
    }
    if (best.getNofObjs() > 1)
      return best;
    if (subcir.nodes.empty())
      return eSLIM3CirMan(0);
    const unsigned n = subcir.inputs.size();
    unsigned permitted = 0, mandatory = 0;
    for (unsigned input : inputs)
      permitted |= 1u << input;
    const unsigned forbidden_mask = ((1u << n) - 1) ^ permitted;
    for (unsigned input = 0; input < n; ++input) {
      const unsigned shift = 1u << input;
      if (((on & (off >> shift)) | (off & (on >> shift))) & ~truth_patterns[input])
        mandatory |= 1u << input;
    }
    // A mandatory PI cannot be supplied through a forbidden feedback path.
    // Three binary gates can depend on at most four distinct PIs.
    if ((mandatory & forbidden_mask) || popcount(mandatory) > 4)
      return eSLIM3CirMan(0);
    const auto& candidates = smallCandidates(n);
    std::array<unsigned, 9> arrivals{};
    for (unsigned input = 0; input < n; ++input)
      arrivals[input] = arrival(input);
    for (unsigned size = 1; size <= std::min(size_t(3), subcir.nodes.size()); ++size) {
      if (popcount(mandatory) > size + 1)
        continue;
      for (const auto& candidate : candidates[size - 1]) {
        if ((candidate.support & forbidden_mask) || (candidate.support & mandatory) != mandatory || !matches(candidate.truth))
          continue;
        unsigned depth = 0;
        if (timed) {
          for (unsigned gate = 0; gate < size; ++gate) {
            const unsigned code = candidate.gates[gate];
            arrivals[n + gate] = 1 + std::max(arrivals[code & 15], arrivals[(code >> 4) & 15]);
          }
          depth = arrivals[n + size - 1];
          if (!improves(depth))
            continue;
        }
        auto circuit = empty();
        for (unsigned gate = 0; gate < size; ++gate) {
          const unsigned code = candidate.gates[gate];
          circuit.addNode({int((code & 15) + 1), int(((code >> 4) & 15) + 1)}, code >> 8);
        }
        circuit.addPo(n + size, false);
        if (!timed)
          return circuit;
        best = std::move(circuit);
        best_arrival = depth;
      }
      if (best.getNofObjs() > 1)
        return best;
    }
    return best;
  }


/**Function*************************************************************

  Synopsis    [Enumerates zero-, one-, and two-gate replacements with up to ten inputs.]

  Description [Additional divisors often make the boundary wider than six
  inputs. Bit-vector care masks keep these tiny replacements inexpensive.
  A two-gate implementation whose output uses both gates is a chain; the
  unused-gate cases were already covered by the zero/one-gate searches.]

***********************************************************************/
  eSLIM3CirMan AreaEngine::synthesiseWideSmall(const Relation& relation,
      const Subcircuit& subcir, const eSLIM3Config& cfg, int delay_bound) {
    using Word = ABC_UINT64_T;
    const unsigned n = subcir.inputs.size();
    if (!cfg.small_synthesis || !cfg.aig || cfg.gate_size != 2 ||
        subcir.outputs.size() != 1 || n < 7 || n > 10 || cfg.expired())
      return eSLIM3CirMan(0);
    const bool timed = delay_bound >= 0;
    assert(!timed || (subcir.arrival_times.size() == n && subcir.remaining_times.size() == 1));
    const unsigned remaining = timed ? subcir.remaining_times[0] : 0;
    if (timed && remaining > unsigned(delay_bound)) return eSLIM3CirMan(0);
    const unsigned limit = timed ? unsigned(delay_bound) - remaining : UINT_MAX;
    const unsigned words = (1u << n) / 64;
    using Truth = std::array<Word,16>;
    Truth on {}, off {}, zero {};
    std::vector<Truth> inputs(n);
    unsigned forbidden_inputs = 0;
    auto forbidden = subcir.forbidden_pairs.find(subcir.outputs[0]);
    for (unsigned i=0;i<n;++i)
      if (forbidden != subcir.forbidden_pairs.end() && forbidden->second.count(subcir.inputs[i]))
        forbidden_inputs |= 1u << i;
    for (unsigned row=0;row<(1u<<n);++row) {
      const Word mask = Word(1) << (row%64);
      const auto bad = relation.getForbiddenTuples(row,1);
      if (bad&1) on[row/64] |= mask;
      if (bad&2) off[row/64] |= mask;
      for (unsigned i=0;i<n;++i) if ((row>>i)&1) inputs[i][row/64] |= mask;
    }
    auto matches = [&](const Truth& truth) {
      for (unsigned w=0;w<words;++w)
        if ((truth[w]&off[w]) || (~truth[w]&on[w])) return false;
      return true;
    };
    auto empty = [&]() {
      eSLIM3CirMan result(n+4);
      for (unsigned i=0;i<n;++i) result.addPi();
      return result;
    };
    if (matches(zero)) { auto result=empty(); result.addPo(0,false); return result; }
    auto arrival = [&](unsigned i) { return timed ? subcir.arrival_times[i] : 0u; };
    eSLIM3CirMan best(0);
    unsigned best_arrival = UINT_MAX;
    for (unsigned i=0;i<n;++i)
      if (!(forbidden_inputs&(1u<<i)) && arrival(i)<=limit && arrival(i)<best_arrival && matches(inputs[i])) {
        best=empty(); best.addPo(i+1,false); best_arrival=arrival(i);
      }
    if (best.getNofObjs()>1 || subcir.nodes.empty()) return best;
    auto evaluate = [](Word a, Word b, unsigned function) {
      switch (function) {
        case 2: return a&~b;
        case 4: return ~a&b;
        case 8: return a&b;
        default: return a|b;
      }
    };
    struct Candidate { unsigned a,b,function,arrival; Truth truth; };
    std::vector<Candidate> first_gates;
    for (unsigned a=0;a<n;++a) for (unsigned b=a+1;b<n;++b) {
      if (forbidden_inputs&((1u<<a)|(1u<<b))) continue;
      for (unsigned function : {2u,4u,8u,14u}) {
        Candidate candidate {a,b,function,1+std::max(arrival(a),arrival(b)),{}};
        for (unsigned w=0;w<words;++w) candidate.truth[w]=evaluate(inputs[a][w],inputs[b][w],function);
        if (candidate.arrival<=limit && candidate.arrival<best_arrival && matches(candidate.truth)) {
          best=empty(); best.addPo(best.addNode({int(a+1),int(b+1)},function),false);
          best_arrival=candidate.arrival;
        }
        first_gates.push_back(std::move(candidate));
      }
    }
    if (best.getNofObjs()>1 || subcir.nodes.size()<2) return best;
    for (const auto& first : first_gates) {
      if (cfg.expired()) return eSLIM3CirMan(0);
      for (unsigned input=0;input<n;++input) {
        if (forbidden_inputs&(1u<<input)) continue;
        const unsigned time=1+std::max(first.arrival,arrival(input));
        if (time>limit || time>=best_arrival) continue;
        for (unsigned function : {2u,4u,8u,14u}) {
          bool match=true;
          for (unsigned w=0;w<words;++w) {
            const Word truth=evaluate(first.truth[w],inputs[input][w],function);
            if ((truth&off[w]) || (~truth&on[w])) { match=false; break; }
          }
          if (!match) continue;
          best=empty();
          const int node=best.addNode({int(first.a+1),int(first.b+1)},first.function);
          best.addPo(best.addNode({node,int(input+1)},function),false);
          best_arrival=time;
          break;
        }
      }
    }
    return best;
  }

/**Function*************************************************************

  Synopsis    [Initializes area synthesis, boundary maps and feedback constraints.]

***********************************************************************/
  AreaEngine::AreaEngine(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log)
            : RelationSynthesiser(relation, subcir, subcir.nodes.size(), cfg, log, cfg.synthesis_cegar) {
    ScopedPhaseTimer encoding_timer(log.synthesis_encoding_time, cfg);
    if (cfg.aig && cfg.gate_size == 2 && cfg.aig_encoding >= 2)
      constrainIrredundantAigArea();
    for (int i = 0; std::size_t(i) < subcir.inputs.size(); i++) {
      input_index_map[subcir.inputs[i]] = i;
    }
    for (int i = 0; std::size_t(i) < subcir.outputs.size(); i++) {
      output_index_map[subcir.outputs[i]] = i;
    }
    if (subcir.forbidden_pairs.size() > 0) {
      setupCycleConstraints();
    }
  }

/**Function*************************************************************

  Synopsis    [Searches for a minimum-area implementation of the relation.]

***********************************************************************/
  eSLIM3CirMan AreaEngine::synthesiseMinimumSizeCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log, bool* complete) {
    if (complete)
      *complete = false;
    ++log.synthesis_searches;
    auto small = synthesiseSmall(relation, subcir, cfg);
    if (small.getNofObjs() > 1) {
      ++log.synthesis_small_hits;
      if (complete)
        *complete = true;
      return small;
    }
    AreaEngine synth(relation, subcir, cfg, log);
    std::vector<bool> last_model;
    int replacement_size = 0;
    for (int i = synth.max_size; i >= int(synth.min_size); i--) {
      double timeout = synth.getDynamicTimeout(i);
      int status = synth.checkSize(i, timeout);
      if (status == 10) {
        last_model = synth.getModel();
        i = synth.getSizeFromActivationVars(last_model);
        replacement_size = i;
        assert(unsigned(i) >= synth.min_size);
        if (complete && unsigned(i) == synth.min_size)
          *complete = true;
      } else {
        if (complete)
          *complete = status == 20;
        // An interrupted equal-size search says nothing about smaller sizes.
        // No model is read until a later query actually returns SAT.
        if (synth.retrySmallerAfterTimeout(status, unsigned(i)))
          continue;
        break;
      }
    }
    if (last_model.empty()) {
      // no replacement found
      return eSLIM3CirMan(0);
    } else {
      return synth.getReplacement(last_model, replacement_size);
    }
  }

/**Function*************************************************************

  Synopsis    [Checks whether a replacement exists at the requested gate count.]

***********************************************************************/
  int AreaEngine::checkSize(unsigned int size) {
    return checkSize(size, 0);
  }

/**Function*************************************************************

  Synopsis    [Checks whether a replacement exists at the requested gate count.]

***********************************************************************/
  int AreaEngine::checkSize(unsigned int size, double timeout) {
    std::vector<int> assumptions = getSizeAssumption(size);
    return solveRelation(assumptions, timeout, size);
  }

/**Function*************************************************************

  Synopsis    [Forbids dependencies that would create a cycle after replacement.]

***********************************************************************/
  void AreaEngine::setupCycleConstraints() {
    assert (!subcir.forbidden_pairs.empty());
    setupConnectionVariables();
    if (subcir.forbidden_pairs.size() > 1) {
      connectionVariablesForCombinedCycles();
    }
    addCycleConstraints();
  }

/**Function*************************************************************

  Synopsis    [Adds dependency constraints preventing cycles through the replacement.]

***********************************************************************/
  void AreaEngine::addCycleConstraints() {
    for (auto const& [outp, inputs] : subcir.forbidden_pairs) {
      for (int inp : inputs) {
        int output_idx = output_index_map.at(outp);
        for (int i = 0; unsigned(i) < max_size; i++) {
          solver.addClause({-gate_activation_variables[i], -gate_output_variables[i][output_idx], -connection_variables.at(inp)[i + subcir.inputs.size()]});
        }
        for (int i = 0; std::size_t(i) < subcir.inputs.size(); i++) {
          solver.addClause({-gate_output_variables[max_size + i][output_idx], -connection_variables.at(inp)[i]});
        }
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Allocates SAT variables representing cut input-to-output connectivity.]

***********************************************************************/
  void AreaEngine::setupConnectionVariables() {
    for (auto const& [out, inputs] : subcir.forbidden_pairs) {
      for (int in : inputs) {
        if (connection_variables.find(in) == connection_variables.end()) {
          connection_variables[in] = getNewVariableVector(max_size + subcir.inputs.size());
        }
      }
    }

    for (const auto& [input_var, connection_vars] : connection_variables) {
      int input_idx = input_index_map.at(input_var);
      // An input is connected to itself
      solver.addClause({connection_vars[input_idx]});
      for (int i = 0; unsigned(i) < max_size; i++) {
        int activation_variable = gate_activation_variables[i];
        for (int j = 0; std::size_t(j) < subcir.inputs.size(); j++) {
          // if gate i uses input j and input j is connected to input_var then also gate i is connected to input_var
          solver.addClause({-activation_variable, -selection_variables[i][j], -connection_vars[j], connection_vars[subcir.inputs.size() + i]});
        }
        for (int j = 0; j < i; j++) {
          // if gate i uses gate j and gate j is connected to input_var then also gate i is connected to input_var
          solver.addClause({-activation_variable, -selection_variables[i][subcir.inputs.size() + j], -connection_vars[subcir.inputs.size() + j], connection_vars[subcir.inputs.size() + i]});
        }
      }
    }
  }


/**Function*************************************************************

  Synopsis    [Connects dependency indicators for cycles through multiple cut outputs.]

***********************************************************************/
  void AreaEngine::connectionVariablesForCombinedCycles() {
    assert (subcir.forbidden_pairs.size() > 1);
    // Inputs are assigned to the outputs on which they depend
    std::unordered_map<int, std::unordered_set<int>> inputs_per_output;
    // Inputs in pairs
    std::unordered_set<int> inputs_in_pairs;
    for (auto const& [outp, inputs] : subcir.forbidden_pairs) {
      for (int inp : inputs) {
        if (inputs_per_output.find(outp) == inputs_per_output.end()) {
          inputs_per_output[outp] = {inp};
        } else {
          inputs_per_output[outp].insert(inp);
        }
        inputs_in_pairs.insert(inp);
      }
    }
    for (const auto& [ov, inp] : inputs_per_output) {
      for (int iv : inputs_in_pairs) {
        if (inp.find(iv) == inp.end()) {
          for (int k : inputs_per_output.at(ov)) {
            for (int i = 0; unsigned(i) < max_size; i++) {
              // Input k depends on output ov.
              // If gate i represents output ov and gate i is connected to iv then also gate k is connected to iv.
              solver.addClause({-gate_activation_variables[i], -gate_output_variables[i][output_index_map.at(ov)],
                              -connection_variables.at(iv)[subcir.inputs.size() + i], connection_variables.at(iv)[input_index_map.at(k)]});
            }
            for (int i = 0; std::size_t(i) < subcir.inputs.size(); i++) {
              // Input k depends on output ov.
              // If input i represents output ov and input i is connected to iv then gate k shall be connected to iv too.
              solver.addClause({-gate_output_variables[max_size + i][output_index_map.at(ov)], -connection_variables.at(iv)[i], connection_variables.at(iv)[input_index_map.at(k)]});
            }
          }
        }
      }
    }
  }


}
ABC_NAMESPACE_IMPL_END
