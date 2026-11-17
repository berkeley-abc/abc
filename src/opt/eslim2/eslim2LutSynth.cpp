/**CFile****************************************************************

  FileName    [eslim2LutSynth.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Exact single-LUT synthesis by projecting complete relation rows.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 16, 2026.]

***********************************************************************/

#include "areaEngine.h"
#include <array>
#include <climits>

ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {
/**Function*************************************************************

  Synopsis    [Finds a minimum-area zero- or one-LUT replacement when possible.]

  Description [Enumerates bounded supports, merging each complete relation's
  required output values onto the support. A conflicting projected row rejects
  that support. Normal truth tables and uncomplemented output connections match
  the existing replacement model. Feedback inputs and arrival bounds are checked
  before projecting. Failure leaves the ordinary multi-LUT SAT search available.]

***********************************************************************/
  eSLIM2CirMan AreaEngine::synthesiseSingleLut(const Relation& relation,
      const Subcircuit& subcir, const eSLIM2Config& cfg, int delay_bound, bool* complete) {
    using Word = ABC_UINT64_T;
    if (complete) *complete = false;
    const unsigned n = subcir.inputs.size();
    if (!cfg.small_synthesis || !cfg.lut_network || !relation.getStatus() ||
        subcir.outputs.size() != 1 || n > 10 || cfg.gate_size < 2 ||
        cfg.gate_size > 6 || cfg.expired()) return eSLIM2CirMan(0);
    const bool timed = delay_bound >= 0;
    assert(!timed || (subcir.arrival_times.size() == n && subcir.remaining_times.size() == 1));
    const unsigned remaining = timed ? subcir.remaining_times[0] : 0;
    if (timed && remaining > unsigned(delay_bound)) return eSLIM2CirMan(0);
    const unsigned limit = timed ? unsigned(delay_bound) - remaining : UINT_MAX;
    auto arrival = [&](unsigned input) { return timed ? unsigned(subcir.arrival_times[input]) : 0u; };
    auto empty = [&]() {
      eSLIM2CirMan circuit(n + 3);
      for (unsigned input = 0; input < n; ++input) circuit.addPi();
      return circuit;
    };
    std::vector<unsigned char> required(1u << n);
    bool constant_zero = true;
    for (unsigned row = 0; row < required.size(); ++row) {
      const Word forbidden = relation.getForbiddenTuples(row, 1);
      if (forbidden == 3) return eSLIM2CirMan(0);
      // Bit 0 requires output zero; bit 1 requires output one.
      required[row] = ((forbidden & 1) << 1) | ((forbidden & 2) >> 1);
      constant_zero &= !(required[row] & 2);
    }
    if (constant_zero) {
      auto circuit = empty(); circuit.addPo(0, false); return circuit;
    }
    const auto forbidden = subcir.forbidden_pairs.find(subcir.outputs[0]);
    unsigned permitted = 0, best_arrival = UINT_MAX;
    eSLIM2CirMan best(0);
    for (unsigned input = 0; input < n; ++input) {
      if (forbidden != subcir.forbidden_pairs.end() && forbidden->second.count(subcir.inputs[input])) continue;
      permitted |= 1u << input;
      if (arrival(input) > limit || arrival(input) >= best_arrival) continue;
      bool matches = true;
      for (unsigned row = 0; row < required.size(); ++row)
        if (required[row] & (1u << (1 ^ ((row >> input) & 1)))) { matches = false; break; }
      if (!matches) continue;
      best = empty(); best.addPo(input + 1, false);
      best_arrival = arrival(input);
      if (!timed) return best;
    }
    if (best.getNofObjs() > 1 || subcir.nodes.empty()) return best;
    unsigned best_pins = UINT_MAX;
    for (unsigned support = 1; support < (1u << n); ++support) {
      if ((support & ~permitted) || popcount(support) < 2 || popcount(support) > unsigned(cfg.gate_size)) continue;
      if (cfg.expired()) return best;
      std::vector<int> fanins;
      unsigned time = 0;
      for (unsigned input = 0; input < n; ++input) if ((support >> input) & 1) {
        fanins.push_back(input + 1);
        time = std::max(time, arrival(input));
      }
      ++time;
      if (time > limit || time > best_arrival ||
          (time == best_arrival && fanins.size() >= best_pins)) continue;
      std::array<unsigned char, 64> projected{};
      // Every internal gate is normalized: its all-zero value is zero.
      projected[0] = 1;
      bool consistent = true;
      for (unsigned row = 0; row < required.size(); ++row) {
        if (!required[row]) continue;
        unsigned index = 0;
        for (unsigned pin = 0; pin < fanins.size(); ++pin)
          index |= ((row >> (fanins[pin] - 1)) & 1) << pin;
        projected[index] |= required[row];
        if (projected[index] == 3) { consistent = false; break; }
      }
      if (!consistent) continue;
      Word truth = 0;
      for (unsigned row = 0; row < (1u << fanins.size()); ++row)
        if (projected[row] & 2) truth |= Word(1) << row;
      best = empty();
      best.addPo(best.addNode(fanins, truth), false);
      best_arrival = time;
      best_pins = fanins.size();
      if (!timed) return best;
    }
    if (complete) *complete = true;
    return best;
  }

/**Function*************************************************************

  Synopsis    [Finds a two-LUT decomposition using cofactor incompatibility.]

  Description [Partitions the inputs into bound and free sets, allowing shared
  inputs. Two incompatible bound cofactors must receive different values from
  the first LUT. A bipartite coloring supplies this value; the second LUT merges
  the resulting compatible rows. Every returned candidate satisfies all rows,
  feedback restrictions and arrival bounds. The bounded partition search is a
  heuristic: failure leaves general SAT available and is never an UNSAT proof.]

***********************************************************************/
  eSLIM2CirMan AreaEngine::synthesiseTwoLuts(const Relation& relation,
      const Subcircuit& subcir, const eSLIM2Config& cfg, int delay_bound) {
    using Word = ABC_UINT64_T;
    const unsigned n = subcir.inputs.size(), k = cfg.gate_size;
    if (!cfg.small_synthesis || !cfg.lut_network || !relation.getStatus() ||
        subcir.outputs.size() != 1 || subcir.nodes.size() < 2 || n > 10 ||
        k < 2 || k > 6) return eSLIM2CirMan(0);
    unsigned all = (1u << n) - 1;
    std::vector<unsigned char> required(1u << n);
    for (unsigned row = 0; row < required.size(); ++row) {
      const Word bad = relation.getForbiddenTuples(row, 1);
      required[row] = ((bad & 1) << 1) | ((bad & 2) >> 1);
      if (bad == 3) return eSLIM2CirMan(0);
    }
    // Equal allowed-value masks in both cofactors prove a removable input.
    for (unsigned pin = 0; pin < n; ++pin) {
      bool depends = false;
      for (unsigned row = 0; row < required.size(); ++row)
        if (!(row & (1u << pin)) && required[row] != required[row | (1u << pin)]) { depends = true; break; }
      if (!depends) all &= ~(1u << pin);
    }
    if (unsigned(popcount(all)) > 2 * k - 1) return eSLIM2CirMan(0);
    const auto shortcut_deadline = std::min(cfg.deadline, std::chrono::steady_clock::now() +
        std::chrono::milliseconds(std::max(1u, cfg.synthesis_timeout_ms)));
    auto project = [](unsigned row, const std::vector<int>& pins) {
      unsigned value = 0;
      for (unsigned i = 0; i < pins.size(); ++i)
        value |= ((row >> (pins[i] - 1)) & 1) << i;
      return value;
    };
    auto pins = [&](unsigned mask) {
      std::vector<int> result;
      for (unsigned i = 0; i < n; ++i) if ((mask >> i) & 1) result.push_back(i + 1);
      return result;
    };
    unsigned work = 0;
    for (unsigned free = 0; free <= all; ++free) {
      if (free & ~all) continue;
      if (!cfg.iterations && std::chrono::steady_clock::now() >= shortcut_deadline) return eSLIM2CirMan(0);
      if (unsigned(popcount(free)) >= k || unsigned(popcount(all ^ free)) > k) continue;
      const auto free_pins = pins(free);
      for (unsigned shared = free;; shared = (shared - 1) & free) {
        const unsigned bound = (all ^ free) | shared;
        if (unsigned(popcount(bound)) >= 2 && unsigned(popcount(bound)) <= k) {
          const auto bound_pins = pins(bound);
          const unsigned nb = 1u << bound_pins.size();
          work += required.size() + nb * nb;
          if (work > (1u << 24) || cfg.expired()) return eSLIM2CirMan(0);
          std::array<Word, 64> on{}, off{}, adjacent{};
          for (unsigned row = 0; row < required.size(); ++row) {
            const unsigned b = project(row, bound_pins), f = project(row, free_pins);
            if (required[row] & 2) on[b] |= Word(1) << f;
            if (required[row] & 1) off[b] |= Word(1) << f;
          }
          bool consistent = true;
          for (unsigned a = 0; a < nb; ++a) {
            if (on[a] & off[a]) { consistent = false; break; }
            for (unsigned b = 0; b < a; ++b)
              if ((on[a] & off[b]) || (off[a] & on[b])) {
                adjacent[a] |= Word(1) << b;
                adjacent[b] |= Word(1) << a;
              }
          }
          std::array<int, 64> color;
          color.fill(-1);
          // Both LUTs are normal: h(0)=0, g(0,0)=0. A cofactor requiring
          // one when all free inputs are zero must therefore have h=1.
          if (on[0] & 1) consistent = false;
          color[0] = 0;
          for (unsigned b = 1; b < nb; ++b) if (on[b] & 1) color[b] = 1;
          auto propagate = [&](std::vector<unsigned> queue) {
            for (unsigned head = 0; head < queue.size() && consistent; ++head) {
              const unsigned a = queue[head];
              for (Word rest = adjacent[a]; rest; rest &= rest - 1) {
                const unsigned b = lsb(rest);
                if (color[b] < 0) { color[b] = 1 - color[a]; queue.push_back(b); }
                else if (color[b] == color[a]) { consistent = false; break; }
              }
            }
          };
          std::vector<unsigned> forced;
          for (unsigned b = 0; b < nb; ++b) if (color[b] >= 0) forced.push_back(b);
          if (consistent) propagate(std::move(forced));
          for (unsigned start = 0; start < nb && consistent; ++start)
            if (color[start] < 0) { color[start] = 0; propagate({start}); }
          if (consistent) {
            Word first = 0, second = 0;
            std::array<unsigned char, 64> rows{};
            rows[0] = 1;
            for (unsigned b = 0; b < nb; ++b) if (color[b]) first |= Word(1) << b;
            for (unsigned row = 0; row < required.size(); ++row) {
              const unsigned index = color[project(row, bound_pins)] | (project(row, free_pins) << 1);
              rows[index] |= required[row];
              if (rows[index] == 3) { consistent = false; break; }
            }
            if (consistent) {
              for (unsigned row = 0; row < (2u << free_pins.size()); ++row)
                if (rows[row] & 2) second |= Word(1) << row;
              eSLIM2CirMan result(n + 4);
              for (unsigned i = 0; i < n; ++i) result.addPi();
              const int h = result.addNode(bound_pins, first);
              auto inputs = free_pins;
              inputs.insert(inputs.begin(), h);
              result.addPo(result.addNode(inputs, second), false);
              result.minimizeLutFanins();
              std::vector<unsigned> arrival(result.getNofObjs());
              if (delay_bound >= 0)
                for (unsigned i = 0; i < n; ++i) arrival[i + 1] = subcir.arrival_times[i];
              const auto forbidden = subcir.forbidden_pairs.find(subcir.outputs[0]);
              for (int id = n + 1; id < result.getNofObjs() - 1; ++id) {
                for (auto* fanin : result.getObj(id).fanins) {
                  const int input = fanin->node_id;
                  arrival[id] = std::max(arrival[id], arrival[input] + 1);
                  if (input > 0 && unsigned(input) <= n && forbidden != subcir.forbidden_pairs.end() &&
                      forbidden->second.count(subcir.inputs[input - 1])) consistent = false;
                }
              }
              const int output = result.getObj(result.getNofObjs() - 1).fanins[0]->node_id;
              if (output > 0 && unsigned(output) <= n && forbidden != subcir.forbidden_pairs.end() &&
                  forbidden->second.count(subcir.inputs[output - 1])) consistent = false;
              if (delay_bound >= 0 && arrival[output] + subcir.remaining_times[0] > unsigned(delay_bound)) consistent = false;
              if (consistent) return result;
            }
          }
        }
        if (!shared) break;
      }
    }
    return eSLIM2CirMan(0);
  }

}
ABC_NAMESPACE_IMPL_END
