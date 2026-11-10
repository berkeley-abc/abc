/**CFile****************************************************************

  FileName    [selectionStrategiesImpl.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Subcircuit selection]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__SELECTIONSTRATEGIESIMPL_h
#define ABC__OPT__ESLIM3__SELECTIONSTRATEGIESIMPL_h

#include <cstddef>
#include <climits>
#include "selectionStrategies.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

/**Function*************************************************************

  Synopsis    [Retains the input-bound constraints for subcircuit selection.]

***********************************************************************/
  inline SubcircuitValidator::SubcircuitValidator(const eSLIM3Config& cfg) : cfg(cfg) {

  }

/**Function*************************************************************

  Synopsis    [Checks the selected cut's supported boundary-input count.]

***********************************************************************/
  inline bool SubcircuitValidator::precheck(const Subcircuit& candidate) const {
    return candidate.inputs.size() <= cfg.cut_input_limit && candidate.inputs.size() >= static_cast<std::size_t>(cfg.gate_size);
  }

/**Function*************************************************************

  Synopsis    [Checks whether the selected cut has a supported boundary.]

***********************************************************************/
  inline bool SubcircuitValidator::check(const Subcircuit& candidate) const {
    return precheck(candidate);
  }

/**Function*************************************************************

  Synopsis    [Checks the cut boundary and rejects feedback dependencies.]

***********************************************************************/
  inline bool SubcircuitNoFBValidator::check(const Subcircuit& candidate) const {
    return SubcircuitValidator::check(candidate) && candidate.forbidden_pairs.empty();
  }

/**Function*************************************************************

  Synopsis    [Initializes fanout-directed subcircuit growth.]

***********************************************************************/
  inline ForwardSearch::ForwardSearch(eSLIM3CirMan& es_man) : es_man(es_man) {
  }

/**Function*************************************************************

  Synopsis    [Returns the first adjacent object in the configured search direction.]

***********************************************************************/
  inline auto ForwardSearch::getNextBegin(const eSLIM3CirObj& obj) {
    return obj.fanouts.begin();
  }

/**Function*************************************************************

  Synopsis    [Returns the end of the adjacency range in the configured search direction.]

***********************************************************************/
  inline auto ForwardSearch::getNextEnd(const eSLIM3CirObj& obj) {
    return obj.fanouts.end();
  }

/**Function*************************************************************

  Synopsis    [Tests whether fanout growth can continue through this object.]

***********************************************************************/
  inline bool ForwardSearch::check(const eSLIM3CirObj& obj) const {
    return !es_man.isPo(obj.node_id);
  }

/**Function*************************************************************

  Synopsis    [Initializes fanin-directed subcircuit growth.]

***********************************************************************/
  inline BackwardSearch::BackwardSearch(eSLIM3CirMan& es_man) : es_man(es_man) {
  }

/**Function*************************************************************

  Synopsis    [Returns the first adjacent object in the configured search direction.]

***********************************************************************/
  inline auto BackwardSearch::getNextBegin(const eSLIM3CirObj& obj) {
    return obj.fanins.begin();
  }

/**Function*************************************************************

  Synopsis    [Returns the end of the adjacency range in the configured search direction.]

***********************************************************************/
  inline auto BackwardSearch::getNextEnd(const eSLIM3CirObj& obj) {
    return obj.fanins.end();
  }

/**Function*************************************************************

  Synopsis    [Tests whether fanin growth can continue through this object.]

***********************************************************************/
  inline bool BackwardSearch::check(const eSLIM3CirObj& obj) const {
    return !es_man.isPi(obj.node_id);
  }

/**Function*************************************************************

  Synopsis    [Retains the circuit used for uniform root selection.]

***********************************************************************/
  inline BaseRootSelector::BaseRootSelector(eSLIM3CirMan& es_man, const eSLIM3Config& cfg) : es_man(es_man) {

  }

/**Function*************************************************************

  Synopsis    [Initializes and attaches the circuit's taboo-aware root selector.]

***********************************************************************/
  inline TabooRootSelector::TabooRootSelector(eSLIM3CirMan& es_man, const eSLIM3Config& cfg) : es_man(es_man), cfg(cfg), taboo(es_man) {
    es_man.registerTabooList(&taboo);
  }

/**Function*************************************************************

  Synopsis    [Detaches the root selector from its independently owned circuit.]

***********************************************************************/
  inline TabooRootSelector::~TabooRootSelector() {
    es_man.unregisterTabooList();
  }


/**Function*************************************************************

  Synopsis    [Samples an integer uniformly from the requested inclusive range.]

***********************************************************************/
  inline unsigned int BaseRootSelector::getUniformRandomNumber(std::mt19937& rng, unsigned int lower, unsigned int upper) {
    udistr.param(std::uniform_int_distribution<std::mt19937::result_type>::param_type(lower, upper));
    return udistr(rng);
  }

/**Function*************************************************************

  Synopsis    [Selects a root according to the configured selection policy.]

***********************************************************************/
  inline int BaseRootSelector::getRoot(std::mt19937& rng, eSLIM3Log*) {
    int min_id = es_man.getNofPis() + 1;
    int max_id = es_man.getNofObjs() - es_man.getNofPos() - 1;
    return  getUniformRandomNumber(rng, min_id, max_id);
  }


/**Function*************************************************************

  Synopsis    [Selects a root according to the configured selection policy.]

***********************************************************************/
  inline int TabooRootSelector::getRoot(std::mt19937& rng, eSLIM3Log* log) {
    return taboo.getRandomNonTaboo(rng, cfg.taboo_ratio, cfg.taboo_time, log);
  }

/**Function*************************************************************

  Synopsis    [Leaves pure uniform selection independent of previous outcomes.]

***********************************************************************/
  inline void BaseRootSelector::recordFailure(int) {
  }

/**Function*************************************************************

  Synopsis    [Retains bounded failure history in the owning gate.]

***********************************************************************/
  inline void TabooRootSelector::recordFailure(int node) {
    taboo.recordFailure(node);
  }

/**Function*************************************************************

  Synopsis    [Resets selection state for the current graph.]

***********************************************************************/
  inline void TabooRootSelector::reset() {
    taboo.reset();
    es_man.registerTabooList(&taboo);
  }

/**Function*************************************************************

  Synopsis    [Selects a root according to the configured selection policy.]

***********************************************************************/
  inline int CriticalPathSelector::getRoot(std::mt19937& rng, eSLIM3Log* log) {
    if (cfg.depth_floor >= 0 && es_man.getDepth() <= cfg.depth_floor)
      return TabooRootSelector::getRoot(rng, log);
    return taboo.getBiasedRandomNonTaboo<CriticalPathBiasSelector>(rng, cfg.bias, cfg.taboo_ratio, cfg.taboo_time, log);
  }

/**Function*************************************************************

  Synopsis    [Rejects gates already present in the selected subcircuit.]

***********************************************************************/
  inline bool BaseCandidateNodeConstraint::check(int to_check, const eSLIM3CirMan& cir, const std::set<int>& subcircuit) {
    return subcircuit.find(to_check) == subcircuit.end();
  }

/**Function*************************************************************

  Synopsis    [Requires an added gate to keep all fanouts inside the selected cut.]

***********************************************************************/
  inline bool SingleOutputCandidateNodeConstraint::check(int to_check, const eSLIM3CirMan& cir, const std::set<int>& subcircuit) {
    if (subcircuit.find(to_check) != subcircuit.end()) {
      return false;
    }
    const auto& obj = cir.getObj(to_check);
    for (const auto& fo : obj.fanouts) {
      // The node has a fanout that is not yet in the subcircuit
      if (subcircuit.find(fo->node_id) == subcircuit.end()) {
        return false;
      }
    }
    return true;
  }

/**Function*************************************************************

  Synopsis    [Initializes randomized cut growth and its independent random generator.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::RandomizedBFSSelection(eSLIM3CirMan& es_man, const eSLIM3Config& cfg, eSLIM3Log& log)
                                                                  : es_man(es_man), cfg(cfg), log(log), validator(cfg), root_selector(es_man, cfg), search_direction(es_man),
                                                                    bdist(cfg.expansion_probability), biased_bdist(std::min(1., cfg.expansion_probability*1.5)) {
  }

/**Function*************************************************************

  Synopsis    [Seeds the selection policy's independent random generator.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::setSeed(int seed) {
    rng.seed(seed);
  }

/**Function*************************************************************

  Synopsis    [Samples the configured cut-expansion probability.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  bool RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::getRandomBool() {
    return bdist(rng);
  }

/**Function*************************************************************

  Synopsis    [Samples the increased expansion probability for biased nodes.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  bool RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::getBiasedRandomBool() {
    return biased_bdist(rng);
  }

/**Function*************************************************************

  Synopsis    [Selects the next cut root through the configured root policy.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  int RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::selectRoot() {
    last_root = root_selector.getRoot(rng, &log);
    return last_root;
  }

/**Function*************************************************************

  Synopsis    [Records only a proved-optimal or structurally unchanged selected cut.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::recordFailure() {
    if (last_root >= 0) root_selector.recordFailure(last_root);
  }

/**Function*************************************************************

  Synopsis    [Resets selection state for the current graph.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::reset() {
    root_selector.reset();
    last_root = -1;
  }

/**Function*************************************************************

  Synopsis    [Grows a randomized subcircuit from a selected root.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  std::set<int> RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::computeSubcircuitCandidate() {
    std::set<int> scir;
    int root_id = selectRoot();
    std::queue<int> candidates;
    processCandidateNode(root_id, scir, candidates);
    std::queue<int> rejected_nodes;
    while (!candidates.empty() && scir.size() < cfg.subcircuit_max_size) {
      int c = candidates.front();
      candidates.pop();
      if (CandidateNodeConstraint::check(c, es_man, scir)) {
        bool add_node;
        if ((cfg.depth_floor < 0 || es_man.getDepth() > cfg.depth_floor) &&
            BiasSelector::useBias(es_man, es_man.getObj(c))) {
          add_node = getBiasedRandomBool();
        } else {
          add_node = getRandomBool();
        }
        if (add_node) {
          processCandidateNode(c, scir, candidates);
        } else {
          rejected_nodes.push(c);
        }
      }
    }
    if (this->cfg.fill_subcircuits) {
      while (!rejected_nodes.empty() && scir.size() < cfg.subcircuit_max_size) {
        int c = rejected_nodes.front();
        rejected_nodes.pop();
        if (CandidateNodeConstraint::check(c, es_man, scir)) {
          processCandidateNode(c, scir, rejected_nodes);
        }
      }
    }
    return scir;
  }

/**Function*************************************************************

  Synopsis    [Adds nearby shared-fanin gates to approach the preferred output count.]

  Description [Forward neighbors can merge existing exits; sibling gates can
  expose additional related exits. Rank a bounded set of candidates by shared
  inputs, and accept a step only if it approaches the requested output count
  within the input and gate limits. Full cone and feedback checks follow.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::growOutputBoundary(std::set<int>& nodes) {
    auto outputs = [&](const std::set<int>& gates) {
      unsigned count = 0;
      for (int id : gates) {
        const auto& node = es_man.getObj(id);
        count += std::any_of(node.fanouts.begin(), node.fanouts.end(),
            [&](const eSLIM3CirObj* user) { return !gates.count(user->node_id); });
      }
      return count;
    };
    auto distance = [&](unsigned count) {
      return count < cfg.preferred_outputs ? cfg.preferred_outputs - count : count - cfg.preferred_outputs;
    };
    unsigned current_distance = distance(outputs(nodes));
    while (current_distance && nodes.size() < cfg.subcircuit_max_size && !cfg.expired()) {
      std::set<int> inputs, candidates;
      for (int id : nodes)
        for (auto* input : es_man.getObj(id).fanins)
          if (!es_man.isConst(*input) && !nodes.count(input->node_id)) inputs.insert(input->node_id);
      auto neighbors = [&](int id) {
        unsigned visited = 0;
        for (auto* user : es_man.getObj(id).fanouts) {
          if (++visited > output_growth_fanout_limit) break;
          if (es_man.isGate(user->node_id) && !nodes.count(user->node_id)) candidates.insert(user->node_id);
        }
      };
      for (int id : nodes) neighbors(id);
      for (int id : inputs) neighbors(id);
      std::vector<std::pair<int, int>> ranked;
      for (int id : candidates) {
        int score = 0;
        for (auto* input : es_man.getObj(id).fanins)
          score += nodes.count(input->node_id) ? 4 : inputs.count(input->node_id) ? 2 : 0;
        ranked.emplace_back(-score, id);
      }
      std::sort(ranked.begin(), ranked.end());
      if (ranked.size() > output_growth_candidate_limit) ranked.resize(output_growth_candidate_limit);
      int best = -1;
      unsigned best_distance = current_distance, best_inputs = UINT_MAX;
      for (const auto& item : ranked) {
        if (cfg.expired()) break;
        const int id = item.second;
        if (!CandidateNodeConstraint::check(id, es_man, nodes)) continue;
        auto trial = nodes;
        trial.insert(id);
        const unsigned next_distance = distance(outputs(trial));
        if (next_distance >= current_distance || next_distance > best_distance) continue;
        std::set<int> boundary;
        for (int gate : trial)
          for (auto* input : es_man.getObj(gate).fanins)
            if (!es_man.isConst(*input) && !trial.count(input->node_id)) boundary.insert(input->node_id);
        if (boundary.size() > cfg.cut_input_limit) continue;
        if (best < 0 || next_distance < best_distance || boundary.size() < best_inputs) {
          best = id;
          best_distance = next_distance;
          best_inputs = boundary.size();
        }
      }
      if (best < 0) break;
      nodes.insert(best);
      current_distance = best_distance;
      ++log.output_boundary_gates_added;
    }
  }

/**Function*************************************************************

  Synopsis    [Expands fanout-free fanin cones while retaining every selected cut output.]

  Description [Only gates whose users are all inside the cut can be added.
  Closing a feedback hole that would remove a cut output is deferred, so a
  three-output seed keeps its three observable boundaries during growth.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::growMffcs(std::set<int>& nodes) {
    while (nodes.size() < cfg.subcircuit_max_size && !cfg.expired()) {
      std::set<int> boundary;
      for (int id : nodes)
        for (auto* fanin : es_man.getObj(id).fanins)
          if (es_man.isGate(fanin->node_id) && !nodes.count(fanin->node_id)) boundary.insert(fanin->node_id);
      int best = -1;
      unsigned best_users = 0;
      for (int id : boundary) {
        const auto& node = es_man.getObj(id);
        if (!std::all_of(node.fanouts.begin(), node.fanouts.end(),
            [&](const eSLIM3CirObj* user) { return nodes.count(user->node_id); })) continue;
        auto trial = nodes;
        trial.insert(id);
        const bool hides_output = std::any_of(node.fanins.begin(), node.fanins.end(),
            [&](const eSLIM3CirObj* input) {
              return nodes.count(input->node_id) && std::all_of(input->fanouts.begin(), input->fanouts.end(),
                  [&](const eSLIM3CirObj* user) { return trial.count(user->node_id); });
            });
        if (hides_output) continue;
        std::set<int> inputs;
        for (int gate : trial)
          for (auto* fanin : es_man.getObj(gate).fanins)
            if (!es_man.isConst(*fanin) && !trial.count(fanin->node_id)) inputs.insert(fanin->node_id);
        if (inputs.size() > cfg.cut_input_limit) continue;
        const unsigned users = node.fanouts.size();
        if (best < 0 || users > best_users ||
            (users == best_users && node.depth > es_man.getObj(best).depth)) {
          best = id;
          best_users = users;
        }
      }
      if (best < 0) break;
      nodes.insert(best);
      ++log.mffc_gates_added;
    }
  }

/**Function*************************************************************

  Synopsis    [Restores a chosen candidate's marks and checks its complete boundary constraints.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  Subcircuit RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::finishSelection(
      const std::vector<int>& nodes, int root, bool preferred, bool& status) {
    es_man.incrementTraversalId();
    auto candidate = Subcircuit::getSubcircuitBare(es_man, nodes.begin(), nodes.end());
    candidate.markCones(es_man);
    status = validator.check(candidate);
    if (status) {
      last_root = root;
      if (preferred && candidate.outputs.size() == cfg.preferred_outputs) ++log.preferred_output_hits;
    }
    return candidate;
  }

/**Function*************************************************************

  Synopsis    [Adds a candidate gate and queues adjacent objects for expansion.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::processCandidateNode(int node, std::set<int>& subcircuit, std::queue<int>& candidates) {
    subcircuit.insert(node);
    auto& obj = es_man.getObj(node);
    for (auto it = search_direction.getNextBegin(obj); it != search_direction.getNextEnd(obj); it++) {
      const auto& f = *it;
      if (search_direction.check(*f)) {
        candidates.push(f->node_id);
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Selects a valid subcircuit within the configured trial limits.]

***********************************************************************/
  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  Subcircuit RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::getSubcircuit(bool& status) {
    std::set<int> scir;
    status = false;
    const bool preferred = !std::is_same_v<CandidateNodeConstraint, SingleOutputCandidateNodeConstraint> &&
        cfg.preferred_outputs && cfg.preferred_outputs <= cfg.subcircuit_max_size &&
        ++selection_round % ordinary_selection_interval != 0;
    if (preferred) ++log.preferred_output_selections;
    std::vector<int> best;
    unsigned best_distance = UINT_MAX;
    int best_root = -1;
    for (unsigned i = 0; i < cfg.nselection_trials; i++) {
      if (cfg.expired()) break;
      scir = computeSubcircuitCandidate();
      if (preferred) growOutputBoundary(scir);
      // Keep one quarter of the selections small when output targeting is on.
      // Explicit untargeted MFFC growth (-y 0 without -w) still applies to all cuts.
      if (cfg.grow_mffcs && (preferred || !cfg.preferred_outputs)) growMffcs(scir);
      if (scir.size() < min_size) {
        continue;
      }
      es_man.incrementTraversalId();
      Subcircuit candidate = Subcircuit::getSubcircuitBare(es_man, scir);
      if (!validator.precheck(candidate)) {
        continue;
      }
      const unsigned outputs = candidate.outputs.size();
      const unsigned distance = outputs < cfg.preferred_outputs ? cfg.preferred_outputs - outputs : outputs - cfg.preferred_outputs;
      if (best.empty() || distance < best_distance || (distance == best_distance && candidate.nodes.size() > best.size())) {
        best = candidate.nodes;
        best_root = last_root;
        best_distance = distance;
      }
      if (!preferred || !distance || i + 1 >= preferred_output_trials) {
        auto selected = finishSelection(best, best_root, preferred, status);
        if (status) return selected;
        best.clear();
      }
    }
    if (!best.empty() && !cfg.expired()) return finishSelection(best, best_root, preferred, status);
    return Subcircuit::getEmptySubcircuit();
  }


}
ABC_NAMESPACE_CXX_HEADER_END

#endif
