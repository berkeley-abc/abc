/**CFile****************************************************************

  FileName    [selectionStrategies.tpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Subcircuit selection]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include "selectionStrategies.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  inline SubcircuitValidator::SubcircuitValidator(const eSLIMConfig& cfg) : cfg(cfg) {

  }

  inline bool SubcircuitValidator::precheck(const Subcircuit& candidate) const {
    return candidate.inputs.size() <= max_ninputs && candidate.inputs.size() >= cfg.gate_size;
  }

  inline bool SubcircuitValidator::check(const Subcircuit& candidate) const {
    return precheck(candidate);
  }

  inline bool SubcircuitNoFBValidator::check(const Subcircuit& candidate) const {
    return SubcircuitValidator::check(candidate) && candidate.forbidden_pairs.empty();
  }

  inline ForwardSearch::ForwardSearch(eSLIMCirMan& es_man) : es_man(es_man) {
  }

  inline auto ForwardSearch::getNextBegin(const eSLIMCirObj& obj) {
    return obj.fanouts.begin();
  }

  inline auto ForwardSearch::getNextEnd(const eSLIMCirObj& obj) {
    return obj.fanouts.end();
  }

  inline bool ForwardSearch::check(const eSLIMCirObj& obj) const {
    return !es_man.isPo(obj.node_id);
  }

  inline BackwardSearch::BackwardSearch(eSLIMCirMan& es_man) : es_man(es_man) {
  }

  inline auto BackwardSearch::getNextBegin(const eSLIMCirObj& obj) {
    return obj.fanins.begin();
  }

  inline auto BackwardSearch::getNextEnd(const eSLIMCirObj& obj) {
    return obj.fanins.end();
  }

  inline bool BackwardSearch::check(const eSLIMCirObj& obj) const {
    return !es_man.isPi(obj.node_id);
  }

  // inline BaseRootSelector::BaseRootSelector(eSLIMCirMan& es_man, const eSLIMConfig& cfg) : es_man(es_man), cfg(cfg) {
  inline BaseRootSelector::BaseRootSelector(eSLIMCirMan& es_man, const eSLIMConfig& cfg) : es_man(es_man) {

  }

  inline TabooRootSelector::TabooRootSelector(eSLIMCirMan& es_man, const eSLIMConfig& cfg) : es_man(es_man), cfg(cfg), taboo(es_man) {
    es_man.registerTabooList(&taboo);
  }

  inline TabooRootSelector::~TabooRootSelector() {
    es_man.unregisterTabooList();
  }


  inline unsigned int BaseRootSelector::getUniformRandomNumber(std::mt19937& rng, unsigned int lower, unsigned int upper) {
    udistr.param(std::uniform_int_distribution<std::mt19937::result_type>::param_type(lower, upper));
    return udistr(rng);
  }

  inline int BaseRootSelector::getRoot(std::mt19937& rng) {
    int min_id = es_man.getNofPis() + 1;
    int max_id = es_man.getNofObjs() - es_man.getNofPos() - 1;
    return  getUniformRandomNumber(rng, min_id, max_id);
  }


  inline int TabooRootSelector::getRoot(std::mt19937& rng) {
    return taboo.getRandomNonTaboo(rng, cfg.taboo_ratio, cfg.taboo_time);
  }

  inline void TabooRootSelector::reset() {
    taboo.reset();
    es_man.registerTabooList(&taboo);
  }

  inline int CriticalPathSelector::getRoot(std::mt19937& rng) {
    return taboo.getBiasedRandomNonTaboo<CriticalPathBiasSelector>(rng, cfg.bias, cfg.taboo_ratio, cfg.taboo_time);
  }
  
  inline bool BaseCandidateNodeConstraint::check(int to_check, const eSLIMCirMan& cir, const std::set<int>& subcircuit) { 
    return subcircuit.find(to_check) == subcircuit.end();
  }

  inline bool SingleOutputCandidateNodeConstraint::check(int to_check, const eSLIMCirMan& cir, const std::set<int>& subcircuit) {
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

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::RandomizedBFSSelection(eSLIMCirMan& es_man, const eSLIMConfig& cfg, eSLIMLog& log)
                                                                  : es_man(es_man), cfg(cfg), log(log), validator(cfg), root_selector(es_man, cfg), search_direction(es_man), 
                                                                    bdist(cfg.expansion_probability), biased_bdist(std::min(1., cfg.expansion_probability*1.5)) {
  }

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::setSeed(int seed) {
    rng.seed(seed);
  }

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  bool RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::getRandomBool() {
    return bdist(rng);
  }

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  bool RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::getBiasedRandomBool() {
    return biased_bdist(rng);
  }

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  int RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::selectRoot() {
    return root_selector.getRoot(rng);
  }

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  void RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::reset() {
    root_selector.reset();
  }

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
        if (BiasSelector::useBias(es_man, es_man.getObj(c))) {
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

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector, typename CandidateNodeConstraint>
  Subcircuit RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector, CandidateNodeConstraint>::getSubcircuit(bool& status) {
    std::set<int> scir;
    status = false;
    for (int i = 0; i < cfg.nselection_trials; i++) {
      scir = computeSubcircuitCandidate();
      if (scir.size() < min_size) {
        continue;
      }
      es_man.incrementTraversalId();
      Subcircuit candidate = Subcircuit::getSubcircuitBare(es_man, scir);
      if (!validator.precheck(candidate)) {
        continue;
      }
      candidate.markCones(es_man);
      if (validator.check(candidate)) {
        status = true;
        return candidate;
      }
    }
    return Subcircuit::getEmptySubcircuit();
  }


}
ABC_NAMESPACE_CXX_HEADER_END