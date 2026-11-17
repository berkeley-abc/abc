/**CFile****************************************************************

  FileName    [selectionStrategies.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Subcircuit selection]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__SELECTIONSTRATEGIES_h
#define ABC__OPT__ESLIM2__SELECTIONSTRATEGIES_h

#include <random>
#include <queue>
#include <set>

#include "misc/util/abc_namespaces.h"

#include "eslim2CirMan.h"
#include "subcircuit.h"
#include "utils.h"
#include "tabooList.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  struct SubcircuitValidator {
    public:
      SubcircuitValidator(const eSLIM2Config& cf);
      // Checks that do not require the TFI/TFO marks or the forbidden pairs,
      // i.e. can be run on a bare subcircuit (created by getSubcircuitBare).
      bool precheck(const Subcircuit& candidate) const;
      bool check(const Subcircuit& candidate) const;

    private:
      const eSLIM2Config& cfg;
      static constexpr unsigned int min_size = 2;

  };

  struct SubcircuitNoFBValidator : public SubcircuitValidator {
    public:
      using SubcircuitValidator::SubcircuitValidator;
      bool check(const Subcircuit& candidate) const;
  };

  class ForwardSearch {
    public:
      ForwardSearch(eSLIM2CirMan& es_man);
      auto getNextBegin(const eSLIM2CirObj& obj);
      auto getNextEnd(const eSLIM2CirObj& obj);
      bool check(const eSLIM2CirObj& obj) const;
    private:
      eSLIM2CirMan& es_man;
  };

  class BackwardSearch {
    public:
      BackwardSearch(eSLIM2CirMan& es_man);
      auto getNextBegin(const eSLIM2CirObj& obj);
      auto getNextEnd(const eSLIM2CirObj& obj);
      bool check(const eSLIM2CirObj& obj) const;
    private:
      eSLIM2CirMan& es_man;
  };

  class BaseRootSelector {
    public:
      BaseRootSelector(eSLIM2CirMan& es_man, const eSLIM2Config& cfg);
      int getRoot(std::mt19937& rng, eSLIM2Log* log = nullptr);
      void reset() {}
      void recordFailure(int node);

    private:
      unsigned int getUniformRandomNumber(std::mt19937& rng, unsigned int lower, unsigned int upper); // requires lower < upper

      eSLIM2CirMan& es_man;
      // const eSLIM2Config& cfg;
      std::uniform_int_distribution<std::mt19937::result_type> udistr;
  };

  class TabooRootSelector {
    public:
      TabooRootSelector(eSLIM2CirMan& es_man, const eSLIM2Config& cfg);
      ~TabooRootSelector();
      int getRoot(std::mt19937& rng, eSLIM2Log* log = nullptr);
      void reset();
      void recordFailure(int node);

    protected:
      eSLIM2CirMan& es_man;
      const eSLIM2Config& cfg;
      TabooList taboo;

  };

  class CriticalPathSelector : public TabooRootSelector {
    public:
      using TabooRootSelector::TabooRootSelector;
      int getRoot(std::mt19937& rng, eSLIM2Log* log = nullptr);
  };

  struct BaseCandidateNodeConstraint {
    static bool check(int to_check, const eSLIM2CirMan& cir, const std::set<int>& subcircuit);
  };

  struct SingleOutputCandidateNodeConstraint {
    static bool check(int to_check, const eSLIM2CirMan& cir, const std::set<int>& subcircuit);
  };

  struct NoBiasSelector {
/**Function*************************************************************

  Synopsis    [Reports whether the selection policy favors the given object.]

***********************************************************************/
    static bool useBias(const eSLIM2CirMan& es_man, const eSLIM2CirObj& obj) {return false;}
  };

  struct CriticalPathBiasSelector {
/**Function*************************************************************

  Synopsis    [Reports whether the selection policy favors the given object.]

***********************************************************************/
    static bool useBias(const eSLIM2CirMan& es_man, const eSLIM2CirObj& obj) {return es_man.isOnCricticalPath(obj);}
  };

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector = NoBiasSelector, typename CandidateNodeConstraint = BaseCandidateNodeConstraint>
  class RandomizedBFSSelection {
    friend struct eSLIM2TestAccess;

    public:
      RandomizedBFSSelection(eSLIM2CirMan& es_man, const eSLIM2Config& cfg, eSLIM2Log& log);
      Subcircuit getSubcircuit(bool& status); // status indicates if the search was successful
      void setSeed(int seed);
      void reset(bool full = true);
      void recordFailure();
      void recordEvaluation();
      bool exhausted() const { return cfg.trial_limit_active && active_roots.empty(); }

      static constexpr bool requiresRemainingTimes() {return std::is_same_v<CriticalPathBiasSelector, BiasSelector>;}

    private:

      std::set<int> computeSubcircuitCandidate();
      void growOutputBoundary(std::set<int>& nodes);
      void growMffcs(std::set<int>& nodes);
      Subcircuit finishSelection(const std::vector<int>& nodes, int root, bool preferred, bool& status);
      int selectRoot();
      bool fitsInputLimit(int node, const std::set<int>& selected) const;
      void processCandidateNode(int candidate, std::set<int>& subcircuit, std::queue<int>& candidates);
      bool getRandomBool();
      bool getBiasedRandomBool();

      eSLIM2CirMan& es_man;
      const eSLIM2Config& cfg;
      static constexpr unsigned int min_size = 2;
      static constexpr unsigned preferred_output_trials = 8;
      static constexpr unsigned ordinary_selection_interval = 4;
      static constexpr unsigned output_growth_candidate_limit = 32;
      static constexpr unsigned output_growth_fanout_limit = 64;

      eSLIM2Log& log;
      Validator validator;
      RootSelector root_selector;
      SearchDirection search_direction;

      std::mt19937 rng;
      std::bernoulli_distribution bdist;
      std::bernoulli_distribution biased_bdist;
      int last_root = -1;
      unsigned selection_round = 0;
      std::vector<int> active_roots, root_positions;
      std::vector<unsigned> root_trials, root_draws;
      struct RootState { ABC_UINT64_T signature = 0; unsigned trials = 0, epoch = 0; };
      std::unordered_map<unsigned, RootState> root_states;
      unsigned root_epoch = 0;
  };



  using RamdomizedBFS=RandomizedBFSSelection<SubcircuitValidator,BaseRootSelector, BackwardSearch>;
  using RamdomizedBFSForward=RandomizedBFSSelection<SubcircuitValidator,BaseRootSelector, ForwardSearch>;
  using RandomizedBFSNoFB=RandomizedBFSSelection<SubcircuitNoFBValidator,BaseRootSelector, BackwardSearch>;
  using RamdomizedBFSTaboo=RandomizedBFSSelection<SubcircuitValidator,TabooRootSelector, BackwardSearch>;
  using RamdomizedBFSTabooForward=RandomizedBFSSelection<SubcircuitValidator,TabooRootSelector, ForwardSearch>;
  using RamdomizedBFSTabooNoFB=RandomizedBFSSelection<SubcircuitNoFBValidator,TabooRootSelector, BackwardSearch>;

  using SingleOutputBFS = RandomizedBFSSelection<SubcircuitValidator,TabooRootSelector, BackwardSearch, NoBiasSelector, SingleOutputCandidateNodeConstraint>;


}
ABC_NAMESPACE_CXX_HEADER_END


#include "selectionStrategiesImpl.h"

#endif
