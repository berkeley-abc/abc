/**CFile****************************************************************

  FileName    [selectionStrategies.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Subcircuit selection]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM__SELECTIONSTRATEGIES_hpp
#define ABC__OPT__ESLIM__SELECTIONSTRATEGIES_hpp

#include <random>
#include <queue>
#include <set>

#include "misc/util/abc_namespaces.h"

#include "eslimCirMan.hpp"
#include "subcircuit.hpp"
#include "utils.hpp"
#include "tabooList.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  struct SubcircuitValidator {
    public:
      SubcircuitValidator(const eSLIMConfig& cf);
      // Checks that do not require the TFI/TFO marks or the forbidden pairs,
      // i.e. can be run on a bare subcircuit (created by getSubcircuitBare).
      bool precheck(const Subcircuit& candidate) const;
      bool check(const Subcircuit& candidate) const;

    private:
      const eSLIMConfig& cfg;
      static constexpr unsigned int min_size = 2;
      static constexpr unsigned int max_ninputs = 10;

  };

  struct SubcircuitNoFBValidator : public SubcircuitValidator {
    public:
      using SubcircuitValidator::SubcircuitValidator;
      bool check(const Subcircuit& candidate) const;
  };

  class ForwardSearch {
    public:
      ForwardSearch(eSLIMCirMan& es_man);
      auto getNextBegin(const eSLIMCirObj& obj);
      auto getNextEnd(const eSLIMCirObj& obj);
      bool check(const eSLIMCirObj& obj) const;
    private:
      eSLIMCirMan& es_man;
  };

  class BackwardSearch {
    public:
      BackwardSearch(eSLIMCirMan& es_man);
      auto getNextBegin(const eSLIMCirObj& obj);
      auto getNextEnd(const eSLIMCirObj& obj);
      bool check(const eSLIMCirObj& obj) const;
    private:
      eSLIMCirMan& es_man;
  };

  class BaseRootSelector {
    public:
      BaseRootSelector(eSLIMCirMan& es_man, const eSLIMConfig& cfg);
      int getRoot(std::mt19937& rng);
      void reset() {}

    private:
      unsigned int getUniformRandomNumber(std::mt19937& rng, unsigned int lower, unsigned int upper); // requires lower < upper

      eSLIMCirMan& es_man; 
      // const eSLIMConfig& cfg;
      std::uniform_int_distribution<std::mt19937::result_type> udistr;
  };

  class TabooRootSelector {
    public:
      TabooRootSelector(eSLIMCirMan& es_man, const eSLIMConfig& cfg);
      ~TabooRootSelector();
      int getRoot(std::mt19937& rng);
      void reset();

    private:
      eSLIMCirMan& es_man; 
      

    protected:
      const eSLIMConfig& cfg;
      TabooList taboo;
      
  };

  class CriticalPathSelector : public TabooRootSelector {
    public:
      using TabooRootSelector::TabooRootSelector;
      int getRoot(std::mt19937& rng);
  };

  struct BaseCandidateNodeConstraint {
    static bool check(int to_check, const eSLIMCirMan& cir, const std::set<int>& subcircuit);
  };

  struct SingleOutputCandidateNodeConstraint {
    static bool check(int to_check, const eSLIMCirMan& cir, const std::set<int>& subcircuit);
  };

  struct NoBiasSelector {
    static bool useBias(const eSLIMCirMan& es_man, const eSLIMCirObj& obj) {return false;}
  };

  struct CriticalPathBiasSelector {
    static bool useBias(const eSLIMCirMan& es_man, const eSLIMCirObj& obj) {return es_man.isOnCricticalPath(obj);}
  };

  template <typename Validator, typename RootSelector, typename SearchDirection, typename BiasSelector = NoBiasSelector, typename CandidateNodeConstraint = BaseCandidateNodeConstraint>
  class RandomizedBFSSelection {

    public:
      RandomizedBFSSelection(eSLIMCirMan& es_man, const eSLIMConfig& cfg, eSLIMLog& log);
      Subcircuit getSubcircuit(bool& status); // status indicates if the search was successful
      void setSeed(int seed);
      void reset();

      static constexpr bool requiresRemainingTimes() {return std::is_same_v<CriticalPathBiasSelector, BiasSelector>;}

    private:

      std::set<int> computeSubcircuitCandidate(); 
      int selectRoot();
      void processCandidateNode(int candidate, std::set<int>& subcircuit, std::queue<int>& candidates);
      bool getRandomBool();
      bool getBiasedRandomBool();

      eSLIMCirMan& es_man;
      const eSLIMConfig& cfg;
      static constexpr unsigned int min_size = 2;
      static constexpr unsigned int max_ninputs = 10;
      
      eSLIMLog& log;
      Validator validator;
      RootSelector root_selector;
      SearchDirection search_direction;
      
      std::mt19937 rng;
      std::bernoulli_distribution bdist;
      std::bernoulli_distribution biased_bdist;
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


#include "selectionStrategies.tpp"

#endif