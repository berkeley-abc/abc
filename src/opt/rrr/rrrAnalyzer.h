#pragma once

#include "rrrParameter.h"
#include "rrrUtils.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  template <typename Ntk, typename Sim, typename Sol>
  class Analyzer {
  private:
    // pointer to network
    Ntk *pNtk;

    // parameters
    bool nVerbose;

    // data
    Sim sim;
    Sol sol;

  public:
    // constructors
    Analyzer(Parameter const *pPar);
    void AssignNetwork(Ntk *pNtk_, bool fReuse);

    // checks
    bool CheckRedundancy(int id, int idx);
    bool CheckFeasibility(int id, int fi, bool c);

    // summary
    void ResetSummary();
    summary<int> GetStatsSummary() const;
    summary<double> GetTimesSummary() const;
  };

  /* {{{ Constructors */
  
  template <typename Ntk, typename Sim, typename Sol>
  Analyzer<Ntk, Sim, Sol>::Analyzer(Parameter const *pPar) :
    pNtk(NULL),
    nVerbose(pPar->nAnalyzerVerbose),
    sim(pPar),
    sol(pPar) {
  }

  template <typename Ntk, typename Sim, typename Sol>
  void Analyzer<Ntk, Sim, Sol>::AssignNetwork(Ntk *pNtk_, bool fReuse) {
    pNtk = pNtk_;
    sim.AssignNetwork(pNtk, fReuse);
    sol.AssignNetwork(pNtk, fReuse);
  }

  /* }}} */

  /* {{{ Checks */
  
  template <typename Ntk, typename Sim, typename Sol>
  bool Analyzer<Ntk, Sim, Sol>::CheckRedundancy(int id, int idx) {
    if(sim.CheckRedundancy(id, idx)) {
      if(nVerbose) {
        std::cout << "node " << id << " fanin " << (pNtk->GetCompl(id, idx)? "!": "") << pNtk->GetFanin(id, idx) << " index " << idx << " seems redundant" << std::endl;
      }
      SatResult r = sol.CheckRedundancy(id, idx);
      if(r == UNSAT) {
        if(nVerbose) {
          std::cout << "node " << id << " fanin " << (pNtk->GetCompl(id, idx)? "!": "") << pNtk->GetFanin(id, idx) << " index " << idx << " is redundant" << std::endl;
        }
        return true;
      }
      if(r == SAT) {
        if(nVerbose) {
          std::cout << "node " << id << " fanin " << (pNtk->GetCompl(id, idx)? "!": "") << pNtk->GetFanin(id, idx) << " index " << idx << " is NOT redundant" << std::endl;
        }
        sim.AddCex(sol.GetCex());
      }
    } else {
      // if(nVerbose) {
      //   std::cout << "node " << id << " fanin " << (pNtk->GetCompl(id, idx)? "!": "") << pNtk->GetFanin(id, idx) << " index " << idx << " is not redundant" << std::endl;
      // }
    }
    return false;
  }
  
  template <typename Ntk, typename Sim, typename Sol>
  bool Analyzer<Ntk, Sim, Sol>::CheckFeasibility(int id, int fi, bool c) {
    if(sim.CheckFeasibility(id, fi, c)) {
      if(nVerbose) {
        std::cout << "node " << id << " fanin " << (c? "!": "") << fi << " seems feasible" << std::endl;
      }
      SatResult r = sol.CheckFeasibility(id, fi, c);
      if(r == UNSAT) {
        if(nVerbose) {
          std::cout << "node " << id << " fanin " << (c? "!": "") << fi << " is feasible" << std::endl;
        }
        return true;
      }
      if(r == SAT) {
        if(nVerbose) {
          std::cout << "node " << id << " fanin " << (c? "!": "") << fi << " is NOT feasible" << std::endl;
        }
        sim.AddCex(sol.GetCex());
      }
    } else {
      // if(nVerbose) {
      //   std::cout << "node " << id << " fanin " << (c? "!": "") << fi << " is not feasible" << std::endl;
      // }
    }
    return false;
  }

  /* }}} */

  /* {{{ Summary */
  
  template <typename Ntk, typename Sim, typename Sol>
  void Analyzer<Ntk, Sim, Sol>::ResetSummary() {
    sim.ResetSummary();
    sol.ResetSummary();
  }
  
  template <typename Ntk, typename Sim, typename Sol>
  summary<int> Analyzer<Ntk, Sim, Sol>::GetStatsSummary() const {
    summary<int> v = sim.GetStatsSummary();
    summary<int> v2 = sol.GetStatsSummary();
    v.insert(v.end(), v2.begin(), v2.end());
    return v;
  }

  template <typename Ntk, typename Sim, typename Sol>
  summary<double> Analyzer<Ntk, Sim, Sol>::GetTimesSummary() const {
    summary<double> v = sim.GetTimesSummary();
    summary<double> v2 = sol.GetTimesSummary();
    v.insert(v.end(), v2.begin(), v2.end());
    return v;
  }

  /* }}} */
  
}

ABC_NAMESPACE_CXX_HEADER_END
