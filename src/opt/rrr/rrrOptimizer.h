#pragma once

#include <vector>
#include <map>
#include <iterator>
#include <random>
#include <numeric>
#include <limits>

#include "rrrParameter.h"
#include "rrrTypes.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  template <typename Ntk, typename Ana>
  class Optimizer {
  private:
    // aliases
    using itr = std::vector<int>::iterator;
    using citr = std::vector<int>::const_iterator;
    using ritr = std::vector<int>::reverse_iterator;
    using critr = std::vector<int>::const_reverse_iterator;

    // pointer to network
    Ntk *pNtk;
    
    // parameters
    int nVerbose;
    std::function<double(Ntk *)> CostFunction;
    int nSortType;
    int nFlow;
    seconds nTimeout; // assigned upon Run

    // data
    Ana *pAna;
    std::mt19937 rng;
    std::vector<int> vTmp;
    std::map<int, std::set<int>> mapNewFanins;
    time_point start;

    // fanin sorting data
    std::vector<int> vRandPiOrder;
    std::vector<double> vRandCosts;

    // marks
    int target;
    std::vector<bool> vMarks;
    
    // callback
    void ActionCallback(Action const &action);

    // topology
    void MarkTfo(int id);

    // time
    bool Timeout();

    // sort fanins
    void SetRandPiOrder();
    void SetRandCosts();
    void SortFanins(int id);

    // reduce fanin
    bool ReduceFanin(int id, bool fRemoveUnused = false);
    bool ReduceFaninOneRandom(int id, bool fRemoveUnused = false);

    // reduce
    void Reduce();
    void ReduceRandom();

    // remove redundancy
    void RemoveRedundancy();
    void RemoveRedundancyRandom();

    // addition
    template <typename T>
    T SingleAdd(int id, T begin, T end);
    int  MultiAdd(int id, std::vector<int> const &vCands, int nMax = 0);

    // resub
    void SingleResub(int id, std::vector<int> const &vCands, bool fGreedy = true);
    void MultiResub(int id, std::vector<int> const &vCands, bool fGreedy = true, int nMax = 0);
    
    // apply
    void ApplyReverseTopologically(std::function<void(int)> const &func);
    
  public:
    // constructors
    Optimizer(Ntk *pNtk, Parameter const *pPar, std::function<double(Ntk *)> CostFunction);
    ~Optimizer();
    void UpdateNetwork(Ntk *pNtk_, bool fSame);

    // run
    void Run(seconds nTimeout_ = 0);
    void Randomize();
    
  };

  /* {{{ Callback */
  
  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::ActionCallback(Action const &action) {
    if(nVerbose) {
      PrintAction(action);
    }
    switch(action.type) {
    case REMOVE_FANIN:
      if(action.id != target) {
        target = -1;
      }
      break;
    case REMOVE_UNUSED:
      break;
    case REMOVE_BUFFER:
    case REMOVE_CONST:
      if(action.id == target) {
        target = -1;
      }
      break;
    case ADD_FANIN:
      if(action.id != target) {
        target = -1;
      }
      break;
    case TRIVIAL_COLLAPSE:
      break;
    case TRIVIAL_DECOMPOSE:
      target = -1;
      break;
    case SORT_FANINS:
      break;
    case SAVE:
      break;
    case LOAD:
      //target = -1; // this is not always needed, so do it manually
      break;
    case POP_BACK:
      break;
    default:
      assert(0);
    }
  }

  /* }}} */

  /* {{{ Topology */
  
  template <typename Ntk, typename Ana>
  inline void Optimizer<Ntk, Ana>::MarkTfo(int id) {
    // includes id itself
    if(id == target) {
      return;
    }
    target = id;
    vMarks.clear();
    vMarks.resize(pNtk->GetNumNodes());
    vMarks[id] = true;
    pNtk->ForEachTfo(id, false, [&](int fo) {
      vMarks[fo] = true;
    });
  }

  /* }}} */

  /* {{{ Time */
  
  template <typename Ntk, typename Ana>
  inline bool Optimizer<Ntk, Ana>::Timeout() {
    if(nTimeout) {
      time_point current = GetCurrentTime();
      if(DurationInSeconds(start, current) > nTimeout) {
        return true;
      }
    }
    return false;
  }

  /* }}} */

  /* {{{ Sort fanins */

  template <typename Ntk, typename Ana>
  inline void Optimizer<Ntk, Ana>::SetRandPiOrder() {
    assert(vRandPiOrder.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    if((int)vRandPiOrder.size() != pNtk->GetNumPis()) {
      vRandPiOrder.clear();
      vRandPiOrder.resize(pNtk->GetNumPis());
      std::iota(vRandPiOrder.begin(), vRandPiOrder.end(), 0);
      std::shuffle(vRandPiOrder.begin(), vRandPiOrder.end(), rng);      
    }    
  }

  template <typename Ntk, typename Ana>
  inline void Optimizer<Ntk, Ana>::SetRandCosts() {
    std::uniform_real_distribution<> dis(std::numeric_limits<double>::lowest(), std::numeric_limits<double>::max());
    assert(vRandCosts.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    while((int)vRandCosts.size() < pNtk->GetNumNodes()) {
      vRandCosts.push_back(dis(rng));
    }
  }

  template <typename Ntk, typename Ana>
  inline void Optimizer<Ntk, Ana>::SortFanins(int id) {
    switch(nSortType) {
    case 0: // no sorting
      break;
    case 1: // prioritize internals
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        return !pNtk->IsPi(i) && pNtk->IsPi(j);
      });
      break;
    case 2: // prioritize internals with (reversely) sorted PIs
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return pNtk->GetPiIndex(i) > pNtk->GetPiIndex(j);
        }
        return pNtk->IsPi(j);
      });
      break;
    case 3: // prioritize internals with random PI order
      SetRandPiOrder();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return vRandPiOrder[pNtk->GetPiIndex(i)] > vRandPiOrder[pNtk->GetPiIndex(j)];
        }
        return pNtk->IsPi(j);
      });
      break;
    case 4: // smaller fanout takes larger cost
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        return pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j);
      });
      break;
    case 5: // fanout + PI
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && !pNtk->IsPi(j)) {
          return false;
        }
        if(!pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return true;
        }
        return pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j);
      });
      break;
    case 6: // fanout + sorted PI
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return pNtk->GetPiIndex(i) > pNtk->GetPiIndex(j);
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        return pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j);
      });
      break;
    case 7: // fanout + random PI
      SetRandPiOrder();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return vRandPiOrder[pNtk->GetPiIndex(i)] > vRandPiOrder[pNtk->GetPiIndex(j)];
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        return pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j);
      });
      break;
    case 8: // reverse topological order + PI
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return false;
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        return pNtk->GetIntIndex(i) > pNtk->GetIntIndex(j);
      });
      break;
    case 9: // reverse topological order + sorted PI
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return pNtk->GetPiIndex(i) > pNtk->GetPiIndex(j);
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        return pNtk->GetIntIndex(i) > pNtk->GetIntIndex(j);
      });
      break;
    case 10: // reverse topological order + random PI
      SetRandPiOrder();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return vRandPiOrder[pNtk->GetPiIndex(i)] > vRandPiOrder[pNtk->GetPiIndex(j)];
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        return pNtk->GetIntIndex(i) > pNtk->GetIntIndex(j);
      });
      break;
    case 11: // topo + fanout + PI
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && !pNtk->IsPi(j)) {
          return false;
        }
        if(!pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return true;
        }
        if(pNtk->GetNumFanouts(i) > pNtk->GetNumFanouts(j)) {
          return false;
        }
        if(pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j)) {
          return true;
        }
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return false;
        }
        return pNtk->GetIntIndex(i) > pNtk->GetIntIndex(j);
      });
      break;
    case 12: // topo + fanout + sorted PI
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return pNtk->GetPiIndex(i) > pNtk->GetPiIndex(j);
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        if(pNtk->GetNumFanouts(i) > pNtk->GetNumFanouts(j)) {
          return false;
        }
        if(pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j)) {
          return true;
        }
        return pNtk->GetIntIndex(i) > pNtk->GetIntIndex(j);
      });
      break;
    case 13: // topo + fanout + random PI
      SetRandPiOrder();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return vRandPiOrder[pNtk->GetPiIndex(i)] > vRandPiOrder[pNtk->GetPiIndex(j)];
        }
        if(pNtk->IsPi(i)) {
          return false;
        }
        if(pNtk->IsPi(j)) {
          return true;
        }
        if(pNtk->GetNumFanouts(i) > pNtk->GetNumFanouts(j)) {
          return false;
        }
        if(pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j)) {
          return true;
        }
        return pNtk->GetIntIndex(i) > pNtk->GetIntIndex(j);
      });
      break;
    case 14: // random order
      SetRandCosts();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        return vRandCosts[i] > vRandCosts[j];
      });
      break;
    case 15: // random + PI
      SetRandCosts();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && !pNtk->IsPi(j)) {
          return false;
        }
        if(!pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return true;
        }
        return vRandCosts[i] > vRandCosts[j];
      });
      break;
    case 16: // random + fanout
      SetRandCosts();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->GetNumFanouts(i) > pNtk->GetNumFanouts(j)) {
          return false;
        }
        if(pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j)) {
          return true;
        }
        return vRandCosts[i] > vRandCosts[j];
      });
      break;
    case 17: // random + fanout + PI
      SetRandCosts();
      pNtk->SortFanins(id, [&](int i, bool ci, int j, bool cj) {
        if(pNtk->IsPi(i) && !pNtk->IsPi(j)) {
          return false;
        }
        if(!pNtk->IsPi(i) && pNtk->IsPi(j)) {
          return true;
        }
        if(pNtk->GetNumFanouts(i) > pNtk->GetNumFanouts(j)) {
          return false;
        }
        if(pNtk->GetNumFanouts(i) < pNtk->GetNumFanouts(j)) {
          return true;
        }
        return vRandCosts[i] > vRandCosts[j];
      });
      break;
    default:
      assert(0);
    }
  }
  
  /* }}} */
  
  /* {{{ Reduce fanin */
  
  template <typename Ntk, typename Ana>
  inline bool Optimizer<Ntk, Ana>::ReduceFanin(int id, bool fRemoveUnused) {
    assert(pNtk->GetNumFanouts(id) > 0);
    SortFanins(id);
    bool fRemoved = false;
    for(int idx = 0; idx < pNtk->GetNumFanins(id); idx++) {
      // skip fanins that were just added
      if(mapNewFanins.count(id)) {
        int fi = pNtk->GetFanin(id, idx);
        if(mapNewFanins[id].count(fi)) {
          continue;
        }
      }
      // reduce
      if(pAna->CheckRedundancy(id, idx)) {
        int fi = pNtk->GetFanin(id, idx);
        pNtk->RemoveFanin(id, idx);
        fRemoved = true;
        idx--;
        if(fRemoveUnused && pNtk->GetNumFanouts(fi) == 0) {
          pNtk->RemoveUnused(fi, true);
        }
      }
    }
    return fRemoved;
  }

  template <typename Ntk, typename Ana>
  inline bool Optimizer<Ntk, Ana>::ReduceFaninOneRandom(int id, bool fRemoveUnused) {
    assert(pNtk->GetNumFanouts(id) > 0);
    // generate random order
    vTmp.resize(pNtk->GetNumFanins(id));
    std::iota(vTmp.begin(), vTmp.end(), 0);
    std::shuffle(vTmp.begin(), vTmp.end(), rng);
    for(int idx: vTmp) {
      // skip fanins that were just added
      if(mapNewFanins.count(id)) {
        int fi = pNtk->GetFanin(id, idx);
        if(mapNewFanins[id].count(fi)) {
          continue;
        }
      }
      // reduce
      if(pAna->CheckRedundancy(id, idx)) {
        int fi = pNtk->GetFanin(id, idx);
        pNtk->RemoveFanin(id, idx);
        if(fRemoveUnused && pNtk->GetNumFanouts(fi) == 0) {
          pNtk->RemoveUnused(fi, true);
        }
        return true;
      }
    }
    return false;
  }
  
  // TODO: add a method to minimize the size of fanins (check singles, pairs, trios, and so on)?
  
  /* }}} */
  
  /* {{{ Reduce */

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::Reduce() {
    std::vector<int> vInts = pNtk->GetInts();
    for(critr it = vInts.rbegin(); it != vInts.rend(); it++) {
      if(!pNtk->IsInt(*it)) {
        continue;
      }
      if(pNtk->GetNumFanouts(*it) == 0) {
        pNtk->RemoveUnused(*it);
        continue;
      }
      ReduceFanin(*it);
      if(pNtk->GetNumFanins(*it) <= 1) {
        pNtk->Propagate(*it);
      }
      /*
      if(pNtk->GetNumFanins(*it) == 1) {
        pNtk->RemoveBuffer(*it);
      }
      if(pNtk->GetNumFanins(*it) == 0) {
        pNtk->RemoveConst(*it);
      }
      */
    }
  }

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::ReduceRandom() {
    pNtk->Sweep(false);
    std::vector<int> vInts = pNtk->GetInts();
    std::shuffle(vInts.begin(), vInts.end(), rng);
    for(citr it = vInts.begin(); it != vInts.end(); it++) {
      if(!pNtk->IsInt(*it)) {
        continue;
      }
      if(pNtk->GetNumFanouts(*it) == 0) {
        pNtk->RemoveUnused(*it);
        continue;
      }
      ReduceFanin(*it, true);
      if(pNtk->GetNumFanins(*it) <= 1) {
        pNtk->Propagate(*it);
      }
    }
  }

  /* }}} */

  /* {{{ Redundancy removal */
  
  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::RemoveRedundancy() {
    std::vector<int> vInts = pNtk->GetInts();
    for(critr it = vInts.rbegin(); it != vInts.rend();) {
      if(!pNtk->IsInt(*it)) {
        it++;
        continue;
      }
      if(pNtk->GetNumFanouts(*it) == 0) {
        pNtk->RemoveUnused(*it);
        it++;
        continue;
      }
      bool fReduced = ReduceFanin(*it);
      if(pNtk->GetNumFanins(*it) <= 1) {
        pNtk->Propagate(*it);
      }
      if(fReduced) {
        it = vInts.rbegin();
      } else {
        it++;
      }
    }
  }

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::RemoveRedundancyRandom() {
    pNtk->Sweep(false);
    std::vector<int> vInts = pNtk->GetInts();
    std::shuffle(vInts.begin(), vInts.end(), rng);
    for(citr it = vInts.begin(); it != vInts.end();) {
      if(!pNtk->IsInt(*it)) {
        it++;
        continue;
      }
      if(pNtk->GetNumFanouts(*it) == 0) {
        pNtk->RemoveUnused(*it);
        it++;
        continue;
      }
      bool fReduced = ReduceFaninOneRandom(*it, true);
      if(pNtk->GetNumFanins(*it) <= 1) {
        pNtk->Propagate(*it);
      }
      if(fReduced) {
        std::shuffle(vInts.begin(), vInts.end(), rng);
        it = vInts.begin();
      } else {
        it++;
      }
    }
  }

  /* }}} */

  /* {{{ Addition */

  template <typename Ntk, typename Ana>
  template <typename T>
  T Optimizer<Ntk, Ana>::SingleAdd(int id, T begin, T end) {
    MarkTfo(id);
    pNtk->ForEachFanin(id, [&](int fi, bool c) {
      vMarks[fi] = true;
    });
    T it = begin;
    for(; it != end; it++) {
      if(!pNtk->IsInt(*it) && !pNtk->IsPi(*it)) {
        continue;
      }
      if(vMarks[*it]) {
        continue;
      }
      if(pAna->CheckFeasibility(id, *it, false)) {
        pNtk->AddFanin(id, *it, false);
      } else if(pNtk->UseComplementedEdges() && pAna->CheckFeasibility(id, *it, true)) {
        pNtk->AddFanin(id, *it, true);
      } else {
        continue;
      }
      mapNewFanins[id].insert(*it);
      break;
    }
    pNtk->ForEachFanin(id, [&](int fi, bool c) {
      vMarks[fi] = false;
    });
    return it;
  }

  template <typename Ntk, typename Ana>
  int Optimizer<Ntk, Ana>::MultiAdd(int id, std::vector<int> const &vCands, int nMax) {
    MarkTfo(id);
    pNtk->ForEachFanin(id, [&](int fi, bool c) {
      vMarks[fi] = true;
    });
    int nAdded = 0;
    for(int cand: vCands) {
      if(!pNtk->IsInt(cand) && !pNtk->IsPi(cand)) {
        continue;
      }
      if(vMarks[cand]) {
        continue;
      }
      if(pAna->CheckFeasibility(id, cand, false)) {
        pNtk->AddFanin(id, cand, false);
      } else if(pNtk->UseComplementedEdges() && pAna->CheckFeasibility(id, cand, true)) {
        pNtk->AddFanin(id, cand, true);
      } else {
        continue;
      }
      mapNewFanins[id].insert(cand);
      nAdded++;
      if(nAdded == nMax) {
        break;
      }
    }
    pNtk->ForEachFanin(id, [&](int fi, bool c) {
      vMarks[fi] = false;
    });
    return nAdded;
  }

  /* }}} */
  
  /* {{{ Resub */

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::SingleResub(int id, std::vector<int> const &vCands, bool fGreedy) {
    // NOTE: this assumes trivial collapse/decompose does not change cost
    // let us assume the node is not trivially redundant for now
    assert(pNtk->GetNumFanouts(id) != 0);
    assert(pNtk->GetNumFanins(id) > 1);
    // collapse
    pNtk->TrivialCollapse(id);
    // save if wanted
    int slot;
    if(fGreedy) {
      slot = pNtk->Save();
    }
    double dCost = CostFunction(pNtk);
    // main loop
    for(citr it = vCands.begin(); it != vCands.end(); it++) {
      if(Timeout()) {
        break;
      }
      if(!pNtk->IsInt(id)) {
        break;
      }
      it = SingleAdd<citr>(id, it, vCands.end());
      if(it == vCands.end()) {
        break;
      }
      RemoveRedundancy();
      mapNewFanins.clear();
      double dNewCost = CostFunction(pNtk);
      if(nVerbose) {
        std::cout << "cost: " << dCost << " -> " << dNewCost << std::endl;
      }
      if(fGreedy) {
        if(dNewCost <= dCost) {
          pNtk->Save(slot);
          dCost = dNewCost;
        } else {
          pNtk->Load(slot);
        }
      } else {
        dCost = dNewCost;
      }
    }
    if(pNtk->IsInt(id)) {
      pNtk->TrivialDecompose(id);
    }
    if(fGreedy) {
      pNtk->PopBack();
    }
  }

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::MultiResub(int id, std::vector<int> const &vCands, bool fGreedy, int nMax) {
    // NOTE: this assumes trivial collapse/decompose does not change cost
    // let us assume the node is not trivially redundant for now
    assert(pNtk->GetNumFanouts(id) != 0);
    assert(pNtk->GetNumFanins(id) > 1);
    // save if wanted
    int slot;
    if(fGreedy) {
      slot = pNtk->Save();
    }
    double dCost = CostFunction(pNtk);
    // collapse
    pNtk->TrivialCollapse(id);
    // resub
    MultiAdd(id, vCands, nMax);
    RemoveRedundancy();
    mapNewFanins.clear();
    RemoveRedundancy();
    double dNewCost = CostFunction(pNtk);
    if(nVerbose) {
      std::cout << "cost: " << dCost << " -> " << dNewCost << std::endl;
    }
    if(fGreedy && dNewCost > dCost) {
      pNtk->Load(slot);
    }
    if(pNtk->IsInt(id)) {
      pNtk->TrivialDecompose(id);
    }
    if(fGreedy) {
      pNtk->PopBack();
    }
  }
  
  /* }}} */

  /* {{{ Apply */

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::ApplyReverseTopologically(std::function<void(int)> const &func) {
    std::vector<int> vInts = pNtk->GetInts();
    for(critr it = vInts.rbegin(); it != vInts.rend(); it++) {
      if(Timeout()) {
        break;
      }
      if(!pNtk->IsInt(*it)) {
        continue;
      }
      if(nVerbose) {
        std::cout << "node " << *it << " (" << std::distance(vInts.crbegin(), it) + 1 << "/" << vInts.size() << ")" << std::endl;
      }
      func(*it);
    }
  }
  
  /* }}} */
  
  /* {{{ Constructors */
  
  template <typename Ntk, typename Ana>
  Optimizer<Ntk, Ana>::Optimizer(Ntk *pNtk, Parameter const *pPar, std::function<double(Ntk *)> CostFunction) :
    pNtk(pNtk),
    nVerbose(pPar->nOptimizerVerbose),
    CostFunction(CostFunction),
    nSortType(pPar->nSortType),
    nFlow(pPar->nOptimizerFlow),
    target(-1) {
    pNtk->AddCallback(std::bind(&Optimizer<Ntk, Ana>::ActionCallback, this, std::placeholders::_1));
    pAna = new Ana(pNtk, pPar);
    rng.seed(pPar->iSeed);
  }
  
  template <typename Ntk, typename Ana>
  Optimizer<Ntk, Ana>::~Optimizer() {
    delete pAna;
  }
  
  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::UpdateNetwork(Ntk *pNtk_, bool fSame) {
    pNtk = pNtk_;
    target = -1;
    pNtk->AddCallback(std::bind(&Optimizer<Ntk, Ana>::ActionCallback, this, std::placeholders::_1));
    pAna->UpdateNetwork(pNtk, fSame);
  }
  
  /* }}} */

  /* {{{ Run */

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::Run(seconds nTimeout_) {
    nTimeout = nTimeout_;
    start = GetCurrentTime();
    switch(nFlow) {
    case 0:
      RemoveRedundancy();
      ApplyReverseTopologically([&](int id) {
        std::vector<int> vCands = pNtk->GetPisInts();
        SingleResub(id, vCands);
      });
      break;
    case 1:
      RemoveRedundancy();
      ApplyReverseTopologically([&](int id) {
        std::vector<int> vCands = pNtk->GetInts();
        MultiResub(id, vCands);
      });
      break;
    case 2: {
      RemoveRedundancy();
      double dCost = CostFunction(pNtk);
      while(true) {
        ApplyReverseTopologically([&](int id) {
          std::vector<int> vCands = pNtk->GetPisInts();
          SingleResub(id, vCands);
        });
        ApplyReverseTopologically([&](int id) {
          std::vector<int> vCands = pNtk->GetInts();
          MultiResub(id, vCands);
        });
        double dNewCost = CostFunction(pNtk);
        if(dNewCost < dCost) {
          dCost = dNewCost;
        } else {
          break;
        }
      }
      break;
    }
    default:
      assert(0);
    }
  }

  template <typename Ntk, typename Ana>
  void Optimizer<Ntk, Ana>::Randomize() {
    nSortType = rng() % 18;
    vRandPiOrder.clear();
    vRandCosts.clear();
  }
  
  /* }}} */
  
}

ABC_NAMESPACE_CXX_HEADER_END
