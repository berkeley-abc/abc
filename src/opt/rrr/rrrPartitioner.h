#pragma once

#include <utility>
#include <map>
#include <tuple>
#include <random>

#include "rrrParameter.h"
#include "rrrUtils.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  template <typename Ntk>
  class Partitioner {
  private:
    // pointer to network
    Ntk *pNtk;

    // parameters
    int nVerbose;
    int nWindowSize;

    // data
    std::map<Ntk *, std::tuple<std::set<int>, std::vector<int>, std::vector<bool>, std::vector<int>>> mSubNtk2Io;
    std::set<int> sBlocked;

    // subroutines
    Ntk *ExtractDisjoint(int id);
    
  public:
    // constructors
    Partitioner(Parameter const *pPar);
    void UpdateNetwork(Ntk *pNtk);

    // APIs
    Ntk *Extract(int iSeed);
    void Insert(Ntk *pSubNtk);
  };

  /* {{{ Subroutines */

  template <typename Ntk>
  Ntk *Partitioner<Ntk>::ExtractDisjoint(int id) {
    // collect neighbor
    assert(!sBlocked.count(id));
    if(nVerbose) {
      std::cout << "extracting with a center node " << id << std::endl;
    }
    int nRadius = 2;
    std::vector<int> vNodes = pNtk->GetNeighbors(id, false, nRadius);
    std::vector<int> vNodesNew = pNtk->GetNeighbors(id, false, nRadius + 1);
    // gradually increase radius until it hits window size limit
    while(int_size(vNodesNew) < nWindowSize) {
      if(int_size(vNodes) == int_size(vNodesNew)) { // already maximum
        break;
      }
      vNodes = vNodesNew;
      nRadius++;
      vNodesNew = pNtk->GetNeighbors(id, false, nRadius + 1);
    }
    std::set<int> sNodes(vNodes.begin(), vNodes.end());
    sNodes.insert(id);
    if(nVerbose) {
      std::cout << "neighbors: " << sNodes << std::endl;
    }
    // remove nodes that are already blocked
    for(std::set<int>::iterator it = sNodes.begin(); it != sNodes.end();) {
      if(sBlocked.count(*it)) {
        it = sNodes.erase(it);
      } else {
        it++;
      }
    }
    if(nVerbose) {
      std::cout << "disjoint neighbors: " << sNodes << std::endl;
    }
    // get tentative window IO
    std::set<int> sInputs, sOutputs;
    for(int id: sNodes) {
      pNtk->ForEachFanin(id, [&](int fi) {
        if(!sNodes.count(fi)) {
          sInputs.insert(fi);
        }
      });
      bool fOutput = false;
      pNtk->ForEachFanout(id, true, [&](int fo) {
        if(!sNodes.count(fo)) {
          fOutput = true;
        }
      });
      if(fOutput) {
        sOutputs.insert(id);
      }
    }
    if(nVerbose) {
      std::cout << "\tinputs: " << sInputs << std::endl;
      std::cout << "\toutputs: " << sOutputs << std::endl;
    }
    // prevent potential loops while ensuring disjointness
    // first by including inner nodes
    std::set<int> sFanouts;
    for(int id: sOutputs) {
      pNtk->ForEachFanout(id, false, [&](int fo) {
        if(!sNodes.count(fo)) {
          sFanouts.insert(fo);
        }
      });
    }
    std::vector<int> vInners = pNtk->GetInners(sFanouts, sInputs);
    while(!vInners.empty()) {
      if(nVerbose) {
        std::cout << "inners: " << vInners << std::endl;
      }
      if(int_size(sNodes) + int_size(vInners) > 2 * nWindowSize) {
        // TODO: parametrize
        break;
      }
      bool fOverlap = false;
      for(int i: vInners) {
        if(sBlocked.count(i)) {
          fOverlap = true;
          break;
        }
      }
      if(fOverlap) {
        break;
      }
      sNodes.insert(vInners.begin(), vInners.end());
      if(nVerbose) {
        std::cout << "new neighbors: " << sNodes << std::endl;
      }
      sInputs.clear();
      sOutputs.clear();
      for(int id: sNodes) {
        pNtk->ForEachFanin(id, [&](int fi) {
          if(!sNodes.count(fi)) {
            sInputs.insert(fi);
          }
        });
        bool fOutput = false;
        pNtk->ForEachFanout(id, true, [&](int fo) {
          if(!sNodes.count(fo)) {
            fOutput = true;
          }
        });
        if(fOutput) {
          sOutputs.insert(id);
        }
      }
      if(nVerbose) {
        std::cout << "\tnew inputs: " << sInputs << std::endl;
        std::cout << "\tnew outputs: " << sOutputs << std::endl;
      }
      sFanouts.clear();
      for(int id: sOutputs) {
        pNtk->ForEachFanout(id, false, [&](int fo) {
          if(!sNodes.count(fo)) {
            sFanouts.insert(fo);
          }
        });
      }
      vInners = pNtk->GetInners(sFanouts, sInputs);
    }
    if(!vInners.empty()) {
      // fall back method by removing TFI of outputs reachable to inputs
      for(int id: sOutputs) {
        if(!sNodes.count(id)) { // already removed
          continue;
        }
        sFanouts.clear();
        pNtk->ForEachFanout(id, false, [&](int fo) {
          if(!sNodes.count(fo)) {
            sFanouts.insert(fo);
          }
        });
        if(pNtk->IsReachable(sFanouts, sInputs)) {
          if(nVerbose) {
            std::cout << id << " is reachable to inputs" << std::endl;
          }
          sNodes.erase(id);
          pNtk->ForEachTfiEnd(id, sInputs, [&](int fi) {
            int r = sNodes.erase(fi);
            assert(r);
          });
          if(nVerbose) {
            std::cout << "new neighbors: " << sNodes << std::endl;
          }
          if(sNodes.empty()) {
            if(nVerbose) {
              std::cout << "IS EMPTY" << std::endl;
            }
            return NULL;
          }
          // recompute inputs
          sInputs.clear();
          for(int id: sNodes) {
            pNtk->ForEachFanin(id, [&](int fi) {
              if(!sNodes.count(fi)) {
                sInputs.insert(fi);
              }
            });
          }
          if(nVerbose) {
            std::cout << "\tnew inputs: " << sInputs << std::endl;
          }
        }
      }
      // recompute outputs
      for(std::set<int>::iterator it = sOutputs.begin(); it != sOutputs.end();) {
        if(!sNodes.count(*it)) {
          it = sOutputs.erase(it);
        } else {
          it++;
        }
      }
      if(nVerbose) {
        std::cout << "\tnew outputs: " << sOutputs << std::endl;
      }
    }
    // ensure outputs of both windows do not reach each other's inputs at the same time
    for(auto const &entry: mSubNtk2Io) {
      if(!pNtk->IsReachable(sOutputs, std::get<1>(entry.second))) {
        continue;
      }
      if(!pNtk->IsReachable(std::get<3>(entry.second), sInputs)) {
        continue;
      }
      if(nVerbose) {
        std::cout << "POTENTIAL LOOPS" << std::endl;
      }
      return NULL;
    }
    if(int_size(sNodes) < nWindowSize / 2) {
      // too small
      // TODO: fix this parameterized
      return NULL;
    }
    // extract by inputs, internals, and outputs (no checks needed in ntk side)
    std::vector<int> vInputs(sInputs.begin(), sInputs.end());
    std::vector<int> vOutputs(sOutputs.begin(), sOutputs.end());
    Ntk *pSubNtk = pNtk->Extract(sNodes, vInputs, vOutputs);
    // return subntk to be modified, while remember IOs
    for(int i: sNodes) {
      sBlocked.insert(i);
    }
    mSubNtk2Io.emplace(pSubNtk, std::make_tuple(std::move(sNodes), std::move(vInputs), std::vector<bool>(vInputs.size()), std::move(vOutputs)));
    return pSubNtk;
  }
  
  /* }}} */

  /* {{{ Constructors */
  
  template <typename Ntk>
  Partitioner<Ntk>::Partitioner(Parameter const *pPar) :
    nVerbose(pPar->nPartitionerVerbose),
    nWindowSize(pPar->nWindowSize) {
  }

  template <typename Ntk>
  void Partitioner<Ntk>::UpdateNetwork(Ntk *pNtk_) {
    pNtk = pNtk_;
  }

  /* }}} */

  /* {{{ APIs */
  
  template <typename Ntk>
  Ntk *Partitioner<Ntk>::Extract(int iSeed) {
    // pick a center node from candidates that do not belong to any other ongoing windows
    std::mt19937 rng(iSeed);
    std::vector<int> vInts = pNtk->GetInts();
    std::shuffle(vInts.begin(), vInts.end(), rng);
    for(int id: vInts) {
      if(!sBlocked.count(id)) {
        Ntk *pSubNtk = ExtractDisjoint(id);
        if(pSubNtk) {
          return pSubNtk;
        }
      }
    }
    return NULL;
  }

  template <typename Ntk>
  void Partitioner<Ntk>::Insert(Ntk *pSubNtk) {
    for(int i: std::get<0>(mSubNtk2Io[pSubNtk])) {
      sBlocked.erase(i);
    }
    std::pair<std::vector<int>, std::vector<bool>> vNewSignals = pNtk->Insert(pSubNtk, std::get<1>(mSubNtk2Io[pSubNtk]), std::get<2>(mSubNtk2Io[pSubNtk]), std::get<3>(mSubNtk2Io[pSubNtk]));
    std::vector<int> &vOldOutputs = std::get<3>(mSubNtk2Io[pSubNtk]);
    std::vector<int> &vNewOutputs = vNewSignals.first;
    std::vector<bool> &vNewCompls = vNewSignals.second;
    // need to remap updated outputs that are used as inputs in other windows
    std::map<int, int> mOutput2Idx;
    for(int idx = 0; idx < int_size(vOldOutputs); idx++) {
      mOutput2Idx[vOldOutputs[idx]] = idx;
    }
    for(auto &entry: mSubNtk2Io) {
      if(entry.first != pSubNtk) {
        std::vector<int> &vInputs = std::get<1>(entry.second);
        std::vector<bool> &vCompls = std::get<2>(entry.second);
        for(int i = 0; i < int_size(vInputs); i++) {
          if(mOutput2Idx.count(vInputs[i])) {
            int idx = mOutput2Idx[vInputs[i]];
            vInputs[i] = vNewOutputs[idx];
            vCompls[i] = vCompls[i] ^ vNewCompls[idx];
          }
        }
      }
    }
    delete pSubNtk;
    mSubNtk2Io.erase(pSubNtk);
  }

  /* }}} */
  
}

ABC_NAMESPACE_CXX_HEADER_END
