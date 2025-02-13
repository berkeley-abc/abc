#pragma once

#include <iostream>
#include <vector>
#include <list>
#include <set>
#include <initializer_list>
#include <string>
#include <functional>
#include <algorithm>
#include <limits>

#include "rrrParameter.h"
#include "rrrTypes.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  class AndNetwork {
  private:
    // aliases
    using itr = std::list<int>::iterator;
    using citr = std::list<int>::const_iterator;
    using ritr = std::list<int>::reverse_iterator;
    using critr = std::list<int>::const_reverse_iterator;
    using Callback = std::function<void(Action const &)>;

    // network data
    int nNodes; // number of allocated nodes
    std::vector<int> vPis;
    std::list<int> lInts; // internal nodes in topological order
    std::set<int> sInts; // internal nodes as a set
    std::vector<int> vPos;
    std::vector<std::vector<int>> vvFaninEdges; // complementable edges, no duplicated fanins allowed (including complements), and nodes without fanins are treated as const-1
    std::vector<int> vRefs; // reference count (number of fanouts)

    // mark for network traversal
    bool fLockTrav;
    unsigned iTrav;
    std::vector<unsigned> vTrav;

    // flag used during constant propagation
    bool fPropagating;

    // callback functions
    std::vector<Callback> vCallbacks;

    // network backups
    std::vector<AndNetwork> vBackups;

    // conversion between node and edge
    int  Node2Edge(int id, bool c) const { return (id << 1) + (int)c; }
    int  Edge2Node(int f)          const { return f >> 1;             }
    bool EdgeIsCompl(int f)        const { return f & 1;              }

    // other private functions
    int  CreateNode();
    void SortInts(itr it);
    void StartTraversal();
    void EndTraversal();
    void TakenAction(Action const &action) const;

  public:
    // constructors
    AndNetwork();
    AndNetwork(AndNetwork const &x);
    AndNetwork &operator=(AndNetwork const &x);

    // initialization APIs (should not be called after optimization has started)
    void Clear();
    void Reserve(int nReserve);
    int  AddPi();
    int  AddPo(int id, bool c);
    int  AddAnd(int id0, int id1, bool c0, bool c1);
    template <typename Ntk, typename Reader>
    void Read(Ntk *pFrom, Reader &reader);

    // network properties
    bool UseComplementedEdges() const;
    int  GetNumNodes() const; // number of allocated nodes (max id + 1)
    int  GetNumPis() const;
    int  GetNumInts() const;
    int  GetNumPos() const;
    int  GetConst0() const;
    int  GetPi(int idx) const;
    std::vector<int> GetPis() const;
    std::vector<int> GetInts() const;
    std::vector<int> GetPisInts() const;
    std::vector<int> GetPos() const;
    
    // node properties
    bool IsPi(int id) const;
    bool IsInt(int id) const;
    bool IsPo(int id) const;
    NodeType GetNodeType(int id) const;
    bool IsPoDriver(int id) const;
    int  GetPiIndex(int id) const;
    int  GetIntIndex(int id) const;
    int  GetPoIndex(int id) const;
    int  GetNumFanins(int id) const;
    int  GetNumFanouts(int id) const;
    int  GetFanin(int id, int idx) const;
    bool GetCompl(int id, int idx) const;
    int  FindFanin(int id, int fi) const;
    bool IsReconvergent(int id);

    // network traversal
    void ForEachPi(std::function<void(int)> const &func) const;
    void ForEachInt(std::function<void(int)> const &func) const;
    void ForEachIntReverse(std::function<void(int)> const &func) const;
    void ForEachPo(std::function<void(int)> const &func) const;
    void ForEachPoDriver(std::function<void(int, bool)> const &func) const;
    void ForEachFanin(int id, std::function<void(int, bool)> const &func) const;
    void ForEachFaninIdx(int id, std::function<void(int, int, bool)> const &func) const; // func(fi, c, index of fi in fanin list of id)
    void ForEachFanout(int id, bool fPos, std::function<void(int, bool)> const &func) const;
    void ForEachFanoutRidx(int id, bool fPos, std::function<void(int, bool, int)> const &func) const; // func(fo, c, index of id in fanin list of fo)
    void ForEachTfo(int id, bool fPos, std::function<void(int)> const &func);
    void ForEachTfoReverse(int id, bool fPos, std::function<void(int)> const &func);
    void ForEachTfoUpdate(int id, bool fPos, std::function<bool(int)> const &func);
    template <template <typename...> typename Container, typename ... Ts>
    void ForEachTfos(Container<Ts...> const &ids, bool fPos, std::function<void(int)> const &func);
    template <template <typename...> typename Container, typename ... Ts>
    void ForEachTfosUpdate(Container<Ts...> const &ids, bool fPos, std::function<bool(int)> const &func);

    // Actions
    void RemoveFanin(int id, int idx);
    void RemoveUnused(int id, bool fRecursive = false);
    void RemoveBuffer(int id);
    void RemoveConst(int id);
    void AddFanin(int id, int fi, bool c);
    void TrivialCollapse(int id);
    void TrivialDecompose(int id);
    void SortFanins(int id, std::function<bool(int, bool, int, bool)> const &cost);

    // Network cleanup
    void Propagate(int id = -1); // all nodes unless specified
    void Sweep(bool fPropagate);

    // save & load
    int  Save(int slot = -1); // slot is assigned automatically unless specified
    void Load(int slot);
    void PopBack(); // deletes the last entry of backups

    // misc
    void AddCallback(Callback const &callback);
    void Print() const;
  };

  /* {{{ Private functions */

  inline int AndNetwork::CreateNode() {
    // TODO: reuse already allocated but dead nodes? or perform garbage collection?
    vvFaninEdges.emplace_back();
    vRefs.push_back(0);
    assert(nNodes != std::numeric_limits<int>::max());
    return nNodes++;
  }

  void AndNetwork::SortInts(itr it) {
    ForEachFanin(*it, [&](int fi, bool c) {
      itr it2 = std::find(it, lInts.end(), fi);
      if(it2 != lInts.end()) {
        lInts.erase(it2);
        it2 = lInts.insert(it, fi);
        SortInts(it2);
      }
    });
  }

  inline void AndNetwork::StartTraversal() {
    assert(!fLockTrav);
    fLockTrav = true;
    vTrav.resize(nNodes);
    iTrav++;
    assert(iTrav != 0); //TODO: handle this overflow
  }
  
  inline void AndNetwork::EndTraversal() {
    assert(fLockTrav);
    fLockTrav = false;
  }
  
  inline void AndNetwork::TakenAction(Action const &action) const {
    for(Callback const &callback: vCallbacks) {
      callback(action);
    }
  }

  /* }}} */

  /* {{{ Constructors */

  AndNetwork::AndNetwork() :
    nNodes(0),
    fLockTrav(false),
    iTrav(0),
    fPropagating(false) {
    // add constant node
    vvFaninEdges.emplace_back();
    vRefs.push_back(0);
    nNodes++;
  }

  AndNetwork::AndNetwork(AndNetwork const &x) :
    fLockTrav(false),
    iTrav(0),
    fPropagating(false) {
    nNodes       = x.nNodes;
    vPis         = x.vPis;
    lInts        = x.lInts;
    sInts        = x.sInts;
    vPos         = x.vPos;
    vvFaninEdges = x.vvFaninEdges;
    vRefs        = x.vRefs;
  }
  
  AndNetwork &AndNetwork::operator=(AndNetwork const &x) {
    nNodes       = x.nNodes;
    vPis         = x.vPis;
    lInts        = x.lInts;
    sInts        = x.sInts;
    vPos         = x.vPos;
    vvFaninEdges = x.vvFaninEdges;
    vRefs        = x.vRefs;
    return *this;
  }
  
  /* }}} */

  /* {{{ Initialization APIs */

  void AndNetwork::Clear() {
    nNodes = 0;
    vPis.clear();
    lInts.clear();
    sInts.clear();
    vPos.clear();
    vvFaninEdges.clear();
    vRefs.clear();
    fLockTrav = false;
    iTrav = 0;
    vTrav.clear();
    fPropagating = false;
    vCallbacks.clear();
    vBackups.clear();
    // add constant node
    vvFaninEdges.emplace_back();
    vRefs.push_back(0);
    nNodes++;
  }

  void AndNetwork::Reserve(int nReserve) {
    vvFaninEdges.reserve(nReserve);
    vRefs.reserve(nReserve);
  }
  
  inline int AndNetwork::AddPi() {
    vPis.push_back(nNodes);
    vvFaninEdges.emplace_back();
    vRefs.push_back(0);
    assert(nNodes != std::numeric_limits<int>::max());
    return nNodes++;
  }
  
  inline int AndNetwork::AddAnd(int id0, int id1, bool c0, bool c1) {
    assert(id0 < nNodes);
    assert(id1 < nNodes);
    assert(id0 != id1);
    lInts.push_back(nNodes);
    sInts.insert(nNodes);
    vRefs[id0]++;
    vRefs[id1]++;
    vvFaninEdges.emplace_back(std::initializer_list<int>({Node2Edge(id0, c0), Node2Edge(id1, c1)}));
    vRefs.push_back(0);
    assert(nNodes != std::numeric_limits<int>::max());
    return nNodes++;
  }

  inline int AndNetwork::AddPo(int id, bool c) {
    assert(id < nNodes);
    vPos.push_back(nNodes);
    vRefs[id]++;
    vvFaninEdges.emplace_back(std::initializer_list<int>({Node2Edge(id, c)}));
    vRefs.push_back(0);
    assert(nNodes != std::numeric_limits<int>::max());
    return nNodes++;
  }

  template <typename Ntk, typename Reader>
  void AndNetwork::Read(Ntk *pFrom, Reader &reader) {
    Clear();
    reader(pFrom, this);
  }
  
  /* }}} */
  
  /* {{{ Network properties */
  
  inline bool AndNetwork::UseComplementedEdges() const {
    return true;
  }
  
  inline int AndNetwork::GetNumNodes() const {
    return nNodes;
  }

  inline int AndNetwork::GetNumPis() const {
    assert(vPis.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    return vPis.size();
  }
  
  inline int AndNetwork::GetNumInts() const {
    assert(lInts.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    return lInts.size();
  }
  
  inline int AndNetwork::GetNumPos() const {
    assert(vPos.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    return vPos.size();
  }

  inline int AndNetwork::GetConst0() const {
    return 0;
  }
  
  inline int AndNetwork::GetPi(int idx) const {
    return vPis[idx];
  }

  inline std::vector<int> AndNetwork::GetPis() const {
    return vPis;
  }

  inline std::vector<int> AndNetwork::GetInts() const {
    return std::vector<int>(lInts.begin(), lInts.end());
  }
  
  inline std::vector<int> AndNetwork::GetPisInts() const {
    std::vector<int> vPisInts = vPis;
    vPisInts.insert(vPisInts.end(), lInts.begin(), lInts.end());
    return vPisInts;
  }
  
  inline std::vector<int> AndNetwork::GetPos() const {
    return vPos;
  }
  
  /* }}} */

  /* {{{ Node properties */
  
  inline bool AndNetwork::IsPi(int id) const {
    return GetNumFanins(id) == 0 && std::find(vPis.begin(), vPis.end(), id) != vPis.end();
  }

  inline bool AndNetwork::IsInt(int id) const {
    return sInts.count(id);
  }

  inline bool AndNetwork::IsPo(int id) const {
    return GetNumFanouts(id) == 0 && std::find(vPos.begin(), vPos.end(), id) != vPos.end();
  }
  
  inline NodeType AndNetwork::GetNodeType(int id) const {
    if(IsPi(id)) {
      return PI;
    }
    if(IsPo(id)) {
      return PO;
    }
    return AND;
  }

  inline bool AndNetwork::IsPoDriver(int id) const {
    for(int po: vPos) {
      if(GetFanin(po, 0) == id) {
        return true;
      }
    }
    return false;
  }

  int AndNetwork::GetPiIndex(int id) const {
    assert(IsPi(id));
    assert(vPis.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    std::vector<int>::const_iterator it = std::find(vPis.begin(), vPis.end(), id);
    assert(it != vPis.end());
    return std::distance(vPis.begin(), it);
  }
  
  int AndNetwork::GetIntIndex(int id) const {
    int index = 0;
    citr it = lInts.begin();
    for(; it != lInts.end(); it++) {
      if(*it == id) {
        break;
      }
      assert(index < (std::vector<int>::size_type)std::numeric_limits<int>::max());
      index++;
    }
    assert(it != lInts.end());
    return index;
  }

  int AndNetwork::GetPoIndex(int id) const {
    assert(IsPo(id));
    assert(vPos.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    std::vector<int>::const_iterator it = std::find(vPos.begin(), vPos.end(), id);
    assert(it != vPos.end());
    return std::distance(vPos.begin(), it);
  }
  
  inline int AndNetwork::GetNumFanins(int id) const {
    //assert(vvFaninEdges[id].size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    return vvFaninEdges[id].size();
  }

  inline int AndNetwork::GetNumFanouts(int id) const {
    return vRefs[id];
  }

  inline int AndNetwork::GetFanin(int id, int idx) const {
    return Edge2Node(vvFaninEdges[id][idx]);
  }

  inline bool AndNetwork::GetCompl(int id, int idx) const {
    return EdgeIsCompl(vvFaninEdges[id][idx]);
  }

  inline int AndNetwork::FindFanin(int id, int fi) const {
    for(int idx = 0; idx < GetNumFanins(id); idx++) {
      if(GetFanin(id, idx) == fi) {
        return idx;
      }
    }
    return -1;
  }
  
  inline bool AndNetwork::IsReconvergent(int id) {
    if(GetNumFanouts(id) <= 1) {
      return false;
    }
    StartTraversal();
    unsigned iTravStart = iTrav;
    ForEachFanout(id, false, [&](int fo, bool c) {
      vTrav[fo] = iTrav;
      iTrav++;
      assert(iTrav != 0); //TODO: handle this overflow
    });
    iTrav--;
    if(iTrav <= iTravStart) {
      // less than one fanouts excluding POs
      EndTraversal();
      return false;
    }
    citr it = lInts.begin();
    while(vTrav[*it] < iTravStart && it != lInts.end()) {
      it++;
    }
    it++;
    for(; it != lInts.end(); it++) {
      for(int fi_edge: vvFaninEdges[*it]) {
        int fi = Edge2Node(fi_edge);
        if(vTrav[fi] >= iTravStart) {
          if(vTrav[*it] >= iTravStart && vTrav[*it] != vTrav[fi]) {
            EndTraversal();
            return true;
          }
          vTrav[*it] = vTrav[fi];
        }
      }
    }
    EndTraversal();
    return false;
  }

  /* }}} */

  /* {{{ Network traversal */

  inline void AndNetwork::ForEachPi(std::function<void(int)> const &func) const {
    for(int pi: vPis) {
      func(pi);
    }
  }
  
  inline void AndNetwork::ForEachInt(std::function<void(int)> const &func) const {
    for(int id: lInts) {
      func(id);
    }
  }

  inline void AndNetwork::ForEachIntReverse(std::function<void(int)> const &func) const {
    for(critr it = lInts.rbegin(); it != lInts.rend(); it++) {
      func(*it);
    }
  }

  inline void AndNetwork::ForEachPo(std::function<void(int)> const &func) const {
    for(int po: vPos) {
      func(po);
    }
  }
  
  inline void AndNetwork::ForEachPoDriver(std::function<void(int, bool)> const &func) const {
    for(int po: vPos) {
      func(GetFanin(po, 0), GetCompl(po, 0));
    }
  }
  
  inline void AndNetwork::ForEachFanin(int id, std::function<void(int, bool)> const &func) const {
    for(int fi_edge: vvFaninEdges[id]) {
      func(Edge2Node(fi_edge), EdgeIsCompl(fi_edge));
    }
  }

  inline void AndNetwork::ForEachFaninIdx(int id, std::function<void(int, int, bool)> const &func) const {
    for(int idx = 0; idx < GetNumFanins(id); idx++) {
      func(idx, GetFanin(id, idx), GetCompl(id, idx));
    }
  }
  
  inline void AndNetwork::ForEachFanout(int id, bool fPos, std::function<void(int, bool)> const &func) const {
    if(vRefs[id] == 0) {
      return;
    }
    citr it = std::find(lInts.begin(), lInts.end(), id);
    assert(it != lInts.end());
    it++;
    int nRefs = vRefs[id];
    for(; nRefs != 0 && it != lInts.end(); it++) {
      int idx = FindFanin(*it, id);
      if(idx >= 0) {
        func(*it, GetCompl(*it, idx));
        nRefs--;
      }
    }
    if(fPos && nRefs != 0) {
      for(int po: vPos) {
        if(GetFanin(po, 0) == id) {
          func(po, GetCompl(po, 0));
          nRefs--;
          if(nRefs == 0) {
            break;
          }
        }
      }
    }
    assert(!fPos || nRefs == 0);
  }
  
  inline void AndNetwork::ForEachFanoutRidx(int id, bool fPos, std::function<void(int, bool, int)> const &func) const {
    if(vRefs[id] == 0) {
      return;
    }
    citr it = std::find(lInts.begin(), lInts.end(), id);
    assert(it != lInts.end());
    it++;
    int nRefs = vRefs[id];
    for(; nRefs != 0 && it != lInts.end(); it++) {
      int idx = FindFanin(*it, id);
      if(idx >= 0) {
        func(*it, GetCompl(*it, idx), idx);
        nRefs--;
      }
    }
    if(fPos && nRefs != 0) {
      for(int po: vPos) {
        if(GetFanin(po, 0) == id) {
          func(po, GetCompl(po, 0), 0);
          nRefs--;
          if(nRefs == 0) {
            break;
          }
        }
      }
    }
    assert(!fPos || nRefs == 0);
  }
  
  inline void AndNetwork::ForEachTfo(int id, bool fPos, std::function<void(int)> const &func) {
    // this does not include id itself
    if(vRefs[id] == 0) {
      return;
    }
    StartTraversal();
    vTrav[id] = iTrav;
    citr it = std::find(lInts.begin(), lInts.end(), id);
    assert(it != lInts.end());
    it++;
    for(; it != lInts.end(); it++) {
      for(int fi_edge: vvFaninEdges[*it]) {
        if(vTrav[Edge2Node(fi_edge)] == iTrav) {
          func(*it);
          vTrav[*it] = iTrav;
          break;
        }
      }
    }
    if(fPos) {
      for(int po: vPos) {
        if(vTrav[GetFanin(po, 0)] == iTrav) {
          func(po);
          vTrav[po] = iTrav;
        }
      }
    }
    EndTraversal();
  }

  inline void AndNetwork::ForEachTfoReverse(int id, bool fPos, std::function<void(int)> const &func) {
    // this does not include id itself
    if(vRefs[id] == 0) {
      return;
    }
    StartTraversal();
    vTrav[id] = iTrav;
    citr it = std::find(lInts.begin(), lInts.end(), id);
    assert(it != lInts.end());
    it++;
    for(; it != lInts.end(); it++) {
      for(int fi_edge: vvFaninEdges[*it]) {
        if(vTrav[Edge2Node(fi_edge)] == iTrav) {
          vTrav[*it] = iTrav;
          break;
        }
      }
    }
    if(fPos) {
      for(int po: vPos) {
        if(vTrav[GetFanin(po, 0)] == iTrav) {
          vTrav[po] = iTrav;
        }
      }
    }
    EndTraversal(); // release here so func can call IsReconvergent
    unsigned iTravTfo = iTrav;
    if(fPos) {
      // use reverse order even for POs
      for(std::vector<int>::const_reverse_iterator it = vPos.rbegin(); it != vPos.rend(); it++) {
        assert(vTrav[*it] <= iTravTfo); // make sure func does not touch vTrav of preceding nodes
        if(vTrav[*it] == iTravTfo) {
          func(*it);
        }
      }
    }
    for(critr it = lInts.rbegin(); *it != id; it++) {
      assert(vTrav[*it] <= iTravTfo); // make sure func does not touch vTrav of preceding nodes
      if(vTrav[*it] == iTravTfo) {
        func(*it);
      }
    }
  }

  inline void AndNetwork::ForEachTfoUpdate(int id, bool fPos, std::function<bool(int)> const &func) {
    // this does not include id itself
    if(vRefs[id] == 0) {
      return;
    }
    StartTraversal();
    vTrav[id] = iTrav;
    citr it = std::find(lInts.begin(), lInts.end(), id);
    assert(it != lInts.end());
    it++;
    for(; it != lInts.end(); it++) {
      for(int fi_edge: vvFaninEdges[*it]) {
        if(vTrav[Edge2Node(fi_edge)] == iTrav) {
          if(func(*it)) {
            vTrav[*it] = iTrav;
          }
          break;
        }
      }
    }
    if(fPos) {
      for(int po: vPos) {
        if(vTrav[GetFanin(po, 0)] == iTrav) {
          if(func(po)) {
            vTrav[po] = iTrav;
          }
        }
      }
    }
    EndTraversal();
  }

  template <template <typename...> typename Container, typename ... Ts>
  inline void AndNetwork::ForEachTfos(Container<Ts...> const &ids, bool fPos, std::function<void(int)> const &func) {
    // this includes ids themselves
    StartTraversal();
    for(int id: ids) {
      vTrav[id] = iTrav;
    }
    citr it = lInts.begin();
    while(vTrav[*it] != iTrav && it != lInts.end()) {
      it++;
    }
    for(; it != lInts.end(); it++) {
      if(vTrav[*it] == iTrav) {
        func(*it);
      } else {
        for(int fi_edge: vvFaninEdges[*it]) {
          if(vTrav[Edge2Node(fi_edge)] == iTrav) {
            func(*it);
            vTrav[*it] = iTrav;
            break;
          }
        }
      }
    }
    if(fPos) {
      for(int po: vPos) {
        if(vTrav[po] == iTrav || vTrav[GetFanin(po, 0)] == iTrav) {
          func(po);
          vTrav[po] = iTrav;
        }
      }
    }
    EndTraversal();
  }
  
  template <template <typename...> typename Container, typename ... Ts>
  inline void AndNetwork::ForEachTfosUpdate(Container<Ts...> const &ids, bool fPos, std::function<bool(int)> const &func) {
    // this includes ids themselves
    StartTraversal();
    for(int id: ids) {
      vTrav[id] = iTrav;
    }
    citr it = lInts.begin();
    while(vTrav[*it] != iTrav && it != lInts.end()) {
      it++;
    }
    for(; it != lInts.end(); it++) {
      if(vTrav[*it] == iTrav) {
        if(!func(*it)) {
          vTrav[*it] = 0;
        }
      } else {
        for(int fi_edge: vvFaninEdges[*it]) {
          if(vTrav[Edge2Node(fi_edge)] == iTrav) {
            if(func(*it)) {
              vTrav[*it] = iTrav;
            }
            break;
          }
        }
      }
    }
    if(fPos) {
      for(int po: vPos) {
        if(vTrav[po] == iTrav) {
          if(!func(po)) {
            vTrav[po] = 0;
          }
        } else if(vTrav[GetFanin(po, 0)] == iTrav) {
          if(func(po)) {
            vTrav[po] = iTrav;
          }
        }
      }
    }
    EndTraversal();
  }

  /* }}} */
  
  /* {{{ Actions */
  
  void AndNetwork::RemoveFanin(int id, int idx) {
    Action action;
    action.type = REMOVE_FANIN;
    action.id = id;
    action.idx = idx;
    int fi = GetFanin(id, idx);
    bool c = GetCompl(id, idx);
    action.fi = fi;
    action.c = c;
    vRefs[fi]--;
    vvFaninEdges[id].erase(vvFaninEdges[id].begin() + idx);
    TakenAction(action);
  }

  void AndNetwork::RemoveUnused(int id, bool fRecursive) {
    assert(vRefs[id] == 0);
    Action action;
    action.type = REMOVE_UNUSED;
    action.id = id;
    ForEachFanin(id, [&](int fi, bool c) {
      action.vFanins.push_back(fi);
      vRefs[fi]--;
    });
    vvFaninEdges[id].clear();
    itr it = std::find(lInts.begin(), lInts.end(), id);
    lInts.erase(it);
    sInts.erase(id);
    TakenAction(action);
    if(fRecursive) {
      for(int fi: action.vFanins) {
        if(vRefs[fi] == 0) {
          RemoveUnused(fi, true);
        }
      }
    }
  }

  void AndNetwork::RemoveBuffer(int id) {
    assert(GetNumFanins(id) == 1);
    assert(!fPropagating || fLockTrav);
    int fi = GetFanin(id, 0);
    bool c = GetCompl(id, 0);
    // check if it is buffering constant
    if(fi == GetConst0()) {
      RemoveConst(id);
      return;
    }
    // remove if substitution would lead to duplication with the same polarity
    ForEachFanoutRidx(id, false, [&](int fo, bool foc, int idx) {
      int idx2 = FindFanin(fo, fi);
      if(idx2 != -1 && GetCompl(fo, idx2) == (c ^ foc)) {
        RemoveFanin(fo, idx);
        if(fPropagating && GetNumFanins(fo) == 1) {
          vTrav[fo] = iTrav;
        }
      }
    });
    // substitute node with fanin or const-0
    Action action;
    action.type = REMOVE_BUFFER;
    action.id = id;
    action.fi = fi;
    action.c = c;
    ForEachFanoutRidx(id, true, [&](int fo, bool foc, int idx) {
      action.vFanouts.push_back(fo);
      int idx2 = FindFanin(fo, fi);
      if(idx2 != -1) { // substitute with const-0 in case of duplication
        assert(GetCompl(fo, idx2) != (c ^ foc)); // of a different polarity
        vRefs[GetConst0()]++;
        vvFaninEdges[fo][idx] = Node2Edge(GetConst0(), 0);
        if(fPropagating) {
          vTrav[fo] = iTrav;
        }
      } else { // otherwise, substitute with fanin
        vvFaninEdges[fo][idx] = Node2Edge(fi, c ^ foc);
        vRefs[fi]++;
      }
    });
    // remove node
    vRefs[id] = 0;
    vRefs[fi]--;
    vvFaninEdges[id].clear();
    if(!fPropagating) {
      itr it = std::find(lInts.begin(), lInts.end(), id);
      lInts.erase(it);
    }
    sInts.erase(id);
    TakenAction(action);
  }

  void AndNetwork::RemoveConst(int id) {
    assert(GetNumFanins(id) == 0 || FindFanin(id, GetConst0()) != -1);
    assert(!fPropagating || fLockTrav);
    bool c = (GetNumFanins(id) == 0);
    // just remove immediately if polarity is true but not PO
    ForEachFanoutRidx(id, false, [&](int fo, bool foc, int idx) {
      if(c ^ foc) {
        assert(!IsPo(fo));
        RemoveFanin(fo, idx);
        if(fPropagating && GetNumFanins(fo) <= 1) {
          vTrav[fo] = iTrav;
        }
      }
    });
    // substitute with constant
    Action action;
    action.type = REMOVE_CONST;
    action.id = id;
    ForEachFanoutRidx(id, true, [&](int fo, bool foc, int idx) {
      action.vFanouts.push_back(fo);
      vRefs[GetConst0()]++;
      vvFaninEdges[fo][idx] = Node2Edge(GetConst0(), c ^ foc);
      if(fPropagating) {
        vTrav[fo] = iTrav;
      }
    });
    // remove node
    vRefs[id] = 0;
    ForEachFanin(id, [&](int fi, bool c) {
      vRefs[fi]--;
      action.vFanins.push_back(fi);
    });
    vvFaninEdges[id].clear();
    if(!fPropagating) {
      itr it = std::find(lInts.begin(), lInts.end(), id);
      lInts.erase(it);
    }
    sInts.erase(id);
    TakenAction(action);
  }

  void AndNetwork::AddFanin(int id, int fi, bool c) {
    assert(FindFanin(id, fi) == -1); // no duplication
    assert(fi != GetConst0() || !c); // no const-1
    Action action;
    action.type = ADD_FANIN;
    action.id = id;
    action.idx = vvFaninEdges[id].size();
    action.fi = fi;
    action.c = c;
    itr it = std::find(lInts.begin(), lInts.end(), id);
    itr it2 = std::find(it, lInts.end(), fi);
    if(it2 != lInts.end()) {
      lInts.erase(it2);
      it2 = lInts.insert(it, fi);
      SortInts(it2);
    }
    vRefs[fi]++;
    vvFaninEdges[id].push_back(Node2Edge(fi, c));
    TakenAction(action);
  }

  void AndNetwork::TrivialCollapse(int id) {
    for(int idx = 0; idx < GetNumFanins(id);) {
      int fi_edge = vvFaninEdges[id][idx];
      int fi = Edge2Node(fi_edge);
      bool c = EdgeIsCompl(fi_edge);
      if(!IsPi(fi) && !c && vRefs[fi] == 1) {
        Action action;
        action.type = TRIVIAL_COLLAPSE;
        action.id = id;
        action.idx = idx;
        action.fi = fi;
        action.c = c;
        std::vector<int>::iterator it = vvFaninEdges[id].begin() + idx;
        it = vvFaninEdges[id].erase(it);
        vvFaninEdges[id].insert(it, vvFaninEdges[fi].begin(), vvFaninEdges[fi].end());
        ForEachFanin(fi, [&](int fi, bool c) {
          action.vFanins.push_back(fi);
        });
        // remove collapsed fanin
        vRefs[fi] = 0;
        vvFaninEdges[fi].clear();
        lInts.erase(std::find(lInts.begin(), lInts.end(), fi));
        sInts.erase(fi);
        TakenAction(action);
      } else {
        idx++;
      }
    }
  }

  void AndNetwork::TrivialDecompose(int id) {
    while(GetNumFanins(id) > 2) {
      Action action;
      action.type = TRIVIAL_DECOMPOSE;
      action.id = id;
      action.idx = vvFaninEdges[id].size() - 2;
      int new_fi = CreateNode();
      action.fi = new_fi;
      int fi_edge1 = vvFaninEdges[id].back();
      vvFaninEdges[id].pop_back();
      int fi_edge0 = vvFaninEdges[id].back();
      vvFaninEdges[id].pop_back();
      vvFaninEdges[new_fi].push_back(fi_edge0);
      action.vFanins.push_back(Edge2Node(fi_edge0));
      vvFaninEdges[new_fi].push_back(fi_edge1);
      action.vFanins.push_back(Edge2Node(fi_edge1));
      vvFaninEdges[id].push_back(Node2Edge(new_fi, false));
      vRefs[new_fi]++;
      itr it = std::find(lInts.begin(), lInts.end(), id);
      lInts.insert(it, new_fi);
      sInts.insert(new_fi);
      TakenAction(action);
    }
  }

  void AndNetwork::SortFanins(int id, std::function<bool(int, bool, int, bool)> const &comp) {
    std::vector<int> vFaninEdges = vvFaninEdges[id];
    std::sort(vvFaninEdges[id].begin(), vvFaninEdges[id].end(), [&](int i, int j) {
      return comp(Edge2Node(i), EdgeIsCompl(i), Edge2Node(j), EdgeIsCompl(j));
    });
    if(vFaninEdges == vvFaninEdges[id]) {
      return;
    }
    Action action;
    action.type = SORT_FANINS;
    action.id = id;
    assert(vFaninEdges.size() <= (std::vector<int>::size_type)std::numeric_limits<int>::max());
    for(int fanin_edge: vvFaninEdges[id]) {
      std::vector<int>::const_iterator it = std::find(vFaninEdges.begin(), vFaninEdges.end(), fanin_edge);
      action.vIndices.push_back(std::distance(vFaninEdges.cbegin(), it));
    }
    TakenAction(action);
  }

  /* }}} */

  /* {{{ Network cleanup */
  
  void AndNetwork::Propagate(int id) {
    StartTraversal();
    itr it;
    if(id == -1) {
      ForEachInt([&](int id) {
        if(GetNumFanins(id) <= 1 || FindFanin(id, GetConst0()) != -1) {
          vTrav[id] = iTrav;
        }
      });
      it = lInts.begin();
      while(vTrav[*it] != iTrav && it != lInts.end()) {
        it++;
      }
    } else {
      vTrav[id] = iTrav;
      it = std::find(lInts.begin(), lInts.end(), id);
    }
    fPropagating = true;
    while(it != lInts.end()) {
      if(vTrav[*it] == iTrav) {
        if(GetNumFanins(*it) == 1) {
          RemoveBuffer(*it);
        } else {
          RemoveConst(*it);
        }
        it = lInts.erase(it);
      } else {
        it++;
      }
    }
    fPropagating = false;
    EndTraversal();
  }

  void AndNetwork::Sweep(bool fPropagate) {
    if(fPropagate) {
      Propagate();
    }
    for(ritr it = lInts.rbegin(); it != lInts.rend();) {
      if(vRefs[*it] == 0) {
        RemoveUnused(*it);
        it = ritr(lInts.erase(--it.base()));
      } else {
        it++;
      }
    }
  }
  
  /* }}} */

  /* {{{ Save & load */

  int AndNetwork::Save(int slot) {
    Action action;
    action.type = SAVE;
    if(slot < 0) {
      slot = vBackups.size();
      vBackups.push_back(*this);
    } else {
      assert(slot < vBackups.size());
      vBackups[slot] = *this;
    }
    action.idx = slot;
    TakenAction(action);
    return slot;
  }

  void AndNetwork::Load(int slot) {
    assert(slot < vBackups.size());
    Action action;
    action.type = LOAD;
    action.idx = slot;
    *this = vBackups[slot];
    TakenAction(action);
  }

  void AndNetwork::PopBack() {
    assert(!vBackups.empty());
    Action action;
    action.type = POP_BACK;
    action.idx = vBackups.size() - 1;
    vBackups.pop_back();
    TakenAction(action);
  }

  /* }}} */
  
  /* {{{ Misc */

  void AndNetwork::AddCallback(Callback const &callback) {
    vCallbacks.push_back(callback);
  }
  
  void AndNetwork::Print() const {
    std::cout << "pi: ";
    std::string delim = "";
    ForEachPi([&](int id) {
      std::cout << delim << id;
      delim = ", ";
    });
    std::cout << std::endl;
    ForEachInt([&](int id) {
      std::cout << "node " << id << ": ";
      delim = "";
      ForEachFanin(id, [&](int fi, bool c) {
        std::cout << delim;
        if(c) {
          std::cout << "!";
        }
        std::cout << fi;
        delim = ", ";
      });
      std::cout << " (ref = " << vRefs[id] << ")";
      std::cout << std::endl;
    });
    std::cout << "po: ";
    delim = "";
    ForEachPoDriver([&](int fi, bool c) {
      std::cout << delim;
      if(c) {
        std::cout << "!";
      }
      std::cout << fi;
      delim = ", ";
    });
    std::cout << std::endl;
  }

  /* }}} Misc end */

}

ABC_NAMESPACE_CXX_HEADER_END
