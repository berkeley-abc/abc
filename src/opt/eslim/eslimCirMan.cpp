/**CFile****************************************************************

  FileName    [eslimCirMan.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Internal circuit representation.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <cassert>
#include <unordered_map>
#include <iostream>
#include <algorithm>

#include "eslimCirMan.hpp"
#include "subcircuit.hpp"
#include "tabooList.hpp"
#include "utils.hpp"

#include "map/mio/mio.h"

ABC_NAMESPACE_HEADER_START
  void Mio_IntallSimpleLibrary();
  void * Abc_FrameReadLibGen();
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START
namespace eSLIM {

  eSLIMCirObj::eSLIMCirObj(int id, std::vector<eSLIMCirObj*>&& fanins)
              : node_id(id), fanins(fanins) {
  }

  int eSLIMCirObj::getNFanins() const{
    return fanins.size();
  }

  int eSLIMCirObj::getTTLength() const {
    return static_cast<ABC_UINT64_T>(1) << getNFanins();
  }

  unsigned int eSLIMCirObj::getId() const {
    return id;
  }


  eSLIMCirMan::eSLIMCirMan(int nObjEstimate) {
    nodes.reserve(1 + nObjEstimate);
    std::unique_ptr<eSLIMCirObj> pobj = std::make_unique<eSLIMCirObj>(0, std::vector<eSLIMCirObj*>()); // const false node
    nodes.push_back(std::move(pobj));
  }

  eSLIMCirMan::eSLIMCirMan(eSLIMCirMan& es_man, const Subcircuit& scir)
              : eSLIMCirMan(scir.inputs.size() + scir.outputs.size() + scir.nodes.size()) {
    for (int i = 0; i < scir.inputs.size(); i++) {
      es_man.nodes[scir.inputs[i]]->value1 = addPi();
    }
    for (int nd : scir.nodes) {
      std::vector<int> fanins;
      for (auto f : es_man.nodes[nd]->fanins) {
        fanins.push_back(f->value1);
      }
      es_man.nodes[nd]->value1 = addNode(fanins, es_man.nodes[nd]->tt);
    }
    for (int i = 0; i < scir.outputs.size(); i++) {
      addPo(es_man.nodes[scir.outputs[i]]->value1,false);
    }
  }

  eSLIMCirMan::eSLIMCirMan(Gia_Man_t * pGia) : eSLIMCirMan(Gia_ManObjNum(pGia)) {
    assert (!Gia_ManHasDangling(pGia));
    Gia_ManConst0(pGia)->Value = 0;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManForEachPi( pGia, pObj, i ) {
      pObj->Value = addPi();
    }
    Gia_ManIncrementTravId(pGia);
    
    Gia_ManForEachAnd( pGia, pObj, i ) {
      ABC_UINT64_T tt = ttFromGiaObj(pGia, pObj);
      if (!ttisnormal(tt)) { 
        Gia_ObjSetTravIdCurrent(pGia, pObj); // marked nodes are considered negated
        tt = negateTT(tt, 2);
      }
      pObj->Value = addNode({static_cast<int>(Gia_ObjFanin0(pObj)->Value), static_cast<int>(Gia_ObjFanin1(pObj)->Value)}, tt);
    }

    Gia_ManForEachPo( pGia, pObj, i ) {
      bool po_is_negated = Gia_ObjFaninC0(pObj) != Gia_ObjIsTravIdCurrent(pGia, Gia_ObjFanin0(pObj));
      pObj->Value = addPo(Gia_ObjFanin0(pObj)->Value, po_is_negated);
    }
  }

  eSLIMCirMan::eSLIMCirMan(Abc_Ntk_t * pNtk, bool simplify) : eSLIMCirMan(Abc_NtkObjNum(pNtk)) {
    assert(Abc_NtkIsLogic(pNtk));
    assert(Abc_NtkHasSop(pNtk));

    Abc_NtkIncrementTravId(pNtk);

    std::unordered_map<int,int> ids;
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachPi(pNtk, pObj, i) {
      ids[pObj->Id] = addPi();
    }

    // Nodes are not necessarily topologically sorted.
    // A po can be driven by another po
    Abc_NtkForEachPo(pNtk, pObj, i) {
      if (!Abc_ObjIsPo(Abc_ObjChild0(pObj))) {
        insertNtkNodes(pNtk, Abc_ObjChild0(pObj)->Id, ids, simplify);
      }
    }

    // POs shall occur after the gates:
    Abc_NtkForEachPo(pNtk, pObj, i) {
      bool negated = false;
      do {
        int fc0 = Abc_ObjFaninC0(pObj);
        pObj = Abc_ObjChild0(pObj);
        negated ^= (fc0 ^ Abc_NodeIsTravIdCurrent(pObj));
      } while (Abc_ObjIsPo(pObj));
      addPo(ids.at(pObj->Id), negated);
    }
  }

  int eSLIMCirMan::insertNtkNodes(Abc_Ntk_t * pNtk, int node_id, std::unordered_map<int,int>& ids, bool simplify) {
    auto it = ids.find(node_id);
    if (it != ids.end()) {
      return it->second;
    }
    Abc_Obj_t * pObj = Abc_NtkObj(pNtk, node_id);
    if (Vec_IntSize(&pObj->vFanins) == 0 ) { 
      ABC_UINT64_T tt = ttFromNtkObj(pNtk, pObj);
      if (ttisnormal(tt)) { // const0
        ids[pObj->Id] = 0;
        return 0;
      } else if (simplify) {
        ids[pObj->Id] = 0;
        Abc_NodeSetTravIdCurrent(pObj);
        return 0;
      }
    }

    std::vector<int> fanins (Vec_IntSize(&pObj->vFanins), 0);
    int j, f;
    Vec_IntForEachEntry(&(pObj->vFanins), f, j) {
      auto it = ids.find(f);
      if (it == ids.end()) {
        fanins[j] = insertNtkNodes(pNtk, f, ids, simplify);
      } else {
        fanins[j] = it->second;
      }
    }

    // the truth table must be computed after we traversed the fanins in order to take account for normalised gates
    ABC_UINT64_T tt = ttFromNtkObj(pNtk, pObj);
    if (simplify && Vec_IntSize(&pObj->vFanins) == 1) {
      int id = fanins[0];
      if (!ttisnormal(tt)) {
        Abc_NodeSetTravIdCurrent(pObj);
      }
      ids[pObj->Id] = id;
      return id; 
    }

    // We normalise each gate
    if (simplify && !ttisnormal(tt)) {
      tt = negateTT(tt, Vec_IntSize(&pObj->vFanins));
      Abc_NodeSetTravIdCurrent(pObj);
    }
    int id = addNode(fanins, tt);
    ids[pObj->Id] = id;
    return id;
  }


  eSLIMCirObj* eSLIMCirMan::getpObj(int id) {
    return nodes[id].get();
  }

  const eSLIMCirObj* eSLIMCirMan::getpObj(int id) const {
    return nodes[id].get();
  }

  eSLIMCirObj* eSLIMCirMan::getPo(int id) {
    return nodes[getNofObjs() - nof_pos - 1 + id].get();
  }

  const eSLIMCirObj& eSLIMCirMan::getObj(int id) const {
    return *nodes[id].get();
  }

  int eSLIMCirMan::addPi() {
    nof_pis++;
    int id = nodes.size();
    std::unique_ptr<eSLIMCirObj> pobj = std::make_unique<eSLIMCirObj>(id, std::vector<eSLIMCirObj*>());
    pobj->tt = 2;
    pobj->depth = 0;
    pobj->id = last_node_id++;
    nodes.push_back(std::move(pobj));
    return id;
  }

  // If the fanin is negated we use the tt-member to indicate this negation
  int eSLIMCirMan::addPo(int fanin, bool negated) {
    nof_pos++;
    // 1 represents negation and 2 projection
    ABC_UINT64_T tt = negated ? 1 : 2;
    // return addNode({fanin}, tt);
    int id = addNode({fanin}, tt);
    depth = std::max(depth, nodes.back()->depth);
    return id;
  }

  int eSLIMCirMan::addNode(const std::vector<int>& fanins, ABC_UINT64_T tt) {
    int id = nodes.size();
    std::vector<eSLIMCirObj*> pfan;
    unsigned int max_fan_depth = 0;
    for (int f : fanins) {
      pfan.push_back(getpObj(f));
      max_fan_depth = pfan.back()->depth > max_fan_depth ? pfan.back()->depth : max_fan_depth;
    }
    std::unique_ptr<eSLIMCirObj> pobj = std::make_unique<eSLIMCirObj>(id, std::move(pfan));
    pobj->tt = tt;
    pobj->depth = max_fan_depth + 1;
    pobj->id = last_node_id++;
    for (int f : fanins) {
      getpObj(f)->fanouts.insert(pobj.get());
    }
    nodes.push_back(std::move(pobj));
    return id;
  }

  int eSLIMCirMan::getDepth() const {
    return depth;
  }

  void eSLIMCirMan::setupTimings() {
    for (int i = 0; i < nodes.size(); i++) {
      getpObj(i)->remaining_time = 0;
    }
    for (int i = nodes.size() - nof_pos - 1; i > 0; i--) {
      eSLIMCirObj* pe = getpObj(i);
      pe->remaining_time++;
      for (int j = 0; j < pe->fanins.size(); j++) {
        (pe->fanins[j])->remaining_time = std::max((pe->fanins[j])->remaining_time, pe->remaining_time);
      }
    }
  }

  bool eSLIMCirMan::isConst(int id) const {
    return id == 0;
  }

  bool eSLIMCirMan::isConst(const eSLIMCirObj& obj) const {
    return obj.node_id == 0;
  }

  bool eSLIMCirMan::isPi(int id) const {
    return id <= nof_pis; // 0 is the const0 node
  }

  bool eSLIMCirMan::isPi(const eSLIMCirObj& obj) const {
    return obj.node_id <= nof_pis;
  }

  bool eSLIMCirMan::isOnCricticalPath(const eSLIMCirObj& obj) const {
    return obj.depth + obj.remaining_time == depth;
  }

  bool eSLIMCirMan::isPo(int id) const {
    return id >= nodes.size() - nof_pos;
  }
  
  bool eSLIMCirMan::isGate(int id) const {
    return !isPi(id) && !isPo(id);
  }

  int eSLIMCirMan::getNofObjs() const {
    return nodes.size();
  }

  int eSLIMCirMan::getNofPis() const {
    return nof_pis;
  }

  int eSLIMCirMan::getNofPos() const {
    return nof_pos;
  }

  int eSLIMCirMan::getNofGates() const {
    return nodes.size() - nof_pis - nof_pos - 1;
  }

  void eSLIMCirMan::setTraversalId(eSLIMCirObj& obj) {
    obj.trav_id = traversal_id;
  }

  void eSLIMCirMan::setTraversalId(int n) {
    getpObj(n)->trav_id = traversal_id;
  }
  
  bool eSLIMCirMan::isCurrentTraversalId(int n) const {
    return getpObj(n)->trav_id == traversal_id;
  }

  bool eSLIMCirMan::isCurrentTraversalId(const eSLIMCirObj& obj) const {
    return obj.trav_id == traversal_id;
  }

  void eSLIMCirMan::setInTFI(eSLIMCirObj& obj) {
    obj.inTFI = traversal_id;
  }

  void eSLIMCirMan::setInTFO(eSLIMCirObj& obj) {
    obj.inTFO = traversal_id;
  }

  void eSLIMCirMan::setInSubcircuit(eSLIMCirObj& obj) {
    obj.inSubcircuit = traversal_id;
  }
      

  bool eSLIMCirMan::inTFI(const eSLIMCirObj& obj) const {
    return  obj.inTFI == traversal_id;
  }

  bool eSLIMCirMan::inTFO(const eSLIMCirObj& obj) const {
    return obj.inTFO == traversal_id;
  }

  bool eSLIMCirMan::inSubcircuit(const eSLIMCirObj& obj) const {
    return obj.inSubcircuit == traversal_id;
  }

  bool eSLIMCirMan::isTaboo(const eSLIMCirObj& obj, int taboo_time) const {
    return obj.isTaboo != 0 && (traversal_id - obj.isTaboo < taboo_time);
  }
  
  void eSLIMCirMan::setTaboo(eSLIMCirObj& obj) {
    obj.isTaboo = traversal_id;
  }

  void eSLIMCirMan::markSubcircuit(const std::vector<int>& nodes) {
    for (int n : nodes) {
      setInSubcircuit(*getpObj(n));
    }
  }

  void eSLIMCirMan::markCones(const std::vector<int>& nodes) {
    int min_node = *std::min_element(nodes.begin(), nodes.end());
    int max_node = *std::max_element(nodes.begin(), nodes.end());
    // mark TFI
    for (int i = max_node; i >= getNofPis(); i--) {
      if (inSubcircuit(*getpObj(i)) || inTFI(*getpObj(i))) {
        for (auto& f : getpObj(i)->fanins) {
          if (!inSubcircuit(*f)) {
            setInTFI(*f);
          }
        }
      }
    }
    // mark tfo
    for (int i = min_node; i < getNofObjs(); i++) {
      if (!inSubcircuit(*getpObj(i))) {
        for (auto& f : getpObj(i)->fanins) {
          if (inSubcircuit(*f) || inTFO(*f)) {
            setInTFO(*getpObj(i));
          }
        }
      }
    }
  }

  ABC_UINT64_T eSLIMCirMan::ttFromGiaObj(Gia_Man_t * pGia, Gia_Obj_t * pObj) {
    assert(Gia_ObjIsAnd(pObj));
    // A fanin is negated if is either negated in pGia or (exclusive) if it is marked
    if (Gia_ObjFaninC0(pObj) != Gia_ObjIsTravIdCurrent(pGia, Gia_ObjFanin0(pObj))) {
      if (Gia_ObjFaninC1(pObj) != Gia_ObjIsTravIdCurrent(pGia, Gia_ObjFanin1(pObj))) {
        return 1;
      } else {
        return 4;
      }
    } else {
      if (Gia_ObjFaninC1(pObj) != Gia_ObjIsTravIdCurrent(pGia, Gia_ObjFanin1(pObj))) {
        return 2;
      } else {
        return 8;
      }
    }
  }

  ABC_UINT64_T eSLIMCirMan::ttFromNtkObj(Abc_Ntk_t * pNtk, Abc_Obj_t * pObj) {
    int j, f;
    char * pSop = (char *)pObj->pData;
    ABC_UINT64_T tt = sop2tt(pSop);
    Vec_IntForEachEntry(&(pObj->vFanins), f, j) {
      if (Abc_NodeIsTravIdCurrent(Abc_NtkObj(pNtk, f))) {
        tt = ttNegateFanin(tt, j);
      }
    }
    return tt;
  }

  bool eSLIMCirMan::ttisnormal(ABC_UINT64_T tt) {
    return !(tt & 1);
  }

  ABC_UINT64_T eSLIMCirMan::negateTT(ABC_UINT64_T tt, unsigned int nfanin) {
    assert (nfanin <= 6);
    constexpr ABC_UINT64_T filters[7] {0x1ull, 0x3ull, 0xFull, 0xFFull, 0xFFFFull, 0xFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull};
    return ~tt & filters[nfanin];
  }

  ABC_UINT64_T eSLIMCirMan::ttNegateFanin(ABC_UINT64_T tt, unsigned int fan) {
    assert (fan < 6);
    constexpr ABC_UINT64_T filters1[6] = {0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull, 0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};
    constexpr ABC_UINT64_T filters2[6] = {0x5555555555555555ull, 0x3333333333333333ull, 0xF0F0F0F0F0F0F0Full, 0xFF00FF00FF00FFull, 0xFFFF0000FFFFull, 0xFFFFFFFFull};
    constexpr int shifts[6] = {1,2,4,8,16,32};
    ABC_UINT64_T x = tt & filters1[fan];
    ABC_UINT64_T y = tt & filters2[fan];
    return (x >> shifts[fan]) | (y << shifts[fan]);
  }

  ABC_UINT64_T eSLIMCirMan::sop2tt(char * pSop) {
    constexpr ABC_UINT64_T filters[7] {0x1ull, 0x3ull, 0xFull, 0xFFull, 0xFFFFull, 0xFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull};
    int nVars = Abc_SopGetVarNum(pSop);
    ABC_UINT64_T tt = Abc_SopToTruth(pSop, nVars);
    return tt & filters[nVars];
  }

  char* eSLIMCirMan::tt2sop(ABC_UINT64_T tt, int nVars, Mem_Flex_t * pMan) {
    int bit_count = popcount(tt);
    if (bit_count == 0) {
      char* pSopCover = Abc_SopCreateConst0(pMan);
      return pSopCover;
    } else if (bit_count == 1 << nVars) {
      char* pSopCover = Abc_SopCreateConst1(pMan);
      return pSopCover;
    }
    char* pSopCover = Abc_SopStart( pMan, bit_count, nVars );
    int sop_id = 0;
    for (int i = 0; i < (1 << nVars); i++) {
      if ((tt >> i) & 1) {
        for (int j = 0; j < nVars; j++) {
          char bit = ((i >> j) & 1) ? '1' : '0';
          pSopCover[sop_id*(nVars + 3) + j] = bit;
        }
        pSopCover[sop_id*(nVars + 3) + nVars] = ' ';
        pSopCover[sop_id*(nVars + 3) + nVars + 1] = '1';
        pSopCover[sop_id*(nVars + 3) + nVars + 2] = '\n';
        sop_id++;
      }
    }
    pSopCover[sop_id*(nVars + 3)] = 0;
    return pSopCover;
  }


  int eSLIMCirMan::addGiaGate(Gia_Man_t * pGia, int node_id, std::vector<int>& node_ids, std::vector<bool>& is_node_negated) {
    eSLIMCirObj* pe = getpObj(node_id);
    // assert (pe->getNFanins() == 2);
    int bit_count = popcount(pe->tt);
    assert(ttisnormal(pe->tt));
    assert (bit_count > 0 || bit_count < 4); // the circuit shall not contain constants
    ABC_UINT64_T tt = pe->tt;
    bool negate_and = false;
    bool is_xor = false;
    bool fan1negated = false, fan2negated = false;
    if (bit_count == 3) { // or gates are represented by negated and gates 
      tt = negateTT(pe->tt, 2);
      negate_and = true;
      fan1negated = true;
      fan2negated = true;
    } else if (pe->tt == 2) {
      fan1negated = false;
      fan2negated = true;
    } else if (pe->tt == 4) {
      fan1negated = true;
      fan2negated = false;
    } else if (pe->tt == 8) {
      fan1negated = false;
      fan2negated = false;
    } else {
      // XOR
      assert (pe->tt == 6);
      is_xor = true;
    }

    int fan1 = node_ids[(pe->fanins[0])->node_id];
    int fan2 = node_ids[(pe->fanins[1])->node_id];

    fan1negated = (fan1negated != is_node_negated[(pe->fanins[0])->node_id]);
    fan2negated = (fan2negated != is_node_negated[(pe->fanins[1])->node_id]);

    // We need to remove gates with duplicate fanins.
    // We do not use simplifyDuplicateFanins as it does not propagate duplicate fanins.
    if (fan1 == fan2) {
      if ((fan1negated != fan2negated ) || is_xor) {
        assert (!negate_and);
        node_ids[node_id] = const_false_id;
        is_node_negated[node_id] = negate_and;
        return const_false_id;
      } else {
        node_ids[node_id] = fan1;
        // Gates are assumed to be normal -> x = !a && !a (x = !a || !a) is not possible.
        is_node_negated[node_id] = is_node_negated[(pe->fanins[1])->node_id];
        return fan1;
      }
    }

    int id;
    if (is_xor) {
      id = Gia_ManAppendXor(pGia, Abc_LitNotCond(fan1, fan1negated), Abc_LitNotCond(fan2, fan2negated));
      // id = Gia_ManAppendXorReal(pGia, Abc_LitNotCond(fan1, fan1negated), Abc_LitNotCond(fan2, fan2negated));
    } else {
      id = Gia_ManAppendAnd(pGia, Abc_LitNotCond(fan1, fan1negated), Abc_LitNotCond(fan2, fan2negated));
    }
 

    node_ids[node_id] = id;
    is_node_negated[node_id] = negate_and;
    
    return id;
  }


  Gia_Man_t* eSLIMCirMan::eSLIMCirManToGia() {
    // simplifyDuplicateFanins();
    Gia_Man_t * pNew = Gia_ManStart( getNofObjs() );

    std::vector<int> node_ids(nodes.size(), 0);
    std::vector<bool> is_node_negated(nodes.size(), false);

    for (int i = 1; i <= nof_pis; i++) {
      int id = Gia_ManAppendCi(pNew);
      node_ids[i] = id;
      is_node_negated[i] = false;
    }

    for (int i = nof_pis + 1; i < nodes.size() - nof_pos; i++) {
      assert(nodes[i]->getNFanins() == 2);
      addGiaGate( pNew, i, node_ids, is_node_negated );
    }

    for (int i = nodes.size() - nof_pos; i < nodes.size(); i++) {
      eSLIMCirObj* pobj = getpObj(i);
      bool fan_negated = ((pobj->tt == 1) != is_node_negated.at((pobj->fanins[0])->node_id));
      int fanin0 = Abc_LitNotCond(node_ids[(pobj->fanins[0])->node_id], fan_negated);
      int id = Gia_ManAppendCo( pNew, fanin0 );
      node_ids[i] = id;
    }

    return pNew;
  }

  Abc_Ntk_t* eSLIMCirMan::eSLIMCirManToNtk() {
    simplifyDuplicateFanins();
    Abc_Ntk_t* pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_SOP, 1 );
    std::vector<Abc_Obj_t*> ntk_objs;
    // constant0
    Abc_Obj_t* pObj = Abc_NtkCreateNodeConst0(pNtk);
    ntk_objs.push_back(pObj);
    Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );

    for (int i = 1; i <= nof_pis; i++) {
      Abc_Obj_t* pObj = Abc_NtkCreatePi(pNtk);
      ntk_objs.push_back(pObj);
      Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
    }
    for (int i = nof_pis + 1; i < nodes.size() - nof_pos; i++) {
      Abc_Obj_t* pObj = Abc_NtkCreateNode( pNtk );
      Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
      ntk_objs.push_back(pObj);
      char* sop = tt2sop(nodes[i]->tt, nodes[i]->fanins.size(),  (Mem_Flex_t *)pNtk->pManFunc);
      pObj->pData = sop;
      for (auto f : nodes[i]->fanins) {
        int fid = f->node_id;
        Abc_ObjAddFanin(pObj, ntk_objs[fid]);
      }
    }
    for (int i = nodes.size() - nof_pos; i < nodes.size(); i++) {
      Abc_Obj_t* fobj;
      int fid = nodes[i]->fanins[0]->node_id;
      // bool use_pi_name = false;
      if (nodes[i]->tt == 1) { // a negated po
        char* sop = tt2sop(1, 1, (Mem_Flex_t *)pNtk->pManFunc);
        fobj = Abc_NtkCreateNode( pNtk );
        Nm_ManStoreIdName( pNtk->pManName, fobj->Id, fobj->Type, Abc_ObjName(fobj), NULL );
        fobj->pData = sop;
        Abc_ObjAddFanin(fobj, ntk_objs[fid]);
      } else {
        // We add buffer to simplify the handling of the SimpleCos condition
        char* sop = tt2sop(2, 1, (Mem_Flex_t *)pNtk->pManFunc);
        fobj = Abc_NtkCreateNode( pNtk );
        Nm_ManStoreIdName( pNtk->pManName, fobj->Id, fobj->Type, Abc_ObjName(fobj), NULL );
        fobj->pData = sop;
        Abc_ObjAddFanin(fobj, ntk_objs[fid]);
      }
      Abc_Obj_t* pObj = Abc_NtkCreatePo(pNtk);
      Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
      Abc_ObjAddFanin(pObj, fobj);
    }

    assert( Abc_NtkCiNum(pNtk)    == nof_pis );
    assert( Abc_NtkCoNum(pNtk)    == nof_pos );
    assert( Abc_NtkLatchNum(pNtk) == 0 );
    assert( Abc_NtkCheck(pNtk) );
    assert( Abc_NtkLogicHasSimpleCos(pNtk));
    return pNtk;
  }

  Abc_Ntk_t* eSLIMCirMan::eSLIMCirManToMappedNtk() {

    Mio_IntallSimpleLibrary();
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();

    Abc_Ntk_t* pNtk = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_MAP, 1 );
    std::vector<Abc_Obj_t*> ntk_objs;
    Abc_Obj_t* pObj = Abc_NtkCreateNode( pNtk );
    pObj->pData = Mio_LibraryReadGateByName( pLib, "zero", NULL );
    ntk_objs.push_back(pObj);
    Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
    Abc_Obj_t* const1 = Abc_NtkCreateNode( pNtk );
    const1->pData = Mio_LibraryReadGateByName( pLib, "one", NULL );
    // ntk_objs.push_back(pObj);
    Nm_ManStoreIdName( pNtk->pManName, const1->Id, const1->Type, Abc_ObjName(const1), NULL );

    for (int i = 1; i <= nof_pis; i++) {
      Abc_Obj_t* pObj = Abc_NtkCreatePi(pNtk);
      ntk_objs.push_back(pObj);
      Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
    }

    for (int i = nof_pis + 1; i < nodes.size() - nof_pos; i++) {
      // Replace an inverted const false by const true
      if (nodes[i]->tt == 1 && nodes[i]->fanins.size() == 1 && nodes[i]->fanins[0]->node_id == 0) {
        ntk_objs.push_back(const1);
        continue;
      }
      // if a gate has no fanins it must be const true (const false is handled separatley)
      if (nodes[i]->fanins.size() == 0) {
        assert (nodes[i]->tt == 1);
        ntk_objs.push_back(const1);
        continue;
      }
      Abc_Obj_t* pObj = Abc_NtkCreateNode( pNtk );
      Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
      ntk_objs.push_back(pObj);
      for (auto f : nodes[i]->fanins) {
        int fid = f->node_id;
        Abc_ObjAddFanin(pObj, ntk_objs[fid]);
      }
      switch (nodes[i]->tt) {
        case 1:
          if (nodes[i]->fanins.size() == 1) {
            pObj->pData = Mio_LibraryReadGateByName( pLib, "inv", NULL );
          } else if (nodes[i]->fanins.size() == 2) {
            pObj->pData = Mio_LibraryReadGateByName( pLib, "nor2", NULL );
          } else {
            pObj->pData = Mio_LibraryReadGateByName( pLib, "nor3", NULL );
          }
          break;
        case 2:
          pObj->pData = Mio_LibraryReadGateByName( pLib, "buf", NULL );
          break;
        case 7:
          if (nodes[i]->fanins.size() == 2) {
            pObj->pData = Mio_LibraryReadGateByName( pLib, "nand2", NULL );
          } else {
            pObj->pData = Mio_LibraryReadGateByName( pLib, "aoi21", NULL );
          }
          break;
        case 31:
          pObj->pData = Mio_LibraryReadGateByName( pLib, "oai21", NULL );
          break;
        case 127:
          pObj->pData = Mio_LibraryReadGateByName( pLib, "nand3", NULL );
          break;
        case 1911:
          pObj->pData = Mio_LibraryReadGateByName( pLib, "aoi22", NULL );
          break;
        case 4383:
          pObj->pData = Mio_LibraryReadGateByName( pLib, "oai22", NULL );
          break;
      
      default:
        std::cerr << "Error: A node with a function not part of the library was detected." << std::endl;
        Abc_NtkDelete( pNtk );
        return NULL;
      }
    }
    std::unordered_map<int, int> negated_pos;
    std::unordered_map<int, int> buffers;

    for (int i = nodes.size() - nof_pos; i < nodes.size(); i++) {
      Abc_Obj_t* fobj;
      int fid = nodes[i]->fanins[0]->node_id;
      if (nodes[i]->tt == 1) { // a negated po
        if (fid == 0) {
          fobj = const1;
        } else {
          if (negated_pos.find(fid) != negated_pos.end()) {
            negated_pos[fid] = ntk_objs.size();
            Abc_Obj_t* pObj = Abc_NtkCreateNode( pNtk );
            Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
            ntk_objs.push_back(pObj);
            pObj->pData = Mio_LibraryReadGateByName( pLib, "inv", NULL );
            Abc_ObjAddFanin(pObj, ntk_objs[fid]); 
          }
          fobj = ntk_objs[negated_pos[fid]];
        }
      } else {
        if (0 < fid && fid <= nof_pis) {
          if (buffers.find(fid) == buffers.end()) {
            Abc_Obj_t* pObj = Abc_NtkCreateNode( pNtk );
            Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
            buffers[fid] = ntk_objs.size();
            ntk_objs.push_back(pObj);
            pObj->pData = Mio_LibraryReadGateByName( pLib, "buf", NULL );
            Abc_ObjAddFanin(pObj, ntk_objs[fid]); 
          } 
          fobj = ntk_objs[buffers[fid]];
        } else {
          fobj = ntk_objs[fid];
        }
      }
      Abc_Obj_t* pObj = Abc_NtkCreatePo(pNtk);
      Nm_ManStoreIdName( pNtk->pManName, pObj->Id, pObj->Type, Abc_ObjName(pObj), NULL );
      Abc_ObjAddFanin(pObj, fobj);
    }

    assert( Abc_NtkCiNum(pNtk)    == nof_pis );
    assert( Abc_NtkCoNum(pNtk)    == nof_pos );
    assert( Abc_NtkLatchNum(pNtk) == 0 );
    assert( Abc_NtkCheck(pNtk) );
    assert( Abc_NtkLogicHasSimpleCos(pNtk));
    return pNtk;
  }

  void eSLIMCirMan::setMarks(eSLIMCirObj& pObj, int id) {
    pObj.node_id = id;
    pObj.depth = 0;
    for (const auto& f : pObj.fanins) {
      if (f->depth >= pObj.depth) {
        pObj.depth = f->depth + 1;
      }
    }
    setTraversalId(pObj);
  }

  void eSLIMCirMan::moveNode(std::vector<std::unique_ptr<eSLIMCirObj>>& vec, std::unique_ptr<eSLIMCirObj>& pobj) {
    int id = vec.size();
    vec.push_back(std::move(pobj));
    pobj = nullptr;
    setMarks(*vec.back(), id);
  }

  void eSLIMCirMan::addFans(eSLIMCirObj* out, eSLIMCirObj* in, int fin_id) {
    out->fanouts.insert(in);
    in->fanins[fin_id] = out;
  }

  void eSLIMCirMan::processNonGateRepFanin( eSLIMCirObj* obj, eSLIMCirObj* fan, int fid, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                                            eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec) {
    if (replacement.isConst(*fan)) {
      addFans(sorted[0].get(), obj, fid);
    } else {
      int in_id = fan->node_id - 1;
      addFans(in_vec[in_id], obj, fid);
      insertSortedRec(in_vec[in_id], sorted, replacement, out_map, in_vec);
    }
  }

  void eSLIMCirMan::processRepFanin(eSLIMCirObj* obj, eSLIMCirObj* fan, int fid, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                                    eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec) {
    if (isCurrentTraversalId(*fan)) {
      addFans(fan, obj, fid);
    } else if (replacement.isPi(*fan)) {
      processNonGateRepFanin(obj, fan, fid, sorted, replacement, out_map, in_vec);
    } else {
      fan->fanouts.clear(); // the ids changed, so we cannot reuse the set
      addFans(fan, obj, fid);
      insertSortedRecRep(fan, sorted, replacement, out_map, in_vec);
    }
  }

  void eSLIMCirMan::processRepPo( eSLIMCirObj* obj, eSLIMCirObj* scir_out, int fid, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                                  eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec) {
    int out_id = out_map.at(scir_out->node_id);
    int out_node_id = replacement.nodes.size() - replacement.getNofPos() + out_id;
    auto rf = replacement.nodes[out_node_id]->fanins[0];
    processRepFanin(obj, rf, fid, sorted, replacement, out_map, in_vec);
  }

  void eSLIMCirMan::insertSorted( eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                                  eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec) {
    auto f = obj->fanins[0];
    if (inSubcircuit(*f)) {
      processRepPo(obj, f, 0, sorted, replacement, out_map, in_vec);
    } else {
      insertSortedRec(f, sorted, replacement, out_map, in_vec);
    }
  }

  void eSLIMCirMan::insertSortedRec(eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted,
                                    eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec) {
    if (isPi(*obj) || isCurrentTraversalId(*obj)) {
      return;
    }
    for (int i = 0; i < obj->fanins.size(); i++) {
      auto f = obj->fanins[i];
      if (inSubcircuit(*f)) {
        processRepPo(obj, f, i, sorted, replacement, out_map, in_vec);
      } else {
        insertSortedRec(f, sorted, replacement, out_map, in_vec);
      }
    }
    moveNode(sorted, nodes[obj->node_id]);
  }

  void eSLIMCirMan::insertSortedRecRep( eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                                        eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec) {
    assert(!isCurrentTraversalId(*obj));
    for (int i = 0; i < obj->fanins.size(); i++) {
      auto f = obj->fanins[i];
      if (!isCurrentTraversalId(*f)) {
        if (replacement.isPi(*f)) {
          processNonGateRepFanin(obj, f, i, sorted, replacement, out_map, in_vec);
        } else {
          f->fanouts.clear();
          f->fanouts.insert(obj);
          insertSortedRecRep(f, sorted, replacement, out_map, in_vec);
        }
      } else {
        f->fanouts.insert(obj);
      }
    }
    if (taboo != nullptr) {
      taboo->addNode(replacement.nodes[obj->node_id].get());
    }
    moveNode(sorted, replacement.nodes[obj->node_id]);
  }

  // We want to preserve the invariant that nodes are topological sorted.
  // Even if we replace a subcircuit by a same sized circuit it is not necessarily possible 
  // to simply replace the old nodes by the new nodes, while preserving the order.
  // We can only process circuits with thousands (maybe tenthousends) nodes.
  // For such sizes the replacement should be reasonable fast. 
  void eSLIMCirMan::replace(eSLIMCirMan& replacement, const Subcircuit& subcir) {
    clearFanouts(subcir);
    setupMarksForReplacement(replacement);
    if (taboo != nullptr) {
      taboo->discardSubcircuit(subcir);
    }
    std::vector<std::unique_ptr<eSLIMCirObj>> nodes_aux = replaceInternal(replacement, subcir);
    int size_diff = subcir.nodes.size() - replacement.getNofGates(); 
    if (nodes_aux.size() + size_diff != nodes.size()) { 
      int nredundant = processRedundant(subcir);
      assert(nodes_aux.size() + size_diff + nredundant == nodes.size());
    }
    std::swap(nodes, nodes_aux);
  }

  void eSLIMCirMan::setupMarksForReplacement(eSLIMCirMan& replacement) {
    for (int i = replacement.getNofPis() + 1; i < replacement.getNofObjs() - replacement.getNofPos(); i++) {
      replacement.nodes[i]->isTaboo = traversal_id;
      replacement.nodes[i]->id = last_node_id++;
    }
  }

  void eSLIMCirMan::clearFanouts(const Subcircuit& subcir) {
    for (int n : subcir.nodes) {
     eSLIMCirObj* obj = nodes[n].get();
     nodes[0]->fanouts.erase(obj);
     for (int i : subcir.inputs) {
      nodes[i]->fanouts.erase(obj);
     }
    }
  }

  std::vector<std::unique_ptr<eSLIMCirObj>> eSLIMCirMan::replaceInternal(eSLIMCirMan& replacement, const Subcircuit& subcir) {
    std::unordered_map<int,int> out_map;
    for (int i = 0; i < subcir.outputs.size(); i++) {
      out_map[subcir.outputs[i]] = i;
    }
    std::vector<eSLIMCirObj*> invec;
    for (int i = 0; i < subcir.inputs.size(); i++) {
      invec.push_back(nodes[subcir.inputs[i]].get());
    }

    int size_diff = subcir.nodes.size() - replacement.getNofGates();
    std::vector<std::unique_ptr<eSLIMCirObj>> nodes_aux;
    nodes_aux.reserve(getNofObjs() - size_diff);
    for (int i = 0; i <= getNofPis(); i++) { // "<=" because of the constant node
      moveNode(nodes_aux, nodes[i]);
    }

    // it is possible that after the insertion no Po is reachable from some nodes.
    // These nodes can be remove.
    for (int i = 1; i <= getNofPos(); i++) {
      insertSorted(nodes[nodes.size() - i].get(), nodes_aux, replacement, out_map, invec);
    }
    assert (nodes_aux.size() <= nodes.size());
    int current_depth = 0;
    for (int i = 0; i < getNofPos(); i++) {
      int po_id = getNofObjs() - getNofPos() + i;
      moveNode(nodes_aux, nodes[po_id]);
      current_depth = std::max(current_depth, nodes_aux.back()->depth);
    }
    depth = current_depth;
    return nodes_aux;
  }

  int eSLIMCirMan::processRedundant(const Subcircuit& subcir) {
    int nredundant = 0;
    std::vector<int> to_process (subcir.inputs.begin(), subcir.inputs.end());
    std::unordered_set<int> seen (subcir.inputs.begin(), subcir.inputs.end());
    while (to_process.size() > 0) {
      int nd = to_process.back();
      to_process.pop_back();
      if (nodes[nd] != nullptr && !inSubcircuit(*nodes[nd])) {
        // This is a redundant node that can be discarded
        nredundant++;
        auto ptr = nodes[nd].get();
        if (taboo != nullptr) {
          taboo->removeRedundantNode(ptr);
        }
        for (auto& f : nodes[nd]->fanins) {
          f->fanouts.erase(nodes[nd].get());
          // in the dfs traversal the node was not copied
          if (!isCurrentTraversalId(*f)) {
            auto [it, inserted] = seen.insert(f->node_id);
            if (inserted) { // the node was not seen before
              to_process.push_back(f->node_id);
            }
          }
        }
      }
    }
    return nredundant;
  }

  void eSLIMCirMan::applyLevelBasedOrdering() {
    std::sort(nodes.begin() + getNofPis() + 1, nodes.begin() + getNofObjs() - getNofPos(),
      [](const std::unique_ptr<eSLIMCirObj>& a, const std::unique_ptr<eSLIMCirObj>& b) {
        return a->depth < b->depth || (a->depth == b->depth && a->id < b->id);
      }
    );
  }

  // Reorders the nodes to an alternative topological order.
  void eSLIMCirMan::applyDFSOrdering(const std::vector<int>& po_nodes) {
    incrementTraversalId();
    std::vector<std::unique_ptr<eSLIMCirObj>> nodes_reordered;
    nodes_reordered.reserve(nodes.size());
    for (int i = 0; i <= nof_pis; i++) {
      setTraversalId(*nodes[i]);
      nodes_reordered.push_back(std::move(nodes[i]));
    }
    for (int i = 0; i < nof_pos; i++) {
      int po_id = po_nodes[i];
      applyDFSOrderingRec(nodes[po_id]->fanins[0], nodes_reordered);
    }
    for (int i = 0; i < nof_pos; i++) {
      int po_id = getNofObjs() - getNofPos() + i;
      nodes_reordered.push_back(std::move(nodes[po_id]));
    }
    std::swap(nodes, nodes_reordered);
  }

  void eSLIMCirMan::applyDFSOrderingRec(eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted) {
    if (!isCurrentTraversalId(*obj)) {
      setTraversalId(*obj);
      for (auto& fan : obj->fanins) {
        applyDFSOrderingRec(fan, sorted);
      }
      auto& pobj = nodes[obj->node_id];
      pobj->node_id = sorted.size();
      sorted.push_back(std::move(pobj));
    }
  }

  void eSLIMCirMan::print() const {
    std::cout << "Inputs:";
    for (int i = 1; i <= nof_pis; i++) {
      std::cout << " " << i;
    }
    std::cout << "\n";
    for (int i = nof_pis + 1; i < getNofObjs() - getNofPos(); i++) {
      std::cout << nodes[i]->node_id << " :";
      for (auto& f : nodes[i]->fanins) {
        std::cout << " " << f->node_id;
      }
      std::cout << " - " << nodes[i]->tt << "\n";
    }
    std::cout << "Outputs:";
    for (int i = getNofObjs() - getNofPos(); i < getNofObjs(); i++) {
      std::cout << " " << nodes[i]->fanins[0]->node_id;
    }
    std::cout << "\n";
  }

  void eSLIMCirMan::print(const Subcircuit& scir) const {
    std::cout << "Inputs:";
    for (int i : scir.inputs) {
      std::cout << " " << i;
    }
    std::cout << "\n";
    for (int nd : scir.nodes) {
      std::cout << nodes[nd]->node_id << " :";
      for (auto& f : nodes[nd]->fanins) {
        std::cout << " " << f->node_id;
      }
      std::cout << " - " << nodes[nd]->tt << "\n";
    }
    std::cout << "Outputs:";
    for (int o : scir.outputs) {
      std::cout << " " << o;
    }
    std::cout << "\nForbidden pairs:";
    for (const auto & [out,inps] : scir.forbidden_pairs) {
      std::cout << "\n" << out << " :";
      for (int inp : inps) {
        std::cout << " " << inp;
      }
    }
    std::cout << "\n";
  }

  eSLIMCirMan eSLIMCirMan::duplicate() const {
    eSLIMCirMan dup(getNofObjs());
    for (int i = 0; i < getNofPis(); i++) {
      dup.addPi();
    }
    for (int i = getNofPis() + 1; i < getNofObjs() - getNofPos(); i++) {
      std::vector<int> fanins;
      for (const auto& f : nodes[i]->fanins) {
        fanins.push_back(f->node_id);
      }
      dup.addNode(fanins, nodes[i]->tt);
    }
    for (int i = getNofObjs() - getNofPos(); i < getNofObjs(); i++) {
      const auto& obj = nodes[i]->fanins[0];
      dup.addPo(obj->node_id, obj->tt == 1);
    }
    return dup;
  }

  void eSLIMCirMan::simplifyDuplicateFanins() {
    std::unordered_map<int,int> fanins;
    for (int i = getNofPis() + 1; i < getNofObjs() - getNofPos(); i++) {
      fanins.clear();
      for (auto it = nodes[i]->fanins.begin(); it != nodes[i]->fanins.end(); ) {
        int fanin_id = std::distance(nodes[i]->fanins.begin(), it);
        if (!fanins[(*it)->node_id]) {
          fanins[(*it)->node_id] = fanin_id + 1; // 0 should indicate that this node_id was not yet considered
          it++;
        } else {
          nodes[i]->tt = removeInputFromTT(nodes[i]->tt, fanins[(*it)->node_id] - 1, fanin_id);
          // In general, we do not expect many duplicate fanins. 
          // Hence, we immediatley delete from the vector.
          it = nodes[i]->fanins.erase(it);
        }
      }
    }
  }

  ABC_UINT64_T eSLIMCirMan::compressTT(ABC_UINT64_T tt, unsigned int input) {
    static constexpr ABC_UINT64_T filters1[] {0x1111111111111111ull, 0x303030303030303ull, 0xF000F000F000Full, 0xFF000000FFull, 0xFFFFull};
    static constexpr ABC_UINT64_T filters2[] {0x4444444444444444ull, 0x3030303030303030ull, 0xF000F000F000F00ull, 0xFF000000FF0000ull, 0xFFFF00000000ull};
    static constexpr int shifts[] {1,2,4,8,16};
    if (input == 5) {
      return tt & 0xFFFFFFFFull;
    }
    for (int i = input; i < 5; i++) {
      tt = (tt & filters1[i]) | ((tt & filters2[i]) >> shifts[i]);
    }
    return tt;
  }

  // we drop the lines from the tt where the values for inputs first_occurrence and second_occurrence do not coincide. Then we compress the tt.
  ABC_UINT64_T eSLIMCirMan::removeInputFromTT(ABC_UINT64_T tt, unsigned int first_occurrence, unsigned int second_occurrence) {
    assert (first_occurrence < 6 && second_occurrence && first_occurrence < second_occurrence); // we can only represent 6-input functions with the 64-bit ints

    // filter that gives all the tt-lines with the ith input is true
    static constexpr ABC_UINT64_T isTruePatterns[] {0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull, 0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};
    // filter that gives all the tt-lines with the ith input is false
    static constexpr ABC_UINT64_T isFalsePatterns[] {0x5555555555555555ull, 0x3333333333333333ull, 0xF0F0F0F0F0F0F0Full, 0xFF00FF00FF00FFull, 0xFFFF0000FFFFull, 0xFFFFFFFFull};
    // the first tt-line where the ith input is true
    static constexpr unsigned char firstTrueIn1[] {1, 2, 4, 8, 16, 32};

    ABC_UINT64_T true_filter = isTruePatterns[first_occurrence] & isTruePatterns[second_occurrence];
    ABC_UINT64_T false_filter = isFalsePatterns[first_occurrence] & isFalsePatterns[second_occurrence];
    // the first line of the tt where both considered inputs are true
    unsigned int shift = lsb(true_filter) - firstTrueIn1[first_occurrence];

    ABC_UINT64_T true_positions = tt & true_filter;
    ABC_UINT64_T false_positions = tt & false_filter;
    ABC_UINT64_T tt_new = false_positions | (true_positions >> shift);

    return compressTT(tt_new, second_occurrence);
  }


  void eSLIMCirMan::registerTabooList(TabooList* taboo) {
    this->taboo = taboo;
  }

  void eSLIMCirMan::unregisterTabooList() {
    this->taboo = nullptr;
  }


}
ABC_NAMESPACE_IMPL_END