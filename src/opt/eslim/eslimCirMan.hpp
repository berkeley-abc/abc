/**CFile****************************************************************

  FileName    [eslimCirMan.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Internal circuit representation.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM__ESLIMCIRMAN_hpp
#define ABC__OPT__ESLIM__ESLIMCIRMAN_hpp

#include <vector>
#include <memory>
#include <unordered_map>
#include <set>

#include "aig/gia/gia.h"
#include "base/abc/abc.h"
#include "misc/util/abc_namespaces.h"
#include "misc/util/abc_global.h"



ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  class Subcircuit;
  class eSLIMCirMan;
  class TabooList;
  template <typename SynthesisEngine, typename SelectionStrategy> class WindowMan;

  // Nodes must not have more than 6 fanins
  class eSLIMCirObj {

    private:

      // This comparator is used in sets of pointers to nodes.
      // As the order does not really matter, the comparator could be replaced by comparing addresses.
      // This would slightly simplify the code as we would not need to change the fanouts of replacement circuits
      // (unlike to the ids the addresses of the nodes in the replacement do not change during the replacement).
      // Nevertheless, we use this iterator to make iteration orders more predictable.
      struct eSLIMObjComp {
        bool operator()(eSLIMCirObj* a, eSLIMCirObj* b) const {
          return a->getId() < b->getId();
        }
      };

    public:

      eSLIMCirObj(int id, std::vector<eSLIMCirObj*>&& fanins);
      int getNFanins() const;
      int getTTLength() const;
      unsigned int getId() const;

      int node_id;
      std::vector<eSLIMCirObj*> fanins;
      std::set<eSLIMCirObj*, eSLIMObjComp> fanouts;
      ABC_UINT64_T tt; //truth table representing the function
      int depth = 0; // the step from a input/gate node to an output node is also counted -> depth differs from depths in abc
      int remaining_time = 0;

      int value1 = 0;

    private:
      unsigned int id = 0;
      // set traversal_id
      unsigned int trav_id = 0;
      unsigned int inSubcircuit = 0;
      unsigned int inTFI = 0;
      unsigned int inTFO = 0;
      unsigned int isTaboo = 0;

    friend eSLIMCirMan;
    friend TabooList;
  };

  class eSLIMCirMan {

    public:

      eSLIMCirMan(int nObjEstimate);
      eSLIMCirMan(Gia_Man_t * pGia);
      eSLIMCirMan(Abc_Ntk_t * pNtk, bool simplify);
      eSLIMCirMan(eSLIMCirMan& es_man, const Subcircuit& scir);
      
      // normalises the aig
      // static eSLIMCirMan eSLIMCirManFromGia(Gia_Man_t * pGia);
      static ABC_UINT64_T negateTT(ABC_UINT64_T tt, unsigned int nfanin);
      static ABC_UINT64_T ttNegateFanin(ABC_UINT64_T tt, unsigned int fan);
      static bool ttisnormal(ABC_UINT64_T tt);

      void registerTabooList(TabooList* taboo);
      void unregisterTabooList();

      void replace(eSLIMCirMan& replacement, const Subcircuit& subcir);


      Gia_Man_t* eSLIMCirManToGia();
      Abc_Ntk_t* eSLIMCirManToNtk();
      Abc_Ntk_t* eSLIMCirManToMappedNtk();
      void setupTimings();

      bool isConst(int id) const;
      bool isPi(int id) const; // or constant node
      bool isPo(int id) const;
      bool isGate(int id) const;

      bool isConst(const eSLIMCirObj&) const;
      bool isPi(const eSLIMCirObj&) const;

      bool isOnCricticalPath(const eSLIMCirObj&) const;

      int getNofObjs() const;
      int getNofPis() const;
      int getNofPos() const;
      int getNofGates() const;

      int getDepth() const;

      const eSLIMCirObj& getObj(int id) const;

      void incrementTraversalId() {traversal_id++;}
      void setTraversalId(eSLIMCirObj& obj);
      void setTraversalId(int n);
      bool isCurrentTraversalId(const eSLIMCirObj& obj) const;
      bool isCurrentTraversalId(int n) const;

      void setInSubcircuit(eSLIMCirObj& obj);
      void setInTFI(eSLIMCirObj& obj);
      void setInTFO(eSLIMCirObj& obj);
      bool inSubcircuit(const eSLIMCirObj& obj) const;
      bool inTFI(const eSLIMCirObj& obj) const;
      bool inTFO(const eSLIMCirObj& obj) const;

      void markSubcircuit(const std::vector<int>& nodes);
      void markCones(const std::vector<int>& nodes);
      void markConesRange(const std::vector<int>& nodes);

      int addPi();
      int addPo(int fanin, bool negated); 
      int addNode(const std::vector<int>& fanins, ABC_UINT64_T tt);

      void print() const;
      void print(const Subcircuit& scir) const;
      eSLIMCirMan duplicate() const;

    private:

      bool isTaboo(const eSLIMCirObj& obj, int taboo_time) const;
      void setTaboo(eSLIMCirObj& obj);
      
      eSLIMCirObj* getpObj(int id);
      const eSLIMCirObj* getpObj(int id) const;

      eSLIMCirObj* getPo(int id);

      static ABC_UINT64_T ttFromGiaObj(Gia_Man_t * pGia, Gia_Obj_t * pObj);
      static ABC_UINT64_T ttFromNtkObj(Abc_Ntk_t * pNtk, Abc_Obj_t * pObj);

      std::vector<std::unique_ptr<eSLIMCirObj>> replaceInternal(eSLIMCirMan& replacement, const Subcircuit& subcir);
      void setupMarksForReplacement(eSLIMCirMan& replacement);
      void clearFanouts(const Subcircuit& subcir);

      void insertSorted(eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                        eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec); 
      void insertSortedRec( eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                            eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec);
      
      void insertSortedRecRep(eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                              eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec);  
      void processRepFanin( eSLIMCirObj* obj, eSLIMCirObj* fan, int fid, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                            eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec);
      void processRepPo( eSLIMCirObj* obj, eSLIMCirObj* fan, int fid, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                            eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec);
      void processNonGateRepFanin(eSLIMCirObj* obj, eSLIMCirObj* fan, int fid, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted, 
                                  eSLIMCirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIMCirObj*>& in_vec);
      void addFans(eSLIMCirObj* out, eSLIMCirObj* in, int fin_id);
      
      
      int addGiaGate(Gia_Man_t * pGia, int node_id, std::vector<int>& node_ids, std::vector<bool>& is_node_negated);
      static ABC_UINT64_T sop2tt(char * pSop);
      static char* tt2sop(ABC_UINT64_T tt, int nVars, Mem_Flex_t * pMan);

      int insertNtkNodes(Abc_Ntk_t * pNtk, int node_id, std::unordered_map<int,int>& ids, bool simplify);

      int processRedundant(const Subcircuit& subcir);
      void moveNode(std::vector<std::unique_ptr<eSLIMCirObj>>& vec, std::unique_ptr<eSLIMCirObj>& pobj);
      void setMarks(eSLIMCirObj& pObj, int id);

      // The nodes vector contains nodes in topological order.
      // This does not necessarily ensure that if a < b we have lv(a) < lv(b) (lv: the level/depth of the node)
      // If nodes are sorted according to their levels i.e. a <= b iff lv(a) <= lv(b) then the nodes are also topologically sorted.
      void applyLevelBasedOrdering();
      void applyDFSOrdering(const std::vector<int>& po_nodes); // po_nodes must contain the node_id of each primary output
      void applyDFSOrderingRec(eSLIMCirObj* obj, std::vector<std::unique_ptr<eSLIMCirObj>>& sorted);

      // remove repeated fanins
      // The Gia representation does not allow repeated fanins.
      void simplifyDuplicateFanins();
      ABC_UINT64_T removeInputFromTT(ABC_UINT64_T tt, unsigned int first_occurrence, unsigned int second_occurrence);
      ABC_UINT64_T compressTT(ABC_UINT64_T tt, unsigned int input);

      unsigned int nof_pis = 0;
      unsigned int nof_pos = 0;
      std::vector<std::unique_ptr<eSLIMCirObj>> nodes;
      unsigned int last_node_id = 0;

      static constexpr int const_false_id = 0;
      unsigned int traversal_id = 0;

      int depth = 0;

      TabooList* taboo = nullptr;

      friend TabooList;
      template <typename SynthesisEngine, typename SelectionStrategy> friend class WindowMan;

  };

}
ABC_NAMESPACE_CXX_HEADER_END

#endif