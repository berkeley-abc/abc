/**CFile****************************************************************

  FileName    [eslim2CirMan.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Internal circuit representation.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eslim2CirMan.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__ESLIM2CIRMAN_hpp
#define ABC__OPT__ESLIM2__ESLIM2CIRMAN_hpp

#include <vector>
#include <memory>
#include <unordered_map>
#include <set>

#include "aig/gia/gia.h"
#include "base/abc/abc.h"
#include "misc/util/abc_namespaces.h"
#include "misc/util/abc_global.h"



ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  class Subcircuit;
  class eSLIM2CirMan;
  class TabooList;
  template <typename SynthesisEngine, typename SelectionStrategy> class WindowMan;

  // Nodes must not have more than 6 fanins
  class eSLIM2CirObj {

    private:

      // This comparator is used in sets of pointers to nodes.
      // As the order does not really matter, the comparator could be replaced by comparing addresses.
      // This would slightly simplify the code as we would not need to change the fanouts of replacement circuits
      // (unlike to the ids the addresses of the nodes in the replacement do not change during the replacement).
      // Nevertheless, we use this iterator to make iteration orders more predictable.
      struct eSLIM2ObjComp {
        bool operator()(eSLIM2CirObj* a, eSLIM2CirObj* b) const {
          return a->getId() < b->getId();
        }
      };

    public:

      eSLIM2CirObj(int id, std::vector<eSLIM2CirObj*>&& fanins);
      int getNFanins() const;
      int getTTLength() const;
      unsigned int getId() const;

      int node_id;
      std::vector<eSLIM2CirObj*> fanins;
      std::set<eSLIM2CirObj*, eSLIM2ObjComp> fanouts;
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

    friend eSLIM2CirMan;
    friend TabooList;
  };

  class eSLIM2CirMan {

    public:

      eSLIM2CirMan(int nObjEstimate);
      eSLIM2CirMan(Gia_Man_t * pGia);
      eSLIM2CirMan(Abc_Ntk_t * pNtk, bool simplify);
      eSLIM2CirMan(eSLIM2CirMan& es_man, const Subcircuit& scir);

      // normalises the aig
      // static eSLIM2CirMan eSLIM2CirManFromGia(Gia_Man_t * pGia);
      static ABC_UINT64_T negateTT(ABC_UINT64_T tt, unsigned int nfanin);
      static ABC_UINT64_T ttNegateFanin(ABC_UINT64_T tt, unsigned int fan);
      static bool ttisnormal(ABC_UINT64_T tt);

      void registerTabooList(TabooList* taboo);
      void unregisterTabooList();

      void replace(eSLIM2CirMan& replacement, const Subcircuit& subcir);


      Gia_Man_t* eSLIM2CirManToGia();
      Abc_Ntk_t* eSLIM2CirManToNtk();
      Abc_Ntk_t* eSLIM2CirManToMappedNtk();
      void setupTimings();

      bool isConst(int id) const;
      bool isPi(int id) const; // or constant node
      bool isPo(int id) const;
      bool isGate(int id) const;

      bool isConst(const eSLIM2CirObj&) const;
      bool isPi(const eSLIM2CirObj&) const;

      bool isOnCricticalPath(const eSLIM2CirObj&) const;

      int getNofObjs() const;
      int getNofPis() const;
      int getNofPos() const;
      int getNofGates() const;

      int getDepth() const;

      const eSLIM2CirObj& getObj(int id) const;

      void incrementTraversalId() {traversal_id++;}
      void setTraversalId(eSLIM2CirObj& obj);
      void setTraversalId(int n);
      bool isCurrentTraversalId(const eSLIM2CirObj& obj) const;
      bool isCurrentTraversalId(int n) const;

      void setInSubcircuit(eSLIM2CirObj& obj);
      void setInTFI(eSLIM2CirObj& obj);
      void setInTFO(eSLIM2CirObj& obj);
      bool inSubcircuit(const eSLIM2CirObj& obj) const;
      bool inTFI(const eSLIM2CirObj& obj) const;
      bool inTFO(const eSLIM2CirObj& obj) const;

      void markSubcircuit(const std::vector<int>& nodes);
      void markCones(const std::vector<int>& nodes);
      void markConesRange(const std::vector<int>& nodes);

      int addPi();
      int addPo(int fanin, bool negated);
      int addNode(const std::vector<int>& fanins, ABC_UINT64_T tt);

      void print() const;
      void print(const Subcircuit& scir) const;
      eSLIM2CirMan duplicate() const;

    private:

      // Frozen boundary timing for independently optimized windows. These
      // vectors are empty for a manager representing the whole circuit.
      std::vector<unsigned> window_arrivals, window_required;
      unsigned window_delay_bound = 0;

      struct SimulationEntry {
        ABC_UINT64_T first = 0, second = 0, truth = 0, version = 0;
        std::vector<ABC_UINT64_T> values;
        bool live = false;
      };
      struct SimulationCache {
        std::unordered_map<unsigned, SimulationEntry> entries;
        std::vector<ABC_UINT64_T> reference, versions;
        ABC_UINT64_T next_version = ABC_UINT64_T(1) << 32;
        unsigned words = 0;
      };
      // One thread may use each manager at a time. IDs select cache entries;
      // fanin-value versions and truth tables validate them. Each version names
      // only one value vector. Rebuilding the manager starts an empty cache.
      mutable std::unique_ptr<SimulationCache> simulation_cache;
      friend class RelationGenerator;

      bool isTaboo(const eSLIM2CirObj& obj, int taboo_time) const;
      void setTaboo(eSLIM2CirObj& obj);

      eSLIM2CirObj* getpObj(int id);
      const eSLIM2CirObj* getpObj(int id) const;

      eSLIM2CirObj* getPo(int id);

      static ABC_UINT64_T ttFromGiaObj(Gia_Man_t * pGia, Gia_Obj_t * pObj);
      static ABC_UINT64_T ttFromNtkObj(Abc_Ntk_t * pNtk, Abc_Obj_t * pObj);

      std::vector<std::unique_ptr<eSLIM2CirObj>> replaceInternal(eSLIM2CirMan& replacement, const Subcircuit& subcir);
      void setupMarksForReplacement(eSLIM2CirMan& replacement);
      void clearFanouts(const Subcircuit& subcir);

      void insertSorted(eSLIM2CirObj* obj, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted,
                        eSLIM2CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM2CirObj*>& in_vec);
      void insertSortedRec( eSLIM2CirObj* obj, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted,
                            eSLIM2CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM2CirObj*>& in_vec);

      void insertSortedRecRep(eSLIM2CirObj* obj, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted,
                              eSLIM2CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM2CirObj*>& in_vec);
      void processRepFanin( eSLIM2CirObj* obj, eSLIM2CirObj* fan, int fid, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted,
                            eSLIM2CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM2CirObj*>& in_vec);
      void processRepPo( eSLIM2CirObj* obj, eSLIM2CirObj* fan, int fid, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted,
                            eSLIM2CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM2CirObj*>& in_vec);
      void processNonGateRepFanin(eSLIM2CirObj* obj, eSLIM2CirObj* fan, int fid, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted,
                                  eSLIM2CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM2CirObj*>& in_vec);
      void addFans(eSLIM2CirObj* out, eSLIM2CirObj* in, int fin_id);


      int addGiaGate(Gia_Man_t * pGia, int node_id, std::vector<int>& node_ids, std::vector<bool>& is_node_negated);
      static ABC_UINT64_T sop2tt(char * pSop);
      static char* tt2sop(ABC_UINT64_T tt, int nVars, Mem_Flex_t * pMan);

      int insertNtkNodes(Abc_Ntk_t * pNtk, int node_id, std::unordered_map<int,int>& ids, bool simplify);

      int processRedundant(const Subcircuit& subcir);
      void moveNode(std::vector<std::unique_ptr<eSLIM2CirObj>>& vec, std::unique_ptr<eSLIM2CirObj>& pobj);
      void setMarks(eSLIM2CirObj& pObj, int id);

      // The nodes vector contains nodes in topological order.
      // This does not necessarily ensure that if a < b we have lv(a) < lv(b) (lv: the level/depth of the node)
      // If nodes are sorted according to their levels i.e. a <= b iff lv(a) <= lv(b) then the nodes are also topologically sorted.
      void applyLevelBasedOrdering();
      void applyDFSOrdering(const std::vector<int>& po_nodes); // po_nodes must contain the node_id of each primary output
      void applyDFSOrderingRec(eSLIM2CirObj* obj, std::vector<std::unique_ptr<eSLIM2CirObj>>& sorted);

      // remove repeated fanins
      // The Gia representation does not allow repeated fanins.
      void simplifyDuplicateFanins();
      ABC_UINT64_T removeInputFromTT(ABC_UINT64_T tt, unsigned int first_occurrence, unsigned int second_occurrence);
      ABC_UINT64_T compressTT(ABC_UINT64_T tt, unsigned int input);

      unsigned int nof_pis = 0;
      unsigned int nof_pos = 0;
      std::vector<std::unique_ptr<eSLIM2CirObj>> nodes;
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
