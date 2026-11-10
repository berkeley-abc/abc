/**CFile****************************************************************

  FileName    [eslim3CirMan.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Internal circuit representation.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__ESLIM3CIRMAN_h
#define ABC__OPT__ESLIM3__ESLIM3CIRMAN_h

#include <vector>
#include <memory>
#include <unordered_map>
#include <set>

#include "aig/gia/gia.h"
#include "base/abc/abc.h"
#include "misc/util/abc_namespaces.h"
#include "misc/util/abc_global.h"



ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class Subcircuit;
  class eSLIM3CirMan;
  class TabooList;
  template <typename SynthesisEngine, typename SelectionStrategy> class WindowMan;

  // Nodes must not have more than 6 fanins
  class eSLIM3CirObj {

    private:

      // This comparator is used in sets of pointers to nodes.
      // As the order does not really matter, the comparator could be replaced by comparing addresses.
      // This would slightly simplify the code as we would not need to change the fanouts of replacement circuits
      // (unlike to the ids the addresses of the nodes in the replacement do not change during the replacement).
      // Nevertheless, we use this iterator to make iteration orders more predictable.
      struct eSLIM3ObjComp {
        bool operator()(eSLIM3CirObj* a, eSLIM3CirObj* b) const {
          return a->getId() < b->getId();
        }
      };

    public:

      eSLIM3CirObj(int id, std::vector<eSLIM3CirObj*>&& fanins);
      int getNFanins() const;
      int getTTLength() const;
      unsigned int getId() const;

      int node_id;
      std::vector<eSLIM3CirObj*> fanins;
      std::set<eSLIM3CirObj*, eSLIM3ObjComp> fanouts;
      ABC_UINT64_T tt = 0; //truth table representing the function (including constant zero)
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
      unsigned int root_failures = 0;

    friend eSLIM3CirMan;
    friend TabooList;
  };

  class eSLIM3CirMan {

    public:

      eSLIM3CirMan(int nObjEstimate);
      eSLIM3CirMan(Gia_Man_t * pGia);
      eSLIM3CirMan(Abc_Ntk_t * pNtk, bool simplify);
      eSLIM3CirMan(eSLIM3CirMan& es_man, const Subcircuit& scir);

      // normalises the aig
      // static eSLIM3CirMan eSLIM3CirManFromGia(Gia_Man_t * pGia);
      static ABC_UINT64_T negateTT(ABC_UINT64_T tt, unsigned int nfanin);
      static ABC_UINT64_T ttNegateFanin(ABC_UINT64_T tt, unsigned int fan);
      static bool ttisnormal(ABC_UINT64_T tt);

      void registerTabooList(TabooList* taboo);
      void unregisterTabooList();

      void replace(eSLIM3CirMan& replacement, const Subcircuit& subcir);


      Gia_Man_t* eSLIM3CirManToGia();
      Abc_Ntk_t* eSLIM3CirManToNtk();
      Abc_Ntk_t* eSLIM3CirManToMappedNtk();
      void setupTimings();

      bool isConst(int id) const;
      bool isPi(int id) const; // or constant node
      bool isPo(int id) const;
      bool isGate(int id) const;

      bool isConst(const eSLIM3CirObj&) const;
      bool isPi(const eSLIM3CirObj&) const;

      bool isOnCricticalPath(const eSLIM3CirObj&) const;

      int getNofObjs() const;
      int getNofPis() const;
      int getNofPos() const;
      int getNofGates() const;

      int getDepth() const;

      const eSLIM3CirObj& getObj(int id) const;

      void incrementTraversalId() {traversal_id++;}
      void setTraversalId(eSLIM3CirObj& obj);
      void setTraversalId(int n);
      bool isCurrentTraversalId(const eSLIM3CirObj& obj) const;
      bool isCurrentTraversalId(int n) const;

      void setInSubcircuit(eSLIM3CirObj& obj);
      void setInTFI(eSLIM3CirObj& obj);
      void setInTFO(eSLIM3CirObj& obj);
      bool inSubcircuit(const eSLIM3CirObj& obj) const;
      bool inTFI(const eSLIM3CirObj& obj) const;
      bool inTFO(const eSLIM3CirObj& obj) const;

      void markSubcircuit(const std::vector<int>& nodes);
      void markCones(const std::vector<int>& nodes);
      void markConesRange(const std::vector<int>& nodes);

      int addPi();
      int addPo(int fanin, bool negated);
      int addNode(const std::vector<int>& fanins, ABC_UINT64_T tt);

      void print() const;
      void print(const Subcircuit& scir) const;
      eSLIM3CirMan duplicate() const;
      eSLIM3CirMan permuteInputs(const std::vector<unsigned>& old_to_new) const;

    private:

      // Frozen boundary timing for independently optimized windows. These
      // vectors are empty for a manager representing the whole circuit.
      std::vector<unsigned> window_arrivals, window_required;
      unsigned window_delay_bound = 0;
      friend struct eSLIM3TestAccess;

      struct RelationWindowEntry {
        unsigned generation = 0, references = 0;
        int local_id = 0;
        bool inside = false, listed = false;
      };
      struct RelationWindowScratch {
        unsigned generation = 0;
        std::vector<RelationWindowEntry> entries;
        std::vector<int> region, boundary, frontier, next;
/**Function*************************************************************

  Synopsis    [Starts a new window without clearing the whole enclosing graph.]

***********************************************************************/
        void begin(unsigned objects) {
          if (entries.size() < objects) entries.resize(objects);
          if (!++generation) {
            for (auto& entry : entries) entry.generation = 0;
            generation = 1;
          }
          region.clear(); boundary.clear(); frontier.clear(); next.clear();
        }
/**Function*************************************************************

  Synopsis    [Initializes one window entry on its first use in this generation.]

***********************************************************************/
        RelationWindowEntry& get(int id) {
          auto& entry = entries[id];
          if (entry.generation != generation) {
            entry = RelationWindowEntry{};
            entry.generation = generation;
          }
          return entry;
        }
      };
      // Separate marks preserve the cut's TFI/TFO traversal state. Scratch
      // belongs to this manager, and generations also handle reused node IDs.
      mutable std::unique_ptr<RelationWindowScratch> relation_window_scratch;
      friend class RelationGenerator;

      bool isTaboo(const eSLIM3CirObj& obj, int taboo_time) const;
      void setTaboo(eSLIM3CirObj& obj);

      eSLIM3CirObj* getpObj(int id);
      const eSLIM3CirObj* getpObj(int id) const;

      eSLIM3CirObj* getPo(int id);

      static ABC_UINT64_T ttFromGiaObj(Gia_Man_t * pGia, Gia_Obj_t * pObj);
      static ABC_UINT64_T ttFromNtkObj(Abc_Ntk_t * pNtk, Abc_Obj_t * pObj);

      std::vector<std::unique_ptr<eSLIM3CirObj>> replaceInternal(eSLIM3CirMan& replacement, const Subcircuit& subcir);
      void setupMarksForReplacement(eSLIM3CirMan& replacement);
      void clearFanouts(const Subcircuit& subcir);

      void insertSorted(eSLIM3CirObj* obj, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted,
                        eSLIM3CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM3CirObj*>& in_vec);
      void insertSortedRec( eSLIM3CirObj* obj, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted,
                            eSLIM3CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM3CirObj*>& in_vec);

      void insertSortedRecRep(eSLIM3CirObj* obj, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted,
                              eSLIM3CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM3CirObj*>& in_vec);
      void processRepFanin( eSLIM3CirObj* obj, eSLIM3CirObj* fan, int fid, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted,
                            eSLIM3CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM3CirObj*>& in_vec);
      void processRepPo( eSLIM3CirObj* obj, eSLIM3CirObj* fan, int fid, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted,
                            eSLIM3CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM3CirObj*>& in_vec);
      void processNonGateRepFanin(eSLIM3CirObj* obj, eSLIM3CirObj* fan, int fid, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted,
                                  eSLIM3CirMan& replacement, const std::unordered_map<int,int>& out_map, const std::vector<eSLIM3CirObj*>& in_vec);
      void addFans(eSLIM3CirObj* out, eSLIM3CirObj* in, int fin_id);


      int addGiaGate(Gia_Man_t * pGia, int node_id, std::vector<int>& node_ids, std::vector<bool>& is_node_negated);
      static ABC_UINT64_T sop2tt(char * pSop);
      static char* tt2sop(ABC_UINT64_T tt, int nVars, Mem_Flex_t * pMan);

      int insertNtkNodes(Abc_Ntk_t * pNtk, int node_id, std::unordered_map<int,int>& ids, bool simplify);

      int processRedundant(const Subcircuit& subcir);
      void moveNode(std::vector<std::unique_ptr<eSLIM3CirObj>>& vec, std::unique_ptr<eSLIM3CirObj>& pobj);
      void setMarks(eSLIM3CirObj& pObj, int id);

      // The nodes vector contains nodes in topological order.
      // This does not necessarily ensure that if a < b we have lv(a) < lv(b) (lv: the level/depth of the node)
      // If nodes are sorted according to their levels i.e. a <= b iff lv(a) <= lv(b) then the nodes are also topologically sorted.
      void applyLevelBasedOrdering();
      void applyDFSOrdering(const std::vector<int>& po_nodes); // po_nodes must contain the node_id of each primary output
      void applyDFSOrderingRec(eSLIM3CirObj* obj, std::vector<std::unique_ptr<eSLIM3CirObj>>& sorted);

      // remove repeated fanins
      // The Gia representation does not allow repeated fanins.
      void simplifyDuplicateFanins();
      ABC_UINT64_T removeInputFromTT(ABC_UINT64_T tt, unsigned int first_occurrence, unsigned int second_occurrence);
      ABC_UINT64_T compressTT(ABC_UINT64_T tt, unsigned int input);

      unsigned int nof_pis = 0;
      unsigned int nof_pos = 0;
      std::vector<std::unique_ptr<eSLIM3CirObj>> nodes;
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
