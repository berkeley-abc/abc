/**CFile****************************************************************

  FileName    [tabooList.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Taboo list for subcircuit selection.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__TABOOLIST_h
#define ABC__OPT__ESLIM2__TABOOLIST_h

#include <set>
#include <random>
#include <algorithm>
#include <deque>

#include "misc/util/abc_namespaces.h"

#include "eslim2CirMan.h"
#include "subcircuit.h"
#include "utils.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  class TabooList {
    friend struct eSLIM2TestAccess;

    public:
      TabooList(eSLIM2CirMan& es_man);
      int getRandomNonTaboo(std::mt19937& rng, double taboo_ratio, unsigned int taboo_time, eSLIM2Log* log = nullptr);
      template<typename BiasCondition>
      int getBiasedRandomNonTaboo(std::mt19937& rng, unsigned int bias, double taboo_ratio, unsigned int taboo_time, eSLIM2Log* log = nullptr);
      void reset();
      void recordFailure(int node);

    private:
      struct eSLIM2CirObjCompBase {
        bool operator()(eSLIM2CirObj* a, eSLIM2CirObj* b) const {
          return a->getId() < b->getId();
        }
      };

      struct eSLIM2CirObjComp  {
        bool operator()(eSLIM2CirObj* a, eSLIM2CirObj* b) const {
          return a->isTaboo < b->isTaboo || (a->isTaboo == b->isTaboo && eSLIM2CirObjCompBase()(a,b));
        }
      };

      void updateTaboo(double taboo_ratio, unsigned int taboo_time);
      void registerReplacement(eSLIM2CirMan& replacement, const Subcircuit& subcir);
      void discardSubcircuit(const Subcircuit& subcir);
      void removeRedundantNode(eSLIM2CirObj* nptr);
      void fill();
      void registerNeighborhood(const Subcircuit& subcir);
      void enqueueNeighbor(eSLIM2CirObj* node);
      int takeNeighbor();
      bool acceptFailedRoot(eSLIM2CirObj* node, std::mt19937& rng, eSLIM2Log* log);

      void addNode(eSLIM2CirObj* pobj);
      void discardNode(eSLIM2CirObj* pobj);
      void addNonTaboo(eSLIM2CirObj* pobj);
      void removeNonTaboo(eSLIM2CirObj* pobj);


      eSLIM2CirMan& es_man;
      std::set<eSLIM2CirObj*, eSLIM2CirObjComp> taboo_nodes;
      std::set<eSLIM2CirObj*, eSLIM2CirObjCompBase> non_taboo_nodes;
      std::vector<eSLIM2CirObj*> random_nodes;
      std::unordered_map<eSLIM2CirObj*, size_t> random_positions;
      std::deque<eSLIM2CirObj*> neighborhood;
      bool prefer_neighborhood = true;
      static constexpr unsigned max_neighborhood = 64;
      static constexpr unsigned max_root_failures = 4;
      static constexpr unsigned max_root_draws = 8;

    friend eSLIM2CirMan;
  };

/**Function*************************************************************

  Synopsis    [Initializes the selectable and temporarily excluded gate sets.]

***********************************************************************/
  inline TabooList::TabooList(eSLIM2CirMan& es_man)
                  : es_man(es_man) {
    fill();
  }

/**Function*************************************************************

  Synopsis    [Adds all current internal gates to the selectable set.]

***********************************************************************/
  inline void TabooList::fill() {
    for (int i = es_man.getNofPis() + 1; i < es_man.getNofObjs()-es_man.getNofPos(); i++) {
      auto pObj = es_man.nodes[i].get();
      pObj->root_failures = 0;
      addNonTaboo(pObj);
    }
  }

/**Function*************************************************************

  Synopsis    [Resets selection state for the current graph.]

***********************************************************************/
  inline void TabooList::reset() {
    taboo_nodes.clear();
    non_taboo_nodes.clear();
    random_nodes.clear();
    random_positions.clear();
    neighborhood.clear();
    prefer_neighborhood = true;
    fill();
  }

/**Function*************************************************************

  Synopsis    [Releases expired or excess entries from the taboo set.]

***********************************************************************/
  inline void TabooList::updateTaboo(double taboo_ratio, unsigned int taboo_time) {
    assert (taboo_ratio > 0 && taboo_ratio < 1);
    auto it = taboo_nodes.begin();
    while (it != taboo_nodes.end()) {
      if (!es_man.isTaboo(*(*it), taboo_time)) {
        addNonTaboo(*it);
        it = taboo_nodes.erase(it);
      } else if (taboo_nodes.size() > static_cast<double>(es_man.getNofGates()) * taboo_ratio) {
        addNonTaboo(*it);
        it = taboo_nodes.erase(it);
      } else {
        return;
      }
    }
  }

/**Function*************************************************************

  Synopsis    [Replaces old cut entries with the newly installed taboo gates.]

***********************************************************************/
  inline void TabooList::registerReplacement(eSLIM2CirMan& replacement, const Subcircuit& subcir) {
    discardSubcircuit(subcir);
    for (int i = replacement.getNofPis() + 1; i < replacement.getNofObjs() - replacement.getNofPos(); i++) {
      auto pObj = replacement.nodes[i].get();
      taboo_nodes.insert(pObj);
    }
  }

/**Function*************************************************************

  Synopsis    [Removes all selected cut gates from the selection sets.]

***********************************************************************/
  inline void TabooList::discardSubcircuit(const Subcircuit& subcir) {
    for (int nd : subcir.nodes) {
      discardNode(es_man.nodes[nd].get());
    }
  }

/**Function*************************************************************

  Synopsis    [Removes a deleted gate from the selection sets.]

***********************************************************************/
  inline void TabooList::removeRedundantNode(eSLIM2CirObj* nptr) {
    discardNode(nptr);
  }


/**Function*************************************************************

  Synopsis    [Interleaves nearby and globally sampled gates with bounded failure backoff.]

***********************************************************************/
  inline int TabooList::getRandomNonTaboo(std::mt19937& rng, double taboo_ratio, unsigned int taboo_time, eSLIM2Log* log) {
    updateTaboo(taboo_ratio, taboo_time);
    const int nearby = takeNeighbor();
    if (nearby >= 0) {
      if (log) ++log->neighborhood_roots;
      return nearby;
    }
    assert(non_taboo_nodes.size() > 0);
    std::uniform_int_distribution<std::mt19937::result_type> udistr(0, non_taboo_nodes.size() - 1);
    for (unsigned draw = 0; ; ++draw) {
      auto* node = random_nodes[udistr(rng)];
      if (draw + 1 == max_root_draws || acceptFailedRoot(node, rng, log)) return node->node_id;
    }
  }

/**Function*************************************************************

  Synopsis    [Interleaves nearby and globally biased gates with bounded failure backoff.]

***********************************************************************/
  template<typename BiasCondition>
  int TabooList::getBiasedRandomNonTaboo(std::mt19937& rng, unsigned int bias, double taboo_ratio, unsigned int taboo_time, eSLIM2Log* log) {
    updateTaboo(taboo_ratio, taboo_time);
    const int nearby = takeNeighbor();
    if (nearby >= 0) {
      if (log) ++log->neighborhood_roots;
      return nearby;
    }
    assert(!random_nodes.empty());
    std::uniform_int_distribution<unsigned> choose(0, random_nodes.size() - 1);
    std::uniform_int_distribution<unsigned> accept(0, std::max(1u, bias) - 1);
    for (unsigned draw = 0; ; ++draw) {
      auto* node = random_nodes[choose(rng)];
      if (draw + 1 == max_root_draws ||
          ((BiasCondition::useBias(es_man, *node) || !accept(rng)) && acceptFailedRoot(node, rng, log)))
        return node->node_id;
    }
  }

/**Function*************************************************************

  Synopsis    [Records an optimal or unchanged cut without permanently excluding its root.]

***********************************************************************/
  inline void TabooList::recordFailure(int node) {
    auto* object = es_man.nodes[node].get();
    object->root_failures = std::min(max_root_failures, object->root_failures + 1);
  }

/**Function*************************************************************

  Synopsis    [Softly reduces repeated draws of previously unproductive roots.]

***********************************************************************/
  inline bool TabooList::acceptFailedRoot(eSLIM2CirObj* node, std::mt19937& rng, eSLIM2Log* log) {
    if (!node->root_failures || !(rng() & ((1u << node->root_failures) - 1))) return true;
    if (log) ++log->failed_root_draws_skipped;
    return false;
  }

/**Function*************************************************************

  Synopsis    [Queues a live neighboring gate and resets its failure history.]

***********************************************************************/
  inline void TabooList::enqueueNeighbor(eSLIM2CirObj* node) {
    if (!es_man.isGate(node->node_id) || es_man.inSubcircuit(*node)) return;
    node->root_failures = 0;
    if (std::find(neighborhood.begin(), neighborhood.end(), node) != neighborhood.end()) return;
    if (neighborhood.size() == max_neighborhood) neighborhood.pop_front();
    neighborhood.push_back(node);
  }

/**Function*************************************************************

  Synopsis    [Captures the live boundary before a replacement removes its old fanout links.]

  Description [Object addresses survive topological renumbering. Every node
  deletion removes its queue entry through discardNode before releasing it.]

***********************************************************************/
  inline void TabooList::registerNeighborhood(const Subcircuit& subcir) {
    const auto enqueueFanouts = [&](eSLIM2CirObj* node) {
      unsigned visited = 0;
      for (auto* fanout : node->fanouts) {
        if (++visited > max_neighborhood) break;
        enqueueNeighbor(fanout);
      }
    };
    for (int input : subcir.inputs) {
      auto* node = es_man.nodes[input].get();
      enqueueNeighbor(node);
      enqueueFanouts(node);
    }
    for (int output : subcir.outputs)
      enqueueFanouts(es_man.nodes[output].get());
  }

/**Function*************************************************************

  Synopsis    [Interleaves nearby roots with global exploration after a graph change.]

***********************************************************************/
  inline int TabooList::takeNeighbor() {
    if (neighborhood.empty()) return -1;
    prefer_neighborhood = !prefer_neighborhood;
    if (prefer_neighborhood) return -1;
    while (!neighborhood.empty()) {
      auto* node = neighborhood.front();
      neighborhood.pop_front();
      if (non_taboo_nodes.count(node)) return node->node_id;
    }
    return -1;
  }

/**Function*************************************************************

  Synopsis    [Adds a newly installed gate to the taboo set.]

***********************************************************************/
  inline void TabooList::addNode(eSLIM2CirObj* pobj) {
    taboo_nodes.insert(pobj);
  }

/**Function*************************************************************

  Synopsis    [Removes a gate from both selectable and taboo sets.]

***********************************************************************/
  inline void TabooList::discardNode(eSLIM2CirObj* pobj) {
    neighborhood.erase(std::remove(neighborhood.begin(), neighborhood.end(), pobj), neighborhood.end());
    removeNonTaboo(pobj);
    taboo_nodes.erase(pobj);
  }

/**Function*************************************************************

  Synopsis    [Adds a gate to the selectable non-taboo set.]

***********************************************************************/
  inline void TabooList::addNonTaboo(eSLIM2CirObj* pobj) {
    if (non_taboo_nodes.insert(pobj).second) {
      random_positions[pobj] = random_nodes.size();
      random_nodes.push_back(pobj);
    }
  }

/**Function*************************************************************

  Synopsis    [Removes a gate from the selectable non-taboo set.]

***********************************************************************/
  inline void TabooList::removeNonTaboo(eSLIM2CirObj* pobj) {
    auto position = random_positions.find(pobj);
    if (position != random_positions.end()) {
      random_nodes[position->second] = random_nodes.back();
      random_positions[random_nodes.back()] = position->second;
      random_nodes.pop_back();
      random_positions.erase(position);
    }
    non_taboo_nodes.erase(pobj);
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
