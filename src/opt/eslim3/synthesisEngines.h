/**CFile****************************************************************

  FileName    [synthesisEngines.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Synthesis engines]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__SYNTHESISENGINES_h
#define ABC__OPT__ESLIM3__SYNTHESISENGINES_h

#include <algorithm>

#include "misc/util/abc_global.h"

#include "eslim3CirMan.h"
#include "areaEngine.h"
#include "delayEngine.h"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class Relation;
  class Subcircuit;
  struct eSLIM3Config;
  class eSLIM3Log;

  class AreaMinimizer {
    public:
/**Function*************************************************************

  Synopsis    [Finds a minimum-area implementation of the selected relation.]

***********************************************************************/
      static eSLIM3CirMan optimize(const eSLIM3CirMan& encompassing, const Relation& relation, const Subcircuit& subcir,
                                  const eSLIM3Config& cfg, eSLIM3Log& log, bool* complete = nullptr) {
        return AreaEngine::synthesiseMinimumSizeCircuit(relation, subcir, cfg, log, complete);
      }
    private:
      AreaMinimizer() = default;
  };

  class AreaDelayConstraintMinimizer {
    public:
/**Function*************************************************************

  Synopsis    [Refine critical cuts while the requested global depth target is unmet.]

  Description [Without a percentage target, retain unrestricted refinement.
  Slack cuts cannot shorten the current critical path, so with a target
  their budget is better spent finding smaller implementations.]

***********************************************************************/
      static bool refineDepthForCut(const eSLIM3CirMan& encompassing, const Subcircuit& subcir,
                                    const eSLIM3Config& cfg) {
        if (!cfg.refine_depth) return false;
        if (cfg.depth_floor < 0) return true;
        if (encompassing.getDepth() <= cfg.depth_floor) return false;
        return std::any_of(subcir.outputs.begin(), subcir.outputs.end(),
            [&](int output) { return encompassing.isOnCricticalPath(encompassing.getObj(output)); });
      }
/**Function*************************************************************

  Synopsis    [Minimizes area under the active depth and equal-area timing bounds.]

***********************************************************************/
      static eSLIM3CirMan optimize(eSLIM3CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM3Config& cfg, eSLIM3Log& log, bool* complete = nullptr) {
        subcir.setupTimings(encompassing);
        const unsigned bound = cfg.areaDepthBound(encompassing.getDepth());
        eSLIM3Config active = cfg;
        active.refine_depth = refineDepthForCut(encompassing, subcir, cfg);
        return DelayEngine::synthesizeMinimumAreaDelayConstraintCircuit(relation, subcir, bound, active, log, complete,
            cfg.protect_neutral_depth ? encompassing.getDepth() : -1);
      }
    private:
      AreaDelayConstraintMinimizer() = default;
  };

  class AreaDelayMinimizer {
    public:
/**Function*************************************************************

  Synopsis    [Minimizes area first and then delay using the cut boundary timings.]

***********************************************************************/
      static eSLIM3CirMan optimize(eSLIM3CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM3Config& cfg, eSLIM3Log& log) {
        subcir.setupTimings(encompassing);
        return DelayEngine::synthesizeMinimumAreaDelayCircuit(relation, subcir, cfg, log);
      }
    private:
      AreaDelayMinimizer() = default;
  };

  class DelayMinimizer {
    public:
/**Function*************************************************************

  Synopsis    [Minimizes delay within the configured replacement size limit.]

***********************************************************************/
      static eSLIM3CirMan optimize(eSLIM3CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM3Config& cfg, eSLIM3Log& log) {
        int max_crossing_path = subcir.setupTimings(encompassing);
        unsigned int max_size = std::min(cfg.subcircuit_max_size, static_cast<unsigned int>(subcir.nodes.size() + cfg.additional_gates));
        return DelayEngine::synthesizeMinimumDelayCircuit(relation, subcir, max_crossing_path, max_size, cfg, log);
      }
    private:
      DelayMinimizer() = default;
  };

  class DelayAreaMinimizer {
    public:
/**Function*************************************************************

  Synopsis    [Minimizes delay first and then area within the replacement size limit.]

***********************************************************************/
      static eSLIM3CirMan optimize(eSLIM3CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM3Config& cfg, eSLIM3Log& log) {
        int max_crossing_path = subcir.setupTimings(encompassing);
        unsigned int max_size = std::min(cfg.subcircuit_max_size, static_cast<unsigned int>(subcir.nodes.size() + cfg.additional_gates));
        return DelayEngine::synthesizeMinimumDelayAreaCircuit(relation, subcir, max_crossing_path, max_size, cfg, log);
      }
    private:
      DelayAreaMinimizer() = default;
  };


  template<class T>
  struct isDelayEngine : std::integral_constant< bool,
    std::is_same<eSLIM3::AreaDelayMinimizer, typename std::remove_cv<T>::type>::value
    ||  std::is_same<eSLIM3::AreaDelayConstraintMinimizer, typename std::remove_cv<T>::type>::value
    ||  std::is_same<eSLIM3::DelayMinimizer, typename std::remove_cv<T>::type>::value
    ||  std::is_same<eSLIM3::DelayAreaMinimizer, typename std::remove_cv<T>::type>::value
  > {};

  static_assert(!isDelayEngine<AreaMinimizer>::value);
  static_assert(isDelayEngine<AreaDelayMinimizer>::value);
  static_assert(isDelayEngine<AreaDelayConstraintMinimizer>::value);
  static_assert(isDelayEngine<DelayMinimizer>::value);
  static_assert(isDelayEngine<DelayAreaMinimizer>::value);


}

ABC_NAMESPACE_CXX_HEADER_END
#endif
