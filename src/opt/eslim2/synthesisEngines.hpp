/**CFile****************************************************************

  FileName    [synthesisEngines.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Synthesis engines]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: synthesisEngines.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__SYNTHESISENGINES_hpp
#define ABC__OPT__ESLIM2__SYNTHESISENGINES_hpp


#include "misc/util/abc_global.h"

#include "eslim2CirMan.hpp"
#include "areaEngine.hpp"
#include "delayEngine.hpp"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

  class Relation;
  class Subcircuit;
  struct eSLIM2Config;
  class eSLIM2Log;

  class AreaMinimizer {
    public:
      static eSLIM2CirMan optimize(const eSLIM2CirMan& encompassing, const Relation& relation, const Subcircuit& subcir,
                                  const eSLIM2Config& cfg, eSLIM2Log& log) {
        return AreaEngine::synthesiseMinimumSizeCircuit(relation, subcir, cfg, log);
      }
    private:
      AreaMinimizer() = default;
  };

  class AreaDelayConstraintMinimizer {
    public:
      static eSLIM2CirMan optimize(eSLIM2CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM2Config& cfg, eSLIM2Log& log, bool* complete = nullptr) {
        subcir.setupTimings(encompassing);
        const unsigned bound = cfg.area_depth_bound >= 0 ? unsigned(cfg.area_depth_bound) : unsigned(encompassing.getDepth());
        return DelayEngine::synthesizeMinimumAreaDelayConstraintCircuit(relation, subcir, bound, cfg, log, complete);
      }
    private:
      AreaDelayConstraintMinimizer() = default;
  };

  class AreaDelayMinimizer {
    public:
      static eSLIM2CirMan optimize(eSLIM2CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM2Config& cfg, eSLIM2Log& log) {
        subcir.setupTimings(encompassing);
        return DelayEngine::synthesizeMinimumAreaDelayCircuit(relation, subcir, cfg, log);
      }
    private:
      AreaDelayMinimizer() = default;
  };

  class DelayMinimizer {
    public:
      static eSLIM2CirMan optimize(eSLIM2CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM2Config& cfg, eSLIM2Log& log) {
        int max_crossing_path = subcir.setupTimings(encompassing);
        unsigned int max_size = std::min(cfg.subcircuit_max_size, static_cast<unsigned int>(subcir.nodes.size() + cfg.additional_gates));
        return DelayEngine::synthesizeMinimumDelayCircuit(relation, subcir, max_crossing_path, max_size, cfg, log);
      }
    private:
      DelayMinimizer() = default;
  };

  class DelayAreaMinimizer {
    public:
      static eSLIM2CirMan optimize(eSLIM2CirMan& encompassing, const Relation& relation, Subcircuit& subcir,
                                  const eSLIM2Config& cfg, eSLIM2Log& log) {
        int max_crossing_path = subcir.setupTimings(encompassing);
        unsigned int max_size = std::min(cfg.subcircuit_max_size, static_cast<unsigned int>(subcir.nodes.size() + cfg.additional_gates));
        return DelayEngine::synthesizeMinimumDelayAreaCircuit(relation, subcir, max_crossing_path, max_size, cfg, log);
      }
    private:
      DelayAreaMinimizer() = default;
  };


  template<class T>
  struct isDelayEngine : std::integral_constant< bool,
    std::is_same<eSLIM2::AreaDelayMinimizer, typename std::remove_cv<T>::type>::value
    ||  std::is_same<eSLIM2::AreaDelayConstraintMinimizer, typename std::remove_cv<T>::type>::value
    ||  std::is_same<eSLIM2::DelayMinimizer, typename std::remove_cv<T>::type>::value
    ||  std::is_same<eSLIM2::DelayAreaMinimizer, typename std::remove_cv<T>::type>::value
  > {};

  static_assert(!isDelayEngine<AreaMinimizer>::value);
  static_assert(isDelayEngine<AreaDelayMinimizer>::value);
  static_assert(isDelayEngine<AreaDelayConstraintMinimizer>::value);
  static_assert(isDelayEngine<DelayMinimizer>::value);
  static_assert(isDelayEngine<DelayAreaMinimizer>::value);


}

ABC_NAMESPACE_CXX_HEADER_END
#endif
