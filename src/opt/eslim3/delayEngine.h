/**CFile****************************************************************

  FileName    [delayEngine.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Implementation of delay based SAT encoding.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__DELAYENGINE_h
#define ABC__OPT__ESLIM3__DELAYENGINE_h

#include <map>

#include "misc/util/abc_global.h"

#include "relationSynthesiser.h"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class DelayEngine : public RelationSynthesiser {

    public:
      // Find a replacement with at most max_size gates that yields minimum delay
      static eSLIM3CirMan synthesizeMinimumDelayCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIM3Config& cfg, eSLIM3Log& log);
      // Find a replacement with at most max_size gates that yields minimum delay. Among these circuits find one of minimum size
      static eSLIM3CirMan synthesizeMinimumDelayAreaCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIM3Config& cfg, eSLIM3Log& log);
      // First minimize area, then minimize delay
      static eSLIM3CirMan synthesizeMinimumAreaDelayCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIM3Config& cfg, eSLIM3Log& log);
      // Find a smaller replacement that must not increase delay
      static eSLIM3CirMan synthesizeMinimumAreaDelayConstraintCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, const eSLIM3Config& cfg, eSLIM3Log& log, bool* complete = nullptr, int equal_size_bound = -1);

    private:

    std::vector<int> unique_arrival_times;
    std::vector<int> inputid2uniqueid;
    unsigned int max_delay;
    int fixed_delay = -1;
    unsigned fixed_earliest = 0;
    unsigned fixed_span = 0;
    std::vector<std::vector<int>> fixed_levels;
    // Indicate the length of the longest paths from inputs to gates
    std::vector<std::vector<std::vector<int>>> delay_variables;
    std::vector<std::vector<std::vector<int>>> output_delays;

    std::map<int, int, std::greater<int>> delay_selectors;
    std::map<int, std::vector<int>, std::greater<int>> delays2delay_variables;

    DelayEngine(const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIM3Config& cfg, eSLIM3Log& log, int fixed_bound = -1, int equal_size_bound = -1);
    bool setupFixedDelay(unsigned bound, eSLIM3Log& log, int equal_size_bound, bool refine_depth);
    void constrainFixedOutputs(unsigned bound, int guard = 0);
    void refineDepth(std::vector<bool>& model, const eSLIM3Config& cfg, eSLIM3Log& log);
    int existsReplacement(unsigned int size, unsigned int delay, double timeout);
    int existsReplacement(unsigned int delay, double timeout);
    std::vector<int> getAssumptions(unsigned int delay);
    std::vector<int> getAssumptions(unsigned int size, unsigned int delay);
    void setupVariables();

    unsigned int getDelayFromDelayVariables(const std::vector<bool>& model);
    unsigned int computeDelay(const std::vector<bool>& model);

    std::vector<bool> reduceArea(unsigned int max_delay, unsigned int initial_area, bool* complete = nullptr);
    std::vector<bool> reduceDelay(unsigned int max_size, unsigned int initial_delay);

    int getDelaySelector(int delay);
    void setupDelayConstraints();
    void constrainDelayVariables();

  };


}
ABC_NAMESPACE_CXX_HEADER_END
#endif
