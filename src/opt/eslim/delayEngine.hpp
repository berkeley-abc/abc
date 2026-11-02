/**CFile****************************************************************

  FileName    [delayEngine.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Implementation of delay based SAT encoding.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM__DELAYENGINE_hpp
#define ABC__OPT__ESLIM__DELAYENGINE_hpp

#include <map>

#include "misc/util/abc_global.h"

#include "relationSynthesiser.hpp"


ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM {

  class DelayEngine : public RelationSynthesiser {

    public:
      // Find a replacement with at most max_size gates that yields minimum delay
      static eSLIMCirMan synthesizeMinimumDelayCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log);
      // Find a replacement with at most max_size gates that yields minimum delay. Among these circuits find one of minimum size
      static eSLIMCirMan synthesizeMinimumDelayAreaCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log);
      // First minimize area, then minimize delay
      static eSLIMCirMan synthesizeMinimumAreaDelayCircuit(const Relation& relation, const Subcircuit& subcir, const eSLIMConfig& cfg, eSLIMLog& log);
      // Find a smaller replacement that must not increase delay
      static eSLIMCirMan synthesizeMinimumAreaDelayConstraintCircuit(const Relation& relation, const Subcircuit& subcir, unsigned int delay, const eSLIMConfig& cfg, eSLIMLog& log);

    private:

    std::vector<int> unique_arrival_times;
    std::vector<int> inputid2uniqueid;
    unsigned int max_delay;
    int symmetry_selector;
    int symmetry_selector_assignment;
    // Indicate the length of the longest paths from inputs to gates
    std::vector<std::vector<std::vector<int>>> delay_variables;
    std::vector<std::vector<std::vector<int>>> output_delays;

    std::map<int, int, std::greater<int>> delay_selectors;
    std::map<int, std::vector<int>, std::greater<int>> delays2delay_variables;

    DelayEngine(const Relation& relation, const Subcircuit& subcir, unsigned int max_size, const eSLIMConfig& cfg, eSLIMLog& log);
    int existsReplacement(unsigned int size, unsigned int delay, double timeout);
    int existsReplacement(unsigned int delay, double timeout);
    std::vector<int> getAssumptions(unsigned int delay);
    std::vector<int> getAssumptions(unsigned int size, unsigned int delay);
    void setupVariables();

    unsigned int getDelayFromDelayVariables(const std::vector<bool>& model);
    unsigned int computeDelay(const std::vector<bool>& model);

    std::vector<bool> reduceArea(unsigned int max_delay, unsigned int initial_area);
    std::vector<bool> reduceDelay(unsigned int max_size, unsigned int initial_delay);

    int getDelaySelector(int delay);
    void setupDelayConstraints();
    void constrainDelayVariables();

  };


}
ABC_NAMESPACE_CXX_HEADER_END
#endif