/**CFile****************************************************************

  FileName    [synthesisSolver.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Incremental SAT backends for exact synthesis of Boolean relations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 10, 2026.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__SYNTHESISSOLVER_h
#define ABC__OPT__ESLIM3__SYNTHESISSOLVER_h

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <initializer_list>
#include <limits>
#include <memory>
#include <vector>

#include "cadicalSolver.h"
#include "sat/glucose3/AbcGlucose3.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class SynthesisSolver {
    friend struct eSLIM3TestAccess;
    public:
      explicit SynthesisSolver(unsigned mode);
      ~SynthesisSolver();
      SynthesisSolver(const SynthesisSolver&) = delete;
      SynthesisSolver& operator=(const SynthesisSolver&) = delete;
      void addClause(const std::vector<int>& clause);
      void addClause(std::initializer_list<int> clause);
      bool setOption(const char* name, int value);
      bool configure(const char* name);
      void setDeadline(std::chrono::steady_clock::time_point value);
      int solve(double timeout, const std::vector<int>& assumptions);
      double getRunTime() const;
      bool getValue(int variable);
      std::vector<bool> getModel(int maximum_variable);

    private:
      std::unique_ptr<CadicalSolver> cadical;
      bmcg3_sat_solver* glucose = nullptr;
      std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();
      std::vector<int> literals;
      int variables = 1;
      bool inconsistent = false;
      bool model_valid = false;
      int model_variables = 0;
      double runtime = 0;
      template<class Iterator> void convert(Iterator begin, Iterator end);
      template<class Iterator> void add(Iterator begin, Iterator end);
      int solvePortable(double timeout, std::chrono::steady_clock::time_point start);
  };

/**Function*************************************************************

  Synopsis    [Creates only the selected synthesis solver.]

***********************************************************************/
  inline SynthesisSolver::SynthesisSolver(unsigned mode) {
    if (mode == 6)
      glucose = bmcg3_sat_solver_start();
    else
      cadical.reset(new CadicalSolver);
  }

/**Function*************************************************************

  Synopsis    [Releases the incremental solver and its learned clauses.]

***********************************************************************/
  inline SynthesisSolver::~SynthesisSolver() {
    if (glucose)
      bmcg3_sat_solver_stop(glucose);
  }

/**Function*************************************************************

  Synopsis    [Configures the CaDiCaL backend before adding clauses.]

***********************************************************************/
  inline bool SynthesisSolver::setOption(const char* name, int value) {
    return cadical && cadical->setOption(name, value);
  }

/**Function*************************************************************

  Synopsis    [Selects a documented CaDiCaL configuration.]

***********************************************************************/
  inline bool SynthesisSolver::configure(const char* name) {
    return cadical && cadical->configure(name);
  }

/**Function*************************************************************

  Synopsis    [Shares the outer deadline without changing its allowance.]

***********************************************************************/
  inline void SynthesisSolver::setDeadline(std::chrono::steady_clock::time_point value) {
    deadline = value;
    if (cadical)
      cadical->setDeadline(value);
  }

/**Function*************************************************************

  Synopsis    [Converts signed one-based literals to the Glucose convention.]

***********************************************************************/
  template<class Iterator>
  inline void SynthesisSolver::convert(Iterator begin, Iterator end) {
    literals.clear();
    for (; begin != end; ++begin) {
      const int lit = *begin;
      assert(lit && lit != std::numeric_limits<int>::min());
      const int variable = lit < 0 ? -lit : lit;
      assert(variable < std::numeric_limits<int>::max() / 2);
      variables = std::max(variables, variable + 1);
      literals.push_back(2 * variable + (lit < 0));
    }
    bmcg3_sat_solver_set_nvars(glucose, variables);
  }

/**Function*************************************************************

  Synopsis    [Adds a clause while retaining an empty-clause contradiction.]

***********************************************************************/
  template<class Iterator>
  inline void SynthesisSolver::add(Iterator begin, Iterator end) {
    model_valid = false;
    if (cadical) {
      cadical->addClause(std::vector<int>(begin, end));
      return;
    }
    if (inconsistent)
      return;
    convert(begin, end);
    inconsistent = literals.empty() ||
      !bmcg3_sat_solver_addclause(glucose, literals.data(), static_cast<int>(literals.size()));
  }

/**Function*************************************************************

  Synopsis    [Adds an existing clause without copying it for CaDiCaL.]

***********************************************************************/
  inline void SynthesisSolver::addClause(const std::vector<int>& clause) {
    model_valid = false;
    if (cadical)
      cadical->addClause(clause);
    else
      add(clause.begin(), clause.end());
  }

/**Function*************************************************************

  Synopsis    [Adds a short clause without allocating a temporary vector.]

***********************************************************************/
  inline void SynthesisSolver::addClause(std::initializer_list<int> clause) {
    add(clause.begin(), clause.end());
  }

/**Function*************************************************************

  Synopsis    [Solves under assumptions and the remaining per-size allowance.]

  Description [Polls the steady clock between conflict batches on every
               platform. Glucose's native time limit is checked only at
               restart boundaries and can overrun short query allowances.]

***********************************************************************/
  inline int SynthesisSolver::solve(double timeout, const std::vector<int>& assumptions) {
    model_valid = false;
    model_variables = 0;
    if (cadical) {
      const int status = cadical->solve(timeout, assumptions);
      model_valid = status == 10;
      if (model_valid) model_variables = cadical->getVariableCount() + 1;
      return status;
    }
    const auto start = std::chrono::steady_clock::now();
    runtime = 0;
    const double remaining = deadline == std::chrono::steady_clock::time_point::max() ?
      std::numeric_limits<double>::infinity() : std::chrono::duration<double>(deadline - start).count();
    timeout = std::min(timeout, remaining);
    if (timeout <= 0)
      return 0;
    if (inconsistent)
      return 20;
    convert(assumptions.begin(), assumptions.end());
    const int status = solvePortable(timeout, start);
    runtime = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - start).count();
    return status > 0 ? 10 : status < 0 ? 20 : 0;
  }

/**Function*************************************************************

  Synopsis    [Polls a wall deadline between bounded incremental conflict batches.]

***********************************************************************/
  inline int SynthesisSolver::solvePortable(double timeout, std::chrono::steady_clock::time_point start) {
    // The ABC clock is CPU time on some hosts; it must not silently replace
    // a wall-clock deadline. A batch is an interruption, never an UNSAT proof.
    model_valid = false;
    model_variables = 0;
    constexpr int conflicts_per_batch = 128;
    bmcg3_sat_solver_set_runtime_limit(glucose, 0);
    bmcg3_sat_solver_set_conflict_budget(glucose, std::isfinite(timeout) ? conflicts_per_batch : 0);
    int status = 0;
    do {
      status = bmcg3_sat_solver_solve(glucose, literals.data(), static_cast<int>(literals.size()));
      if (status || std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() >= timeout)
        break;
      bmcg3_sat_solver_set_conflict_budget(glucose, conflicts_per_batch);
    } while (true);
    bmcg3_sat_solver_set_conflict_budget(glucose, 0);
    model_valid = status > 0;
    if (model_valid) model_variables = bmcg3_sat_solver_varnum(glucose);
    return status;
  }

/**Function*************************************************************

  Synopsis    [Returns the last SAT allowance's elapsed time in milliseconds.]

***********************************************************************/
  inline double SynthesisSolver::getRunTime() const {
    return cadical ? cadical->getRunTime() : runtime;
  }

/**Function*************************************************************

  Synopsis    [Reads a variable from the last satisfying model.]

***********************************************************************/
  inline bool SynthesisSolver::getValue(int variable) {
    assert(model_valid && variable > 0 && variable < model_variables);
    return cadical ? cadical->getValue(variable) : bmcg3_sat_solver_read_cex_varvalue(glucose, variable) != 0;
  }

/**Function*************************************************************

  Synopsis    [Copies the model for reconstruction and exhaustive verification.]

***********************************************************************/
  inline std::vector<bool> SynthesisSolver::getModel(int maximum_variable) {
    assert(model_valid && maximum_variable >= 0);
    // Variables reserved by the encoding but absent from every clause and
    // assumption are free. Give those trailing variables a defined value.
    std::vector<bool> model(std::size_t(maximum_variable) + 1, false);
    for (int variable = 1; variable <= maximum_variable && variable < model_variables; ++variable)
      model[variable] = getValue(variable);
    return model;
  }
}
ABC_NAMESPACE_CXX_HEADER_END
#endif
