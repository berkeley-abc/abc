/**CFile****************************************************************

  FileName    [cadicalSolver.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Interface for Cadical SAT solver.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - November 9, 2026; derived from eSLIM2.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__CADICALSOLVER_h
#define ABC__OPT__ESLIM3__CADICALSOLVER_h

#include <vector>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <limits>

#include "sat/cadical/cadical.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {

  class CadicalSolver {
    public:
      ~CadicalSolver();
      void addClause(const std::vector<int>& clause);
      void addClause(std::vector<int>&& clause);
      void addCombinedClause(const std::vector<int>& cl1, const std::vector<int>& cl2, const std::vector<int>& cl3);
      void assume(const std::vector<int>& assumptions);
      int solve(double timeout, const std::vector<int>& assumptions);
      int solve(const std::vector<int>& assumptions);
      int solve(double timeout);
      int solve();
      void setDeadline(std::chrono::steady_clock::time_point value) { deadline = value; }
      bool setOption(const char* name, int value) { return solver.set(name, value); }
      bool configure(const char* name) { return solver.configure(name); }
      std::vector<int> getFailed(const std::vector<int>& assumptions);
      bool isFailed(int lit);
      std::vector<int> getValues(const std::vector<int>& variables);
      bool getValue(int var);
      std::vector<bool> getModel();
      int getVariableCount();
      double getRunTime() const;

    private:
      void assumeAll(const std::vector<int>& assumptions);
      int val(int variable);
      double last_runtime = 0;
      std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();
      CaDiCaL::Solver solver;

    public:
      class TimeoutTerminator : public CaDiCaL::Terminator {
        public:
          TimeoutTerminator(double max_runtime);
          bool terminate();

        private:
          double max_runtime; //in seconds
          std::chrono::time_point<std::chrono::steady_clock> start = std::chrono::steady_clock::now();
      };

  };

/**Function*************************************************************

  Synopsis    [Initializes the elapsed-time limit for one SAT query.]

***********************************************************************/
  inline CadicalSolver::TimeoutTerminator::TimeoutTerminator(double max_runtime) : max_runtime(max_runtime) {
  }

/**Function*************************************************************

  Synopsis    [Reports whether the SAT query has exhausted its time allowance.]

***********************************************************************/
  inline bool CadicalSolver::TimeoutTerminator::terminate() {
    auto current_time = std::chrono::steady_clock::now();
    std::chrono::duration<double> elapsed_seconds = current_time - start;
    return elapsed_seconds.count() > max_runtime;
  }



  inline CadicalSolver::~CadicalSolver()=default;

/**Function*************************************************************

  Synopsis    [Adds a zero-terminated clause to the owned SAT solver.]

***********************************************************************/
  inline void CadicalSolver::addClause(const std::vector<int>& clause) {
    for (auto& l: clause) {
      solver.add(l);
    }
    solver.add(0);
  }

/**Function*************************************************************

  Synopsis    [Adds a zero-terminated clause to the owned SAT solver.]

***********************************************************************/
  inline void CadicalSolver::addClause(std::vector<int>&& clause) {
    for (auto& l: clause) {
      solver.add(l);
    }
    solver.add(0);
  }

/**Function*************************************************************

  Synopsis    [Concatenates three literal vectors into one SAT clause.]

***********************************************************************/
  inline void CadicalSolver::addCombinedClause(const std::vector<int>& cl1, const std::vector<int>& cl2, const std::vector<int>& cl3) {
    for (auto& l: cl1) {
      solver.add(l);
    }
    for (auto& l: cl2) {
      solver.add(l);
    }
    for (auto& l: cl3) {
      solver.add(l);
    }
    solver.add(0);
  }

/**Function*************************************************************

  Synopsis    [Installs the supplied assumptions for the next SAT query.]

***********************************************************************/
  inline void CadicalSolver::assume(const std::vector<int>& assumptions) {
    for (auto& l: assumptions) {
      solver.assume(l);
    }
  }


/**Function*************************************************************

  Synopsis    [Installs the supplied assumption vector for the next SAT query.]

***********************************************************************/
  inline void CadicalSolver::assumeAll(const std::vector<int>& assumptions) {
    solver.reset_assumptions();
    assume(assumptions);
  }

/**Function*************************************************************

  Synopsis    [Runs the owned SAT solver and reports SAT, UNSAT or interruption.]

***********************************************************************/
  inline int CadicalSolver::solve(double timeout, const std::vector<int>& assumptions) {
    assumeAll(assumptions);
    return solve(timeout);
  }

/**Function*************************************************************

  Synopsis    [Runs the owned SAT solver and reports SAT, UNSAT or interruption.]

***********************************************************************/
  inline int CadicalSolver::solve(const std::vector<int>& assumptions) {
    assumeAll(assumptions);
    return solve();
  }

/**Function*************************************************************

  Synopsis    [Runs the owned SAT solver and reports SAT, UNSAT or interruption.]

***********************************************************************/
  inline int CadicalSolver::solve(double timeout) {
    const auto start = std::chrono::steady_clock::now();
    const double remaining = deadline == std::chrono::steady_clock::time_point::max() ?
        std::numeric_limits<double>::infinity() : std::chrono::duration<double>(deadline - start).count();
    timeout = std::min(timeout, remaining);
    if (timeout <= 0) {
      last_runtime = 0;
      return 0;
    }
    TimeoutTerminator terminator(timeout);
    solver.connect_terminator(&terminator);
    int status = solver.solve();
    last_runtime = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - start).count();
    // Always disconnect the stack-allocated terminator, including error paths.
    solver.disconnect_terminator();
    if (solver.state() == CaDiCaL::INVALID) {
      std::cerr << "Solver is in invalid state" << std::endl;
      return -1;
    }
    return status;
  }

/**Function*************************************************************

  Synopsis    [Runs the owned SAT solver and reports SAT, UNSAT or interruption.]

***********************************************************************/
  inline int CadicalSolver::solve() {
    return solve(std::numeric_limits<double>::infinity());
  }

/**Function*************************************************************

  Synopsis    [Returns the most recent solver runtime in milliseconds.]

***********************************************************************/
  inline double CadicalSolver::getRunTime() const {
    return last_runtime;
  }

/**Function*************************************************************

  Synopsis    [Returns failed assumption literals after an UNSAT result.]

***********************************************************************/
  inline std::vector<int> CadicalSolver::getFailed(const std::vector<int>& assumptions) {
    std::vector<int> failed_literals;
    for (auto& l: assumptions) {
      if (solver.failed(l)) {
        failed_literals.push_back(l);
      }
    }
    return failed_literals;
  }

/**Function*************************************************************

  Synopsis    [Tests whether a literal belongs to the failed assumption set.]

***********************************************************************/
  inline bool CadicalSolver::isFailed(int lit) {
    return solver.failed(lit);
  }

/**Function*************************************************************

  Synopsis    [Reads signed model values for the requested SAT variables.]

***********************************************************************/
  inline std::vector<int> CadicalSolver::getValues(const std::vector<int>& variables) {
    std::vector<int> assignment;
    for (auto& v: variables) {
      assignment.push_back(val(v));
    }
    return assignment;
  }

/**Function*************************************************************

  Synopsis    [Reads the Boolean model value of a SAT variable.]

***********************************************************************/
  inline bool CadicalSolver::getValue(int var) {
    return val(var) > 0;
  }

/**Function*************************************************************

  Synopsis    [Returns the satisfying assignment indexed by SAT variable.]

***********************************************************************/
  inline std::vector<bool> CadicalSolver::getModel() {
    std::vector<bool> assignment;
    assignment.push_back(false);
    for (int v = 1; v <= solver.vars(); v++) {
      assignment.push_back(val(v) > 0);
    }
    return assignment;
  }

/**Function*************************************************************

  Synopsis    [Returns the largest variable known to the owned solver.]

***********************************************************************/
  inline int CadicalSolver::getVariableCount() {
    return solver.vars();
  }

/**Function*************************************************************

  Synopsis    [Returns a signed model literal, choosing positive for an unassigned variable.]

***********************************************************************/
  inline int CadicalSolver::val(int variable) {
    auto l = solver.val(variable);
    auto v = abs(l);
    if (v == variable) {
      return l;
    } else {
      return variable;
    }
  }

}
ABC_NAMESPACE_CXX_HEADER_END
#endif
