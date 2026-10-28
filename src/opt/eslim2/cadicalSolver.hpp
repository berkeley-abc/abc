/**CFile****************************************************************

  FileName    [cadicalSolver.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Interface for Cadical SAT solver.]

  Author      [Franz-Xaver Reichl]

  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: cadicalSolver.hpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM2__SATINTERFACE_h
#define ABC__OPT__ESLIM2__SATINTERFACE_h

#include <vector>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <limits>

#include "sat/cadical/cadical.hpp"

ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM2 {

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
      std::vector<int> getFailed(const std::vector<int>& assumptions);
      bool isFailed(int lit);
      std::vector<int> getValues(const std::vector<int>& variables);
      bool getValue(int var);
      std::vector<bool> getModel();
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

  inline CadicalSolver::TimeoutTerminator::TimeoutTerminator(double max_runtime) : max_runtime(max_runtime) {
  }

  inline bool CadicalSolver::TimeoutTerminator::terminate() {
    auto current_time = std::chrono::steady_clock::now();
    std::chrono::duration<double> elapsed_seconds = current_time - start;
    return elapsed_seconds.count() > max_runtime;
  }



  inline CadicalSolver::~CadicalSolver()=default;

  inline void CadicalSolver::addClause(const std::vector<int>& clause) {
    for (auto& l: clause) {
      solver.add(l);
    }
    solver.add(0);
  }

  inline void CadicalSolver::addClause(std::vector<int>&& clause) {
    for (auto& l: clause) {
      solver.add(l);
    }
    solver.add(0);
  }

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

  inline void CadicalSolver::assume(const std::vector<int>& assumptions) {
    for (auto& l: assumptions) {
      solver.assume(l);
    }
  }


  inline void CadicalSolver::assumeAll(const std::vector<int>& assumptions) {
    solver.reset_assumptions();
    assume(assumptions);
  }

  inline int CadicalSolver::solve(double timeout, const std::vector<int>& assumptions) {
    assumeAll(assumptions);
    return solve(timeout);
  }

  inline int CadicalSolver::solve(const std::vector<int>& assumptions) {
    assumeAll(assumptions);
    return solve();
  }

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
    last_runtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start).count();
    // Always disconnect the stack-allocated terminator, including error paths.
    solver.disconnect_terminator();
    if (solver.state() == CaDiCaL::INVALID) {
      std::cerr << "Solver is in invalid state" << std::endl;
      return -1;
    }
    return status;
  }

  inline int CadicalSolver::solve() {
    return solve(std::numeric_limits<double>::infinity());
  }

  inline double CadicalSolver::getRunTime() const {
    return last_runtime;
  }

  inline std::vector<int> CadicalSolver::getFailed(const std::vector<int>& assumptions) {
    std::vector<int> failed_literals;
    for (auto& l: assumptions) {
      if (solver.failed(l)) {
        failed_literals.push_back(l);
      }
    }
    return failed_literals;
  }

  inline bool CadicalSolver::isFailed(int lit) {
    return solver.failed(lit);
  }

  inline std::vector<int> CadicalSolver::getValues(const std::vector<int>& variables) {
    std::vector<int> assignment;
    for (auto& v: variables) {
      assignment.push_back(val(v));
    }
    return assignment;
  }

  inline bool CadicalSolver::getValue(int var) {
    return val(var) > 0;
  }

  inline std::vector<bool> CadicalSolver::getModel() {
    std::vector<bool> assignment;
    assignment.push_back(false);
    for (int v = 1; v <= solver.vars(); v++) {
      assignment.push_back(val(v) > 0);
    }
    return assignment;
  }

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
