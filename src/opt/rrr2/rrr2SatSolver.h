/**HFile****************************************************************

  FileName    [rrr2SatSolver.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Experimental redundancy removal and resubstitution.]

  Synopsis    [Redundancy analysis and optimization: SatSolver.]

  Author      [Yukio Miyasaka]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 1, 2026.]

  Description [Derived from the rrr package. The original command is unchanged.]

***********************************************************************/

#pragma once

#include <algorithm>

#include <sat/bsat/satSolver.h>

#include "rrr2Parameter.h"
#include "rrr2Utils.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr2 {

  template <typename Ntk>
  class SatSolver {
  private:
    // pointer to network
    Ntk *pNtk;

    // parameters
    int nVerbose;
    int nConflictLimit;
    bool fProfile;
    bool fDirectCnf;
    bool fGeneralize;
    int nWindow;
    int nFirstConflicts;
    bool fWindowActive = false;

    // data
    sat_solver *pSat;
    bool status; // false indicates trivial UNSAT
    int  target; // node for which miter has been encoded
    std::vector<int> vVars; // SAT variable for each node
    std::vector<int> vLits; // temporary storage
    bool fUpdate;
    int iLastRemoved;
    int iLastCandidate;
    bool fLastCompl;

    // stats
    int nCalls;
    int nSats;
    int nUnsats;
    double durationRedundancy;
    double durationFeasibility;
    double durationEncode;
    double durationSolve;
    int nMiters;
    int nQueries, nWindowCalls, nWindowProved, nRetries;

    // callback
    void ActionCallback(Action const &action);

    // encode
    void EncodeNode(sat_solver *p, std::vector<int> const &v, int id, int to_negate = -1) const;
    void EncodeMiter(sat_solver *p, std::vector<int> &v, int id, bool fWindow = false); // create a careset miter where the counterpart has the output of target negated
    void SetTarget(int id);
    int SolveCurrent(bool fRetry);
    std::vector<VarValue> Generalize(std::vector<VarValue> const &model) const;

  public:
    // constructors
    SatSolver(Parameter const *pPar);
    ~SatSolver();
    void AssignNetwork(Ntk *pNtk_, bool fReuse);

    // checks
    SatResult CheckRedundancy(int id, int idx);
    SatResult CheckFeasibility(int id, int fi, bool c);

    // cex
    std::vector<VarValue> GetCex();

    // stats
    void ResetSummary();
    summary<int> GetStatsSummary() const;
    summary<double> GetTimesSummary() const;
  };

  // {{{ Callback

  template <typename Ntk>
  void SatSolver<Ntk>::ActionCallback(Action const &action) {
    if(target == -1) {
      return;
    }
    switch(action.type) {
    case REMOVE_FANIN:
      if(action.id != target) {
        fUpdate = true;
      }
      break;
    case REMOVE_UNUSED:
      break;
    case REMOVE_BUFFER:
    case REMOVE_CONST:
      if(action.id == target) {
        target = -1;
      }
      break;
    case ADD_FANIN:
      if(action.id != target) {
        fUpdate = true;
      }
      break;
    case TRIVIAL_COLLAPSE:
      break;
    case TRIVIAL_DECOMPOSE:
      fUpdate = true;
      break;
    case SORT_FANINS:
      break;
    case READ:
      status = false;
      target = -1;
      fUpdate = false;
      break;
    case SAVE:
      break;
    case LOAD:
      target = -1;
      break;
    case POP_BACK:
      break;
    default:
      assert(0);
    }
  }

  // }}}

  // {{{ Encode

  template <typename Ntk>
  void SatSolver<Ntk>::EncodeNode(sat_solver *p, std::vector<int> const &v, int id, int to_negate) const {
    if(fDirectCnf && pNtk->GetNumFanins(id) > 2) {
      // y <=> AND(literals): one binary implication per input and one clause
      // for the reverse implication. No internal chain variables are needed.
      std::vector<int> clause;
      clause.reserve(pNtk->GetNumFanins(id) + 1);
      clause.push_back(toLit(v[id]));
      pNtk->ForEachFanin(id, [&](int fi, bool c) {
        int input = toLitCond(v[fi], c ^ (fi == to_negate));
        int pair[2] = {lit_neg(toLit(v[id])), input};
        int result = sat_solver_addclause(p, pair, pair + 2);
        (void)result;
        assert(result);
        clause.push_back(lit_neg(input));
      });
      int result = sat_solver_addclause(p, clause.data(), clause.data() + clause.size());
      (void)result;
      assert(result);
      return;
    }
    int RetValue;
    int x = -1, y = -1;
    bool cx = false, cy = false;
    assert(pNtk->GetNodeType(id) == AND);
    std::string delim;
    if(nVerbose) {
      std::cout << "node " << std::setw(3) << id << ": ";
    }
    pNtk->ForEachFanin(id, [&](int fi, bool c) {
      if(x == -1) {
        x = v[fi];
        cx = c ^ (fi == to_negate);
      } else if(y == -1) {
        y = v[fi];
        cy = c ^ (fi == to_negate);
      } else {
        int z = sat_solver_addvar(p);
        if(nVerbose) {
          std::cout << delim << z << " = " << (cx? "!": "") << x << " & " << (cy? "!": "") << y << std::endl;
          delim = std::string(10, ' ');
        }
        RetValue = sat_solver_add_and(p, z, x, y, cx, cy, 0);
        assert(RetValue);
        x = z;
        cx = false;
        y = v[fi];
        cy = c ^ (fi == to_negate);
      }
    });
    if(x == -1) {
      if(nVerbose) {
        std::cout << delim << v[id] << " = !0" << std::endl;
      }
      RetValue = sat_solver_add_const(p, v[id], 0);
      assert(RetValue);
    } else if(y == -1) {
      if(nVerbose) {
        std::cout << delim << v[id] << " = " << (cx? "!": "") << x << std::endl;
      }
      RetValue = sat_solver_add_buffer(p, v[id], x, cx);
      assert(RetValue);
    } else {
      if(nVerbose) {
        std::cout << delim << v[id] << " = " << (cx? "!": "") << x << " & " << (cy? "!": "") << y << std::endl;
      }
      RetValue = sat_solver_add_and(p, v[id], x, y, cx, cy, 0);
      assert(RetValue);
    }
  }

  /**Function*************************************************************

    Synopsis    [Encodes a full miter or a conservative local context.]

    Description [Window boundary inputs are free. Preserving every boundary
    output therefore preserves the full network. A SAT or unknown window
    result is retried with full context before returning a counterexample.]

  ***********************************************************************/
  template <typename Ntk>
  void SatSolver<Ntk>::EncodeMiter(sat_solver *p, std::vector<int> &v, int id, bool fWindow) {
    v.clear();
    sat_solver_restart(p);
    status = true;
    int nNodes = pNtk->GetNumNodes();
    sat_solver_setnvars(p, nNodes);
    v.resize(nNodes);
    for(int i = 0; i < nNodes; i++) v[i] = i;
    int result = sat_solver_add_const(p, v[0], 1);
    (void)result;
    assert(result);
    std::vector<unsigned char> inside, base;
    std::vector<int> outputs;
    if(fWindow) {
      inside.assign(nNodes, 0);
      base.assign(nNodes, 0);
      std::vector<int> distance(nNodes, -1), back(nNodes, -1);
      distance[id] = 0;
      inside[id] = 1;
      pNtk->ForEachTfo(id, false, [&](int fo) {
        int d = -1;
        pNtk->ForEachFanin(fo, [&](int fi) { d = std::max(d, distance[fi]); });
        distance[fo] = d + 1;
        inside[fo] = distance[fo] <= nWindow;
      });
      std::vector<unsigned char> frontier(nNodes, 0);
      pNtk->ForEachInt([&](int node) {
        if(inside[node]) back[node] = 0;
        else pNtk->ForEachFanin(node, [&](int fi) { if(inside[fi]) frontier[fi] = 1; });
      });
      pNtk->ForEachPoDriver([&](int fi) { if(inside[fi]) frontier[fi] = 1; });
      pNtk->ForEachIntReverse([&](int node) {
        if(back[node] < 0) return;
        base[node] = 1;
        if(back[node] < nWindow) pNtk->ForEachFanin(node, [&](int fi) {
          int d = back[node] + 1;
          if(back[fi] < 0 || d < back[fi]) back[fi] = d;
        });
      });
      pNtk->ForEachInt([&](int node) { if(frontier[node]) outputs.push_back(node); });
    } else {
      pNtk->ForEachPoDriver([&](int fi) { outputs.push_back(fi); });
    }
    pNtk->ForEachInt([&](int node) {
      if(!fWindow || base[node]) EncodeNode(p, v, node);
    });
    if(std::find(outputs.begin(), outputs.end(), id) != outputs.end()) return;
    pNtk->ForEachTfo(id, false, [&](int fo) {
      if(!fWindow || inside[fo]) {
        v[fo] = sat_solver_addvar(p);
        EncodeNode(p, v, fo, id);
      }
    });
    vLits.clear();
    for(int fi: outputs) {
      if(v[fi] == fi) continue;
      int x = sat_solver_addvar(p);
      result = sat_solver_add_xor(p, x, fi, v[fi], 0);
      assert(result);
      vLits.push_back(toLit(x));
    }
    if(vLits.empty()) {
      status = false;
      return;
    }
    status = sat_solver_addclause(p, vLits.data(), vLits.data() + vLits.size());
  }

  /**Function*************************************************************

    Synopsis    [Uses a cheap window and conflict budget before full retries.]

    Description [Only UNSAT proves a change. Unknown answers simply forgo an
    optimization. Window SAT models never escape into the PI pattern packer.]

  ***********************************************************************/
  template <typename Ntk>
  int SatSolver<Ntk>::SolveCurrent(bool fRetry) {
    nQueries++;
    auto solve = [&](int budget) {
      nCalls++;
      time_point begin;
      if(fProfile) begin = GetCurrentTime();
      int result = sat_solver_solve(pSat, vLits.data(), vLits.data() + vLits.size(), budget, 0, 0, 0);
      if(fProfile) durationSolve += Duration(begin, GetCurrentTime());
      return result;
    };
    if(fWindowActive) {
      nWindowCalls++;
      int result = solve(nConflictLimit ? std::min(nConflictLimit, 32) : 32);
      if(result == l_False) {
        nWindowProved++;
        return result;
      }
      std::vector<int> assumptions = vLits;
      time_point begin;
      if(fProfile) begin = GetCurrentTime();
      fWindowActive = false;
      EncodeMiter(pSat, vVars, target);
      if(fProfile) durationEncode += Duration(begin, GetCurrentTime());
      nMiters++;
      vLits = std::move(assumptions);
      if(!status) return l_False;
    }
    int budget = nFirstConflicts ? nFirstConflicts : nConflictLimit;
    if(nConflictLimit && budget > nConflictLimit) budget = nConflictLimit;
    int result = solve(budget);
    if(result == l_Undef && nFirstConflicts && fRetry && (!nConflictLimit || nConflictLimit > budget)) {
      nRetries++;
      result = solve(nConflictLimit ? nConflictLimit - budget : 0);
    }
    return result;
  }

  template <typename Ntk>
  void SatSolver<Ntk>::SetTarget(int id) {
    if(!fUpdate && id == target) {
      return;
    }
    fUpdate = false;
    target = id;
    time_point timeStart;
    if(fProfile) timeStart = GetCurrentTime();
    fWindowActive = nWindow > 0;
    EncodeMiter(pSat, vVars, target, fWindowActive);
    if(fProfile) durationEncode += Duration(timeStart, GetCurrentTime());
    nMiters++;
  }

  // }}}

  // {{{ Constructors

  template <typename Ntk>
  SatSolver<Ntk>::SatSolver(Parameter const *pPar) :
    pNtk(NULL),
    nVerbose(pPar->nSatSolverVerbose),
    nConflictLimit(pPar->nConflictLimit),
    fProfile(pPar->nSchedulerVerbose > 1),
    fDirectCnf(pPar->fDirectCnf),
    fGeneralize(pPar->fGeneralize),
    nWindow(pPar->nWindow),
    nFirstConflicts(pPar->nFirstConflicts),
    pSat(sat_solver_new()),
    status(false),
    target(-1),
    fUpdate(false) {
    ResetSummary();
  }

  template <typename Ntk>
  SatSolver<Ntk>::~SatSolver() {
    sat_solver_delete(pSat);
    //std::cout << "SAT solver stats: calls = " << nCalls << " (SAT = " << nSats << ", UNSAT = " << nUnsats << ", UNDET = " << nCalls - nSats - nUnsats << ")" << std::endl;
  }

  template <typename Ntk>
  void SatSolver<Ntk>::AssignNetwork(Ntk *pNtk_, bool fReuse) {
    (void)fReuse;
    status = false;
    target = -1;
    fUpdate = false;
    pNtk = pNtk_;
    pNtk->AddCallback(std::bind(&SatSolver<Ntk>::ActionCallback, this, std::placeholders::_1));
  }

  // }}}

  // {{{ Checks

  template <typename Ntk>
  SatResult SatSolver<Ntk>::CheckRedundancy(int id, int idx) {
    iLastRemoved = idx;
    iLastCandidate = -1;
    time_point timeStart = GetCurrentTime();
    SetTarget(id);
    if(!status) {
      if(nVerbose) {
        std::cout << "trivially UNSATISFIABLE" << std::endl;
      }
      durationRedundancy += Duration(timeStart, GetCurrentTime());
      return UNSAT;
    }
    vLits.clear();
    assert(pNtk->GetNodeType(id) == AND);
    pNtk->ForEachFaninIdx(id, [&](int idx2, int fi, bool c) {
      if(idx == idx2) {
        vLits.push_back(toLitCond(vVars[fi], !c));
      } else {
        vLits.push_back(toLitCond(vVars[fi], c));
      }
    });
    if(nVerbose) {
      std::cout << "solving with assumptions: ";
      std::string delim = "";
      for(int iLit: vLits) {
        std::cout << delim << (lit_sign(iLit)? "!": "") << lit_var(iLit);
        delim = ", ";
      }
      std::cout << std::endl;
    }
    bool retry = pNtk->GetNumFanins(id) <= 2 || pNtk->GetNumFanouts(pNtk->GetFanin(id, idx)) == 1;
    int res = SolveCurrent(retry);
    if(res == l_False) {
      if(nVerbose) {
        std::cout << "UNSATISFIABLE" << std::endl;
      }
      nUnsats++;
      durationRedundancy += Duration(timeStart, GetCurrentTime());
      return UNSAT;
    }
    if(res == l_Undef) {
      if(nVerbose) {
        std::cout << "UNDETERMINED" << std::endl;
      }
      durationRedundancy += Duration(timeStart, GetCurrentTime());
      return UNDET;
    }
    assert(res == l_True);
    if(nVerbose) {
      std::cout << "SATISFIABLE" << std::endl;
    }
    nSats++;
    // Only the PI model is needed by GetCex; avoid copying every internal value.
#ifndef NDEBUG
    pNtk->ForEachFaninIdx(id, [&](int idx2, int fi, bool c) {
      assert(sat_solver_var_value(pSat, vVars[fi]) ^ (idx == idx2) ^ c);
    });
#endif
    durationRedundancy += Duration(timeStart, GetCurrentTime());
    return SAT;
  }

  template <typename Ntk>
  SatResult SatSolver<Ntk>::CheckFeasibility(int id, int fi, bool c) {
    iLastRemoved = -1;
    iLastCandidate = fi;
    fLastCompl = c;
    time_point timeStart = GetCurrentTime();
    SetTarget(id);
    if(!status) {
      if(nVerbose) {
        std::cout << "trivially UNSATISFIABLE" << std::endl;
      }
      durationFeasibility += Duration(timeStart, GetCurrentTime());
      return UNSAT;
    }
    vLits.clear();
    assert(pNtk->GetNodeType(id) == AND);
    vLits.push_back(toLit(vVars[id]));
    vLits.push_back(toLitCond(vVars[fi], !c));
    if(nVerbose) {
      std::cout << "solving with assumptions: ";
      std::string delim = "";
      for(int iLit: vLits) {
        std::cout << delim << (lit_sign(iLit)? "!": "") << lit_var(iLit);
        delim = ", ";
      }
      std::cout << std::endl;
    }
    bool retry = pNtk->IsPi(fi) || pNtk->GetNumFanins(id) > 4;
    int res = SolveCurrent(retry);
    if(res == l_False) {
      if(nVerbose) {
        std::cout << "UNSATISFIABLE" << std::endl;
      }
      nUnsats++;
      durationFeasibility += Duration(timeStart, GetCurrentTime());
      return UNSAT;
    }
    if(res == l_Undef) {
      if(nVerbose) {
        std::cout << "UNDETERMINED" << std::endl;
      }
      durationFeasibility += Duration(timeStart, GetCurrentTime());
      return UNDET;
    }
    assert(res == l_True);
    if(nVerbose) {
      std::cout << "SATISFIABLE" << std::endl;
    }
    nSats++;
#ifndef NDEBUG
    assert(sat_solver_var_value(pSat, vVars[id]));
    assert(sat_solver_var_value(pSat, vVars[fi]) ^ !c);
#endif
    durationFeasibility += Duration(timeStart, GetCurrentTime());
    return SAT;
  }

  // }}}

  // {{{ Cex

  /**Function*************************************************************

    Synopsis    [Justifies a query witness and its observability with a cube.]

    Description [Simulates the current network with the target forced to both
    values. Backtracing opposite values at one output preserves observability
    for every completion of the cube. The target's query conditions are also
    justified. This does not depend on the target's old SAT definition.]

  ***********************************************************************/
  template <typename Ntk>
  std::vector<VarValue> SatSolver<Ntk>::Generalize(std::vector<VarValue> const &model) const {
    int nNodes = pNtk->GetNumNodes();
    int nPis = pNtk->GetNumPis();
    std::vector<unsigned char> values(nNodes, 0), marked(2 * nNodes, 0);
    std::vector<int> costs(2 * nNodes, 0), piIndex(nNodes, -1);
    pNtk->ForEachPiIdx([&](int idx, int id) {
      piIndex[id] = idx;
      values[id] = model[idx] == TRUE ? 3 : 0;
      costs[2 * id] = costs[2 * id + 1] = 1;
    });
    pNtk->ForEachInt([&](int id) {
      if(id == target) {
        values[id] = 2;
        return;
      }
      unsigned char value = 3;
      pNtk->ForEachFanin(id, [&](int fi, bool c) {
        value &= values[fi] ^ (c ? 3 : 0);
      });
      values[id] = value;
      for(int mode = 0; mode < 2; mode++) {
        bool one = (value >> mode) & 1;
        int cost = one ? 0 : nPis;
        pNtk->ForEachFanin(id, [&](int fi, bool c) {
          if(one) {
            cost = std::min(nPis, cost + costs[2 * fi + mode]);
          } else if(!(((values[fi] >> mode) & 1) ^ c)) {
            cost = std::min(cost, costs[2 * fi + mode]);
          }
        });
        costs[2 * id + mode] = cost;
      }
    });
    int output = -1, best = 2 * nPis + 1;
    pNtk->ForEachPoDriver([&](int fi) {
      if((values[fi] == 1 || values[fi] == 2) && costs[2 * fi] + costs[2 * fi + 1] < best) {
        output = fi;
        best = costs[2 * fi] + costs[2 * fi + 1];
      }
    });
    if(output < 0) {
      return model;
    }
    std::vector<std::pair<int, int>> pending;
    bool valid = true;
    pNtk->ForEachFaninIdx(target, [&](int idx, int fi, bool c) {
      bool wanted = idx != iLastRemoved;
      valid &= bool((values[fi] & 1) ^ c) == wanted;
      pending.emplace_back(fi, 0);
    });
    if(iLastCandidate >= 0) {
      valid &= !bool((values[iLastCandidate] & 1) ^ fLastCompl);
      pending.emplace_back(iLastCandidate, 0);
    }
    if(!valid) {
      return model;
    }
    pending.emplace_back(output, 0);
    pending.emplace_back(output, 1);
    std::vector<VarValue> cube(nPis, UNDEF);
    while(!pending.empty()) {
      int id = pending.back().first, mode = pending.back().second;
      pending.pop_back();
      if(id == 0 || id == target || marked[2 * id + mode]) {
        continue;
      }
      marked[2 * id + mode] = 1;
      if(piIndex[id] >= 0) {
        cube[piIndex[id]] = model[piIndex[id]];
        continue;
      }
      if((values[id] >> mode) & 1) {
        pNtk->ForEachFanin(id, [&](int fi) { pending.emplace_back(fi, mode); });
      } else {
        int chosen = -1, cost = nPis + 1;
        pNtk->ForEachFanin(id, [&](int fi, bool c) {
          if(!(((values[fi] >> mode) & 1) ^ c)) {
            int score = marked[2 * fi + mode] ? 0 : costs[2 * fi + mode];
            if(score < cost) {
              chosen = fi;
              cost = score;
            }
          }
        });
        assert(chosen >= 0);
        pending.emplace_back(chosen, mode);
      }
    }
    // The pattern packer expects at least one assigned PI.
    if(nPis && std::find_if(cube.begin(), cube.end(), [](VarValue v) { return v != UNDEF; }) == cube.end()) {
      cube[0] = model[0];
    }
    return cube;
  }

  /**Function*************************************************************

    Synopsis    [Keeps the complete input witness, including observability.]

    Description [Generalizing only the target's fanin requirements can drop
    assignments that make the target observable at an output. Packing that
    partial pattern need not reproduce the SAT counterexample. A complete
    model preserves both the local condition and the miter's care condition.]

  ***********************************************************************/
  template <typename Ntk>
  std::vector<VarValue> SatSolver<Ntk>::GetCex() {
    std::vector<VarValue> vCex;
    vCex.reserve(pNtk->GetNumPis());
    pNtk->ForEachPi([&](int id) {
      vCex.push_back(sat_solver_var_value(pSat, vVars[id]) ? TRUE : FALSE);
    });
    if(fGeneralize) {
      vCex = Generalize(vCex);
    }
    if(nVerbose) {
      std::cout << "cex: ";
      for(VarValue value: vCex) {
        std::cout << GetVarValueChar(value);
      }
      std::cout << std::endl;
    }
    return vCex;
  }

  // }}}

  // {{{ Stats

  template <typename Ntk>
  void SatSolver<Ntk>::ResetSummary() {
    nCalls = 0;
    nSats = 0;
    nUnsats = 0;
    durationRedundancy = 0;
    durationFeasibility = 0;
    durationEncode = 0;
    durationSolve = 0;
    nMiters = 0;
    nQueries = nWindowCalls = nWindowProved = nRetries = 0;
  }

  template <typename Ntk>
  summary<int> SatSolver<Ntk>::GetStatsSummary() const {
    summary<int> v;
    v.emplace_back("sat call", nCalls);
    if(fProfile) {
      v.emplace_back("sat miter builds", nMiters);
      v.emplace_back("sat queries", nQueries);
      v.emplace_back("sat window calls", nWindowCalls);
      v.emplace_back("sat window proved", nWindowProved);
      v.emplace_back("sat budget retries", nRetries);
    }
    v.emplace_back("sat satisfiable", nSats);
    v.emplace_back("sat unsatisfiable", nUnsats);
    return v;
  }

  template <typename Ntk>
  summary<double> SatSolver<Ntk>::GetTimesSummary() const {
    summary<double> v;
    v.emplace_back("sat redundancy", durationRedundancy);
    v.emplace_back("sat feasibility", durationFeasibility);
    if(fProfile) {
      // These components are contained in the two totals above.
      v.emplace_back("sat encoding (included)", durationEncode);
      v.emplace_back("sat solving (included)", durationSolve);
    }
    return v;
  }

  // }}}

}

ABC_NAMESPACE_CXX_HEADER_END
