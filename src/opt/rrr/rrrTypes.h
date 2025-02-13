#pragma once

#include <iostream>
#include <vector>
#include <string>
#include <chrono>
#include <cassert>

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  enum NodeType {
    PI,
    PO,
    AND,
    XOR,
    LUT
  };

  enum SatResult {
    SAT,
    UNSAT,
    UNDET
  };

  enum VarValue: char {
    UNDEF,
    TRUE,
    FALSE,
    TEMP_TRUE,
    TEMP_FALSE
  };

  /* {{{ VarValue functions */
  
  static inline VarValue DecideVarValue(VarValue x) {
    switch(x) {
    case UNDEF:
      assert(0);
    case TRUE:
      return TRUE;
    case FALSE:
      return FALSE;
    case TEMP_TRUE:
      return TRUE;
    case TEMP_FALSE:
      return FALSE;
    default:
      assert(0);
    }
  }

  static inline char GetVarValueChar(VarValue x) {
    switch(x) {
    case UNDEF:
      return 'x';
    case TRUE:
      return '1';
    case FALSE:
      return '0';
    case TEMP_TRUE:
      return 't';
    case TEMP_FALSE:
      return 'f';
    default:
      assert(0);
    }
  }

  /* }}} */

  enum ActionType {
    NONE,
    REMOVE_FANIN,
    REMOVE_UNUSED,
    REMOVE_BUFFER,
    REMOVE_CONST,
    ADD_FANIN,
    TRIVIAL_COLLAPSE,
    TRIVIAL_DECOMPOSE,
    SORT_FANINS,
    SAVE,
    LOAD,
    POP_BACK
  };

  struct Action {
    ActionType type = NONE;
    int id = -1;
    int idx = -1;
    int fi = -1;
    bool c = false;
    std::vector<int> vFanins;
    std::vector<int> vIndices;
    std::vector<int> vFanouts;
  };

  /* {{{ Action functions */

  static inline void PrintAction(Action action) {
    switch(action.type) {
    case REMOVE_FANIN:
      std::cout << "remove fanin";
      break;
    case REMOVE_UNUSED:
      std::cout << "remove unused";
      break;
    case REMOVE_BUFFER:
      std::cout << "remove buffer";
      break;
    case REMOVE_CONST:
      std::cout << "remove const";
      break;
    case ADD_FANIN:
      std::cout << "add fanin";
      break;
    case TRIVIAL_COLLAPSE:
      std::cout << "trivial collapse";
      break;
    case TRIVIAL_DECOMPOSE:
      std::cout << "trivial decompose";
      break;
    case SORT_FANINS:
      std::cout << "sort fanins";
      break;
    case SAVE:
      std::cout << "save";
      break;
    case LOAD:
      std::cout << "load";
      break;
    case POP_BACK:
      std::cout << "pop back";
      break;
    default:
      assert(0);
    }
    std::cout << ":";
    if(action.id != -1) {
      std::cout << " node " << action.id;
    }
    if(action.fi != -1) {
      std::cout << " fanin " << (action.c? "!": "") << action.fi;
    }
    if(action.idx != -1) {
      std::cout << " index " << action.idx;
    }
    std::cout << std::endl;
    if(!action.vFanins.empty()) {
      std::cout << "\t" << "fanins: ";
      std::string delim = "";
      for(int fi: action.vFanins) {
        std::cout << delim << fi;
        delim = ", ";
      }
      std::cout << std::endl;
    }
    if(!action.vIndices.empty()) {
      std::cout << "\t" << "indices: ";
      std::string delim = "";
      for(int fi: action.vIndices) {
        std::cout << delim << fi;
        delim = ", ";
      }
      std::cout << std::endl;
    }
    if(!action.vFanouts.empty()) {
      std::cout << "\t" << "fanouts: ";
      std::string delim = "";
      for(int fo: action.vFanouts) {
        std::cout << delim << fo;
        delim = ", ";
      }
      std::cout << std::endl;
    }
  }

  /* }}} */

  using seconds = int64_t;
  using clock_type = std::chrono::steady_clock;
  using time_point = std::chrono::time_point<clock_type>;
  
  /* {{{ Time functions */
  
  static inline time_point GetCurrentTime() {
    return clock_type::now();
  }

  static inline seconds DurationInSeconds(time_point start, time_point end) {
    seconds t = (std::chrono::duration_cast<std::chrono::seconds>(end - start)).count();
    assert(t >= 0);
    return t;
  }

  static inline double Duration(time_point start, time_point end) {
    double t = (std::chrono::duration<double>(end - start)).count();
    assert(t >= 0);
    return t;
  }

  /* }}} */
  
}

ABC_NAMESPACE_CXX_HEADER_END
