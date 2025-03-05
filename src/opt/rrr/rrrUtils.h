#pragma once

#include <iostream>
#include <iomanip>
#include <vector>
#include <set>
#include <string>
#include <functional>
#include <limits>
#include <type_traits>
#include <cassert>

#include "rrrTypes.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr {

  /* {{{ Invocable */

#if defined(__cpp_lib_is_invocable)
  template <typename Fn, typename... Args>
  using is_invokable = std::is_invocable<Fn, Args...>;
#else
  template <typename Fn, typename... Args>
  struct is_invokable: std::is_constructible<std::function<void(Args...)>, std::reference_wrapper<typename std::remove_reference<Fn>::type>> {};
#endif

  /* }}} */

  /* {{{ Int size */
  
  template <template <typename...> typename Container, typename ... Ts>
  static inline int int_size(Container<Ts...> const &c) {
    assert(c.size() <= (typename Container<Ts...>::size_type)std::numeric_limits<int>::max());
    return c.size();
  }

  template <template <typename...> typename Container, typename ... Ts>
  static inline bool check_int_size(Container<Ts...> const &c) {
    return c.size() <= (typename Container<Ts...>::size_type)std::numeric_limits<int>::max();
  }

  static inline bool check_int_max(int i) {
    return i == std::numeric_limits<int>::max();
  }
  
  /* }}} */
  
  /* {{{ Print helpers */

  template <typename T>
  std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
    std::string delim;
    os << "[";
    for(T const &e: v) {
      os << delim << e;
      delim = ", ";
    }
    os << "]";
    return os;
  }
  
  template <typename T>
  std::ostream& operator<<(std::ostream& os, const std::set<T>& s) {
    std::string delim;
    os << "{";
    for(T const &e: s) {
      os << delim << e;
      delim = ", ";
    }
    os << "}";
    return os;
  }

  void PrintComplementedEdges(std::function<void(std::function<void(int, bool)> const &)> const &ForEachEdge) {
    std::string delim;
    std::cout << "[";
    ForEachEdge([&] (int id, bool c) {
      std::cout << delim << (c? "!": "") << id;
      delim = ", ";
    });
    std::cout << "]";
  }

  /* }}} */
  
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
    case INSERT:
      std::cout << "insert";
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
      std::cout << "\t" << "fanins: " << action.vFanins << std::endl;
    }
    if(!action.vIndices.empty()) {
      std::cout << "\t" << "indices: " << action.vIndices << std::endl;
    }
    if(!action.vFanouts.empty()) {
      std::cout << "\t" << "fanouts: " << action.vFanouts << std::endl;
    }
  }

  /* }}} */
  
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
