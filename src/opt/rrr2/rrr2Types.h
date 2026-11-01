/**HFile****************************************************************

  FileName    [rrr2Types.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Experimental redundancy removal and resubstitution.]

  Synopsis    [Redundancy analysis and optimization: Types.]

  Author      [Yukio Miyasaka]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 1, 2026.]

  Description [Derived from the rrr package. The original command is unchanged.]

***********************************************************************/

#pragma once

#include <vector>
#include <cstdint>
#include <string>
#include <utility>
#include <chrono>

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr2 {

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
    READ,
    SAVE,
    LOAD,
    POP_BACK,
    INSERT
  };

  struct Action {
    ActionType type = NONE;
    int id = -1;
    int idx = -1;
    int fi = -1;
    bool c = false;
    bool fNew = false;
    std::vector<int> vFanins;
    std::vector<int> vIndices;
    std::vector<int> vFanouts;
  };

  using seconds = int64_t;
  using clock_type = std::chrono::steady_clock;
  using time_point = std::chrono::time_point<clock_type>;

  template <typename T>
  using summary = std::vector<std::pair<std::string, T>>;

}

ABC_NAMESPACE_CXX_HEADER_END
