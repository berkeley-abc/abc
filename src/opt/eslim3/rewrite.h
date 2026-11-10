/**CFile****************************************************************

  FileName    [rewrite.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Owned native restructuring under a logic-depth target.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 9, 2026.]

***********************************************************************/

#ifndef ABC__OPT__ESLIM3__REWRITE_h
#define ABC__OPT__ESLIM3__REWRITE_h
#include "aig/gia/gia.h"
#include <chrono>
ABC_NAMESPACE_CXX_HEADER_START
namespace eSLIM3 {
  Gia_Man_t* rewriteWithChoices(Gia_Man_t* original, unsigned target,
      unsigned bound, unsigned attempt, std::chrono::steady_clock::time_point deadline,
      bool area_only);
}
ABC_NAMESPACE_CXX_HEADER_END
#endif
