#ifndef _phases_hpp_INCLUDED
#define _phases_hpp_INCLUDED

#include "global.h"

#include <vector>

ABC_NAMESPACE_CXX_HEADER_START

namespace CaDiCaL {

struct Phases {

  std::vector<signed char> best;   // The current largest trail phase.
  std::vector<signed char> forced; // Forced through 'phase'.
  std::vector<signed char> prev;   // Previous during local search.
  std::vector<signed char> saved;  // The actual saved phase.
  std::vector<signed char> target; // The current target phase.
};

} // namespace CaDiCaL

ABC_NAMESPACE_CXX_HEADER_END

#endif
