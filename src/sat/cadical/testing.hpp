#ifndef _testing_hpp_INCLUDED
#define _testing_hpp_INCLUDED

// This class provides access to 'internal' which should only be used for
// internal testing and not for any other purpose as 'internal' is supposed
// to be hidden.

#include "cadical.hpp"

namespace CaDiCaL {

class Testing {
  Solver *solver;

public:
  Testing (Solver &s) : solver (&s) {}
  Testing (Solver *s) : solver (s) {}
  Internal *internal () { return solver->internal; }
  External *external () { return solver->external; }
};

} // namespace CaDiCaL

#endif
