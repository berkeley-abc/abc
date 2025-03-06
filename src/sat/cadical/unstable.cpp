#ifdef PROFILE_MODE
#include "internal.hpp"

namespace CaDiCaL {

bool Internal::propagate_unstable () {
  assert (!stable);
  START (propunstable);
  bool res = propagate ();
  STOP (propunstable);
  return res;
}

void Internal::analyze_unstable () {
  assert (!stable);
  START (analyzeunstable);
  analyze ();
  STOP (analyzeunstable);
}

int Internal::decide_unstable () {
  assert (!stable);
  return decide ();
}

}; // namespace CaDiCaL
#else
int unstable_if_no_profile_mode;
#endif
