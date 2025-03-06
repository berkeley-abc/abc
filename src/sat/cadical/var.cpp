#include "internal.hpp"

namespace CaDiCaL {

void Internal::reset_subsume_bits () {
  LOG ("marking all variables as not subsume");
  for (auto idx : vars)
    flags (idx).subsume = false;
}

void Internal::check_var_stats () {
#ifndef NDEBUG
  int64_t fixed = 0, eliminated = 0, substituted = 0, pure = 0, unused = 0;
  for (auto idx : vars) {
    Flags &f = flags (idx);
    if (f.active ())
      continue;
    if (f.fixed ())
      fixed++;
    if (f.eliminated ())
      eliminated++;
    if (f.substituted ())
      substituted++;
    if (f.unused ())
      unused++;
    if (f.pure ())
      pure++;
  }
  assert (stats.now.fixed == fixed);
  assert (stats.now.eliminated == eliminated);
  assert (stats.now.substituted == substituted);
  assert (stats.now.pure == pure);
  int64_t inactive = unused + fixed + eliminated + substituted + pure;
  assert (stats.inactive == inactive);
  assert (max_var == stats.active + stats.inactive);
#endif
}

} // namespace CaDiCaL
