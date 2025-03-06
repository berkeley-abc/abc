#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Binary implication graph lists.

void Internal::init_bins () {
  assert (big.empty ());
  if (big.size () < 2 * vsize)
    big.resize (2 * vsize, Bins ());
  LOG ("initialized binary implication graph");
}

void Internal::reset_bins () {
  assert (!big.empty ());
  erase_vector (big);
  LOG ("reset binary implication graph");
}

} // namespace CaDiCaL
