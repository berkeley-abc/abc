/**CFile****************************************************************

  FileName    [rewire2Rng.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Rng.h,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef RAR2_RNG_H
#define RAR2_RNG_H

// random number generation

#include "base/abc/abc.h"

// Creates a sequence of random numbers.
// http://www.codeproject.com/KB/recipes/SimpleRNG.aspx

ABC_NAMESPACE_HEADER_START

#define RW2_NUMBER1 3716960521u
#define RW2_NUMBER2 2174103536u

unsigned Rw2_Random_Int(int fReset);

word Rw2_Random_Word(int fReset);

// This procedure should be called once with Seed > 0 to initialize the generator.
// After initialization, the generator should be always called with Seed == 0.
unsigned Rw2_Random_Num(int Seed);

ABC_NAMESPACE_HEADER_END

#endif // RAR2_RNG_H
