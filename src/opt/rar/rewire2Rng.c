/**CFile****************************************************************

  FileName    [rewire2Rng.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Rng.c,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rewire2Rng.h"

ABC_NAMESPACE_IMPL_START

unsigned Rw2_Random_Int(int fReset) {
    static ABC_THREAD_LOCAL unsigned int m_z = RW2_NUMBER1;
    static ABC_THREAD_LOCAL unsigned int m_w = RW2_NUMBER2;
    if (fReset) {
        m_z = RW2_NUMBER1;
        m_w = RW2_NUMBER2;
    }
    m_z = 36969 * (m_z & 65535) + (m_z >> 16);
    m_w = 18000 * (m_w & 65535) + (m_w >> 16);
    return (m_z << 16) + m_w;
}

word Rw2_Random_Word(int fReset) {
    return ((word)Rw2_Random_Int(fReset) << 32) | ((word)Rw2_Random_Int(fReset) << 0);
}

// This procedure should be called once with Seed > 0 to initialize the generator.
// After initialization, the generator should be always called with Seed == 0.
unsigned Rw2_Random_Num(int Seed) {
    static ABC_THREAD_LOCAL unsigned RandMask = 0;
    if (Seed == 0)
        return RandMask ^ Rw2_Random_Int(0);
    RandMask = Rw2_Random_Int(1);
    for (int i = 0; i < Seed; i++)
        RandMask = Rw2_Random_Int(0);
    return RandMask;
}

ABC_NAMESPACE_IMPL_END
