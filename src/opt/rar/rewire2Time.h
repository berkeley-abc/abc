/**CFile****************************************************************

  FileName    [rewire2Time.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Time.h,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef RAR2_TIME_H
#define RAR2_TIME_H

// counting wall time

#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START

static inline iword Rw2_Time_Clock() {
#if defined(__APPLE__) && defined(__MACH__)
#define RW2_APPLE_MACH (__APPLE__ & __MACH__)
#else
#define RW2_APPLE_MACH 0
#endif
#if (defined(LIN) || defined(LIN64)) && !RW2_APPLE_MACH && !defined(__MINGW32__)
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) < 0)
        return (iword)-1;
    iword res = ((iword)ts.tv_sec) * CLOCKS_PER_SEC;
    res += (((iword)ts.tv_nsec) * CLOCKS_PER_SEC) / 1000000000;
    return res;
#else
    return (iword)clock();
#endif
}

static inline void Rw2_Time_Print(const char *pStr, iword time) {
    printf("%s = %10.2f sec", pStr, (float)1.0 * ((double)(time)) / ((double)CLOCKS_PER_SEC));
}

static inline void Rw2_Time_PrintEndl(const char *pStr, iword time) {
    Rw2_Time_Print(pStr, time);
    printf("\n");
}

ABC_NAMESPACE_HEADER_END

#endif // RAR2_TIME_H
