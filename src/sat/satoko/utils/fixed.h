//===--- sort.h -------------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#ifndef satoko__utils__fixed_h
#define satoko__utils__fixed_h

#include "misc.h"

#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

typedef unsigned fixed_t;
static const int FIXED_W_BITS = 16; /* */
static const int FIXED_F_BITS = 16;//32 - FIXED_W_BITS;
static const int FIXED_F_MASK = 0xFFFF; //(1 << FIXED_F_BITS) - 1;
static const fixed_t FIXED_MAX = 0xFFFFFFFF;
static const fixed_t FIXED_MIN = 0x00000000;
static const fixed_t FIXED_ONE = 0x10000;//(1 << FIXED_F_BITS);

/* Conversion functions */
static inline fixed_t uint2fixed(unsigned a) { return a * FIXED_ONE; }
static inline unsigned fixed2uint(fixed_t a)
{
    return (a + (FIXED_ONE >> 1)) / FIXED_ONE;
}

static inline float fixed2float(fixed_t a) { return (float)a / FIXED_ONE; }
static inline fixed_t float2fixed(float a)
{
    float temp = a * FIXED_ONE;
    temp += (temp >= 0) ? 0.5f : -0.5f;
    return (fixed_t)temp;
}

static inline double fixed2dble(fixed_t a) { return (double)a / FIXED_ONE; }
static inline fixed_t dble2fixed(double a)
{
    double temp = a * FIXED_ONE;
    temp += (temp >= 0) ? 0.5f : -0.5f;
    return (fixed_t)temp;
}

static inline fixed_t fixed_add(fixed_t a, fixed_t b) { return (a + b); }
static inline fixed_t fixed_mult(fixed_t a, fixed_t b)
{
    unsigned hi_a = (a >> FIXED_F_BITS), lo_a = (a & FIXED_F_MASK);
    unsigned hi_b = (b >> FIXED_F_BITS), lo_b = (b & FIXED_F_MASK);
    unsigned lo_ab = lo_a * lo_b;
    unsigned ab_ab = (hi_a * lo_b) + (lo_a * hi_b);
    unsigned hi_ret = (hi_a * hi_b) + (ab_ab >> FIXED_F_BITS);
    unsigned lo_ret = lo_ab + (ab_ab << FIXED_W_BITS);

    /* Carry */
    if (lo_ret < lo_ab)
        hi_ret++;

    return (hi_ret << FIXED_F_BITS) | (lo_ret >> FIXED_W_BITS);
}

ABC_NAMESPACE_HEADER_END

#endif /* satoko__utils__fixed_h */
