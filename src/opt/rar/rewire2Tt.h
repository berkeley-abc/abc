/**CFile****************************************************************

  FileName    [rewire2Tt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Tt.h,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef RAR2_TT_H
#define RAR2_TT_H

// truth table manipulation

#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START

// the bit count for the first 256 integer numbers
static int Rw2_Tt_BitCount8[256] = {
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8};

static inline int Rw2_Tt_BitCount16(int i) {
    return Rw2_Tt_BitCount8[i & 0xFF] + Rw2_Tt_BitCount8[i >> 8];
}

static word Rw2_Truths6[6] = {
    ABC_CONST(0xAAAAAAAAAAAAAAAA),
    ABC_CONST(0xCCCCCCCCCCCCCCCC),
    ABC_CONST(0xF0F0F0F0F0F0F0F0),
    ABC_CONST(0xFF00FF00FF00FF00),
    ABC_CONST(0xFFFF0000FFFF0000),
    ABC_CONST(0xFFFFFFFF00000000)};

static inline int Rw2_Tt_HexDigitNum(int n) {
    return n <= 2 ? 1 : 1 << (n - 2);
}

static inline void Rw2_Tt_Print(word *p, int nWords) {
    int k, Digit, nDigits = nWords * 16;
    for (k = nDigits - 1; k >= 0; k--) {
        Digit = (int)((p[k / 16] >> ((k % 16) * 4)) & 15);
        if (Digit < 10)
            printf("%d", Digit);
        else
            printf("%c", 'A' + Digit - 10);
    }
    printf("\n");
}

static inline int Rw2_Tt_CountOnes(word x) {
    x = x - ((x >> 1) & ABC_CONST(0x5555555555555555));
    x = (x & ABC_CONST(0x3333333333333333)) + ((x >> 2) & ABC_CONST(0x3333333333333333));
    x = (x + (x >> 4)) & ABC_CONST(0x0F0F0F0F0F0F0F0F);
    x = x + (x >> 8);
    x = x + (x >> 16);
    x = x + (x >> 32);
    return (int)(x & 0xFF);
}

static inline int Rw2_Tt_CountOnes2(word x) {
    return x ? Rw2_Tt_CountOnes(x) : 0;
}

static inline int Rw2_Tt_CountOnesVec(word *x, int nWords) {
    int w, Count = 0;
    for (w = 0; w < nWords; w++)
        Count += Rw2_Tt_CountOnes2(x[w]);
    return Count;
}

static inline int Rw2_Tt_CountOnesVecMask(word *x, word *pMask, int nWords) {
    int w, Count = 0;
    for (w = 0; w < nWords; w++)
        Count += Rw2_Tt_CountOnes2(pMask[w] & x[w]);
    return Count;
}

static inline void Rw2_Tt_Clear(word *pOut, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] = 0;
}

static inline void Rw2_Tt_Fill(word *pOut, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] = ~(word)0;
}

static inline void Rw2_Tt_Dup(word *pOut, word *pIn, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] = pIn[w];
}

static inline void Rw2_Tt_DupC(word *pOut, word *pIn, int fC, int nWords) {
    int w;
    if (fC)
        for (w = 0; w < nWords; w++)
            pOut[w] = ~pIn[w];
    else
        for (w = 0; w < nWords; w++)
            pOut[w] = pIn[w];
}

static inline void Rw2_Tt_Not(word *pOut, word *pIn, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] = ~pIn[w];
}

static inline void Rw2_Tt_And(word *pOut, word *pIn1, word *pIn2, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] = pIn1[w] & pIn2[w];
}

static inline void Rw2_Tt_Sharp(word *pOut, word *pIn, int fC, int nWords) {
    int w;
    if (fC)
        for (w = 0; w < nWords; w++)
            pOut[w] &= ~pIn[w];
    else
        for (w = 0; w < nWords; w++)
            pOut[w] &= pIn[w];
}

static inline void Rw2_Tt_OrXor(word *pOut, word *pIn1, word *pIn2, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] |= pIn1[w] ^ pIn2[w];
}

static inline void Rw2_Tt_OrXorAnd(word *pOut, word *pIn1, word *pIn2, word *pIn3, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        pOut[w] |= (pIn1[w] ^ pIn2[w]) & pIn3[w];
}

static inline int Rw2_Tt_WordNum(int n) {
    return n > 6 ? (1 << (n - 6)) : 1;
}

static inline void Rw2_Tt_ElemInit(word *pTruth, int iVar, int nWords) {
    int k;
    if (iVar < 6)
        for (k = 0; k < nWords; k++)
            pTruth[k] = Rw2_Truths6[iVar];
    else
        for (k = 0; k < nWords; k++)
            pTruth[k] = (k & (1 << (iVar - 6))) ? ~(word)0 : 0;
}

static inline int Rw2_Tt_IntersectC(word *pIn1, word *pIn2, int fC, int nWords) {
    int w;
    if (fC) {
        for (w = 0; w < nWords; w++)
            if (pIn1[w] & ~pIn2[w])
                return 1;
    } else {
        for (w = 0; w < nWords; w++)
            if (pIn1[w] & pIn2[w])
                return 1;
    }
    return 0;
}

static inline int Rw2_Tt_Equal(word *pIn1, word *pIn2, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        if (pIn1[w] != pIn2[w])
            return 0;
    return 1;
}

static inline int Rw2_Tt_EqualOnCare(word *pCare, word *pIn1, word *pIn2, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        if (pCare[w] & (pIn1[w] ^ pIn2[w]))
            return 0;
    return 1;
}

static inline int Rw2_Tt_IsConst0(word *pIn, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        if (pIn[w])
            return 0;
    return 1;
}

static inline int Rw2_Tt_IsConst1(word *pIn, int nWords) {
    int w;
    for (w = 0; w < nWords; w++)
        if (pIn[w] != ~(word)0)
            return 0;
    return 1;
}

// read/write/flip i-th bit of a bit string table:
static inline int Rw2_Tt_GetBit(word *p, int k) {
    return (int)(p[k >> 6] >> (k & 63)) & 1;
}

static inline void Rw2_Tt_SetBit(word *p, int k) {
    p[k >> 6] |= (((word)1) << (k & 63));
}

static inline void Rw2_Tt_XorBit(word *p, int k) {
    p[k >> 6] ^= (((word)1) << (k & 63));
}

ABC_NAMESPACE_HEADER_END

#endif // RAR2_TT_H
