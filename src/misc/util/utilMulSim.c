/**CFile****************************************************************

  FileName    [utilMulSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Generating multiplier simulation info.]

  Synopsis    [Generating multiplier simulation info.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Feburary 13, 2011.]

  Revision    [$Id: utilMulSim.c,v 1.00 2011/02/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include "misc/util/abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#define SIG_WIDTH 64    // 64 simulation patterns in each signature word

// ----------------------------------------------------------------------
// Core 32-bit-limb big integer unsigned multiply
// ----------------------------------------------------------------------

uint32_t * product(const uint32_t *pArg1, int nInts1,
                   const uint32_t *pArg2, int nInts2)
{
    assert( pArg1 && pArg2 && nInts1 > 0 && nInts2 > 0 );
    int nRes = nInts1 + nInts2;
    uint32_t *pRes = (uint32_t *)calloc((size_t)nRes, sizeof(uint32_t));
    if (!pRes) return NULL;
    // Schoolbook multiplication in base 2^32
    for (int i = 0; i < nInts1; ++i) {
        uint64_t a = pArg1[i];
        if (a == 0) continue;        
        uint64_t carry = 0;
        for (int j = 0; j < nInts2; ++j) {
            uint64_t t = (uint64_t)pRes[i + j] + a * (uint64_t)pArg2[j] + carry;
            pRes[i + j] = (uint32_t)t;
            carry       = t >> 32;
        }
        pRes[i + nInts2] = (uint32_t)carry;
    }
    return pRes;
}

// ----------------------------------------------------------------------
// Bit-matrix helpers: signatures <-> per-pattern 32-bit-limb big ints
// ----------------------------------------------------------------------

static void transpose_signatures_to_pattern(const uint64_t *sigs,
                                            int nBits,
                                            uint32_t *dst,
                                            int nInts,
                                            int patternIdx)
{
    memset(dst, 0, (size_t)nInts * sizeof(uint32_t));
    for (int bit = 0; bit < nBits; ++bit) {
        uint64_t sigWord = sigs[bit];
        uint64_t bitVal  = (sigWord >> patternIdx) & 1ULL;
        if (!bitVal) continue;
        int word   = bit / 32;
        int offset = bit & 31;
        dst[word] |= (uint32_t)(1u << offset);
    }
}

static void transpose_pattern_to_signatures(const uint32_t *src,
                                            int nIntsRes,
                                            int nBitsRes,
                                            uint64_t *outSigs,
                                            int patternIdx)
{
    for (int bit = 0; bit < nBitsRes; ++bit) {
        int word   = bit / 32;
        int offset = bit & 31;
        if (word >= nIntsRes)
            break;
        uint32_t bitVal = (src[word] >> offset) & 1u;
        if (bitVal)
            outSigs[bit] |= (uint64_t)1ULL << patternIdx;
    }
}

// ----------------------------------------------------------------------
// Signed helpers for 32-bit-limb big ints (two's complement on nBits)
// ----------------------------------------------------------------------

static int is_negative(const uint32_t *x, int nBits)
{
    int bitPos = nBits - 1;
    int word   = bitPos / 32;
    int offset = bitPos & 31;
    return (x[word] >> offset) & 1u;
}

static void mask_to_nBits(uint32_t *x, int nInts, int nBits)
{
    if (nBits <= 0) {
        for (int i = 0; i < nInts; ++i)
            x[i] = 0;
        return;
    }
    int lastWord       = (nBits - 1) / 32;          // index of last used word
    int usedBitsInLast = nBits - lastWord * 32;     // 1..32
    // Zero any words above the last used word
    for (int i = lastWord + 1; i < nInts; ++i)
        x[i] = 0;
    // If nBits is not a multiple of 32, mask off the high bits of last word
    if (usedBitsInLast < 32) {
        uint32_t mask = ((uint32_t)1u << usedBitsInLast) - 1u;
        x[lastWord] &= mask;
    }
}

static void twos_complement_inplace(uint32_t *x, int nInts, int nBits)
{
    // Invert
    for (int i = 0; i < nInts; ++i)
        x[i] = ~x[i];
    mask_to_nBits(x, nInts, nBits);
    // Add 1
    uint64_t carry = 1;
    for (int i = 0; i < nInts; ++i) {
        uint64_t sum = (uint64_t)x[i] + carry;
        x[i] = (uint32_t)sum;
        carry = sum >> 32;
        if (!carry)
            break;
    }
    mask_to_nBits(x, nInts, nBits);
}

// ----------------------------------------------------------------------
// product_many: unsigned and signed (two's-complement) versions
// ----------------------------------------------------------------------

uint64_t * product_many_unsigned(uint64_t *pInfo1, int nBits1,
                                 uint64_t *pInfo2, int nBits2)
{
    assert( pInfo1 && pInfo2 && nBits1 > 0 && nBits2 > 0 );
    int nInts1   = (nBits1 + 31) / 32;
    int nInts2   = (nBits2 + 31) / 32;
    int nBitsRes = nBits1 + nBits2;
    int nIntsRes = nInts1 + nInts2;
    uint64_t *outSigs = (uint64_t *)calloc((size_t)nBitsRes, sizeof(uint64_t));
    if (!outSigs) return NULL;
    uint32_t *tmp1 = (uint32_t *)calloc((size_t)nInts1, sizeof(uint32_t));
    uint32_t *tmp2 = (uint32_t *)calloc((size_t)nInts2, sizeof(uint32_t));
    assert( tmp1 && tmp2 );
    for (int pattern = 0; pattern < SIG_WIDTH; ++pattern) {
        transpose_signatures_to_pattern(pInfo1, nBits1, tmp1, nInts1, pattern);
        transpose_signatures_to_pattern(pInfo2, nBits2, tmp2, nInts2, pattern);
        uint32_t *tmpRes = product(tmp1, nInts1, tmp2, nInts2);  assert( tmpRes );
        transpose_pattern_to_signatures(tmpRes, nIntsRes, nBitsRes, outSigs, pattern);
        free(tmpRes);
    }
    free(tmp1);
    free(tmp2);
    return outSigs;
}

uint64_t * product_many_signed(uint64_t *pInfo1, int nBits1,
                               uint64_t *pInfo2, int nBits2)
{
    assert( pInfo1 && pInfo2 && nBits1 > 0 && nBits2 > 0 );
    int nInts1   = (nBits1 + 31) / 32;
    int nInts2   = (nBits2 + 31) / 32;
    int nBitsRes = nBits1 + nBits2;
    int nIntsRes = nInts1 + nInts2;
    uint64_t *outSigs = (uint64_t *)calloc((size_t)nBitsRes, sizeof(uint64_t));
    if (!outSigs) return NULL;
    uint32_t *op1 = (uint32_t *)calloc((size_t)nInts1, sizeof(uint32_t));
    uint32_t *op2 = (uint32_t *)calloc((size_t)nInts2, sizeof(uint32_t));
    assert( op1 && op2 );    
    for (int pattern = 0; pattern < SIG_WIDTH; ++pattern) {
        transpose_signatures_to_pattern(pInfo1, nBits1, op1, nInts1, pattern);
        transpose_signatures_to_pattern(pInfo2, nBits2, op2, nInts2, pattern);
        int neg1   = is_negative(op1, nBits1);
        int neg2   = is_negative(op2, nBits2);
        int negRes = neg1 ^ neg2;
        if (neg1) twos_complement_inplace(op1, nInts1, nBits1);
        if (neg2) twos_complement_inplace(op2, nInts2, nBits2);
        uint32_t *tmpRes = product(op1, nInts1, op2, nInts2); assert( tmpRes );
        if (negRes) 
            twos_complement_inplace(tmpRes, nIntsRes, nBitsRes);
        else
            mask_to_nBits(tmpRes, nIntsRes, nBitsRes);
        transpose_pattern_to_signatures(tmpRes, nIntsRes, nBitsRes, outSigs, pattern);
        free(tmpRes);
    }
    free(op1);
    free(op2);
    return outSigs;
}

word * product_many(word *pInfo1, int nBits1, word *pInfo2, int nBits2, int fSigned )
{
    if ( fSigned )
        return (word *)product_many_signed((uint64_t *)pInfo1, nBits1, (uint64_t *)pInfo2, nBits2);
    else 
        return (word *)product_many_unsigned((uint64_t *)pInfo1, nBits1, (uint64_t *)pInfo2, nBits2);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

