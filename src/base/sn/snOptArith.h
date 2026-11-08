/**CFile****************************************************************

  FileName    [snOptArith.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Local word-level arithmetic rewrites preserving state boundaries.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: snOptArith.h,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef SN_OPT_ARITH_H
#define SN_OPT_ARITH_H
#include "snRewrite.h"
ABC_NAMESPACE_HEADER_START

typedef struct sn_opt_arith_stats_t {
    size_t modules, carry_adds, csa_trees, compressors, absorbed_carries;
} sn_opt_arith_stats_t;

// Extension belongs to the consuming addition, not to the leaf in isolation.
typedef struct sn_arith_term_t {
    sn_obj_id_t object;
    bool sign_extend, negate;
    uint32_t shift;
} sn_arith_term_t;

typedef struct sn_arith_word_t {
    sn_obj_id_t object;
    uint32_t low, high;
    unsigned arrival;
} sn_arith_word_t;

/**Function*************************************************************

  Synopsis    [Recognizes literal constants.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool sn_arith_const(const sn_module_t* m, sn_obj_id_t o)
{
    sn_obj_type_t t = sn_obj_type(m, o);
    return t == SN_CONST0 || t == SN_CONST1 || t == SN_CONST;
}

/**Function*************************************************************

  Synopsis    [Recognizes an all-zero word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool sn_arith_zero(const sn_module_t* m, sn_obj_id_t o)
{
    if (!sn_arith_const(m, o)) return false;
    for (uint32_t i = 0; i < sn_const_word_count(sn_obj_width(m, o)); ++i)
        if (sn_const_word(m, o, i)) return false;
    return true;
}

// Return a scalar (or literal 0/1) whose unsigned extension is exactly o.
// Do not look through truncation or sign extension, even if incidental values
// could make a particular instance safe.
/**Function*************************************************************

  Synopsis    [Finds a scalar carry through unsigned wiring.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_arith_carry(const sn_module_t* m, sn_obj_id_t o)
{
    for (;;) {
        sn_obj_type_t t = sn_obj_type(m, o);
        if (sn_obj_is_signed(m, o)) return SN_INVALID_ID;
        if (sn_obj_width(m, o) == 1) return o;
        if (sn_arith_const(m, o)) {
            if (sn_const_word(m, o, 0) > 1) return SN_INVALID_ID;
            for (uint32_t i = 1; i < sn_const_word_count(sn_obj_width(m, o)); ++i)
                if (sn_const_word(m, o, i)) return SN_INVALID_ID;
            return o;
        }
        if (t == SN_BUF || t == SN_POS || t == SN_CAST) {
            sn_obj_id_t f = sn_obj_fanin(m, o, 0);
            if (sn_obj_width(m, f) > sn_obj_width(m, o) || sn_obj_is_signed(m, f)) return SN_INVALID_ID;
            o = f;
        } else if (t == SN_CONCAT) {
            for (uint32_t k = 1; k < sn_obj_fanin_count(m, o); ++k)
                if (!sn_arith_zero(m, sn_obj_fanin(m, o, k))) return SN_INVALID_ID;
            o = sn_obj_fanin(m, o, 0);
        } else return SN_INVALID_ID;
    }
}

/**Function*************************************************************

  Synopsis    [Finds an unshared same-width arithmetic node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_arith_inner(const sn_module_t* m, sn_obj_id_t o,
                                         uint32_t width, const uint32_t* refs, bool unsigned_only)
{
    for (;;) {
        sn_obj_type_t t = sn_obj_type(m, o);
        if (refs[o] != 1 || sn_obj_width(m, o) != width ||
            (unsigned_only && sn_obj_is_signed(m, o))) return SN_INVALID_ID;
        if (t == SN_ADD || (!unsigned_only && width > 1 && t == SN_SUB)) return o;
        if (t != SN_BUF && t != SN_POS && t != SN_CAST) return SN_INVALID_ID;
        o = sn_obj_fanin(m, o, 0);
    }
}

// Remove only arithmetic cones made dead by this rewrite. State, ports, and
// instances are never swept. Inverse type lists are rebuilt once at the end.
/**Function*************************************************************

  Synopsis    [Retires arithmetic objects made dead by a rewrite.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_arith_release(sn_module_t* m, sn_obj_id_t o, uint32_t* refs, sn_vec_t* stack)
{
    *sn_vec_push(sn_obj_id_t, stack) = o;
    while (stack->size) {
        sn_obj_id_t node = sn_vec_at(sn_obj_id_t, stack, --stack->size);
        assert(refs[node]);
        if (--refs[node] || !sn_obj_type_is_operator(sn_obj_type(m, node))) continue;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, node); ++k)
            *sn_vec_push(sn_obj_id_t, stack) = sn_obj_fanin(m, node, k);
        sn_vec_at(sn_obj_type_t, &m->obj_types, node) = SN_CONST0;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, node) = 0;
        {
            uint32_t zero = 0;
            sn_vec_at(uint32_t, &m->obj_data, node) = sn_design_intern_const(m->design, 1, &zero);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Records extension and negation for arithmetic operands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_arith_push_terms(const sn_module_t* m, sn_obj_id_t add, bool negate,
                                       uint32_t shift, sn_vec_t* pending)
{
    sn_obj_id_t a = sn_obj_fanin(m, add, 0), b = sn_obj_fanin(m, add, 1);
    bool sign = sn_obj_is_signed(m, a) && sn_obj_is_signed(m, b);
    sn_arith_term_t left = {a, sign, negate, shift};
    sn_arith_term_t right = {b, sign, negate != (sn_obj_type(m, add) == SN_SUB), shift};
    *sn_vec_push(sn_arith_term_t, pending) = right;
    *sn_vec_push(sn_arith_term_t, pending) = left;
}

/**Function*************************************************************

  Synopsis    [Reads a small signed or unsigned literal without truncation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline bool sn_arith_literal(const sn_module_t* m, sn_obj_id_t o, bool sign, int* value)
{
    uint32_t width = sn_obj_width(m, o);
    if (!sn_arith_const(m, o)) return false;
    bool negative = sign && sn_const_bit(m, o, width - 1);
    uint32_t bits = 0;
    for (uint32_t k = 0; k < width; ++k) {
        bool bit = sn_const_bit(m, o, k);
        if (k < 16) bits |= (uint32_t)bit << k;
        else if (bit != negative) return false;
    }
    if (negative && width < 16) bits |= UINT32_C(0xffff) << width;
    *value = negative ? (int)(bits & 0xffff) - 65536 : (int)bits;
    return true;
}

// Collect single-use sums evaluated at the root width. Width-preserving casts
// may change signedness but not these bits. Width-changing wrappers and sums
// stay opaque: extending a narrow, already-overflowed sum is not distributive.
// Record each original ADD/SUB's extension policy and distribute negation
// before normalizing its operands. All arithmetic is modulo the root width.
/**Function*************************************************************

  Synopsis    [Collects a same-width arithmetic tree.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_arith_terms(const sn_module_t* m, sn_obj_id_t root, uint32_t width,
                                   const uint32_t* refs, sn_vec_t* pending, sn_vec_t* terms)
{
    pending->size = terms->size = 0;
    sn_arith_push_terms(m, root, false, 0, pending);
    while (pending->size) {
        sn_arith_term_t term = sn_vec_at(sn_arith_term_t, pending, --pending->size);
        sn_obj_id_t inner = sn_arith_inner(m, term.object, width, refs, false);
        if (inner != SN_INVALID_ID) {
            sn_arith_push_terms(m, inner, term.negate, term.shift, pending);
            continue;
        }
        sn_obj_id_t o = term.object;
        while (refs[o] == 1 && sn_obj_width(m, o) == width &&
               (sn_obj_type(m, o) == SN_BUF || sn_obj_type(m, o) == SN_POS || sn_obj_type(m, o) == SN_CAST))
            o = sn_obj_fanin(m, o, 0);
        if (refs[o] == 1 && sn_obj_width(m, o) == width) {
            sn_obj_type_t type = sn_obj_type(m, o);
            if (type == SN_NEG) {
                term.object = sn_obj_fanin(m, o, 0);
                term.sign_extend = sn_obj_is_signed(m, term.object);
                term.negate = !term.negate;
                *sn_vec_push(sn_arith_term_t, pending) = term;
                continue;
            }
            int value;
            if ((type == SN_SHL || type == SN_ASHL) &&
                sn_arith_literal(m, sn_obj_fanin(m, o, 1), false, &value) &&
                value >= 0 && (unsigned)value <= 31 - term.shift) {
                term.object = sn_obj_fanin(m, o, 0);
                term.sign_extend = sn_obj_is_signed(m, term.object);
                term.shift += (unsigned)value;
                *sn_vec_push(sn_arith_term_t, pending) = term;
                continue;
            }
            if (type == SN_MUL) {
                sn_obj_id_t a = sn_obj_fanin(m, o, 0), b = sn_obj_fanin(m, o, 1);
                bool sign = sn_obj_is_signed(m, a) && sn_obj_is_signed(m, b);
                bool literal_a = sn_arith_literal(m, a, sign, &value);
                if (literal_a || sn_arith_literal(m, b, sign, &value)) {
                    sn_obj_id_t data = literal_a ? b : a;
                    unsigned magnitude = (unsigned)(value < 0 ? -value : value), count = 0, bit = 0;
                    sn_arith_term_t digits[16];
                    while (magnitude) {
                        if (magnitude & 1) {
                            int digit = (magnitude & 3) == 3 ? -1 : 1;
                            sn_arith_term_t part = {data, sign, term.negate != ((value < 0) != (digit < 0)), term.shift + bit};
                            digits[count++] = part;
                            magnitude = digit < 0 ? magnitude + 1 : magnitude - 1;
                        }
                        magnitude >>= 1; ++bit;
                    }
                    // Keep expansion small and corrections representable in 64 bits.
                    if (count && count <= 4 && term.shift + bit <= 32 &&
                        pending->size + terms->size + count <= 256) {
                        for (unsigned k = count; k-- > 0;) *sn_vec_push(sn_arith_term_t, pending) = digits[k];
                        continue;
                    }
                }
            }
        }
        *sn_vec_push(sn_arith_term_t, terms) = term;
    }
}

// Produce an unsigned W-bit pattern for SN_FA. SN_CAST uses its DESTINATION
// signedness for extension: first sign-extend when required, then reinterpret
// at the same width. Each normalized term has exactly one use of its old leaf,
// so reference accounting never needs entries for the newly appended objects.
/**Function*************************************************************

  Synopsis    [Normalizes a leaf before compression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_arith_normalize(sn_module_t* m, sn_arith_term_t term, uint32_t width)
{
    sn_obj_id_t o = term.object;
    if (term.sign_extend && sn_obj_width(m, o) < width)
        o = sn_module_add_operator(m, SN_CAST, width, true, 1, &o, NULL);
    if (sn_obj_width(m, o) != width || sn_obj_is_signed(m, o))
        o = sn_module_add_operator(m, SN_CAST, width, false, 1, &o, NULL);
    // Complement after extension; the caller accumulates the +1 corrections.
    if (term.negate) o = sn_module_add_operator(m, SN_BIT_NOT, width, false, 1, &o, NULL);
    if (term.shift) {
        uint32_t zero = 0;
        if (term.shift >= width) return sn_module_add_const(m, width, false, &zero, NULL);
        sn_obj_id_t args[2] = {sn_module_add_const(m, term.shift, false, &zero, NULL),
                              sn_module_add_slice(m, o, (int32_t)(width - term.shift - 1), 0, NULL)};
        o = sn_module_add_concat(m, 2, args, NULL);
    }
    return o;
}

/**Function*************************************************************

  Synopsis    [Creates the combined correction for complemented operands.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_arith_correction(sn_module_t* m, uint32_t width, uint64_t value)
{
    uint32_t count = sn_const_word_count(width);
    uint32_t* words = (uint32_t*)calloc(count, sizeof(uint32_t));
    sn_obj_id_t result;
    assert(words);
    for (uint32_t k = 0; k < count; ++k, value >>= 32) words[k] = (uint32_t)value;
    result = sn_module_add_const(m, width, false, words, NULL);
    free(words);
    return result;
}

/**Function*************************************************************

  Synopsis    [Reads a literal bit through bounded wiring, or returns unknown.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int sn_arith_const_bit(const sn_module_t* m, sn_obj_id_t o, uint32_t bit, unsigned depth)
{
    sn_obj_type_t type = sn_obj_type(m, o);
    assert(bit < sn_obj_width(m, o));
    if (sn_arith_const(m, o)) return sn_const_bit(m, o, bit);
    if (!depth) return -1;
    if (type == SN_BUF || type == SN_POS || type == SN_CAST) {
        sn_obj_id_t f = sn_obj_fanin(m, o, 0);
        if (bit >= sn_obj_width(m, f)) {
            if (!sn_obj_is_signed(m, type == SN_CAST ? o : f)) return 0;
            bit = sn_obj_width(m, f) - 1;
        }
        return sn_arith_const_bit(m, f, bit, depth - 1);
    }
    if (type == SN_REPLICATE)
        return sn_arith_const_bit(m, sn_obj_fanin(m, o, 0), bit % sn_obj_width(m, sn_obj_fanin(m, o, 0)), depth - 1);
    if (type == SN_SLICE) {
        sn_slice_info_t slice = sn_obj_slice_info(m, o);
        uint32_t index = slice.left_index >= slice.right_index ? (uint32_t)slice.right_index + bit : (uint32_t)slice.right_index - bit;
        return sn_arith_const_bit(m, sn_obj_fanin(m, o, 0), index, depth - 1);
    }
    if (type == SN_CONCAT)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (bit < sn_obj_width(m, f)) return sn_arith_const_bit(m, f, bit, depth - 1);
            bit -= sn_obj_width(m, f);
        }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Combines literal terms and negation corrections modulo the width.]

  Description [Dynamic terms stay in the leaf vector. A total of zero or one
               needs no word input; the existing compressor absorbs the unit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_arith_fold_constants(sn_module_t* m, sn_vec_t* leaves,
                                                 uint32_t width, uint64_t* correction)
{
    uint32_t count = sn_const_word_count(width);
    uint32_t* sum = (uint32_t*)calloc(count, sizeof(uint32_t));
    uint32_t* words = (uint32_t*)calloc(count, sizeof(uint32_t));
    size_t kept = 0, folded = 0;
    sn_obj_id_t result = SN_INVALID_ID;
    assert(sum && words);
    sum[0] = (uint32_t)*correction;
    if (count > 1) sum[1] = (uint32_t)(*correction >> 32);
    for (size_t i = 0; i < leaves->size; ++i) {
        sn_arith_term_t term = sn_vec_at(sn_arith_term_t, leaves, i);
        uint32_t source_width = sn_obj_width(m, term.object), bit;
        memset(words, 0, count * sizeof(uint32_t));
        for (bit = term.shift; bit < width; ++bit) {
            uint32_t source_bit = bit - term.shift;
            int value = source_bit < source_width ? sn_arith_const_bit(m, term.object, source_bit, 16) :
                term.sign_extend ? sn_arith_const_bit(m, term.object, source_width - 1, 16) : 0;
            if (value < 0) break;
            if (value != (int)term.negate) words[bit >> 5] |= (uint32_t)1 << (bit & 31);
        }
        if (bit < width) {
            sn_vec_at(sn_arith_term_t, leaves, kept++) = term;
            continue;
        }
        uint64_t carry = 0;
        for (uint32_t k = 0; k < count; ++k) {
            carry += (uint64_t)sum[k] + words[k];
            sum[k] = (uint32_t)carry;
            carry >>= 32;
        }
        ++folded;
    }
    leaves->size = kept;
    if (folded) {
        if (width & 31) sum[count - 1] &= ((uint32_t)1 << (width & 31)) - 1;
        bool unit = sum[0] <= 1;
        for (uint32_t k = 1; k < count; ++k) unit &= sum[k] == 0;
        *correction = unit ? sum[0] : 0;
        if (!unit) result = sn_module_add_const(m, width, false, sum, NULL);
    }
    free(words); free(sum);
    return result;
}

/**Function*************************************************************

  Synopsis    [Bounds the nonzero columns through constant and wiring nodes.]

  Description [A bounded walk falls back to the full word when inconclusive.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_arith_bounds(const sn_module_t* m, sn_obj_id_t o, unsigned depth,
                                    uint32_t* low, uint32_t* high)
{
    uint32_t width = sn_obj_width(m, o);
    sn_obj_type_t type = sn_obj_type(m, o);
    *low = 0; *high = width;
    if (!depth) return;
    if (sn_arith_const(m, o)) {
        while (*low < width && !sn_const_bit(m, o, *low)) ++*low;
        while (*high > *low && !sn_const_bit(m, o, *high - 1)) --*high;
    } else if (type == SN_BUF || type == SN_POS || type == SN_CAST) {
        sn_obj_id_t f = sn_obj_fanin(m, o, 0);
        sn_arith_bounds(m, f, depth - 1, low, high);
        if (sn_obj_is_signed(m, type == SN_CAST ? o : f) && *high == sn_obj_width(m, f) && *low < *high)
            *high = width;
        if (*high > width) *high = width;
        if (*low > *high) *low = *high;
    } else if (type == SN_CONCAT) {
        uint32_t offset = 0;
        *low = width; *high = 0;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            uint32_t lo, hi;
            sn_arith_bounds(m, f, depth - 1, &lo, &hi);
            if (lo < hi) {
                if (offset + lo < *low) *low = offset + lo;
                if (offset + hi > *high) *high = offset + hi;
            }
            offset += sn_obj_width(m, f);
        }
        if (*low > *high) *low = *high;
    } else if (type == SN_SLICE) {
        sn_slice_info_t slice = sn_obj_slice_info(m, o);
        uint32_t lo, hi, first = (uint32_t)(slice.left_index < slice.right_index ? slice.left_index : slice.right_index);
        sn_arith_bounds(m, sn_obj_fanin(m, o, 0), depth - 1, &lo, &hi);
        if (lo < first) lo = first;
        if (hi > first + width) hi = first + width;
        if (lo >= hi) *low = *high = 0;
        else if (slice.left_index >= slice.right_index) { *low = lo - first; *high = hi - first; }
        else { *low = first + width - hi; *high = first + width - lo; }
    }
}

/**Function*************************************************************

  Synopsis    [Pads a compressor window, optionally filling its vacant LSB.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_obj_id_t sn_arith_pad(sn_module_t* m, sn_obj_id_t o, uint32_t low,
                                       uint32_t width, sn_obj_id_t bit)
{
    sn_obj_id_t args[4];
    unsigned count = 0;
    uint32_t high = low + (o == SN_INVALID_ID ? 0 : sn_obj_width(m, o));
    assert(high <= width && (bit == SN_INVALID_ID || low));
    if (bit != SN_INVALID_ID) args[count++] = bit;
    if (low > (unsigned)(bit != SN_INVALID_ID))
        args[count++] = sn_arith_correction(m, low - (unsigned)(bit != SN_INVALID_ID), 0);
    if (o != SN_INVALID_ID) args[count++] = o;
    if (high < width) args[count++] = sn_arith_correction(m, width - high, 0);
    assert(count);
    return count == 1 ? args[0] : sn_module_add_concat(m, count, args, NULL);
}

/**Function*************************************************************

  Synopsis    [Orders early, narrow terms before late arithmetic inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int sn_arith_word_compare(const void* left, const void* right)
{
    const sn_arith_word_t* a = (const sn_arith_word_t*)left;
    const sn_arith_word_t* b = (const sn_arith_word_t*)right;
    if (a->arrival != b->arrival) return a->arrival < b->arrival ? -1 : 1;
    if (a->high - a->low != b->high - b->low) return a->high - a->low < b->high - b->low ? -1 : 1;
    if (a->low != b->low) return a->low < b->low ? -1 : 1;
    return a->object < b->object ? -1 : a->object != b->object;
}

/**Function*************************************************************

  Synopsis    [Records the active columns of a normalized arithmetic term.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_arith_push_word(sn_module_t* m, sn_vec_t* terms, sn_obj_id_t o, unsigned arrival)
{
    sn_arith_word_t word = {o, 0, 0, arrival};
    sn_arith_bounds(m, o, 16, &word.low, &word.high);
    *sn_vec_push(sn_arith_word_t, terms) = word;
}

/**Function*************************************************************

  Synopsis    [Compresses disjoint triples and absorbs carry corrections.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline size_t sn_arith_compress(sn_module_t* m, sn_vec_t* terms, sn_vec_t* next,
                                      uint32_t width, sn_obj_id_t carry_in, uint64_t* correction)
{
    size_t count = 0;
    // Each round reduces all disjoint triples before using any of their outputs.
    // This avoids the serial compressor chain produced by a left-fold reduction.
    sn_obj_id_t one = SN_INVALID_ID;
    while (terms->size > 2) {
        qsort(terms->data, terms->size, sizeof(sn_arith_word_t), sn_arith_word_compare);
        next->size = 0;
        size_t i = 0;
        for (; i + 2 < terms->size; i += 3) {
            sn_arith_word_t* words = &sn_vec_at(sn_arith_word_t, terms, i);
            uint32_t low = width, high = 0;
            unsigned arrival = 0;
            for (unsigned k = 0; k < 3; ++k) {
                if (words[k].low < words[k].high) {
                    if (words[k].low < low) low = words[k].low;
                    if (words[k].high > high) high = words[k].high;
                }
                if (words[k].arrival > arrival) arrival = words[k].arrival;
            }
            if (low >= high) { low = 0; high = 1; }
            sn_obj_id_t inputs[3];
            for (unsigned k = 0; k < 3; ++k)
                inputs[k] = low == 0 && high == width ? words[k].object :
                    sn_module_add_slice(m, words[k].object, (int32_t)high - 1, (int32_t)low, NULL);
            sn_obj_id_t fa = sn_module_add_fa(m, inputs[0], inputs[1], inputs[2], NULL);
            sn_arith_word_t sum = {sn_arith_pad(m, fa+1, low, width, SN_INVALID_ID), low, high, arrival+2};
            *sn_vec_push(sn_arith_word_t, next) = sum;
            sn_obj_id_t bit = carry_in, carry = fa + 2;
            if (bit == SN_INVALID_ID && *correction) {
                if (one == SN_INVALID_ID) one = sn_arith_correction(m, 1, 1);
                bit = one;
                --*correction;
            }
            if (high == width)
                carry = high - low == 1 ? SN_INVALID_ID :
                    sn_module_add_slice(m, carry, (int32_t)(high - low) - 2, 0, NULL);
            sn_arith_word_t shifted = {sn_arith_pad(m, carry, low+1, width, bit),
                                      low+1, high < width ? high+1 : width, arrival+1};
            if (bit != SN_INVALID_ID) { shifted.low = 0; if (!shifted.high) shifted.high = 1; }
            *sn_vec_push(sn_arith_word_t, next) = shifted;
            carry_in = SN_INVALID_ID;
            ++count;
        }
        for (; i < terms->size; ++i)
            *sn_vec_push(sn_arith_word_t, next) = sn_vec_at(sn_arith_word_t, terms, i);
        sn_vec_t swap = *terms; *terms = *next; *next = swap;
    }
    assert(carry_in == SN_INVALID_ID && terms->size == 2);
    return count;
}

/**Function*************************************************************

  Synopsis    [Finishes a modular sum with one carry-propagating adder.]

  Description [The root retains its ID, width, signedness, and users.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_arith_finish(sn_module_t* m, sn_obj_id_t root,
                                   sn_obj_id_t a, sn_obj_id_t b, sn_obj_id_t carry)
{
    uint32_t width = sn_obj_width(m, root);
    if (carry == SN_INVALID_ID) {
        sn_vec_at(sn_obj_type_t, &m->obj_types, root) = SN_ADD;
        sn_obj_connect(m, root, 0, a);
        sn_obj_connect(m, root, 1, b);
    } else {
        sn_obj_id_t args[2] = {carry, a}, wide_a, wide_b, sum;
        wide_a = sn_module_add_concat(m, 2, args, NULL);
        args[1] = b;
        wide_b = sn_module_add_concat(m, 2, args, NULL);
        args[0] = wide_a; args[1] = wide_b;
        sum = sn_module_add_operator(m, SN_ADD, width + 1, false, 2, args, NULL);
        sn_vec_at(sn_obj_type_t, &m->obj_types, root) = SN_SLICE;
        sn_vec_at(sn_fanin_count_t, &m->fanin_counts, root) = 1;
        sn_vec_at(uint32_t, &m->obj_data, root) = sn_slice_pack((int32_t)width, true);
        sn_obj_connect(m, root, 0, sum);
    }
}

/**Function*************************************************************

  Synopsis    [Rewrites arithmetic in one module definition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline size_t sn_arith_module(sn_design_t* d, sn_module_id_t id,
                                      size_t* trees, size_t* compressors, size_t* absorbed)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size, changed = 0;
    uint32_t* refs = (uint32_t*)calloc(n ? n : 1, sizeof(uint32_t));
    unsigned* arrival = sn_rewrite_arrivals(m);
    sn_vec_t stack, terms, next, pending, leaves;
    sn_vec_init(&stack);
    sn_vec_init(&terms);
    sn_vec_init(&next);
    sn_vec_init(&pending);
    sn_vec_init(&leaves);
    *trees = *compressors = *absorbed = 0;
    assert(refs);
    for (sn_obj_id_t o = 0; o < n; ++o)
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID) ++refs[f];
        }
    // Visit users before their inputs so a maximal two-add pattern is seen
    // before its intermediate is considered. Do not match newly added nodes.
    for (size_t index = n; index-- > 0;) {
        sn_obj_id_t o = (sn_obj_id_t)index;
        uint32_t width = sn_obj_width(m, o);
        bool found = false;
        // One-bit arithmetic is XOR already; preserve its existing grouping.
        if (width == 1 || (sn_obj_type(m, o) != SN_ADD && sn_obj_type(m, o) != SN_SUB) ||
            !refs[o] || width >= (UINT32_MAX >> 1)) continue;
        sn_arith_terms(m, o, width, refs, &pending, &leaves);
        // Fuse a three-term sum directly, but collect larger trees first so
        // a carry-in cannot hide another carry-propagating addition.
        for (uint32_t side = 0; side < 2 && leaves.size == 3 && !found &&
             sn_obj_type(m, o) == SN_ADD && !sn_obj_is_signed(m, o); ++side) {
            sn_obj_id_t old[2] = {sn_obj_fanin(m, o, 0), sn_obj_fanin(m, o, 1)};
            sn_obj_id_t inner = sn_arith_inner(m, old[side], width, refs, true);
            sn_obj_id_t inputs[3];
            if (inner == SN_INVALID_ID) continue;
            inputs[0] = sn_obj_fanin(m, inner, 0);
            inputs[1] = sn_obj_fanin(m, inner, 1);
            inputs[2] = old[1 - side];
            for (uint32_t ci = 0; ci < 3 && !found; ++ci) {
                sn_obj_id_t carry = sn_arith_carry(m, inputs[ci]);
                sn_obj_id_t a = inputs[(ci + 1) % 3], b = inputs[(ci + 2) % 3];
                if (carry == SN_INVALID_ID || sn_obj_is_signed(m, inputs[ci]) ||
                    sn_obj_width(m, inputs[ci]) > width || sn_obj_is_signed(m, a) || sn_obj_is_signed(m, b) ||
                    sn_obj_width(m, a) != width || sn_obj_width(m, b) != width) continue;
                // Pin the reused original values before releasing the old cone.
                ++refs[a]; ++refs[b];
                // A scalar feeds both concats; a wide literal feeds one slice.
                refs[carry] += sn_obj_width(m, carry) == 1 ? 2 : 1;
                if (sn_obj_width(m, carry) != 1) carry = sn_module_add_slice(m, carry, 0, 0, NULL);
                sn_arith_finish(m, o, a, b, carry);
                sn_arith_release(m, old[0], refs, &stack);
                sn_arith_release(m, old[1], refs, &stack);
                found = true;
                ++changed;
            }
        }
        if (!found) {
            sn_obj_id_t old[2] = {sn_obj_fanin(m, o, 0), sn_obj_fanin(m, o, 1)};
            sn_obj_id_t carry_in = SN_INVALID_ID;
            uint64_t correction = 0;
            if (leaves.size < 3) continue;
            for (size_t i = 0; i < leaves.size; ++i) {
                sn_arith_term_t term = sn_vec_at(sn_arith_term_t, &leaves, i);
                if (term.negate) correction += UINT64_C(1) << term.shift;
            }
            if (width < 64) correction &= (UINT64_C(1) << width) - 1;
            sn_obj_id_t literal = sn_arith_fold_constants(m, &leaves, width, &correction);
            terms.size = 0;
            for (size_t i = 0; i < leaves.size; ++i) {
                sn_arith_term_t term = sn_vec_at(sn_arith_term_t, &leaves, i);
                if (leaves.size + (literal != SN_INVALID_ID) > 3 && !term.negate && !term.shift && carry_in == SN_INVALID_ID) {
                    sn_obj_id_t carry = sn_arith_carry(m, term.object);
                    if (carry != SN_INVALID_ID) {
                        ++refs[carry];
                        carry_in = sn_obj_width(m, carry) == 1 ? carry : sn_module_add_slice(m, carry, 0, 0, NULL);
                        ++*absorbed;
                        continue;
                    }
                }
                ++refs[term.object];
                sn_arith_push_word(m, &terms, sn_arith_normalize(m, term, width), arrival[term.object]);
            }
            if (literal != SN_INVALID_ID) sn_arith_push_word(m, &terms, literal, 0);
            // Constant folding may leave fewer than two operands. These zeros
            // are actual final-adder inputs, not unused compressor temporaries.
            while (terms.size < 2) sn_arith_push_word(m, &terms, sn_arith_correction(m, width, 0), 0);
            *compressors += sn_arith_compress(m, &terms, &next, width, carry_in, &correction);
            // Each carry word absorbs a unit correction. A final unit uses
            // the ordinary carry-in identity; larger remainders need one
            // more compressor instead of another carry-propagating adder.
            if (correction > 1) {
                sn_arith_push_word(m, &terms, sn_arith_correction(m, width, correction), 0);
                correction = 0;
                *compressors += sn_arith_compress(m, &terms, &next, width, SN_INVALID_ID, &correction);
            }
            sn_arith_finish(m, o, sn_vec_at(sn_arith_word_t, &terms, 0).object, sn_vec_at(sn_arith_word_t, &terms, 1).object,
                correction ? sn_arith_correction(m, 1, 1) : SN_INVALID_ID);
            sn_arith_release(m, old[0], refs, &stack);
            sn_arith_release(m, old[1], refs, &stack);
            ++*trees;
        }
    }
    if (changed || *trees) sn_rewrite_rebuild(d, id);
    sn_vec_destroy(&stack);
    sn_vec_destroy(&terms);
    sn_vec_destroy(&next);
    sn_vec_destroy(&pending);
    sn_vec_destroy(&leaves);
    free(refs);
    free(arrival);
    return changed;
}

/**Function*************************************************************

  Synopsis    [Rewrites arithmetic in a reachable module hierarchy.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline sn_opt_arith_stats_t sn_design_opt_arith(sn_design_t* d, sn_module_id_t root, FILE* verbose)
{
    sn_opt_arith_stats_t stats = {0, 0, 0, 0, 0};
    uint8_t* seen = (uint8_t*)calloc(d->modules.size, 1);
    sn_vec_t stack;
    assert(seen);
    sn_vec_init(&stack);
    *sn_vec_push(sn_module_id_t, &stack) = root;
    while (stack.size) {
        sn_module_id_t id = sn_vec_at(sn_module_id_t, &stack, --stack.size);
        sn_module_t* m;
        size_t changes, trees, compressors, absorbed;
        if (seen[id]) continue;
        seen[id] = 1;
        m = sn_design_get_module(d, id);
        if (sn_module_is_blackbox(m)) continue;
        for (size_t i = 0; i < m->type_objects[SN_INST].size; ++i)
            *sn_vec_push(sn_module_id_t, &stack) = sn_obj_data(m, sn_vec_at(sn_obj_id_t, &m->type_objects[SN_INST], i));
        changes = sn_arith_module(d, id, &trees, &compressors, &absorbed);
        if (changes || trees) {
            ++stats.modules;
            stats.carry_adds += changes;
            stats.csa_trees += trees;
            stats.compressors += compressors;
            stats.absorbed_carries += absorbed;
            if (verbose) fprintf(verbose, "@opt_arith: module %s: %zu carry-in additions, %zu CSA trees (%zu vector full adders), %zu absorbed carries.\n",
                sn_name_get(&d->names, sn_design_get_module(d, id)->name), changes, trees, compressors, absorbed);
        }
    }
    sn_vec_destroy(&stack);
    free(seen);
    return stats;
}

ABC_NAMESPACE_HEADER_END
#endif
