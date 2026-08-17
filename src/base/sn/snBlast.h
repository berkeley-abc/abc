/**CFile****************************************************************

  FileName    [snBlast.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Bit-blasting flat or hierarchical SN designs into MiniAIG networks.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snBlast.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_BLAST_H
#define SN_BLAST_H

// Flat combinational SN-to-MiniAIG bit blaster.  MiniAIG is intentionally not
// hashed or constant propagated; Mini_AigerWrite() emits the resulting AIGER.

#include "sn.h"
#include "aig/miniaig/miniaig.h"

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

ABC_NAMESPACE_HEADER_START

typedef enum sn_blast_mul_mode_t
{
    SN_BLAST_MUL_BAUGH_WOOLEY = 0,
    SN_BLAST_MUL_BOOTH = 1
} sn_blast_mul_mode_t;

typedef enum sn_blast_mode_t
{
    // State elements are exposed as extra PI/PO pairs and are not marked as latches.
    SN_BLAST_COMB = 0,
    // State outputs are extra CIs, state inputs are the final COs, and nRegs is set.
    SN_BLAST_SEQ = 1,
    // Emit the sequential transition relation as a combinational AIG. Synchronous controls are folded into each
    // next-state function exactly as in sequential mode, but nRegs remains zero. This is intended for combinational
    // equivalence checking of state logic before and after word-level transformations.
    SN_BLAST_TRANSITION = 2
} sn_blast_mode_t;

static inline bool sn_blast_mode_has_transition(sn_blast_mode_t mode)
{
    return mode == SN_BLAST_SEQ || mode == SN_BLAST_TRANSITION;
}

typedef struct sn_blast_options_t
{
    sn_blast_mul_mode_t mul_mode;
    bool ripple_adders;
    bool delay_comparators;
    bool abstract_memories;
    bool abstract_multipliers;
    // Treat every child instance as a combinational boundary. This derives one natural module partition while
    // preserving the hierarchy and is used by module-by-module logic mapping.
    bool abstract_instances;
    bool expose_register_controls;
    sn_blast_mode_t mode;
} sn_blast_options_t;

static inline sn_blast_options_t sn_blast_default_options(void)
{
    sn_blast_options_t options = {SN_BLAST_MUL_BAUGH_WOOLEY, false, true, true, true, false, true, SN_BLAST_COMB};
    return options;
}

// Latches cannot be represented by MiniAIG's edge-triggered register convention. Command-level clients use this
// query to reject a reachable latch before constructing an AIG or modifying any saved extraction state.
static inline sn_module_id_t sn_design_find_reachable_latch(const sn_design_t* design, sn_module_id_t root,
                                                             sn_obj_id_t* returned_latch)
{
    assert(design && root < design->modules.size);
    uint8_t* seen = (uint8_t*)calloc(design->modules.size, 1);
    sn_module_id_t* pending = (sn_module_id_t*)malloc(sizeof(sn_module_id_t) * design->modules.size);
    size_t pending_count = 0;
    assert(seen && pending);
    seen[root] = 1;
    pending[pending_count++] = root;
    while (pending_count)
    {
        sn_module_id_t module_id = pending[--pending_count];
        const sn_module_t* module = sn_design_get_module_const(design, module_id);
        if (!sn_module_is_technology_primitive(module))
            for (size_t i = 0; i < module->reg_flags.size; i++)
                if (sn_vec_at(uint32_t, &module->reg_flags, i) & SN_REG_LATCH)
                {
                    if (returned_latch)
                        *returned_latch = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
                    free(pending);
                    free(seen);
                    return module_id;
                }
        for (size_t i = 0; i < module->inst_modules.size; i++)
        {
            sn_module_id_t child = sn_vec_at(sn_module_id_t, &module->inst_modules, i);
            assert(child < design->modules.size);
            if (!seen[child])
            {
                seen[child] = 1;
                pending[pending_count++] = child;
            }
        }
    }
    free(pending);
    free(seen);
    if (returned_latch)
        *returned_latch = SN_INVALID_ID;
    return SN_INVALID_ID;
}

typedef struct sn_blast_ctx_t sn_blast_ctx_t;
typedef int* (*sn_blast_special_eval_fn)(sn_blast_ctx_t* ctx, sn_obj_id_t object);

struct sn_blast_ctx_t
{
    const sn_module_t* module;
    Mini_Aig_t* aig;
    sn_blast_options_t options;
    int** bits;
    uint8_t* state;
    sn_blast_special_eval_fn special_eval;
    void* special_data;
};

static inline int* sn_blast_eval(sn_blast_ctx_t* ctx, sn_obj_id_t object);

static inline bool sn_blast_reg_init_bit(const sn_module_t* module, sn_obj_id_t reg_out, uint32_t bit)
{
    sn_obj_id_t data = sn_obj_reg_init_data(module, reg_out);
    sn_obj_id_t mask = sn_obj_reg_init_mask(module, reg_out);
    assert(bit < sn_obj_width(module, reg_out));
    if (data == SN_INVALID_ID)
        return false;
    return (mask == SN_INVALID_ID || sn_const_bit(module, mask, bit)) && sn_const_bit(module, data, bit);
}

static inline int* sn_blast_alloc_bits(uint32_t width)
{
    assert(width);
    int* bits = (int*)malloc(sizeof(int) * width);
    assert(bits);
    return bits;
}

static inline void sn_blast_copy(int* dst, const int* src, uint32_t width)
{
    for (uint32_t i = 0; i < width; i++)
        dst[i] = src[i];
}

static inline int sn_blast_bit(const sn_blast_ctx_t* ctx, sn_obj_id_t object, uint32_t bit)
{
    const sn_module_t* module = ctx->module;
    assert(object < module->obj_types.size);
    assert(bit < sn_obj_width(module, object));
    return ctx->bits[object][bit];
}

static inline int sn_blast_fill_bit(const sn_blast_ctx_t* ctx, sn_obj_id_t object, uint32_t bit, bool sign)
{
    uint32_t width = sn_obj_width(ctx->module, object);
    if (bit < width)
        return sn_blast_bit(ctx, object, bit);
    return sign ? sn_blast_bit(ctx, object, width - 1) : Mini_AigLitConst0();
}

static inline int* sn_blast_extend(sn_blast_ctx_t* ctx, sn_obj_id_t object, uint32_t width, bool sign)
{
    sn_blast_eval(ctx, object);
    int* result = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i < width; i++)
        result[i] = sn_blast_fill_bit(ctx, object, i, sign);
    return result;
}

static inline int sn_blast_or(Mini_Aig_t* aig, const int* bits, uint32_t width)
{
    assert(width);
    assert(width <= INT_MAX);
    int* temp = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i < width; i++)
        temp[i] = Mini_AigLitNot(bits[i]);
    int result = Mini_AigLitNot(Mini_AigAndMulti(aig, temp, (int)width));
    free(temp);
    return result;
}

static inline int sn_blast_and(Mini_Aig_t* aig, const int* bits, uint32_t width)
{
    assert(width);
    assert(width <= INT_MAX);
    int* temp = sn_blast_alloc_bits(width);
    sn_blast_copy(temp, bits, width);
    int result = Mini_AigAndMulti(aig, temp, (int)width);
    free(temp);
    return result;
}

static inline int sn_blast_xor(Mini_Aig_t* aig, const int* bits, uint32_t width)
{
    assert(width);
    assert(width <= INT_MAX);
    int* temp = sn_blast_alloc_bits(width);
    sn_blast_copy(temp, bits, width);
    int result = Mini_AigXorMulti(aig, temp, (int)width);
    free(temp);
    return result;
}

static inline int sn_blast_lut_rec(Mini_Aig_t* aig, const int* inputs, uint32_t count, uint64_t truth)
{
    if (count == 0)
        return (truth & 1) ? Mini_AigLitConst1() : Mini_AigLitConst0();
    uint32_t half = UINT32_C(1) << (count - 1);
    uint64_t mask = half == 32 ? UINT32_MAX : (UINT64_C(1) << half) - 1;
    int zero = sn_blast_lut_rec(aig, inputs, count - 1, truth & mask);
    int one = sn_blast_lut_rec(aig, inputs, count - 1, truth >> half);
    return Mini_AigMux(aig, inputs[count - 1], one, zero);
}

// Seven-node full adder from Wlc_BlastFullAdder(). Complement propagation handles a constant-one input without
// introducing avoidable logic. The generic construction creates exactly seven unstrashed MiniAIG AND nodes.
static inline void sn_blast_full_adder(Mini_Aig_t* aig, int a, int b, int c, int* carry, int* sum)
{
    bool complement = a == Mini_AigLitConst1() || b == Mini_AigLitConst1() || c == Mini_AigLitConst1();
    if (complement)
    {
        a = Mini_AigLitNot(a);
        b = Mini_AigLitNot(b);
        c = Mini_AigLitNot(c);
    }
    int and1 = Mini_AigAnd(aig, a, b);
    int and1n = Mini_AigAnd(aig, Mini_AigLitNot(a), Mini_AigLitNot(b));
    int x_ab = Mini_AigAnd(aig, Mini_AigLitNot(and1), Mini_AigLitNot(and1n));
    int and2 = Mini_AigAnd(aig, c, x_ab);
    int and2n = Mini_AigAnd(aig, Mini_AigLitNot(c), Mini_AigLitNot(x_ab));
    *sum = Mini_AigAnd(aig, Mini_AigLitNot(and2), Mini_AigLitNot(and2n));
    *carry = Mini_AigOr(aig, and1, and2);
    if (complement)
    {
        *sum = Mini_AigLitNot(*sum);
        *carry = Mini_AigLitNot(*carry);
    }
}

static inline void sn_blast_add_inplace_ripple(Mini_Aig_t* aig, int* dst, const int* add, uint32_t width,
                                               bool subtract)
{
    int carry = subtract ? Mini_AigLitConst1() : Mini_AigLitConst0();
    for (uint32_t i = 0; i < width; i++)
    {
        int value = subtract ? Mini_AigLitNot(add[i]) : add[i];
        sn_blast_full_adder(aig, dst[i], value, carry, &carry, &dst[i]);
    }
}

// XOR using an existing a & b node. This is the polarity used by Wlc_BlastFullAdder() and saves one AIG node
// whenever an adder generate or propagate-carry term is already available.
static inline int sn_blast_xor_with_and(Mini_Aig_t* aig, int a, int b, int and_ab)
{
    int and_neither = Mini_AigAnd(aig, Mini_AigLitNot(a), Mini_AigLitNot(b));
    return Mini_AigAnd(aig, Mini_AigLitNot(and_ab), Mini_AigLitNot(and_neither));
}

// Brent-Kung parallel-prefix addition. The prefix pairs are (propagate, generate), and the two sweeps follow the
// topology used by ABC's &genadder -b. Inputs and results remain in SN's LSB-first significance order.
static inline void sn_blast_add_inplace_brent_kung(Mini_Aig_t* aig, int* dst, const int* add, uint32_t width,
                                                   bool subtract)
{
    // A - B is A + ~B + 1: complement the second operand and use a constant-one carry-in. Folding this carry
    // into the bit-0 generate before the prefix sweeps avoids adding it separately to every group carry.
    bool carry_in = subtract;
    uint32_t prefix_width = width - 1;
    int* props = sn_blast_alloc_bits(width);
    int* group_props = prefix_width ? sn_blast_alloc_bits(prefix_width) : NULL;
    int* group_gens = prefix_width ? sn_blast_alloc_bits(prefix_width) : NULL;
    int* local_terms = prefix_width ? sn_blast_alloc_bits(prefix_width) : NULL;
    for (uint32_t i = 0; i < width; i++)
    {
        int value = carry_in ? Mini_AigLitNot(add[i]) : add[i];
        if (i < prefix_width)
        {
            int generate = Mini_AigAnd(aig, dst[i], value);
            props[i] = sn_blast_xor_with_and(aig, dst[i], value, generate);
            group_props[i] = props[i];
            group_gens[i] = i == 0 && carry_in ? Mini_AigOr(aig, dst[i], value) : generate;
            local_terms[i] = -1;
        }
        else
            props[i] = Mini_AigXor(aig, dst[i], value);
    }

    // The carry leaving the most-significant result bit is discarded, so construct prefixes only through bit
    // width - 2. Record the complete Brent-Kung schedule first. A group-propagate output is useful only when a
    // later operation updates the same target; omitting all other propagate outputs removes dead prefix logic.
    uint32_t* targets = prefix_width ? (uint32_t*)malloc(sizeof(uint32_t) * 2 * prefix_width) : NULL;
    uint32_t* lowers = prefix_width ? (uint32_t*)malloc(sizeof(uint32_t) * 2 * prefix_width) : NULL;
    uint32_t* last_target = prefix_width ? (uint32_t*)malloc(sizeof(uint32_t) * prefix_width) : NULL;
    assert(!prefix_width || (targets && lowers && last_target));
    for (uint32_t i = 0; i < prefix_width; i++)
        last_target[i] = UINT32_MAX;

    uint32_t operation_count = 0;
    uint64_t step;
    for (step = 2; step / 2 < prefix_width; step <<= 1)
        for (uint64_t i = step - 1; i < prefix_width; i += step)
        {
            assert(operation_count < 2 * prefix_width);
            targets[operation_count] = (uint32_t)i;
            lowers[operation_count++] = (uint32_t)(i - step / 2);
        }
    for (step >>= 1; step >= 2; step >>= 1)
        for (uint64_t i = 3 * step / 2 - 1; i < prefix_width; i += step)
        {
            assert(operation_count < 2 * prefix_width);
            targets[operation_count] = (uint32_t)i;
            lowers[operation_count++] = (uint32_t)(i - step / 2);
        }
    for (uint32_t i = 0; i < operation_count; i++)
        last_target[targets[i]] = i;
    for (uint32_t i = 0; i < operation_count; i++)
    {
        uint32_t target = targets[i], lower = lowers[i];
        int term = Mini_AigAnd(aig, group_props[target], group_gens[lower]);
        if (target == lower + 1 && (last_target[lower] == UINT32_MAX || last_target[lower] < i))
            local_terms[target] = term;
        group_gens[target] = Mini_AigOr(aig, group_gens[target], term);
        if (last_target[target] != i)
            group_props[target] = Mini_AigAnd(aig, group_props[target], group_props[lower]);
    }

    for (uint32_t i = 0; i < width; i++)
        if (i == 0)
            dst[i] = carry_in ? Mini_AigLitNot(props[i]) : props[i];
        else if (i < prefix_width && local_terms[i] >= 0)
            dst[i] = sn_blast_xor_with_and(aig, props[i], group_gens[i - 1], local_terms[i]);
        else
            dst[i] = Mini_AigXor(aig, props[i], group_gens[i - 1]);
    free(last_target);
    free(lowers);
    free(targets);
    free(local_terms);
    free(group_gens);
    free(group_props);
    free(props);
}

static inline void sn_blast_add_inplace(Mini_Aig_t* aig, int* dst, const int* add, uint32_t width, bool subtract,
                                        bool ripple)
{
    if (ripple)
        sn_blast_add_inplace_ripple(aig, dst, add, width, subtract);
    else
        sn_blast_add_inplace_brent_kung(aig, dst, add, width, subtract);
}

// Minimum-node comparator topology used by ABC's &gencomp. The construction computes a > b and consumes vectors in
// SN's LSB-first significance order. Signed comparison removes the sign bits, then selects b's sign when they differ.
static inline int sn_blast_gt(Mini_Aig_t* aig, const int* a, const int* b, uint32_t width, bool signed_compare)
{
    assert(width > 0);
    uint32_t compare_width = width;
    int signs_differ = Mini_AigLitConst0();
    int b_sign = Mini_AigLitConst0();
    if (signed_compare)
    {
        compare_width--;
        signs_differ = Mini_AigXor(aig, a[compare_width], b[compare_width]);
        b_sign = b[compare_width];
    }

    int result = compare_width ? Mini_AigLitConst1() : Mini_AigLitConst0();
    for (uint32_t i = 0; i < compare_width; i++)
    {
        int bit_a0 = a[i], bit_b0 = b[i];
        int bit_a1 = i + 1 < compare_width ? a[i + 1] : Mini_AigLitConst0();
        int bit_b1 = i + 1 < compare_width ? b[i + 1] : Mini_AigLitConst0();
        bool odd = (i & 1) != 0;
        int term0 = i == 0
                        ? Mini_AigOr(aig, odd ? bit_a0 : Mini_AigLitNot(bit_a0),
                                        odd ? Mini_AigLitNot(bit_b0) : bit_b0)
                        : Mini_AigAnd(aig, odd ? bit_a0 : Mini_AigLitNot(bit_a0),
                                         odd ? Mini_AigLitNot(bit_b0) : bit_b0);
        int term1 = Mini_AigAnd(aig, odd ? bit_a1 : Mini_AigLitNot(bit_a1),
                                     odd ? Mini_AigLitNot(bit_b1) : bit_b1);
        result = Mini_AigOr(aig, Mini_AigLitNot(result), Mini_AigOr(aig, term0, term1));
    }
    result = (compare_width & 1) ? Mini_AigLitNot(result) : result;
    return signed_compare ? Mini_AigMux(aig, signs_differ, b_sign, result) : result;
}

// Delay-oriented comparator. Each bit produces a greater-than generate and an equality propagate. Adjacent ranges
// are combined from least to most significant in a balanced tree: G = G_high | (E_high & G_low),
// E = E_high & E_low. Complementing both sign bits converts signed ordering into unsigned ordering.
static inline int sn_blast_gt_delay(Mini_Aig_t* aig, const int* a, const int* b, uint32_t width, bool signed_compare)
{
    assert(width > 0);
    int* generates = sn_blast_alloc_bits(width);
    int* equals = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i < width; i++)
    {
        int bit_a = signed_compare && i + 1 == width ? Mini_AigLitNot(a[i]) : a[i];
        int bit_b = signed_compare && i + 1 == width ? Mini_AigLitNot(b[i]) : b[i];
        generates[i] = Mini_AigAnd(aig, bit_a, Mini_AigLitNot(bit_b));
        equals[i] = Mini_AigLitNot(Mini_AigXor(aig, bit_a, bit_b));
    }
    for (uint32_t count = width; count > 1; count = (count + 1) / 2)
    {
        uint32_t output = 0;
        for (uint32_t i = 0; i < count; i += 2, output++)
        {
            if (i + 1 == count)
            {
                generates[output] = generates[i];
                equals[output] = equals[i];
                continue;
            }
            int low_generate = generates[i];
            int high_generate = generates[i + 1];
            int high_equal = equals[i + 1];
            generates[output] = Mini_AigOr(aig, high_generate, Mini_AigAnd(aig, high_equal, low_generate));
            equals[output] = Mini_AigAnd(aig, high_equal, equals[i]);
        }
    }
    int result = generates[0];
    free(generates);
    free(equals);
    return result;
}

static inline int sn_blast_eq_bits(Mini_Aig_t* aig, const int* a, const int* b, uint32_t width)
{
    assert(width && width <= INT_MAX);
    int* temp = sn_blast_alloc_bits(width);
    uint32_t count = 0;
    for (uint32_t i = 0; i < width; i++)
    {
        int equal;
        if (a[i] == Mini_AigLitConst0())
            equal = Mini_AigLitNot(b[i]);
        else if (a[i] == Mini_AigLitConst1())
            equal = b[i];
        else if (b[i] == Mini_AigLitConst0())
            equal = Mini_AigLitNot(a[i]);
        else if (b[i] == Mini_AigLitConst1())
            equal = a[i];
        else if (a[i] == b[i])
            equal = Mini_AigLitConst1();
        else if (a[i] == Mini_AigLitNot(b[i]))
            equal = Mini_AigLitConst0();
        else
            equal = Mini_AigLitNot(Mini_AigXor(aig, a[i], b[i]));
        if (equal == Mini_AigLitConst0())
        {
            free(temp);
            return Mini_AigLitConst0();
        }
        if (equal != Mini_AigLitConst1())
            temp[count++] = equal;
    }
    int result = count ? Mini_AigAndMulti(aig, temp, (int)count) : Mini_AigLitConst1();
    free(temp);
    return result;
}

static inline int* sn_blast_add_vectors(Mini_Aig_t* aig, const int* a, const int* b, uint32_t width, bool subtract,
                                        bool ripple)
{
    int* result = sn_blast_alloc_bits(width);
    sn_blast_copy(result, a, width);
    sn_blast_add_inplace(aig, result, b, width, subtract, ripple);
    return result;
}

static inline int* sn_blast_negate_vector(Mini_Aig_t* aig, const int* value, uint32_t width, bool ripple)
{
    if (!ripple)
    {
        int* result = sn_blast_alloc_bits(width);
        for (uint32_t i = 0; i < width; i++)
            result[i] = Mini_AigLitConst0();
        sn_blast_add_inplace_brent_kung(aig, result, value, width, true);
        return result;
    }
    int* result = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i < width; i++)
        result[i] = Mini_AigLitNot(value[i]);
    int carry = Mini_AigLitConst1();
    for (uint32_t i = 0; i < width; i++)
    {
        int old = result[i];
        result[i] = Mini_AigXor(aig, old, carry);
        carry = Mini_AigAnd(aig, old, carry);
    }
    return result;
}

static inline int* sn_blast_mux_tree(Mini_Aig_t* aig, int* select, uint32_t select_width, const int* alternatives,
                                     uint32_t output_width)
{
    assert(select_width < 31);
    int* result = sn_blast_alloc_bits(output_width);
    uint32_t count = 1u << select_width;
    for (uint32_t bit = 0; bit < output_width; bit++)
    {
        int* values = sn_blast_alloc_bits(count);
        for (uint32_t i = 0; i < count; i++)
            values[i] = alternatives[i * output_width + bit];
        result[bit] = Mini_AigMuxMulti(aig, select, (int)select_width, values, (int)count);
        free(values);
    }
    return result;
}

static inline int sn_blast_mux_simplified(Mini_Aig_t* aig, int select, int one, int zero)
{
    if (one == zero)
        return one;
    if (select == Mini_AigLitConst0())
        return zero;
    if (select == Mini_AigLitConst1())
        return one;
    if (one == Mini_AigLitConst1() && zero == Mini_AigLitConst0())
        return select;
    if (one == Mini_AigLitConst0() && zero == Mini_AigLitConst1())
        return Mini_AigLitNot(select);
    if (zero == Mini_AigLitConst0())
        return Mini_AigAnd(aig, select, one);
    if (one == Mini_AigLitConst0())
        return Mini_AigAnd(aig, Mini_AigLitNot(select), zero);
    if (one == Mini_AigLitConst1())
        return Mini_AigOr(aig, select, zero);
    if (zero == Mini_AigLitConst1())
        return Mini_AigOr(aig, Mini_AigLitNot(select), one);
    return Mini_AigMux(aig, select, one, zero);
}

// A constant table is read one output bit at a time. This bounds temporary storage by the table entry count rather
// than its full packed bit count and removes constant/equal mux branches before they enter the unhashed MiniAIG.
static inline int* sn_blast_const_mux_tree(Mini_Aig_t* aig, const sn_module_t* module, sn_obj_id_t table,
                                           int* select, uint32_t select_width, uint32_t output_width)
{
    assert(select_width < 31);
    uint32_t count = 1u << select_width;
    int* values = sn_blast_alloc_bits(count);
    int* result = sn_blast_alloc_bits(output_width);
    for (uint32_t bit = 0; bit < output_width; bit++)
    {
        for (uint32_t i = 0; i < count; i++)
            values[i] = sn_const_bit(module, table, i * output_width + bit) ? Mini_AigLitConst1()
                                                                           : Mini_AigLitConst0();
        uint32_t value_count = count;
        for (uint32_t stage = 0; stage < select_width; stage++)
        {
            for (uint32_t i = 0; i < value_count / 2; i++)
                values[i] = sn_blast_mux_simplified(aig, select[stage], values[2 * i + 1], values[2 * i]);
            value_count /= 2;
        }
        assert(value_count == 1);
        result[bit] = values[0];
    }
    free(values);
    return result;
}

typedef struct sn_blast_column_t
{
    int* values;
    uint32_t* levels;
    uint32_t size;
    uint32_t cap;
} sn_blast_column_t;

static inline void sn_blast_column_push(sn_blast_column_t* column, int literal, uint32_t level)
{
    if (column->size == column->cap)
    {
        column->cap = column->cap ? 2 * column->cap : 8;
        column->values = (int*)realloc(column->values, sizeof(int) * column->cap);
        column->levels = (uint32_t*)realloc(column->levels, sizeof(uint32_t) * column->cap);
        assert(column->values);
        assert(column->levels);
    }
    uint32_t i = column->size++;
    while (i && column->levels[i - 1] < level)
    {
        column->values[i] = column->values[i - 1];
        column->levels[i] = column->levels[i - 1];
        i--;
    }
    column->values[i] = literal;
    column->levels[i] = level;
}

static inline sn_blast_column_t* sn_blast_columns_alloc(uint32_t count, uint32_t cap)
{
    sn_blast_column_t* columns = (sn_blast_column_t*)calloc(count, sizeof(*columns));
    assert(columns);
    for (uint32_t i = 0; i < count; i++)
    {
        columns[i].cap = cap;
        columns[i].values = (int*)malloc(sizeof(int) * cap);
        columns[i].levels = (uint32_t*)malloc(sizeof(uint32_t) * cap);
        assert(columns[i].values);
        assert(columns[i].levels);
    }
    return columns;
}

static inline void sn_blast_columns_free(sn_blast_column_t* columns, uint32_t count)
{
    for (uint32_t i = 0; i < count; i++)
    {
        free(columns[i].values);
        free(columns[i].levels);
    }
    free(columns);
}

// Reduces a partial-product matrix by always combining the three least-deep signals in each column. This is the
// Mini_Aig counterpart of Wlc_BlastReduceMatrix(): sum and carry depths are tracked explicitly and inserted back in
// level order, preventing carries from creating a serial diagonal chain through the matrix.
static inline int* sn_blast_reduce_columns(Mini_Aig_t* aig, sn_blast_column_t* columns, uint32_t width, bool ripple)
{
    int* row0 = sn_blast_alloc_bits(width);
    int* row1 = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i < width; i++)
    {
        sn_blast_column_t* column = &columns[i];
        while (column->size > 2)
        {
            uint32_t level0 = column->levels[--column->size];
            int value0 = column->values[column->size];
            uint32_t level1 = column->levels[--column->size];
            int value1 = column->values[column->size];
            uint32_t level2 = column->levels[--column->size];
            int value2 = column->values[column->size];
            uint32_t level = level0 > level1 ? level0 : level1;
            level = level > level2 ? level : level2;
            int carry, sum;
            sn_blast_full_adder(aig, value0, value1, value2, &carry, &sum);
            sn_blast_column_push(column, sum, level + 2);
            sn_blast_column_push(&columns[i + 1], carry, level + 1);
        }
        row0[i] = column->size ? column->values[0] : Mini_AigLitConst0();
        row1[i] = column->size == 2 ? column->values[1] : Mini_AigLitConst0();
    }
    sn_blast_add_inplace(aig, row0, row1, width, false, ripple);
    free(row1);
    return row0;
}

static inline int* sn_blast_mul_operand(const int* value, bool is_signed, uint32_t width, uint32_t work)
{
    int* result = sn_blast_alloc_bits(work);
    for (uint32_t i = 0; i < work; i++)
        result[i] = i < width ? value[i] : (is_signed ? value[width - 1] : Mini_AigLitConst0());
    return result;
}

static inline int* sn_blast_mul_baugh_wooley(Mini_Aig_t* aig, const int* a, bool a_signed, uint32_t a_width,
                                             const int* b, bool b_signed, uint32_t b_width, uint32_t result_width,
                                             bool ripple)
{
    // Unsigned and mixed multiplication use the partial-product matrix directly. Baugh-Wooley operates on two signed
    // operands at their original widths, without sign-extending either input.
    bool signed_matrix = a_signed && b_signed;
    uint32_t a_work = a_width;
    uint32_t b_work = b_width;
    uint32_t product_width = a_work + b_work;
    uint32_t column_count = product_width + 1;
    uint32_t cap = (a_work < b_work ? a_work : b_work) + 8;
    int* aa = sn_blast_mul_operand(a, a_signed, a_width, a_work);
    int* bb = sn_blast_mul_operand(b, b_signed, b_width, b_work);
    sn_blast_column_t* columns = sn_blast_columns_alloc(column_count, cap);
    for (uint32_t i = 0; i < a_work; i++)
        for (uint32_t j = 0; j < b_work; j++)
        {
            bool complement = signed_matrix && ((i + 1 == a_work) != (j + 1 == b_work));
            int product = Mini_AigAnd(aig, aa[i], bb[j]);
            sn_blast_column_push(&columns[i + j], complement ? Mini_AigLitNot(product) : product, 0);
        }
    if (signed_matrix)
    {
        sn_blast_column_push(&columns[a_work - 1], Mini_AigLitConst1(), 0);
        sn_blast_column_push(&columns[b_work - 1], Mini_AigLitConst1(), 0);
        sn_blast_column_push(&columns[product_width - 1], Mini_AigLitConst1(), 0);
    }
    int* product = sn_blast_reduce_columns(aig, columns, product_width, ripple);
    int* result = sn_blast_alloc_bits(result_width);
    for (uint32_t i = 0; i < result_width; i++)
        result[i] = i < product_width ? product[i]
                                      : (signed_matrix ? product[product_width - 1] : Mini_AigLitConst0());
    free(product);
    free(aa);
    free(bb);
    sn_blast_columns_free(columns, column_count);
    return result;
}

static inline int* sn_blast_mul_booth(Mini_Aig_t* aig, const int* a, bool a_signed, uint32_t a_width,
                                      const int* b, bool b_signed, uint32_t b_width, uint32_t result_width,
                                      bool ripple)
{
    bool signed_multiply = a_signed && b_signed;
    uint32_t common_width = a_width > b_width ? a_width : b_width;
    uint32_t a_constants = 0, b_constants = 0;
    for (uint32_t i = 0; i < common_width; i++)
    {
        int a_bit = i < a_width ? a[i] : (signed_multiply ? a[a_width - 1] : Mini_AigLitConst0());
        int b_bit = i < b_width ? b[i] : (signed_multiply ? b[b_width - 1] : Mini_AigLitConst0());
        a_constants += Mini_AigLitIsConst(a_bit);
        b_constants += Mini_AigLitIsConst(b_bit);
    }
    if (a_constants < b_constants)
    {
        const int* temp_value = a;
        uint32_t temp_width = a_width;
        a = b;
        a_width = b_width;
        b = temp_value;
        b_width = temp_width;
    }

    uint32_t product_width = a_width + b_width;
    uint32_t matrix_width = product_width + 3;
    uint32_t column_count = matrix_width + 1;
    uint32_t cap = a_width + 8;
    sn_blast_column_t* columns = sn_blast_columns_alloc(column_count, cap);
    int fill_a = signed_multiply ? a[a_width - 1] : Mini_AigLitConst0();
    int fill_b = signed_multiply ? b[b_width - 1] : Mini_AigLitConst0();
    int* extended_b = sn_blast_alloc_bits(b_width + 4);
    uint32_t extended_size = 0;
    extended_b[extended_size++] = Mini_AigLitConst0();
    for (uint32_t i = 0; i < b_width; i++)
        extended_b[extended_size++] = b[i];
    if (!signed_multiply)
    {
        extended_b[extended_size++] = fill_b;
        extended_b[extended_size++] = fill_b;
    }
    if ((extended_size & 1) == 0)
        extended_b[extended_size++] = fill_b;
    assert(extended_size & 1);
    for (uint32_t k = 0; k + 2 < extended_size; k += 2)
    {
        int q_minus = extended_b[k];
        int q = extended_b[k + 1];
        int q_plus = extended_b[k + 2];
        int negative = q_plus;
        int one = Mini_AigXor(aig, q, q_minus);
        int two = Mini_AigMux(aig, negative,
                              Mini_AigAnd(aig, Mini_AigLitNot(q), Mini_AigLitNot(q_minus)),
                              Mini_AigAnd(aig, q, q_minus));
        int partial = Mini_AigLitConst0();
        uint32_t i;
        for (i = 0; i <= a_width; i++)
        {
            int current = i == a_width ? fill_a : a[i];
            int previous = i ? a[i - 1] : Mini_AigLitConst0();
            int part = Mini_AigOr(aig, Mini_AigAnd(aig, one, current), Mini_AigAnd(aig, two, previous));
            partial = Mini_AigXor(aig, part, negative);
            if (partial != Mini_AigLitConst0() && !(signed_multiply && i == a_width))
                sn_blast_column_push(&columns[k + i], partial, 0);
        }
        if (signed_multiply)
            i--;
        int sign = signed_multiply ? partial : negative;
        if (k == 0)
        {
            sn_blast_column_push(&columns[k + i], sign, 0);
            sn_blast_column_push(&columns[k + i + 1], sign, 0);
            if (sign != Mini_AigLitConst1())
                sn_blast_column_push(&columns[k + i + 2], Mini_AigLitNot(sign), 0);
        }
        else
        {
            if (sign != Mini_AigLitConst1())
                sn_blast_column_push(&columns[k + i], Mini_AigLitNot(sign), 0);
            sn_blast_column_push(&columns[k + i + 1], Mini_AigLitConst1(), 0);
        }
        if (negative != Mini_AigLitConst0())
            sn_blast_column_push(&columns[k], negative, 0);
    }
    int* product = sn_blast_reduce_columns(aig, columns, matrix_width, ripple);
    int* result = sn_blast_alloc_bits(result_width);
    for (uint32_t i = 0; i < result_width; i++)
        result[i] = i < product_width ? product[i]
                                      : (signed_multiply ? product[product_width - 1] : Mini_AigLitConst0());
    free(extended_b);
    free(product);
    sn_blast_columns_free(columns, column_count);
    return result;
}

static inline int* sn_blast_div_vectors(Mini_Aig_t* aig, const int* dividend, const int* divisor, uint32_t width,
                                        bool signed_operands, bool remainder_result, bool ripple,
                                        bool delay_comparators)
{
    int* a = sn_blast_alloc_bits(width);
    int* b = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i < width; i++)
    {
        a[i] = dividend[i];
        b[i] = divisor[i];
    }
    int sign_a = signed_operands ? a[width - 1] : 0;
    int sign_b = signed_operands ? b[width - 1] : 0;
    if (signed_operands)
    {
        int* neg_a = sn_blast_negate_vector(aig, a, width, ripple);
        int* neg_b = sn_blast_negate_vector(aig, b, width, ripple);
        for (uint32_t i = 0; i < width; i++)
        {
            a[i] = Mini_AigMux(aig, sign_a, neg_a[i], a[i]);
            b[i] = Mini_AigMux(aig, sign_b, neg_b[i], b[i]);
        }
        free(neg_a);
        free(neg_b);
    }
    int* rem = sn_blast_alloc_bits(width + 1);
    int* div = sn_blast_alloc_bits(width + 1);
    int* quotient = sn_blast_alloc_bits(width);
    for (uint32_t i = 0; i <= width; i++)
    {
        rem[i] = 0;
        div[i] = i < width ? b[i] : 0;
    }
    for (uint32_t i = 0; i < width; i++)
        quotient[i] = 0;
    int divisor_zero = Mini_AigLitNot(sn_blast_or(aig, b, width));
    for (uint32_t i = width; i-- > 0;)
    {
        int* shifted = sn_blast_alloc_bits(width + 1);
        shifted[0] = a[i];
        for (uint32_t k = 1; k <= width; k++)
            shifted[k] = rem[k - 1];
        int less = delay_comparators ? sn_blast_gt_delay(aig, div, shifted, width + 1, false)
                                     : sn_blast_gt(aig, div, shifted, width + 1, false);
        int ge = Mini_AigLitNot(less);
        int* difference = sn_blast_alloc_bits(width + 1);
        sn_blast_copy(difference, shifted, width + 1);
        sn_blast_add_inplace(aig, difference, div, width + 1, true, ripple);
        for (uint32_t k = 0; k <= width; k++)
            rem[k] = Mini_AigMux(aig, ge, difference[k], shifted[k]);
        quotient[i] = Mini_AigMux(aig, divisor_zero, Mini_AigLitConst1(), ge);
        free(shifted);
        free(difference);
    }
    int* result = sn_blast_alloc_bits(width);
    if (remainder_result)
        for (uint32_t i = 0; i < width; i++)
            result[i] = Mini_AigMux(aig, divisor_zero, dividend[i], rem[i]);
    else
        for (uint32_t i = 0; i < width; i++)
            result[i] = quotient[i];
    if (signed_operands)
    {
        int result_sign = remainder_result ? sign_a : Mini_AigXor(aig, sign_a, sign_b);
        result_sign = Mini_AigMux(aig, divisor_zero, Mini_AigLitConst0(), result_sign);
        int* neg_result = sn_blast_negate_vector(aig, result, width, ripple);
        for (uint32_t i = 0; i < width; i++)
            result[i] = Mini_AigMux(aig, result_sign, neg_result[i], result[i]);
        free(neg_result);
    }
    free(a);
    free(b);
    free(rem);
    free(div);
    free(quotient);
    return result;
}

static inline int* sn_blast_power(Mini_Aig_t* aig, const int* base, uint32_t base_width, bool base_signed,
                                  const int* exponent, uint32_t exponent_width, bool exponent_signed,
                                  uint32_t result_width, sn_blast_mul_mode_t mode, bool ripple)
{
    int* result = sn_blast_alloc_bits(result_width);
    int* power = sn_blast_alloc_bits(result_width);
    for (uint32_t i = 0; i < result_width; i++)
    {
        result[i] = i == 0 ? Mini_AigLitConst1() : Mini_AigLitConst0();
        power[i] = i < base_width ? base[i]
                                  : (base_signed ? base[base_width - 1] : Mini_AigLitConst0());
    }
    for (uint32_t i = 0; i < exponent_width; i++)
    {
        int* selected = mode == SN_BLAST_MUL_BOOTH
                            ? sn_blast_mul_booth(aig, result, base_signed, result_width, power, base_signed,
                                                 result_width,
                                                 result_width, ripple)
                            : sn_blast_mul_baugh_wooley(aig, result, base_signed, result_width, power, base_signed,
                                                        result_width,
                                                        result_width, ripple);
        for (uint32_t bit = 0; bit < result_width; bit++)
            result[bit] = Mini_AigMux(aig, exponent[i], selected[bit], result[bit]);
        free(selected);
        if (i + 1 < exponent_width)
        {
            int* squared = mode == SN_BLAST_MUL_BOOTH
                               ? sn_blast_mul_booth(aig, power, base_signed, result_width, power, base_signed,
                                                    result_width, result_width, ripple)
                               : sn_blast_mul_baugh_wooley(aig, power, base_signed, result_width, power, base_signed,
                                                           result_width, result_width, ripple);
            free(power);
            power = squared;
        }
    }
    if (exponent_signed)
    {
        int is_zero = Mini_AigLitConst1();
        int is_one = Mini_AigLitConst1();
        int is_minus_one = Mini_AigLitConst1();
        for (uint32_t i = 0; i < base_width; i++)
        {
            is_zero = Mini_AigAnd(aig, is_zero, Mini_AigLitNot(base[i]));
            is_one = Mini_AigAnd(aig, is_one, i == 0 ? base[i] : Mini_AigLitNot(base[i]));
            if (base_signed)
                is_minus_one = Mini_AigAnd(aig, is_minus_one, base[i]);
        }
        int unit = Mini_AigOr(aig, is_zero, is_one);
        if (base_signed)
            unit = Mini_AigOr(aig, unit, is_minus_one);
        int force_zero = Mini_AigAnd(aig, exponent[exponent_width - 1], Mini_AigLitNot(unit));
        for (uint32_t i = 0; i < result_width; i++)
            result[i] = Mini_AigAnd(aig, result[i], Mini_AigLitNot(force_zero));
    }
    free(power);
    return result;
}

static inline int* sn_blast_shift(sn_blast_ctx_t* ctx, sn_obj_id_t object, bool left, bool arithmetic)
{
    const sn_module_t* m = ctx->module;
    sn_obj_id_t value_id = sn_obj_fanin(m, object, 0);
    sn_obj_id_t amount_id = sn_obj_fanin(m, object, 1);
    uint32_t width = sn_obj_width(m, object);
    uint32_t value_width = sn_obj_width(m, value_id);
    uint32_t amount_width = sn_obj_width(m, amount_id);
    uint32_t work_width = width > value_width ? width : value_width;
    int* current = sn_blast_extend(ctx, value_id, work_width, sn_obj_is_signed(m, value_id));
    const int* amount = sn_blast_eval(ctx, amount_id);
    int fill = arithmetic && !left && sn_obj_is_signed(m, value_id) ? current[work_width - 1]
                                                                    : Mini_AigLitConst0();
    uint32_t useful_stages = 0;
    // SN widths are capped below 2^31, so this unsigned shift never reaches 32.
    while ((UINT32_C(1) << useful_stages) < work_width)
        useful_stages++;
    uint32_t stage_count = amount_width < useful_stages ? amount_width : useful_stages;
    for (uint32_t stage = 0; stage < stage_count; stage++)
    {
        uint64_t distance = UINT64_C(1) << stage;
        int* next = sn_blast_alloc_bits(work_width);
        for (uint32_t bit = 0; bit < work_width; bit++)
        {
            int shifted = fill;
            if (left)
                shifted = bit >= distance ? current[bit - distance] : Mini_AigLitConst0();
            else
                shifted = bit + distance < work_width ? current[bit + distance] : fill;
            next[bit] = Mini_AigMux(ctx->aig, amount[stage], shifted, current[bit]);
        }
        free(current);
        current = next;
    }
    if (amount_width > useful_stages)
    {
        int overshift = sn_blast_or(ctx->aig, amount + useful_stages, amount_width - useful_stages);
        for (uint32_t bit = 0; bit < work_width; bit++)
            current[bit] = Mini_AigMux(ctx->aig, overshift, fill, current[bit]);
    }
    int* result = sn_blast_alloc_bits(width);
    for (uint32_t bit = 0; bit < width; bit++)
        result[bit] = current[bit];
    free(current);
    return result;
}

static inline int* sn_blast_eval(sn_blast_ctx_t* ctx, sn_obj_id_t object)
{
    const sn_module_t* m = ctx->module;
    assert(object < m->obj_types.size);
    if (ctx->bits[object])
        return ctx->bits[object];
    assert(ctx->state[object] == 0);
    ctx->state[object] = 1;
    sn_obj_type_t type = sn_obj_type(m, object);
    uint32_t width = sn_obj_width(m, object);
    int* result = NULL;
    if ((type == SN_PI || type == SN_INST || type == SN_FAN) && ctx->special_eval)
        result = ctx->special_eval(ctx, object);
    else if (type == SN_PO || type == SN_LOOP_OUT || type == SN_LOOP_IN)
    {
        sn_obj_id_t fanin = sn_obj_fanin(m, object, 0);
        assert(fanin != SN_INVALID_ID);
        int* source = sn_blast_eval(ctx, fanin);
        result = sn_blast_alloc_bits(width);
        sn_blast_copy(result, source, width);
    }
    else if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
    {
        result = sn_blast_alloc_bits(width);
        for (uint32_t i = 0; i < width; i++)
            result[i] = sn_const_bit(m, object, i) ? Mini_AigLitConst1() : Mini_AigLitConst0();
    }
    else if (type == SN_BUF || type == SN_POS || type == SN_CAST)
    {
        sn_obj_id_t fanin = sn_obj_fanin(m, object, 0);
        result = sn_blast_extend(ctx, fanin, width, type == SN_CAST ? sn_obj_is_signed(m, object)
                                                                     : sn_obj_is_signed(m, fanin));
    }
    else if (type == SN_CONCAT)
    {
        result = sn_blast_alloc_bits(width);
        uint32_t offset = 0;
        for (uint32_t i = 0; i < sn_obj_fanin_count(m, object); i++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(m, object, i);
            int* source = sn_blast_eval(ctx, fanin);
            uint32_t source_width = sn_obj_width(m, fanin);
            sn_blast_copy(result + offset, source, source_width);
            offset += source_width;
        }
        assert(offset == width);
    }
    else if (type == SN_REPLICATE)
    {
        sn_obj_id_t fanin = sn_obj_fanin(m, object, 0);
        int* source = sn_blast_eval(ctx, fanin);
        uint32_t source_width = sn_obj_width(m, fanin);
        uint32_t count = sn_obj_repeat_count(m, object);
        result = sn_blast_alloc_bits(width);
        for (uint32_t i = 0; i < count; i++)
            sn_blast_copy(result + i * source_width, source, source_width);
    }
    else if (type == SN_SLICE)
    {
        sn_obj_id_t fanin = sn_obj_fanin(m, object, 0);
        int* source = sn_blast_eval(ctx, fanin);
        const sn_slice_info_t* info = sn_obj_slice_info(m, object);
        result = sn_blast_alloc_bits(width);
        for (uint32_t i = 0; i < width; i++)
        {
            int64_t index = info->left_index >= info->right_index ? (int64_t)info->right_index + i
                                                                   : (int64_t)info->right_index - i;
            assert(index >= 0 && (uint64_t)index < sn_obj_width(m, fanin));
            result[i] = source[index];
        }
    }
    else if (type == SN_BIT_NOT || type == SN_NEG || type == SN_LOG_NOT ||
             type == SN_REDUCE_AND || type == SN_REDUCE_NAND || type == SN_REDUCE_OR ||
             type == SN_REDUCE_NOR || type == SN_REDUCE_XOR || type == SN_REDUCE_XNOR)
    {
        sn_obj_id_t fanin = sn_obj_fanin(m, object, 0);
        int* source = sn_blast_eval(ctx, fanin);
        if (type == SN_BIT_NOT)
        {
            int* extended = sn_blast_extend(ctx, fanin, width, sn_obj_is_signed(m, fanin));
            result = sn_blast_alloc_bits(width);
            for (uint32_t i = 0; i < width; i++)
                result[i] = Mini_AigLitNot(extended[i]);
            free(extended);
        }
        else if (type == SN_NEG)
        {
            int* extended = sn_blast_extend(ctx, fanin, width, sn_obj_is_signed(m, fanin));
            result = sn_blast_negate_vector(ctx->aig, extended, width, ctx->options.ripple_adders);
            free(extended);
        }
        else
        {
            int reduced = type == SN_LOG_NOT
                              ? Mini_AigLitNot(sn_blast_or(ctx->aig, source, sn_obj_width(m, fanin)))
                              : type == SN_REDUCE_AND || type == SN_REDUCE_NAND
                                    ? sn_blast_and(ctx->aig, source, sn_obj_width(m, fanin))
                                    : type == SN_REDUCE_OR || type == SN_REDUCE_NOR
                                          ? sn_blast_or(ctx->aig, source, sn_obj_width(m, fanin))
                                          : sn_blast_xor(ctx->aig, source, sn_obj_width(m, fanin));
            if (type == SN_REDUCE_NAND || type == SN_REDUCE_NOR || type == SN_REDUCE_XNOR)
                reduced = Mini_AigLitNot(reduced);
            result = sn_blast_alloc_bits(width);
            result[0] = reduced;
            for (uint32_t i = 1; i < width; i++)
                result[i] = 0;
        }
    }
    else if (type == SN_BIT_AND || type == SN_BIT_OR || type == SN_BIT_XOR || type == SN_BIT_XNOR ||
             type == SN_LOG_AND || type == SN_LOG_OR)
    {
        sn_obj_id_t a_id = sn_obj_fanin(m, object, 0), b_id = sn_obj_fanin(m, object, 1);
        bool logical = type == SN_LOG_AND || type == SN_LOG_OR;
        uint32_t a_width = logical ? sn_obj_width(m, a_id) : width;
        uint32_t b_width = logical ? sn_obj_width(m, b_id) : width;
        int* a = sn_blast_extend(ctx, a_id, a_width, sn_obj_is_signed(m, a_id) && sn_obj_is_signed(m, b_id));
        int* b = sn_blast_extend(ctx, b_id, b_width, sn_obj_is_signed(m, a_id) && sn_obj_is_signed(m, b_id));
        result = sn_blast_alloc_bits(width);
        if (logical)
        {
            int av = sn_blast_or(ctx->aig, a, a_width);
            int bv = sn_blast_or(ctx->aig, b, b_width);
            result[0] = type == SN_LOG_AND ? Mini_AigAnd(ctx->aig, av, bv) : Mini_AigOr(ctx->aig, av, bv);
            for (uint32_t i = 1; i < width; i++)
                result[i] = 0;
        }
        else
            for (uint32_t i = 0; i < width; i++)
                result[i] = type == SN_BIT_AND ? Mini_AigAnd(ctx->aig, a[i], b[i])
                             : type == SN_BIT_OR ? Mini_AigOr(ctx->aig, a[i], b[i])
                             : type == SN_BIT_XOR ? Mini_AigXor(ctx->aig, a[i], b[i])
                             : Mini_AigLitNot(Mini_AigXor(ctx->aig, a[i], b[i]));
        free(a);
        free(b);
    }
    else if (type == SN_EQ || type == SN_NE || type == SN_CASE_EQ || type == SN_CASE_NE ||
             type == SN_WILDCARD_EQ || type == SN_WILDCARD_NE || type == SN_LT || type == SN_LE ||
             type == SN_GT || type == SN_GE)
    {
        sn_obj_id_t a_id = sn_obj_fanin(m, object, 0), b_id = sn_obj_fanin(m, object, 1);
        uint32_t compare_width = sn_obj_width(m, a_id) > sn_obj_width(m, b_id) ? sn_obj_width(m, a_id)
                                                                                 : sn_obj_width(m, b_id);
        bool signed_compare = sn_obj_is_signed(m, a_id) && sn_obj_is_signed(m, b_id);
        int* a = sn_blast_extend(ctx, a_id, compare_width, signed_compare);
        int* b = sn_blast_extend(ctx, b_id, compare_width, signed_compare);
        int value;
        if (type == SN_EQ || type == SN_CASE_EQ || type == SN_WILDCARD_EQ || type == SN_NE ||
            type == SN_CASE_NE || type == SN_WILDCARD_NE)
            value = sn_blast_eq_bits(ctx->aig, a, b, compare_width);
        else
        {
            int (*blast_gt)(Mini_Aig_t*, const int*, const int*, uint32_t, bool) =
                ctx->options.delay_comparators ? sn_blast_gt_delay : sn_blast_gt;
            if (type == SN_GT)
                value = blast_gt(ctx->aig, a, b, compare_width, signed_compare);
            else if (type == SN_LT)
                value = blast_gt(ctx->aig, b, a, compare_width, signed_compare);
            else if (type == SN_GE)
                value = Mini_AigLitNot(blast_gt(ctx->aig, b, a, compare_width, signed_compare));
            else
                value = Mini_AigLitNot(blast_gt(ctx->aig, a, b, compare_width, signed_compare));
        }
        if (type == SN_NE || type == SN_CASE_NE || type == SN_WILDCARD_NE)
            value = Mini_AigLitNot(value);
        result = sn_blast_alloc_bits(width);
        result[0] = value;
        for (uint32_t i = 1; i < width; i++)
            result[i] = 0;
        free(a);
        free(b);
    }
    else if (type == SN_ADD || type == SN_SUB)
    {
        sn_obj_id_t a_id = sn_obj_fanin(m, object, 0), b_id = sn_obj_fanin(m, object, 1);
        bool signed_operands = sn_obj_is_signed(m, a_id) && sn_obj_is_signed(m, b_id);
        int* a = sn_blast_extend(ctx, a_id, width, signed_operands);
        int* b = sn_blast_extend(ctx, b_id, width, signed_operands);
        result = sn_blast_add_vectors(ctx->aig, a, b, width, type == SN_SUB, ctx->options.ripple_adders);
        free(a);
        free(b);
    }
    else if (type == SN_MUL)
    {
        sn_obj_id_t a_id = sn_obj_fanin(m, object, 0), b_id = sn_obj_fanin(m, object, 1);
        int* a = sn_blast_eval(ctx, a_id), *b = sn_blast_eval(ctx, b_id);
        bool signed_operands = sn_obj_is_signed(m, a_id) && sn_obj_is_signed(m, b_id);
        uint32_t a_width = sn_obj_width(m, a_id), b_width = sn_obj_width(m, b_id);
        result = ctx->options.mul_mode == SN_BLAST_MUL_BOOTH
                     ? sn_blast_mul_booth(ctx->aig, a, signed_operands, a_width, b, signed_operands, b_width, width,
                                          ctx->options.ripple_adders)
                     : sn_blast_mul_baugh_wooley(ctx->aig, a, signed_operands, a_width, b, signed_operands, b_width,
                                                 width, ctx->options.ripple_adders);
    }
    else if (type == SN_LUT)
    {
        uint32_t count = sn_obj_fanin_count(m, object);
        int inputs[6];
        assert(count <= sizeof(inputs) / sizeof(inputs[0]));
        for (uint32_t i = 0; i < count; i++)
            inputs[i] = sn_blast_eval(ctx, sn_obj_fanin(m, object, i))[0];
        result = sn_blast_alloc_bits(1);
        result[0] = sn_blast_lut_rec(ctx->aig, inputs, count, sn_obj_lut_truth(m, object));
    }
    else if (type == SN_DIV || type == SN_MOD)
    {
        sn_obj_id_t a_id = sn_obj_fanin(m, object, 0), b_id = sn_obj_fanin(m, object, 1);
        uint32_t work_width = sn_obj_width(m, a_id) > sn_obj_width(m, b_id) ? sn_obj_width(m, a_id)
                                                                             : sn_obj_width(m, b_id);
        if (work_width < width)
            work_width = width;
        bool signed_operands = sn_obj_is_signed(m, a_id) && sn_obj_is_signed(m, b_id);
        int* a = sn_blast_extend(ctx, a_id, work_width, signed_operands);
        int* b = sn_blast_extend(ctx, b_id, work_width, signed_operands);
        int* quotient_or_remainder = sn_blast_div_vectors(ctx->aig, a, b, work_width, signed_operands,
                                                          type == SN_MOD, ctx->options.ripple_adders,
                                                          ctx->options.delay_comparators);
        result = sn_blast_alloc_bits(width);
        for (uint32_t i = 0; i < width; i++)
            result[i] = quotient_or_remainder[i];
        free(a);
        free(b);
        free(quotient_or_remainder);
    }
    else if (type == SN_POW)
    {
        sn_obj_id_t base_id = sn_obj_fanin(m, object, 0), exponent_id = sn_obj_fanin(m, object, 1);
        int* base = sn_blast_eval(ctx, base_id);
        int* exponent = sn_blast_eval(ctx, exponent_id);
        result = sn_blast_power(ctx->aig, base, sn_obj_width(m, base_id), sn_obj_is_signed(m, base_id), exponent,
                                sn_obj_width(m, exponent_id), sn_obj_is_signed(m, exponent_id), width,
                                ctx->options.mul_mode, ctx->options.ripple_adders);
    }
    else if (type == SN_SHL || type == SN_SHR || type == SN_ASHL || type == SN_ASHR)
        result = sn_blast_shift(ctx, object, type == SN_SHL || type == SN_ASHL, type == SN_ASHR);
    else if (type == SN_MUX)
    {
        int* select = sn_blast_eval(ctx, sn_obj_fanin(m, object, SN_MUX_SELECT));
        int* one = sn_blast_eval(ctx, sn_obj_fanin(m, object, SN_MUX_SELECTED));
        int* zero = sn_blast_eval(ctx, sn_obj_fanin(m, object, SN_MUX_DEFAULT));
        result = sn_blast_alloc_bits(width);
        for (uint32_t i = 0; i < width; i++)
            result[i] = Mini_AigMux(ctx->aig, select[0], one[i], zero[i]);
    }
    else if (type == SN_BMUX)
    {
        int* select = sn_blast_eval(ctx, sn_obj_fanin(m, object, 0));
        sn_obj_id_t alternatives_id = sn_obj_fanin(m, object, 1);
        sn_obj_type_t alternatives_type = sn_obj_type(m, alternatives_id);
        uint32_t select_width = sn_obj_width(m, sn_obj_fanin(m, object, 0));
        if (alternatives_type == SN_CONST0 || alternatives_type == SN_CONST1 || alternatives_type == SN_CONST)
            result = sn_blast_const_mux_tree(ctx->aig, m, alternatives_id, select, select_width, width);
        else
        {
            int* alternatives = sn_blast_eval(ctx, alternatives_id);
            result = sn_blast_mux_tree(ctx->aig, select, select_width, alternatives, width);
        }
    }
    else if (type == SN_PMUX)
    {
        int* select = sn_blast_eval(ctx, sn_obj_fanin(m, object, 0));
        int* alternatives = sn_blast_eval(ctx, sn_obj_fanin(m, object, 1));
        int* default_value = sn_blast_eval(ctx, sn_obj_fanin(m, object, 2));
        uint32_t select_width = sn_obj_width(m, sn_obj_fanin(m, object, 0));
        int any_select = sn_blast_or(ctx->aig, select, select_width);
        result = sn_blast_alloc_bits(width);
        int* terms = sn_blast_alloc_bits(select_width + 1);
        for (uint32_t bit = 0; bit < width; bit++)
        {
            for (uint32_t i = 0; i < select_width; i++)
                terms[i] = Mini_AigAnd(ctx->aig, select[i], alternatives[i * width + bit]);
            terms[select_width] = Mini_AigAnd(ctx->aig, Mini_AigLitNot(any_select), default_value[bit]);
            result[bit] = sn_blast_or(ctx->aig, terms, select_width + 1);
        }
        free(terms);
    }
    else
        assert(false);
    assert(result);
    ctx->bits[object] = result;
    ctx->state[object] = 2;
    return result;
}

static inline void sn_blast_check_module(const sn_module_t* module, sn_blast_options_t options)
{
    assert(module);
    for (sn_obj_id_t object = 0; object < module->obj_types.size; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        assert(type != SN_INST && type != SN_FAN);
        if (type == SN_LUT)
            assert(sn_obj_fanin_count(module, object) <= 6);
        if (type == SN_REG_OUT)
            assert(!(sn_vec_at(uint32_t, &module->reg_flags, sn_obj_type_id(module, object)) & SN_REG_LATCH));
        if (!options.abstract_memories)
            assert(type != SN_MEM_OUT && type != SN_MEM_IN && type != SN_MEM_READ && type != SN_MEM_WRITE);
    }
    assert(sn_module_is_topo(module));
}

static inline Mini_Aig_t* sn_module_blast_comb_options(const sn_module_t* module,
                                                       sn_blast_options_t options);

static inline Mini_Aig_t* sn_module_blast_comb(const sn_module_t* module)
{
    return sn_module_blast_comb_options(module, sn_blast_default_options());
}

static inline Mini_Aig_t* sn_module_blast_seq_options(const sn_module_t* module, sn_blast_options_t options)
{
    options.mode = SN_BLAST_SEQ;
    return sn_module_blast_comb_options(module, options);
}

static inline Mini_Aig_t* sn_module_blast_seq(const sn_module_t* module)
{
    return sn_module_blast_seq_options(module, sn_blast_default_options());
}

typedef struct sn_blast_hier_stats_t
{
    uint64_t primary_input_bits;
    uint64_t primary_output_bits;
    uint64_t flop_bits;
    uint64_t register_control_bits;
    uint64_t memory_count;
    uint64_t multiplier_count;
    uint64_t abstraction_input_bits;
    uint64_t abstraction_output_bits;
} sn_blast_hier_stats_t;

typedef enum sn_blast_boundary_kind_t
{
    SN_BLAST_BOUNDARY_TOP_PI,
    SN_BLAST_BOUNDARY_MEMORY_OUTPUT,
    SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT,
    SN_BLAST_BOUNDARY_REG_OUTPUT,
    SN_BLAST_BOUNDARY_LOOP_OUTPUT,
    SN_BLAST_BOUNDARY_TOP_PO,
    SN_BLAST_BOUNDARY_REG_CONTROL,
    SN_BLAST_BOUNDARY_MEMORY_INPUT,
    SN_BLAST_BOUNDARY_PRIMITIVE_INPUT,
    SN_BLAST_BOUNDARY_REG_INPUT,
    SN_BLAST_BOUNDARY_LOOP_INPUT
} sn_blast_boundary_kind_t;

typedef struct sn_blast_hier_ref_t
{
    uint32_t occurrence;
    sn_obj_id_t object;
    uint32_t bit;
} sn_blast_hier_ref_t;

typedef struct sn_blast_boundary_bit_t
{
    sn_blast_boundary_kind_t kind;
    sn_blast_hier_ref_t signal;
    uint32_t owner;
    uint32_t port;
} sn_blast_boundary_bit_t;

typedef struct sn_blast_occurrence_t
{
    sn_module_id_t module;
    uint32_t parent_occurrence;
    sn_obj_id_t parent_inst;
} sn_blast_occurrence_t;

typedef struct sn_blast_primitive_t
{
    uint32_t occurrence;
    sn_obj_id_t inst;
    sn_module_id_t module;
    uint32_t ci_begin;
    uint32_t ci_count;
    uint32_t co_begin;
    uint32_t co_count;
} sn_blast_primitive_t;

typedef struct sn_blast_register_t
{
    uint32_t occurrence;
    sn_obj_id_t reg_out;
    uint32_t ci_begin;
    uint32_t co_begin;
    uint32_t control_co_begin[SN_REG_FANIN_COUNT];
    uint32_t width;
} sn_blast_register_t;

typedef struct sn_blast_loop_t
{
    uint32_t occurrence;
    sn_obj_id_t loop_out;
    uint32_t co_begin;
    uint32_t width;
} sn_blast_loop_t;

typedef struct sn_blast_boundary_t
{
    uint32_t register_bits;
    sn_vec_t occurrences; // sn_blast_occurrence_t
    sn_vec_t primitives;  // sn_blast_primitive_t
    sn_vec_t registers;   // sn_blast_register_t
    sn_vec_t loops;       // sn_blast_loop_t
    sn_vec_t cis;         // sn_blast_boundary_bit_t in MiniAIG PI order
    sn_vec_t cos;         // sn_blast_boundary_bit_t in MiniAIG PO order
} sn_blast_boundary_t;

static inline void sn_blast_boundary_init(sn_blast_boundary_t* boundary)
{
    assert(boundary);
    boundary->register_bits = 0;
    sn_vec_init(&boundary->occurrences);
    sn_vec_init(&boundary->primitives);
    sn_vec_init(&boundary->registers);
    sn_vec_init(&boundary->loops);
    sn_vec_init(&boundary->cis);
    sn_vec_init(&boundary->cos);
}

static inline void sn_blast_boundary_destroy(sn_blast_boundary_t* boundary)
{
    assert(boundary);
    boundary->register_bits = 0;
    sn_vec_destroy(&boundary->occurrences);
    sn_vec_destroy(&boundary->primitives);
    sn_vec_destroy(&boundary->registers);
    sn_vec_destroy(&boundary->loops);
    sn_vec_destroy(&boundary->cis);
    sn_vec_destroy(&boundary->cos);
}

typedef struct sn_blast_hier_t sn_blast_hier_t;

typedef struct sn_blast_hier_frame_t
{
    sn_blast_hier_t* hierarchy;
    sn_blast_ctx_t blast;
    struct sn_blast_hier_frame_t** children;
    uint32_t occurrence;
    struct sn_blast_hier_frame_t* parent;
    sn_obj_id_t parent_inst;
} sn_blast_hier_frame_t;

typedef struct sn_blast_hier_object_t
{
    sn_blast_hier_frame_t* frame;
    sn_obj_id_t object;
    uint32_t boundary_owner;
} sn_blast_hier_object_t;

struct sn_blast_hier_t
{
    const sn_design_t* design;
    Mini_Aig_t* aig;
    sn_blast_options_t options;
    sn_blast_hier_stats_t stats;
    sn_blast_boundary_t* boundary;
    uint8_t* active_modules;
    sn_vec_t memory_reads;
    sn_vec_t memory_writes;
    sn_vec_t registers;
    sn_vec_t loops;
    sn_vec_t abstract_insts;
};

static inline bool sn_blast_reg_control_is_comb_output(const sn_module_t* module, sn_obj_id_t reg_out,
                                                        uint32_t slot)
{
    uint32_t flags = sn_obj_reg_flags(module, reg_out);
    if (slot == SN_REG_ENABLE)
        return true;
    if (slot == SN_REG_SET)
        return !(flags & SN_REG_SET_ASYNC);
    if (slot == SN_REG_RESET)
        return !(flags & SN_REG_RESET_ASYNC);
    if (slot == SN_REG_RESET_VALUE)
        return sn_obj_fanin(module, reg_out, SN_REG_RESET) != SN_INVALID_ID && !(flags & SN_REG_RESET_ASYNC);
    return false;
}

static inline bool sn_blast_hier_is_abstract_inst(const sn_blast_hier_t* hierarchy,
                                                       const sn_module_t* module, sn_obj_id_t inst)
{
    const sn_module_t* child = sn_design_get_module_const(hierarchy->design,
                                                           sn_inst_module_id(module, inst));
    if (sn_module_is_blackbox(child))
        return true;
    const char* name = sn_name_get(&hierarchy->design->names, child->name);
    bool memory = strncmp(name, "__sn_RAM", 8) == 0 || strncmp(name, "__sn_URAM", 9) == 0;
    bool multiplier = strncmp(name, "__sn_DSP", 8) == 0;
    bool carry = strncmp(name, "__sn_CARRY", 10) == 0;
    return hierarchy->options.abstract_instances || (memory && hierarchy->options.abstract_memories) ||
           (multiplier && hierarchy->options.abstract_multipliers) || carry;
}

static inline sn_blast_hier_object_t* sn_blast_hier_add_object(sn_vec_t* objects, sn_blast_hier_frame_t* frame,
                                                               sn_obj_id_t object)
{
    sn_blast_hier_object_t* entry = sn_vec_push(sn_blast_hier_object_t, objects);
    entry->frame = frame;
    entry->object = object;
    entry->boundary_owner = SN_INVALID_ID;
    return entry;
}

static inline uint64_t sn_blast_hier_memory_input_bits(const sn_module_t* module, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    uint32_t first = type == SN_MEM_READ ? (uint32_t)SN_MEM_READ_CLOCK : (uint32_t)SN_MEM_WRITE_CLOCK;
    uint32_t count = type == SN_MEM_READ ? (uint32_t)SN_MEM_READ_FANIN_COUNT
                                         : (uint32_t)SN_MEM_WRITE_FANIN_COUNT;
    uint64_t bits = 0;
    for (uint32_t slot = first; slot < count; slot++)
    {
        sn_obj_id_t fanin = sn_obj_fanin(module, object, slot);
        if (fanin != SN_INVALID_ID)
            bits += sn_obj_width(module, fanin);
    }
    return bits;
}

static inline sn_blast_hier_frame_t* sn_blast_hier_build_frame(sn_blast_hier_t* hierarchy, sn_module_id_t module_id,
                                                                uint32_t parent_occurrence,
                                                                sn_obj_id_t parent_inst,
                                                                sn_blast_hier_frame_t* parent_frame)
{
    assert(module_id < hierarchy->design->modules.size);
    assert(!hierarchy->active_modules[module_id]);
    hierarchy->active_modules[module_id] = 1;
    const sn_module_t* module = sn_design_get_module_const(hierarchy->design, module_id);
    assert(sn_module_is_topo(module));
    for (size_t i = 0; i < module->reg_flags.size; i++)
        assert(!(sn_vec_at(uint32_t, &module->reg_flags, i) & SN_REG_LATCH));
    for (size_t i = 0; i < module->type_objects[SN_LUT].size; i++)
        assert(sn_obj_fanin_count(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_LUT], i)) <= 6);

    sn_blast_hier_frame_t* frame = (sn_blast_hier_frame_t*)calloc(1, sizeof(sn_blast_hier_frame_t));
    assert(frame);
    size_t object_count = module->obj_types.size;
    frame->hierarchy = hierarchy;
    frame->parent = parent_frame;
    frame->parent_inst = parent_inst;
    frame->occurrence = SN_INVALID_ID;
    if (hierarchy->boundary)
    {
        assert(hierarchy->boundary->occurrences.size < UINT32_MAX);
        frame->occurrence = (uint32_t)hierarchy->boundary->occurrences.size;
        sn_blast_occurrence_t* occurrence = sn_vec_push(sn_blast_occurrence_t, &hierarchy->boundary->occurrences);
        occurrence->module = module_id;
        occurrence->parent_occurrence = parent_occurrence;
        occurrence->parent_inst = parent_inst;
    }
    frame->blast.module = module;
    frame->blast.aig = NULL;
    frame->blast.options = hierarchy->options;
    frame->blast.bits = (int**)calloc(object_count, sizeof(int*));
    frame->blast.state = (uint8_t*)calloc(object_count, sizeof(uint8_t));
    frame->children = (sn_blast_hier_frame_t**)calloc(object_count, sizeof(sn_blast_hier_frame_t*));
    assert(frame->blast.bits && frame->blast.state && frame->children);

    // Boundary order must not depend on physical/topological object order, because a word-level transform can
    // legitimately rebuild that order. Type IDs are the stable natural order preserved by SN duplication. Collect
    // each class in type-ID order and recurse through child occurrences in natural instance order. Register bits then
    // have the canonical key (depth-first instance path, register type ID, LSB-first bit index).
    hierarchy->stats.memory_count += module->type_objects[SN_MEM_OUT].size;
    if (hierarchy->options.abstract_memories)
    {
        for (size_t i = 0; i < module->type_objects[SN_MEM_READ].size; i++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_READ], i);
            sn_blast_hier_add_object(&hierarchy->memory_reads, frame, object);
            hierarchy->stats.abstraction_output_bits += sn_obj_width(module, object);
            hierarchy->stats.abstraction_input_bits += sn_blast_hier_memory_input_bits(module, object);
        }
    }
    if (hierarchy->options.abstract_memories)
    {
        for (size_t i = 0; i < module->type_objects[SN_MEM_WRITE].size; i++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_WRITE], i);
            sn_blast_hier_add_object(&hierarchy->memory_writes, frame, object);
            hierarchy->stats.abstraction_input_bits += sn_blast_hier_memory_input_bits(module, object);
        }
    }
    for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        sn_blast_hier_object_t* entry = sn_blast_hier_add_object(&hierarchy->registers, frame, object);
        if (hierarchy->boundary)
        {
            assert(hierarchy->boundary->registers.size < UINT32_MAX);
            entry->boundary_owner = (uint32_t)hierarchy->boundary->registers.size;
            sn_blast_register_t* reg = sn_vec_push(sn_blast_register_t, &hierarchy->boundary->registers);
            reg->occurrence = frame->occurrence;
            reg->reg_out = object;
            reg->ci_begin = SN_INVALID_ID;
            reg->co_begin = SN_INVALID_ID;
            for (uint32_t slot = 0; slot < SN_REG_FANIN_COUNT; slot++)
                reg->control_co_begin[slot] = SN_INVALID_ID;
            reg->width = sn_obj_width(module, object);
        }
        hierarchy->stats.flop_bits += sn_obj_width(module, object);
        if (hierarchy->options.expose_register_controls)
        {
            const uint32_t slots[] = {SN_REG_ENABLE, SN_REG_SET, SN_REG_RESET, SN_REG_RESET_VALUE};
            for (size_t j = 0; j < sizeof(slots) / sizeof(slots[0]); j++)
            {
                if (hierarchy->options.mode != SN_BLAST_COMB ||
                    !sn_blast_reg_control_is_comb_output(module, object, slots[j]))
                    continue;
                sn_obj_id_t fanin = sn_obj_fanin(module, object, slots[j]);
                if (fanin != SN_INVALID_ID)
                    hierarchy->stats.register_control_bits += sn_obj_width(module, fanin);
            }
        }
    }
    for (size_t i = 0; i < module->type_objects[SN_LOOP_OUT].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_LOOP_OUT], i);
        sn_blast_hier_object_t* entry = sn_blast_hier_add_object(&hierarchy->loops, frame, object);
        if (hierarchy->boundary)
        {
            assert(hierarchy->boundary->loops.size < UINT32_MAX);
            entry->boundary_owner = (uint32_t)hierarchy->boundary->loops.size;
            sn_blast_loop_t* loop = sn_vec_push(sn_blast_loop_t, &hierarchy->boundary->loops);
            loop->occurrence = frame->occurrence;
            loop->loop_out = object;
            loop->co_begin = SN_INVALID_ID;
            loop->width = sn_obj_width(module, object);
        }
        hierarchy->stats.abstraction_output_bits += sn_obj_width(module, object);
        hierarchy->stats.abstraction_input_bits += sn_obj_width(module, object);
    }
    for (size_t i = 0; i < module->type_objects[SN_INST].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i);
        const sn_module_t* child = sn_design_get_module_const(hierarchy->design,
                                                               sn_inst_module_id(module, object));
        if (sn_blast_hier_is_abstract_inst(hierarchy, module, object))
        {
            sn_blast_hier_object_t* entry = sn_blast_hier_add_object(&hierarchy->abstract_insts, frame, object);
            if (hierarchy->boundary)
            {
                assert(hierarchy->boundary->primitives.size < UINT32_MAX);
                entry->boundary_owner = (uint32_t)hierarchy->boundary->primitives.size;
                sn_blast_primitive_t* primitive =
                    sn_vec_push(sn_blast_primitive_t, &hierarchy->boundary->primitives);
                primitive->occurrence = frame->occurrence;
                primitive->inst = object;
                primitive->module = child->id;
                primitive->ci_begin = SN_INVALID_ID;
                primitive->ci_count = 0;
                primitive->co_begin = SN_INVALID_ID;
                primitive->co_count = 0;
            }
            const char* name = sn_name_get(&hierarchy->design->names, child->name);
            if (strncmp(name, "__sn_DSP", 8) == 0)
                hierarchy->stats.multiplier_count++;
            else if (strncmp(name, "__sn_RAM", 8) == 0 || strncmp(name, "__sn_URAM", 9) == 0)
                hierarchy->stats.memory_count++;
            for (size_t j = 0; j < child->type_objects[SN_PO].size; j++)
            {
                sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], j);
                hierarchy->stats.abstraction_output_bits += sn_obj_width(child, output);
            }
            for (uint32_t j = 0; j < sn_obj_fanin_count(module, object); j++)
                hierarchy->stats.abstraction_input_bits += sn_obj_width(module, sn_obj_fanin(module, object, j));
        }
        else
            frame->children[object] =
                sn_blast_hier_build_frame(hierarchy, child->id, frame->occurrence, object, frame);
    }
    hierarchy->active_modules[module_id] = 0;
    return frame;
}

static inline int* sn_blast_hier_eval_inst(sn_blast_ctx_t* context, sn_obj_id_t object)
{
    // sn_blast_eval() caches this result on the parent SN_INST or SN_FAN object, while the child PO evaluation below
    // is cached in the child occurrence frame. Thus each used output cone is built once per instance occurrence;
    // subsequent fanouts neither re-enter the child nor rebuild its logic. Unused outputs remain unexpanded.
    sn_blast_hier_frame_t* frame = (sn_blast_hier_frame_t*)context->special_data;
    const sn_module_t* module = context->module;
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_PI)
    {
        assert(frame->parent && frame->parent_inst != SN_INVALID_ID);
        uint32_t port = sn_obj_type_id(module, object);
        sn_obj_id_t parent_fanin = sn_obj_fanin(frame->parent->blast.module, frame->parent_inst, port);
        assert(sn_obj_width(module, object) == sn_obj_width(frame->parent->blast.module, parent_fanin));
        int* source = sn_blast_eval(&frame->parent->blast, parent_fanin);
        int* result = sn_blast_alloc_bits(sn_obj_width(module, object));
        sn_blast_copy(result, source, sn_obj_width(module, object));
        return result;
    }
    sn_obj_id_t inst = type == SN_INST ? object : sn_fan_inst_id(module, object);
    uint32_t output_index = type == SN_INST ? 0 : sn_fan_output_index(module, object);
    sn_blast_hier_frame_t* child = frame->children[inst];
    assert(child); // Abstract insts have their output bits pre-seeded as CIs.
    const sn_module_t* child_module = child->blast.module;
    assert(output_index < child_module->type_objects[SN_PO].size);
    sn_obj_id_t child_po = sn_vec_at(sn_obj_id_t, &child_module->type_objects[SN_PO], output_index);
    int* source = sn_blast_eval(&child->blast, child_po);
    uint32_t width = sn_obj_width(module, object);
    assert(width == sn_obj_width(child_module, child_po));
    int* result = sn_blast_alloc_bits(width);
    sn_blast_copy(result, source, width);
    return result;
}

static inline void sn_blast_hier_prepare_frame(sn_blast_hier_frame_t* frame, Mini_Aig_t* aig,
                                                sn_blast_options_t options)
{
    frame->blast.aig = aig;
    frame->blast.options = options;
    frame->blast.special_eval = sn_blast_hier_eval_inst;
    frame->blast.special_data = frame;
    for (sn_obj_id_t object = 0; object < frame->blast.module->obj_types.size; object++)
        if (frame->children[object])
            sn_blast_hier_prepare_frame(frame->children[object], aig, options);
}

static inline void sn_blast_hier_seed_object(sn_blast_hier_frame_t* frame, sn_obj_id_t object, Mini_Aig_t* aig,
                                              bool invert)
{
    const sn_module_t* module = frame->blast.module;
    uint32_t width = sn_obj_width(module, object);
    assert(!frame->blast.bits[object]);
    frame->blast.bits[object] = sn_blast_alloc_bits(width);
    for (uint32_t bit = 0; bit < width; bit++)
    {
        int input = Mini_AigCreatePi(aig);
        frame->blast.bits[object][bit] = invert ? Mini_AigLitNot(input) : input;
    }
    frame->blast.state[object] = 2;
}

static inline void sn_blast_boundary_add_bit(sn_blast_hier_t* hierarchy, bool is_ci,
                                              sn_blast_boundary_kind_t kind, sn_blast_hier_frame_t* frame,
                                              sn_obj_id_t object, uint32_t bit, uint32_t owner, uint32_t port)
{
    if (!hierarchy->boundary)
        return;
    sn_vec_t* bits = is_ci ? &hierarchy->boundary->cis : &hierarchy->boundary->cos;
    sn_blast_boundary_bit_t* entry = sn_vec_push(sn_blast_boundary_bit_t, bits);
    entry->kind = kind;
    entry->signal.occurrence = frame->occurrence;
    entry->signal.object = object;
    entry->signal.bit = bit;
    entry->owner = owner;
    entry->port = port;
}

static inline void sn_blast_hier_seed_abstract_inst(sn_blast_hier_object_t occurrence, Mini_Aig_t* aig)
{
    const sn_module_t* module = occurrence.frame->blast.module;
    sn_obj_id_t inst = occurrence.object;
    const sn_module_t* child = sn_design_get_module_const(occurrence.frame->hierarchy->design,
                                                           sn_inst_module_id(module, inst));
    uint32_t output_count = (uint32_t)child->type_objects[SN_PO].size;
    sn_blast_primitive_t* primitive = NULL;
    if (occurrence.frame->hierarchy->boundary)
    {
        primitive = &sn_vec_at(sn_blast_primitive_t, &occurrence.frame->hierarchy->boundary->primitives,
                               occurrence.boundary_owner);
        // The boundary vector is the running CI count. Mini_AigPiNum() scans the whole manager and must not be used
        // here because this routine is called once per primitive occurrence.
        primitive->ci_begin = (uint32_t)occurrence.frame->hierarchy->boundary->cis.size;
    }
    for (uint32_t i = 0; i < output_count; i++)
    {
        sn_obj_id_t output = output_count == 1 ? inst : sn_inst_output(module, inst, i);
        sn_blast_hier_seed_object(occurrence.frame, output, aig, false);
        for (uint32_t bit = 0; bit < sn_obj_width(module, output); bit++)
            sn_blast_boundary_add_bit(occurrence.frame->hierarchy, true,
                                      SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT, occurrence.frame, output, bit,
                                      occurrence.boundary_owner, i);
    }
    if (primitive)
        primitive->ci_count = (uint32_t)occurrence.frame->hierarchy->boundary->cis.size - primitive->ci_begin;
}

static inline void sn_blast_hier_emit_memory_inputs(sn_blast_hier_object_t occurrence, Mini_Aig_t* aig)
{
    const sn_module_t* module = occurrence.frame->blast.module;
    sn_obj_type_t type = sn_obj_type(module, occurrence.object);
    uint32_t first = type == SN_MEM_READ ? (uint32_t)SN_MEM_READ_CLOCK : (uint32_t)SN_MEM_WRITE_CLOCK;
    uint32_t count = type == SN_MEM_READ ? (uint32_t)SN_MEM_READ_FANIN_COUNT
                                         : (uint32_t)SN_MEM_WRITE_FANIN_COUNT;
    for (uint32_t slot = first; slot < count; slot++)
    {
        sn_obj_id_t fanin = sn_obj_fanin(module, occurrence.object, slot);
        if (fanin == SN_INVALID_ID)
            continue;
        int* bits = sn_blast_eval(&occurrence.frame->blast, fanin);
        for (uint32_t bit = 0; bit < sn_obj_width(module, fanin); bit++)
        {
            Mini_AigCreatePo(aig, bits[bit]);
            sn_blast_boundary_add_bit(occurrence.frame->hierarchy, false, SN_BLAST_BOUNDARY_MEMORY_INPUT,
                                      occurrence.frame, fanin, bit, SN_INVALID_ID, slot);
        }
    }
}

static inline void sn_blast_hier_emit_register_controls(sn_blast_hier_object_t occurrence, Mini_Aig_t* aig)
{
    sn_blast_hier_t* hierarchy = occurrence.frame->hierarchy;
    if (!hierarchy->options.expose_register_controls || hierarchy->options.mode != SN_BLAST_COMB)
        return;
    const sn_module_t* module = occurrence.frame->blast.module;
    const uint32_t slots[] = {SN_REG_ENABLE, SN_REG_SET, SN_REG_RESET, SN_REG_RESET_VALUE};
    for (size_t i = 0; i < sizeof(slots) / sizeof(slots[0]); i++)
    {
        uint32_t slot = slots[i];
        if (!sn_blast_reg_control_is_comb_output(module, occurrence.object, slot))
            continue;
        sn_obj_id_t fanin = sn_obj_fanin(module, occurrence.object, slot);
        if (fanin == SN_INVALID_ID)
            continue;
        int* bits = sn_blast_eval(&occurrence.frame->blast, fanin);
        if (hierarchy->boundary)
            sn_vec_at(sn_blast_register_t, &hierarchy->boundary->registers,
                      occurrence.boundary_owner).control_co_begin[slot] =
                (uint32_t)hierarchy->boundary->cos.size;
        for (uint32_t bit = 0; bit < sn_obj_width(module, fanin); bit++)
        {
            Mini_AigCreatePo(aig, bits[bit]);
            sn_blast_boundary_add_bit(hierarchy, false, SN_BLAST_BOUNDARY_REG_CONTROL, occurrence.frame,
                                      fanin, bit, occurrence.boundary_owner, slot);
        }
    }
}

// Constructs the edge-triggered next-state function. Synchronous reset has
// highest priority, followed by synchronous set, enable, and the raw data input,
// matching the SN Verilog writer. Clock and asynchronous controls deliberately
// remain outside the sequential AIG transition relation.
static inline int* sn_blast_hier_reg_next(sn_blast_hier_object_t occurrence)
{
    sn_blast_ctx_t* context = &occurrence.frame->blast;
    const sn_module_t* module = context->module;
    sn_obj_id_t reg_out = occurrence.object;
    sn_obj_id_t reg_in = sn_obj_fanin(module, reg_out, SN_REG_DATA);
    sn_obj_id_t data = sn_obj_fanin(module, reg_in, 0);
    uint32_t width = sn_obj_width(module, reg_out);
    uint32_t flags = sn_obj_reg_flags(module, reg_out);
    int* source = sn_blast_eval(context, data);
    int* result = sn_blast_alloc_bits(width);
    sn_blast_copy(result, source, width);

    sn_obj_id_t enable = sn_obj_fanin(module, reg_out, SN_REG_ENABLE);
    if (enable != SN_INVALID_ID)
    {
        int control = sn_blast_eval(context, enable)[0];
        int* state = sn_blast_eval(context, reg_out);
        for (uint32_t bit = 0; bit < width; bit++)
            result[bit] = Mini_AigMux(context->aig, control, result[bit], state[bit]);
    }

    sn_obj_id_t set = sn_obj_fanin(module, reg_out, SN_REG_SET);
    if (set != SN_INVALID_ID && !(flags & SN_REG_SET_ASYNC))
    {
        int control = sn_blast_eval(context, set)[0];
        if (flags & SN_REG_SET_NEGEDGE)
            control = Mini_AigLitNot(control);
        for (uint32_t bit = 0; bit < width; bit++)
            result[bit] = Mini_AigMux(context->aig, control, Mini_AigLitConst1(), result[bit]);
    }

    sn_obj_id_t reset = sn_obj_fanin(module, reg_out, SN_REG_RESET);
    if (reset != SN_INVALID_ID && !(flags & SN_REG_RESET_ASYNC))
    {
        int control = sn_blast_eval(context, reset)[0];
        if (flags & SN_REG_RESET_NEGEDGE)
            control = Mini_AigLitNot(control);
        sn_obj_id_t value = sn_obj_fanin(module, reg_out, SN_REG_RESET_VALUE);
        int* reset_bits = value == SN_INVALID_ID ? NULL : sn_blast_eval(context, value);
        for (uint32_t bit = 0; bit < width; bit++)
            result[bit] = Mini_AigMux(context->aig, control,
                                      reset_bits ? reset_bits[bit] : Mini_AigLitConst0(), result[bit]);
    }
    return result;
}

static inline void sn_blast_hier_destroy_frame(sn_blast_hier_frame_t* frame)
{
    for (sn_obj_id_t object = 0; object < frame->blast.module->obj_types.size; object++)
    {
        if (frame->children[object])
            sn_blast_hier_destroy_frame(frame->children[object]);
        free(frame->blast.bits[object]);
    }
    free(frame->blast.bits);
    free(frame->blast.state);
    free(frame->children);
    free(frame);
}

// Derives one flat MiniAIG directly from a hierarchical SN design without first
// materializing a flat SN module. Every reachable module must be in SN
// topological order. A preliminary depth-first walk builds one lightweight
// object-to-literal frame per inst occurrence and counts top-level ports,
// flop bits, generic memories, and mapped RAM/DSP leaf insts. This permits
// all MiniAIG CIs to be created before the first AND: top PIs first, abstracted
// memory/DSP outputs next, and flop outputs last. The second depth-first walk
// binds each child PI to its inst fanin and bit-blasts child outputs in
// place. It emits top POs first, combinational register-control side outputs and
// abstract-box inputs next, and flop inputs last; the flop CIs and COs therefore
// occupy MiniAIG's required final positions.
// Every final MiniAIG node is created directly in this one manager: there is no
// temporary AIG, AIG duplication, or AIG-literal remapping pass. Consequently
// the AIG is flat while the usually much larger, attribute-rich collapsed SN
// module is never allocated. Generic memories and mapped RAM/DSP insts are
// black-boxed as extra CI/CO bundles according to the options.
//
// The boundary variant fills an initialized, empty descriptor whose stable
// occurrence/object/bit references survive destruction of the temporary frames.
// In combinational mode, synchronous enable/set/reset inputs become side COs
// before the raw register-data COs; clock and asynchronous controls are omitted.
// In sequential mode these synchronous controls are folded into the effective D
// function instead. The caller releases the descriptor with
// sn_blast_boundary_destroy().
static inline Mini_Aig_t* sn_design_blast_hier_boundary_options(const sn_design_t* design,
                                                                sn_module_id_t top_module_id,
                                                                sn_blast_options_t options,
                                                                sn_blast_hier_stats_t* returned_stats,
                                                                sn_blast_boundary_t* boundary)
{
    assert(design && top_module_id < design->modules.size);
    sn_blast_hier_t hierarchy;
    memset(&hierarchy, 0, sizeof(hierarchy));
    hierarchy.design = design;
    hierarchy.options = options;
    hierarchy.boundary = boundary;
    if (boundary)
        assert(boundary->occurrences.size == 0 && boundary->primitives.size == 0 &&
               boundary->registers.size == 0 && boundary->loops.size == 0 &&
               boundary->cis.size == 0 && boundary->cos.size == 0);
    hierarchy.active_modules = (uint8_t*)calloc(design->modules.size, sizeof(uint8_t));
    assert(hierarchy.active_modules);
    sn_vec_init(&hierarchy.memory_reads);
    sn_vec_init(&hierarchy.memory_writes);
    sn_vec_init(&hierarchy.registers);
    sn_vec_init(&hierarchy.loops);
    sn_vec_init(&hierarchy.abstract_insts);

    sn_blast_hier_frame_t* root =
        sn_blast_hier_build_frame(&hierarchy, top_module_id, SN_INVALID_ID, SN_INVALID_ID, NULL);
    const sn_module_t* top = root->blast.module;
    for (size_t i = 0; i < top->type_objects[SN_PI].size; i++)
        hierarchy.stats.primary_input_bits +=
            sn_obj_width(top, sn_vec_at(sn_obj_id_t, &top->type_objects[SN_PI], i));
    for (size_t i = 0; i < top->type_objects[SN_PO].size; i++)
        hierarchy.stats.primary_output_bits +=
            sn_obj_width(top, sn_vec_at(sn_obj_id_t, &top->type_objects[SN_PO], i));

    hierarchy.aig = Mini_AigStart();
    sn_blast_hier_prepare_frame(root, hierarchy.aig, options);
    for (size_t i = 0; i < top->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &top->type_objects[SN_PI], i);
        sn_blast_hier_seed_object(root, object, hierarchy.aig, false);
        for (uint32_t bit = 0; bit < sn_obj_width(top, object); bit++)
            sn_blast_boundary_add_bit(&hierarchy, true, SN_BLAST_BOUNDARY_TOP_PI, root, object, bit,
                                      SN_INVALID_ID, (uint32_t)i);
    }
    for (size_t i = 0; i < hierarchy.memory_reads.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.memory_reads, i);
        sn_blast_hier_seed_object(occurrence.frame, occurrence.object, hierarchy.aig, false);
        for (uint32_t bit = 0; bit < sn_obj_width(occurrence.frame->blast.module, occurrence.object); bit++)
            sn_blast_boundary_add_bit(&hierarchy, true, SN_BLAST_BOUNDARY_MEMORY_OUTPUT, occurrence.frame,
                                      occurrence.object, bit, SN_INVALID_ID, (uint32_t)i);
    }
    for (size_t i = 0; i < hierarchy.abstract_insts.size; i++)
        sn_blast_hier_seed_abstract_inst(
            sn_vec_at(sn_blast_hier_object_t, &hierarchy.abstract_insts, i), hierarchy.aig);
    for (size_t i = 0; i < hierarchy.loops.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.loops, i);
        sn_blast_hier_seed_object(occurrence.frame, occurrence.object, hierarchy.aig, false);
        for (uint32_t bit = 0; bit < sn_obj_width(occurrence.frame->blast.module, occurrence.object); bit++)
            sn_blast_boundary_add_bit(&hierarchy, true, SN_BLAST_BOUNDARY_LOOP_OUTPUT, occurrence.frame,
                                      occurrence.object, bit, occurrence.boundary_owner, bit);
    }
    for (size_t i = 0; i < hierarchy.registers.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.registers, i);
        if (boundary)
            sn_vec_at(sn_blast_register_t, &boundary->registers, occurrence.boundary_owner).ci_begin =
                (uint32_t)boundary->cis.size;
        sn_blast_hier_seed_object(occurrence.frame, occurrence.object, hierarchy.aig, false);
        if (sn_blast_mode_has_transition(options.mode))
            for (uint32_t bit = 0;
                 bit < sn_obj_width(occurrence.frame->blast.module, occurrence.object); bit++)
                if (sn_blast_reg_init_bit(occurrence.frame->blast.module, occurrence.object, bit))
                    occurrence.frame->blast.bits[occurrence.object][bit] =
                        Mini_AigLitNot(occurrence.frame->blast.bits[occurrence.object][bit]);
        for (uint32_t bit = 0; bit < sn_obj_width(occurrence.frame->blast.module, occurrence.object); bit++)
            sn_blast_boundary_add_bit(&hierarchy, true, SN_BLAST_BOUNDARY_REG_OUTPUT, occurrence.frame,
                                      occurrence.object, bit, occurrence.boundary_owner, bit);
    }
    assert((uint64_t)Mini_AigPiNum(hierarchy.aig) == hierarchy.stats.primary_input_bits +
                                                       hierarchy.stats.abstraction_output_bits +
                                                       hierarchy.stats.flop_bits);

    // Evaluate every emitted CO cone before creating the first PO. MiniAIG's
    // normalized form requires all AND nodes to precede all POs. This selective
    // preparation also avoids elaborating clock and asynchronous-control cones.
    int** reg_next = (int**)calloc(hierarchy.registers.size, sizeof(int*));
    assert(reg_next || hierarchy.registers.size == 0);
    for (size_t i = 0; i < top->type_objects[SN_PO].size; i++)
        sn_blast_eval(&root->blast, sn_vec_at(sn_obj_id_t, &top->type_objects[SN_PO], i));
    for (size_t i = 0; i < hierarchy.registers.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.registers, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        if (sn_blast_mode_has_transition(options.mode))
            reg_next[i] = sn_blast_hier_reg_next(occurrence);
        else
        {
            sn_obj_id_t reg_in = sn_obj_fanin(module, occurrence.object, SN_REG_DATA);
            sn_blast_eval(&occurrence.frame->blast, sn_obj_fanin(module, reg_in, 0));
            const uint32_t slots[] = {SN_REG_ENABLE, SN_REG_SET, SN_REG_RESET, SN_REG_RESET_VALUE};
            for (size_t k = 0; k < sizeof(slots) / sizeof(slots[0]); k++)
                if (sn_blast_reg_control_is_comb_output(module, occurrence.object, slots[k]))
                {
                    sn_obj_id_t fanin = sn_obj_fanin(module, occurrence.object, slots[k]);
                    if (fanin != SN_INVALID_ID)
                        sn_blast_eval(&occurrence.frame->blast, fanin);
                }
        }
    }
    for (size_t i = 0; i < hierarchy.memory_reads.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.memory_reads, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        for (uint32_t slot = SN_MEM_READ_CLOCK; slot < SN_MEM_READ_FANIN_COUNT; slot++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, occurrence.object, slot);
            if (fanin != SN_INVALID_ID)
                sn_blast_eval(&occurrence.frame->blast, fanin);
        }
    }
    for (size_t i = 0; i < hierarchy.memory_writes.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.memory_writes, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        for (uint32_t slot = SN_MEM_WRITE_CLOCK; slot < SN_MEM_WRITE_FANIN_COUNT; slot++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, occurrence.object, slot);
            if (fanin != SN_INVALID_ID)
                sn_blast_eval(&occurrence.frame->blast, fanin);
        }
    }
    for (size_t i = 0; i < hierarchy.abstract_insts.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.abstract_insts, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        for (uint32_t slot = 0; slot < sn_obj_fanin_count(module, occurrence.object); slot++)
            sn_blast_eval(&occurrence.frame->blast, sn_obj_fanin(module, occurrence.object, slot));
    }
    for (size_t i = 0; i < hierarchy.loops.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.loops, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        sn_obj_id_t loop_in = sn_obj_pair_in(module, occurrence.object);
        sn_blast_eval(&occurrence.frame->blast, sn_obj_fanin(module, loop_in, 0));
    }

    for (size_t i = 0; i < top->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &top->type_objects[SN_PO], i);
        int* bits = sn_blast_eval(&root->blast, object);
        for (uint32_t bit = 0; bit < sn_obj_width(top, object); bit++)
        {
            Mini_AigCreatePo(hierarchy.aig, bits[bit]);
            sn_blast_boundary_add_bit(&hierarchy, false, SN_BLAST_BOUNDARY_TOP_PO, root, object, bit,
                                      SN_INVALID_ID, (uint32_t)i);
        }
    }
    for (size_t i = 0; i < hierarchy.registers.size; i++)
        sn_blast_hier_emit_register_controls(
            sn_vec_at(sn_blast_hier_object_t, &hierarchy.registers, i), hierarchy.aig);
    for (size_t i = 0; i < hierarchy.memory_reads.size; i++)
        sn_blast_hier_emit_memory_inputs(sn_vec_at(sn_blast_hier_object_t, &hierarchy.memory_reads, i),
                                         hierarchy.aig);
    for (size_t i = 0; i < hierarchy.memory_writes.size; i++)
        sn_blast_hier_emit_memory_inputs(sn_vec_at(sn_blast_hier_object_t, &hierarchy.memory_writes, i),
                                         hierarchy.aig);
    for (size_t i = 0; i < hierarchy.abstract_insts.size; i++)
    {
        sn_blast_hier_object_t occurrence =
            sn_vec_at(sn_blast_hier_object_t, &hierarchy.abstract_insts, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        sn_blast_primitive_t* primitive = NULL;
        if (boundary)
        {
            primitive = &sn_vec_at(sn_blast_primitive_t, &boundary->primitives, occurrence.boundary_owner);
            // As above, the boundary vector provides a constant-time running count; Mini_AigPoNum() is linear.
            primitive->co_begin = (uint32_t)boundary->cos.size;
        }
        for (uint32_t slot = 0; slot < sn_obj_fanin_count(module, occurrence.object); slot++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, occurrence.object, slot);
            int* bits = sn_blast_eval(&occurrence.frame->blast, fanin);
            for (uint32_t bit = 0; bit < sn_obj_width(module, fanin); bit++)
            {
                Mini_AigCreatePo(hierarchy.aig, bits[bit]);
                sn_blast_boundary_add_bit(&hierarchy, false, SN_BLAST_BOUNDARY_PRIMITIVE_INPUT,
                                          occurrence.frame, fanin, bit, occurrence.boundary_owner, slot);
            }
        }
        if (primitive)
            primitive->co_count = (uint32_t)boundary->cos.size - primitive->co_begin;
    }
    for (size_t i = 0; i < hierarchy.loops.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.loops, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        sn_obj_id_t loop_in = sn_obj_pair_in(module, occurrence.object);
        sn_obj_id_t data = sn_obj_fanin(module, loop_in, 0);
        int* bits = sn_blast_eval(&occurrence.frame->blast, data);
        if (boundary)
            sn_vec_at(sn_blast_loop_t, &boundary->loops, occurrence.boundary_owner).co_begin =
                (uint32_t)boundary->cos.size;
        for (uint32_t bit = 0; bit < sn_obj_width(module, occurrence.object); bit++)
        {
            Mini_AigCreatePo(hierarchy.aig, bits[bit]);
            sn_blast_boundary_add_bit(&hierarchy, false, SN_BLAST_BOUNDARY_LOOP_INPUT, occurrence.frame,
                                      data, bit, occurrence.boundary_owner, bit);
        }
    }

    // Register inputs are deliberately emitted last; nRegs pairs the final CIs and final COs.
    for (size_t i = 0; i < hierarchy.registers.size; i++)
    {
        sn_blast_hier_object_t occurrence = sn_vec_at(sn_blast_hier_object_t, &hierarchy.registers, i);
        const sn_module_t* module = occurrence.frame->blast.module;
        sn_obj_id_t reg_in = sn_obj_fanin(module, occurrence.object, SN_REG_DATA);
        sn_obj_id_t data = sn_obj_fanin(module, reg_in, 0);
        int* bits = sn_blast_mode_has_transition(options.mode) ? reg_next[i]
                                                               : sn_blast_eval(&occurrence.frame->blast, data);
        if (boundary)
            sn_vec_at(sn_blast_register_t, &boundary->registers, occurrence.boundary_owner).co_begin =
                (uint32_t)boundary->cos.size;
        for (uint32_t bit = 0; bit < sn_obj_width(module, occurrence.object); bit++)
        {
            bool invert = sn_blast_mode_has_transition(options.mode) &&
                          sn_blast_reg_init_bit(module, occurrence.object, bit);
            Mini_AigCreatePo(hierarchy.aig, invert ? Mini_AigLitNot(bits[bit]) : bits[bit]);
            sn_blast_boundary_add_bit(&hierarchy, false, SN_BLAST_BOUNDARY_REG_INPUT, occurrence.frame,
                                      data, bit, occurrence.boundary_owner, bit);
        }
        if (sn_blast_mode_has_transition(options.mode))
            free(reg_next[i]);
    }
    free(reg_next);

    Mini_AigSetRegNum(hierarchy.aig, options.mode == SN_BLAST_SEQ ? (int)hierarchy.stats.flop_bits : 0);
    assert(Mini_AigIsNormalized(hierarchy.aig));
    if (boundary)
    {
        boundary->register_bits = (uint32_t)Mini_AigRegNum(hierarchy.aig);
        assert(boundary->cis.size == (size_t)Mini_AigPiNum(hierarchy.aig));
        assert(boundary->cos.size == (size_t)Mini_AigPoNum(hierarchy.aig));
    }
    if (returned_stats)
        *returned_stats = hierarchy.stats;
    Mini_Aig_t* result = hierarchy.aig;
    sn_blast_hier_destroy_frame(root);
    sn_vec_destroy(&hierarchy.memory_reads);
    sn_vec_destroy(&hierarchy.memory_writes);
    sn_vec_destroy(&hierarchy.registers);
    sn_vec_destroy(&hierarchy.loops);
    sn_vec_destroy(&hierarchy.abstract_insts);
    free(hierarchy.active_modules);
    return result;
}

static inline Mini_Aig_t* sn_design_blast_hier_options(const sn_design_t* design, sn_module_id_t top_module_id,
                                                       sn_blast_options_t options,
                                                       sn_blast_hier_stats_t* returned_stats)
{
    return sn_design_blast_hier_boundary_options(design, top_module_id, options, returned_stats, NULL);
}

static inline Mini_Aig_t* sn_design_blast_hier(const sn_design_t* design, sn_module_id_t top_module_id)
{
    return sn_design_blast_hier_options(design, top_module_id, sn_blast_default_options(), NULL);
}

static inline Mini_Aig_t* sn_design_blast_hier_seq_options(const sn_design_t* design, sn_module_id_t top_module_id,
                                                           sn_blast_options_t options,
                                                           sn_blast_hier_stats_t* returned_stats)
{
    options.mode = SN_BLAST_SEQ;
    return sn_design_blast_hier_options(design, top_module_id, options, returned_stats);
}

static inline Mini_Aig_t* sn_design_blast_hier_seq(const sn_design_t* design, sn_module_id_t top_module_id)
{
    return sn_design_blast_hier_seq_options(design, top_module_id, sn_blast_default_options(), NULL);
}

static inline Mini_Aig_t* sn_design_blast_hier_transition(const sn_design_t* design,
                                                          sn_module_id_t top_module_id)
{
    sn_blast_options_t options = sn_blast_default_options();
    options.mode = SN_BLAST_TRANSITION;
    return sn_design_blast_hier_options(design, top_module_id, options, NULL);
}

// Keep the standalone-module API as a thin adapter around the hierarchical
// driver so register controls, loop boundaries, and initialization semantics
// cannot drift between the two exported blasting paths.
static inline Mini_Aig_t* sn_module_blast_comb_options(const sn_module_t* module,
                                                       sn_blast_options_t options)
{
    sn_blast_check_module(module, options);
    sn_design_t wrapper;
    memset(&wrapper, 0, sizeof(wrapper));
    sn_vec_init(&wrapper.modules);
    *sn_vec_push(sn_module_t*, &wrapper.modules) = (sn_module_t*)module;
    Mini_Aig_t* aig = sn_design_blast_hier_options(&wrapper, 0, options, NULL);
    sn_vec_destroy(&wrapper.modules);
    return aig;
}

static inline Mini_Aig_t* sn_design_blast_comb_options(sn_design_t* design, sn_module_id_t module_id,
                                                       sn_blast_options_t options)
{
    assert(design);
    assert(module_id < design->modules.size);
    return sn_design_blast_hier_options(design, module_id, options, NULL);
}

static inline Mini_Aig_t* sn_design_blast_comb(sn_design_t* design, sn_module_id_t module_id)
{
    return sn_design_blast_comb_options(design, module_id, sn_blast_default_options());
}

static inline Mini_Aig_t* sn_design_blast_seq_options(sn_design_t* design, sn_module_id_t module_id,
                                                      sn_blast_options_t options)
{
    options.mode = SN_BLAST_SEQ;
    return sn_design_blast_comb_options(design, module_id, options);
}

static inline Mini_Aig_t* sn_design_blast_seq(sn_design_t* design, sn_module_id_t module_id)
{
    return sn_design_blast_seq_options(design, module_id, sn_blast_default_options());
}

static inline void sn_module_write_aiger(const sn_module_t* module, const char* file_name,
                                         sn_blast_options_t options)
{
    assert(module && file_name);
    Mini_Aig_t* aig = sn_module_blast_comb_options(module, options);
    Mini_AigerWrite((char*)file_name, aig, 0);
    Mini_AigStop(aig);
}

ABC_NAMESPACE_HEADER_END

#endif
