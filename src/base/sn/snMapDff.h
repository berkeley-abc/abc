/**CFile****************************************************************

  FileName    [snMapDff.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Word-level register optimization and flip-flop mapping.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapDff.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MAP_DFF_H
#define SN_MAP_DFF_H

// Optimizes word-level registers before flip-flop technology mapping.
// Registers that provably hold one constant value under SN's two-state
// sequential convention become that constant. Registers with identical
// controls, initialization, and next-state data merge into one. Merging is
// interleaved with combinational subexpression sharing until a fixed point,
// so registers whose next-state cones become identical only after earlier
// merges are found as well. Logic left without fanout is swept afterwards.
// Flop-cell legalization and shift-register extraction can later extend this
// pass; they must also run before LUT mapping so the LUT mapper covers the
// final combinational cloud.

#include "sn.h"

ABC_NAMESPACE_HEADER_START

typedef struct sn_dff_map_options_t
{
    bool fold_constants;
    bool merge_registers;
    bool merge_logic;
    // 0 iterates to a fixed point; a chain of n identical shift registers
    // needs n rounds, so a small cap can leave duplicates behind.
    uint32_t max_rounds;
} sn_dff_map_options_t;

static inline sn_dff_map_options_t sn_dff_map_default_options(void)
{
    sn_dff_map_options_t options = {true, true, true, 0};
    return options;
}

typedef struct sn_dff_map_stats_t
{
    size_t modules_changed;
    size_t const_regs;
    size_t merged_regs;
    size_t merged_objects;
    size_t reg_bits_before;
    size_t reg_bits_after;
    size_t regs_before;
    size_t regs_after;
} sn_dff_map_stats_t;

// One representative per object. Merged objects point at an earlier
// equivalent; chains arise when a representative itself merges in a later
// round, so resolution follows the chain with path compression.
static inline sn_obj_id_t sn_dff_rep(sn_obj_id_t* reps, sn_obj_id_t object)
{
    if (object == SN_INVALID_ID)
        return SN_INVALID_ID;
    sn_obj_id_t root = object;
    while (reps[root] != root)
        root = reps[root];
    while (reps[object] != root)
    {
        sn_obj_id_t next = reps[object];
        reps[object] = root;
        object = next;
    }
    return root;
}

static inline uint64_t sn_dff_hash_mix(uint64_t hash, uint64_t value)
{
    return (hash ^ value) * UINT64_C(1099511628211);
}

// Objects the sharing pass may merge. Interface objects, state pairs, memory
// ports, ordering boundaries, and insts (whose child may be an opaque black
// box) keep their identity.
static inline bool sn_dff_object_shareable(sn_obj_type_t type)
{
    if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
        return true;
    return sn_obj_type_is_operator(type);
}

static inline uint64_t sn_dff_object_signature(const sn_module_t* module, sn_obj_id_t object, sn_obj_id_t* reps)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    uint64_t hash = UINT64_C(1469598103934665603);
    hash = sn_dff_hash_mix(hash, type);
    hash = sn_dff_hash_mix(hash, sn_obj_width(module, object));
    hash = sn_dff_hash_mix(hash, sn_obj_is_signed(module, object) ? 1 : 0);
    if (type == SN_CONST)
    {
        for (uint32_t i = 0; i < sn_const_word_count(sn_obj_width(module, object)); i++)
            hash = sn_dff_hash_mix(hash, sn_const_word(module, object, i));
    }
    else if (type == SN_SLICE)
    {
        sn_slice_info_t info = sn_obj_slice_info(module, object);
        hash = sn_dff_hash_mix(hash, (uint32_t)info.left_index);
        hash = sn_dff_hash_mix(hash, (uint32_t)info.right_index);
        hash = sn_dff_hash_mix(hash, info.flags);
    }
    else if (type == SN_REPLICATE)
        hash = sn_dff_hash_mix(hash, sn_obj_repeat_count(module, object));
    else if (type == SN_LUT)
        hash = sn_dff_hash_mix(hash, sn_obj_lut_truth(module, object));
    else if (type == SN_GATE)
        hash = sn_dff_hash_mix(hash, sn_obj_gate_id(module, object));
    uint32_t fanin_count = sn_obj_fanin_count(module, object);
    hash = sn_dff_hash_mix(hash, fanin_count);
    for (uint32_t i = 0; i < fanin_count; i++)
        hash = sn_dff_hash_mix(hash, sn_dff_rep(reps, sn_obj_fanin(module, object, i)));
    return hash;
}

static inline bool sn_dff_objects_equal(const sn_module_t* module, sn_obj_id_t a, sn_obj_id_t b,
                                        sn_obj_id_t* reps)
{
    sn_obj_type_t type = sn_obj_type(module, a);
    if (type != sn_obj_type(module, b) || sn_obj_width(module, a) != sn_obj_width(module, b) ||
        sn_obj_is_signed(module, a) != sn_obj_is_signed(module, b))
        return false;
    if (type == SN_CONST)
    {
        if (sn_obj_data(module, a) != sn_obj_data(module, b))
            return false;
    }
    else if (type == SN_SLICE)
    {
        sn_slice_info_t info_a = sn_obj_slice_info(module, a);
        sn_slice_info_t info_b = sn_obj_slice_info(module, b);
        if (info_a.left_index != info_b.left_index || info_a.right_index != info_b.right_index ||
            info_a.flags != info_b.flags)
            return false;
    }
    else if (type == SN_REPLICATE)
    {
        if (sn_obj_repeat_count(module, a) != sn_obj_repeat_count(module, b))
            return false;
    }
    else if (type == SN_LUT)
    {
        if (sn_obj_lut_truth(module, a) != sn_obj_lut_truth(module, b))
            return false;
    }
    else if (type == SN_GATE)
    {
        if (sn_obj_gate_id(module, a) != sn_obj_gate_id(module, b))
            return false;
    }
    uint32_t fanin_count = sn_obj_fanin_count(module, a);
    if (fanin_count != sn_obj_fanin_count(module, b))
        return false;
    for (uint32_t i = 0; i < fanin_count; i++)
        if (sn_dff_rep(reps, sn_obj_fanin(module, a, i)) != sn_dff_rep(reps, sn_obj_fanin(module, b, i)))
            return false;
    return true;
}

// The next-state value used for register comparison. Direct self-feedback is
// canonicalized to a shared sentinel so two registers that each hold their
// own value merge; the remaining controls decide their equivalence.
#define SN_DFF_SELF_FEEDBACK ((sn_obj_id_t)0xfffffffeu)

static inline sn_obj_id_t sn_dff_reg_data(const sn_module_t* module, sn_obj_id_t reg_out, sn_obj_id_t* reps)
{
    sn_obj_id_t data = sn_dff_rep(reps, sn_obj_fanin(module, sn_obj_pair_in(module, reg_out), 0));
    return data == reg_out ? SN_DFF_SELF_FEEDBACK : data;
}

// Register signature and equality cover controls, polarity flags,
// initialization, and next-state data through representatives. The data slot
// is folded separately so that self-feedback compares canonically.
static inline uint64_t sn_dff_reg_signature(const sn_module_t* module, sn_obj_id_t reg_out, sn_obj_id_t* reps)
{
    uint64_t hash = UINT64_C(1469598103934665603);
    hash = sn_dff_hash_mix(hash, sn_obj_width(module, reg_out));
    hash = sn_dff_hash_mix(hash, sn_obj_is_signed(module, reg_out) ? 1 : 0);
    hash = sn_dff_hash_mix(hash, sn_obj_reg_flags(module, reg_out));
    for (uint32_t slot = 0; slot < SN_REG_FANIN_COUNT; slot++)
        if (slot != SN_REG_DATA)
            hash = sn_dff_hash_mix(hash, sn_dff_rep(reps, sn_reg_fanin(module, reg_out, (sn_reg_fanin_t)slot)));
    hash = sn_dff_hash_mix(hash, sn_dff_reg_data(module, reg_out, reps));
    return hash;
}

static inline bool sn_dff_regs_equal(const sn_module_t* module, sn_obj_id_t a, sn_obj_id_t b, sn_obj_id_t* reps)
{
    if (sn_obj_width(module, a) != sn_obj_width(module, b) ||
        sn_obj_is_signed(module, a) != sn_obj_is_signed(module, b) ||
        sn_obj_reg_flags(module, a) != sn_obj_reg_flags(module, b))
        return false;
    for (uint32_t slot = 0; slot < SN_REG_FANIN_COUNT; slot++)
        if (slot != SN_REG_DATA &&
            sn_dff_rep(reps, sn_reg_fanin(module, a, (sn_reg_fanin_t)slot)) !=
                sn_dff_rep(reps, sn_reg_fanin(module, b, (sn_reg_fanin_t)slot)))
            return false;
    return sn_dff_reg_data(module, a, reps) == sn_dff_reg_data(module, b, reps);
}

typedef struct sn_dff_hash_table_t
{
    uint64_t* hashes;
    sn_obj_id_t* objects;
    size_t mask;
} sn_dff_hash_table_t;

static inline void sn_dff_hash_init(sn_dff_hash_table_t* table, size_t expected)
{
    size_t size = 64;
    while (size < expected * 2)
        size *= 2;
    table->hashes = (uint64_t*)calloc(size, sizeof(uint64_t));
    table->objects = (sn_obj_id_t*)malloc(size * sizeof(sn_obj_id_t));
    assert(table->hashes && table->objects);
    for (size_t i = 0; i < size; i++)
        table->objects[i] = SN_INVALID_ID;
    table->mask = size - 1;
}

static inline void sn_dff_hash_clear(sn_dff_hash_table_t* table)
{
    for (size_t i = 0; i <= table->mask; i++)
        table->objects[i] = SN_INVALID_ID;
}

static inline void sn_dff_hash_destroy(sn_dff_hash_table_t* table)
{
    free(table->hashes);
    free(table->objects);
}

// Returns the previously inserted equivalent object or inserts this one.
static inline sn_obj_id_t sn_dff_hash_find_or_insert(sn_dff_hash_table_t* table, const sn_module_t* module,
                                                     sn_obj_id_t object, uint64_t hash, sn_obj_id_t* reps,
                                                     bool is_reg)
{
    size_t slot = (size_t)hash & table->mask;
    while (table->objects[slot] != SN_INVALID_ID)
    {
        sn_obj_id_t existing = table->objects[slot];
        if (table->hashes[slot] == hash &&
            (is_reg ? sn_dff_regs_equal(module, existing, object, reps)
                    : sn_dff_objects_equal(module, existing, object, reps)))
            return existing;
        slot = (slot + 1) & table->mask;
    }
    table->hashes[slot] = hash;
    table->objects[slot] = object;
    return object;
}

static inline bool sn_dff_const_like(sn_obj_type_t type)
{
    return type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST;
}

// Bit of the constant a register holds when only its initialization drives
// it. Unspecified and masked-out bits start at zero under SN's two-state
// sequential convention.
static inline bool sn_dff_init_bit(const sn_module_t* module, sn_obj_id_t init_data, sn_obj_id_t init_mask,
                                   uint32_t bit)
{
    if (init_data == SN_INVALID_ID)
        return false;
    if (init_mask != SN_INVALID_ID && !sn_const_bit(module, init_mask, bit))
        return false;
    return sn_const_bit(module, init_data, bit);
}

// Decides whether this register provably holds one constant value forever.
// The reasoning is deliberately local: the initialization value is the
// candidate, the next-state data must be that same constant, the register's
// own output, or gated off by a never-true enable, and any reachable set or
// reset must reload the same value.
static inline bool sn_dff_reg_constant(const sn_module_t* module, sn_obj_id_t reg_out, sn_obj_id_t* reps,
                                       uint8_t* zero_cache, uint32_t* value_words)
{
    uint32_t width = sn_obj_width(module, reg_out);
    uint32_t flags = sn_obj_reg_flags(module, reg_out);
    sn_obj_id_t init_data = sn_obj_reg_init_data(module, reg_out);
    sn_obj_id_t init_mask = sn_obj_reg_init_mask(module, reg_out);
    sn_obj_id_t enable = sn_reg_fanin(module, reg_out, SN_REG_ENABLE);
    sn_obj_id_t reset_value = sn_dff_rep(reps, sn_reg_fanin(module, reg_out, SN_REG_RESET_VALUE));
    sn_obj_id_t data = sn_dff_rep(reps, sn_obj_fanin(module, sn_obj_pair_in(module, reg_out), 0));

    for (uint32_t word = 0; word < sn_const_word_count(width); word++)
        value_words[word] = 0;
    bool all_ones = true;
    for (uint32_t bit = 0; bit < width; bit++)
    {
        bool one = sn_dff_init_bit(module, init_data, init_mask, bit);
        if (one)
            value_words[bit / 32] |= 1u << (bit % 32);
        all_ones = all_ones && one;
    }

    bool enable_off = enable != SN_INVALID_ID && sn_obj_is_const_zero_rec(module, enable, zero_cache);
    bool holds = data == reg_out || enable_off;
    if (!holds && data != SN_INVALID_ID && sn_dff_const_like(sn_obj_type(module, data)))
    {
        holds = true;
        for (uint32_t bit = 0; bit < width && holds; bit++)
            holds = sn_const_bit(module, data, bit) == (((value_words[bit / 32] >> (bit % 32)) & 1u) != 0);
    }
    if (!holds)
        return false;

    if ((flags & SN_REG_LATCH) == 0)
    {
        // Controls are judged by their polarity: an active-low set tied low fires.
        if (!sn_reg_control_inactive(module, reg_out, SN_REG_SET, zero_cache) && !all_ones)
            return false;
        if (!sn_reg_control_inactive(module, reg_out, SN_REG_RESET, zero_cache))
        {
            if (reset_value != SN_INVALID_ID && !sn_dff_const_like(sn_obj_type(module, reset_value)))
                return false;
            for (uint32_t bit = 0; bit < width; bit++)
            {
                bool one = reset_value != SN_INVALID_ID && sn_const_bit(module, reset_value, bit);
                if (one != (((value_words[bit / 32] >> (bit % 32)) & 1u) != 0))
                    return false;
            }
        }
    }
    return true;
}

// Value of one object under the assumption that every still-standing
// stuck-at-zero candidate register is zero. Wider than the assumption-free
// sn_const_zero_evaluate: buffers, arithmetic on zeros, shifts of zero, and
// LUTs at the all-zero input point propagate zero as well.
static inline bool sn_dff_zero_evaluate(const sn_module_t* module, sn_obj_id_t object, const uint8_t* zero)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_CONST0)
        return true;
    if (type == SN_CONST)
    {
        for (uint32_t i = 0; i < sn_const_word_count(sn_obj_width(module, object)); i++)
            if (sn_const_word(module, object, i))
                return false;
        return true;
    }
    switch (type)
    {
        case SN_BUF:
        case SN_POS:
        case SN_NEG:
        case SN_CAST:
        case SN_SLICE:
        case SN_REPLICATE:
        case SN_REDUCE_AND:
        case SN_REDUCE_OR:
        case SN_REDUCE_XOR:
            return sn_const_zero_cached(zero, sn_obj_fanin(module, object, 0));
        case SN_CONCAT:
        case SN_BIT_OR:
        case SN_BIT_XOR:
        case SN_LOG_OR:
        case SN_ADD:
        case SN_SUB:
        {
            for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
                if (!sn_const_zero_cached(zero, sn_obj_fanin(module, object, i)))
                    return false;
            return true;
        }
        case SN_BIT_AND:
        case SN_LOG_AND:
        case SN_MUL:
        {
            for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
                if (sn_const_zero_cached(zero, sn_obj_fanin(module, object, i)))
                    return true;
            return false;
        }
        case SN_SHL:
        case SN_SHR:
        case SN_ASHL:
        case SN_ASHR:
            return sn_const_zero_cached(zero, sn_obj_fanin(module, object, 0));
        case SN_MUX:
        {
            sn_obj_id_t select = sn_obj_fanin(module, object, SN_MUX_SELECT);
            sn_obj_id_t selected = sn_obj_fanin(module, object, SN_MUX_SELECTED);
            sn_obj_id_t default_value = sn_obj_fanin(module, object, SN_MUX_DEFAULT);
            return sn_const_zero_cached(zero, select)
                       ? sn_const_zero_cached(zero, default_value)
                       : sn_const_zero_cached(zero, selected) && sn_const_zero_cached(zero, default_value);
        }
        case SN_BMUX:
            return sn_const_zero_cached(zero, sn_obj_fanin(module, object, SN_BMUX_ALTERNATIVES));
        case SN_PMUX:
        {
            sn_obj_id_t select = sn_obj_fanin(module, object, SN_PMUX_SELECT);
            sn_obj_id_t alternatives = sn_obj_fanin(module, object, SN_PMUX_ALTERNATIVES);
            sn_obj_id_t default_value = sn_obj_fanin(module, object, SN_PMUX_DEFAULT);
            return sn_const_zero_cached(zero, select)
                       ? sn_const_zero_cached(zero, default_value)
                       : sn_const_zero_cached(zero, alternatives) && sn_const_zero_cached(zero, default_value);
        }
        case SN_LUT:
        {
            if ((sn_obj_lut_truth(module, object) & 1) != 0)
                return false;
            for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
                if (!sn_const_zero_cached(zero, sn_obj_fanin(module, object, i)))
                    return false;
            return true;
        }
        default:
            return false;
    }
}

// Inductive stuck-at-zero analysis: every register whose initialization is
// zero and whose set and reset can only reload zero starts as a candidate.
// Candidates are assumed zero, values are propagated through the module, and
// any candidate whose next-state data or controls fail under the assumption
// is demoted. The loop repeats until no demotion, so the surviving
// candidates are a genuine invariant: they start at zero and can never leave
// it. This is the word-level analogue of AIG-level sequential cleanup with
// ternary simulation from the initial state.
static inline size_t sn_dff_inductive_zero(sn_module_t* module, const sn_vec_t* order, uint8_t* candidate)
{
    size_t object_count = module->obj_types.size;
    size_t candidate_count = 0;
    uint8_t* zero = object_count ? (uint8_t*)calloc(object_count, sizeof(uint8_t)) : NULL;
    assert(!object_count || zero);

    for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        sn_obj_id_t init_data = sn_obj_reg_init_data(module, reg_out);
        sn_obj_id_t init_mask = sn_obj_reg_init_mask(module, reg_out);
        bool init_zero = true;
        for (uint32_t bit = 0; bit < sn_obj_width(module, reg_out) && init_zero; bit++)
            init_zero = !sn_dff_init_bit(module, init_data, init_mask, bit);
        candidate[reg_out] = init_zero ? 1 : 0;
        candidate_count += init_zero ? 1 : 0;
    }
    if (!candidate_count)
    {
        free(zero);
        return 0;
    }

    bool changed = true;
    while (changed)
    {
        changed = false;
        for (size_t i = 0; i < order->size; i++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, order, i);
            sn_obj_type_t type = sn_obj_type(module, object);
            if (type == SN_REG_OUT)
                zero[object] = candidate[object] ? 1 : 2;
            else
                zero[object] = sn_dff_zero_evaluate(module, object, zero) ? 1 : 2;
        }
        for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
        {
            sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
            if (!candidate[reg_out])
                continue;
            sn_obj_id_t data = sn_obj_fanin(module, sn_obj_pair_in(module, reg_out), 0);
            sn_obj_id_t set = sn_reg_fanin(module, reg_out, SN_REG_SET);
            sn_obj_id_t reset = sn_reg_fanin(module, reg_out, SN_REG_RESET);
            sn_obj_id_t reset_value = sn_reg_fanin(module, reg_out, SN_REG_RESET_VALUE);
            uint32_t reg_flags = sn_obj_reg_flags(module, reg_out);
            // An active-high control is inactive when the induction holds it at zero; an active-low
            // control only when it is structurally the constant one.
            bool set_inactive = set == SN_INVALID_ID ||
                                ((reg_flags & SN_REG_SET_NEGEDGE) ? sn_obj_is_const_one_bit(module, set)
                                                                  : sn_const_zero_cached(zero, set));
            bool reset_inactive = reset == SN_INVALID_ID ||
                                  ((reg_flags & SN_REG_RESET_NEGEDGE) ? sn_obj_is_const_one_bit(module, reset)
                                                                      : sn_const_zero_cached(zero, reset));
            bool ok = data == reg_out || sn_const_zero_cached(zero, data);
            ok = ok && set_inactive;
            ok = ok && (reset_inactive || reset_value == SN_INVALID_ID || sn_const_zero_cached(zero, reset_value));
            if (!ok)
            {
                candidate[reg_out] = 0;
                candidate_count--;
                changed = true;
            }
        }
    }
    free(zero);
    return candidate_count;
}

// Reads a constant object of at most 64 bits as an unsigned value.
static inline bool sn_dff_const_value64(const sn_module_t* module, sn_obj_id_t object, uint64_t* value)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    uint32_t width = sn_obj_width(module, object);
    if (!sn_dff_const_like(type) || width > 64)
        return false;
    if (type == SN_CONST0)
        *value = 0;
    else if (type == SN_CONST1)
        *value = 1;
    else
    {
        *value = sn_const_word(module, object, 0);
        if (width > 32)
            *value |= (uint64_t)sn_const_word(module, object, 1) << 32;
    }
    return true;
}

static inline bool sn_dff_const_is_zero(const sn_module_t* module, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_CONST0)
        return true;
    if (type != SN_CONST)
        return false;
    for (uint32_t i = 0; i < sn_const_word_count(sn_obj_width(module, object)); i++)
        if (sn_const_word(module, object, i))
            return false;
    return true;
}

static inline bool sn_dff_const_is_ones(const sn_module_t* module, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    uint32_t width = sn_obj_width(module, object);
    if (type == SN_CONST1)
        return width == 1;
    if (type != SN_CONST)
        return false;
    for (uint32_t bit = 0; bit < width; bit++)
        if (!((sn_const_word(module, object, bit / 32) >> (bit % 32)) & 1u))
            return false;
    return true;
}

// Extends a constant to 64 bits following the operand's own signedness, the
// resize SN applies to each operand of a width-defined operator.
static inline uint64_t sn_dff_extend64(uint64_t value, uint32_t width, bool is_signed)
{
    if (width == 0 || width >= 64)
        return value;
    uint64_t sign = UINT64_C(1) << (width - 1);
    if (is_signed && (value & sign))
        return value | ~((sign << 1) - 1);
    return value & ((sign << 1) - 1);
}

// Local constant folding and identity simplification. Returns the replacement
// object (an existing fanin or a fresh constant) or SN_INVALID_ID. The result
// object must match the folded object's width and signedness exactly, so a
// rule that cannot guarantee that is skipped. Folding runs inside the sharing
// fixpoint: a fold can expose further folds, shares, and register constants.
static inline sn_obj_id_t sn_dff_try_fold(sn_module_t* module, sn_obj_id_t object, sn_obj_id_t* reps,
                                          bool* build_const, uint64_t* const_value)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    uint32_t width = sn_obj_width(module, object);
    bool is_signed = sn_obj_is_signed(module, object);
    uint32_t fanin_count = sn_obj_fanin_count(module, object);
    *build_const = false;
    sn_obj_id_t f[3] = {SN_INVALID_ID, SN_INVALID_ID, SN_INVALID_ID};
    for (uint32_t i = 0; i < fanin_count && i < 3; i++)
        f[i] = sn_dff_rep(reps, sn_obj_fanin(module, object, i));

    // An equal-shape cast or a single-fanin concatenation is its operand.
    if ((type == SN_CAST || type == SN_CONCAT) && fanin_count == 1 && f[0] != SN_INVALID_ID &&
        sn_obj_width(module, f[0]) == width && sn_obj_is_signed(module, f[0]) == is_signed)
        return f[0];

    // A mux with a constant select is the selected branch.
    if (type == SN_MUX && f[0] != SN_INVALID_ID && sn_dff_const_like(sn_obj_type(module, f[0])))
    {
        sn_obj_id_t branch = sn_dff_const_is_zero(module, f[0]) ? f[SN_MUX_DEFAULT] : f[SN_MUX_SELECTED];
        if (branch != SN_INVALID_ID && sn_obj_width(module, branch) == width &&
            sn_obj_is_signed(module, branch) == is_signed)
            return branch;
    }

    // Bitwise identities of any width.
    if ((type == SN_BIT_AND || type == SN_BIT_OR) && fanin_count == 2)
        for (uint32_t i = 0; i < 2; i++)
        {
            sn_obj_id_t other = f[1 - i];
            if (f[i] == SN_INVALID_ID || other == SN_INVALID_ID ||
                !sn_dff_const_like(sn_obj_type(module, f[i])))
                continue;
            bool zero = sn_dff_const_is_zero(module, f[i]);
            bool ones = sn_obj_width(module, f[i]) == width && sn_dff_const_is_ones(module, f[i]);
            if (type == SN_BIT_AND && zero)
            {
                *build_const = true;
                *const_value = 0;
                return SN_INVALID_ID;
            }
            if (((type == SN_BIT_AND && ones) || (type == SN_BIT_OR && zero)) &&
                sn_obj_width(module, other) == width && sn_obj_is_signed(module, other) == is_signed)
                return other;
        }
    if (type == SN_LOG_AND || type == SN_LOG_OR)
        for (uint32_t i = 0; i < fanin_count && i < 3; i++)
        {
            if (f[i] == SN_INVALID_ID || !sn_dff_const_like(sn_obj_type(module, f[i])))
                continue;
            bool zero = sn_dff_const_is_zero(module, f[i]);
            if (type == SN_LOG_AND && zero)
            {
                *build_const = true;
                *const_value = 0;
                return SN_INVALID_ID;
            }
            if (type == SN_LOG_OR && !zero)
            {
                *build_const = true;
                *const_value = 1;
                return SN_INVALID_ID;
            }
            // A true operand of a two-input logical AND leaves the other
            // operand's truth value; forward it only when it is already the
            // one-bit result shape.
            sn_obj_id_t other = fanin_count == 2 ? f[1 - i] : SN_INVALID_ID;
            if (type == SN_LOG_AND && !zero && other != SN_INVALID_ID && width == 1 &&
                sn_obj_width(module, other) == 1 && sn_obj_is_signed(module, other) == is_signed)
                return other;
        }

    // Constant evaluation for common operators up to 64 bits.
    uint64_t a = 0, b = 0;
    uint32_t a_width = f[0] == SN_INVALID_ID ? 0 : sn_obj_width(module, f[0]);
    uint32_t b_width = f[1] == SN_INVALID_ID ? 0 : sn_obj_width(module, f[1]);
    bool a_const = f[0] != SN_INVALID_ID && sn_dff_const_value64(module, f[0], &a);
    bool b_const = f[1] != SN_INVALID_ID && sn_dff_const_value64(module, f[1], &b);
    uint64_t mask = width >= 64 ? ~UINT64_C(0) : (UINT64_C(1) << width) - 1;
    if (width <= 64 && fanin_count == 1 && a_const)
    {
        uint64_t extended = sn_dff_extend64(a, a_width, sn_obj_is_signed(module, f[0]));
        switch (type)
        {
            case SN_CAST:
                // A cast extends by the result's signedness, unlike other
                // width-defined operators.
                *const_value = sn_dff_extend64(a, a_width, is_signed) & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_BUF:
            case SN_POS:
                *const_value = extended & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_NEG:
                // Two's complement in modular arithmetic; negating INT64_MIN as a signed
                // integer would be undefined.
                *const_value = (UINT64_C(0) - extended) & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_BIT_NOT:
                *const_value = ~extended & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_LOG_NOT:
                *const_value = a == 0;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_REDUCE_OR:
                *const_value = a != 0;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_REDUCE_NOR:
                *const_value = a == 0;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_REDUCE_AND:
                *const_value = a_width && a == ((a_width >= 64) ? ~UINT64_C(0)
                                                                : (UINT64_C(1) << a_width) - 1);
                *build_const = true;
                return SN_INVALID_ID;
            default:
                break;
        }
    }
    if (width <= 64 && fanin_count == 2 && a_const && b_const && f[0] != SN_INVALID_ID &&
        f[1] != SN_INVALID_ID)
    {
        bool a_signed = sn_obj_is_signed(module, f[0]);
        bool b_signed = sn_obj_is_signed(module, f[1]);
        // Width-defined binary operators extend both operands with their
        // common signedness: signed only when both operands are signed.
        bool common_signed = a_signed && b_signed;
        uint64_t ax = sn_dff_extend64(a, a_width, common_signed);
        uint64_t bx = sn_dff_extend64(b, b_width, common_signed);
        switch (type)
        {
            case SN_ADD:
                *const_value = (ax + bx) & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_SUB:
                *const_value = (ax - bx) & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_MUL:
                *const_value = (ax * bx) & mask;
                *build_const = true;
                return SN_INVALID_ID;
            case SN_BIT_AND:
            case SN_BIT_OR:
            case SN_BIT_XOR:
                if (a_width == width && b_width == width)
                {
                    *const_value = (type == SN_BIT_AND ? (ax & bx) : type == SN_BIT_OR ? (ax | bx) : (ax ^ bx)) &
                                   mask;
                    *build_const = true;
                    return SN_INVALID_ID;
                }
                break;
            case SN_EQ:
            case SN_NE:
                if (a_width == b_width)
                {
                    *const_value = (type == SN_EQ) == (a == b);
                    *build_const = true;
                    return SN_INVALID_ID;
                }
                break;
            case SN_LT:
            case SN_LE:
            case SN_GT:
            case SN_GE:
                if (a_width == b_width && a_signed == b_signed)
                {
                    bool less = a_signed ? (int64_t)ax < (int64_t)bx : a < b;
                    bool equal = a == b;
                    bool result = type == SN_LT   ? less
                                  : type == SN_LE ? less || equal
                                  : type == SN_GT ? !less && !equal
                                                  : !less;
                    *const_value = result;
                    *build_const = true;
                    return SN_INVALID_ID;
                }
                break;
            default:
                break;
        }
    }
    // A shift by a constant zero is its value operand.
    if ((type == SN_SHL || type == SN_SHR || type == SN_ASHL || type == SN_ASHR) && fanin_count == 2 &&
        b_const && b == 0 && f[0] != SN_INVALID_ID && sn_obj_width(module, f[0]) == width &&
        sn_obj_is_signed(module, f[0]) == is_signed)
        return f[0];
    return SN_INVALID_ID;
}

// Computes representatives for one module. Returns true when anything can be
// replaced. Constant substitutes are appended to the module as fanin-free
// constant objects and recorded in added_consts; the caller copies them into
// the rebuilt module. The reps array must have room for original objects
// plus one appended constant per register.
static inline bool sn_dff_analyze_module(sn_module_t* module, const sn_dff_map_options_t* options,
                                         sn_obj_id_t* reps, size_t reps_capacity, sn_vec_t* added_consts,
                                         sn_dff_map_stats_t* stats)
{
    size_t original_count = module->obj_types.size;
    sn_vec_t order = sn_module_topo_order(module);
    uint8_t* zero_cache = original_count ? (uint8_t*)calloc(original_count, sizeof(uint8_t)) : NULL;
    uint32_t max_words = 1;
    for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        uint32_t words = sn_const_word_count(sn_obj_width(module, reg_out));
        max_words = words > max_words ? words : max_words;
    }
    uint32_t* value_words = (uint32_t*)malloc(max_words * sizeof(uint32_t));
    assert(value_words && (!original_count || zero_cache));
    (void)reps_capacity;

    sn_dff_hash_table_t table;
    sn_dff_hash_init(&table, original_count);

    bool anything = false;
    if (options->fold_constants && module->type_objects[SN_REG_OUT].size)
    {
        uint8_t* candidate = (uint8_t*)calloc(original_count, sizeof(uint8_t));
        assert(candidate);
        if (sn_dff_inductive_zero(module, &order, candidate))
            for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
            {
                sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
                if (!candidate[reg_out])
                    continue;
                uint32_t width = sn_obj_width(module, reg_out);
                for (uint32_t word = 0; word < sn_const_word_count(width); word++)
                    value_words[word] = 0;
                size_t before_count = module->obj_types.size;
                sn_obj_id_t constant =
                    sn_module_add_const(module, width, sn_obj_is_signed(module, reg_out), value_words, NULL);
                if (module->obj_types.size > before_count)
                {
                    assert(module->obj_types.size <= reps_capacity);
                    reps[constant] = constant;
                    *sn_vec_push(sn_obj_id_t, added_consts) = constant;
                }
                reps[reg_out] = constant;
                reps[sn_obj_pair_in(module, reg_out)] = constant;
                stats->const_regs++;
                anything = true;
            }
        free(candidate);
    }

    uint32_t round = 0;
    bool changed = true;
    while (changed && (options->max_rounds == 0 || round < options->max_rounds))
    {
        changed = false;
        round++;

        if (options->merge_logic)
        {
            sn_dff_hash_clear(&table);
            for (size_t i = 0; i < order.size; i++)
            {
                sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &order, i);
                if (sn_dff_rep(reps, object) != object)
                    continue;
                sn_obj_type_t type = sn_obj_type(module, object);
                if (!sn_dff_object_shareable(type))
                    continue;
                if (options->fold_constants && object < original_count)
                {
                    bool build_const = false;
                    uint64_t const_value = 0;
                    sn_obj_id_t folded = sn_dff_try_fold(module, object, reps, &build_const, &const_value);
                    if (build_const)
                    {
                        uint32_t width_bits = sn_obj_width(module, object);
                        uint32_t word_count = sn_const_word_count(width_bits);
                        uint32_t stack_words[8] = {0};
                        uint32_t* words =
                            word_count <= 8 ? stack_words : (uint32_t*)calloc(word_count, sizeof(uint32_t));
                        assert(words);
                        words[0] = (uint32_t)const_value;
                        if (word_count > 1)
                            words[1] = (uint32_t)(const_value >> 32);
                        uint32_t final_bits = width_bits & 31u;
                        if (final_bits)
                            words[word_count - 1] &= (1u << final_bits) - 1u;
                        size_t before_count = module->obj_types.size;
                        folded = sn_module_add_const(module, width_bits, sn_obj_is_signed(module, object),
                                                     words, NULL);
                        if (words != stack_words)
                            free(words);
                        if (module->obj_types.size > before_count)
                        {
                            assert(module->obj_types.size <= reps_capacity);
                            reps[folded] = folded;
                            *sn_vec_push(sn_obj_id_t, added_consts) = folded;
                        }
                    }
                    if (folded != SN_INVALID_ID && folded != object)
                    {
                        reps[object] = folded;
                        stats->merged_objects++;
                        changed = anything = true;
                        continue;
                    }
                }
                // An unnamed same-shape buffer forwards its fanin directly.
                if (type == SN_BUF && sn_obj_name_id(module, object) == SN_INVALID_ID)
                {
                    sn_obj_id_t fanin = sn_dff_rep(reps, sn_obj_fanin(module, object, 0));
                    if (fanin != SN_INVALID_ID && sn_obj_width(module, fanin) == sn_obj_width(module, object) &&
                        sn_obj_is_signed(module, fanin) == sn_obj_is_signed(module, object))
                    {
                        reps[object] = fanin;
                        stats->merged_objects++;
                        changed = anything = true;
                        continue;
                    }
                }
                uint64_t hash = sn_dff_object_signature(module, object, reps);
                sn_obj_id_t existing = sn_dff_hash_find_or_insert(&table, module, object, hash, reps, false);
                if (existing != object)
                {
                    reps[object] = existing;
                    stats->merged_objects++;
                    changed = anything = true;
                }
            }
        }

        if (options->fold_constants)
        {
            for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
            {
                sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
                if (sn_dff_rep(reps, reg_out) != reg_out)
                    continue;
                if (!sn_dff_reg_constant(module, reg_out, reps, zero_cache, value_words))
                    continue;
                size_t before_count = module->obj_types.size;
                sn_obj_id_t constant = sn_module_add_const(module, sn_obj_width(module, reg_out),
                                                           sn_obj_is_signed(module, reg_out), value_words, NULL);
                if (module->obj_types.size > before_count)
                {
                    assert(module->obj_types.size <= reps_capacity);
                    reps[constant] = constant;
                    *sn_vec_push(sn_obj_id_t, added_consts) = constant;
                }
                reps[reg_out] = constant;
                reps[sn_obj_pair_in(module, reg_out)] = constant;
                stats->const_regs++;
                changed = anything = true;
            }
        }

        if (options->merge_registers)
        {
            sn_dff_hash_clear(&table);
            for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
            {
                sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
                if (sn_dff_rep(reps, reg_out) != reg_out)
                    continue;
                uint64_t hash = sn_dff_reg_signature(module, reg_out, reps);
                sn_obj_id_t existing = sn_dff_hash_find_or_insert(&table, module, reg_out, hash, reps, true);
                if (existing != reg_out)
                {
                    reps[reg_out] = existing;
                    reps[sn_obj_pair_in(module, reg_out)] = sn_obj_pair_in(module, existing);
                    stats->merged_regs++;
                    changed = anything = true;
                }
            }
        }
    }

    sn_dff_hash_destroy(&table);
    free(value_words);
    free(zero_cache);
    sn_vec_destroy(&order);
    return anything;
}

// Rebuilds one module with representatives applied, then re-duplicates it in
// clean topological order so cones that lost their last fanout are swept.
// Mirrors the provisional/final identity dance of sn_design_map_tech.
static inline sn_module_id_t sn_design_opt_dff_module(sn_design_t* design, sn_module_id_t source_module_id,
                                                      const sn_dff_map_options_t* options, bool force_copy,
                                                      sn_dff_map_stats_t* stats)
{
    sn_module_t* source = sn_design_get_module(design, source_module_id);
    size_t original_count = source->obj_types.size;
    // Folding and register-constant substitution can each append at most one
    // constant per original object.
    size_t reps_capacity = 2 * original_count + source->type_objects[SN_REG_OUT].size + 2;
    sn_obj_id_t* reps = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * reps_capacity);
    assert(reps);
    for (size_t i = 0; i < reps_capacity; i++)
        reps[i] = (sn_obj_id_t)i;

    sn_vec_t added_consts;
    sn_vec_init(&added_consts);
    bool changed = sn_dff_analyze_module(source, options, reps, reps_capacity, &added_consts, stats);
    size_t object_count = source->obj_types.size;
    if (!changed && !force_copy)
    {
        free(reps);
        sn_vec_destroy(&added_consts);
        return source_module_id;
    }
    if (changed)
        stats->modules_changed++;

    const char* source_name = sn_name_get(&design->names, source->name);
    char mapped_name[256];
    int length = snprintf(mapped_name, sizeof(mapped_name), "%s_dffopt", source_name);
    assert(length >= 0 && (size_t)length < sizeof(mapped_name));
    for (uint32_t suffix = 1; sn_design_find_module(design, mapped_name) != SN_INVALID_ID; suffix++)
    {
        length = snprintf(mapped_name, sizeof(mapped_name), "%s_dffopt_%u", source_name, suffix);
        assert(length >= 0 && (size_t)length < sizeof(mapped_name));
    }
    sn_module_id_t mapped_id = sn_design_add_module(design, mapped_name);
    sn_module_t* mapped = sn_design_get_module(design, mapped_id);
    sn_vec_t order = sn_module_topo_order(source);
    sn_vec_resize(sn_obj_id_t, &source->copy_ids, object_count);
    for (size_t i = 0; i < object_count; i++)
        sn_vec_at(sn_obj_id_t, &source->copy_ids, i) = SN_INVALID_ID;

    // Copy skeletons for representatives only: the PI prefix, then appended
    // constants (which the analysis created after the topological order was
    // taken), then the remaining representatives in topological order.
    size_t pi_count = source->type_objects[SN_PI].size;
    for (size_t i = 0; i < pi_count; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) =
            sn_module_dup_obj_skeleton(mapped, source, old_object);
    }
    for (size_t k = 0; k < added_consts.size; k++)
    {
        sn_obj_id_t constant = sn_vec_at(sn_obj_id_t, &added_consts, k);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, constant) =
            sn_module_dup_obj_skeleton(mapped, source, constant);
    }
    for (size_t i = pi_count; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        if (sn_dff_rep(reps, old_object) != old_object)
            continue;
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) =
            sn_module_dup_obj_skeleton(mapped, source, old_object);
    }
    sn_module_order_pairs_by_source(mapped, source);

    // Metadata and fanins for the copied representatives, with every fanin
    // resolved through its representative's copy. Appended constants carry
    // only their constant-word metadata.
    for (size_t k = 0; k < added_consts.size; k++)
    {
        sn_obj_id_t constant = sn_vec_at(sn_obj_id_t, &added_consts, k);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, constant);
        sn_module_dup_obj_metadata(mapped, new_object, source, constant);
    }
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        if (new_object == SN_INVALID_ID)
            continue;
        sn_module_dup_obj_metadata(mapped, new_object, source, old_object);
        for (uint32_t j = 0; j < sn_obj_fanin_count(source, old_object); j++)
        {
            sn_obj_id_t old_fanin = sn_obj_fanin(source, old_object, j);
            sn_obj_id_t new_fanin = SN_INVALID_ID;
            if (old_fanin != SN_INVALID_ID)
            {
                new_fanin = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_dff_rep(reps, old_fanin));
                assert(new_fanin != SN_INVALID_ID);
            }
            sn_obj_connect(mapped, new_object, j, new_fanin);
        }
    }
    sn_module_link_pairs(mapped);
    // Merged objects map to their representative's copy so the composed copy
    // map stays valid for callers.
    for (size_t i = 0; i < object_count; i++)
    {
        sn_obj_id_t root = sn_dff_rep(reps, (sn_obj_id_t)i);
        if (root != (sn_obj_id_t)i)
            sn_vec_at(sn_obj_id_t, &source->copy_ids, i) = sn_vec_at(sn_obj_id_t, &source->copy_ids, root);
    }

    // Sweep cones that lost their last fanout. Modules with ordering
    // boundaries keep a plain topological duplicate: the conservative
    // instance-dependency traversal of the clean pass can see an artificial
    // cycle through a loop breaker.
    char temporary_name[96];
    uint32_t temporary_suffix = 0;
    do
    {
        length = snprintf(temporary_name, sizeof(temporary_name), "__sn_dff_topo_%u_%u", mapped_id,
                          temporary_suffix++);
        assert(length >= 0 && (size_t)length < sizeof(temporary_name) && temporary_suffix != 0);
    } while (sn_name_find(&design->names, temporary_name) != SN_INVALID_ID);
    sn_module_id_t final_id = mapped->type_objects[SN_LOOP_OUT].size
                                  ? sn_design_dup_module_topo(design, mapped_id, temporary_name)
                                  : sn_design_dup_module_clean_topo(design, mapped_id, temporary_name);
    assert(final_id + 1 == design->modules.size);
    sn_module_t* provisional = sn_design_get_module(design, mapped_id);
    sn_module_t* final_module = sn_design_get_module(design, final_id);
    sn_name_id_t temporary_name_id = final_module->name;
    for (size_t i = 0; i < source->copy_ids.size; i++)
    {
        sn_obj_id_t provisional_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, i);
        if (provisional_object != SN_INVALID_ID)
            sn_vec_at(sn_obj_id_t, &source->copy_ids, i) =
                sn_vec_at(sn_obj_id_t, &provisional->copy_ids, provisional_object);
    }
    sn_name_id_t mapped_name_id = provisional->name;
    bool interface_locked = provisional->interface_locked;
    sn_design_invalidate_copies_to_module_except(design, mapped_id, source);
    sn_module_destroy(provisional);
    free(provisional);
    final_module->id = mapped_id;
    final_module->name = mapped_name_id;
    final_module->interface_locked = interface_locked;
    sn_vec_at(sn_module_t*, &design->modules, mapped_id) = final_module;
    design->modules.size--;
    sn_name_remove_last(&design->names, temporary_name_id);
    source->copy_module = mapped_id;
    assert(sn_module_is_topo(final_module));

    // Analysis appends fresh constants to the source module after its PO
    // suffix; restore the source's canonical order so the retained original
    // definition stays legal.
    if (added_consts.size)
        sn_design_reorder_module_topo(design, source_module_id);

    free(reps);
    sn_vec_destroy(&order);
    sn_vec_destroy(&added_consts);
    return mapped_id;
}

static inline void sn_dff_count_regs(const sn_design_t* design, sn_module_id_t root, size_t* regs,
                                     size_t* reg_bits)
{
    size_t module_count = design->modules.size;
    uint8_t* seen = (uint8_t*)calloc(module_count, 1);
    sn_vec_t stack;
    assert(seen);
    sn_vec_init(&stack);
    *sn_vec_push(sn_module_id_t, &stack) = root;
    seen[root] = 1;
    *regs = 0;
    *reg_bits = 0;
    while (stack.size)
    {
        sn_module_id_t id = sn_vec_at(sn_module_id_t, &stack, --stack.size);
        const sn_module_t* module = sn_design_get_module_const(design, id);
        for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
        {
            sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
            (*regs)++;
            *reg_bits += sn_obj_width(module, reg_out);
        }
        for (size_t i = 0; i < module->type_objects[SN_INST].size; i++)
        {
            sn_module_id_t child = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i));
            if (!seen[child])
            {
                seen[child] = 1;
                *sn_vec_push(sn_module_id_t, &stack) = child;
            }
        }
    }
    sn_vec_destroy(&stack);
    free(seen);
}

typedef struct sn_dff_hierarchy_frame_t
{
    sn_module_id_t module;
    size_t next_inst;
} sn_dff_hierarchy_frame_t;

// Visits the reachable hierarchy bottom-up, exactly like technology mapping:
// a module is rebuilt when it contains an optimization opportunity or when a
// child definition changed and its instance references must be redirected.
static inline sn_module_id_t sn_design_opt_dff_hierarchy(sn_design_t* design, sn_module_id_t top_id,
                                                         const sn_dff_map_options_t* options,
                                                         sn_dff_map_stats_t* returned_stats)
{
    assert(design && top_id < design->modules.size && options);
    sn_dff_map_stats_t stats = {0};
    sn_dff_count_regs(design, top_id, &stats.regs_before, &stats.reg_bits_before);

    size_t original_count = design->modules.size;
    sn_module_id_t* replacements = (sn_module_id_t*)malloc(sizeof(sn_module_id_t) * original_count);
    uint8_t* states = (uint8_t*)calloc(original_count, sizeof(uint8_t));
    sn_vec_t stack, postorder;
    assert(replacements && states);
    for (sn_module_id_t id = 0; id < original_count; id++)
        replacements[id] = id;
    sn_vec_init(&stack);
    sn_vec_init(&postorder);
    states[top_id] = 1;
    sn_dff_hierarchy_frame_t* root = sn_vec_push(sn_dff_hierarchy_frame_t, &stack);
    root->module = top_id;
    root->next_inst = 0;
    while (stack.size)
    {
        sn_dff_hierarchy_frame_t* frame = &sn_vec_at(sn_dff_hierarchy_frame_t, &stack, stack.size - 1);
        const sn_module_t* module = sn_design_get_module_const(design, frame->module);
        if (frame->next_inst < module->type_objects[SN_INST].size)
        {
            sn_module_id_t child = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], frame->next_inst++));
            assert(child < original_count);
            assert(states[child] != 1 && "recursive module instantiation is unsupported");
            if (states[child] == 0)
            {
                states[child] = 1;
                sn_dff_hierarchy_frame_t* child_frame = sn_vec_push(sn_dff_hierarchy_frame_t, &stack);
                child_frame->module = child;
                child_frame->next_inst = 0;
            }
            continue;
        }
        states[frame->module] = 2;
        *sn_vec_push(sn_module_id_t, &postorder) = frame->module;
        stack.size--;
    }

    for (size_t order = 0; order < postorder.size; order++)
    {
        sn_module_id_t id = sn_vec_at(sn_module_id_t, &postorder, order);
        const sn_module_t* module = sn_design_get_module_const(design, id);
        if (sn_module_is_technology_primitive(module))
            continue;
        bool child_changed = false;
        for (size_t i = 0; i < module->type_objects[SN_INST].size; i++)
        {
            sn_module_id_t child = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i));
            child_changed |= replacements[child] != child;
        }
        replacements[id] = sn_design_opt_dff_module(design, id, options, child_changed, &stats);
        if (replacements[id] == id)
            continue;
        sn_module_t* mapped = sn_design_get_module(design, replacements[id]);
        for (size_t i = 0; i < mapped->type_objects[SN_INST].size; i++)
        {
            sn_module_id_t child = sn_inst_module_id(mapped, sn_vec_at(sn_obj_id_t, &mapped->type_objects[SN_INST], i));
            if (child < original_count)
                sn_obj_set_data(mapped, sn_vec_at(sn_obj_id_t, &mapped->type_objects[SN_INST], i), replacements[child]);
        }
    }

    sn_module_id_t result = replacements[top_id];
    sn_dff_count_regs(design, result, &stats.regs_after, &stats.reg_bits_after);
    sn_vec_destroy(&postorder);
    sn_vec_destroy(&stack);
    free(states);
    free(replacements);
    if (returned_stats)
        *returned_stats = stats;
    return result;
}

ABC_NAMESPACE_HEADER_END

#endif
