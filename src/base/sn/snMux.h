/**CFile****************************************************************

  FileName    [snMux.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Mux-path sharing and restructuring for word-level SN designs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMux.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MUX_H
#define SN_MUX_H

// Word-level mux-path sharing for register-fed SN_MUX trees and nested SN_PMUX objects. Root-to-terminal paths are
// enumerated, structurally equal LSB-first words are represented once, and their path conditions are ORed. A hold
// terminal is moved into SN_REG_ENABLE when controls are provably exclusive. General PMUX alternatives preserve SN's
// one-hot-select semantics; as for SN_PMUX itself, behavior for multi-hot selects is unspecified. Modules are
// duplicated and rewritten transactionally; hierarchy, stable module IDs, and the complete canonical register
// interface are preserved.

#include "sn.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

ABC_NAMESPACE_HEADER_START

typedef struct sn_share_options_t
{
    uint32_t min_width;
    uint32_t min_alternatives;
    uint32_t min_saved_paths;
} sn_share_options_t;

typedef struct sn_share_stats_t
{
    uint64_t modules;
    uint64_t registers;
    uint64_t muxes;
    uint64_t paths_before;
    uint64_t paths_after;
} sn_share_stats_t;

typedef struct sn_share_step_t
{
    sn_obj_id_t select;
    uint32_t bit;
    bool positive;
} sn_share_step_t;

typedef struct sn_share_path_t
{
    sn_obj_id_t term;
    uint32_t step_offset;
    uint32_t step_count;
    uint32_t group;
} sn_share_path_t;

enum
{
    SN_SHARE_MAX_PATHS = 1 << 20,
    SN_SHARE_MAX_DEPTH = 4096,
    SN_SHARE_MAX_STEPS = 1 << 24
};

static inline sn_share_options_t sn_share_default_options(void)
{
    sn_share_options_t options = {4, 6, 2};
    return options;
}

static inline sn_obj_id_t sn_share_strip_value(const sn_module_t* module, sn_obj_id_t object)
{
    while (object != SN_INVALID_ID)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if ((type != SN_BUF && type != SN_POS && type != SN_CAST) || sn_obj_fanin_count(module, object) != 1 ||
            sn_obj_width(module, object) != sn_obj_width(module, sn_obj_fanin(module, object, 0)))
            break;
        object = sn_obj_fanin(module, object, 0);
    }
    return object;
}

static inline bool sn_share_const_equal(const sn_module_t* module, sn_obj_id_t a, sn_obj_id_t b)
{
    if (sn_obj_width(module, a) != sn_obj_width(module, b))
        return false;
    sn_obj_type_t ta = sn_obj_type(module, a), tb = sn_obj_type(module, b);
    if ((ta != SN_CONST0 && ta != SN_CONST1 && ta != SN_CONST) ||
        (tb != SN_CONST0 && tb != SN_CONST1 && tb != SN_CONST))
        return false;
    uint32_t width = sn_obj_width(module, a);
    for (uint32_t bit = 0; bit < width; bit++)
    {
        bool av = (ta == SN_CONST1 && bit == 0) ||
                  (ta == SN_CONST && ((sn_const_words(module, a)[bit >> 5] >> (bit & 31)) & 1));
        bool bv = (tb == SN_CONST1 && bit == 0) ||
                  (tb == SN_CONST && ((sn_const_words(module, b)[bit >> 5] >> (bit & 31)) & 1));
        if (av != bv)
            return false;
    }
    return true;
}

// Returns the unique raw selector value accepted by an equality comparison,
// accounting for the comparison's signed extension. A wider constant whose
// high bits cannot equal the extended selector makes the predicate impossible.
static inline bool sn_share_decode_value(const sn_module_t* module, sn_obj_id_t value,
                                         sn_obj_id_t constant, uint32_t* decoded)
{
    uint32_t value_width = sn_obj_width(module, value);
    uint32_t constant_width = sn_obj_width(module, constant);
    bool sign = sn_obj_is_signed(module, value) && sn_obj_is_signed(module, constant);
    if (!value_width || value_width >= 31)
        return false;
    uint32_t result = 0;
    for (uint32_t bit = 0; bit < value_width; bit++)
    {
        bool constant_bit = bit < constant_width ? sn_const_bit(module, constant, bit)
                                                 : sign && sn_const_bit(module, constant, constant_width - 1);
        result |= (uint32_t)constant_bit << bit;
    }
    if (constant_width > value_width)
    {
        bool extension = sign && ((result >> (value_width - 1)) & 1);
        for (uint32_t bit = value_width; bit < constant_width; bit++)
            if (sn_const_bit(module, constant, bit) != extension)
                return false;
    }
    *decoded = result;
    return true;
}

// Structural word identity through the inexpensive wiring operators used heavily by Slang lowering. This is the
// object-level counterpart of UtilMux's canonical bit-vector IDs: separately-created slices/concatenations of the
// same LSB-first source bits are recognized as the same mux terminal without bit-blasting the module.
static inline bool sn_share_value_equal(const sn_module_t* module, sn_obj_id_t a, sn_obj_id_t b)
{
    a = sn_share_strip_value(module, a);
    b = sn_share_strip_value(module, b);
    if (a == b)
        return true;
    if (sn_obj_width(module, a) != sn_obj_width(module, b))
        return false;
    sn_obj_type_t ta = sn_obj_type(module, a), tb = sn_obj_type(module, b);
    if ((ta == SN_CONST0 || ta == SN_CONST1 || ta == SN_CONST) &&
        (tb == SN_CONST0 || tb == SN_CONST1 || tb == SN_CONST))
        return sn_share_const_equal(module, a, b);
    if (ta != tb)
        return false;
    if (ta == SN_SLICE)
    {
        const sn_slice_info_t* ia = sn_obj_slice_info(module, a);
        const sn_slice_info_t* ib = sn_obj_slice_info(module, b);
        return ia->left_index == ib->left_index && ia->right_index == ib->right_index &&
               sn_share_value_equal(module, sn_obj_fanin(module, a, 0), sn_obj_fanin(module, b, 0));
    }
    if (ta == SN_REPLICATE)
        return sn_obj_repeat_count(module, a) == sn_obj_repeat_count(module, b) &&
               sn_share_value_equal(module, sn_obj_fanin(module, a, 0), sn_obj_fanin(module, b, 0));
    if (ta == SN_CONCAT && sn_obj_fanin_count(module, a) == sn_obj_fanin_count(module, b))
    {
        for (uint32_t i = 0; i < sn_obj_fanin_count(module, a); i++)
            if (!sn_share_value_equal(module, sn_obj_fanin(module, a, i), sn_obj_fanin(module, b, i)))
                return false;
        return true;
    }
    return false;
}

static inline uint64_t sn_share_hash_mix(uint64_t hash, uint64_t value)
{
    hash ^= value;
    return hash * UINT64_C(1099511628211);
}

// Compute structural hashes for the inexpensive wiring words recognized by sn_share_value_equal(). Modules entering
// @opt_mux are topologically ordered, so every hashed wiring fanin is already available. Unsupported terminals retain
// object identity. Hash collisions are always resolved with the exact structural comparison.
static inline uint64_t* sn_share_value_hashes(const sn_module_t* module)
{
    uint64_t* hashes = (uint64_t*)calloc(module->obj_types.size, sizeof(uint64_t));
    assert(hashes || module->obj_types.size == 0);
    for (sn_obj_id_t object = 0; object < module->obj_types.size; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        uint64_t hash = sn_share_hash_mix(UINT64_C(1469598103934665603), sn_obj_width(module, object));
        if (type == SN_BUF || type == SN_POS || type == SN_CAST)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, object, 0);
            hashes[object] = sn_obj_width(module, object) == sn_obj_width(module, fanin)
                                 ? hashes[fanin] : sn_share_hash_mix(hash, object);
            continue;
        }
        if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
        {
            uint32_t count = sn_const_word_count(sn_obj_width(module, object));
            for (uint32_t i = 0; i < count; i++)
            {
                uint32_t word = type == SN_CONST ? sn_const_words(module, object)[i]
                                                 : type == SN_CONST1 && i == 0 ? 1 : 0;
                if (i + 1 == count && (sn_obj_width(module, object) & 31))
                    word &= (UINT32_C(1) << (sn_obj_width(module, object) & 31)) - 1;
                hash = sn_share_hash_mix(hash, word);
            }
            hashes[object] = hash;
            continue;
        }
        hash = sn_share_hash_mix(hash, type);
        if (type == SN_SLICE)
        {
            const sn_slice_info_t* info = sn_obj_slice_info(module, object);
            hash = sn_share_hash_mix(hash, (uint32_t)info->left_index);
            hash = sn_share_hash_mix(hash, (uint32_t)info->right_index);
            hash = sn_share_hash_mix(hash, hashes[sn_obj_fanin(module, object, 0)]);
        }
        else if (type == SN_REPLICATE)
        {
            hash = sn_share_hash_mix(hash, sn_obj_repeat_count(module, object));
            hash = sn_share_hash_mix(hash, hashes[sn_obj_fanin(module, object, 0)]);
        }
        else if (type == SN_CONCAT)
            for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
                hash = sn_share_hash_mix(hash, hashes[sn_obj_fanin(module, object, i)]);
        else
            hash = sn_share_hash_mix(hash, object);
        hashes[object] = hash;
    }
    return hashes;
}

static inline bool sn_share_hashed_equal(const sn_module_t* module, const uint64_t* hashes,
                                         sn_obj_id_t a, sn_obj_id_t b)
{
    a = sn_share_strip_value(module, a);
    b = sn_share_strip_value(module, b);
    return hashes[a] == hashes[b] && sn_share_value_equal(module, a, b);
}

// Recognize a binary decode. The equality predicates compare one common selector against distinct constants, so at
// most one PMUX select bit is true and ordinary combinational CEC is valid. An incomplete decode uses the PMUX default.
static inline bool sn_share_select_is_decode(const sn_module_t* module, sn_obj_id_t select)
{
    if (sn_obj_type(module, select) != SN_CONCAT || sn_obj_fanin_count(module, select) < 2)
        return false;
    sn_obj_id_t common = SN_INVALID_ID;
    sn_vec_t decoded_values;
    sn_vec_init(&decoded_values);
    for (uint32_t i = 0; i < sn_obj_fanin_count(module, select); i++)
    {
        sn_obj_id_t compare = sn_obj_fanin(module, select, i);
        sn_obj_type_t type = sn_obj_type(module, compare);
        if ((type != SN_EQ && type != SN_CASE_EQ) || sn_obj_fanin_count(module, compare) != 2)
        {
            sn_vec_destroy(&decoded_values);
            return false;
        }
        sn_obj_id_t value = sn_obj_fanin(module, compare, 0), constant = sn_obj_fanin(module, compare, 1);
        sn_obj_type_t constant_type = sn_obj_type(module, constant);
        if (constant_type != SN_CONST0 && constant_type != SN_CONST1 && constant_type != SN_CONST)
        {
            sn_vec_destroy(&decoded_values);
            return false;
        }
        if (common == SN_INVALID_ID)
            common = value;
        else if (sn_share_strip_value(module, value) != sn_share_strip_value(module, common) ||
                 sn_obj_width(module, value) != sn_obj_width(module, common) ||
                 sn_obj_is_signed(module, value) != sn_obj_is_signed(module, common))
        {
            sn_vec_destroy(&decoded_values);
            return false;
        }
        uint32_t decoded;
        if (!sn_share_decode_value(module, value, constant, &decoded))
            continue;
        for (size_t j = 0; j < decoded_values.size; j++)
            if (sn_vec_at(uint32_t, &decoded_values, j) == decoded)
            {
                sn_vec_destroy(&decoded_values);
                return false;
            }
        *sn_vec_push(uint32_t, &decoded_values) = decoded;
    }
    uint32_t width = sn_obj_width(module, common);
    bool result = width < 31 && sn_obj_fanin_count(module, select) <= (UINT32_C(1) << width);
    sn_vec_destroy(&decoded_values);
    return result;
}

static inline bool sn_share_pmux_words(const sn_module_t* module, sn_obj_id_t pmux, sn_vec_t* words)
{
    assert(sn_obj_type(module, pmux) == SN_PMUX);
    sn_obj_id_t select = sn_obj_fanin(module, pmux, SN_PMUX_SELECT);
    sn_obj_id_t packed = sn_obj_fanin(module, pmux, SN_PMUX_ALTERNATIVES);
    uint32_t count = sn_obj_width(module, select), width = sn_obj_width(module, pmux);
    sn_vec_init(words);
    if (sn_obj_type(module, packed) != SN_CONCAT || sn_obj_fanin_count(module, packed) != count)
        return false;
    sn_vec_reserve(sn_obj_id_t, words, count);
    for (uint32_t i = 0; i < count; i++)
    {
        sn_obj_id_t word = sn_obj_fanin(module, packed, i);
        if (sn_obj_width(module, word) != width)
        {
            sn_vec_destroy(words);
            sn_vec_init(words);
            return false;
        }
        *sn_vec_push(sn_obj_id_t, words) = sn_share_strip_value(module, word);
    }
    return true;
}

static inline sn_obj_id_t sn_share_or(sn_module_t* module, const sn_obj_id_t* values, uint32_t count)
{
    assert(count);
    if (count == 1)
        return values[0];
    sn_vec_t level, next;
    sn_vec_init(&level);
    sn_vec_init(&next);
    sn_vec_reserve(sn_obj_id_t, &level, count);
    for (uint32_t i = 0; i < count; i++)
        *sn_vec_push(sn_obj_id_t, &level) = values[i];
    while (level.size > 1)
    {
        next.size = 0;
        for (size_t i = 0; i < level.size; i += 2)
        {
            if (i + 1 == level.size)
                *sn_vec_push(sn_obj_id_t, &next) = sn_vec_at(sn_obj_id_t, &level, i);
            else
            {
                sn_obj_id_t fanins[2] = {sn_vec_at(sn_obj_id_t, &level, i),
                                         sn_vec_at(sn_obj_id_t, &level, i + 1)};
                *sn_vec_push(sn_obj_id_t, &next) =
                    sn_module_add_operator(module, SN_BIT_OR, 1, false, 2, fanins, NULL);
            }
        }
        sn_vec_t swap = level;
        level = next;
        next = swap;
    }
    sn_obj_id_t result = sn_vec_at(sn_obj_id_t, &level, 0);
    sn_vec_destroy(&level);
    sn_vec_destroy(&next);
    return result;
}

static inline sn_obj_id_t sn_share_and(sn_module_t* module, const sn_obj_id_t* values, uint32_t count)
{
    assert(count);
    if (count == 1)
        return values[0];
    sn_vec_t level, next;
    sn_vec_init(&level);
    sn_vec_init(&next);
    for (uint32_t i = 0; i < count; i++)
        *sn_vec_push(sn_obj_id_t, &level) = values[i];
    while (level.size > 1)
    {
        next.size = 0;
        for (size_t i = 0; i < level.size; i += 2)
        {
            if (i + 1 == level.size)
                *sn_vec_push(sn_obj_id_t, &next) = sn_vec_at(sn_obj_id_t, &level, i);
            else
            {
                sn_obj_id_t fanins[2] = {sn_vec_at(sn_obj_id_t, &level, i),
                                         sn_vec_at(sn_obj_id_t, &level, i + 1)};
                *sn_vec_push(sn_obj_id_t, &next) =
                    sn_module_add_operator(module, SN_BIT_AND, 1, false, 2, fanins, NULL);
            }
        }
        sn_vec_t swap = level;
        level = next;
        next = swap;
    }
    sn_obj_id_t result = sn_vec_at(sn_obj_id_t, &level, 0);
    sn_vec_destroy(&level);
    sn_vec_destroy(&next);
    return result;
}

static inline void sn_share_collect_mux_paths(const sn_module_t* module, sn_obj_id_t object, sn_vec_t* stack,
                                              sn_vec_t* steps, sn_vec_t* paths, uint8_t* active, bool* exclusive,
                                              bool* overflow)
{
    if (*overflow)
        return;
    if (stack->size >= SN_SHARE_MAX_DEPTH || paths->size >= SN_SHARE_MAX_PATHS ||
        steps->size > SN_SHARE_MAX_STEPS - stack->size)
    {
        *overflow = true;
        return;
    }
    object = sn_share_strip_value(module, object);
    if (sn_obj_type(module, object) == SN_MUX && !active[object])
    {
        active[object] = 1;
        sn_share_step_t* step = sn_vec_push(sn_share_step_t, stack);
        step->select = sn_obj_fanin(module, object, SN_MUX_SELECT);
        step->bit = 0;
        step->positive = true;
        sn_share_collect_mux_paths(module, sn_obj_fanin(module, object, SN_MUX_SELECTED), stack, steps, paths,
                                   active, exclusive, overflow);
        sn_vec_at(sn_share_step_t, stack, stack->size - 1).positive = false;
        sn_share_collect_mux_paths(module, sn_obj_fanin(module, object, SN_MUX_DEFAULT), stack, steps, paths,
                                   active, exclusive, overflow);
        stack->size--;
        active[object] = 0;
        return;
    }
    if (sn_obj_type(module, object) == SN_PMUX && !active[object])
    {
        sn_obj_id_t select = sn_obj_fanin(module, object, SN_PMUX_SELECT);
        sn_vec_t words;
        sn_vec_init(&words);
        if (sn_share_pmux_words(module, object, &words))
        {
            if (!sn_share_select_is_decode(module, select))
                *exclusive = false;
            active[object] = 1;
            for (uint32_t i = 0; i < words.size; i++)
            {
                sn_share_step_t* step = sn_vec_push(sn_share_step_t, stack);
                step->select = select;
                step->bit = i;
                step->positive = true;
                sn_share_collect_mux_paths(module, sn_vec_at(sn_obj_id_t, &words, i), stack, steps, paths, active,
                                           exclusive, overflow);
                stack->size--;
            }
            size_t old_stack_size = stack->size;
            for (uint32_t i = 0; i < words.size; i++)
            {
                sn_share_step_t* step = sn_vec_push(sn_share_step_t, stack);
                step->select = select;
                step->bit = i;
                step->positive = false;
            }
            sn_share_collect_mux_paths(module, sn_obj_fanin(module, object, SN_PMUX_DEFAULT), stack, steps, paths,
                                       active, exclusive, overflow);
            stack->size = old_stack_size;
            active[object] = 0;
            sn_vec_destroy(&words);
            return;
        }
        sn_vec_destroy(&words);
    }
    assert(steps->size <= UINT32_MAX && stack->size <= UINT32_MAX);
    sn_share_path_t* path = sn_vec_push(sn_share_path_t, paths);
    path->term = object;
    path->step_offset = (uint32_t)steps->size;
    path->step_count = (uint32_t)stack->size;
    path->group = SN_INVALID_ID;
    sn_vec_reserve(sn_share_step_t, steps, steps->size + stack->size);
    for (size_t i = 0; i < stack->size; i++)
        *sn_vec_push(sn_share_step_t, steps) = sn_vec_at(sn_share_step_t, stack, i);
}

static inline sn_obj_id_t sn_share_path_condition(sn_module_t* target, const sn_module_t* source,
                                                   const sn_share_path_t* path, const sn_vec_t* steps)
{
    sn_vec_t literals;
    sn_vec_init(&literals);
    for (uint32_t i = 0; i < path->step_count; i++)
    {
        sn_share_step_t step = sn_vec_at(sn_share_step_t, steps, path->step_offset + i);
        sn_obj_id_t literal = sn_obj_dup(source, step.select);
        if (sn_obj_width(target, literal) != 1)
            literal = sn_module_add_slice(target, literal, (int32_t)step.bit, (int32_t)step.bit, NULL);
        if (!step.positive)
            literal = sn_module_add_operator(target, SN_LOG_NOT, 1, false, 1, &literal, NULL);
        *sn_vec_push(sn_obj_id_t, &literals) = literal;
    }
    sn_obj_id_t result = sn_share_and(target, sn_vec_data(sn_obj_id_t, &literals), (uint32_t)literals.size);
    sn_vec_destroy(&literals);
    return result;
}

static inline bool sn_share_reg_mux_tree(sn_module_t* target, const sn_module_t* source, sn_obj_id_t old_reg,
                                         const uint64_t* hashes, sn_share_options_t options, sn_share_stats_t* stats)
{
    sn_obj_id_t old_in = sn_obj_pair_in(source, old_reg);
    sn_obj_id_t old_root = sn_obj_fanin(source, old_in, 0);
    if (old_root == SN_INVALID_ID || sn_obj_type(source, sn_share_strip_value(source, old_root)) != SN_MUX)
        return false;
    if (sn_obj_width(source, old_reg) < options.min_width)
        return false;
    sn_vec_t stack, steps, paths, terms, term_hashes, term_links, data_terms, controls;
    sn_obj_id_t hold = SN_INVALID_ID, data = SN_INVALID_ID, new_reg = SN_INVALID_ID;
    uint32_t* term_buckets = NULL;
    uint32_t* group_heads = NULL;
    uint32_t* path_links = NULL;
    uint32_t term_bucket_count = 0;
    size_t hold_index = 0;
    bool exclusive = true, overflow = false;
    sn_vec_init(&stack);
    sn_vec_init(&steps);
    sn_vec_init(&paths);
    sn_vec_init(&terms);
    sn_vec_init(&term_hashes);
    sn_vec_init(&term_links);
    sn_vec_init(&data_terms);
    sn_vec_init(&controls);
    uint8_t* active = (uint8_t*)calloc(source->obj_types.size, sizeof(uint8_t));
    assert(active);
    sn_share_collect_mux_paths(source, old_root, &stack, &steps, &paths, active, &exclusive, &overflow);
    free(active);
    if (overflow)
        goto unchanged;
    if (paths.size < options.min_alternatives)
        goto unchanged;
    term_bucket_count = 1;
    while (term_bucket_count < 2 * paths.size)
        term_bucket_count <<= 1;
    term_buckets = (uint32_t*)malloc((size_t)term_bucket_count * sizeof(uint32_t));
    assert(term_buckets);
    memset(term_buckets, 0xff, (size_t)term_bucket_count * sizeof(uint32_t));
    for (size_t i = 0; i < paths.size; i++)
    {
        sn_share_path_t* path = &sn_vec_at(sn_share_path_t, &paths, i);
        sn_obj_id_t term = path->term;
        uint64_t term_hash = hashes[sn_share_strip_value(source, term)];
        uint32_t bucket = (uint32_t)term_hash & (term_bucket_count - 1);
        uint32_t k;
        for (k = term_buckets[bucket]; k != SN_INVALID_ID; k = sn_vec_at(uint32_t, &term_links, k))
            if (sn_vec_at(uint64_t, &term_hashes, k) == term_hash &&
                sn_share_value_equal(source, sn_vec_at(sn_obj_id_t, &terms, k), term))
                break;
        if (k == SN_INVALID_ID)
        {
            k = (uint32_t)terms.size;
            *sn_vec_push(sn_obj_id_t, &terms) = term;
            *sn_vec_push(uint64_t, &term_hashes) = term_hash;
            *sn_vec_push(uint32_t, &term_links) = term_buckets[bucket];
            term_buckets[bucket] = k;
        }
        path->group = k;
    }
    if (paths.size <= terms.size || paths.size - terms.size < options.min_saved_paths || paths.size < 2 * terms.size)
        goto unchanged;
    group_heads = (uint32_t*)malloc(terms.size * sizeof(uint32_t));
    path_links = (uint32_t*)malloc(paths.size * sizeof(uint32_t));
    assert(group_heads && path_links);
    for (size_t k = 0; k < terms.size; k++)
        group_heads[k] = SN_INVALID_ID;
    for (size_t i = 0; i < paths.size; i++)
    {
        uint32_t group = sn_vec_at(sn_share_path_t, &paths, i).group;
        assert(group < terms.size);
        path_links[i] = group_heads[group];
        group_heads[group] = (uint32_t)i;
    }

    hold = sn_share_strip_value(source, old_reg);
    hold_index = terms.size;
    if (exclusive)
        for (size_t k = 0; k < terms.size; k++)
            if (sn_share_hashed_equal(source, hashes, sn_vec_at(sn_obj_id_t, &terms, k), hold))
                hold_index = k;
    for (size_t k = 0; k < terms.size; k++)
    {
        if (k == hold_index)
            continue;
        sn_vec_t cubes;
        sn_vec_init(&cubes);
        for (uint32_t i = group_heads[k]; i != SN_INVALID_ID; i = path_links[i])
        {
            sn_share_path_t* path = &sn_vec_at(sn_share_path_t, &paths, i);
            *sn_vec_push(sn_obj_id_t, &cubes) = sn_share_path_condition(target, source, path, &steps);
        }
        *sn_vec_push(sn_obj_id_t, &controls) =
            sn_share_or(target, sn_vec_data(sn_obj_id_t, &cubes), (uint32_t)cubes.size);
        *sn_vec_push(sn_obj_id_t, &data_terms) = sn_obj_dup(source, sn_vec_at(sn_obj_id_t, &terms, k));
        sn_vec_destroy(&cubes);
    }
    if (!data_terms.size)
    {
        goto unchanged;
    }
    data = sn_vec_at(sn_obj_id_t, &data_terms, data_terms.size - 1);
    if (data_terms.size > 1)
    {
        sn_obj_id_t packed_select =
            sn_module_add_concat(target, (uint32_t)controls.size, sn_vec_data(sn_obj_id_t, &controls), NULL);
        sn_obj_id_t packed_data =
            sn_module_add_concat(target, (uint32_t)data_terms.size, sn_vec_data(sn_obj_id_t, &data_terms), NULL);
        data = sn_module_add_pmux(target, packed_select, packed_data, data, NULL);
    }
    new_reg = sn_obj_dup(source, old_reg);
    sn_obj_connect(target, sn_obj_pair_in(target, new_reg), 0, data);
    if (hold_index < terms.size)
    {
        sn_obj_id_t update = sn_share_or(target, sn_vec_data(sn_obj_id_t, &controls), (uint32_t)controls.size);
        sn_obj_id_t enable = sn_obj_fanin(target, new_reg, SN_REG_ENABLE);
        if (enable != SN_INVALID_ID)
        {
            sn_obj_id_t fanins[2] = {enable, update};
            update = sn_module_add_operator(target, SN_BIT_AND, 1, false, 2, fanins, NULL);
        }
        sn_reg_set_fanin(target, new_reg, SN_REG_ENABLE, update);
    }
    stats->registers++;
    stats->muxes++;
    stats->paths_before += paths.size;
    stats->paths_after += terms.size;
    sn_vec_destroy(&data_terms);
    sn_vec_destroy(&controls);
    sn_vec_destroy(&stack);
    sn_vec_destroy(&steps);
    sn_vec_destroy(&paths);
    sn_vec_destroy(&terms);
    sn_vec_destroy(&term_hashes);
    sn_vec_destroy(&term_links);
    free(path_links);
    free(group_heads);
    free(term_buckets);
    return true;

unchanged:
    sn_vec_destroy(&stack);
    sn_vec_destroy(&steps);
    sn_vec_destroy(&paths);
    sn_vec_destroy(&terms);
    sn_vec_destroy(&term_hashes);
    sn_vec_destroy(&term_links);
    free(path_links);
    free(group_heads);
    free(term_buckets);
    sn_vec_destroy(&data_terms);
    sn_vec_destroy(&controls);
    return false;
}

static inline sn_obj_id_t sn_share_select_bit(sn_module_t* module, sn_obj_id_t select, uint32_t bit)
{
    if (sn_obj_width(module, select) == 1)
        return select;
    return sn_module_add_slice(module, select, (int32_t)bit, (int32_t)bit, NULL);
}

static inline bool sn_share_reg_pmux(sn_module_t* target, const sn_module_t* source, sn_obj_id_t old_reg,
                                     const uint64_t* hashes, sn_share_options_t options, sn_share_stats_t* stats)
{
    sn_obj_id_t old_in = sn_obj_pair_in(source, old_reg);
    sn_obj_id_t old_root = sn_obj_fanin(source, old_in, 0);
    if (old_root != SN_INVALID_ID)
        old_root = sn_share_strip_value(source, old_root);
    if (old_root == SN_INVALID_ID || sn_obj_type(source, old_root) != SN_PMUX)
        return false;
    if (sn_obj_width(source, old_reg) < options.min_width)
        return false;
    sn_vec_t words;
    if (!sn_share_pmux_words(source, old_root, &words))
        return false;
    uint32_t count = (uint32_t)words.size;
    if (count < options.min_alternatives || count > UINT16_MAX)
    {
        sn_vec_destroy(&words);
        return false;
    }
    sn_obj_id_t old_default = sn_share_strip_value(source, sn_obj_fanin(source, old_root, SN_PMUX_DEFAULT));
    sn_obj_id_t old_hold = sn_share_strip_value(source, old_reg);
    bool extracts_hold = sn_share_select_is_decode(source, sn_obj_fanin(source, old_root, SN_PMUX_SELECT)) &&
                         sn_share_hashed_equal(source, hashes, old_default, old_hold);
    sn_vec_t unique, unique_hashes, unique_links, conditions, members;
    sn_vec_init(&unique);
    sn_vec_init(&unique_hashes);
    sn_vec_init(&unique_links);
    sn_vec_init(&conditions);
    sn_vec_init(&members);
    uint32_t bucket_count = 1;
    while (bucket_count < 2 * count)
        bucket_count <<= 1;
    uint32_t* buckets = (uint32_t*)malloc((size_t)bucket_count * sizeof(uint32_t));
    uint32_t* member_heads = NULL;
    uint32_t* member_links = NULL;
    assert(buckets);
    memset(buckets, 0xff, (size_t)bucket_count * sizeof(uint32_t));
    for (uint32_t i = 0; i < count; i++)
    {
        sn_obj_id_t value = sn_vec_at(sn_obj_id_t, &words, i);
        if (extracts_hold && sn_share_hashed_equal(source, hashes, value, old_hold))
            continue;
        uint64_t value_hash = hashes[sn_share_strip_value(source, value)];
        uint32_t bucket = (uint32_t)value_hash & (bucket_count - 1);
        uint32_t k;
        for (k = buckets[bucket]; k != SN_INVALID_ID; k = sn_vec_at(uint32_t, &unique_links, k))
            if (sn_vec_at(uint64_t, &unique_hashes, k) == value_hash &&
                sn_share_value_equal(source, sn_vec_at(sn_obj_id_t, &unique, k), value))
                break;
        if (k == SN_INVALID_ID)
        {
            k = (uint32_t)unique.size;
            *sn_vec_push(sn_obj_id_t, &unique) = value;
            *sn_vec_push(uint64_t, &unique_hashes) = value_hash;
            *sn_vec_push(uint32_t, &unique_links) = buckets[bucket];
            buckets[bucket] = k;
        }
        assert(k <= UINT16_MAX && i <= UINT16_MAX);
        *sn_vec_push(uint32_t, &members) = ((uint32_t)k << 16) | i;
    }
    uint32_t after = (uint32_t)unique.size;
    uint32_t before = count + 1;
    if (!extracts_hold)
        after++;
    if (!unique.size || before <= after || before - after < options.min_saved_paths || before < 2 * after)
    {
        sn_vec_destroy(&words);
        sn_vec_destroy(&unique);
        sn_vec_destroy(&unique_hashes);
        sn_vec_destroy(&unique_links);
        sn_vec_destroy(&conditions);
        sn_vec_destroy(&members);
        free(buckets);
        return false;
    }
    member_heads = (uint32_t*)malloc(unique.size * sizeof(uint32_t));
    member_links = (uint32_t*)malloc(members.size * sizeof(uint32_t));
    assert(member_heads && member_links);
    for (size_t k = 0; k < unique.size; k++)
        member_heads[k] = SN_INVALID_ID;
    for (size_t j = 0; j < members.size; j++)
    {
        uint32_t group = sn_vec_at(uint32_t, &members, j) >> 16;
        assert(group < unique.size);
        member_links[j] = member_heads[group];
        member_heads[group] = (uint32_t)j;
    }

    sn_obj_id_t new_reg = sn_obj_dup(source, old_reg);
    sn_obj_id_t new_in = sn_obj_pair_in(target, new_reg);
    sn_obj_id_t new_select = sn_obj_dup(source, sn_obj_fanin(source, old_root, SN_PMUX_SELECT));
    for (size_t k = 0; k < unique.size; k++)
    {
        sn_vec_t bits;
        sn_vec_init(&bits);
        for (uint32_t j = member_heads[k]; j != SN_INVALID_ID; j = member_links[j])
        {
            uint32_t member = sn_vec_at(uint32_t, &members, j);
            *sn_vec_push(sn_obj_id_t, &bits) = sn_share_select_bit(target, new_select, member & UINT16_MAX);
        }
        *sn_vec_push(sn_obj_id_t, &conditions) =
            sn_share_or(target, sn_vec_data(sn_obj_id_t, &bits), (uint32_t)bits.size);
        sn_vec_destroy(&bits);
    }
    sn_obj_id_t new_data;
    if (unique.size == 1)
    {
        sn_obj_id_t alternative = sn_obj_dup(source, sn_vec_at(sn_obj_id_t, &unique, 0));
        new_data = extracts_hold ? alternative
                                 : sn_module_add_mux(target, sn_vec_at(sn_obj_id_t, &conditions, 0), alternative,
                                                     sn_obj_dup(source, old_default), NULL);
    }
    else
    {
        sn_vec_t alternatives;
        sn_vec_init(&alternatives);
        for (size_t k = 0; k < unique.size; k++)
            *sn_vec_push(sn_obj_id_t, &alternatives) = sn_obj_dup(source, sn_vec_at(sn_obj_id_t, &unique, k));
        sn_obj_id_t packed_select =
            sn_module_add_concat(target, (uint32_t)conditions.size, sn_vec_data(sn_obj_id_t, &conditions), NULL);
        sn_obj_id_t packed_data =
            sn_module_add_concat(target, (uint32_t)alternatives.size, sn_vec_data(sn_obj_id_t, &alternatives), NULL);
        sn_obj_id_t default_data = extracts_hold ? sn_vec_at(sn_obj_id_t, &alternatives, alternatives.size - 1)
                                                 : sn_obj_dup(source, old_default);
        new_data = sn_module_add_pmux(target, packed_select, packed_data, default_data, NULL);
        sn_vec_destroy(&alternatives);
    }
    sn_obj_connect(target, new_in, 0, new_data);
    if (extracts_hold)
    {
        sn_obj_id_t update =
            sn_share_or(target, sn_vec_data(sn_obj_id_t, &conditions), (uint32_t)conditions.size);
        sn_obj_id_t enable = sn_obj_fanin(target, new_reg, SN_REG_ENABLE);
        if (enable != SN_INVALID_ID)
        {
            sn_obj_id_t fanins[2] = {enable, update};
            update = sn_module_add_operator(target, SN_BIT_AND, 1, false, 2, fanins, NULL);
        }
        sn_reg_set_fanin(target, new_reg, SN_REG_ENABLE, update);
    }
    stats->registers++;
    stats->muxes++;
    stats->paths_before += before;
    stats->paths_after += after;
    sn_vec_destroy(&words);
    sn_vec_destroy(&unique);
    sn_vec_destroy(&unique_hashes);
    sn_vec_destroy(&unique_links);
    sn_vec_destroy(&conditions);
    sn_vec_destroy(&members);
    free(member_links);
    free(member_heads);
    free(buckets);
    return true;
}

static inline void sn_share_replace_module(sn_design_t* design, sn_module_id_t old_id, sn_module_id_t new_id)
{
    assert(new_id + 1 == design->modules.size && old_id != new_id);
    sn_module_t* old_module = sn_design_get_module(design, old_id);
    sn_module_t* new_module = sn_design_get_module(design, new_id);
    sn_name_id_t temporary_name_id = new_module->name;
    sn_name_id_t name = old_module->name;
    bool interface_locked = old_module->interface_locked;
    sn_design_invalidate_copies_to_module(design, old_id);
    sn_module_destroy(old_module);
    free(old_module);
    new_module->id = old_id;
    new_module->name = name;
    new_module->interface_locked = interface_locked;
    sn_vec_at(sn_module_t*, &design->modules, old_id) = new_module;
    design->modules.size--;
    sn_name_remove_last(&design->names, temporary_name_id);
}

static inline bool sn_share_module_has_candidate(const sn_module_t* module, sn_share_options_t options)
{
    for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t reg = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        if (sn_obj_width(module, reg) < options.min_width)
            continue;
        sn_obj_id_t root = sn_obj_fanin(module, sn_obj_pair_in(module, reg), 0);
        if (root == SN_INVALID_ID)
            continue;
        root = sn_share_strip_value(module, root);
        if (sn_obj_type(module, root) == SN_MUX)
            return true;
        if (sn_obj_type(module, root) == SN_PMUX)
        {
            sn_obj_id_t select = sn_obj_fanin(module, root, SN_PMUX_SELECT);
            sn_obj_id_t alternatives = sn_obj_fanin(module, root, SN_PMUX_ALTERNATIVES);
            uint32_t count = sn_obj_width(module, select);
            if (count >= options.min_alternatives &&
                (uint64_t)count * sn_obj_width(module, root) == sn_obj_width(module, alternatives))
                return true;
        }
    }
    return false;
}

static inline bool sn_design_share_module(sn_design_t* design, sn_module_id_t module_id,
                                          sn_share_options_t options, sn_share_stats_t* stats)
{
    sn_module_t* source = sn_design_get_module(design, module_id);
    if (!sn_share_module_has_candidate(source, options))
        return false;
    char name[96];
    uint32_t suffix = 0;
    do
    {
        int length = snprintf(name, sizeof(name), "__sn_share_%u_%u", module_id, suffix++);
        assert(length > 0 && (size_t)length < sizeof(name) && suffix != 0);
        (void)length;
    } while (sn_name_find(&design->names, name) != SN_INVALID_ID);
    sn_module_id_t target_id = sn_design_dup_module_topo(design, module_id, name);
    sn_module_t* target = sn_design_get_module(design, target_id);
    uint64_t* hashes = sn_share_value_hashes(source);
    bool changed = false;
    for (size_t i = 0; i < source->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t reg = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_REG_OUT], i);
        bool reg_changed = sn_share_reg_mux_tree(target, source, reg, hashes, options, stats);
        if (!reg_changed)
            reg_changed = sn_share_reg_pmux(target, source, reg, hashes, options, stats);
        changed |= reg_changed;
    }
    free(hashes);
    if (!changed)
    {
        sn_name_id_t temporary_name_id = target->name;
        sn_module_destroy(target);
        free(target);
        design->modules.size--;
        sn_name_remove_last(&design->names, temporary_name_id);
        sn_vec_destroy(&source->copy_ids);
        sn_vec_init(&source->copy_ids);
        source->copy_module = SN_INVALID_ID;
        return false;
    }
    sn_share_replace_module(design, module_id, target_id);
    // Do not use observable-cone cleanup here: even a constant or externally unobservable register is part of the
    // canonical transition interface used by pre/post CEC. Reordering preserves every pair and its type ID. Dangling
    // mux objects retained by this first implementation are harmless because hierarchical blasting is demand-driven.
    sn_design_reorder_module_topo(design, module_id);
    stats->modules++;
    return true;
}

static inline sn_share_stats_t sn_design_share(sn_design_t* design, sn_share_options_t options)
{
    assert(design && sn_design_is_topo(design));
    sn_share_stats_t stats = {0};
    size_t module_count = design->modules.size;
    for (sn_module_id_t module = 0; module < module_count; module++)
        sn_design_share_module(design, module, options, &stats);
    assert(design->modules.size == module_count && sn_design_is_topo(design));
    return stats;
}

ABC_NAMESPACE_HEADER_END

#endif
