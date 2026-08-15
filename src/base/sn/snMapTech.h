/**CFile****************************************************************

  FileName    [snMapTech.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Technology mapping infrastructure for SN hierarchy and hard primitives.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapTech.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MAP_TECH_H
#define SN_MAP_TECH_H

#include "snMapAdd.h"
#include "snMapDsp.h"
#include "snMapMem.h"

ABC_NAMESPACE_HEADER_START

// Combined technology mapping rebuilds each module once. Memory and multiplier
// expansion may temporarily introduce forward references; the result is
// finalized through one dependency-aware topological duplication.

typedef struct sn_tech_map_options_t
{
    bool map_memories;
    bool map_multipliers;
    bool map_adders;
    sn_mem_map_options_t memory;
    sn_dsp_map_options_t dsp;
    sn_add_map_options_t add;
} sn_tech_map_options_t;

typedef struct sn_tech_map_stats_t
{
    size_t mem_insts;
    size_t dsp_insts;
    size_t carry_insts;
} sn_tech_map_stats_t;

typedef struct sn_tech_mem_plan_t
{
    sn_obj_id_t memory;
    sn_obj_id_t memory_in;
    sn_obj_id_t read;
    sn_obj_id_t write;
    sn_obj_id_t reads[2];
    sn_obj_id_t writes[2];
    uint32_t read_count;
    uint32_t write_count;
    int8_t port_reads[2];
    int8_t port_writes[2];
    const sn_mem_tech_t* primitive;
    uint32_t port_width;
    uint32_t tile_depth;
    uint32_t width_tiles;
    uint32_t depth_tiles;
} sn_tech_mem_plan_t;

typedef struct sn_tech_dsp_chunk_t
{
    sn_obj_id_t object;
    uint32_t offset;
    bool unsigned_correction;
} sn_tech_dsp_chunk_t;

static inline sn_tech_mem_plan_t* sn_tech_read_plan(const sn_module_t* module, sn_tech_mem_plan_t* plans,
                                                    sn_obj_id_t object)
{
    return sn_obj_type(module, object) == SN_MEM_READ ? &plans[sn_obj_type_id(module, object)] : NULL;
}

static inline sn_tech_map_options_t sn_tech_map_default_options(void)
{
    sn_tech_map_options_t options;
    options.map_memories = true;
    options.map_multipliers = true;
    options.map_adders = false;
    options.memory = sn_mem_map_default_options();
    options.dsp = sn_dsp_map_default_options();
    options.add = sn_add_map_default_options();
    return options;
}

static inline uint32_t sn_tech_ceil_div(uint32_t value, uint32_t divisor)
{
    assert(divisor);
    return value / divisor + (value % divisor != 0);
}

static inline uint32_t sn_tech_floor_pow2(uint32_t value)
{
    assert(value);
    uint32_t result = 1;
    while (result <= value / 2)
        result <<= 1;
    return result;
}

static inline uint32_t sn_tech_ceil_log2(uint32_t value)
{
    assert(value);
    uint32_t result = 0;
    for (value--; value; value >>= 1)
        result++;
    return result;
}

static inline sn_obj_id_t sn_tech_add_uint_const(sn_module_t* module, uint32_t width, uint32_t value)
{
    assert(width && width <= 32);
    assert(width == 32 || value < (1u << width));
    return sn_module_add_const(module, width, false, &value, NULL);
}

static inline sn_obj_id_t sn_tech_add_cast(sn_module_t* module, sn_obj_id_t value, uint32_t width, bool is_signed)
{
    return sn_module_add_operator(module, SN_CAST, width, is_signed, 1, &value, NULL);
}

static inline sn_obj_id_t sn_tech_add_zero_extend(sn_module_t* module, sn_obj_id_t value, uint32_t width)
{
    uint32_t old_width = sn_obj_width(module, value);
    assert(old_width <= width);
    if (old_width == width)
        return value;
    sn_obj_id_t padding = sn_module_add_named_obj(module, SN_CONST0, width - old_width, false, 0, NULL);
    sn_obj_id_t fanins[2] = {value, padding};
    return sn_module_add_concat(module, 2, fanins, NULL);
}

static inline uint32_t sn_tech_dsp_chunk_count(uint32_t width, uint32_t port_width, uint32_t low_width,
                                               uint32_t min_width)
{
    assert(width && port_width && low_width && low_width <= port_width && min_width <= port_width);
    if (width < min_width || low_width < min_width)
        return UINT32_MAX;
    uint32_t count = 1;
    while (width > port_width)
    {
        uint32_t chunk_width = low_width;
        if (width - chunk_width < min_width)
            chunk_width = width - min_width;
        if (chunk_width < min_width || chunk_width > port_width)
            return UINT32_MAX;
        width -= chunk_width;
        count++;
    }
    return count;
}

static inline uint32_t sn_tech_dsp_box_count(const sn_module_t* module, const sn_dsp_tech_t* dsp,
                                             const sn_dsp_map_options_t* options, sn_obj_id_t a, sn_obj_id_t b)
{
    bool signed_operands = sn_obj_is_signed(module, a) && sn_obj_is_signed(module, b);
    uint32_t a_width = sn_obj_width(module, a) + !signed_operands;
    uint32_t b_width = sn_obj_width(module, b) + !signed_operands;
    uint32_t a_low = options->a_unsigned_chunk_width ? options->a_unsigned_chunk_width : dsp->a_width;
    uint32_t b_low = options->b_unsigned_chunk_width ? options->b_unsigned_chunk_width : dsp->b_width;
    if (a_low < dsp->min_a_width || a_low > dsp->a_width || b_low < dsp->min_b_width || b_low > dsp->b_width)
        return UINT32_MAX;
    uint32_t direct_a = sn_tech_dsp_chunk_count(a_width, dsp->a_width, a_low, dsp->min_a_width);
    uint32_t direct_b = sn_tech_dsp_chunk_count(b_width, dsp->b_width, b_low, dsp->min_b_width);
    uint32_t swapped_a = sn_tech_dsp_chunk_count(b_width, dsp->a_width, a_low, dsp->min_a_width);
    uint32_t swapped_b = sn_tech_dsp_chunk_count(a_width, dsp->b_width, b_low, dsp->min_b_width);
    uint32_t direct = direct_a == UINT32_MAX || direct_b == UINT32_MAX || direct_a > UINT32_MAX / direct_b
                          ? UINT32_MAX
                          : direct_a * direct_b;
    uint32_t swapped = swapped_a == UINT32_MAX || swapped_b == UINT32_MAX || swapped_a > UINT32_MAX / swapped_b
                           ? UINT32_MAX
                           : swapped_a * swapped_b;
    return direct < swapped ? direct : swapped;
}

static inline void sn_tech_dsp_make_chunks(sn_module_t* module, sn_obj_id_t value, uint32_t port_width,
                                           uint32_t low_width, uint32_t min_width, sn_vec_t* chunks)
{
    assert(module && chunks);
    uint32_t width = sn_obj_width(module, value);
    uint32_t count = sn_tech_dsp_chunk_count(width, port_width, low_width, min_width);
    assert(count != UINT32_MAX);
    uint32_t offset = 0, remaining = width;
    for (uint32_t i = 0; i < count; i++)
    {
        uint32_t chunk_width = remaining <= port_width ? remaining : low_width;
        if (remaining > port_width && remaining - chunk_width < min_width)
            chunk_width = remaining - min_width;
        assert(chunk_width >= min_width && chunk_width <= port_width);
        sn_obj_id_t chunk = count == 1
                                ? value
                                : sn_module_add_slice(module, value, (int32_t)(offset + chunk_width - 1),
                                                      (int32_t)offset, NULL);
        chunk = sn_tech_add_cast(module, chunk, chunk_width, true);
        sn_tech_dsp_chunk_t* entry = sn_vec_push(sn_tech_dsp_chunk_t, chunks);
        entry->object = chunk;
        entry->offset = offset;
        entry->unsigned_correction = i + 1 != count;
        offset += chunk_width;
        remaining -= chunk_width;
    }
    assert(!remaining && offset == width);
}

static inline sn_obj_id_t sn_tech_dsp_align(sn_module_t* module, sn_obj_id_t value, uint32_t result_width,
                                            uint32_t shift, bool is_signed)
{
    value = sn_tech_add_cast(module, value, result_width, is_signed);
    if (!shift)
        return value;
    sn_obj_id_t amount = sn_tech_add_uint_const(module, 32, shift);
    sn_obj_id_t fanins[2] = {value, amount};
    return sn_module_add_operator(module, SN_SHL, result_width, is_signed, 2, fanins, NULL);
}

static inline void sn_tech_dsp_add_gated_correction(sn_module_t* module, sn_vec_t* partials, sn_obj_id_t condition,
                                                    sn_obj_id_t value, uint32_t result_width, uint32_t shift)
{
    if (shift >= result_width)
        return;
    sn_obj_id_t selected = sn_tech_add_cast(module, value, result_width, true);
    sn_obj_id_t zero = sn_module_add_named_obj(module, SN_CONST0, result_width, false, 0, NULL);
    sn_obj_id_t gated = sn_module_add_mux(module, condition, selected, zero, NULL);
    *sn_vec_push(sn_obj_id_t, partials) = sn_tech_dsp_align(module, gated, result_width, shift, true);
}

static inline sn_obj_id_t sn_tech_map_multiplier(sn_module_t* module, const sn_dsp_tech_t* dsp,
                                                 const sn_dsp_map_options_t* options, sn_obj_id_t a,
                                                 sn_obj_id_t b, uint32_t result_width, bool result_signed)
{
    assert(module && dsp && options && result_width);
    bool signed_operands = sn_obj_is_signed(module, a) && sn_obj_is_signed(module, b);
    if (!signed_operands)
    {
        uint32_t zero = 0;
        sn_obj_id_t sign = sn_module_add_const(module, 1, false, &zero, NULL);
        sn_obj_id_t fanins[2] = {a, sign};
        a = sn_module_add_concat(module, 2, fanins, NULL);
        a = sn_tech_add_cast(module, a, sn_obj_width(module, a), true);
        fanins[0] = b;
        b = sn_module_add_concat(module, 2, fanins, NULL);
        b = sn_tech_add_cast(module, b, sn_obj_width(module, b), true);
    }

    uint32_t a_low = options->a_unsigned_chunk_width ? options->a_unsigned_chunk_width : dsp->a_width;
    uint32_t b_low = options->b_unsigned_chunk_width ? options->b_unsigned_chunk_width : dsp->b_width;
    assert(a_low <= dsp->a_width && b_low <= dsp->b_width);
    uint32_t direct_a = sn_tech_dsp_chunk_count(sn_obj_width(module, a), dsp->a_width, a_low, dsp->min_a_width);
    uint32_t direct_b = sn_tech_dsp_chunk_count(sn_obj_width(module, b), dsp->b_width, b_low, dsp->min_b_width);
    uint32_t swapped_a = sn_tech_dsp_chunk_count(sn_obj_width(module, b), dsp->a_width, a_low, dsp->min_a_width);
    uint32_t swapped_b = sn_tech_dsp_chunk_count(sn_obj_width(module, a), dsp->b_width, b_low, dsp->min_b_width);
    uint32_t direct = direct_a == UINT32_MAX || direct_b == UINT32_MAX || direct_a > UINT32_MAX / direct_b
                          ? UINT32_MAX
                          : direct_a * direct_b;
    uint32_t swapped = swapped_a == UINT32_MAX || swapped_b == UINT32_MAX || swapped_a > UINT32_MAX / swapped_b
                           ? UINT32_MAX
                           : swapped_a * swapped_b;
    if (swapped < direct)
    {
        sn_obj_id_t temporary = a;
        a = b;
        b = temporary;
    }

    sn_vec_t a_chunks, b_chunks, partials;
    sn_vec_init(&a_chunks);
    sn_vec_init(&b_chunks);
    sn_vec_init(&partials);
    sn_tech_dsp_make_chunks(module, a, dsp->a_width, a_low, dsp->min_a_width, &a_chunks);
    sn_tech_dsp_make_chunks(module, b, dsp->b_width, b_low, dsp->min_b_width, &b_chunks);
    assert(!options->max_dsps_per_multiply ||
           a_chunks.size * b_chunks.size <= options->max_dsps_per_multiply);

    for (size_t diagonal = 0; diagonal < a_chunks.size + b_chunks.size - 1; diagonal++)
        for (size_t i = 0; i < a_chunks.size; i++)
        {
            if (diagonal < i)
                continue;
            size_t j = diagonal - i;
            if (j >= b_chunks.size)
                continue;
            const sn_tech_dsp_chunk_t* ac = &sn_vec_at(sn_tech_dsp_chunk_t, &a_chunks, i);
            const sn_tech_dsp_chunk_t* bc = &sn_vec_at(sn_tech_dsp_chunk_t, &b_chunks, j);
            uint32_t shift = ac->offset + bc->offset;
            if (options->prune_unused_high_products && shift >= result_width)
                continue;
            uint32_t product_width = sn_obj_width(module, ac->object) + sn_obj_width(module, bc->object);
            uint32_t primitive_width = product_width < dsp->min_p_width ? dsp->min_p_width : product_width;
            assert(primitive_width <= dsp->p_width);
            sn_module_id_t primitive = sn_map_dsp_primitive_module(
                module->design, dsp, sn_obj_width(module, ac->object), sn_obj_width(module, bc->object),
                primitive_width, true, true);
            sn_obj_id_t inputs[2] = {ac->object, bc->object};
            sn_obj_id_t product = sn_module_add_inst(module, primitive, 2, inputs, NULL, NULL);
            *sn_vec_push(sn_obj_id_t, &partials) = sn_tech_dsp_align(module, product, result_width, shift, true);

            // A non-top radix chunk is unsigned even though the DSP input is signed. For a W-bit chunk U,
            // U = signed(U) + msb(U)*2^W. Add the resulting one-bit-gated correction terms around the signed
            // DSP product. This uses the full 27x18 multiplier while preserving exact unsigned chunk semantics.
            uint32_t ac_width = sn_obj_width(module, ac->object);
            uint32_t bc_width = sn_obj_width(module, bc->object);
            sn_obj_id_t ac_sign = SN_INVALID_ID, bc_sign = SN_INVALID_ID;
            if (ac->unsigned_correction)
            {
                ac_sign = sn_module_add_slice(module, ac->object, (int32_t)(ac_width - 1),
                                              (int32_t)(ac_width - 1), NULL);
                sn_tech_dsp_add_gated_correction(module, &partials, ac_sign, bc->object, result_width,
                                                 shift + ac_width);
            }
            if (bc->unsigned_correction)
            {
                bc_sign = sn_module_add_slice(module, bc->object, (int32_t)(bc_width - 1),
                                              (int32_t)(bc_width - 1), NULL);
                sn_tech_dsp_add_gated_correction(module, &partials, bc_sign, ac->object, result_width,
                                                 shift + bc_width);
            }
            if (ac->unsigned_correction && bc->unsigned_correction && shift + ac_width + bc_width < result_width)
            {
                sn_obj_id_t fanins[2] = {ac_sign, bc_sign};
                sn_obj_id_t both = sn_module_add_operator(module, SN_BIT_AND, 1, false, 2, fanins, NULL);
                *sn_vec_push(sn_obj_id_t, &partials) =
                    sn_tech_dsp_align(module, both, result_width, shift + ac_width + bc_width, false);
            }
        }

    if (!partials.size)
        *sn_vec_push(sn_obj_id_t, &partials) = sn_tech_add_uint_const(module, result_width, 0);
    while (partials.size > 1)
    {
        sn_vec_t next;
        sn_vec_init(&next);
        if (options->balance_adders)
        {
            for (size_t i = 0; i < partials.size; i += 2)
            {
                if (i + 1 == partials.size)
                    *sn_vec_push(sn_obj_id_t, &next) = sn_vec_at(sn_obj_id_t, &partials, i);
                else
                {
                    sn_obj_id_t fanins[2] = {sn_vec_at(sn_obj_id_t, &partials, i),
                                             sn_vec_at(sn_obj_id_t, &partials, i + 1)};
                    *sn_vec_push(sn_obj_id_t, &next) =
                        sn_module_add_operator(module, SN_ADD, result_width, true, 2, fanins, NULL);
                }
            }
        }
        else
        {
            sn_obj_id_t fanins[2] = {sn_vec_at(sn_obj_id_t, &partials, 0),
                                     sn_vec_at(sn_obj_id_t, &partials, 1)};
            *sn_vec_push(sn_obj_id_t, &next) =
                sn_module_add_operator(module, SN_ADD, result_width, true, 2, fanins, NULL);
            for (size_t i = 2; i < partials.size; i++)
                *sn_vec_push(sn_obj_id_t, &next) = sn_vec_at(sn_obj_id_t, &partials, i);
        }
        sn_vec_destroy(&partials);
        partials = next;
    }
    sn_obj_id_t result = sn_tech_add_cast(module, sn_vec_at(sn_obj_id_t, &partials, 0), result_width, result_signed);
    sn_vec_destroy(&a_chunks);
    sn_vec_destroy(&b_chunks);
    sn_vec_destroy(&partials);
    return result;
}

static inline bool sn_tech_choose_memory_for_mode(const sn_tech_t* tech, uint32_t width, uint32_t depth,
                                                  const sn_mem_map_options_t* options, bool simple_dual,
                                                  sn_tech_mem_plan_t* plan)
{
    assert(tech && options && plan && width && depth);
    uint64_t best_cost = UINT64_MAX;
    uint32_t best_port_width = 0;
    for (size_t i = 0; i < tech->memory_count; i++)
    {
        const sn_mem_tech_t* primitive = &tech->memories[i];
        const uint32_t* widths = simple_dual && primitive->simple_dual_width_count
                                     ? primitive->simple_dual_widths
                                     : primitive->widths;
        size_t width_count = simple_dual && primitive->simple_dual_width_count
                                 ? primitive->simple_dual_width_count
                                 : primitive->width_count;
        for (size_t j = 0; j < width_count; j++)
        {
            uint32_t port_width = widths[j];
            uint32_t tile_depth = sn_tech_floor_pow2(primitive->cap_bits / port_width);
            if (tile_depth > (1u << primitive->address_bits))
                tile_depth = 1u << primitive->address_bits;
            uint32_t width_tiles = sn_tech_ceil_div(width, port_width);
            uint32_t depth_tiles = sn_tech_ceil_div(depth, tile_depth);
            uint64_t count = (uint64_t)width_tiles * depth_tiles;
            if (options->max_primitives_per_memory && count > options->max_primitives_per_memory)
                continue;
            uint64_t cost = count * primitive->mapping_cost;
            bool prefer_tie = cost == best_cost &&
                              ((options->split_order == SN_MEM_SPLIT_WIDTH_FIRST && port_width > best_port_width) ||
                               (options->split_order == SN_MEM_SPLIT_DEPTH_FIRST && port_width < best_port_width));
            if (cost > best_cost || (cost == best_cost && !prefer_tie))
                continue;
            best_cost = cost;
            best_port_width = port_width;
            plan->primitive = primitive;
            plan->port_width = port_width;
            plan->tile_depth = tile_depth;
            plan->width_tiles = width_tiles;
            plan->depth_tiles = depth_tiles;
        }
    }
    return best_cost != UINT64_MAX;
}

static inline bool sn_tech_choose_memory(const sn_tech_t* tech, uint32_t width, uint32_t depth,
                                         const sn_mem_map_options_t* options, sn_tech_mem_plan_t* plan)
{
    return sn_tech_choose_memory_for_mode(tech, width, depth, options, false, plan);
}

static inline sn_module_id_t sn_tech_memory_tile_module(sn_design_t* design, const sn_mem_tech_t* primitive,
                                                         uint32_t width, uint32_t depth)
{
    uint32_t address_width = sn_tech_ceil_log2(depth);
    char name[128];
    int length = snprintf(name, sizeof(name), "__sn_%s_tile_%u_%u", primitive->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;
    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock = sn_module_add_pi(module, 1, false, "clock");
    sn_obj_id_t enable = sn_module_add_pi(module, 1, false, "enable");
    sn_obj_id_t write_address = sn_module_add_pi(module, address_width, false, "write_address");
    sn_obj_id_t data = sn_module_add_pi(module, width, false, "write_data");
    sn_obj_id_t read_address = sn_module_add_pi(module, address_width, false, "read_address");
    sn_obj_pair_t pair = sn_module_add_mem_pair(module, width, false, depth, "mem_out", "mem_in");
    sn_module_add_mem_write(module, pair.in, clock, enable, data, write_address, "write");
    sn_obj_id_t read = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, read_address, "read");
    sn_module_add_po(module, width, false, "read_data", read);
    sn_design_reorder_module_topo(design, id);
    return id;
}

// A behavioral true-dual-port tile. Reads are deliberately asynchronous in
// this wrapper: frontend-imported synchronous reads are represented by the
// existing registers driven by SN_MEM_READ objects. Keeping those registers
// outside the wrapper preserves latency until a later RAM-cell emitter absorbs
// them into the physical primitive's registered read ports.
static inline sn_module_id_t sn_tech_memory_tdp_tile_module(sn_design_t* design, const sn_mem_tech_t* primitive,
                                                            uint32_t width, uint32_t depth)
{
    uint32_t address_width = sn_tech_ceil_log2(depth);
    char name[128];
    int length = snprintf(name, sizeof(name), "__sn_%s_tdp_tile_%u_%u", primitive->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;

    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock[2], write_enable[2], address[2], data[2];
    for (uint32_t port = 0; port < 2; port++)
    {
        char suffix = (char)('a' + port);
        char object_name[32];
        snprintf(object_name, sizeof(object_name), "clock_%c", suffix);
        clock[port] = sn_module_add_pi(module, 1, false, object_name);
        snprintf(object_name, sizeof(object_name), "write_enable_%c", suffix);
        write_enable[port] = sn_module_add_pi(module, 1, false, object_name);
        snprintf(object_name, sizeof(object_name), "address_%c", suffix);
        address[port] = sn_module_add_pi(module, address_width, false, object_name);
        snprintf(object_name, sizeof(object_name), "write_data_%c", suffix);
        data[port] = sn_module_add_pi(module, width, false, object_name);
    }

    sn_obj_pair_t pair = sn_module_add_mem_pair(module, width, false, depth, "mem_out", "mem_in");
    sn_module_add_mem_write(module, pair.in, clock[0], write_enable[0], data[0], address[0], "write_a");
    sn_module_add_mem_write(module, pair.in, clock[1], write_enable[1], data[1], address[1], "write_b");
    sn_obj_id_t read_a = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, address[0], "read_a");
    sn_obj_id_t read_b = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, address[1], "read_b");
    sn_module_add_po(module, width, false, "read_data_a", read_a);
    sn_module_add_po(module, width, false, "read_data_b", read_b);
    sn_design_reorder_module_topo(design, id);
    return id;
}

static inline bool sn_tech_assign_tdp_ports(const sn_module_t* source, sn_tech_mem_plan_t* plan)
{
    assert(source && plan && plan->read_count <= 2 && plan->write_count <= 2);
    plan->port_reads[0] = plan->port_reads[1] = -1;
    plan->port_writes[0] = plan->port_writes[1] = -1;
    for (uint32_t write = 0; write < plan->write_count; write++)
        plan->port_writes[write] = (int8_t)write;

    // Prefer sharing a physical port when the logical read and write use the
    // same address. This recognizes the usual read-first HLS R/W port.
    for (uint32_t read = 0; read < plan->read_count; read++)
    {
        sn_obj_id_t read_address = sn_obj_fanin(source, plan->reads[read], SN_MEM_READ_ADDRESS);
        for (uint32_t port = 0; port < 2; port++)
        {
            int8_t write = plan->port_writes[port];
            if (write >= 0 && plan->port_reads[port] < 0 &&
                sn_obj_fanin(source, plan->writes[(uint32_t)write], SN_MEM_WRITE_ADDRESS) == read_address)
            {
                plan->port_reads[port] = (int8_t)read;
                break;
            }
        }
    }
    for (uint32_t read = 0; read < plan->read_count; read++)
    {
        bool assigned = false;
        for (uint32_t port = 0; port < 2; port++)
            assigned |= plan->port_reads[port] == (int8_t)read;
        if (assigned)
            continue;
        for (uint32_t port = 0; port < 2; port++)
            if (plan->port_reads[port] < 0 && plan->port_writes[port] < 0)
            {
                plan->port_reads[port] = (int8_t)read;
                assigned = true;
                break;
            }
        if (!assigned)
            return false;
    }
    return true;
}

static inline sn_obj_id_t sn_tech_memory_bank_select(sn_module_t* module, sn_obj_id_t address,
                                                     uint32_t address_bits, uint32_t bank_bits, uint32_t bank)
{
    if (!bank_bits)
        return sn_tech_add_uint_const(module, 1, 1);
    uint32_t needed = address_bits + bank_bits;
    address = sn_tech_add_zero_extend(module, address, needed > sn_obj_width(module, address)
                                                         ? needed
                                                         : sn_obj_width(module, address));
    sn_obj_id_t index = sn_module_add_slice(module, address, (int32_t)(needed - 1), (int32_t)address_bits, NULL);
    sn_obj_id_t value = sn_tech_add_uint_const(module, bank_bits, bank);
    sn_obj_id_t fanins[2] = {index, value};
    return sn_module_add_operator(module, SN_EQ, 1, false, 2, fanins, NULL);
}

static inline sn_obj_id_t sn_tech_memory_local_address(sn_module_t* module, sn_obj_id_t address,
                                                       uint32_t address_bits)
{
    if (sn_obj_width(module, address) > address_bits)
        return sn_module_add_slice(module, address, (int32_t)(address_bits - 1), 0, NULL);
    return sn_tech_add_zero_extend(module, address, address_bits);
}

static inline sn_obj_id_t sn_tech_map_memory(sn_module_t* module, const sn_module_t* source,
                                             const sn_tech_mem_plan_t* plan, const sn_mem_map_options_t* options)
{
    assert(module && source && plan && options);
    sn_obj_id_t clock = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                  sn_obj_fanin(source, plan->write, SN_MEM_WRITE_CLOCK));
    sn_obj_id_t enable_old = sn_obj_fanin(source, plan->write, SN_MEM_WRITE_ENABLE);
    sn_obj_id_t enable = enable_old == SN_INVALID_ID
                             ? sn_tech_add_uint_const(module, 1, 1)
                             : sn_vec_at(sn_obj_id_t, &source->copy_ids, enable_old);
    sn_obj_id_t data = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                 sn_obj_fanin(source, plan->write, SN_MEM_WRITE_DATA));
    sn_obj_id_t write_address = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                          sn_obj_fanin(source, plan->write, SN_MEM_WRITE_ADDRESS));
    sn_obj_id_t read_address = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                         sn_obj_fanin(source, plan->read, SN_MEM_READ_ADDRESS));
    uint32_t address_bits = sn_tech_ceil_log2(plan->tile_depth);
    uint32_t bank_bits = sn_tech_ceil_log2(plan->depth_tiles);
    sn_obj_id_t local_write = sn_tech_memory_local_address(module, write_address, address_bits);
    sn_obj_id_t local_read = sn_tech_memory_local_address(module, read_address, address_bits);
    sn_module_id_t primitive =
        sn_tech_memory_tile_module(module->design, plan->primitive, plan->port_width, plan->tile_depth);

    sn_vec_t bank_enables, read_selects;
    sn_vec_init(&bank_enables);
    sn_vec_init(&read_selects);
    for (uint32_t d = 0; d < plan->depth_tiles; d++)
    {
        sn_obj_id_t write_select =
            sn_tech_memory_bank_select(module, write_address, address_bits, bank_bits, d);
        sn_obj_id_t enable_fanins[2] = {enable, write_select};
        *sn_vec_push(sn_obj_id_t, &bank_enables) =
            sn_module_add_operator(module, SN_BIT_AND, 1, false, 2, enable_fanins, NULL);
        *sn_vec_push(sn_obj_id_t, &read_selects) =
            sn_tech_memory_bank_select(module, read_address, address_bits, bank_bits, d);
    }

    sn_vec_t width_results;
    sn_vec_init(&width_results);
    for (uint32_t w = 0; w < plan->width_tiles; w++)
    {
        uint32_t offset = w * plan->port_width;
        uint32_t actual = sn_obj_width(source, plan->memory) - offset;
        if (actual > plan->port_width)
            actual = plan->port_width;
        sn_obj_id_t write_data = sn_module_add_slice(module, data, (int32_t)(offset + actual - 1),
                                                      (int32_t)offset, NULL);
        write_data = sn_tech_add_zero_extend(module, write_data, plan->port_width);
        sn_vec_t banks;
        sn_vec_init(&banks);
        for (uint32_t d = 0; d < plan->depth_tiles; d++)
        {
            sn_obj_id_t tile_enable = sn_vec_at(sn_obj_id_t, &bank_enables, d);
            sn_obj_id_t inputs[5] = {clock, tile_enable, local_write, write_data, local_read};
            *sn_vec_push(sn_obj_id_t, &banks) = sn_module_add_inst(module, primitive, 5, inputs, NULL, NULL);
        }
        sn_obj_id_t selected = sn_vec_at(sn_obj_id_t, &banks, 0);
        for (uint32_t d = 1; d < plan->depth_tiles; d++)
        {
            sn_obj_id_t select = sn_vec_at(sn_obj_id_t, &read_selects, d);
            selected = sn_module_add_mux(module, select, sn_vec_at(sn_obj_id_t, &banks, d), selected, NULL);
        }
        if (actual != plan->port_width)
            selected = sn_module_add_slice(module, selected, (int32_t)(actual - 1), 0, NULL);
        *sn_vec_push(sn_obj_id_t, &width_results) = selected;
        sn_vec_destroy(&banks);
    }
    sn_obj_id_t result = width_results.size == 1
                             ? sn_vec_at(sn_obj_id_t, &width_results, 0)
                             : sn_module_add_concat(module, (uint32_t)width_results.size,
                                                    sn_vec_data(sn_obj_id_t, &width_results), NULL);
    sn_vec_destroy(&width_results);
    sn_vec_destroy(&read_selects);
    sn_vec_destroy(&bank_enables);
    return result;
}

static inline void sn_tech_map_tdp_memory(sn_module_t* module, const sn_module_t* source,
                                          const sn_tech_mem_plan_t* plan, sn_obj_id_t results[2])
{
    assert(module && source && plan && plan->read_count > 1 && plan->read_count <= 2 &&
           plan->write_count <= 2 && plan->primitive->port_mode == SN_MEM_PORT_TRUE_DUAL);
    results[0] = results[1] = SN_INVALID_ID;
    uint32_t address_bits = sn_tech_ceil_log2(plan->tile_depth);
    uint32_t bank_bits = sn_tech_ceil_log2(plan->depth_tiles);
    sn_module_id_t primitive =
        sn_tech_memory_tdp_tile_module(module->design, plan->primitive, plan->port_width, plan->tile_depth);
    sn_obj_id_t zero = sn_tech_add_uint_const(module, 1, 0);
    sn_obj_id_t zero_data = sn_module_add_named_obj(module, SN_CONST0, plan->port_width, false, 0, NULL);

    sn_obj_id_t port_clocks[2] = {zero, zero};
    sn_obj_id_t port_addresses[2] = {SN_INVALID_ID, SN_INVALID_ID};
    sn_obj_id_t port_write_data[2] = {SN_INVALID_ID, SN_INVALID_ID};
    sn_vec_t port_enables[2], read_selects[2];
    for (uint32_t port = 0; port < 2; port++)
    {
        sn_vec_init(&port_enables[port]);
        int8_t read_index = plan->port_reads[port];
        int8_t write_index = plan->port_writes[port];
        sn_obj_id_t old_address = read_index >= 0
                                      ? sn_obj_fanin(source, plan->reads[(uint32_t)read_index], SN_MEM_READ_ADDRESS)
                                      : sn_obj_fanin(source, plan->writes[(uint32_t)write_index],
                                                     SN_MEM_WRITE_ADDRESS);
        sn_obj_id_t address = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_address);
        port_addresses[port] = sn_tech_memory_local_address(module, address, address_bits);
        sn_obj_id_t enable = zero;
        if (write_index >= 0)
        {
            sn_obj_id_t write = plan->writes[(uint32_t)write_index];
            port_clocks[port] = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                          sn_obj_fanin(source, write, SN_MEM_WRITE_CLOCK));
            sn_obj_id_t old_enable = sn_obj_fanin(source, write, SN_MEM_WRITE_ENABLE);
            enable = old_enable == SN_INVALID_ID ? sn_tech_add_uint_const(module, 1, 1)
                                                  : sn_vec_at(sn_obj_id_t, &source->copy_ids, old_enable);
            port_write_data[port] = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                              sn_obj_fanin(source, write, SN_MEM_WRITE_DATA));
        }
        for (uint32_t depth_tile = 0; depth_tile < plan->depth_tiles; depth_tile++)
        {
            sn_obj_id_t bank_enable = zero;
            if (write_index >= 0)
            {
                sn_obj_id_t bank_select =
                    sn_tech_memory_bank_select(module, address, address_bits, bank_bits, depth_tile);
                sn_obj_id_t enable_fanins[2] = {enable, bank_select};
                bank_enable = sn_module_add_operator(module, SN_BIT_AND, 1, false, 2, enable_fanins, NULL);
            }
            *sn_vec_push(sn_obj_id_t, &port_enables[port]) = bank_enable;
        }
    }
    for (uint32_t read = 0; read < plan->read_count; read++)
    {
        sn_vec_init(&read_selects[read]);
        sn_obj_id_t address = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                        sn_obj_fanin(source, plan->reads[read], SN_MEM_READ_ADDRESS));
        for (uint32_t depth_tile = 0; depth_tile < plan->depth_tiles; depth_tile++)
            *sn_vec_push(sn_obj_id_t, &read_selects[read]) =
                sn_tech_memory_bank_select(module, address, address_bits, bank_bits, depth_tile);
    }

    sn_vec_t read_width_results[2];
    for (uint32_t read = 0; read < plan->read_count; read++)
        sn_vec_init(&read_width_results[read]);

    for (uint32_t width_tile = 0; width_tile < plan->width_tiles; width_tile++)
    {
        uint32_t offset = width_tile * plan->port_width;
        uint32_t actual = sn_obj_width(source, plan->memory) - offset;
        if (actual > plan->port_width)
            actual = plan->port_width;
        sn_vec_t bank_results[2];
        for (uint32_t read = 0; read < plan->read_count; read++)
            sn_vec_init(&bank_results[read]);

        for (uint32_t depth_tile = 0; depth_tile < plan->depth_tiles; depth_tile++)
        {
            sn_obj_id_t inputs[8];
            for (uint32_t port = 0; port < 2; port++)
            {
                int8_t write_index = plan->port_writes[port];
                sn_obj_id_t write_data = zero_data;
                if (write_index >= 0)
                {
                    write_data = sn_module_add_slice(module, port_write_data[port],
                                                     (int32_t)(offset + actual - 1),
                                                     (int32_t)offset, NULL);
                    write_data = sn_tech_add_zero_extend(module, write_data, plan->port_width);
                }
                inputs[4 * port + 0] = port_clocks[port];
                inputs[4 * port + 1] = sn_vec_at(sn_obj_id_t, &port_enables[port], depth_tile);
                inputs[4 * port + 2] = port_addresses[port];
                inputs[4 * port + 3] = write_data;
            }
            sn_obj_id_t inst = sn_module_add_inst(module, primitive, 8, inputs, NULL, NULL);
            for (uint32_t port = 0; port < 2; port++)
                if (plan->port_reads[port] >= 0)
                {
                    uint32_t read = (uint32_t)plan->port_reads[port];
                    *sn_vec_push(sn_obj_id_t, &bank_results[read]) = sn_inst_output(module, inst, port);
                }
        }

        for (uint32_t read = 0; read < plan->read_count; read++)
        {
            sn_obj_id_t selected = sn_vec_at(sn_obj_id_t, &bank_results[read], 0);
            for (uint32_t depth_tile = 1; depth_tile < plan->depth_tiles; depth_tile++)
            {
                sn_obj_id_t select = sn_vec_at(sn_obj_id_t, &read_selects[read], depth_tile);
                selected = sn_module_add_mux(module, select,
                                             sn_vec_at(sn_obj_id_t, &bank_results[read], depth_tile), selected, NULL);
            }
            if (actual != plan->port_width)
                selected = sn_module_add_slice(module, selected, (int32_t)(actual - 1), 0, NULL);
            *sn_vec_push(sn_obj_id_t, &read_width_results[read]) = selected;
            sn_vec_destroy(&bank_results[read]);
        }
    }

    for (uint32_t read = 0; read < plan->read_count; read++)
    {
        results[read] = read_width_results[read].size == 1
                            ? sn_vec_at(sn_obj_id_t, &read_width_results[read], 0)
                            : sn_module_add_concat(module, (uint32_t)read_width_results[read].size,
                                                   sn_vec_data(sn_obj_id_t, &read_width_results[read]), NULL);
        sn_vec_destroy(&read_width_results[read]);
        sn_vec_destroy(&read_selects[read]);
    }
    for (uint32_t port = 0; port < 2; port++)
        sn_vec_destroy(&port_enables[port]);
}

static inline sn_module_id_t sn_design_map_tech_internal(sn_design_t* design, sn_module_id_t source_module_id,
                                                         const sn_tech_t* tech,
                                                         const sn_tech_map_options_t* user_options, bool force_copy)
{
    assert(design && tech && source_module_id < design->modules.size);
    sn_tech_map_options_t defaults = sn_tech_map_default_options();
    const sn_tech_map_options_t* options = user_options ? user_options : &defaults;
    sn_module_t* source = sn_design_get_module(design, source_module_id);
    size_t object_count = source->obj_types.size;
    size_t read_count = source->type_objects[SN_MEM_READ].size;
    bool* omit = (bool*)calloc(object_count, sizeof(bool));
    bool* map_mul = (bool*)calloc(object_count, sizeof(bool));
    bool* map_add = (bool*)calloc(object_count, sizeof(bool));
    sn_tech_mem_plan_t* read_plans = (sn_tech_mem_plan_t*)calloc(read_count, sizeof(sn_tech_mem_plan_t));
    assert((!object_count || omit) && (!object_count || map_mul) && (!object_count || map_add) &&
           (!read_count || read_plans));
    for (size_t i = 0; i < read_count; i++)
    {
        memset(&read_plans[i], 0, sizeof(read_plans[i]));
        read_plans[i].memory = SN_INVALID_ID;
    }

    if (options->map_memories)
        for (size_t i = 0; i < source->type_objects[SN_MEM_OUT].size; i++)
        {
            sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_MEM_OUT], i);
            uint64_t bits = (uint64_t)sn_obj_width(source, memory) * sn_obj_mem_depth(source, memory);
            if (bits < options->memory.min_memory_bits || sn_obj_mem_init_data(source, memory) != SN_INVALID_ID)
                continue;
            sn_obj_id_t reads_found[2] = {SN_INVALID_ID, SN_INVALID_ID};
            sn_obj_id_t writes_found[2] = {SN_INVALID_ID, SN_INVALID_ID};
            uint32_t reads = 0, writes = 0;
            for (size_t j = 0; j < source->type_objects[SN_MEM_READ].size; j++)
            {
                sn_obj_id_t candidate = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_MEM_READ], j);
                if (sn_obj_fanin(source, candidate, SN_MEM_READ_MEMORY) == memory)
                {
                    if (reads < 2)
                        reads_found[reads] = candidate;
                    reads++;
                }
            }
            sn_obj_id_t memory_in = sn_obj_pair_in(source, memory);
            for (uint32_t j = 0; j < sn_obj_fanin_count(source, memory_in); j++)
            {
                sn_obj_id_t candidate = sn_obj_fanin(source, memory_in, j);
                if (candidate != SN_INVALID_ID && sn_obj_type(source, candidate) == SN_MEM_WRITE)
                {
                    if (writes < 2)
                        writes_found[writes] = candidate;
                    writes++;
                }
            }
            if (!reads || reads > 2 || !writes || writes > 2)
                continue;
            // A single read with two independent writes needs true-dual-port
            // collision analysis; preserve it until that case is modeled.
            if (reads == 1 && writes != 1)
                continue;
            bool asynchronous_reads = true;
            for (uint32_t read = 0; read < reads; read++)
                asynchronous_reads &= sn_obj_fanin(source, reads_found[read], SN_MEM_READ_CLOCK) == SN_INVALID_ID &&
                                      sn_obj_fanin(source, reads_found[read], SN_MEM_READ_ENABLE) == SN_INVALID_ID;
            if (!asynchronous_reads)
                continue;
            sn_tech_mem_plan_t plan = {0};
            plan.memory = memory;
            plan.memory_in = memory_in;
            plan.read = reads_found[0];
            plan.write = writes_found[0];
            plan.read_count = reads;
            plan.write_count = writes;
            for (uint32_t read = 0; read < reads; read++)
                plan.reads[read] = reads_found[read];
            for (uint32_t write = 0; write < writes; write++)
                plan.writes[write] = writes_found[write];
            if (!sn_tech_choose_memory_for_mode(tech, sn_obj_width(source, memory),
                                                sn_obj_mem_depth(source, memory), &options->memory,
                                                reads == 1 && writes == 1, &plan))
                continue;
            if (reads > 1 && (!plan.primitive || plan.primitive->port_mode != SN_MEM_PORT_TRUE_DUAL ||
                              !sn_tech_assign_tdp_ports(source, &plan)))
                continue;
            for (uint32_t read = 0; read < reads; read++)
                read_plans[sn_obj_type_id(source, reads_found[read])] = plan;
            omit[memory] = omit[memory_in] = true;
            for (uint32_t write = 0; write < writes; write++)
                omit[writes_found[write]] = true;
        }

    if (options->map_multipliers)
    {
        assert(tech->dsp_count);
        const sn_dsp_tech_t* dsp = &tech->dsps[0];
        bool mapping_failed = false;
        for (size_t i = 0; i < source->type_objects[SN_MUL].size; i++)
        {
            sn_obj_id_t mul = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_MUL], i);
            sn_obj_id_t a = sn_obj_fanin(source, mul, 0);
            sn_obj_id_t b = sn_obj_fanin(source, mul, 1);
            uint32_t count = sn_tech_dsp_box_count(source, dsp, &options->dsp, a, b);
            map_mul[mul] = count != UINT32_MAX &&
                           (!options->dsp.max_dsps_per_multiply ||
                            count <= options->dsp.max_dsps_per_multiply);
            mapping_failed |= !map_mul[mul] && !options->dsp.allow_soft_fallback;
        }
        if (mapping_failed)
        {
            free(omit);
            free(map_mul);
            free(map_add);
            free(read_plans);
            return SN_INVALID_ID;
        }
    }

    if (options->map_adders)
    {
        assert(tech->carry_count);
        const sn_carry_tech_t* carry = &tech->carries[0];
        for (sn_obj_id_t object = 0; object < object_count; object++)
            map_add[object] = sn_add_tech_supports(carry, &options->add, sn_obj_type(source, object),
                                                   sn_obj_width(source, object));
    }

    bool changed = false;
    for (sn_obj_id_t object = 0; object < object_count && !changed; object++)
    {
        const sn_tech_mem_plan_t* read_plan = sn_tech_read_plan(source, read_plans, object);
        changed = omit[object] || map_mul[object] || map_add[object] ||
                  (read_plan && read_plan->memory != SN_INVALID_ID);
    }
    if (!changed && !force_copy)
    {
        free(omit);
        free(map_mul);
        free(map_add);
        free(read_plans);
        return source_module_id;
    }

    const char* source_name = sn_name_get(&design->names, source->name);
    char mapped_name[256];
    int length = snprintf(mapped_name, sizeof(mapped_name), "%s_techmap", source_name);
    assert(length >= 0 && (size_t)length < sizeof(mapped_name));
    for (uint32_t suffix = 1; sn_design_find_module(design, mapped_name) != SN_INVALID_ID; suffix++)
    {
        length = snprintf(mapped_name, sizeof(mapped_name), "%s_techmap_%u", source_name, suffix);
        assert(length >= 0 && (size_t)length < sizeof(mapped_name));
    }
    sn_module_id_t mapped_id = sn_design_add_module(design, mapped_name);
    sn_module_t* mapped = sn_design_get_module(design, mapped_id);
    sn_vec_t order = sn_module_topo_order(source);
    sn_vec_resize(sn_obj_id_t, &source->copy_ids, object_count);
    for (size_t i = 0; i < object_count; i++)
        sn_vec_at(sn_obj_id_t, &source->copy_ids, i) = SN_INVALID_ID;

    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        if (omit[old_object])
            continue;
        bool special_mul = map_mul[old_object];
        const sn_tech_mem_plan_t* read_plan = sn_tech_read_plan(source, read_plans, old_object);
        bool special_mem = read_plan && read_plan->memory != SN_INVALID_ID;
        bool special_add = map_add[old_object];
        sn_obj_id_t new_object = special_mul || special_mem || special_add
                                     ? sn_module_add_obj(mapped, SN_BUF, sn_obj_width(source, old_object),
                                                         sn_obj_is_signed(source, old_object), 1,
                                                         sn_obj_name_id(source, old_object))
                                     : sn_module_dup_obj_skeleton(mapped, source, old_object);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = new_object;
    }

    // Topological traversal can order paired IN objects differently from their
    // source-order OUT objects. Restore matching type IDs before metadata and
    // fanins are copied so state pairs remain paired in the provisional graph.
    sn_module_clean_rebuild_pair_ids(mapped, source, SN_REG_OUT, SN_REG_IN);
    sn_module_clean_rebuild_pair_ids(mapped, source, SN_MEM_OUT, SN_MEM_IN);
    sn_module_clean_rebuild_pair_ids(mapped, source, SN_LOOP_OUT, SN_LOOP_IN);

    const sn_dsp_tech_t* dsp = tech->dsp_count ? &tech->dsps[0] : NULL;
    const sn_carry_tech_t* carry = tech->carry_count ? &tech->carries[0] : NULL;
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t placeholder = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        const sn_tech_mem_plan_t* read_plan = sn_tech_read_plan(source, read_plans, old_object);
        if (placeholder == SN_INVALID_ID)
            continue;
        if (map_mul[old_object])
        {
            assert(dsp && sn_obj_fanin_count(source, old_object) == 2);
            sn_obj_id_t a = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, old_object, 0));
            sn_obj_id_t b = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, old_object, 1));
            sn_obj_id_t result = sn_tech_map_multiplier(mapped, dsp, &options->dsp, a, b,
                                                        sn_obj_width(source, old_object),
                                                        sn_obj_is_signed(source, old_object));
            sn_obj_connect(mapped, placeholder, 0, result);
        }
        else if (map_add[old_object])
        {
            assert(carry && sn_obj_fanin_count(source, old_object) == 2);
            sn_obj_id_t a = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, old_object, 0));
            sn_obj_id_t b = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, old_object, 1));
            const char* name = sn_obj_name_id(source, old_object) == SN_INVALID_ID ? NULL
                                                                                  : sn_obj_name(source, old_object);
            sn_obj_id_t result = sn_add_map_carry_chain(
                mapped, carry, sn_obj_type(source, old_object), a, b, sn_obj_width(source, old_object),
                sn_obj_is_signed(source, old_object), name);
            sn_obj_connect(mapped, placeholder, 0, result);
        }
        else if (read_plan && read_plan->memory != SN_INVALID_ID)
        {
            const sn_tech_mem_plan_t* plan = read_plan;
            if (plan->read_count == 1)
            {
                sn_obj_id_t result = sn_tech_map_memory(mapped, source, plan, &options->memory);
                sn_obj_connect(mapped, placeholder, 0, result);
            }
            else if (old_object == plan->reads[0])
            {
                sn_obj_id_t results[2];
                sn_tech_map_tdp_memory(mapped, source, plan, results);
                for (uint32_t read = 0; read < plan->read_count; read++)
                {
                    sn_obj_id_t read_placeholder =
                        sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->reads[read]);
                    sn_obj_connect(mapped, read_placeholder, 0, results[read]);
                }
            }
        }
    }

    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        const sn_tech_mem_plan_t* read_plan = sn_tech_read_plan(source, read_plans, old_object);
        bool special = map_mul[old_object] || map_add[old_object] ||
                       (read_plan && read_plan->memory != SN_INVALID_ID);
        if (new_object == SN_INVALID_ID || special)
            continue;
        sn_module_dup_obj_metadata(mapped, sn_obj_type_id(mapped, new_object), source, old_object);
        if (sn_obj_type(source, old_object) == SN_FAN)
        {
            sn_obj_id_t old_inst = sn_fan_inst_id(source, old_object);
            sn_vec_at(sn_obj_id_t, &mapped->fan_insts, sn_obj_type_id(mapped, new_object)) =
                sn_vec_at(sn_obj_id_t, &source->copy_ids, old_inst);
        }
        for (uint32_t j = 0; j < sn_obj_fanin_count(source, old_object); j++)
        {
            sn_obj_id_t old_fanin = sn_obj_fanin(source, old_object, j);
            sn_obj_id_t new_fanin = old_fanin == SN_INVALID_ID
                                        ? SN_INVALID_ID
                                        : sn_vec_at(sn_obj_id_t, &source->copy_ids, old_fanin);
            assert(new_fanin != SN_INVALID_ID || old_fanin == SN_INVALID_ID);
            sn_obj_connect(mapped, new_object, j, new_fanin);
        }
    }

    // Finalize the provisional graph and compose its reorder map with the
    // persistent source-to-mapped copy array.
    char temporary_name[96];
    uint32_t temporary_suffix = 0;
    do
    {
        length = snprintf(temporary_name, sizeof(temporary_name), "__sn_tech_topo_%u_%u", mapped_id,
                          temporary_suffix++);
        assert(length >= 0 && (size_t)length < sizeof(temporary_name) && temporary_suffix != 0);
    } while (sn_name_find(&design->names, temporary_name) != SN_INVALID_ID);
    sn_module_id_t final_id = sn_design_dup_module_topo(design, mapped_id, temporary_name);
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

    free(omit);
    free(map_mul);
    free(map_add);
    free(read_plans);
    sn_vec_destroy(&order);
    return mapped_id;
}

static inline sn_module_id_t sn_design_map_tech(sn_design_t* design, sn_module_id_t source_module_id,
                                                const sn_tech_t* tech, const sn_tech_map_options_t* user_options)
{
    return sn_design_map_tech_internal(design, source_module_id, tech, user_options, false);
}

typedef struct sn_tech_count_frame_t
{
    sn_module_id_t module;
    size_t next_inst;
} sn_tech_count_frame_t;

static inline void sn_tech_count_hierarchy_instances(const sn_design_t* design, sn_module_id_t root,
                                                      sn_tech_map_stats_t* stats)
{
    size_t module_count = design->modules.size;
    uint8_t* states = (uint8_t*)calloc(module_count, 1);
    sn_tech_map_stats_t* cached = (sn_tech_map_stats_t*)calloc(module_count, sizeof(sn_tech_map_stats_t));
    sn_vec_t stack;
    assert(design && root < module_count && stats && states && cached);
    sn_vec_init(&stack);
    states[root] = 1;
    sn_tech_count_frame_t* first = sn_vec_push(sn_tech_count_frame_t, &stack);
    first->module = root;
    first->next_inst = 0;
    while (stack.size)
    {
        sn_tech_count_frame_t* frame = &sn_vec_at(sn_tech_count_frame_t, &stack, stack.size - 1);
        const sn_module_t* module = sn_design_get_module_const(design, frame->module);
        if (frame->next_inst < module->inst_modules.size)
        {
            sn_module_id_t child_id = sn_vec_at(sn_module_id_t, &module->inst_modules, frame->next_inst++);
            const sn_module_t* child = sn_design_get_module_const(design, child_id);
            if (!sn_module_is_technology_primitive(child) && states[child_id] == 0)
            {
                states[child_id] = 1;
                sn_tech_count_frame_t* child_frame = sn_vec_push(sn_tech_count_frame_t, &stack);
                child_frame->module = child_id;
                child_frame->next_inst = 0;
            }
            continue;
        }
        sn_tech_map_stats_t total = {0};
        for (size_t i = 0; i < module->inst_modules.size; i++)
        {
            sn_module_id_t child_id = sn_vec_at(sn_module_id_t, &module->inst_modules, i);
            const sn_module_t* child = sn_design_get_module_const(design, child_id);
            const char* name = sn_name_get(&design->names, child->name);
            if (strncmp(name, "__sn_RAM", 8) == 0 || strncmp(name, "__sn_URAM", 9) == 0)
                total.mem_insts++;
            else if (strncmp(name, "__sn_DSP", 8) == 0)
                total.dsp_insts++;
            else if (strncmp(name, "__sn_CARRY", 10) == 0)
                total.carry_insts++;
            else
            {
                total.mem_insts += cached[child_id].mem_insts;
                total.dsp_insts += cached[child_id].dsp_insts;
                total.carry_insts += cached[child_id].carry_insts;
            }
        }
        cached[frame->module] = total;
        states[frame->module] = 2;
        stack.size--;
    }
    *stats = cached[root];
    sn_vec_destroy(&stack);
    free(cached);
    free(states);
}

typedef struct sn_tech_hierarchy_frame_t
{
    sn_module_id_t module;
    size_t next_inst;
} sn_tech_hierarchy_frame_t;

// Visits the reachable hierarchy bottom-up. A module is copied only when it contains a primitive selected by this
// pass or when one of its child definitions changed and its instance reference must be redirected. Untouched
// subhierarchies retain their original module IDs. The original definitions remain in the design.
static inline sn_module_id_t sn_design_map_tech_hierarchy(sn_design_t* design, sn_module_id_t top_id,
                                                          const sn_tech_t* tech,
                                                          const sn_tech_map_options_t* options,
                                                          sn_tech_map_stats_t* returned_stats)
{
    assert(design && top_id < design->modules.size && tech && options);
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
    sn_tech_hierarchy_frame_t* root = sn_vec_push(sn_tech_hierarchy_frame_t, &stack);
    root->module = top_id;
    root->next_inst = 0;
    while (stack.size)
    {
        sn_tech_hierarchy_frame_t* frame = &sn_vec_at(sn_tech_hierarchy_frame_t, &stack, stack.size - 1);
        const sn_module_t* module = sn_design_get_module_const(design, frame->module);
        if (frame->next_inst < module->inst_modules.size)
        {
            sn_module_id_t child = sn_vec_at(sn_module_id_t, &module->inst_modules, frame->next_inst++);
            assert(child < original_count);
            assert(states[child] != 1 && "recursive module instantiation is unsupported");
            if (states[child] == 0)
            {
                states[child] = 1;
                sn_tech_hierarchy_frame_t* child_frame = sn_vec_push(sn_tech_hierarchy_frame_t, &stack);
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
        for (size_t i = 0; i < module->inst_modules.size; i++)
        {
            sn_module_id_t child = sn_vec_at(sn_module_id_t, &module->inst_modules, i);
            child_changed |= replacements[child] != child;
        }
        replacements[id] = sn_design_map_tech_internal(design, id, tech, options, child_changed);
        if (replacements[id] == SN_INVALID_ID)
        {
            for (sn_module_id_t appended = (sn_module_id_t)original_count;
                 appended < design->modules.size; appended++)
            {
                sn_module_t* discarded = sn_design_get_module(design, appended);
                sn_module_destroy(discarded);
                free(discarded);
            }
            design->modules.size = original_count;
            for (sn_module_id_t reachable = 0; reachable < original_count; reachable++)
                if (states[reachable])
                {
                    sn_module_t* original = sn_design_get_module(design, reachable);
                    sn_vec_destroy(&original->copy_ids);
                    sn_vec_init(&original->copy_ids);
                    original->copy_module = SN_INVALID_ID;
                }
            sn_vec_destroy(&postorder);
            sn_vec_destroy(&stack);
            free(states);
            free(replacements);
            if (returned_stats)
                memset(returned_stats, 0, sizeof(*returned_stats));
            return SN_INVALID_ID;
        }
        if (replacements[id] == id)
            continue;
        sn_module_t* mapped = sn_design_get_module(design, replacements[id]);
        for (size_t i = 0; i < mapped->inst_modules.size; i++)
        {
            sn_module_id_t child = sn_vec_at(sn_module_id_t, &mapped->inst_modules, i);
            if (child < original_count)
                sn_vec_at(sn_module_id_t, &mapped->inst_modules, i) = replacements[child];
        }
    }

    sn_tech_map_stats_t stats = {0};
    sn_module_id_t result = replacements[top_id];
    sn_tech_count_hierarchy_instances(design, result, &stats);
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
