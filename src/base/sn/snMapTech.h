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
#include "snMapDff.h"
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
    bool map_shift_registers;
    sn_mem_map_options_t memory;
    sn_dsp_map_options_t dsp;
    sn_add_map_options_t add;
} sn_tech_map_options_t;

// Mapping a memory into an atomic instance can introduce a parent-level cycle
// through its write pins, even though the memory's read-to-write feedback is
// sequential. Preserve the connection with an explicit ordering boundary, just
// as the frontend does for feedback through retained hierarchy. Do not cut
// feed-forward instance connections.
static inline void sn_tech_break_inst_cycles(sn_module_t* module)
{
    size_t object_count = module->obj_types.size;
    size_t* visited = (size_t*)calloc(object_count, sizeof(size_t));
    assert(visited || !object_count);
    size_t epoch = 0;
    sn_vec_t stack;
    sn_vec_init(&stack);
    for (sn_obj_id_t inst = 0; inst < object_count; inst++)
    {
        if (sn_obj_type(module, inst) != SN_INST)
            continue;
        for (uint32_t pin = 0; pin < sn_obj_fanin_count(module, inst); pin++)
        {
            sn_obj_id_t input = sn_obj_fanin(module, inst, pin);
            if (++epoch == 0)
            {
                memset(visited, 0, object_count * sizeof(size_t));
                epoch = 1;
            }
            stack.size = 0;
            *sn_vec_push(sn_obj_id_t, &stack) = input;
            bool feedback = false;
            while (stack.size && !feedback)
            {
                sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &stack, --stack.size);
                // Newly created objects are loop boundaries and cannot lead back to the instance.
                if (object == SN_INVALID_ID || object >= object_count || visited[object] == epoch)
                    continue;
                visited[object] = epoch;
                if (object == inst)
                {
                    feedback = true;
                    break;
                }
                if (sn_obj_type_is_pair_out(sn_obj_type(module, object)))
                    continue;
                for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
                    *sn_vec_push(sn_obj_id_t, &stack) = sn_obj_fanin(module, object, i);
            }
            if (feedback)
            {
                sn_obj_pair_t loop = sn_module_add_loop_pair(module, sn_obj_width(module, input),
                                                             sn_obj_is_signed(module, input), NULL, NULL);
                sn_obj_connect(module, loop.in, 0, input);
                sn_obj_connect(module, inst, pin, loop.out);
            }
        }
    }
    sn_vec_destroy(&stack);
    free(visited);
}

typedef struct sn_tech_map_stats_t
{
    size_t mem_insts;
    size_t dsp_insts;
    size_t carry_insts;
    size_t srl_insts;
} sn_tech_map_stats_t;

// One collapsed addition tree: its leaves live in shared vectors.
typedef struct sn_tech_csa_plan_t
{
    uint32_t begin;
    uint32_t count;
} sn_tech_csa_plan_t;

// One recognized shift-register memory, recorded on every external tap
// read; the primitive instance is built once and shared by all taps.
#define SN_TECH_SRL_MAX_TAPS 4

typedef struct sn_tech_srl_plan_t
{
    sn_obj_id_t memory;
    sn_obj_id_t din;
    sn_obj_id_t clock;
    sn_obj_id_t enable;
    uint32_t depth;
    uint32_t tap_count;
    uint32_t tap_index;
    sn_obj_id_t taps[SN_TECH_SRL_MAX_TAPS];
    // A valid tap register absorbs into the primitive as a registered tap,
    // the shift-register-with-output-flop form FPGA synthesis packs into
    // one LUT site.
    sn_obj_id_t tap_regs[SN_TECH_SRL_MAX_TAPS];
    sn_obj_id_t tap_clocks[SN_TECH_SRL_MAX_TAPS];
    sn_obj_id_t tap_enables[SN_TECH_SRL_MAX_TAPS];
} sn_tech_srl_plan_t;

// One recognized fixed register shift chain, recorded on its tail register.
typedef struct sn_tech_srlreg_plan_t
{
    sn_obj_id_t din;
    sn_obj_id_t clock;
    sn_obj_id_t enable;
    uint32_t depth;
    bool negedge;
} sn_tech_srlreg_plan_t;

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
    // A valid read clock selects a registered-read tile: that read port is
    // synchronous with its clock and optional enable, either because the
    // source read is clocked or because its single external read register
    // was absorbed. Dual-port plans register either both reads or neither.
    sn_obj_id_t read_clocks[2];
    sn_obj_id_t read_enables[2];
    sn_obj_id_t absorbed_regs[2];
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
    return sn_obj_type(module, object) == SN_MEM_READ ? &plans[sn_obj_data(module, object)] : NULL;
}

static inline sn_tech_map_options_t sn_tech_map_default_options(void)
{
    sn_tech_map_options_t options;
    options.map_memories = true;
    options.map_multipliers = true;
    options.map_adders = false;
    options.map_shift_registers = false;
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

// Chooses between full-port chunking with fabric sign corrections and one-
// bit-narrower zero-extended chunking with none. Zero extension wins unless
// it costs additional DSP boxes; ties favor removing the correction logic.
static inline uint32_t sn_tech_dsp_mode_count(uint32_t a_width, uint32_t b_width, const sn_dsp_tech_t* dsp,
                                              uint32_t a_low, uint32_t b_low)
{
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

static inline uint32_t sn_tech_dsp_box_count(const sn_module_t* module, const sn_dsp_tech_t* dsp,
                                             const sn_dsp_map_options_t* options, sn_obj_id_t a, sn_obj_id_t b)
{
    bool signed_operands = sn_obj_is_signed(module, a) && sn_obj_is_signed(module, b);
    uint32_t a_width = sn_obj_width(module, a) + !signed_operands;
    uint32_t b_width = sn_obj_width(module, b) + !signed_operands;
    uint32_t a_corr = options->a_unsigned_chunk_width ? options->a_unsigned_chunk_width : dsp->a_width;
    uint32_t b_corr = options->b_unsigned_chunk_width ? options->b_unsigned_chunk_width : dsp->b_width;
    uint32_t a_ze = options->a_unsigned_chunk_width ? options->a_unsigned_chunk_width : dsp->a_width - 1;
    uint32_t b_ze = options->b_unsigned_chunk_width ? options->b_unsigned_chunk_width : dsp->b_width - 1;
    if (a_corr < dsp->min_a_width || a_corr > dsp->a_width || b_corr < dsp->min_b_width || b_corr > dsp->b_width)
        return UINT32_MAX;
    uint32_t corrected = sn_tech_dsp_mode_count(a_width, b_width, dsp, a_corr, b_corr);
    uint32_t extended = a_ze >= dsp->min_a_width && b_ze >= dsp->min_b_width
                            ? sn_tech_dsp_mode_count(a_width, b_width, dsp, a_ze, b_ze)
                            : UINT32_MAX;
    return corrected < extended ? corrected : extended;
}

// In zero-extension mode a non-top chunk holds unsigned payload bits of a
// signed operand and is widened by one bit into the signed DSP port, making
// its signed product exact with no gated sign-correction terms; non-top
// chunks are then at most one bit narrower than the port. Otherwise chunks
// fill the full port and every non-top chunk contributes correction terms.
// The caller picks the mode that needs the fewest DSP boxes.
static inline void sn_tech_dsp_make_chunks(sn_module_t* module, sn_obj_id_t value, uint32_t port_width,
                                           uint32_t low_width, uint32_t min_width, bool zero_extend,
                                           sn_vec_t* chunks)
{
    assert(module && chunks);
    assert(!zero_extend || low_width < port_width || low_width == 1);
    uint32_t width = sn_obj_width(module, value);
    uint32_t count = sn_tech_dsp_chunk_count(width, port_width, low_width, min_width);
    assert(count != UINT32_MAX);
    uint32_t offset = 0, remaining = width;
    for (uint32_t i = 0; i < count; i++)
    {
        bool top = i + 1 == count;
        uint32_t chunk_width = remaining <= port_width ? remaining : low_width;
        if (remaining > port_width && remaining - chunk_width < min_width)
            chunk_width = remaining - min_width;
        assert(chunk_width >= min_width && chunk_width <= port_width);
        sn_obj_id_t chunk = count == 1
                                ? value
                                : sn_module_add_slice(module, value, (int32_t)(offset + chunk_width - 1),
                                                      (int32_t)offset, NULL);
        if (zero_extend && !top)
        {
            assert(chunk_width < port_width);
            chunk = sn_tech_add_zero_extend(module, sn_tech_add_cast(module, chunk, chunk_width, false),
                                            chunk_width + 1);
        }
        chunk = sn_tech_add_cast(module, chunk, sn_obj_width(module, chunk), true);
        sn_tech_dsp_chunk_t* entry = sn_vec_push(sn_tech_dsp_chunk_t, chunks);
        entry->object = chunk;
        entry->offset = offset;
        entry->unsigned_correction = !zero_extend && !top;
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

// Maps one multiplication into DSP primitive insts, optionally adding the
// caller's accumulate value into the result exactly (modulo 2^result_width).
// When the result fits the DSP's product width, aligned partial products
// chain through multiply-accumulate primitives via the post-adder input, so
// a multi-DSP multiplier and an absorbed external addend cost no fabric
// adders. Wider results fall back to an explicit balanced adder tree.
static inline sn_obj_id_t sn_tech_map_multiplier(sn_module_t* module, const sn_dsp_tech_t* dsp,
                                                 const sn_dsp_map_options_t* options, sn_obj_id_t a,
                                                 sn_obj_id_t b, uint32_t result_width, bool result_signed,
                                                 sn_obj_id_t accumulate)
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

    uint32_t a_corr = options->a_unsigned_chunk_width ? options->a_unsigned_chunk_width : dsp->a_width;
    uint32_t b_corr = options->b_unsigned_chunk_width ? options->b_unsigned_chunk_width : dsp->b_width;
    uint32_t a_ze = options->a_unsigned_chunk_width ? options->a_unsigned_chunk_width : dsp->a_width - 1;
    uint32_t b_ze = options->b_unsigned_chunk_width ? options->b_unsigned_chunk_width : dsp->b_width - 1;
    assert(a_corr <= dsp->a_width && b_corr <= dsp->b_width);
    uint32_t corrected = sn_tech_dsp_mode_count(sn_obj_width(module, a), sn_obj_width(module, b), dsp,
                                                a_corr, b_corr);
    uint32_t extended = a_ze >= dsp->min_a_width && b_ze >= dsp->min_b_width
                            ? sn_tech_dsp_mode_count(sn_obj_width(module, a), sn_obj_width(module, b), dsp,
                                                     a_ze, b_ze)
                            : UINT32_MAX;
    bool zero_extend = extended <= corrected;
    uint32_t a_low = zero_extend ? a_ze : a_corr;
    uint32_t b_low = zero_extend ? b_ze : b_corr;
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
    sn_tech_dsp_make_chunks(module, a, dsp->a_width, a_low, dsp->min_a_width, zero_extend, &a_chunks);
    sn_tech_dsp_make_chunks(module, b, dsp->b_width, b_low, dsp->min_b_width, zero_extend, &b_chunks);
    assert(!options->max_dsps_per_multiply ||
           a_chunks.size * b_chunks.size <= options->max_dsps_per_multiply);

    // The DSP post-adder chains partial products through the C input, so the
    // multi-DSP sum and any absorbed external addend need no fabric adders.
    // The chain requires every intermediate sum to fit the DSP product
    // width; a wider result keeps the explicit adder tree below.
    bool chain = dsp->has_postadder && options->use_postadder && result_width <= dsp->p_width;
    sn_obj_id_t running = SN_INVALID_ID;
    if (accumulate != SN_INVALID_ID)
    {
        // Widen the addend by its own signedness first; the equal-width
        // reinterpretation as signed then matches the chain arithmetic.
        running = sn_tech_add_cast(module, accumulate, result_width, sn_obj_is_signed(module, accumulate));
        running = sn_tech_add_cast(module, running, result_width, true);
        if (!chain)
        {
            *sn_vec_push(sn_obj_id_t, &partials) = running;
            running = SN_INVALID_ID;
        }
    }

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
            if (chain && running != SN_INVALID_ID)
            {
                sn_module_id_t primitive = sn_map_dsp_mac_primitive_module(
                    module->design, dsp, sn_obj_width(module, ac->object), sn_obj_width(module, bc->object),
                    primitive_width, shift, result_width);
                sn_obj_id_t inputs[3] = {ac->object, bc->object, running};
                sn_obj_id_t inst = sn_module_add_inst(module, primitive, 3, inputs, NULL, NULL);
                running = sn_inst_output(module, inst, 0);
            }
            else
            {
                sn_module_id_t primitive = sn_map_dsp_primitive_module(
                    module->design, dsp, sn_obj_width(module, ac->object), sn_obj_width(module, bc->object),
                    primitive_width, true, true);
                sn_obj_id_t inputs[2] = {ac->object, bc->object};
                sn_obj_id_t product = sn_module_add_inst(module, primitive, 2, inputs, NULL, NULL);
                if (chain)
                    running = sn_tech_dsp_align(module, product, result_width, shift, true);
                else
                    *sn_vec_push(sn_obj_id_t, &partials) =
                        sn_tech_dsp_align(module, product, result_width, shift, true);
            }

            // Full-port chunking makes a non-top chunk unsigned even though the DSP input is signed. For a
            // W-bit chunk U, U = signed(U) + msb(U)*2^W. Add the resulting one-bit-gated correction terms
            // around the signed DSP product; they later combine through the explicit adder tree.
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

    if (chain && running != SN_INVALID_ID)
        *sn_vec_push(sn_obj_id_t, &partials) = running;
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

// Hash of a tile's initialization image, used to give each distinct ROM
// content its own primitive module name.
static inline uint64_t sn_tech_init_hash(const uint32_t* words, uint32_t word_count)
{
    uint64_t hash = UINT64_C(1469598103934665603);
    for (uint32_t i = 0; i < word_count; i++)
        hash = (hash ^ words[i]) * UINT64_C(1099511628211);
    return hash;
}

// Builds the packed initialization image of one tile: entries
// [bank*tile_depth, bank*tile_depth + tile_depth) sliced to bits
// [width_offset, width_offset + port_width). Masked-off and out-of-range
// bits are zero, SN's two-state value of uninitialized storage. Returns NULL
// when the memory carries no initialization.
static inline uint32_t* sn_tech_tile_init_words(const sn_module_t* source, sn_obj_id_t memory,
                                                uint32_t width_offset, uint32_t port_width, uint32_t bank,
                                                uint32_t tile_depth)
{
    sn_obj_id_t data = sn_obj_mem_init_data(source, memory);
    if (data == SN_INVALID_ID)
        return NULL;
    sn_obj_id_t mask = sn_obj_mem_init_mask(source, memory);
    uint32_t mem_width = sn_obj_width(source, memory);
    uint32_t depth = sn_obj_mem_depth(source, memory);
    uint32_t bits = port_width * tile_depth;
    uint32_t* words = (uint32_t*)calloc(sn_const_word_count(bits), sizeof(uint32_t));
    assert(words);
    for (uint32_t entry = 0; entry < tile_depth; entry++)
    {
        uint64_t global_entry = (uint64_t)bank * tile_depth + entry;
        if (global_entry >= depth)
            continue;
        for (uint32_t bit = 0; bit < port_width; bit++)
        {
            uint32_t global_bit = width_offset + bit;
            if (global_bit >= mem_width)
                continue;
            uint32_t index = (uint32_t)(global_entry * mem_width + global_bit);
            if (!sn_const_bit(source, data, index))
                continue;
            if (mask != SN_INVALID_ID && !sn_const_bit(source, mask, index))
                continue;
            uint32_t local = entry * port_width + bit;
            words[local / 32] |= 1u << (local % 32);
        }
    }
    return words;
}

// Attaches an initialization image to a freshly built tile module and
// verifies a cache-hit module carries the same image.
static inline bool sn_tech_tile_init_matches(const sn_module_t* module, const uint32_t* words, uint32_t bits)
{
    sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_OUT], 0);
    sn_obj_id_t data = sn_obj_mem_init_data(module, memory);
    if ((data == SN_INVALID_ID) != (words == NULL))
        return false;
    if (words == NULL)
        return true;
    for (uint32_t bit = 0; bit < bits; bit++)
        if (sn_const_bit(module, data, bit) != (((words[bit / 32] >> (bit % 32)) & 1u) != 0))
            return false;
    return true;
}

// Finds an existing tile module with this name and the same initialization
// image, probing past hash collisions; SN_INVALID_ID means build a new one
// under the final name.
static inline sn_module_id_t sn_tech_tile_find(sn_design_t* design, char* name, size_t name_size, int length,
                                               const uint32_t* init_words, uint32_t bits)
{
    for (uint32_t bump = 0;; bump++)
    {
        sn_module_id_t existing = sn_design_find_module(design, name);
        if (existing == SN_INVALID_ID)
            return SN_INVALID_ID;
        if (sn_tech_tile_init_matches(sn_design_get_module_const(design, existing), init_words, bits))
            return existing;
        int added = snprintf(name + length, name_size - (size_t)length, "_c%u", bump);
        assert(added > 0 && (size_t)length + (size_t)added < name_size);
    }
}

static inline sn_module_id_t sn_tech_memory_tile_module(sn_design_t* design, const sn_mem_tech_t* primitive,
                                                         uint32_t width, uint32_t depth,
                                                        const uint32_t* init_words)
{
    uint32_t address_width = sn_tech_ceil_log2(depth);
    char name[192];
    int length = snprintf(name, sizeof(name), "__sn_%s_tile_%u_%u", primitive->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    if (init_words)
    {
        int added = snprintf(name + length, sizeof(name) - (size_t)length, "_i%016llx",
                             (unsigned long long)sn_tech_init_hash(init_words,
                                                                   sn_const_word_count(width * depth)));
        assert(added > 0 && (size_t)length + (size_t)added < sizeof(name));
        length += added;
    }
    sn_module_id_t existing = sn_tech_tile_find(design, name, sizeof(name), length, init_words, width * depth);
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
    if (init_words)
    {
        sn_obj_id_t init_data = sn_module_add_const(module, width * depth, false, init_words, NULL);
        sn_mem_set_init(module, pair.out, init_data, SN_INVALID_ID);
    }
    sn_module_add_mem_write(module, pair.in, clock, enable, data, write_address, "write");
    sn_obj_id_t read = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, read_address, "read");
    sn_module_add_po(module, width, false, "read_data", read);
    sn_design_reorder_module_topo(design, id);
    return id;
}

// Registered-read tile: the read port is synchronous with its own clock and
// enable, matching the physical primitive's registered output port, so the
// external read register it absorbs disappears from the fabric.
static inline sn_module_id_t sn_tech_memory_rtile_module(sn_design_t* design, const sn_mem_tech_t* primitive,
                                                         uint32_t width, uint32_t depth,
                                                         const uint32_t* init_words)
{
    uint32_t address_width = sn_tech_ceil_log2(depth);
    char name[192];
    int length = snprintf(name, sizeof(name), "__sn_%s_rtile_%u_%u", primitive->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    if (init_words)
    {
        int added = snprintf(name + length, sizeof(name) - (size_t)length, "_i%016llx",
                             (unsigned long long)sn_tech_init_hash(init_words,
                                                                   sn_const_word_count(width * depth)));
        assert(added > 0 && (size_t)length + (size_t)added < sizeof(name));
        length += added;
    }
    sn_module_id_t existing = sn_tech_tile_find(design, name, sizeof(name), length, init_words, width * depth);
    if (existing != SN_INVALID_ID)
        return existing;
    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock = sn_module_add_pi(module, 1, false, "clock");
    sn_obj_id_t enable = sn_module_add_pi(module, 1, false, "enable");
    sn_obj_id_t write_address = sn_module_add_pi(module, address_width, false, "write_address");
    sn_obj_id_t data = sn_module_add_pi(module, width, false, "write_data");
    sn_obj_id_t read_clock = sn_module_add_pi(module, 1, false, "read_clock");
    sn_obj_id_t read_enable = sn_module_add_pi(module, 1, false, "read_enable");
    sn_obj_id_t read_address = sn_module_add_pi(module, address_width, false, "read_address");
    sn_obj_pair_t pair = sn_module_add_mem_pair(module, width, false, depth, "mem_out", "mem_in");
    if (init_words)
    {
        sn_obj_id_t init_data = sn_module_add_const(module, width * depth, false, init_words, NULL);
        sn_mem_set_init(module, pair.out, init_data, SN_INVALID_ID);
    }
    sn_module_add_mem_write(module, pair.in, clock, enable, data, write_address, "write");
    sn_obj_id_t read = sn_module_add_mem_read(module, pair.out, read_clock, read_enable, read_address, "read");
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
                                                            uint32_t width, uint32_t depth,
                                                            const uint32_t* init_words)
{
    uint32_t address_width = sn_tech_ceil_log2(depth);
    char name[192];
    int length = snprintf(name, sizeof(name), "__sn_%s_tdp_tile_%u_%u", primitive->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    if (init_words)
    {
        int added = snprintf(name + length, sizeof(name) - (size_t)length, "_i%016llx",
                             (unsigned long long)sn_tech_init_hash(init_words,
                                                                   sn_const_word_count(width * depth)));
        assert(added > 0 && (size_t)length + (size_t)added < sizeof(name));
        length += added;
    }
    sn_module_id_t existing = sn_tech_tile_find(design, name, sizeof(name), length, init_words, width * depth);
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
    if (init_words)
    {
        sn_obj_id_t init_data = sn_module_add_const(module, width * depth, false, init_words, NULL);
        sn_mem_set_init(module, pair.out, init_data, SN_INVALID_ID);
    }
    sn_module_add_mem_write(module, pair.in, clock[0], write_enable[0], data[0], address[0], "write_a");
    sn_module_add_mem_write(module, pair.in, clock[1], write_enable[1], data[1], address[1], "write_b");
    sn_obj_id_t read_a = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, address[0], "read_a");
    sn_obj_id_t read_b = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, address[1], "read_b");
    sn_module_add_po(module, width, false, "read_data_a", read_a);
    sn_module_add_po(module, width, false, "read_data_b", read_b);
    sn_design_reorder_module_topo(design, id);
    return id;
}

// Registered-read true-dual-port tile: each port's read is synchronous with
// the port clock under its own read enable, matching the physical
// primitive's registered output ports.
static inline sn_module_id_t sn_tech_memory_rtdp_tile_module(sn_design_t* design, const sn_mem_tech_t* primitive,
                                                             uint32_t width, uint32_t depth,
                                                             const uint32_t* init_words)
{
    uint32_t address_width = sn_tech_ceil_log2(depth);
    char name[192];
    int length = snprintf(name, sizeof(name), "__sn_%s_rtdp_tile_%u_%u", primitive->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    if (init_words)
    {
        int added = snprintf(name + length, sizeof(name) - (size_t)length, "_i%016llx",
                             (unsigned long long)sn_tech_init_hash(init_words,
                                                                   sn_const_word_count(width * depth)));
        assert(added > 0 && (size_t)length + (size_t)added < sizeof(name));
        length += added;
    }
    sn_module_id_t existing = sn_tech_tile_find(design, name, sizeof(name), length, init_words, width * depth);
    if (existing != SN_INVALID_ID)
        return existing;

    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock[2], write_enable[2], address[2], data[2], read_enable[2];
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
        snprintf(object_name, sizeof(object_name), "read_enable_%c", suffix);
        read_enable[port] = sn_module_add_pi(module, 1, false, object_name);
    }

    sn_obj_pair_t pair = sn_module_add_mem_pair(module, width, false, depth, "mem_out", "mem_in");
    if (init_words)
    {
        sn_obj_id_t init_data = sn_module_add_const(module, width * depth, false, init_words, NULL);
        sn_mem_set_init(module, pair.out, init_data, SN_INVALID_ID);
    }
    sn_module_add_mem_write(module, pair.in, clock[0], write_enable[0], data[0], address[0], "write_a");
    sn_module_add_mem_write(module, pair.in, clock[1], write_enable[1], data[1], address[1], "write_b");
    sn_obj_id_t read_a =
        sn_module_add_mem_read(module, pair.out, clock[0], read_enable[0], address[0], "read_a");
    sn_obj_id_t read_b =
        sn_module_add_mem_read(module, pair.out, clock[1], read_enable[1], address[1], "read_b");
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
                sn_obj_same_typed_value(source,
                    sn_obj_fanin(source, plan->writes[(uint32_t)write], SN_MEM_WRITE_ADDRESS), read_address))
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
    bool has_write = plan->write_count > 0;
    // A ROM keeps its write port permanently disabled; its content travels
    // in the tiles' initialization images.
    sn_obj_id_t clock = has_write ? sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                              sn_obj_fanin(source, plan->write, SN_MEM_WRITE_CLOCK))
                                  : SN_INVALID_ID;
    sn_obj_id_t enable_old = has_write ? sn_obj_fanin(source, plan->write, SN_MEM_WRITE_ENABLE) : SN_INVALID_ID;
    sn_obj_id_t enable = !has_write ? sn_tech_add_uint_const(module, 1, 0)
                         : enable_old == SN_INVALID_ID
                             ? sn_tech_add_uint_const(module, 1, 1)
                             : sn_vec_at(sn_obj_id_t, &source->copy_ids, enable_old);
    sn_obj_id_t data = has_write ? sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                             sn_obj_fanin(source, plan->write, SN_MEM_WRITE_DATA))
                                 : SN_INVALID_ID;
    sn_obj_id_t write_address = has_write
                                    ? sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                                sn_obj_fanin(source, plan->write, SN_MEM_WRITE_ADDRESS))
                                    : SN_INVALID_ID;
    sn_obj_id_t read_address = sn_vec_at(sn_obj_id_t, &source->copy_ids,
                                         sn_obj_fanin(source, plan->read, SN_MEM_READ_ADDRESS));
    uint32_t address_bits = sn_tech_ceil_log2(plan->tile_depth);
    uint32_t bank_bits = sn_tech_ceil_log2(plan->depth_tiles);
    sn_obj_id_t local_write = has_write
                                  ? sn_tech_memory_local_address(module, write_address, address_bits)
                                  : sn_module_add_named_obj(module, SN_CONST0, address_bits, false, 0, NULL);
    sn_obj_id_t local_read = sn_tech_memory_local_address(module, read_address, address_bits);
    bool registered = plan->read_clocks[0] != SN_INVALID_ID;
    sn_obj_id_t read_clock = SN_INVALID_ID, read_enable = SN_INVALID_ID;
    if (registered)
    {
        read_clock = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_clocks[0]);
        read_enable = plan->read_enables[0] == SN_INVALID_ID
                          ? sn_tech_add_uint_const(module, 1, 1)
                          : sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_enables[0]);
    }
    if (clock == SN_INVALID_ID)
        clock = registered ? read_clock : sn_tech_add_uint_const(module, 1, 0);

    sn_vec_t bank_enables, read_selects;
    sn_vec_init(&bank_enables);
    sn_vec_init(&read_selects);
    // With registered tiles the bank outputs carry last cycle's data, so the
    // output mux must select with last cycle's bank index, held under the
    // same read enable.
    sn_obj_id_t registered_index = SN_INVALID_ID;
    if (registered && bank_bits)
    {
        uint32_t needed = address_bits + bank_bits;
        sn_obj_id_t extended = sn_tech_add_zero_extend(
            module, read_address,
            needed > sn_obj_width(module, read_address) ? needed : sn_obj_width(module, read_address));
        sn_obj_id_t index =
            sn_module_add_slice(module, extended, (int32_t)(needed - 1), (int32_t)address_bits, NULL);
        sn_obj_pair_t held = sn_module_add_reg_pair(module, bank_bits, false, NULL, NULL, read_clock);
        if (plan->read_enables[0] != SN_INVALID_ID)
            sn_reg_set_fanin(module, held.out, SN_REG_ENABLE,
                             sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_enables[0]));
        sn_obj_connect(module, held.in, 0, index);
        registered_index = held.out;
    }
    for (uint32_t d = 0; d < plan->depth_tiles; d++)
    {
        if (has_write)
        {
            sn_obj_id_t write_select =
                sn_tech_memory_bank_select(module, write_address, address_bits, bank_bits, d);
            sn_obj_id_t enable_fanins[2] = {enable, write_select};
            *sn_vec_push(sn_obj_id_t, &bank_enables) =
                sn_module_add_operator(module, SN_BIT_AND, 1, false, 2, enable_fanins, NULL);
        }
        else
            *sn_vec_push(sn_obj_id_t, &bank_enables) = enable;
        sn_obj_id_t select;
        if (registered && bank_bits)
        {
            sn_obj_id_t value = sn_tech_add_uint_const(module, bank_bits, d);
            sn_obj_id_t select_fanins[2] = {registered_index, value};
            select = sn_module_add_operator(module, SN_EQ, 1, false, 2, select_fanins, NULL);
        }
        else
            select = sn_tech_memory_bank_select(module, read_address, address_bits, bank_bits, d);
        *sn_vec_push(sn_obj_id_t, &read_selects) = select;
    }

    sn_vec_t width_results;
    sn_vec_init(&width_results);
    for (uint32_t w = 0; w < plan->width_tiles; w++)
    {
        uint32_t offset = w * plan->port_width;
        uint32_t actual = sn_obj_width(source, plan->memory) - offset;
        if (actual > plan->port_width)
            actual = plan->port_width;
        sn_obj_id_t write_data;
        if (has_write)
        {
            write_data = sn_module_add_slice(module, data, (int32_t)(offset + actual - 1),
                                             (int32_t)offset, NULL);
            write_data = sn_tech_add_zero_extend(module, write_data, plan->port_width);
        }
        else
            write_data = sn_module_add_named_obj(module, SN_CONST0, plan->port_width, false, 0, NULL);
        sn_vec_t banks;
        sn_vec_init(&banks);
        for (uint32_t d = 0; d < plan->depth_tiles; d++)
        {
            uint32_t* tile_init = sn_tech_tile_init_words(source, plan->memory, offset, plan->port_width, d,
                                                          plan->tile_depth);
            sn_module_id_t primitive =
                registered ? sn_tech_memory_rtile_module(module->design, plan->primitive, plan->port_width,
                                                         plan->tile_depth, tile_init)
                           : sn_tech_memory_tile_module(module->design, plan->primitive, plan->port_width,
                                                        plan->tile_depth, tile_init);
            free(tile_init);
            sn_obj_id_t tile_enable = sn_vec_at(sn_obj_id_t, &bank_enables, d);
            sn_obj_id_t inputs[7] = {clock, tile_enable, local_write, write_data,
                                     read_clock, read_enable, local_read};
            if (!registered)
            {
                inputs[4] = local_read;
                *sn_vec_push(sn_obj_id_t, &banks) = sn_module_add_inst(module, primitive, 5, inputs, NULL, NULL);
            }
            else
                *sn_vec_push(sn_obj_id_t, &banks) = sn_module_add_inst(module, primitive, 7, inputs, NULL, NULL);
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
    bool registered = plan->read_clocks[0] != SN_INVALID_ID;
    sn_obj_id_t zero = sn_tech_add_uint_const(module, 1, 0);
    sn_obj_id_t zero_data = sn_module_add_named_obj(module, SN_CONST0, plan->port_width, false, 0, NULL);

    sn_obj_id_t port_clocks[2] = {zero, zero};
    sn_obj_id_t port_addresses[2] = {SN_INVALID_ID, SN_INVALID_ID};
    sn_obj_id_t port_write_data[2] = {SN_INVALID_ID, SN_INVALID_ID};
    sn_obj_id_t port_read_enables[2] = {zero, zero};
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
        if (registered && read_index >= 0)
        {
            port_read_enables[port] =
                plan->read_enables[(uint32_t)read_index] == SN_INVALID_ID
                    ? sn_tech_add_uint_const(module, 1, 1)
                    : sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_enables[(uint32_t)read_index]);
            if (write_index < 0)
                port_clocks[port] =
                    sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_clocks[(uint32_t)read_index]);
        }
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
        // With registered tiles the bank outputs carry last cycle's data, so
        // the output mux selects with last cycle's bank index, held under
        // the same read enable.
        sn_obj_id_t registered_index = SN_INVALID_ID;
        if (registered && bank_bits)
        {
            uint32_t needed = address_bits + bank_bits;
            sn_obj_id_t extended = sn_tech_add_zero_extend(
                module, address,
                needed > sn_obj_width(module, address) ? needed : sn_obj_width(module, address));
            sn_obj_id_t index =
                sn_module_add_slice(module, extended, (int32_t)(needed - 1), (int32_t)address_bits, NULL);
            sn_obj_pair_t held = sn_module_add_reg_pair(
                module, bank_bits, false, NULL, NULL,
                sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_clocks[read]));
            if (plan->read_enables[read] != SN_INVALID_ID)
                sn_reg_set_fanin(module, held.out, SN_REG_ENABLE,
                                 sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->read_enables[read]));
            sn_obj_connect(module, held.in, 0, index);
            registered_index = held.out;
        }
        for (uint32_t depth_tile = 0; depth_tile < plan->depth_tiles; depth_tile++)
        {
            sn_obj_id_t select;
            if (registered && bank_bits)
            {
                sn_obj_id_t value = sn_tech_add_uint_const(module, bank_bits, depth_tile);
                sn_obj_id_t select_fanins[2] = {registered_index, value};
                select = sn_module_add_operator(module, SN_EQ, 1, false, 2, select_fanins, NULL);
            }
            else
                select = sn_tech_memory_bank_select(module, address, address_bits, bank_bits, depth_tile);
            *sn_vec_push(sn_obj_id_t, &read_selects[read]) = select;
        }
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
            uint32_t* tile_init = sn_tech_tile_init_words(source, plan->memory, offset, plan->port_width,
                                                          depth_tile, plan->tile_depth);
            sn_module_id_t primitive =
                registered ? sn_tech_memory_rtdp_tile_module(module->design, plan->primitive,
                                                             plan->port_width, plan->tile_depth, tile_init)
                           : sn_tech_memory_tdp_tile_module(module->design, plan->primitive,
                                                            plan->port_width, plan->tile_depth, tile_init);
            free(tile_init);
            sn_obj_id_t inputs[10];
            uint32_t port_pins = registered ? 5 : 4;
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
                inputs[port_pins * port + 0] = port_clocks[port];
                inputs[port_pins * port + 1] = sn_vec_at(sn_obj_id_t, &port_enables[port], depth_tile);
                inputs[port_pins * port + 2] = port_addresses[port];
                inputs[port_pins * port + 3] = write_data;
                if (registered)
                    inputs[port_pins * port + 4] = port_read_enables[port];
            }
            sn_obj_id_t inst = sn_module_add_inst(module, primitive, 2 * port_pins, inputs, NULL, NULL);
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

static inline const sn_tech_srl_plan_t* sn_tech_srl_plan(const sn_module_t* module,
                                                         const sn_tech_srl_plan_t* plans, sn_obj_id_t object)
{
    if (sn_obj_type(module, object) != SN_MEM_READ)
        return NULL;
    const sn_tech_srl_plan_t* plan = &plans[sn_obj_data(module, object)];
    return plan->memory != SN_INVALID_ID ? plan : NULL;
}

// Chain plans are indexed by a register's position in the REG_OUT list,
// recorded per object in reg_slot.
static inline const sn_tech_srlreg_plan_t* sn_tech_srlreg_plan(const sn_module_t* module,
                                                               const sn_tech_srlreg_plan_t* plans,
                                                               const uint32_t* reg_slot, sn_obj_id_t object)
{
    if (sn_obj_type(module, object) != SN_REG_OUT)
        return NULL;
    const sn_tech_srlreg_plan_t* plan = &plans[reg_slot[object]];
    return plan->depth ? plan : NULL;
}

// A register eligible for shift-chain extraction: plain posedge or negedge
// flop with no set, reset, or initialization, gated at most by one enable.
static inline bool sn_tech_srlreg_eligible(const sn_module_t* module, sn_obj_id_t reg_out)
{
    uint32_t flags = sn_obj_reg_flags(module, reg_out);
    return (flags & ~(uint32_t)SN_REG_CLOCK_NEGEDGE) == 0 &&
           sn_reg_fanin(module, reg_out, SN_REG_SET) == SN_INVALID_ID &&
           sn_reg_fanin(module, reg_out, SN_REG_RESET) == SN_INVALID_ID &&
           sn_obj_reg_init_data(module, reg_out) == SN_INVALID_ID &&
           sn_reg_fanin(module, reg_out, SN_REG_CLOCK) != SN_INVALID_ID;
}

// Resolves a register's next-state source through single-fanout same-shape
// buffers and casts, recording the traversed intermediates.
static inline sn_obj_id_t sn_tech_srlreg_resolve(const sn_module_t* module, sn_obj_id_t value,
                                                 const uint32_t* refcount, uint32_t width,
                                                 sn_obj_id_t* intermediates, uint32_t* intermediate_count,
                                                 uint32_t max_intermediates)
{
    uint32_t hops = 0;
    *intermediate_count = 0;
    while (value != SN_INVALID_ID && hops < 3 &&
           (sn_obj_type(module, value) == SN_BUF || sn_obj_type(module, value) == SN_CAST) &&
           sn_obj_width(module, value) == width && refcount[value] == 1 &&
           *intermediate_count < max_intermediates)
    {
        intermediates[(*intermediate_count)++] = value;
        value = sn_obj_fanin(module, value, 0);
        hops++;
    }
    return value;
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
    bool* map_mac = (bool*)calloc(object_count, sizeof(bool));
    sn_tech_mem_plan_t* read_plans = (sn_tech_mem_plan_t*)calloc(read_count, sizeof(sn_tech_mem_plan_t));
    sn_tech_srl_plan_t* srl_plans = (sn_tech_srl_plan_t*)calloc(read_count ? read_count : 1,
                                                                 sizeof(sn_tech_srl_plan_t));
    sn_obj_id_t* srl_built = (sn_obj_id_t*)malloc((read_count ? read_count : 1) * sizeof(sn_obj_id_t));
    size_t reg_out_count = source->type_objects[SN_REG_OUT].size;
    sn_tech_srlreg_plan_t* srlreg_plans =
        (sn_tech_srlreg_plan_t*)calloc(reg_out_count ? reg_out_count : 1, sizeof(sn_tech_srlreg_plan_t));
    assert(srlreg_plans);
    uint32_t* reg_slot = (uint32_t*)malloc((object_count ? object_count : 1) * sizeof(uint32_t));
    assert(reg_slot);
    for (size_t i = 0; i < object_count; i++)
        reg_slot[i] = SN_INVALID_ID;
    for (size_t i = 0; i < reg_out_count; i++)
        reg_slot[sn_vec_at(sn_obj_id_t, &source->type_objects[SN_REG_OUT], i)] = (uint32_t)i;
    size_t* map_csa = (size_t*)malloc((object_count ? object_count : 1) * sizeof(size_t));
    sn_vec_t csa_leaves, csa_flags, csa_plans;
    sn_vec_init(&csa_leaves);
    sn_vec_init(&csa_flags);
    sn_vec_init(&csa_plans);
    assert(map_csa);
    for (size_t i = 0; i < object_count; i++)
        map_csa[i] = SIZE_MAX;
    // Shared fanout-reference counts for the recognition passes below.
    uint32_t* refcount = (uint32_t*)calloc(object_count ? object_count : 1, sizeof(uint32_t));
    assert(refcount);
    for (sn_obj_id_t object = 0; object < object_count; object++)
        for (uint32_t k = 0; k < sn_obj_fanin_count(source, object); k++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(source, object, k);
            if (fanin != SN_INVALID_ID)
                refcount[fanin]++;
        }
    assert((!object_count || omit) && (!object_count || map_mul) && (!object_count || map_add) &&
           (!read_count || read_plans) && srl_plans);
    assert(srl_built);
    for (size_t i = 0; i < read_count; i++)
    {
        memset(&read_plans[i], 0, sizeof(read_plans[i]));
        read_plans[i].memory = SN_INVALID_ID;
        read_plans[i].read_clocks[0] = read_plans[i].read_clocks[1] = SN_INVALID_ID;
        read_plans[i].read_enables[0] = read_plans[i].read_enables[1] = SN_INVALID_ID;
        read_plans[i].absorbed_regs[0] = read_plans[i].absorbed_regs[1] = SN_INVALID_ID;
        srl_plans[i].memory = SN_INVALID_ID;
        srl_built[i] = SN_INVALID_ID;
    }

    // For each asynchronous memory read, the single plain register (no set,
    // reset, initialization, or clock inversion) fed exclusively by that read
    // through single-fanout buffers. Such a register can be absorbed into a
    // registered-read memory tile, matching the physical primitive's
    // registered output port.
    sn_obj_id_t* read_reg = (sn_obj_id_t*)malloc((read_count ? read_count : 1) * sizeof(sn_obj_id_t));
    sn_obj_id_t (*read_reg_hops)[4] = (sn_obj_id_t (*)[4])malloc((read_count ? read_count : 1) * 4 *
                                                                 sizeof(sn_obj_id_t));
    uint8_t* read_reg_hop_counts = (uint8_t*)calloc(read_count ? read_count : 1, sizeof(uint8_t));
    bool* forwarded = (bool*)calloc(object_count ? object_count : 1, sizeof(bool));
    assert(read_reg && read_reg_hops && read_reg_hop_counts && forwarded);
    for (size_t i = 0; i < read_count; i++)
        read_reg[i] = SN_INVALID_ID;
    if (options->map_memories || options->map_shift_registers)
        for (size_t i = 0; i < source->type_objects[SN_REG_OUT].size; i++)
        {
            sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_REG_OUT], i);
            uint32_t flags = sn_obj_reg_flags(source, reg_out);
            if (flags != 0 || sn_reg_fanin(source, reg_out, SN_REG_SET) != SN_INVALID_ID ||
                sn_reg_fanin(source, reg_out, SN_REG_RESET) != SN_INVALID_ID ||
                sn_obj_reg_init_data(source, reg_out) != SN_INVALID_ID ||
                sn_reg_fanin(source, reg_out, SN_REG_CLOCK) == SN_INVALID_ID)
                continue;
            sn_obj_id_t hops[4];
            uint32_t hop_count = 0;
            sn_obj_id_t data = sn_obj_fanin(source, sn_obj_pair_in(source, reg_out), 0);
            sn_obj_id_t producer = sn_tech_srlreg_resolve(source, data, refcount,
                                                          sn_obj_width(source, reg_out), hops, &hop_count, 4);
            if (producer == SN_INVALID_ID || sn_obj_type(source, producer) != SN_MEM_READ ||
                refcount[producer] != 1 || sn_obj_width(source, producer) != sn_obj_width(source, reg_out))
                continue;
            uint32_t read_id = sn_obj_data(source, producer);
            read_reg[read_id] = reg_out;
            for (uint32_t k = 0; k < hop_count; k++)
                read_reg_hops[read_id][k] = hops[k];
            read_reg_hop_counts[read_id] = (uint8_t)hop_count;
        }


    // Shift-register extraction: a memory whose writes shift entry k-1 into
    // entry k under one clock and one shared enable, fed externally only at
    // entry zero and observed only through one asynchronous tap read, is a
    // shift register. The whole cluster becomes one behavioral SRL primitive,
    // which removes the flops, the shift muxing, and the tap decode from the
    // soft logic. Recognition runs before general memory planning so BRAM
    // tiling never claims a shift register.
    if (options->map_shift_registers && source->type_objects[SN_MEM_OUT].size)
    {
        for (size_t i = 0; i < source->type_objects[SN_MEM_OUT].size; i++)
        {
            sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_MEM_OUT], i);
            uint32_t depth = sn_obj_mem_depth(source, memory);
            if (omit[memory] || depth < 2 || depth > 32 ||
                sn_obj_mem_init_data(source, memory) != SN_INVALID_ID)
                continue;
            sn_obj_id_t memory_in = sn_obj_pair_in(source, memory);
            sn_obj_id_t writes_by_address[32];
            for (uint32_t k = 0; k < depth; k++)
                writes_by_address[k] = SN_INVALID_ID;
            bool valid = true;
            uint32_t write_count = 0;
            for (uint32_t j = 0; valid && j < sn_obj_mem_write_count(source, memory_in); j++)
            {
                sn_obj_id_t write = sn_obj_mem_write(source, memory_in, j);
                if (write == SN_INVALID_ID || sn_obj_type(source, write) != SN_MEM_WRITE)
                    continue;
                sn_obj_id_t address = sn_obj_fanin(source, write, SN_MEM_WRITE_ADDRESS);
                uint64_t value = 0;
                if (address == SN_INVALID_ID || !sn_dff_const_value64(source, address, &value) ||
                    value >= depth || writes_by_address[value] != SN_INVALID_ID)
                {
                    valid = false;
                    break;
                }
                writes_by_address[value] = write;
                write_count++;
            }
            if (!valid || write_count != depth)
                continue;
            sn_obj_id_t clock = sn_obj_fanin(source, writes_by_address[0], SN_MEM_WRITE_CLOCK);
            sn_obj_id_t enable = sn_obj_fanin(source, writes_by_address[0], SN_MEM_WRITE_ENABLE);
            if (clock == SN_INVALID_ID)
                continue;
            for (uint32_t k = 1; valid && k < depth; k++)
                valid = sn_obj_same_typed_value(source,
                            sn_obj_fanin(source, writes_by_address[k], SN_MEM_WRITE_CLOCK), clock) &&
                        sn_obj_same_typed_value(source,
                            sn_obj_fanin(source, writes_by_address[k], SN_MEM_WRITE_ENABLE), enable);
            if (!valid)
                continue;
            // Each shifting write's data must be the single-fanout
            // asynchronous read of the previous entry, possibly through
            // single-fanout same-shape buffers or casts.
            sn_obj_id_t chain_members[32 * 4];
            uint32_t chain_member_count = 0;
            for (uint32_t k = 1; valid && k < depth; k++)
            {
                sn_obj_id_t data = sn_obj_fanin(source, writes_by_address[k], SN_MEM_WRITE_DATA);
                uint32_t hops = 0;
                while (valid && data != SN_INVALID_ID && hops < 3 &&
                       (sn_obj_type(source, data) == SN_BUF || sn_obj_type(source, data) == SN_CAST) &&
                       sn_obj_width(source, data) == sn_obj_width(source, memory) && refcount[data] == 1)
                {
                    if (chain_member_count >= 32 * 4)
                    {
                        valid = false;
                        break;
                    }
                    chain_members[chain_member_count++] = data;
                    data = sn_obj_fanin(source, data, 0);
                    hops++;
                }
                uint64_t read_address = 0;
                valid = valid && data != SN_INVALID_ID && sn_obj_type(source, data) == SN_MEM_READ &&
                        sn_obj_fanin(source, data, SN_MEM_READ_MEMORY) == memory &&
                        sn_obj_fanin(source, data, SN_MEM_READ_CLOCK) == SN_INVALID_ID &&
                        sn_obj_fanin(source, data, SN_MEM_READ_ENABLE) == SN_INVALID_ID && refcount[data] == 1 &&
                        sn_dff_const_value64(source, sn_obj_fanin(source, data, SN_MEM_READ_ADDRESS),
                                             &read_address) &&
                        read_address == k - 1;
                if (valid)
                {
                    assert(chain_member_count < 32 * 4);
                    chain_members[chain_member_count++] = data;
                }
            }
            if (!valid)
                continue;
            // A small number of asynchronous external taps remain; they all
            // read the same shifting state, so one primitive with several
            // tap ports serves them.
            sn_obj_id_t taps[SN_TECH_SRL_MAX_TAPS];
            uint32_t external_reads = 0;
            bool taps_ok = true;
            for (size_t j = 0; taps_ok && j < source->type_objects[SN_MEM_READ].size; j++)
            {
                sn_obj_id_t candidate = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_MEM_READ], j);
                if (sn_obj_fanin(source, candidate, SN_MEM_READ_MEMORY) != memory)
                    continue;
                bool chained = false;
                for (uint32_t k = 0; k < chain_member_count && !chained; k++)
                    chained = chain_members[k] == candidate;
                if (chained)
                    continue;
                if (external_reads >= SN_TECH_SRL_MAX_TAPS ||
                    sn_obj_fanin(source, candidate, SN_MEM_READ_CLOCK) != SN_INVALID_ID ||
                    sn_obj_fanin(source, candidate, SN_MEM_READ_ENABLE) != SN_INVALID_ID)
                {
                    taps_ok = false;
                    break;
                }
                taps[external_reads++] = candidate;
            }
            if (!taps_ok || external_reads == 0)
                continue;
            sn_obj_id_t tap_regs[SN_TECH_SRL_MAX_TAPS];
            sn_obj_id_t tap_clocks[SN_TECH_SRL_MAX_TAPS];
            sn_obj_id_t tap_enables[SN_TECH_SRL_MAX_TAPS];
            for (uint32_t t = 0; t < external_reads; t++)
            {
                uint32_t tap_id = sn_obj_data(source, taps[t]);
                tap_regs[t] = read_reg[tap_id] != SN_INVALID_ID && !omit[read_reg[tap_id]]
                                  ? read_reg[tap_id]
                                  : SN_INVALID_ID;
                tap_clocks[t] = tap_regs[t] != SN_INVALID_ID
                                    ? sn_reg_fanin(source, tap_regs[t], SN_REG_CLOCK)
                                    : SN_INVALID_ID;
                tap_enables[t] = tap_regs[t] != SN_INVALID_ID
                                     ? sn_reg_fanin(source, tap_regs[t], SN_REG_ENABLE)
                                     : SN_INVALID_ID;
            }
            for (uint32_t t = 0; t < external_reads; t++)
            {
                sn_tech_srl_plan_t* plan = &srl_plans[sn_obj_data(source, taps[t])];
                plan->memory = memory;
                plan->din = sn_obj_fanin(source, writes_by_address[0], SN_MEM_WRITE_DATA);
                plan->clock = clock;
                plan->enable = enable;
                plan->depth = depth;
                plan->tap_count = external_reads;
                plan->tap_index = t;
                for (uint32_t k = 0; k < external_reads; k++)
                {
                    plan->taps[k] = taps[k];
                    plan->tap_regs[k] = tap_regs[k];
                    plan->tap_clocks[k] = tap_clocks[k];
                    plan->tap_enables[k] = tap_enables[k];
                }
            }
            omit[memory] = omit[memory_in] = true;
            for (uint32_t k = 0; k < depth; k++)
                omit[writes_by_address[k]] = true;
            for (uint32_t k = 0; k < chain_member_count; k++)
                omit[chain_members[k]] = true;
            for (uint32_t t = 0; t < external_reads; t++)
            {
                if (tap_regs[t] == SN_INVALID_ID)
                    continue;
                uint32_t tap_id = sn_obj_data(source, taps[t]);
                omit[tap_regs[t]] = true;
                forwarded[tap_regs[t]] = true;
                omit[sn_obj_pair_in(source, tap_regs[t])] = true;
                for (uint32_t k = 0; k < read_reg_hop_counts[tap_id]; k++)
                    omit[read_reg_hops[tap_id][k]] = true;
            }
        }
        // Fixed register shift chains: registers on one clock and one shared
        // enable whose next state is the previous stage, with every interior
        // stage read only by its successor. The whole chain becomes one
        // behavioral chain primitive, the idiom FPGA synthesis maps onto SRL
        // cells with an optional output flop.
        if (reg_out_count)
        {
            uint8_t* consumed = (uint8_t*)calloc(object_count, sizeof(uint8_t));
            assert(consumed);
            sn_obj_id_t hops[4];
            uint32_t hop_count = 0;
            for (size_t i = 0; i < reg_out_count; i++)
            {
                sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_REG_OUT], i);
                if (!sn_tech_srlreg_eligible(source, reg_out))
                    continue;
                sn_obj_id_t data = sn_obj_fanin(source, sn_obj_pair_in(source, reg_out), 0);
                sn_obj_id_t previous = sn_tech_srlreg_resolve(source, data, refcount,
                                                              sn_obj_width(source, reg_out), hops, &hop_count, 4);
                if (previous != SN_INVALID_ID && sn_obj_type(source, previous) == SN_REG_OUT &&
                    refcount[previous] == 1 && sn_tech_srlreg_eligible(source, previous))
                    consumed[previous] = 1;
            }
            for (size_t i = 0; i < reg_out_count; i++)
            {
                sn_obj_id_t tail = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_REG_OUT], i);
                if (!sn_tech_srlreg_eligible(source, tail) || consumed[tail] || omit[tail])
                    continue;
                uint32_t width = sn_obj_width(source, tail);
                sn_obj_id_t clock = sn_reg_fanin(source, tail, SN_REG_CLOCK);
                sn_obj_id_t enable = sn_reg_fanin(source, tail, SN_REG_ENABLE);
                uint32_t flags = sn_obj_reg_flags(source, tail);
                sn_obj_id_t members[128];
                sn_obj_id_t buffers[128 * 4];
                uint32_t member_count = 1, buffer_count = 0;
                members[0] = tail;
                sn_obj_id_t current = tail;
                while (member_count < 128)
                {
                    sn_obj_id_t data = sn_obj_fanin(source, sn_obj_pair_in(source, current), 0);
                    sn_obj_id_t previous =
                        sn_tech_srlreg_resolve(source, data, refcount, width, hops, &hop_count, 4);
                    if (previous == SN_INVALID_ID || sn_obj_type(source, previous) != SN_REG_OUT ||
                        refcount[previous] != 1 || omit[previous] ||
                        !sn_tech_srlreg_eligible(source, previous) ||
                        sn_obj_width(source, previous) != width ||
                        sn_reg_fanin(source, previous, SN_REG_CLOCK) != clock ||
                        !sn_obj_same_typed_value(source, sn_reg_fanin(source, previous, SN_REG_ENABLE), enable) ||
                        sn_obj_reg_flags(source, previous) != flags ||
                        buffer_count + hop_count > 128 * 4)
                        break;
                    for (uint32_t k = 0; k < hop_count; k++)
                        buffers[buffer_count++] = hops[k];
                    members[member_count++] = previous;
                    current = previous;
                }
                if (member_count < 3)
                    continue;
                sn_obj_id_t head = members[member_count - 1];
                sn_tech_srlreg_plan_t* plan = &srlreg_plans[i];
                plan->din = sn_obj_fanin(source, sn_obj_pair_in(source, head), 0);
                plan->clock = clock;
                plan->enable = enable;
                plan->depth = member_count;
                plan->negedge = (flags & SN_REG_CLOCK_NEGEDGE) != 0;
                for (uint32_t k = 1; k < member_count; k++)
                {
                    omit[members[k]] = true;
                    omit[sn_obj_pair_in(source, members[k])] = true;
                }
                omit[sn_obj_pair_in(source, tail)] = true;
                for (uint32_t k = 0; k < buffer_count; k++)
                    omit[buffers[k]] = true;
            }
            free(consumed);
        }
    }

    if (options->map_memories)
        for (size_t i = 0; i < source->type_objects[SN_MEM_OUT].size; i++)
        {
            sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_MEM_OUT], i);
            uint64_t bits = (uint64_t)sn_obj_width(source, memory) * sn_obj_mem_depth(source, memory);
            if (omit[memory] || bits < options->memory.min_memory_bits)
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
            for (uint32_t j = 0; j < sn_obj_mem_write_count(source, memory_in); j++)
            {
                sn_obj_id_t candidate = sn_obj_mem_write(source, memory_in, j);
                if (candidate != SN_INVALID_ID && sn_obj_type(source, candidate) == SN_MEM_WRITE)
                {
                    if (writes < 2)
                        writes_found[writes] = candidate;
                    writes++;
                }
            }
            if (!reads || reads > 2 || writes > 2)
                continue;
            // A single read with two independent writes needs true-dual-port
            // collision analysis; preserve it until that case is modeled.
            // A write-free memory is a ROM whose initialization travels into
            // the tiles.
            if (reads == 1 && writes > 1)
                continue;
            // A plan accepts registered reads: a read is registered when the
            // source read is already clocked or when it is asynchronous and
            // its single external read register is absorbed. A dual-read
            // plan registers either both reads or neither; an absorbed
            // register can be released to restore the asynchronous form,
            // while a natively clocked read cannot.
            sn_obj_id_t plan_read_clocks[2] = {SN_INVALID_ID, SN_INVALID_ID};
            sn_obj_id_t plan_read_enables[2] = {SN_INVALID_ID, SN_INVALID_ID};
            sn_obj_id_t plan_absorbed[2] = {SN_INVALID_ID, SN_INVALID_ID};
            bool plannable = true;
            for (uint32_t read = 0; read < reads; read++)
            {
                sn_obj_id_t the_read = reads_found[read];
                sn_obj_id_t own_clock = sn_obj_fanin(source, the_read, SN_MEM_READ_CLOCK);
                if (own_clock != SN_INVALID_ID)
                {
                    plan_read_clocks[read] = own_clock;
                    plan_read_enables[read] = sn_obj_fanin(source, the_read, SN_MEM_READ_ENABLE);
                }
                else if (sn_obj_fanin(source, the_read, SN_MEM_READ_ENABLE) != SN_INVALID_ID)
                    plannable = false;
                else if (read_reg[sn_obj_data(source, the_read)] != SN_INVALID_ID &&
                         !omit[read_reg[sn_obj_data(source, the_read)]])
                {
                    sn_obj_id_t reg_out = read_reg[sn_obj_data(source, the_read)];
                    plan_read_clocks[read] = sn_reg_fanin(source, reg_out, SN_REG_CLOCK);
                    plan_read_enables[read] = sn_reg_fanin(source, reg_out, SN_REG_ENABLE);
                    plan_absorbed[read] = reg_out;
                }
            }
            if (plannable && reads == 2 &&
                (plan_read_clocks[0] != SN_INVALID_ID) != (plan_read_clocks[1] != SN_INVALID_ID))
                for (uint32_t read = 0; read < reads; read++)
                    if (plan_read_clocks[read] != SN_INVALID_ID)
                    {
                        if (plan_absorbed[read] == SN_INVALID_ID)
                            plannable = false;
                        plan_read_clocks[read] = plan_read_enables[read] = SN_INVALID_ID;
                        plan_absorbed[read] = SN_INVALID_ID;
                    }
            if (!plannable)
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
            for (uint32_t read = 0; read < reads; read++)
            {
                plan.read_clocks[read] = plan_read_clocks[read];
                plan.read_enables[read] = plan_read_enables[read];
                plan.absorbed_regs[read] = plan_absorbed[read];
            }
            if (!sn_tech_choose_memory_for_mode(tech, sn_obj_width(source, memory),
                                                sn_obj_mem_depth(source, memory), &options->memory,
                                                reads == 1 && writes <= 1, &plan))
                continue;
            if (reads > 1 && (!plan.primitive || plan.primitive->port_mode != SN_MEM_PORT_TRUE_DUAL ||
                              !sn_tech_assign_tdp_ports(source, &plan)))
                continue;
            // A registered dual-port read shares its port's single physical
            // clock, so its clock must match the assigned port's write clock.
            // On mismatch, release the absorbed registers and fall back to
            // asynchronous reads; a natively clocked read cannot fall back.
            if (reads == 2 && plan.read_clocks[0] != SN_INVALID_ID)
            {
                bool compatible = true;
                for (uint32_t port = 0; port < 2 && compatible; port++)
                {
                    int8_t read_index = plan.port_reads[port];
                    int8_t write_index = plan.port_writes[port];
                    if (read_index < 0)
                        continue;
                    // A read-only port's clock comes from the read itself; a
                    // shared read/write port has one physical clock.
                    compatible = write_index < 0 ||
                                 plan.read_clocks[read_index] ==
                                     sn_obj_fanin(source, plan.writes[(uint32_t)write_index],
                                                  SN_MEM_WRITE_CLOCK);
                }
                if (!compatible)
                {
                    bool releasable = plan.absorbed_regs[0] != SN_INVALID_ID &&
                                      plan.absorbed_regs[1] != SN_INVALID_ID;
                    if (!releasable)
                        continue;
                    for (uint32_t read = 0; read < reads; read++)
                    {
                        plan.read_clocks[read] = plan.read_enables[read] = SN_INVALID_ID;
                        plan.absorbed_regs[read] = SN_INVALID_ID;
                    }
                }
            }
            for (uint32_t read = 0; read < reads; read++)
                read_plans[sn_obj_data(source, reads_found[read])] = plan;
            omit[memory] = omit[memory_in] = true;
            for (uint32_t write = 0; write < writes; write++)
                omit[writes_found[write]] = true;
            for (uint32_t read = 0; read < reads; read++)
            {
                sn_obj_id_t absorbed = plan.absorbed_regs[read];
                if (absorbed == SN_INVALID_ID)
                    continue;
                uint32_t read_id = sn_obj_data(source, reads_found[read]);
                omit[absorbed] = true;
                forwarded[absorbed] = true;
                omit[sn_obj_pair_in(source, absorbed)] = true;
                for (uint32_t k = 0; k < read_reg_hop_counts[read_id]; k++)
                    omit[read_reg_hops[read_id][k]] = true;
            }
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
            free(map_mac);
            free(map_csa);
            sn_vec_destroy(&csa_leaves);
            sn_vec_destroy(&csa_flags);
            sn_vec_destroy(&csa_plans);
            free(read_plans);
            free(srl_plans);
            free(srl_built);
            free(srlreg_plans);
            free(reg_slot);
            free(refcount);
            free(read_reg);
            free(read_reg_hops);
            free(read_reg_hop_counts);
            free(forwarded);
            return SN_INVALID_ID;
        }
        // An addition whose only use of a mapped multiplier is this sum
        // absorbs into the DSP post-adder chain. The multiplication then
        // computes at its own width, so the addition must not be wider, and
        // the chained sums must fit the DSP product width.
        if (dsp->has_postadder && options->dsp.use_postadder)
        {
            for (size_t i = 0; i < source->type_objects[SN_ADD].size; i++)
            {
                sn_obj_id_t add = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_ADD], i);
                if (sn_obj_fanin_count(source, add) != 2)
                    continue;
                sn_obj_id_t first = sn_obj_fanin(source, add, 0);
                sn_obj_id_t second = sn_obj_fanin(source, add, 1);
                if (first == second)
                    continue;
                sn_obj_id_t mul = SN_INVALID_ID;
                if (map_mul[first] && !omit[first] && refcount[first] == 1)
                    mul = first;
                else if (map_mul[second] && !omit[second] && refcount[second] == 1)
                    mul = second;
                if (mul == SN_INVALID_ID || sn_obj_width(source, add) > sn_obj_width(source, mul) ||
                    sn_obj_width(source, mul) > dsp->p_width)
                    continue;
                map_mac[add] = true;
                omit[mul] = true;
            }
        }
    }

    if (options->map_adders)
    {
        assert(tech->carry_count);
        const sn_carry_tech_t* carry = &tech->carries[0];
        for (sn_obj_id_t object = 0; object < object_count; object++)
            map_add[object] = !map_mac[object] &&
                              sn_add_tech_supports(carry, &options->add, sn_obj_type(source, object),
                                                   sn_obj_width(source, object));
    }

    // Multi-operand accumulation: a single-fanout chain of mappable
    // additions and subtractions collapses into one carry-save compressor
    // tree with one final carry chain instead of one chain per operator.
    // Every leaf is recorded with the extension signedness of the operator
    // that consumed it and with its accumulated negation, so distributing
    // subtraction over the tree stays exact modulo 2^width. Roots are
    // visited in reverse topological order so an inner chain joins its
    // outermost consumer rather than forming a separate tree.
    if (options->map_adders && options->add.map_trees)
    {
        uint8_t* leaf_flags_tmp = (uint8_t*)malloc(options->add.max_tree_operands + 2);
        sn_obj_id_t* leaf_tmp = (sn_obj_id_t*)malloc((options->add.max_tree_operands + 2) * sizeof(sn_obj_id_t));
        sn_vec_t stack, interior_tmp;
        sn_vec_init(&stack);
        sn_vec_init(&interior_tmp);
        assert(leaf_flags_tmp && leaf_tmp);
        for (sn_obj_id_t root = (sn_obj_id_t)object_count; root-- > 0;)
        {
            sn_obj_type_t root_type = sn_obj_type(source, root);
            if ((root_type != SN_ADD && root_type != SN_SUB) || !map_add[root] || omit[root] ||
                map_csa[root] != SIZE_MAX || sn_obj_fanin_count(source, root) != 2)
                continue;
            uint32_t root_width = sn_obj_width(source, root);
            uint32_t leaf_count = 0;
            bool ok = true;
            stack.size = 0;
            interior_tmp.size = 0;
            bool root_signed_ext = sn_obj_is_signed(source, sn_obj_fanin(source, root, 0)) &&
                                   sn_obj_is_signed(source, sn_obj_fanin(source, root, 1));
            // Each stack entry packs the object with two flag bits:
            // bit 0 negation, bit 1 extension signedness.
            uint64_t initial0 = ((uint64_t)sn_obj_fanin(source, root, 0) << 2) | (root_signed_ext ? 2 : 0);
            uint64_t initial1 = ((uint64_t)sn_obj_fanin(source, root, 1) << 2) | (root_signed_ext ? 2 : 0) |
                                (root_type == SN_SUB ? 1 : 0);
            *sn_vec_push(uint64_t, &stack) = initial0;
            *sn_vec_push(uint64_t, &stack) = initial1;
            while (ok && stack.size)
            {
                uint64_t entry = sn_vec_at(uint64_t, &stack, --stack.size);
                sn_obj_id_t value = (sn_obj_id_t)(entry >> 2);
                uint8_t flags = (uint8_t)(entry & 3);
                sn_obj_type_t type = sn_obj_type(source, value);
                bool expand = (type == SN_ADD || type == SN_SUB) && map_add[value] && !map_mac[value] &&
                              !omit[value] && map_csa[value] == SIZE_MAX && refcount[value] == 1 &&
                              sn_obj_fanin_count(source, value) == 2 &&
                              sn_obj_width(source, value) >= root_width;
                if (expand)
                {
                    bool ext = sn_obj_is_signed(source, sn_obj_fanin(source, value, 0)) &&
                               sn_obj_is_signed(source, sn_obj_fanin(source, value, 1));
                    *sn_vec_push(sn_obj_id_t, &interior_tmp) = value;
                    *sn_vec_push(uint64_t, &stack) = ((uint64_t)sn_obj_fanin(source, value, 0) << 2) |
                                                     (ext ? 2 : 0) | (flags & 1);
                    *sn_vec_push(uint64_t, &stack) =
                        ((uint64_t)sn_obj_fanin(source, value, 1) << 2) | (ext ? 2 : 0) |
                        ((type == SN_SUB ? !(flags & 1) : (flags & 1)) ? 1 : 0);
                    continue;
                }
                if (leaf_count >= options->add.max_tree_operands)
                {
                    ok = false;
                    break;
                }
                leaf_tmp[leaf_count] = value;
                leaf_flags_tmp[leaf_count] = flags;
                leaf_count++;
            }
            if (!ok || leaf_count < 3)
                continue;
            sn_tech_csa_plan_t* plan = sn_vec_push(sn_tech_csa_plan_t, &csa_plans);
            plan->begin = (uint32_t)csa_leaves.size;
            plan->count = leaf_count;
            for (uint32_t k = 0; k < leaf_count; k++)
            {
                *sn_vec_push(sn_obj_id_t, &csa_leaves) = leaf_tmp[k];
                *sn_vec_push(uint8_t, &csa_flags) = leaf_flags_tmp[k];
            }
            map_csa[root] = csa_plans.size - 1;
            map_add[root] = false;
            for (size_t k = 0; k < interior_tmp.size; k++)
            {
                sn_obj_id_t interior = sn_vec_at(sn_obj_id_t, &interior_tmp, k);
                omit[interior] = true;
                map_add[interior] = false;
            }
        }
        sn_vec_destroy(&stack);
        sn_vec_destroy(&interior_tmp);
        free(leaf_tmp);
        free(leaf_flags_tmp);
    }

    bool changed = false;
    for (sn_obj_id_t object = 0; object < object_count && !changed; object++)
    {
        const sn_tech_mem_plan_t* read_plan = sn_tech_read_plan(source, read_plans, object);
        changed = omit[object] || map_mul[object] || map_add[object] || map_mac[object] ||
                  map_csa[object] != SIZE_MAX ||
                  sn_tech_srlreg_plan(source, srlreg_plans, reg_slot, object) != NULL ||
                  (read_plan && read_plan->memory != SN_INVALID_ID);
    }
    if (!changed && !force_copy)
    {
        free(omit);
        free(map_mul);
        free(map_add);
        free(map_mac);
        free(map_csa);
        sn_vec_destroy(&csa_leaves);
        sn_vec_destroy(&csa_flags);
        sn_vec_destroy(&csa_plans);
        free(read_plans);
        free(srl_plans);
        free(srl_built);
        free(srlreg_plans);
        free(reg_slot);
        free(refcount);
        free(read_reg);
        free(read_reg_hops);
        free(read_reg_hop_counts);
        free(forwarded);
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
        bool special_mac = map_mac[old_object];
        bool special_csa = map_csa[old_object] != SIZE_MAX;
        bool special_srl = sn_tech_srl_plan(source, srl_plans, old_object) != NULL ||
                           sn_tech_srlreg_plan(source, srlreg_plans, reg_slot, old_object) != NULL;
        sn_obj_id_t new_object = special_mul || special_mem || special_add || special_mac || special_csa ||
                                         special_srl
                                     ? sn_module_add_obj(mapped, SN_BUF, sn_obj_width(source, old_object),
                                                         sn_obj_is_signed(source, old_object), 1,
                                                         sn_obj_name_id(source, old_object))
                                     : sn_module_dup_obj_skeleton(mapped, source, old_object);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = new_object;
    }

    sn_module_order_pairs_by_source(mapped, source);

    // An absorbed read or tap register forwards its consumers to the
    // registered read's placeholder copy.
    for (size_t i = 0; i < read_count; i++)
    {
        for (uint32_t read = 0; read_plans[i].memory != SN_INVALID_ID && read < read_plans[i].read_count;
             read++)
            if (read_plans[i].absorbed_regs[read] != SN_INVALID_ID)
                sn_vec_at(sn_obj_id_t, &source->copy_ids, read_plans[i].absorbed_regs[read]) =
                    sn_vec_at(sn_obj_id_t, &source->copy_ids, read_plans[i].reads[read]);
        const sn_tech_srl_plan_t* splan = &srl_plans[i];
        if (splan->memory != SN_INVALID_ID && splan->tap_regs[splan->tap_index] != SN_INVALID_ID)
            sn_vec_at(sn_obj_id_t, &source->copy_ids, splan->tap_regs[splan->tap_index]) =
                sn_vec_at(sn_obj_id_t, &source->copy_ids, splan->taps[splan->tap_index]);
    }

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
                                                        sn_obj_is_signed(source, old_object), SN_INVALID_ID);
            sn_obj_connect(mapped, placeholder, 0, result);
        }
        else if (map_mac[old_object])
        {
            // The addition of a single-use multiplier absorbs into the DSP
            // post-adder chain. The multiplication computes at the omitted
            // multiplier's own width, which bounds the addition's width, so
            // modulo arithmetic keeps the truncating final cast exact.
            sn_obj_id_t mul = sn_obj_fanin(source, old_object, 0);
            sn_obj_id_t addend = sn_obj_fanin(source, old_object, 1);
            if (sn_obj_type(source, mul) != SN_MUL || !omit[mul])
            {
                sn_obj_id_t swap = mul;
                mul = addend;
                addend = swap;
            }
            assert(dsp && sn_obj_type(source, mul) == SN_MUL && omit[mul]);
            sn_obj_id_t a = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, mul, 0));
            sn_obj_id_t b = sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, mul, 1));
            sn_obj_id_t c = sn_vec_at(sn_obj_id_t, &source->copy_ids, addend);
            sn_obj_id_t result =
                sn_tech_map_multiplier(mapped, dsp, &options->dsp, a, b, sn_obj_width(source, mul),
                                       sn_obj_is_signed(source, mul), c);
            result = sn_tech_add_cast(mapped, result, sn_obj_width(source, old_object),
                                      sn_obj_is_signed(source, old_object));
            sn_obj_connect(mapped, placeholder, 0, result);
        }
        else if (map_csa[old_object] != SIZE_MAX)
        {
            const sn_tech_csa_plan_t* plan = &sn_vec_at(sn_tech_csa_plan_t, &csa_plans, map_csa[old_object]);
            uint32_t root_width = sn_obj_width(source, old_object);
            bool fold_consts = root_width <= 64;
            uint64_t const_total = 0;
            uint32_t extra_ones = 0;
            sn_obj_id_t* operands =
                (sn_obj_id_t*)malloc((plan->count + 1) * sizeof(sn_obj_id_t));
            uint32_t operand_count = 0;
            assert(carry && operands);
            for (uint32_t k = 0; k < plan->count; k++)
            {
                sn_obj_id_t leaf = sn_vec_at(sn_obj_id_t, &csa_leaves, plan->begin + k);
                uint8_t flags = sn_vec_at(uint8_t, &csa_flags, plan->begin + k);
                bool negate = (flags & 1) != 0;
                bool ext_signed = (flags & 2) != 0;
                uint64_t leaf_value = 0;
                if (fold_consts && sn_obj_width(source, leaf) <= 64 &&
                    sn_dff_const_value64(source, leaf, &leaf_value))
                {
                    uint64_t extended =
                        sn_dff_extend64(leaf_value, sn_obj_width(source, leaf), ext_signed);
                    const_total = negate ? const_total - extended : const_total + extended;
                    continue;
                }
                sn_obj_id_t value = sn_vec_at(sn_obj_id_t, &source->copy_ids, leaf);
                assert(value != SN_INVALID_ID);
                if (sn_obj_width(mapped, value) != root_width)
                    value = sn_tech_add_cast(mapped, value, root_width, ext_signed);
                if (negate)
                {
                    value = sn_module_add_operator(mapped, SN_BIT_NOT, root_width, false, 1, &value, NULL);
                    extra_ones++;
                }
                operands[operand_count++] = value;
            }
            const_total += extra_ones;
            uint64_t mask = root_width >= 64 ? ~UINT64_C(0) : (UINT64_C(1) << root_width) - 1;
            if ((const_total & mask) != 0 || operand_count < 2)
            {
                uint32_t word_count = sn_const_word_count(root_width);
                uint32_t stack_words[8] = {0};
                uint32_t* words =
                    word_count <= 8 ? stack_words : (uint32_t*)calloc(word_count, sizeof(uint32_t));
                assert(words);
                words[0] = (uint32_t)(const_total & mask);
                if (word_count > 1)
                    words[1] = (uint32_t)((const_total & mask) >> 32);
                uint32_t final_bits = root_width & 31u;
                if (final_bits)
                    words[word_count - 1] &= (1u << final_bits) - 1u;
                operands[operand_count++] = sn_module_add_const(mapped, root_width, false, words, NULL);
                if (words != stack_words)
                    free(words);
            }
            const char* name = sn_obj_name_id(source, old_object) == SN_INVALID_ID
                                   ? NULL
                                   : sn_obj_name(source, old_object);
            sn_obj_id_t result =
                operand_count >= 2
                    ? sn_add_map_csa_tree(mapped, carry, operands, operand_count, root_width,
                                          sn_obj_is_signed(source, old_object), name)
                    : sn_tech_add_cast(mapped, operands[0], root_width,
                                       sn_obj_is_signed(source, old_object));
            free(operands);
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
        else if (sn_tech_srl_plan(source, srl_plans, old_object))
        {
            const sn_tech_srl_plan_t* plan = sn_tech_srl_plan(source, srl_plans, old_object);
            uint32_t key = sn_obj_data(source, plan->taps[0]);
            if (srl_built[key] == SN_INVALID_ID)
            {
                bool has_enable = plan->enable != SN_INVALID_ID;
                uint32_t addr_widths[SN_TECH_SRL_MAX_TAPS];
                bool tap_registered[SN_TECH_SRL_MAX_TAPS];
                for (uint32_t t = 0; t < plan->tap_count; t++)
                {
                    addr_widths[t] =
                        sn_obj_width(source, sn_obj_fanin(source, plan->taps[t], SN_MEM_READ_ADDRESS));
                    tap_registered[t] = plan->tap_regs[t] != SN_INVALID_ID;
                }
                sn_module_id_t primitive = sn_map_srl_primitive_module(
                    design, sn_obj_width(source, plan->memory), plan->depth, plan->tap_count, addr_widths,
                    tap_registered, has_enable);
                sn_obj_id_t inputs[3 + 3 * SN_TECH_SRL_MAX_TAPS];
                uint32_t input_count = 0;
                inputs[input_count++] = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->clock);
                if (has_enable)
                    inputs[input_count++] = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->enable);
                for (uint32_t t = 0; t < plan->tap_count; t++)
                    inputs[input_count++] = sn_vec_at(
                        sn_obj_id_t, &source->copy_ids, sn_obj_fanin(source, plan->taps[t], SN_MEM_READ_ADDRESS));
                inputs[input_count++] = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->din);
                for (uint32_t t = 0; t < plan->tap_count; t++)
                {
                    if (!tap_registered[t])
                        continue;
                    inputs[input_count++] =
                        sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->tap_clocks[t]);
                    inputs[input_count++] =
                        plan->tap_enables[t] == SN_INVALID_ID
                            ? sn_tech_add_uint_const(mapped, 1, 1)
                            : sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->tap_enables[t]);
                }
                srl_built[key] = sn_module_add_inst(mapped, primitive, input_count, inputs, NULL, NULL);
            }
            sn_obj_connect(mapped, placeholder, 0,
                           sn_inst_output(mapped, srl_built[key], plan->tap_index));
        }
        else if (sn_tech_srlreg_plan(source, srlreg_plans, reg_slot, old_object))
        {
            const sn_tech_srlreg_plan_t* plan = sn_tech_srlreg_plan(source, srlreg_plans, reg_slot, old_object);
            bool has_enable = plan->enable != SN_INVALID_ID;
            sn_module_id_t primitive = sn_map_srl_chain_primitive_module(
                design, sn_obj_width(source, old_object), plan->depth, has_enable, plan->negedge);
            sn_obj_id_t inputs[3];
            uint32_t input_count = 0;
            inputs[input_count++] = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->clock);
            if (has_enable)
                inputs[input_count++] = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->enable);
            inputs[input_count++] = sn_vec_at(sn_obj_id_t, &source->copy_ids, plan->din);
            sn_obj_id_t inst = sn_module_add_inst(mapped, primitive, input_count, inputs, NULL, NULL);
            sn_obj_connect(mapped, placeholder, 0, sn_inst_output(mapped, inst, 0));
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
        bool special = map_mul[old_object] || map_add[old_object] || map_mac[old_object] ||
                       map_csa[old_object] != SIZE_MAX || forwarded[old_object] ||
                       sn_tech_srl_plan(source, srl_plans, old_object) != NULL ||
                       sn_tech_srlreg_plan(source, srlreg_plans, reg_slot, old_object) != NULL ||
                       (read_plan && read_plan->memory != SN_INVALID_ID);
        if (new_object == SN_INVALID_ID || special)
            continue;
        sn_module_dup_obj_metadata(mapped, new_object, source, old_object);
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
    sn_module_link_pairs(mapped);

    if (options->map_memories)
        sn_tech_break_inst_cycles(mapped);

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
    free(map_mac);
    free(map_csa);
    sn_vec_destroy(&csa_leaves);
    sn_vec_destroy(&csa_flags);
    sn_vec_destroy(&csa_plans);
    free(read_plans);
    free(srl_plans);
    free(srl_built);
    free(srlreg_plans);
    free(reg_slot);
    free(refcount);
    free(read_reg);
    free(read_reg_hops);
    free(read_reg_hop_counts);
    free(forwarded);
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
        if (frame->next_inst < module->type_objects[SN_INST].size)
        {
            sn_module_id_t child_id = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], frame->next_inst++));
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
        for (size_t i = 0; i < module->type_objects[SN_INST].size; i++)
        {
            sn_module_id_t child_id = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i));
            const sn_module_t* child = sn_design_get_module_const(design, child_id);
            const char* name = sn_name_get(&design->names, child->name);
            if (strncmp(name, "__sn_RAM", 8) == 0 || strncmp(name, "__sn_URAM", 9) == 0)
                total.mem_insts++;
            else if (strncmp(name, "__sn_DSP", 8) == 0)
                total.dsp_insts++;
            else if (strncmp(name, "__sn_CARRY", 10) == 0)
                total.carry_insts++;
            else if (strncmp(name, "__sn_SRL", 8) == 0)
                total.srl_insts++;
            else
            {
                total.mem_insts += cached[child_id].mem_insts;
                total.dsp_insts += cached[child_id].dsp_insts;
                total.carry_insts += cached[child_id].carry_insts;
                total.srl_insts += cached[child_id].srl_insts;
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
        if (frame->next_inst < module->type_objects[SN_INST].size)
        {
            sn_module_id_t child = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], frame->next_inst++));
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
        for (size_t i = 0; i < module->type_objects[SN_INST].size; i++)
        {
            sn_module_id_t child = sn_inst_module_id(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i));
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
        for (size_t i = 0; i < mapped->type_objects[SN_INST].size; i++)
        {
            sn_module_id_t child = sn_inst_module_id(mapped, sn_vec_at(sn_obj_id_t, &mapped->type_objects[SN_INST], i));
            if (child < original_count)
                sn_obj_set_data(mapped, sn_vec_at(sn_obj_id_t, &mapped->type_objects[SN_INST], i), replacements[child]);
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
