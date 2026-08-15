/**CFile****************************************************************

  FileName    [snMapAdd.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Mapping word-level adders and subtractors into FPGA carry primitives.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapAdd.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MAP_ADD_H
#define SN_MAP_ADD_H

// Maps word-level addition and subtraction into preserved FPGA carry-chain
// primitive insts. The surrounding propagate/invert logic remains ordinary SN
// logic and can subsequently be mapped into LUTs.

#include "sn.h"
#include "snTech.h"

ABC_NAMESPACE_HEADER_START

typedef struct sn_add_map_options_t
{
    uint32_t min_width;
    bool map_add;
    bool map_sub;
    bool preserve_names;
} sn_add_map_options_t;

static inline sn_add_map_options_t sn_add_map_default_options(void)
{
    sn_add_map_options_t options = {0, true, true, true};
    return options;
}

static inline bool sn_add_tech_supports(const sn_carry_tech_t* tech, const sn_add_map_options_t* options,
                                        sn_obj_type_t type, uint32_t width)
{
    assert(tech && options);
    uint32_t min_width = options->min_width ? options->min_width : tech->min_op_width;
    return width >= min_width && ((type == SN_ADD && options->map_add) || (type == SN_SUB && options->map_sub));
}

static inline sn_obj_id_t sn_add_slice_bit(sn_module_t* module, sn_obj_id_t value, uint32_t bit)
{
    assert(bit < sn_obj_width(module, value));
    return sn_module_add_slice(module, value, (int32_t)bit, (int32_t)bit, NULL);
}

// The behavioral body is identical to the Xilinx CARRY4 simulation model. It
// permits standalone SN simulation and CEC while the __sn_ prefix marks the
// module as a hard primitive that hierarchy collapse and LUT mapping preserve.
static inline sn_module_id_t sn_add_carry_primitive_module(sn_design_t* design, const sn_carry_tech_t* tech)
{
    assert(design && tech && tech->width == 4);
    char name[64];
    int length = snprintf(name, sizeof(name), "__sn_%s", tech->name);
    assert(length >= 0 && (size_t)length < sizeof(name));
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;

    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t ci = sn_module_add_pi(module, 1, false, "CI");
    sn_obj_id_t cyinit = sn_module_add_pi(module, 1, false, "CYINIT");
    sn_obj_id_t di = sn_module_add_pi(module, 4, false, "DI");
    sn_obj_id_t s = sn_module_add_pi(module, 4, false, "S");
    sn_obj_id_t init_fanins[2] = {ci, cyinit};
    sn_obj_id_t carry = sn_module_add_operator(module, SN_BIT_OR, 1, false, 2, init_fanins, NULL);
    sn_obj_id_t o_bits[4], co_bits[4];
    for (uint32_t bit = 0; bit < 4; bit++)
    {
        sn_obj_id_t s_bit = sn_add_slice_bit(module, s, bit);
        sn_obj_id_t di_bit = sn_add_slice_bit(module, di, bit);
        sn_obj_id_t xor_fanins[2] = {s_bit, carry};
        o_bits[bit] = sn_module_add_operator(module, SN_BIT_XOR, 1, false, 2, xor_fanins, NULL);
        co_bits[bit] = sn_module_add_mux(module, s_bit, carry, di_bit, NULL);
        carry = co_bits[bit];
    }
    sn_obj_id_t o = sn_module_add_concat(module, 4, o_bits, NULL);
    sn_obj_id_t co = sn_module_add_concat(module, 4, co_bits, NULL);
    sn_module_add_po(module, 4, false, "O", o);
    sn_module_add_po(module, 4, false, "CO", co);
    assert(sn_module_is_topo(module));
    return id;
}

static inline sn_obj_id_t sn_add_resize(sn_module_t* module, sn_obj_id_t value, uint32_t width, bool is_signed)
{
    if (sn_obj_width(module, value) == width && sn_obj_is_signed(module, value) == is_signed)
        return value;
    return sn_module_add_operator(module, SN_CAST, width, is_signed, 1, &value, NULL);
}

static inline sn_obj_id_t sn_add_pad_chunk(sn_module_t* module, sn_obj_id_t value, uint32_t width)
{
    assert(width && width <= 4 && sn_obj_width(module, value) == width);
    if (width == 4)
        return value;
    sn_obj_id_t zero = sn_module_add_named_obj(module, SN_CONST0, 4 - width, false, 0, NULL);
    sn_obj_id_t fanins[2] = {value, zero};
    return sn_module_add_concat(module, 2, fanins, NULL);
}

// Implements A+B or A-B exactly as Yosys's Xilinx $alu mapping: DI=A,
// S=A^B (or A^~B), and subtraction starts the carry chain at one.
static inline sn_obj_id_t sn_add_map_carry_chain(sn_module_t* module, const sn_carry_tech_t* tech,
                                                 sn_obj_type_t type, sn_obj_id_t a, sn_obj_id_t b,
                                                 uint32_t result_width, bool result_signed, const char* name)
{
    assert(module && tech && tech->width == 4 && (type == SN_ADD || type == SN_SUB));
    assert(a < module->obj_types.size && b < module->obj_types.size && result_width);
    bool signed_operands = sn_obj_is_signed(module, a) && sn_obj_is_signed(module, b);
    a = sn_add_resize(module, a, result_width, signed_operands);
    b = sn_add_resize(module, b, result_width, signed_operands);
    if (type == SN_SUB)
        b = sn_module_add_operator(module, SN_BIT_NOT, result_width, signed_operands, 1, &b, NULL);
    sn_obj_id_t xor_fanins[2] = {a, b};
    sn_obj_id_t propagate =
        sn_module_add_operator(module, SN_BIT_XOR, result_width, false, 2, xor_fanins, NULL);
    sn_obj_id_t zero = sn_module_add_named_obj(module, SN_CONST0, 1, false, 0, NULL);
    sn_obj_id_t one = sn_module_add_named_obj(module, SN_CONST1, 1, false, 0, NULL);
    sn_obj_id_t carry = zero;
    sn_module_id_t primitive = sn_add_carry_primitive_module(module->design, tech);
    uint32_t chunk_count = (result_width + 3) / 4;
    sn_obj_id_t* chunks = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * chunk_count);
    assert(chunks);
    for (uint32_t chunk = 0; chunk < chunk_count; chunk++)
    {
        uint32_t offset = chunk * 4;
        uint32_t width = result_width - offset < 4 ? result_width - offset : 4;
        sn_obj_id_t di = sn_module_add_slice(module, a, (int32_t)(offset + width - 1), (int32_t)offset, NULL);
        sn_obj_id_t s =
            sn_module_add_slice(module, propagate, (int32_t)(offset + width - 1), (int32_t)offset, NULL);
        di = sn_add_pad_chunk(module, di, width);
        s = sn_add_pad_chunk(module, s, width);
        sn_obj_id_t inputs[4] = {carry, chunk == 0 && type == SN_SUB ? one : zero, di, s};
        const char* output_names[2] = {NULL, NULL};
        sn_obj_id_t inst = sn_module_add_inst(module, primitive, 4, inputs, NULL, output_names);
        chunks[chunk] = sn_inst_output(module, inst, 0);
        sn_obj_id_t co = sn_inst_output(module, inst, 1);
        carry = sn_add_slice_bit(module, co, 3);
    }
    sn_obj_id_t result = chunk_count == 1 ? chunks[0] : sn_module_add_concat(module, chunk_count, chunks, NULL);
    free(chunks);
    if (sn_obj_width(module, result) != result_width)
        result = sn_module_add_slice(module, result, (int32_t)result_width - 1, 0, NULL);
    if (sn_obj_is_signed(module, result) != result_signed)
        result = sn_module_add_operator(module, SN_CAST, result_width, result_signed, 1, &result, name);
    return result;
}

ABC_NAMESPACE_HEADER_END

#endif
