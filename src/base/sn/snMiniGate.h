/**CFile****************************************************************

  FileName    [snMiniGate.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Reconstruction of technology-mapped SN gates from mini-mapping data.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMiniGate.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snMiniGate_h
#define ABC__base__sn__snMiniGate_h

#include "snMiniLut.h"

ABC_NAMESPACE_HEADER_START

typedef uint32_t (*sn_gate_id_resolver_t)(void* context, const char* gate_name);

// Reconstructs ABC's mini-mapping array as one-bit SN_GATE objects. Mini-mapping numbers CIs first and mapped nodes
// afterward in topological order. Gate names stored at the end of the array are resolved into the current library's
// stable gate IDs; the name is also retained as the SN object name for structural Verilog emission.
static inline sn_module_id_t sn_design_add_gate_module(sn_design_t* design, sn_module_id_t source_top_id,
                                                        const int* mapping, size_t mapping_count,
                                                        const sn_blast_boundary_t* boundary,
                                                        sn_gate_id_resolver_t resolver, void* resolver_context,
                                                        const char* module_name)
{
    assert(design && source_top_id < design->modules.size && mapping && boundary && resolver && module_name);
    if (mapping_count < 4 || mapping[0] < 0 || mapping[1] < 0 || mapping[2] < 0 || mapping[3] < 0)
        return SN_INVALID_ID;
    uint32_t ci_count = (uint32_t)mapping[0];
    uint32_t co_count = (uint32_t)mapping[1];
    uint32_t node_count = (uint32_t)mapping[2];
    uint32_t reg_count = (uint32_t)mapping[3];
    if (reg_count != 0 || ci_count != boundary->cis.size || co_count != boundary->cos.size ||
        node_count > UINT32_MAX - ci_count)
        return SN_INVALID_ID;

    // Validate the complete structural prefix and resolve all bounded gate-name strings before mutating the design.
    // A changed genlib or malformed mini-mapping can otherwise leave a partially constructed module behind.
    size_t position = 4;
    uint32_t* fanin_counts = node_count ? (uint32_t*)malloc(sizeof(uint32_t) * node_count) : NULL;
    const uint32_t** fanin_indices =
        node_count ? (const uint32_t**)malloc(sizeof(uint32_t*) * node_count) : NULL;
    uint32_t* gate_ids = node_count ? (uint32_t*)malloc(sizeof(uint32_t) * node_count) : NULL;
    bool valid = true;
    assert((fanin_counts && fanin_indices && gate_ids) || node_count == 0);
    for (uint32_t i = 0; valid && i < node_count; i++)
    {
        if (position >= mapping_count || mapping[position] < 0)
        {
            valid = false;
            break;
        }
        uint32_t count = (uint32_t)mapping[position++];
        if (count > mapping_count - position)
        {
            valid = false;
            break;
        }
        fanin_counts[i] = count;
        fanin_indices[i] = (const uint32_t*)(mapping + position);
        for (uint32_t k = 0; k < count; k++)
            if (mapping[position + k] < 0 || (uint32_t)mapping[position + k] >= ci_count + i)
                valid = false;
        position += count;
    }
    if (valid && co_count > mapping_count - position)
        valid = false;
    const uint32_t* output_indices = valid ? (const uint32_t*)(mapping + position) : NULL;
    for (uint32_t i = 0; valid && i < co_count; i++)
        if (mapping[position + i] < 0 || (uint32_t)mapping[position + i] >= ci_count + node_count)
            valid = false;
    if (valid)
        position += co_count;
    const char* gate_names = valid ? (const char*)(mapping + position) : NULL;
    const char* gate_name = gate_names;
    size_t name_bytes = valid ? (mapping_count - position) * sizeof(int) : 0;
    for (uint32_t i = 0; valid && i < node_count; i++)
    {
        const char* end = (const char*)memchr(gate_name, '\0', name_bytes);
        if (!end || end == gate_name)
        {
            valid = false;
            break;
        }
        gate_ids[i] = resolver(resolver_context, gate_name);
        if (gate_ids[i] == SN_INVALID_ID)
        {
            valid = false;
            break;
        }
        size_t length = (size_t)(end - gate_name) + 1;
        gate_name += length;
        name_bytes -= length;
    }
    if (!valid)
    {
        free(gate_ids);
        free(fanin_indices);
        free(fanin_counts);
        return SN_INVALID_ID;
    }

    const sn_module_t* source = sn_design_get_module_const(design, source_top_id);
    sn_module_id_t result_id = sn_design_add_module(design, module_name);
    sn_module_t* result = sn_design_get_module(design, result_id);
    sn_obj_id_t* top_inputs = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * source->obj_types.size);
    sn_obj_id_t* objects = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * (ci_count + node_count));
    sn_boundary_regs_t regs;
    assert(top_inputs && objects);
    for (size_t i = 0; i < source->obj_types.size; i++)
        top_inputs[i] = SN_INVALID_ID;
    for (uint32_t i = 0; i < ci_count + node_count; i++)
        objects[i] = SN_INVALID_ID;

    for (size_t i = 0; i < source->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t old_pi = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PI], i);
        top_inputs[old_pi] = sn_module_add_pi(result, sn_obj_width(source, old_pi), sn_obj_is_signed(source, old_pi),
                                               sn_obj_name(source, old_pi));
    }
    sn_boundary_regs_init(&regs, design, boundary, result, top_inputs);
    for (uint32_t i = 0; i < ci_count; i++)
    {
        sn_blast_boundary_bit_t bit = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cis, i);
        if (bit.kind == SN_BLAST_BOUNDARY_TOP_PI)
        {
            assert(bit.signal.occurrence == 0 && top_inputs[bit.signal.object] != SN_INVALID_ID);
            objects[i] = sn_module_add_slice(result, top_inputs[bit.signal.object], (int32_t)bit.signal.bit,
                                             (int32_t)bit.signal.bit, "gate_pi_bit");
        }
        else if (bit.kind == SN_BLAST_BOUNDARY_REG_OUTPUT)
            objects[i] = sn_boundary_reg_output_bit(&regs, bit.owner, bit.signal.bit);
        else if (bit.kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT)
            objects[i] = sn_boundary_loop_output_bit(&regs, bit.owner, bit.signal.bit);
        else if (bit.kind == SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT)
            objects[i] = sn_boundary_primitive_output_bit(&regs, bit.owner, bit.port, bit.signal.bit);
        else
            assert(false);
    }

    gate_name = gate_names;

    for (uint32_t i = 0; i < node_count; i++)
    {
        uint32_t count = fanin_counts[i];
        sn_obj_id_t* fanins = count ? (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * count) : NULL;
        assert(fanins || count == 0);
        for (uint32_t k = 0; k < count; k++)
        {
            uint32_t fanin = fanin_indices[i][k];
            assert(fanin < ci_count + i && objects[fanin] != SN_INVALID_ID);
            fanins[k] = objects[fanin];
        }
        objects[ci_count + i] = sn_module_add_gate(result, count, fanins, gate_ids[i], gate_name);
        free(fanins);
        gate_name += strlen(gate_name) + 1;
    }

    uint32_t co_index = 0;
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t old_po = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        uint32_t width = sn_obj_width(source, old_po);
        sn_obj_id_t* bits = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * width);
        assert(bits);
        for (uint32_t bit = 0; bit < width; bit++)
        {
            sn_blast_boundary_bit_t endpoint = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, co_index);
            assert(endpoint.kind == SN_BLAST_BOUNDARY_TOP_PO && endpoint.port == i && endpoint.signal.bit == bit);
            assert(output_indices[co_index] < ci_count + node_count);
            bits[bit] = objects[output_indices[co_index++]];
        }
        sn_obj_id_t driver = sn_lut_pack_bits(result, bits, width, "gate_po_word");
        sn_module_add_po(result, width, sn_obj_is_signed(source, old_po), sn_obj_name(source, old_po), driver);
        free(bits);
    }
    assert(co_index <= co_count);
    sn_obj_id_t* co_drivers = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * co_count);
    assert(co_drivers || co_count == 0);
    for (uint32_t i = 0; i < co_count; i++)
    {
        assert(output_indices[i] < ci_count + node_count);
        co_drivers[i] = objects[output_indices[i]];
    }
    sn_boundary_regs_finish(&regs, co_drivers);
    result = sn_design_get_module(design, result_id);

    free(co_drivers);
    free(fanin_indices);
    free(fanin_counts);
    free(gate_ids);
    free(objects);
    free(top_inputs);
    if (!sn_module_is_topo(result))
        sn_design_reorder_module_topo(design, result_id);
    assert(sn_module_is_topo(sn_design_get_module_const(design, result_id)));
    return result_id;
}

ABC_NAMESPACE_HEADER_END

#endif
