/**CFile****************************************************************

  FileName    [snMiniLut.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Analysis and reconstruction of SN LUTs from MiniLUT networks.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMiniLut.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MINI_LUT_H
#define SN_MINI_LUT_H

// Utilities for validating and analyzing the MiniLUT files written by ABC's
// "&write -l" command.

#include "snBoundary.h"
#include "aig/miniaig/minilut.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

ABC_NAMESPACE_HEADER_START

typedef struct sn_lut_stats_t
{
    uint32_t pi_count;
    uint32_t po_count;
    uint32_t register_count;
    uint32_t lut_count;
    uint32_t lut_size;
    uint32_t lut_levels;
    uint32_t top_output_levels;
    uint32_t register_control_levels;
    uint32_t memory_input_levels;
    uint32_t primitive_input_levels;
    uint32_t loop_input_levels;
    uint32_t register_input_levels;
} sn_lut_stats_t;

static inline uint32_t sn_lut_max_u32(uint32_t a, uint32_t b)
{
    return a > b ? a : b;
}

static inline Mini_Lut_t* sn_lut_load(const char* file_name)
{
    if (!file_name)
        return NULL;
    FILE* file = fopen(file_name, "rb");
    if (!file)
        return NULL;
    int32_t node_count = 0, register_count = 0, lut_size = 0;
    bool valid = fread(&node_count, sizeof(node_count), 1, file) == 1 &&
                 fread(&register_count, sizeof(register_count), 1, file) == 1 &&
                 fread(&lut_size, sizeof(lut_size), 1, file) == 1;
    uint64_t array_count = 0, truth_count = 0;
    if (valid && node_count >= 2 && register_count >= 0 && register_count <= node_count && lut_size >= 2 &&
        lut_size <= 16)
    {
        array_count = (uint64_t)(uint32_t)node_count * (uint32_t)lut_size;
        truth_count = (uint64_t)(uint32_t)node_count * (uint32_t)Mini_LutWordNum(lut_size);
        valid = array_count <= SIZE_MAX / sizeof(int) && truth_count <= SIZE_MAX / sizeof(unsigned);
    }
    else
        valid = false;
    if (valid)
    {
        uint64_t payload_bytes = (array_count + truth_count) * sizeof(uint32_t);
#if defined(_WIN32)
        __int64 position = _ftelli64(file);
        valid = position >= 0 && _fseeki64(file, 0, SEEK_END) == 0;
        __int64 end = valid ? _ftelli64(file) : -1;
        valid = end >= position && (uint64_t)(end - position) == payload_bytes &&
                _fseeki64(file, position, SEEK_SET) == 0;
#else
        long position = ftell(file);
        valid = position >= 0 && fseek(file, 0, SEEK_END) == 0;
        long end = valid ? ftell(file) : -1;
        valid = end >= position && (uint64_t)(end - position) == payload_bytes && fseek(file, position, SEEK_SET) == 0;
#endif
    }
    Mini_Lut_t* lut = valid ? (Mini_Lut_t*)calloc(1, sizeof(Mini_Lut_t)) : NULL;
    if (lut)
    {
        lut->nSize = lut->nCap = node_count;
        lut->nRegs = register_count;
        lut->LutSize = lut_size;
        lut->pArray = (int*)malloc((size_t)array_count * sizeof(int));
        lut->pTruths = (unsigned*)malloc((size_t)truth_count * sizeof(unsigned));
        if (!lut->pArray || !lut->pTruths)
            valid = false;
        else
            valid = fread(lut->pArray, sizeof(int), (size_t)array_count, file) == array_count &&
                    fread(lut->pTruths, sizeof(unsigned), (size_t)truth_count, file) == truth_count &&
                    fgetc(file) == EOF && !ferror(file);
    }
    if (fclose(file) != 0)
        valid = false;
    if (!valid || !lut)
    {
        if (lut)
            Mini_LutStop(lut);
        return NULL;
    }
    for (int object = 2; object < node_count; object++)
    {
        int* fanins = lut->pArray + (size_t)object * lut_size;
        if (fanins[0] == MINI_LUT_NULL)
        {
            for (int i = 1; i < lut_size; i++)
                valid &= fanins[i] == MINI_LUT_NULL;
            continue;
        }
        if (fanins[0] < 0 || fanins[0] >= object)
            valid = false;
        else if (fanins[0] >= 2)
        {
            int* source = lut->pArray + (size_t)fanins[0] * lut_size;
            if (source[0] != MINI_LUT_NULL && source[1] == MINI_LUT_NULL2)
                valid = false;
        }
        if (fanins[1] == MINI_LUT_NULL2)
        {
            for (int i = 2; i < lut_size; i++)
                valid &= fanins[i] == MINI_LUT_NULL;
            continue;
        }
        bool padding = false;
        for (int i = 0; i < lut_size; i++)
            if (fanins[i] == MINI_LUT_NULL)
                padding = true;
            else if (padding || fanins[i] < 0 || fanins[i] >= object || fanins[i] == MINI_LUT_NULL2)
                valid = false;
            else if (fanins[i] >= 2)
            {
                int* source = lut->pArray + (size_t)fanins[i] * lut_size;
                if (source[0] != MINI_LUT_NULL && source[1] == MINI_LUT_NULL2)
                    valid = false;
            }
    }
    if (!valid)
    {
        Mini_LutStop(lut);
        return NULL;
    }
    return lut;
}

static inline bool sn_lut_interface_matches(Mini_Lut_t* lut, const sn_blast_boundary_t* boundary)
{
    if (!lut || !boundary)
        return false;
    uint32_t pi_count = 0, po_count = 0;
    int object;
    Mini_LutForEachPi(lut, object)
        pi_count++;
    Mini_LutForEachPo(lut, object)
        po_count++;
    uint32_t register_count = (uint32_t)Mini_LutRegNum(lut);
    if (pi_count != boundary->cis.size || po_count != boundary->cos.size ||
        register_count != boundary->register_bits || register_count > pi_count || register_count > po_count)
        return false;
    for (uint32_t i = 0; i < register_count; i++)
        if (sn_vec_at(sn_blast_boundary_bit_t, &boundary->cis, pi_count - register_count + i).kind !=
                SN_BLAST_BOUNDARY_REG_OUTPUT ||
            sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, po_count - register_count + i).kind !=
                SN_BLAST_BOUNDARY_REG_INPUT)
            return false;
    return true;
}

// Validates MiniLUT topology and its positional interface against the boundary
// saved while deriving the pre-ABC MiniAIG. Levels count LUTs; constants and
// CIs have level zero. The boundary CO vector is in the same order as MiniLUT
// POs, so depths can be reported separately for top outputs, hard-block inputs,
// register controls, and register inputs.
static inline sn_lut_stats_t sn_lut_analyze(Mini_Lut_t* lut, const sn_blast_boundary_t* boundary)
{
    assert(lut && boundary);
    assert(sn_lut_interface_matches(lut, boundary));
    assert(Mini_LutSize(lut) >= 2 && Mini_LutSize(lut) <= 16);
    size_t object_count = (size_t)Mini_LutNodeNum(lut);
    uint32_t* levels = (uint32_t*)calloc(object_count, sizeof(uint32_t));
    assert(levels);
    sn_lut_stats_t stats = {0};
    stats.lut_size = (uint32_t)Mini_LutSize(lut);

    for (int object = 0; object < Mini_LutNodeNum(lut); object++)
    {
        if (Mini_LutNodeIsConst(lut, object))
            continue;
        if (Mini_LutNodeIsPi(lut, object))
        {
            stats.pi_count++;
            continue;
        }
        if (Mini_LutNodeIsNode(lut, object))
        {
            uint32_t level = 0;
            int fanin, slot;
            Mini_LutForEachFanin(lut, object, fanin, slot)
            {
                assert(fanin >= 0 && fanin < object);
                level = sn_lut_max_u32(level, levels[fanin]);
            }
            levels[object] = level + 1;
            stats.lut_levels = sn_lut_max_u32(stats.lut_levels, levels[object]);
            stats.lut_count++;
            continue;
        }
        assert(Mini_LutNodeIsPo(lut, object));
        int fanin = Mini_LutNodeFanin(lut, object, 0);
        assert(fanin >= 0 && fanin < object);
        levels[object] = levels[fanin];
        stats.po_count++;
    }

    stats.register_count = (uint32_t)Mini_LutRegNum(lut);

    uint32_t po_index = 0;
    int object;
    Mini_LutForEachPo(lut, object)
    {
        sn_blast_boundary_kind_t kind =
            sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, po_index++).kind;
        uint32_t level = levels[object];
        if (kind == SN_BLAST_BOUNDARY_TOP_PO)
            stats.top_output_levels = sn_lut_max_u32(stats.top_output_levels, level);
        else if (kind == SN_BLAST_BOUNDARY_REG_CONTROL)
            stats.register_control_levels = sn_lut_max_u32(stats.register_control_levels, level);
        else if (kind == SN_BLAST_BOUNDARY_MEMORY_INPUT)
            stats.memory_input_levels = sn_lut_max_u32(stats.memory_input_levels, level);
        else if (kind == SN_BLAST_BOUNDARY_PRIMITIVE_INPUT)
            stats.primitive_input_levels = sn_lut_max_u32(stats.primitive_input_levels, level);
        else if (kind == SN_BLAST_BOUNDARY_LOOP_INPUT)
            stats.loop_input_levels = sn_lut_max_u32(stats.loop_input_levels, level);
        else if (kind == SN_BLAST_BOUNDARY_REG_INPUT)
            stats.register_input_levels = sn_lut_max_u32(stats.register_input_levels, level);
        else
            assert(false);
    }
    assert(po_index == stats.po_count);
    free(levels);
    return stats;
}

static inline sn_obj_id_t sn_lut_pack_bits(sn_module_t* module, const sn_obj_id_t* bits, uint32_t width,
                                            const char* name)
{
    assert(width && bits);
    if (width == 1)
        return bits[0];
    return sn_module_add_operator(module, SN_CONCAT, width, false, width, bits, name);
}

static inline uint64_t sn_lut_node_truth(Mini_Lut_t* lut, int object)
{
    unsigned* words = Mini_LutNodeTruth(lut, object);
    return (uint64_t)words[0] | (Mini_LutWordNum(Mini_LutSize(lut)) > 1 ? (uint64_t)words[1] << 32 : 0);
}

// Decomposes a mapped LUT wider than the physical SN_LUT6 primitive by Shannon expansion on its most-significant
// inputs. The leaves are LUT6 objects and each internal selector is another LUT3. MiniLUT and SN both use fanin 0 as
// the least-significant truth-table variable, so each cofactor is a contiguous truth-table interval.
static inline sn_obj_id_t sn_lut_add_physical_rec(sn_module_t* module, const sn_obj_id_t* fanins,
                                                   uint32_t count, const unsigned* truth, uint32_t offset)
{
    assert(module && fanins && truth && count > 0 && count <= 16);
    if (count <= 6)
    {
        uint64_t leaf_truth = 0;
        for (uint32_t bit = 0; bit < (UINT32_C(1) << count); bit++)
            leaf_truth |= (uint64_t)((truth[(offset + bit) >> 5] >> ((offset + bit) & 31)) & 1) << bit;
        return sn_module_add_lut(module, count, fanins, leaf_truth, "lut");
    }
    uint32_t select_bit = count - 1;
    sn_obj_id_t low = sn_lut_add_physical_rec(module, fanins, select_bit, truth, offset);
    sn_obj_id_t high = sn_lut_add_physical_rec(module, fanins, select_bit, truth,
                                                offset + (UINT32_C(1) << select_bit));
    sn_obj_id_t mux_fanins[3] = {fanins[select_bit], high, low};
    return sn_module_add_lut(module, 3, mux_fanins, UINT64_C(0xd8), "lut_wide_mux");
}

// Reconstructs the MiniLUT combinational network and its top-level/register
// boundary as a new flat SN module. Hard-block and control reconnection is
// added by subsequent reconstruction stages; this core establishes the direct
// MiniLUT-object-to-SN-object mapping and preserves MiniLUT register order.
static inline sn_module_id_t sn_design_add_lut_module(sn_design_t* design, sn_module_id_t source_top_id,
                                                       Mini_Lut_t* lut, const sn_blast_boundary_t* boundary,
                                                       const char* module_name)
{
    assert(design && source_top_id < design->modules.size && lut && boundary && module_name);
    sn_lut_analyze(lut, boundary);
    const sn_module_t* source = sn_design_get_module_const(design, source_top_id);
    sn_module_id_t result_id = sn_design_add_module(design, module_name);
    sn_module_t* result = sn_design_get_module(design, result_id);
    sn_obj_id_t* top_inputs = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * source->obj_types.size);
    sn_obj_id_t* mini_objects = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * Mini_LutNodeNum(lut));
    sn_obj_id_t* co_drivers = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * boundary->cos.size);
    sn_boundary_regs_t regs;
    assert(top_inputs && mini_objects && co_drivers);
    for (size_t i = 0; i < source->obj_types.size; i++)
        top_inputs[i] = SN_INVALID_ID;
    for (int i = 0; i < Mini_LutNodeNum(lut); i++)
        mini_objects[i] = SN_INVALID_ID;

    for (size_t i = 0; i < source->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t old_pi = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PI], i);
        top_inputs[old_pi] = sn_module_add_pi(result, sn_obj_width(source, old_pi), sn_obj_is_signed(source, old_pi),
                                               sn_obj_name(source, old_pi));
    }
    sn_boundary_regs_init(&regs, design, boundary, result, top_inputs);
    uint32_t zero_word = 0, one_word = 1;
    mini_objects[Mini_LutNodeConst0()] = sn_module_add_const(result, 1, false, &zero_word, "lut_const0");
    mini_objects[Mini_LutNodeConst1()] = sn_module_add_const(result, 1, false, &one_word, "lut_const1");

    uint32_t ci_index = 0;
    int mini_object;
    Mini_LutForEachPi(lut, mini_object)
    {
        sn_blast_boundary_bit_t bit = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cis, ci_index++);
        if (bit.kind == SN_BLAST_BOUNDARY_TOP_PI)
        {
            assert(bit.signal.occurrence == 0 && top_inputs[bit.signal.object] != SN_INVALID_ID);
            mini_objects[mini_object] =
                sn_module_add_slice(result, top_inputs[bit.signal.object], (int32_t)bit.signal.bit,
                                    (int32_t)bit.signal.bit, "lut_pi_bit");
        }
        else if (bit.kind == SN_BLAST_BOUNDARY_REG_OUTPUT)
            mini_objects[mini_object] = sn_boundary_reg_output_bit(&regs, bit.owner, bit.signal.bit);
        else if (bit.kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT)
            mini_objects[mini_object] = sn_boundary_loop_output_bit(&regs, bit.owner, bit.signal.bit);
        else if (bit.kind == SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT)
            mini_objects[mini_object] =
                sn_boundary_primitive_output_bit(&regs, bit.owner, bit.port, bit.signal.bit);
        else
            assert(false);
    }
    assert(ci_index == boundary->cis.size);

    Mini_LutForEachNode(lut, mini_object)
    {
        sn_obj_id_t fanins[16];
        int fanin, slot, count = 0;
        Mini_LutForEachFanin(lut, mini_object, fanin, slot)
        {
            assert(count < 16 && mini_objects[fanin] != SN_INVALID_ID);
            fanins[count++] = mini_objects[fanin];
        }
        mini_objects[mini_object] = count <= 6
                                         ? sn_module_add_lut(result, (uint32_t)count, fanins,
                                                             sn_lut_node_truth(lut, mini_object), "lut")
                                         : sn_lut_add_physical_rec(result, fanins, (uint32_t)count,
                                                                   Mini_LutNodeTruth(lut, mini_object), 0);
    }
    uint32_t co_index = 0;
    Mini_LutForEachPo(lut, mini_object)
    {
        int fanin = Mini_LutNodeFanin(lut, mini_object, 0);
        assert(mini_objects[fanin] != SN_INVALID_ID);
        co_drivers[co_index++] = mini_objects[fanin];
    }
    assert(co_index == boundary->cos.size);

    co_index = 0;
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t old_po = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        uint32_t width = sn_obj_width(source, old_po);
        sn_obj_id_t* bits = co_drivers + co_index;
        for (uint32_t bit = 0; bit < width; bit++)
        {
            sn_blast_boundary_bit_t endpoint = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, co_index + bit);
            assert(endpoint.kind == SN_BLAST_BOUNDARY_TOP_PO && endpoint.port == i && endpoint.signal.bit == bit);
        }
        co_index += width;
        sn_obj_id_t driver = sn_lut_pack_bits(result, bits, width, "lut_po_word");
        sn_module_add_po(result, width, sn_obj_is_signed(source, old_po), sn_obj_name(source, old_po), driver);
    }
    sn_boundary_regs_finish(&regs, co_drivers);
    result = sn_design_get_module(design, result_id);

    free(co_drivers);
    free(mini_objects);
    free(top_inputs);
    if (!sn_module_is_topo(result))
        sn_design_reorder_module_topo(design, result_id);
    assert(sn_module_is_topo(sn_design_get_module_const(design, result_id)));
    return result_id;
}

ABC_NAMESPACE_HEADER_END

#endif
