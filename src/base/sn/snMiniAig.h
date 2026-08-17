/**CFile****************************************************************

  FileName    [snMiniAig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Reconstruction of SN logic from an unmapped MiniAIG network.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMiniAig.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snMiniAig_h
#define ABC__base__sn__snMiniAig_h

#include "snMiniLut.h"

ABC_NAMESPACE_HEADER_START

static inline sn_obj_id_t sn_aig_lit_object(sn_module_t* module, Mini_Aig_t* aig, const sn_obj_id_t* objects, int lit)
{
    int variable = Mini_AigLit2Var(lit);
    assert(variable >= 0 && variable < Mini_AigNodeNum(aig));
    sn_obj_id_t object = objects[variable];
    assert(object != SN_INVALID_ID);
    if (!Mini_AigLitIsCompl(lit))
        return object;
    if (variable == 0)
    {
        uint32_t one = 1;
        return sn_module_add_const(module, 1, false, &one, "aig_const1");
    }
    return sn_module_add_operator(module, SN_BIT_NOT, 1, false, 1, &object, "aig_inv");
}

// Reconstructs an unmapped combinational MiniAIG as explicit one-bit SN_BIT_AND and SN_BIT_NOT objects. The MiniAIG
// CI/CO order is matched positionally against the boundary recorded by @blast. Register endpoints are reconnected by
// the shared boundary reconstruction stage; RAM/DSP endpoints are rejected by the command until they are supported.
static inline sn_module_id_t sn_design_add_aig_module(sn_design_t* design, sn_module_id_t source_top_id,
                                                       Mini_Aig_t* aig, const sn_blast_boundary_t* boundary,
                                                       const char* module_name)
{
    assert(design && source_top_id < design->modules.size && aig && boundary && module_name);
    assert(Mini_AigRegNum(aig) == 0);
    assert((size_t)Mini_AigPiNum(aig) == boundary->cis.size);
    assert((size_t)Mini_AigPoNum(aig) == boundary->cos.size);

    const sn_module_t* source = sn_design_get_module_const(design, source_top_id);
    sn_module_id_t result_id = sn_design_add_module(design, module_name);
    sn_module_t* result = sn_design_get_module(design, result_id);
    sn_obj_id_t* top_inputs = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * source->obj_types.size);
    sn_obj_id_t* objects = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * Mini_AigNodeNum(aig));
    sn_obj_id_t* drivers = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * boundary->cos.size);
    sn_boundary_regs_t regs;
    assert(top_inputs && objects && drivers);
    for (size_t i = 0; i < source->obj_types.size; i++)
        top_inputs[i] = SN_INVALID_ID;
    for (int i = 0; i < Mini_AigNodeNum(aig); i++)
        objects[i] = SN_INVALID_ID;

    for (size_t i = 0; i < source->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t old_pi = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PI], i);
        top_inputs[old_pi] = sn_module_add_pi(result, sn_obj_width(source, old_pi), sn_obj_is_signed(source, old_pi),
                                               sn_obj_name(source, old_pi));
    }
    sn_boundary_regs_init(&regs, design, boundary, result, top_inputs);
    uint32_t zero = 0;
    objects[0] = sn_module_add_const(result, 1, false, &zero, "aig_const0");

    uint32_t ci_index = 0;
    int mini_object;
    Mini_AigForEachPi(aig, mini_object)
    {
        sn_blast_boundary_bit_t bit = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cis, ci_index++);
        if (bit.kind == SN_BLAST_BOUNDARY_TOP_PI)
        {
            assert(bit.signal.occurrence == 0 && top_inputs[bit.signal.object] != SN_INVALID_ID);
            objects[mini_object] = sn_module_add_slice(result, top_inputs[bit.signal.object], (int32_t)bit.signal.bit,
                                                        (int32_t)bit.signal.bit, "aig_pi_bit");
        }
        else if (bit.kind == SN_BLAST_BOUNDARY_REG_OUTPUT)
            objects[mini_object] = sn_boundary_reg_output_bit(&regs, bit.owner, bit.signal.bit);
        else if (bit.kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT)
            objects[mini_object] = sn_boundary_loop_output_bit(&regs, bit.owner, bit.signal.bit);
        else if (bit.kind == SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT)
            objects[mini_object] = sn_boundary_primitive_output_bit(&regs, bit.owner, bit.port, bit.signal.bit);
        else
            assert(false);
    }
    assert(ci_index == boundary->cis.size);

    Mini_AigForEachAnd(aig, mini_object)
    {
        sn_obj_id_t fanins[2] = {
            sn_aig_lit_object(result, aig, objects, Mini_AigNodeFanin0(aig, mini_object)),
            sn_aig_lit_object(result, aig, objects, Mini_AigNodeFanin1(aig, mini_object))};
        objects[mini_object] = sn_module_add_operator(result, SN_BIT_AND, 1, false, 2, fanins, "aig_and");
    }

    uint32_t co_index = 0;
    Mini_AigForEachPo(aig, mini_object)
        drivers[co_index++] = sn_aig_lit_object(result, aig, objects, Mini_AigNodeFanin0(aig, mini_object));
    assert(co_index <= boundary->cos.size);

    co_index = 0;
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t old_po = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        uint32_t width = sn_obj_width(source, old_po);
        for (uint32_t bit = 0; bit < width; bit++)
        {
            sn_blast_boundary_bit_t endpoint = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, co_index + bit);
            assert(endpoint.kind == SN_BLAST_BOUNDARY_TOP_PO && endpoint.port == i && endpoint.signal.bit == bit);
        }
        sn_obj_id_t driver = sn_lut_pack_bits(result, drivers + co_index, width, "aig_po_word");
        sn_module_add_po(result, width, sn_obj_is_signed(source, old_po), sn_obj_name(source, old_po), driver);
        co_index += width;
    }
    assert(co_index <= boundary->cos.size);
    sn_boundary_regs_finish(&regs, drivers);
    result = sn_design_get_module(design, result_id);

    free(drivers);
    free(objects);
    free(top_inputs);
    if (!sn_module_is_topo(result))
        sn_design_reorder_module_topo(design, result_id);
    assert(sn_module_is_topo(sn_design_get_module_const(design, result_id)));
    return result_id;
}

ABC_NAMESPACE_HEADER_END

#endif
