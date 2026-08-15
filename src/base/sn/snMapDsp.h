/**CFile****************************************************************

  FileName    [snMapDsp.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Mapping word-level multipliers into FPGA DSP primitives.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapDsp.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MAP_DSP_H
#define SN_MAP_DSP_H

#include "sn.h"
#include "snTech.h"

ABC_NAMESPACE_HEADER_START

typedef struct sn_dsp_map_options_t
{
    bool allow_soft_fallback;
    bool use_preadder;
    bool use_postadder;
    bool preserve_names;
    bool balance_adders;
    bool prune_unused_high_products;
    uint32_t a_unsigned_chunk_width;
    uint32_t b_unsigned_chunk_width;
    uint32_t max_dsps_per_multiply;
} sn_dsp_map_options_t;

static inline sn_dsp_map_options_t sn_dsp_map_default_options(void)
{
    sn_dsp_map_options_t options = {true, false, false, true, true, true, 0, 0, 0};
    return options;
}

static inline bool sn_dsp_tech_supports_mul(const sn_dsp_tech_t* tech, uint32_t a_width, uint32_t b_width,
                                            uint32_t result_width, bool a_signed, bool b_signed)
{
    assert(tech);
    if (!a_width || !b_width || !result_width || a_width > tech->a_width || b_width > tech->b_width ||
        result_width > tech->p_width)
        return false;
    if (a_width < tech->min_a_width || b_width < tech->min_b_width || result_width < tech->min_p_width)
        return false;
    if (tech->signed_only && (!a_signed || !b_signed))
        return false;
    return true;
}

static inline sn_module_id_t sn_map_dsp_primitive_module(sn_design_t* design, const sn_dsp_tech_t* tech,
                                                          uint32_t a_width, uint32_t b_width, uint32_t y_width,
                                                          bool a_signed, bool b_signed)
{
    char name[128];
    int length = snprintf(name, sizeof(name), "__sn_%s_mul_%u_%u_%u_s%u%u", tech->name, a_width, b_width,
                          y_width, a_signed ? 1u : 0u, b_signed ? 1u : 0u);
    assert(length >= 0 && (size_t)length < sizeof(name));
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;
    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t a = sn_module_add_pi(module, a_width, a_signed, "A");
    sn_obj_id_t b = sn_module_add_pi(module, b_width, b_signed, "B");
    sn_obj_id_t fanins[] = {a, b};
    sn_obj_id_t product = sn_module_add_operator(module, SN_MUL, y_width, a_signed || b_signed, 2, fanins, "P");
    sn_module_add_po(module, y_width, a_signed || b_signed, "Y", product);
    return id;
}

ABC_NAMESPACE_HEADER_END

#endif
