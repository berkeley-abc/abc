/**CFile****************************************************************

  FileName    [snMapMem.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Mapping technology-independent memories into FPGA memory primitives.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapMem.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MAP_MEM_H
#define SN_MAP_MEM_H

#include "sn.h"
#include "snTech.h"

ABC_NAMESPACE_HEADER_START

typedef enum sn_mem_split_order_t
{
    SN_MEM_SPLIT_AUTO = 0,
    SN_MEM_SPLIT_WIDTH_FIRST,
    SN_MEM_SPLIT_DEPTH_FIRST
} sn_mem_split_order_t;

typedef struct sn_mem_map_options_t
{
    bool allow_lutram_fallback;
    bool allow_register_fallback;
    bool preserve_names;
    uint32_t min_memory_bits;
    uint32_t max_primitives_per_memory;
    sn_mem_split_order_t split_order;
} sn_mem_map_options_t;

static inline sn_mem_map_options_t sn_mem_map_default_options(void)
{
    sn_mem_map_options_t options = {false, false, true, 0, 0, SN_MEM_SPLIT_AUTO};
    return options;
}

// Returns true when a memory's dimensions and port protocol can be represented
// by one technology primitive. This conservative predicate is used before the
// rewriting pass; splitting, packing, and primitive-inst construction are
// the next mapper milestone.
static inline bool sn_mem_tech_supports(const sn_mem_tech_t* tech, uint32_t width, uint32_t depth,
                                        sn_mem_port_mode_t port_mode)
{
    assert(tech);
    if (port_mode != tech->port_mode || !width || !depth || width > UINT32_MAX / depth)
        return false;
    if (width * depth > tech->cap_bits)
        return false;
    if (depth > (1u << tech->address_bits))
        return false;
    for (size_t i = 0; i < tech->width_count; i++)
        if (tech->widths[i] == width)
            return true;
    return false;
}

// Creates a behavioral wrapper for one technology memory shape.  Keeping the
// wrapper as an SN module makes the mapped result simulatable; a later Verilog
// technology writer can replace this module by RAMB/URAM cells.
static inline sn_module_id_t sn_map_mem_primitive_module(sn_design_t* design, const sn_mem_tech_t* tech,
                                                         uint32_t width, uint32_t depth)
{
    char name[128];
    int length = snprintf(name, sizeof(name), "__sn_%s_mem_%u_%u", tech->name, width, depth);
    assert(length >= 0 && (size_t)length < sizeof(name));
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;
    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock = sn_module_add_pi(module, 1, false, "clock");
    sn_obj_id_t enable = sn_module_add_pi(module, 1, false, "enable");
    sn_obj_id_t write_address = sn_module_add_pi(module, 32, false, "write_address");
    sn_obj_id_t data = sn_module_add_pi(module, width, false, "write_data");
    sn_obj_id_t read_address = sn_module_add_pi(module, 32, false, "read_address");
    sn_obj_pair_t pair = sn_module_add_mem_pair(module, width, false, depth, "mem_out", "mem_in");
    sn_module_add_mem_write(module, pair.in, clock, enable, data, write_address, "write");
    sn_obj_id_t read = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, read_address, "read");
    sn_module_add_po(module, width, false, "read_data", read);
    sn_design_reorder_module_topo(design, id);
    return id;
}

ABC_NAMESPACE_HEADER_END

#endif
