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

// Creates a behavioral shift-register primitive: a depth-D memory whose
// writes shift entry k-1 into entry k on the shared clock and enable, with
// din entering at address zero and one asynchronous tap read at the address
// input. This is exactly the shift-register idiom FPGA synthesis maps onto
// SRL cells, and the SN memory body keeps simulation and expanded-blast
// verification exact.
static inline sn_module_id_t sn_map_srl_primitive_module(sn_design_t* design, uint32_t width, uint32_t depth,
                                                         uint32_t tap_count, const uint32_t* addr_widths,
                                                         const bool* tap_registered, bool has_enable)
{
    assert(width && depth >= 2 && tap_count >= 1 && tap_count <= 8 && addr_widths);
    char name[160];
    int length = snprintf(name, sizeof(name), "__sn_SRL_%u_%u_e%u", width, depth, has_enable ? 1u : 0u);
    assert(length >= 0);
    for (uint32_t t = 0; t < tap_count; t++)
    {
        int added = snprintf(name + length, sizeof(name) - (size_t)length, "_%u%s", addr_widths[t],
                             tap_registered && tap_registered[t] ? "r" : "");
        assert(added >= 0 && (size_t)(length + added) < sizeof(name));
        length += added;
    }
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;
    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock = sn_module_add_pi(module, 1, false, "clock");
    sn_obj_id_t enable = has_enable ? sn_module_add_pi(module, 1, false, "enable") : SN_INVALID_ID;
    sn_obj_id_t addresses[8];
    for (uint32_t t = 0; t < tap_count; t++)
    {
        char port[32];
        snprintf(port, sizeof(port), "address%u", t);
        addresses[t] = sn_module_add_pi(module, addr_widths[t], false, port);
    }
    sn_obj_id_t data = sn_module_add_pi(module, width, false, "data");
    // A registered tap absorbs its external output flop: the tap read is
    // synchronous with its own clock and enable, the SRL-plus-flop form
    // FPGA synthesis packs into one LUT site.
    sn_obj_id_t tap_clocks[8], tap_enables[8];
    for (uint32_t t = 0; t < tap_count; t++)
    {
        tap_clocks[t] = tap_enables[t] = SN_INVALID_ID;
        if (tap_registered && tap_registered[t])
        {
            char port[32];
            snprintf(port, sizeof(port), "tap_clock%u", t);
            tap_clocks[t] = sn_module_add_pi(module, 1, false, port);
            snprintf(port, sizeof(port), "tap_enable%u", t);
            tap_enables[t] = sn_module_add_pi(module, 1, false, port);
        }
    }
    sn_obj_pair_t pair = sn_module_add_mem_pair(module, width, false, depth, "shift_out", "shift_in");
    for (uint32_t k = depth; k-- > 0;)
    {
        uint32_t address_value = k;
        sn_obj_id_t write_address = sn_module_add_const(module, 32, false, &address_value, NULL);
        sn_obj_id_t write_data = data;
        if (k)
        {
            uint32_t source_value = k - 1;
            sn_obj_id_t read_address = sn_module_add_const(module, 32, false, &source_value, NULL);
            write_data = sn_module_add_mem_read(module, pair.out, SN_INVALID_ID, SN_INVALID_ID, read_address, NULL);
        }
        sn_module_add_mem_write(module, pair.in, clock, enable, write_data, write_address, NULL);
    }
    for (uint32_t t = 0; t < tap_count; t++)
    {
        char port[32];
        snprintf(port, sizeof(port), "tap%u", t);
        sn_obj_id_t tap =
            sn_module_add_mem_read(module, pair.out, tap_clocks[t], tap_enables[t], addresses[t], NULL);
        sn_module_add_po(module, width, false, port, tap);
    }
    sn_design_reorder_module_topo(design, id);
    return id;
}

// Creates a behavioral fixed shift-register chain primitive: depth registers
// on one clock and one optional shared enable, data entering the first and
// the last driving the output. FPGA synthesis maps the idiom onto SRL cells
// with an optional output flop.
static inline sn_module_id_t sn_map_srl_chain_primitive_module(sn_design_t* design, uint32_t width,
                                                               uint32_t depth, bool has_enable, bool negedge)
{
    assert(width && depth >= 2);
    char name[128];
    int length = snprintf(name, sizeof(name), "__sn_SRLC_%u_%u_e%u_n%u", width, depth, has_enable ? 1u : 0u,
                          negedge ? 1u : 0u);
    assert(length >= 0 && (size_t)length < sizeof(name));
    sn_module_id_t existing = sn_design_find_module(design, name);
    if (existing != SN_INVALID_ID)
        return existing;
    sn_module_id_t id = sn_design_add_module(design, name);
    sn_module_t* module = sn_design_get_module(design, id);
    sn_obj_id_t clock = sn_module_add_pi(module, 1, false, "clock");
    sn_obj_id_t enable = has_enable ? sn_module_add_pi(module, 1, false, "enable") : SN_INVALID_ID;
    sn_obj_id_t data = sn_module_add_pi(module, width, false, "data");
    sn_obj_id_t previous = data;
    for (uint32_t k = 0; k < depth; k++)
    {
        sn_obj_pair_t stage = sn_module_add_reg_pair(module, width, false, NULL, NULL, clock);
        if (negedge)
            sn_reg_set_flags(module, stage.out, SN_REG_CLOCK_NEGEDGE);
        if (enable != SN_INVALID_ID)
            sn_reg_set_fanin(module, stage.out, SN_REG_ENABLE, enable);
        sn_obj_connect(module, stage.in, 0, previous);
        previous = stage.out;
    }
    sn_module_add_po(module, width, false, "tail", previous);
    sn_design_reorder_module_topo(design, id);
    return id;
}

ABC_NAMESPACE_HEADER_END

#endif
