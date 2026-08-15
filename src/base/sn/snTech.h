/**CFile****************************************************************

  FileName    [snTech.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Target-technology descriptions for SN mapping passes.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snTech.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_TECH_H
#define SN_TECH_H

// Technology-independent descriptions used by the SN memory and DSP mappers.
// These describe legal primitive configurations and mapping costs; they do not
// describe device placement or the total number of resources on a die.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_HEADER_START

typedef enum sn_mem_port_mode_t
{
    SN_MEM_PORT_SINGLE = 0,
    SN_MEM_PORT_SIMPLE_DUAL,
    SN_MEM_PORT_TRUE_DUAL
} sn_mem_port_mode_t;

typedef enum sn_mem_read_write_mode_t
{
    SN_MEM_READ_WRITE_NO_CHANGE = 0,
    SN_MEM_READ_WRITE_READ_FIRST,
    SN_MEM_READ_WRITE_WRITE_FIRST
} sn_mem_read_write_mode_t;

typedef struct sn_mem_tech_t
{
    const char* name;
    uint32_t cap_bits;
    uint32_t address_bits;
    const uint32_t* widths;
    size_t width_count;
    sn_mem_port_mode_t port_mode;
    uint32_t byte_width;
    bool synchronous_read;
    bool has_clock_enable;
    bool has_byte_enable;
    bool supports_init;
    bool supports_read_first;
    bool supports_write_first;
    bool supports_no_change;
    uint32_t mapping_cost;
    const uint32_t* simple_dual_widths;
    size_t simple_dual_width_count;
} sn_mem_tech_t;

typedef struct sn_dsp_tech_t
{
    const char* name;
    uint32_t a_width;
    uint32_t b_width;
    uint32_t p_width;
    uint32_t preadder_width;
    uint32_t min_a_width;
    uint32_t min_b_width;
    uint32_t min_p_width;
    bool signed_only;
    bool has_preadder;
    bool has_postadder;
    bool has_simd;
    bool has_cascade;
    uint32_t max_cascade_length;
    uint32_t latency;
    uint32_t mapping_cost;
} sn_dsp_tech_t;

typedef struct sn_carry_tech_t
{
    const char* name;
    uint32_t width;
    uint32_t min_op_width;
    uint32_t mapping_cost;
} sn_carry_tech_t;

typedef struct sn_tech_t
{
    const sn_mem_tech_t* memories;
    size_t memory_count;
    const sn_dsp_tech_t* dsps;
    size_t dsp_count;
    const sn_carry_tech_t* carries;
    size_t carry_count;
} sn_tech_t;

// AMD/Xilinx UltraScale+ primitives used by the initial mapper. Width lists
// follow the legal BRAM/URAM port widths in the Yosys Xilinx memory library.
static inline sn_tech_t sn_tech_xilinx_ultrascale(void)
{
    static const uint32_t bram18_widths[] = {1, 2, 4, 9, 18};
    static const uint32_t bram36_widths[] = {1, 2, 4, 9, 18, 36};
    static const uint32_t bram18_sdp_widths[] = {1, 2, 4, 9, 18, 36};
    static const uint32_t bram36_sdp_widths[] = {1, 2, 4, 9, 18, 36, 72};
    static const uint32_t uram_widths[] = {72, 144};
    static const sn_mem_tech_t memories[] = {
        {"RAMB18E2", 18u * 1024u, 14, bram18_widths, 5, SN_MEM_PORT_TRUE_DUAL, 9, true, true, true, true, true,
         true, true, 129, bram18_sdp_widths, 6},
        {"RAMB36E2", 36u * 1024u, 15, bram36_widths, 6, SN_MEM_PORT_TRUE_DUAL, 9, true, true, true, true, true,
         true, true, 257, bram36_sdp_widths, 7},
        {"URAM288", 288u * 1024u, 12, uram_widths, 2, SN_MEM_PORT_TRUE_DUAL, 9, true, true, true, true, false,
         true, true, 1024, NULL, 0},
    };
    static const sn_dsp_tech_t dsps[] = {
        {"DSP48E2", 27, 18, 48, 27, 2, 2, 9, true, true, true, true, true, 20, 0, 1},
    };
    static const sn_carry_tech_t carries[] = {{"CARRY4", 4, 3, 1}};
    sn_tech_t result = {memories, sizeof(memories) / sizeof(memories[0]), dsps, sizeof(dsps) / sizeof(dsps[0]),
                        carries, sizeof(carries) / sizeof(carries[0])};
    return result;
}

ABC_NAMESPACE_HEADER_END

#endif
