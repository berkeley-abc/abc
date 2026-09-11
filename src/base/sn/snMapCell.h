/**CFile****************************************************************

  FileName    [snMapCell.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [In-process natural-hierarchy standard-cell mapping.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapCell.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snMapCell_h
#define ABC__base__sn__snMapCell_h

#include "snNtk.h"
#include "snBlast.h"

ABC_NAMESPACE_HEADER_START

// The callback borrows the MiniAIG and returns an owned mapped ABC network.
// Its ports must retain sn_partition_{i,o}<index> names in their original
// order. This is a correspondence guard, not an equivalence proof.
typedef Abc_Ntk_t* (*sn_map_cell_partition_fn)(void*, sn_module_id_t, const char*, Mini_Aig_t*);

typedef struct sn_map_cell_stats_t
{
    uint32_t mapped_modules, primitive_modules, empty_modules;
    uint64_t input_ands, output_cells;
    sn_module_id_t failed_module;
} sn_map_cell_stats_t;

static inline void sn_map_cell_port_name(char* name, size_t size, bool output, size_t index)
{
    snprintf(name, size, "sn_partition_%c%zu", output ? 'o' : 'i', index);
}

// Like sn_design_map_lut_hierarchy, retains each shared module definition and
// treats child instances as cuts. Unlike the LUT harness, generic memories
// refuse instead of silently leaving an unmapped partition. The caller must
// supply a private design copy and install it only after this function succeeds.
// Mapping is deliberately serial/in-process; no BLIF or worker protocol here.
static inline bool sn_design_map_cell_hierarchy(sn_design_t* design, sn_module_id_t root,
    Mio_Library_t* mio, sn_map_cell_partition_fn map, void* context,
    sn_map_cell_stats_t* stats, const char** reason)
{
    size_t count = design->modules.size;
    uint8_t* reachable = (uint8_t*)calloc(count, 1);
    sn_vec_t pending;
    bool success = false;
    memset(stats, 0, sizeof(*stats));
    stats->failed_module = SN_INVALID_ID;
    *reason = "invalid library or allocation failure";
    sn_vec_init(&pending);
    if (!reachable || root >= count || !mio || !map || !design->library) goto cleanup;
    *sn_vec_push(sn_module_id_t, &pending) = root;
    while (pending.size)
    {
        sn_module_id_t id = sn_vec_at(sn_module_id_t, &pending, --pending.size);
        if (reachable[id]) continue;
        reachable[id] = 1;
        const sn_module_t* module = sn_design_get_module_const(design, id);
        for (size_t i = 0; i < module->type_objects[SN_INST].size; ++i)
            *sn_vec_push(sn_module_id_t, &pending) = sn_inst_module_id(module,
                sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i));
    }
    for (sn_module_id_t id = 0; id < count; ++id)
    {
        sn_module_t* module = sn_design_get_module(design, id);
        module->copy_ids.size = 0;
        module->copy_module = SN_INVALID_ID;
    }
    for (sn_module_id_t id = 0; id < count; ++id)
    {
        if (!reachable[id]) continue;
        const sn_module_t* module = sn_design_get_module_const(design, id);
        if (sn_module_is_technology_primitive(module)) { ++stats->primitive_modules; continue; }
        stats->failed_module = id;
        sn_name_id_t original_name = module->name;
        sn_blast_options_t options = sn_blast_default_options();
        options.mode = SN_BLAST_COMB;
        options.abstract_instances = true;
        options.opaque_sequential_gates = true;
        sn_blast_boundary_t boundary;
        sn_blast_boundary_init(&boundary);
        Mini_Aig_t* aig = sn_design_blast_hier_boundary_options(design, id, options, NULL, &boundary);
        bool memory = false;
        for (size_t i = 0; i < boundary.cis.size; ++i)
            memory |= sn_vec_at(sn_blast_boundary_bit_t, &boundary.cis, i).kind == SN_BLAST_BOUNDARY_MEMORY_OUTPUT;
        for (size_t i = 0; i < boundary.cos.size; ++i)
            memory |= sn_vec_at(sn_blast_boundary_bit_t, &boundary.cos, i).kind == SN_BLAST_BOUNDARY_MEMORY_INPUT;
        if (!aig || memory)
        {
            *reason = memory ? "generic memories must be mapped before hierarchical cell mapping" : "partition extraction failed";
            if (aig) Mini_AigStop(aig);
            sn_blast_boundary_destroy(&boundary);
            goto cleanup;
        }
        if (!boundary.cos.size)
        {
            ++stats->empty_modules;
            Mini_AigStop(aig);
            sn_blast_boundary_destroy(&boundary);
            continue;
        }
        stats->input_ands += (uint64_t)Mini_AigAndNum(aig);
        Abc_Ntk_t* network = map(context, id, sn_name_get(&design->names, original_name), aig);
        Mini_AigStop(aig);
        bool ports = network && (size_t)Abc_NtkCiNum(network) == boundary.cis.size &&
                     (size_t)Abc_NtkCoNum(network) == boundary.cos.size;
        if (ports)
        {
            Abc_Obj_t* port;
            int index;
            char name[64];
            Abc_NtkForEachCi(network, port, index)
            {
                sn_map_cell_port_name(name, sizeof(name), false, (size_t)index);
                ports &= strcmp(name, Abc_ObjName(port)) == 0;
            }
            Abc_NtkForEachCo(network, port, index)
            {
                sn_map_cell_port_name(name, sizeof(name), true, (size_t)index);
                ports &= strcmp(name, Abc_ObjName(port)) == 0;
            }
        }
        sn_module_id_t replacement = SN_INVALID_ID;
        if (ports)
        {
            char temporary_name[80];
            unsigned suffix = 0;
            do { snprintf(temporary_name, sizeof(temporary_name), "__sn_cell_partition_%u_%u", id, suffix++); }
            while (sn_design_find_module(design, temporary_name) != SN_INVALID_ID);
            replacement = sn_design_add_mapped_network(design, id, network, mio, &boundary, temporary_name, reason);
        }
        else *reason = "mapping failed or changed partition port correspondence";
        if (network) Abc_NtkDelete(network);
        sn_blast_boundary_destroy(&boundary);
        if (replacement == SN_INVALID_ID) goto cleanup;
        stats->output_cells += sn_design_get_module_const(design, replacement)->type_objects[SN_GATE].size;
        sn_design_replace_appended_module(design, id, original_name, replacement);
        ++stats->mapped_modules;
    }
    stats->failed_module = SN_INVALID_ID;
    *reason = NULL;
    success = true;
cleanup:
    sn_vec_destroy(&pending);
    free(reachable);
    return success;
}

ABC_NAMESPACE_HEADER_END
#endif
