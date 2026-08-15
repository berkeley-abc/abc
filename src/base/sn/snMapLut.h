/**CFile****************************************************************

  FileName    [snMapLut.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Partitioned synthesis and LUT mapping of hierarchical SN designs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapLut.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_MAP_LUT_H
#define SN_MAP_LUT_H

// Natural-hierarchy LUT-mapping harness. Each reachable user module is extracted as one combinational MiniAIG while
// child instances, registers, and mapped hard blocks remain boundary terminals. A caller-supplied callback maps this
// partition and returns a MiniLUT. The harness reconstructs the module at its stable ID, preserving parent references.

#include "snBlast.h"
#include "snMiniLut.h"
#include "snPth.h"

ABC_NAMESPACE_HEADER_START

typedef Mini_Lut_t* (*sn_map_lut_partition_fn)(void* context, sn_module_id_t module, const char* name,
                                                Mini_Aig_t* aig, const sn_blast_boundary_t* boundary);

typedef struct sn_map_lut_stats_t
{
    uint32_t reachable_modules;
    uint32_t mapped_modules;
    uint32_t trivial_modules;
    uint32_t primitive_modules;
    uint32_t generic_memory_modules;
    uint64_t input_ands;
    uint64_t output_luts;
    sn_module_id_t failed_module;
} sn_map_lut_stats_t;

typedef struct sn_map_lut_job_t
{
    sn_module_id_t module;
    sn_name_id_t name;
    Mini_Aig_t* aig;
    Mini_Lut_t* lut;
    sn_blast_boundary_t boundary;
} sn_map_lut_job_t;

typedef struct sn_map_lut_runner_t
{
    sn_design_t* design;
    sn_map_lut_partition_fn function;
    void* context;
} sn_map_lut_runner_t;

static inline void sn_map_lut_run_job(void* argument, void* job_argument)
{
    sn_map_lut_runner_t* runner = (sn_map_lut_runner_t*)argument;
    sn_map_lut_job_t* job = (sn_map_lut_job_t*)job_argument;
    job->lut = runner->function(runner->context, job->module,
                                sn_name_get(&runner->design->names, job->name), job->aig, &job->boundary);
}

static inline bool sn_map_lut_boundary_has_generic_memories(const sn_blast_boundary_t* boundary)
{
    for (size_t i = 0; i < boundary->cis.size; i++)
        if (sn_vec_at(sn_blast_boundary_bit_t, &boundary->cis, i).kind == SN_BLAST_BOUNDARY_MEMORY_OUTPUT)
            return true;
    for (size_t i = 0; i < boundary->cos.size; i++)
        if (sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, i).kind == SN_BLAST_BOUNDARY_MEMORY_INPUT)
            return true;
    return false;
}

static inline void sn_design_replace_appended_module(sn_design_t* design, sn_module_id_t module,
                                                       sn_name_id_t name, sn_module_id_t temporary)
{
    sn_module_t* old_module;
    sn_module_t* new_module;
    bool interface_locked;
    assert(design && module < design->modules.size);
    old_module = sn_design_get_module(design, module);
    assert(old_module->name == name);
    assert(temporary + 1 == design->modules.size && temporary != module);
    new_module = sn_design_get_module(design, temporary);
    interface_locked = old_module->interface_locked;
    sn_module_destroy(old_module);
    free(old_module);
    new_module->id = module;
    new_module->name = name;
    new_module->interface_locked = interface_locked;
    sn_vec_at(sn_module_t*, &design->modules, module) = new_module;
    design->modules.size--;
}

// Maps all user modules reachable from root. The callback borrows aig and boundary for the duration of the call and
// returns a newly allocated MiniLUT owned by this harness. A NULL result aborts the pass. Modules containing generic
// memories are skipped; map their memories into primitive instances first if their surrounding logic should be mapped.
// The operation is in-place, so a transactional client should invoke it on a duplicate design and install that design
// only after this API succeeds.
static inline bool sn_design_map_lut_hierarchy(sn_design_t* design, sn_module_id_t root,
                                                sn_map_lut_partition_fn map_partition, void* context,
                                                unsigned processes, bool extract_only,
                                                sn_map_lut_stats_t* returned_stats)
{
    sn_map_lut_stats_t stats = {0};
    size_t module_count;
    bool* reachable;
    sn_vec_t pending;
    sn_vec_t jobs;
    stats.failed_module = SN_INVALID_ID;
    assert(design && root < design->modules.size && map_partition && processes >= 1);
    module_count = design->modules.size;
    // Module replacement invalidates optional duplication maps that may have been cached by earlier mapping passes.
    for (sn_module_id_t module_id = 0; module_id < module_count; module_id++)
    {
        sn_module_t* module = sn_design_get_module(design, module_id);
        sn_vec_destroy(&module->copy_ids);
        sn_vec_init(&module->copy_ids);
        module->copy_module = SN_INVALID_ID;
    }
    reachable = (bool*)calloc(module_count, sizeof(bool));
    assert(reachable);
    sn_vec_init(&pending);
    sn_vec_init(&jobs);
    *sn_vec_push(sn_module_id_t, &pending) = root;
    while (pending.size)
    {
        sn_module_id_t module_id = sn_vec_at(sn_module_id_t, &pending, --pending.size);
        const sn_module_t* module;
        if (reachable[module_id])
            continue;
        reachable[module_id] = true;
        stats.reachable_modules++;
        module = sn_design_get_module_const(design, module_id);
        for (size_t i = 0; i < module->inst_modules.size; i++)
            *sn_vec_push(sn_module_id_t, &pending) = sn_vec_at(sn_module_id_t, &module->inst_modules, i);
    }
    for (sn_module_id_t module_id = 0; module_id < module_count; module_id++)
    {
        const sn_module_t* module;
        sn_name_id_t name_id;
        sn_blast_options_t options;
        sn_blast_boundary_t boundary;
        Mini_Aig_t* aig;
        if (!reachable[module_id])
            continue;
        module = sn_design_get_module_const(design, module_id);
        if (sn_module_is_technology_primitive(module))
        {
            stats.primitive_modules++;
            continue;
        }
        name_id = module->name;
        options = sn_blast_default_options();
        options.mode = SN_BLAST_COMB;
        options.abstract_instances = true;
        sn_blast_boundary_init(&boundary);
        aig = sn_design_blast_hier_boundary_options(design, module_id, options, NULL, &boundary);
        if (sn_map_lut_boundary_has_generic_memories(&boundary))
        {
            stats.generic_memory_modules++;
            Mini_AigStop(aig);
            sn_blast_boundary_destroy(&boundary);
            continue;
        }
        if (Mini_AigAndNum(aig) == 0)
        {
            stats.trivial_modules++;
            Mini_AigStop(aig);
            sn_blast_boundary_destroy(&boundary);
            continue;
        }
        stats.input_ands += (uint64_t)Mini_AigAndNum(aig);
        if (processes == 1)
        {
            Mini_Lut_t* lut = map_partition(context, module_id, sn_name_get(&design->names, name_id), aig, &boundary);
            Mini_AigStop(aig);
            if (!lut)
            {
                stats.failed_module = module_id;
                sn_blast_boundary_destroy(&boundary);
                sn_vec_destroy(&pending);
                sn_vec_destroy(&jobs);
                free(reachable);
                if (returned_stats)
                    *returned_stats = stats;
                return false;
            }
            if (extract_only)
            {
                Mini_LutStop(lut);
                sn_blast_boundary_destroy(&boundary);
                stats.mapped_modules++;
                continue;
            }
            sn_lut_stats_t lut_stats = sn_lut_analyze(lut, &boundary);
            sn_module_id_t temporary = sn_design_add_lut_module(design, module_id, lut, &boundary,
                                                                 "__sn_lut_partition");
            Mini_LutStop(lut);
            sn_blast_boundary_destroy(&boundary);
            sn_design_replace_appended_module(design, module_id, name_id, temporary);
            stats.mapped_modules++;
            stats.output_luts += lut_stats.lut_count;
            continue;
        }
        sn_map_lut_job_t* job = sn_vec_push(sn_map_lut_job_t, &jobs);
        job->module = module_id;
        job->name = name_id;
        job->aig = aig;
        job->lut = NULL;
        job->boundary = boundary;
    }
    void** job_pointers = jobs.size ? (void**)malloc(sizeof(void*) * jobs.size) : NULL;
    assert(job_pointers || jobs.size == 0);
    for (size_t i = 0; i < jobs.size; i++)
        job_pointers[i] = &sn_vec_at(sn_map_lut_job_t, &jobs, i);
    sn_map_lut_runner_t runner = {design, map_partition, context};
    sn_pth_process(job_pointers, jobs.size, processes, sn_map_lut_run_job, &runner);
    free(job_pointers);
    bool success = true;
    for (size_t i = 0; i < jobs.size; i++)
        if (!sn_vec_at(sn_map_lut_job_t, &jobs, i).lut)
        {
            stats.failed_module = sn_vec_at(sn_map_lut_job_t, &jobs, i).module;
            success = false;
            break;
        }
    if (success && !extract_only)
        for (size_t i = 0; i < jobs.size; i++)
        {
            sn_map_lut_job_t* job = &sn_vec_at(sn_map_lut_job_t, &jobs, i);
            sn_lut_stats_t lut_stats = sn_lut_analyze(job->lut, &job->boundary);
            sn_module_id_t temporary = sn_design_add_lut_module(design, job->module, job->lut, &job->boundary,
                                                                 "__sn_lut_partition");
            sn_design_replace_appended_module(design, job->module, job->name, temporary);
            stats.mapped_modules++;
            stats.output_luts += lut_stats.lut_count;
        }
    else if (success)
        stats.mapped_modules += (uint32_t)jobs.size;
    for (size_t i = 0; i < jobs.size; i++)
    {
        sn_map_lut_job_t* job = &sn_vec_at(sn_map_lut_job_t, &jobs, i);
        Mini_AigStop(job->aig);
        if (job->lut)
            Mini_LutStop(job->lut);
        sn_blast_boundary_destroy(&job->boundary);
    }
    sn_vec_destroy(&pending);
    sn_vec_destroy(&jobs);
    free(reachable);
    assert(!success || sn_design_is_topo(design));
    if (returned_stats)
        *returned_stats = stats;
    return success;
}

ABC_NAMESPACE_HEADER_END

#endif
