/**CFile****************************************************************

  FileName    [snRewrite.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Shared support for local word-level rewrites.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 8, 2026.]

  Revision    [$Id: snRewrite.h,v 1.00 2026/11/08 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef SN_REWRITE_H
#define SN_REWRITE_H
#include "snBoundary.h"
ABC_NAMESPACE_HEADER_START

/**Function*************************************************************

  Synopsis    [Removes dead combinational logic and restores module order.]

  Description [Preserves every port, state pair, instance, and library gate,
               including unused ones. Full-adder outputs stay with their owner.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void sn_rewrite_rebuild(sn_design_t* d, sn_module_id_t id)
{
    sn_module_t* m = sn_design_get_module(d, id);
    size_t n = m->obj_types.size;
    uint8_t* remove = (uint8_t*)malloc(n ? n : 1);
    sn_vec_t pending;
    sn_name_id_t name = m->name;
    char temporary[96];
    unsigned suffix = 0;
    assert(remove);
    memset(remove, 1, n);
    sn_vec_init(&pending);
    for (int t = 0; t < SN_OBJ_TYPE_COUNT; ++t) m->type_objects[t].size = 0;
    for (sn_obj_id_t o = 0; o < n; ++o) {
        sn_obj_type_t t = sn_obj_type(m, o);
        if (sn_obj_type_has_dense_index(t)) sn_vec_at(uint32_t, &m->obj_data, o) = (uint32_t)m->type_objects[t].size;
        *sn_vec_push(sn_obj_id_t, &m->type_objects[t]) = o;
        if (t == SN_FAN && sn_obj_type(m, sn_fan_owner(m, o)) == SN_FA) continue;
        if (t == SN_GATE || (!sn_obj_type_is_operator(t) &&
            t != SN_CONST0 && t != SN_CONST1 && t != SN_CONST))
            *sn_vec_push(sn_obj_id_t, &pending) = o;
    }
    while (pending.size) {
        sn_obj_id_t o = sn_vec_at(sn_obj_id_t, &pending, --pending.size);
        if (!remove[o]) continue;
        remove[o] = 0;
        if (sn_obj_type_has_outputs(sn_obj_type(m, o)))
            for (uint32_t k = 0; k < sn_owner_output_count(m, o); ++k)
                *sn_vec_push(sn_obj_id_t, &pending) = sn_owner_output(m, o, k);
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f != SN_INVALID_ID) *sn_vec_push(sn_obj_id_t, &pending) = f;
        }
    }
    do {
        int length = snprintf(temporary, sizeof(temporary), "__sn_rewrite_%u_%u", id, suffix++);
        (void)length;
        assert(length >= 0 && (size_t)length < sizeof(temporary) && suffix);
    } while (sn_name_find(&d->names, temporary) != SN_INVALID_ID);
    sn_module_id_t copy = sn_boundary_dup_filtered_topo(d, id, remove, temporary);
    sn_design_replace_appended_module(d, id, name, copy);
    sn_vec_destroy(&pending);
    free(remove);
}

/**Function*************************************************************

  Synopsis    [Estimates word-operator depth for local arrival ordering.]

  Description [Counts LUT-sized stages, not a technology timing guarantee.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned sn_rewrite_delay(const sn_module_t* m, sn_obj_id_t o)
{
    sn_obj_type_t t = sn_obj_type(m, o);
    uint32_t width = sn_obj_width(m, o);
    unsigned log = 0;
    if (t == SN_BUF || t == SN_POS || t == SN_CAST || t == SN_SLICE ||
        t == SN_CONCAT || t == SN_REPLICATE || t == SN_BIT_NOT || t == SN_FAN) return 0;
    if (t == SN_FA) return 2;
    if (sn_obj_fanin_count(m, o)) {
        uint32_t input_width = sn_obj_width(m, sn_obj_fanin(m, o, 0));
        if (input_width > width) width = input_width;
    }
    for (uint32_t bits = width > 0 ? width - 1 : 0; bits; bits >>= 1) ++log;
    if (t == SN_ADD || t == SN_SUB || t == SN_NEG || (t >= SN_EQ && t <= SN_GE)) return log + 1;
    if (t == SN_MUL) return 2 * log + 2;
    if (t >= SN_REDUCE_AND && t <= SN_REDUCE_XNOR) return (log + 1) / 2;
    if (t >= SN_SHL && t <= SN_ASHR) {
        sn_obj_type_t amount = sn_obj_type(m, sn_obj_fanin(m, o, 1));
        return amount == SN_CONST0 || amount == SN_CONST1 || amount == SN_CONST ? 0 : log;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes conservative word arrivals in topological order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned* sn_rewrite_arrivals(const sn_module_t* m)
{
    size_t n = m->obj_types.size;
    unsigned* arrival = (unsigned*)calloc(n ? n : 1, sizeof(unsigned));
    assert(arrival);
    for (sn_obj_id_t o = 0; o < n; ++o) {
        sn_obj_type_t t = sn_obj_type(m, o);
        if (!sn_obj_type_is_operator(t) && t != SN_FAN) continue;
        for (uint32_t k = 0; k < sn_obj_fanin_count(m, o); ++k) {
            sn_obj_id_t f = sn_obj_fanin(m, o, k);
            if (f < o && arrival[f] > arrival[o]) arrival[o] = arrival[f];
        }
        arrival[o] += sn_rewrite_delay(m, o);
    }
    return arrival;
}

ABC_NAMESPACE_HEADER_END
#endif
