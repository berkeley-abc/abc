/**CFile****************************************************************

  FileName    [snBoundary.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Reconstruction and reconnection of extracted combinational boundaries.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snBoundary.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snBoundary_h
#define ABC__base__sn__snBoundary_h

#include "snBlast.h"

ABC_NAMESPACE_HEADER_START

typedef struct sn_boundary_regs_t
{
    sn_design_t* design;
    const sn_blast_boundary_t* boundary;
    sn_module_t* result;
    sn_obj_id_t* top_inputs;
    sn_obj_pair_t* pairs;
    sn_obj_pair_t* loops;
    sn_obj_pair_t* primitive_pairs;
    uint32_t* primitive_offsets;
    sn_obj_id_t** external_copies;
    struct sn_boundary_link_t* links;
    size_t link_cap;
} sn_boundary_regs_t;

typedef struct sn_boundary_link_t
{
    uint64_t key;
    uint32_t primitive;
    uint32_t child;
    uint32_t reg;
    uint32_t loop;
} sn_boundary_link_t;

typedef struct sn_boundary_external_frame_t
{
    sn_blast_hier_ref_t ref;
    sn_blast_hier_ref_t dependency;
    sn_obj_id_t result;
    uint32_t next_fanin;
    uint8_t phase;
} sn_boundary_external_frame_t;

enum
{
    SN_BOUNDARY_EXTERNAL_START,
    SN_BOUNDARY_EXTERNAL_ALIAS,
    SN_BOUNDARY_EXTERNAL_OPERATOR
};

static inline uint64_t sn_boundary_link_key(uint32_t occurrence, sn_obj_id_t object)
{
    return ((uint64_t)occurrence << 32) | object;
}

static inline size_t sn_boundary_link_hash(uint64_t key, size_t mask)
{
    key ^= key >> 33;
    key *= UINT64_C(0xff51afd7ed558ccd);
    key ^= key >> 33;
    return (size_t)key & mask;
}

static inline sn_boundary_link_t* sn_boundary_link_find(sn_boundary_regs_t* regs, uint32_t occurrence,
                                                         sn_obj_id_t object, bool create)
{
    if (!regs->link_cap)
        return NULL;
    uint64_t key = sn_boundary_link_key(occurrence, object);
    size_t slot = sn_boundary_link_hash(key, regs->link_cap - 1);
    while (regs->links[slot].key != UINT64_MAX && regs->links[slot].key != key)
        slot = (slot + 1) & (regs->link_cap - 1);
    if (regs->links[slot].key == UINT64_MAX)
    {
        if (!create)
            return NULL;
        regs->links[slot].key = key;
    }
    return &regs->links[slot];
}

static inline sn_obj_id_t* sn_boundary_external_copies(sn_boundary_regs_t* regs, sn_blast_hier_ref_t ref,
                                                        const sn_module_t** returned_module)
{
    const sn_blast_occurrence_t* occurrence =
        &sn_vec_at(sn_blast_occurrence_t, &regs->boundary->occurrences, ref.occurrence);
    const sn_module_t* module = sn_design_get_module_const(regs->design, occurrence->module);
    sn_obj_id_t* copies = regs->external_copies[ref.occurrence];
    assert(ref.object < module->obj_types.size);
    if (!copies)
    {
        copies = (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * module->obj_types.size);
        assert(copies);
        for (size_t i = 0; i < module->obj_types.size; i++)
            copies[i] = SN_INVALID_ID;
        regs->external_copies[ref.occurrence] = copies;
    }
    if (returned_module)
        *returned_module = module;
    return copies;
}

static inline sn_obj_id_t sn_boundary_pack_bits(sn_module_t* module, const sn_obj_id_t* bits, uint32_t width,
                                                 const char* name)
{
    assert(module && bits && width);
    return width == 1 ? bits[0] : sn_module_add_operator(module, SN_CONCAT, width, false, width, bits, name);
}

static inline sn_blast_hier_ref_t sn_boundary_parent_ref(const sn_design_t* design,
                                                          const sn_blast_boundary_t* boundary,
                                                          sn_blast_hier_ref_t ref)
{
    const sn_blast_occurrence_t* occurrence;
    const sn_module_t* module;
    const sn_module_t* parent;
    sn_obj_id_t parent_fanin;
    assert(ref.occurrence < boundary->occurrences.size);
    occurrence = &sn_vec_at(sn_blast_occurrence_t, &boundary->occurrences, ref.occurrence);
    module = sn_design_get_module_const(design, occurrence->module);
    assert(sn_obj_type(module, ref.object) == SN_PI && occurrence->parent_occurrence != SN_INVALID_ID);
    parent = sn_design_get_module_const(
        design, sn_vec_at(sn_blast_occurrence_t, &boundary->occurrences, occurrence->parent_occurrence).module);
    parent_fanin = sn_obj_fanin(parent, occurrence->parent_inst, sn_obj_type_id(module, ref.object));
    ref.occurrence = occurrence->parent_occurrence;
    ref.object = parent_fanin;
    return ref;
}

// Resolves clocks, asynchronous controls, and initialization constants that @blast intentionally leaves outside the
// combinational cloud. Hierarchical PI bindings are followed to the root. Generated combinational control cones are
// copied and memoized per hierarchy occurrence; an explicit DFS stack avoids overflowing the C stack on deep control
// cones. The link table resolves inst, primitive, register, and loop endpoints in expected constant time.
static inline sn_obj_id_t sn_boundary_resolve_external(sn_boundary_regs_t* regs, sn_blast_hier_ref_t ref)
{
    sn_blast_hier_ref_t root = ref;
    sn_vec_t stack;
    sn_vec_init(&stack);
    sn_boundary_external_frame_t* initial = sn_vec_push(sn_boundary_external_frame_t, &stack);
    memset(initial, 0, sizeof(*initial));
    initial->ref = ref;
    while (stack.size)
    {
        sn_boundary_external_frame_t* frame =
            &sn_vec_at(sn_boundary_external_frame_t, &stack, stack.size - 1);
        ref = frame->ref;
        const sn_blast_occurrence_t* occurrence =
            &sn_vec_at(sn_blast_occurrence_t, &regs->boundary->occurrences, ref.occurrence);
        const sn_module_t* module;
        sn_obj_id_t* copies = sn_boundary_external_copies(regs, ref, &module);
        if (frame->phase == SN_BOUNDARY_EXTERNAL_ALIAS)
        {
            const sn_module_t* dependency_module;
            sn_obj_id_t* dependency_copies =
                sn_boundary_external_copies(regs, frame->dependency, &dependency_module);
            (void)dependency_module;
            assert(dependency_copies[frame->dependency.object] != SN_INVALID_ID);
            copies[ref.object] = dependency_copies[frame->dependency.object];
            stack.size--;
            continue;
        }
        if (frame->phase == SN_BOUNDARY_EXTERNAL_OPERATOR)
        {
            uint32_t count = sn_obj_fanin_count(module, ref.object);
            if (frame->next_fanin == count)
            {
                stack.size--;
                continue;
            }
            uint32_t index = frame->next_fanin;
            sn_obj_id_t old_fanin = sn_obj_fanin(module, ref.object, index);
            if (old_fanin == SN_INVALID_ID)
            {
                sn_obj_connect(regs->result, frame->result, index, SN_INVALID_ID);
                frame->next_fanin++;
                continue;
            }
            sn_blast_hier_ref_t dependency = {ref.occurrence, old_fanin, 0};
            sn_obj_id_t* dependency_copies = sn_boundary_external_copies(regs, dependency, NULL);
            if (dependency_copies[old_fanin] != SN_INVALID_ID)
            {
                sn_obj_connect(regs->result, frame->result, index, dependency_copies[old_fanin]);
                frame->next_fanin++;
                continue;
            }
            sn_boundary_external_frame_t* child = sn_vec_push(sn_boundary_external_frame_t, &stack);
            memset(child, 0, sizeof(*child));
            child->ref = dependency;
            continue;
        }
        if (copies[ref.object] != SN_INVALID_ID)
        {
            stack.size--;
            continue;
        }
        sn_obj_type_t type = sn_obj_type(module, ref.object);
        if (type == SN_PI && occurrence->parent_occurrence != SN_INVALID_ID)
        {
            frame->phase = SN_BOUNDARY_EXTERNAL_ALIAS;
            frame->dependency = sn_boundary_parent_ref(regs->design, regs->boundary, ref);
            sn_obj_id_t* dependency_copies = sn_boundary_external_copies(regs, frame->dependency, NULL);
            if (dependency_copies[frame->dependency.object] == SN_INVALID_ID)
            {
                sn_boundary_external_frame_t* child = sn_vec_push(sn_boundary_external_frame_t, &stack);
                memset(child, 0, sizeof(*child));
                child->ref = frame->dependency;
            }
            continue;
        }
        if (type == SN_PI)
        {
            assert(ref.occurrence == 0 && regs->top_inputs[ref.object] != SN_INVALID_ID);
            copies[ref.object] = regs->top_inputs[ref.object];
            stack.size--;
            continue;
        }
        if (type == SN_INST || type == SN_FAN)
        {
            sn_obj_id_t inst = type == SN_INST ? ref.object : sn_fan_inst_id(module, ref.object);
            uint32_t output = type == SN_INST ? 0 : sn_fan_output_index(module, ref.object);
            sn_boundary_link_t* link = sn_boundary_link_find(regs, ref.occurrence, inst, false);
            assert(link);
            if (link->primitive != SN_INVALID_ID)
            {
                const sn_blast_primitive_t* primitive =
                    &sn_vec_at(sn_blast_primitive_t, &regs->boundary->primitives, link->primitive);
                assert(output < sn_design_module_output_count(regs->design, primitive->module));
                (void)primitive;
                copies[ref.object] = regs->primitive_pairs[regs->primitive_offsets[link->primitive] + output].out;
                stack.size--;
                continue;
            }
            if (link->child != SN_INVALID_ID)
            {
                const sn_blast_occurrence_t* child_occurrence =
                    &sn_vec_at(sn_blast_occurrence_t, &regs->boundary->occurrences, link->child);
                const sn_module_t* child = sn_design_get_module_const(regs->design, child_occurrence->module);
                assert(output < child->type_objects[SN_PO].size);
                sn_obj_id_t child_po = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], output);
                sn_obj_id_t child_fanin = sn_obj_fanin(child, child_po, 0);
                assert(child_fanin != SN_INVALID_ID);
                frame->phase = SN_BOUNDARY_EXTERNAL_ALIAS;
                frame->dependency.occurrence = link->child;
                frame->dependency.object = child_fanin;
                frame->dependency.bit = 0;
                sn_obj_id_t* dependency_copies = sn_boundary_external_copies(regs, frame->dependency, NULL);
                if (dependency_copies[child_fanin] == SN_INVALID_ID)
                {
                    sn_boundary_external_frame_t* child_frame =
                        sn_vec_push(sn_boundary_external_frame_t, &stack);
                    memset(child_frame, 0, sizeof(*child_frame));
                    child_frame->ref = frame->dependency;
                }
                continue;
            }
            assert(false);
        }
        if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
        {
            uint32_t width = sn_obj_width(module, ref.object);
            uint32_t* words = (uint32_t*)calloc(sn_const_word_count(width), sizeof(uint32_t));
            assert(words);
            for (uint32_t bit = 0; bit < width; bit++)
                words[bit >> 5] |= (uint32_t)sn_const_bit(module, ref.object, bit) << (bit & 31);
            const char* name = sn_obj_name_id(module, ref.object) == SN_INVALID_ID
                                   ? NULL
                                   : sn_obj_name(module, ref.object);
            sn_obj_id_t result = sn_module_add_const(regs->result, width, sn_obj_is_signed(module, ref.object), words,
                                                      name);
            free(words);
            copies[ref.object] = result;
            stack.size--;
            continue;
        }
        if (type == SN_REG_OUT)
        {
            sn_boundary_link_t* link = sn_boundary_link_find(regs, ref.occurrence, ref.object, false);
            assert(link && link->reg != SN_INVALID_ID);
            copies[ref.object] = regs->pairs[link->reg].out;
            stack.size--;
            continue;
        }
        if (type == SN_LOOP_OUT)
        {
            sn_boundary_link_t* link = sn_boundary_link_find(regs, ref.occurrence, ref.object, false);
            assert(link && link->loop != SN_INVALID_ID);
            copies[ref.object] = regs->loops[link->loop].out;
            stack.size--;
            continue;
        }
        assert(type == SN_BUF || (type >= SN_POS && type <= SN_GATE));
        frame->result = sn_module_dup_obj_skeleton(regs->result, module, ref.object);
        copies[ref.object] = frame->result;
        sn_module_dup_obj_metadata(regs->result, sn_obj_type_id(regs->result, frame->result), module, ref.object);
        frame->phase = SN_BOUNDARY_EXTERNAL_OPERATOR;
        frame->next_fanin = 0;
    }
    sn_obj_id_t* root_copies = sn_boundary_external_copies(regs, root, NULL);
    assert(root_copies[root.object] != SN_INVALID_ID);
    sn_obj_id_t result = root_copies[root.object];
    sn_vec_destroy(&stack);
    return result;
}

static inline void sn_boundary_regs_init(sn_boundary_regs_t* regs, sn_design_t* design,
                                         const sn_blast_boundary_t* boundary, sn_module_t* result,
                                         sn_obj_id_t* top_inputs)
{
    assert(regs && design && boundary && result && top_inputs);
    regs->design = design;
    regs->boundary = boundary;
    regs->result = result;
    regs->top_inputs = top_inputs;
    regs->external_copies = boundary->occurrences.size
                                ? (sn_obj_id_t**)calloc(boundary->occurrences.size, sizeof(sn_obj_id_t*))
                                : NULL;
    assert(regs->external_copies || boundary->occurrences.size == 0);
    regs->links = NULL;
    regs->link_cap = 0;
    regs->primitive_offsets = boundary->primitives.size
                                  ? (uint32_t*)malloc(sizeof(uint32_t) * (boundary->primitives.size + 1))
                                  : NULL;
    assert(regs->primitive_offsets || boundary->primitives.size == 0);
    uint32_t primitive_output_count = 0;
    for (size_t i = 0; i < boundary->primitives.size; i++)
    {
        const sn_blast_primitive_t* entry = &sn_vec_at(sn_blast_primitive_t, &boundary->primitives, i);
        regs->primitive_offsets[i] = primitive_output_count;
        primitive_output_count += sn_design_module_output_count(design, entry->module);
    }
    if (boundary->primitives.size)
        regs->primitive_offsets[boundary->primitives.size] = primitive_output_count;
    regs->primitive_pairs = primitive_output_count
                                ? (sn_obj_pair_t*)malloc(sizeof(sn_obj_pair_t) * primitive_output_count)
                                : NULL;
    assert(regs->primitive_pairs || primitive_output_count == 0);
    for (size_t i = 0; i < boundary->primitives.size; i++)
    {
        const sn_blast_primitive_t* entry = &sn_vec_at(sn_blast_primitive_t, &boundary->primitives, i);
        const sn_blast_occurrence_t* occurrence =
            &sn_vec_at(sn_blast_occurrence_t, &boundary->occurrences, entry->occurrence);
        const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
        const sn_module_t* child = sn_design_get_module_const(design, entry->module);
        for (size_t output = 0; output < child->type_objects[SN_PO].size; output++)
        {
            sn_obj_id_t old_output = child->type_objects[SN_PO].size == 1
                                         ? entry->inst
                                         : sn_inst_output(module, entry->inst, (uint32_t)output);
            const char* output_name = sn_obj_name_id(module, old_output) == SN_INVALID_ID
                                          ? NULL
                                          : sn_obj_name(module, old_output);
            regs->primitive_pairs[regs->primitive_offsets[i] + output] =
                sn_module_add_loop_pair(result, sn_obj_width(module, old_output),
                                        sn_obj_is_signed(module, old_output), output_name, "primitive_boundary_input");
        }
    }
    regs->pairs = boundary->registers.size
                      ? (sn_obj_pair_t*)malloc(sizeof(sn_obj_pair_t) * boundary->registers.size)
                      : NULL;
    assert(regs->pairs || boundary->registers.size == 0);
    for (size_t i = 0; i < boundary->registers.size; i++)
    {
        const sn_blast_register_t* entry = &sn_vec_at(sn_blast_register_t, &boundary->registers, i);
        const sn_blast_occurrence_t* occurrence =
            &sn_vec_at(sn_blast_occurrence_t, &boundary->occurrences, entry->occurrence);
        const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
        sn_obj_id_t old_out = entry->reg_out;
        sn_obj_id_t old_in = sn_obj_pair_in(module, old_out);
        const char* out_name = sn_obj_name_id(module, old_out) == SN_INVALID_ID ? NULL : sn_obj_name(module, old_out);
        const char* in_name = sn_obj_name_id(module, old_in) == SN_INVALID_ID ? NULL : sn_obj_name(module, old_in);
        regs->pairs[i] = sn_module_add_reg_pair(result, entry->width, sn_obj_is_signed(module, old_out),
                                                 out_name, in_name, SN_INVALID_ID);
        sn_reg_set_flags(result, regs->pairs[i].out, sn_obj_reg_flags(module, old_out));
    }
    regs->loops = boundary->loops.size ? (sn_obj_pair_t*)malloc(sizeof(sn_obj_pair_t) * boundary->loops.size) : NULL;
    assert(regs->loops || boundary->loops.size == 0);
    for (size_t i = 0; i < boundary->loops.size; i++)
    {
        const sn_blast_loop_t* entry = &sn_vec_at(sn_blast_loop_t, &boundary->loops, i);
        const sn_blast_occurrence_t* occurrence =
            &sn_vec_at(sn_blast_occurrence_t, &boundary->occurrences, entry->occurrence);
        const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
        sn_obj_id_t old_in = sn_obj_pair_in(module, entry->loop_out);
        const char* out_name = sn_obj_name_id(module, entry->loop_out) == SN_INVALID_ID
                                   ? NULL
                                   : sn_obj_name(module, entry->loop_out);
        const char* in_name = sn_obj_name_id(module, old_in) == SN_INVALID_ID ? NULL : sn_obj_name(module, old_in);
        regs->loops[i] = sn_module_add_loop_pair(result, entry->width,
                                                  sn_obj_is_signed(module, entry->loop_out), out_name, in_name);
    }

    size_t link_count = boundary->primitives.size + boundary->registers.size + boundary->loops.size;
    if (boundary->occurrences.size)
        link_count += boundary->occurrences.size - 1;
    if (link_count)
    {
        regs->link_cap = 2;
        while (regs->link_cap < 2 * link_count)
            regs->link_cap <<= 1;
        regs->links = (sn_boundary_link_t*)malloc(regs->link_cap * sizeof(sn_boundary_link_t));
        assert(regs->links);
        for (size_t i = 0; i < regs->link_cap; i++)
        {
            regs->links[i].key = UINT64_MAX;
            regs->links[i].primitive = SN_INVALID_ID;
            regs->links[i].child = SN_INVALID_ID;
            regs->links[i].reg = SN_INVALID_ID;
            regs->links[i].loop = SN_INVALID_ID;
        }
        for (size_t i = 0; i < boundary->primitives.size; i++)
        {
            const sn_blast_primitive_t* entry = &sn_vec_at(sn_blast_primitive_t, &boundary->primitives, i);
            sn_boundary_link_find(regs, entry->occurrence, entry->inst, true)->primitive = (uint32_t)i;
        }
        for (size_t i = 1; i < boundary->occurrences.size; i++)
        {
            const sn_blast_occurrence_t* entry = &sn_vec_at(sn_blast_occurrence_t, &boundary->occurrences, i);
            sn_boundary_link_find(regs, entry->parent_occurrence, entry->parent_inst, true)->child = (uint32_t)i;
        }
        for (size_t i = 0; i < boundary->registers.size; i++)
        {
            const sn_blast_register_t* entry = &sn_vec_at(sn_blast_register_t, &boundary->registers, i);
            sn_boundary_link_find(regs, entry->occurrence, entry->reg_out, true)->reg = (uint32_t)i;
        }
        for (size_t i = 0; i < boundary->loops.size; i++)
        {
            const sn_blast_loop_t* entry = &sn_vec_at(sn_blast_loop_t, &boundary->loops, i);
            sn_boundary_link_find(regs, entry->occurrence, entry->loop_out, true)->loop = (uint32_t)i;
        }
    }
}

static inline sn_obj_id_t sn_boundary_primitive_output_bit(sn_boundary_regs_t* regs, uint32_t owner,
                                                            uint32_t port, uint32_t bit)
{
    assert(owner < regs->boundary->primitives.size);
    const sn_blast_primitive_t* entry = &sn_vec_at(sn_blast_primitive_t, &regs->boundary->primitives, owner);
    assert(port < sn_design_module_output_count(regs->design, entry->module));
    (void)entry;
    sn_obj_id_t output = regs->primitive_pairs[regs->primitive_offsets[owner] + port].out;
    assert(bit < sn_obj_width(regs->result, output));
    return sn_module_add_slice(regs->result, output, (int32_t)bit, (int32_t)bit, "primitive_output_bit");
}

static inline sn_obj_id_t sn_boundary_reg_output_bit(sn_boundary_regs_t* regs, uint32_t owner, uint32_t bit)
{
    assert(owner < regs->boundary->registers.size);
    assert(bit < sn_obj_width(regs->result, regs->pairs[owner].out));
    return sn_module_add_slice(regs->result, regs->pairs[owner].out, (int32_t)bit, (int32_t)bit, "reg_q_bit");
}

static inline sn_obj_id_t sn_boundary_loop_output_bit(sn_boundary_regs_t* regs, uint32_t owner, uint32_t bit)
{
    assert(owner < regs->boundary->loops.size);
    assert(bit < sn_obj_width(regs->result, regs->loops[owner].out));
    return sn_module_add_slice(regs->result, regs->loops[owner].out, (int32_t)bit, (int32_t)bit, "loop_q_bit");
}

static inline sn_obj_id_t sn_boundary_co_word(sn_boundary_regs_t* regs, const sn_obj_id_t* co_drivers,
                                              uint32_t begin, sn_blast_boundary_kind_t kind, uint32_t owner,
                                              uint32_t port, uint32_t width)
{
    assert(begin <= regs->boundary->cos.size && width <= regs->boundary->cos.size - begin);
    for (uint32_t bit = 0; bit < width; bit++)
    {
        sn_blast_boundary_bit_t endpoint =
            sn_vec_at(sn_blast_boundary_bit_t, &regs->boundary->cos, begin + bit);
        assert(endpoint.kind == kind && endpoint.owner == owner &&
               (port == SN_INVALID_ID || endpoint.port == port) && endpoint.signal.bit == bit);
    }
    return sn_boundary_pack_bits(regs->result, co_drivers + begin, width, "boundary_word");
}

typedef struct sn_boundary_dfs_frame_t
{
    sn_obj_id_t object;
    uint32_t next_fanout;
} sn_boundary_dfs_frame_t;

// Marks tentative primitive-output substitutions that create combinational feedback. All temporary pair outputs
// have already been replaced by the corresponding primitive outputs. One iterative Kosaraju traversal identifies
// the resulting strongly connected components; a substituted edge whose endpoints share a component must retain
// its loop pair. This replaces one complete cone walk per primitive output by linear whole-module graph work.
static inline void sn_boundary_mark_feedback_pairs(sn_module_t* module, const sn_obj_id_t* actual_to_pair,
                                                   uint8_t* keep)
{
    size_t object_count = module->obj_types.size;
    uint8_t* visited = (uint8_t*)calloc(object_count, sizeof(uint8_t));
    uint32_t* components = object_count ? (uint32_t*)malloc(object_count * sizeof(uint32_t)) : NULL;
    sn_vec_t order, stack;
    assert(visited && (components || object_count == 0));
    sn_vec_init(&order);
    sn_vec_init(&stack);
    sn_vec_reserve(sn_obj_id_t, &order, object_count);
    sn_module_build_fanouts(module);

    for (sn_obj_id_t start = 0; start < object_count; start++)
    {
        if (visited[start])
            continue;
        visited[start] = 1;
        sn_boundary_dfs_frame_t* first = sn_vec_push(sn_boundary_dfs_frame_t, &stack);
        first->object = start;
        first->next_fanout = 0;
        while (stack.size)
        {
            sn_boundary_dfs_frame_t* frame =
                &sn_vec_at(sn_boundary_dfs_frame_t, &stack, stack.size - 1);
            uint32_t count = sn_obj_fanout_count(module, frame->object);
            if (frame->next_fanout < count)
            {
                sn_obj_id_t fanout = sn_obj_fanout(module, frame->object, frame->next_fanout++);
                if (!visited[fanout])
                {
                    visited[fanout] = 1;
                    sn_boundary_dfs_frame_t* child = sn_vec_push(sn_boundary_dfs_frame_t, &stack);
                    child->object = fanout;
                    child->next_fanout = 0;
                }
                continue;
            }
            *sn_vec_push(sn_obj_id_t, &order) = frame->object;
            stack.size--;
        }
    }

    for (sn_obj_id_t object = 0; object < object_count; object++)
        components[object] = UINT32_MAX;
    uint32_t component_count = 0;
    for (size_t i = order.size; i-- > 0;)
    {
        sn_obj_id_t start = sn_vec_at(sn_obj_id_t, &order, i);
        if (components[start] != UINT32_MAX)
            continue;
        components[start] = component_count;
        *sn_vec_push(sn_obj_id_t, &stack) = start;
        while (stack.size)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &stack, --stack.size);
            for (uint32_t k = 0; k < sn_obj_fanin_count(module, object); k++)
            {
                sn_obj_id_t fanin = sn_obj_fanin(module, object, k);
                if (fanin != SN_INVALID_ID && components[fanin] == UINT32_MAX)
                {
                    components[fanin] = component_count;
                    *sn_vec_push(sn_obj_id_t, &stack) = fanin;
                }
            }
        }
        component_count++;
    }

    for (sn_obj_id_t object = 0; object < object_count; object++)
        for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
        {
            sn_obj_id_t actual = sn_obj_fanin(module, object, i);
            sn_obj_id_t pair_out = actual == SN_INVALID_ID ? SN_INVALID_ID : actual_to_pair[actual];
            if (pair_out != SN_INVALID_ID && components[actual] == components[object])
                keep[pair_out] = 1;
        }

    sn_module_invalidate_fanouts(module);
    sn_vec_destroy(&order);
    sn_vec_destroy(&stack);
    free(components);
    free(visited);
}

// Duplicates a module in topological order while omitting an explicitly unreferenced set of objects. This is used
// to remove temporary primitive-output loop pairs after their consumers have been redirected to the real outputs.
static inline sn_module_id_t sn_boundary_dup_filtered_topo(sn_design_t* design, sn_module_id_t source_id,
                                                            const uint8_t* remove, const char* name)
{
    sn_module_t* source = sn_design_get_module(design, source_id);
    size_t object_count = source->obj_types.size;
    uint8_t* marks = (uint8_t*)calloc(object_count, sizeof(uint8_t));
    sn_vec_t order;
    assert(marks);
    sn_vec_init(&order);
    sn_vec_reserve(sn_obj_id_t, &order, object_count);
    for (sn_obj_id_t object = 0; object < object_count; object++)
        if (remove[object])
            marks[object] = SN_TOPO_DONE;
    for (size_t i = 0; i < source->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PI], i);
        assert(!remove[object]);
        marks[object] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = object;
    }
    for (sn_obj_id_t object = 0; object < object_count; object++)
        if (!remove[object] && sn_obj_type_is_pair_out(sn_obj_type(source, object)))
        {
            marks[object] = SN_TOPO_DONE;
            *sn_vec_push(sn_obj_id_t, &order) = object;
        }
    sn_topo_context_t context = {source, &order, marks};
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        for (uint32_t j = 0; j < sn_obj_fanin_count(source, output); j++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(source, output, j);
            if (fanin != SN_INVALID_ID)
                sn_module_topo_visit(&context, fanin);
        }
    }
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_obj_type(source, object);
        if (type != SN_PI && type != SN_PO && marks[object] == SN_TOPO_UNSEEN)
            sn_module_topo_visit(&context, object);
    }
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        marks[output] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = output;
    }

    sn_module_id_t target_id = sn_design_add_module(design, name);
    sn_module_t* target = sn_design_get_module(design, target_id);
    sn_vec_resize(sn_obj_id_t, &source->copy_ids, object_count);
    for (sn_obj_id_t object = 0; object < object_count; object++)
        sn_vec_at(sn_obj_id_t, &source->copy_ids, object) = SN_INVALID_ID;
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) =
            sn_module_dup_obj_skeleton(target, source, old_object);
    }
    sn_module_clean_rebuild_pair_ids(target, source, SN_REG_OUT, SN_REG_IN);
    sn_module_clean_rebuild_pair_ids(target, source, SN_MEM_OUT, SN_MEM_IN);
    sn_module_clean_rebuild_pair_ids(target, source, SN_LOOP_OUT, SN_LOOP_IN);
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        sn_obj_type_t type = sn_obj_type(source, old_object);
        sn_module_dup_obj_metadata(target, sn_obj_type_id(target, new_object), source, old_object);
        if (type == SN_FAN)
            sn_vec_at(sn_obj_id_t, &target->fan_insts, sn_obj_type_id(target, new_object)) =
                sn_vec_at(sn_obj_id_t, &source->copy_ids, sn_fan_inst_id(source, old_object));
        for (uint32_t j = 0; j < sn_obj_fanin_count(source, old_object); j++)
        {
            sn_obj_id_t old_fanin = sn_obj_fanin(source, old_object, j);
            sn_obj_id_t new_fanin = old_fanin == SN_INVALID_ID
                                        ? SN_INVALID_ID
                                        : sn_vec_at(sn_obj_id_t, &source->copy_ids, old_fanin);
            assert(new_fanin != SN_INVALID_ID || old_fanin == SN_INVALID_ID);
            sn_obj_connect(target, new_object, j, new_fanin);
        }
    }
    source->copy_module = target_id;
    sn_vec_destroy(&order);
    free(marks);
    assert(sn_module_is_topo(target));
    return target_id;
}

static inline void sn_boundary_prune_primitive_pairs(sn_boundary_regs_t* regs)
{
    sn_module_t* source = regs->result;
    size_t object_count = source->obj_types.size;
    uint8_t* remove = (uint8_t*)calloc(object_count, sizeof(uint8_t));
    uint8_t* keep = (uint8_t*)calloc(object_count, sizeof(uint8_t));
    sn_obj_id_t* replacement = object_count ? (sn_obj_id_t*)malloc(object_count * sizeof(sn_obj_id_t)) : NULL;
    sn_obj_id_t* actual_to_pair = object_count ? (sn_obj_id_t*)malloc(object_count * sizeof(sn_obj_id_t)) : NULL;
    size_t remove_count = 0;
    assert(remove && keep && (replacement || object_count == 0) && (actual_to_pair || object_count == 0));
    for (sn_obj_id_t object = 0; object < object_count; object++)
        replacement[object] = actual_to_pair[object] = SN_INVALID_ID;
    for (size_t i = 0; i < regs->boundary->primitives.size; i++)
    {
        const sn_blast_primitive_t* entry = &sn_vec_at(sn_blast_primitive_t, &regs->boundary->primitives, i);
        uint32_t output_count = sn_design_module_output_count(regs->design, entry->module);
        for (uint32_t output = 0; output < output_count; output++)
        {
            sn_obj_pair_t pair = regs->primitive_pairs[regs->primitive_offsets[i] + output];
            sn_obj_id_t actual = sn_obj_fanin(source, pair.in, 0);
            assert(replacement[pair.out] == SN_INVALID_ID && actual_to_pair[actual] == SN_INVALID_ID);
            replacement[pair.out] = actual;
            actual_to_pair[actual] = pair.out;
        }
    }
    for (size_t i = 0; i < source->fanins.size; i++)
    {
        sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &source->fanins, i);
        if (fanin != SN_INVALID_ID && replacement[fanin] != SN_INVALID_ID)
            sn_vec_at(sn_obj_id_t, &source->fanins, i) = replacement[fanin];
    }
    sn_module_invalidate_fanouts(source);
    sn_boundary_mark_feedback_pairs(source, actual_to_pair, keep);
    for (sn_obj_id_t object = 0; object < object_count; object++)
        for (uint32_t i = 0; i < sn_obj_fanin_count(source, object); i++)
        {
            sn_obj_id_t actual = sn_obj_fanin(source, object, i);
            sn_obj_id_t pair_out = actual == SN_INVALID_ID ? SN_INVALID_ID : actual_to_pair[actual];
            if (pair_out != SN_INVALID_ID && keep[pair_out] && object != sn_obj_pair_in(source, pair_out))
                sn_obj_connect(source, object, i, pair_out);
        }
    for (sn_obj_id_t pair_out = 0; pair_out < object_count; pair_out++)
        if (replacement[pair_out] != SN_INVALID_ID && !keep[pair_out])
        {
            sn_obj_id_t actual = replacement[pair_out];
            sn_obj_id_t pair_in = sn_obj_pair_in(source, pair_out);
            if (sn_obj_type(source, actual) == SN_FAN && sn_obj_name_id(source, actual) == SN_INVALID_ID &&
                sn_obj_name_id(source, pair_out) != SN_INVALID_ID)
                sn_vec_at(sn_name_id_t, &source->name_ids, actual) = sn_obj_name_id(source, pair_out);
            remove[pair_out] = remove[pair_in] = 1;
            remove_count += 2;
        }
    sn_module_invalidate_fanouts(source);
    if (remove_count)
    {
        char name[96];
        uint32_t suffix = 0;
        do
        {
            int length = snprintf(name, sizeof(name), "__sn_boundary_%u_%u", source->id, suffix++);
            assert(length >= 0 && (size_t)length < sizeof(name) && suffix != 0);
        } while (sn_name_find(&regs->design->names, name) != SN_INVALID_ID);
        sn_module_id_t source_id = source->id;
        sn_name_id_t source_name = source->name;
        bool interface_locked = source->interface_locked;
        sn_module_id_t filtered_id = sn_boundary_dup_filtered_topo(regs->design, source_id, remove, name);
        sn_module_t* filtered = sn_design_get_module(regs->design, filtered_id);
        sn_name_id_t temporary_name = filtered->name;
        sn_design_invalidate_copies_to_module(regs->design, source_id);
        sn_module_destroy(source);
        free(source);
        filtered->id = source_id;
        filtered->name = source_name;
        filtered->interface_locked = interface_locked;
        sn_vec_at(sn_module_t*, &regs->design->modules, source_id) = filtered;
        regs->design->modules.size--;
        sn_name_remove_last(&regs->design->names, temporary_name);
        regs->result = filtered;
    }
    free(actual_to_pair);
    free(replacement);
    free(keep);
    free(remove);
}

static inline void sn_boundary_regs_finish(sn_boundary_regs_t* regs, const sn_obj_id_t* co_drivers)
{
    for (size_t i = 0; i < regs->boundary->primitives.size; i++)
    {
        const sn_blast_primitive_t* entry = &sn_vec_at(sn_blast_primitive_t, &regs->boundary->primitives, i);
        const sn_blast_occurrence_t* occurrence =
            &sn_vec_at(sn_blast_occurrence_t, &regs->boundary->occurrences, entry->occurrence);
        const sn_module_t* module = sn_design_get_module_const(regs->design, occurrence->module);
        const sn_module_t* child = sn_design_get_module_const(regs->design, entry->module);
        uint32_t input_count = (uint32_t)child->type_objects[SN_PI].size;
        sn_obj_id_t* inputs = input_count ? (sn_obj_id_t*)malloc(sizeof(sn_obj_id_t) * input_count) : NULL;
        assert(inputs || input_count == 0);
        uint32_t co_begin = entry->co_begin;
        for (uint32_t input = 0; input < input_count; input++)
        {
            sn_obj_id_t port = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PI], input);
            uint32_t width = sn_obj_width(child, port);
            inputs[input] = sn_boundary_co_word(regs, co_drivers, co_begin, SN_BLAST_BOUNDARY_PRIMITIVE_INPUT,
                                                 (uint32_t)i, input, width);
            co_begin += width;
        }
        assert(co_begin == entry->co_begin + entry->co_count);
        const char* inst_name = sn_obj_name_id(module, entry->inst) == SN_INVALID_ID
                                    ? NULL
                                    : sn_obj_name(module, entry->inst);
        sn_obj_id_t inst = sn_module_add_inst(regs->result, entry->module, input_count, inputs, inst_name, NULL);
        free(inputs);
        for (uint32_t output = 0; output < child->type_objects[SN_PO].size; output++)
        {
            sn_obj_pair_t pair = regs->primitive_pairs[regs->primitive_offsets[i] + output];
            sn_obj_connect(regs->result, pair.in, 0, sn_inst_output(regs->result, inst, output));
        }
    }
    for (size_t i = 0; i < regs->boundary->loops.size; i++)
    {
        const sn_blast_loop_t* entry = &sn_vec_at(sn_blast_loop_t, &regs->boundary->loops, i);
        sn_obj_id_t data = sn_boundary_co_word(regs, co_drivers, entry->co_begin, SN_BLAST_BOUNDARY_LOOP_INPUT,
                                                (uint32_t)i, SN_INVALID_ID, entry->width);
        sn_obj_connect(regs->result, regs->loops[i].in, 0, data);
    }
    for (size_t i = 0; i < regs->boundary->registers.size; i++)
    {
        const sn_blast_register_t* entry = &sn_vec_at(sn_blast_register_t, &regs->boundary->registers, i);
        const sn_blast_occurrence_t* occurrence =
            &sn_vec_at(sn_blast_occurrence_t, &regs->boundary->occurrences, entry->occurrence);
        const sn_module_t* module = sn_design_get_module_const(regs->design, occurrence->module);
        sn_obj_id_t old_out = entry->reg_out;
        sn_obj_pair_t pair = regs->pairs[i];
        sn_obj_id_t old_clock = sn_obj_fanin(module, old_out, SN_REG_CLOCK);
        if (old_clock != SN_INVALID_ID)
        {
            sn_blast_hier_ref_t ref = {entry->occurrence, old_clock, 0};
            sn_reg_set_fanin(regs->result, pair.out, SN_REG_CLOCK, sn_boundary_resolve_external(regs, ref));
        }
        const uint32_t slots[] = {SN_REG_ENABLE, SN_REG_SET, SN_REG_RESET, SN_REG_RESET_VALUE};
        for (size_t k = 0; k < sizeof(slots) / sizeof(slots[0]); k++)
        {
            uint32_t slot = slots[k];
            sn_obj_id_t old_fanin = sn_obj_fanin(module, old_out, slot);
            if (old_fanin == SN_INVALID_ID)
                continue;
            bool in_cloud = sn_blast_reg_control_is_comb_output(module, old_out, slot);
            sn_obj_id_t fanin;
            if (in_cloud)
            {
                assert(entry->control_co_begin[slot] != SN_INVALID_ID);
                fanin = sn_boundary_co_word(regs, co_drivers, entry->control_co_begin[slot],
                                            SN_BLAST_BOUNDARY_REG_CONTROL, (uint32_t)i, slot,
                                            sn_obj_width(module, old_fanin));
            }
            else
            {
                sn_blast_hier_ref_t ref = {entry->occurrence, old_fanin, 0};
                fanin = sn_boundary_resolve_external(regs, ref);
            }
            sn_reg_set_fanin(regs->result, pair.out, (sn_reg_fanin_t)slot, fanin);
        }
        for (uint32_t slot = SN_REG_INIT_DATA; slot <= SN_REG_INIT_MASK; slot++)
        {
            sn_obj_id_t old_fanin = sn_obj_fanin(module, old_out, slot);
            if (old_fanin != SN_INVALID_ID)
            {
                sn_blast_hier_ref_t ref = {entry->occurrence, old_fanin, 0};
                sn_reg_set_fanin(regs->result, pair.out, (sn_reg_fanin_t)slot,
                                 sn_boundary_resolve_external(regs, ref));
            }
        }
        sn_obj_id_t data = sn_boundary_co_word(regs, co_drivers, entry->co_begin, SN_BLAST_BOUNDARY_REG_INPUT,
                                                (uint32_t)i, SN_INVALID_ID, entry->width);
        sn_obj_connect(regs->result, pair.in, 0, data);
    }
    sn_boundary_prune_primitive_pairs(regs);
    free(regs->pairs);
    free(regs->loops);
    free(regs->primitive_pairs);
    free(regs->primitive_offsets);
    free(regs->links);
    for (size_t i = 0; i < regs->boundary->occurrences.size; i++)
        free(regs->external_copies[i]);
    free(regs->external_copies);
    regs->pairs = NULL;
    regs->loops = NULL;
    regs->primitive_pairs = NULL;
    regs->primitive_offsets = NULL;
    regs->external_copies = NULL;
    regs->links = NULL;
    regs->link_cap = 0;
}

ABC_NAMESPACE_HEADER_END

#endif
