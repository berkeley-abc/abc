/**CFile****************************************************************

  FileName    [snCheck.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Structural and semantic consistency checking for SN designs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snCheck.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_CHECK_H
#define SN_CHECK_H

#include "sn.h"

#include <stdarg.h>

ABC_NAMESPACE_HEADER_START

typedef struct sn_check_ctx_t
{
    FILE* out;
    size_t errors;
    size_t modules;
    size_t objects;
    bool verbose;
} sn_check_ctx_t;

static inline const char* sn_check_module_name(const sn_module_t* module)
{
    if (!module || !module->design || module->name >= module->design->names.names.size)
        return "<invalid>";
    return sn_vec_at(char*, &module->design->names.names, module->name);
}

static inline void sn_check_error(sn_check_ctx_t* ctx, const sn_module_t* module, sn_obj_id_t object,
                                  const char* format, ...)
{
    va_list args;
    ctx->errors++;
    fprintf(ctx->out, "SN check failed");
    if (module)
        fprintf(ctx->out, " in module \"%s\"", sn_check_module_name(module));
    if (object != SN_INVALID_ID)
        fprintf(ctx->out, ", object %u", object);
    fputs(": ", ctx->out);
    va_start(args, format);
    vfprintf(ctx->out, format, args);
    va_end(args);
    fputc('\n', ctx->out);
}

#define SN_CHECK(ctx, module, object, condition, ...)                                                                  \
    do {                                                                                                               \
        if (!(condition))                                                                                              \
            sn_check_error((ctx), (module), (object), __VA_ARGS__);                                                    \
    } while (false)

static inline bool sn_check_vec(sn_check_ctx_t* ctx, const sn_module_t* module, const sn_vec_t* vec,
                                const char* name)
{
    bool valid = vec->size <= vec->cap && (vec->cap == 0 || vec->data != NULL);
    SN_CHECK(ctx, module, SN_INVALID_ID, valid, "vector %s has size %zu, capacity %zu, and data %p", name,
             vec->size, vec->cap, vec->data);
    return valid;
}

static inline bool sn_check_const_type(sn_obj_type_t type)
{
    return type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST;
}

static inline bool sn_check_name_is_emittable(const char* name)
{
    size_t i;
    if (!name || !name[0])
        return false;
    for (i = 0; name[i]; i++)
    {
        unsigned char c = (unsigned char)name[i];
        if (c <= 32 || c >= 127 || c == '\\')
            return false;
    }
    return true;
}

static inline int sn_check_fixed_fanin_count(sn_obj_type_t type)
{
    if (type == SN_PI || type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
        return 0;
    if (type == SN_PO || type == SN_BUF || type == SN_FAN || type == SN_REG_IN || type == SN_LOOP_OUT ||
        type == SN_LOOP_IN || (type >= SN_POS && type <= SN_REDUCE_XNOR) || type == SN_REPLICATE ||
        type == SN_SLICE || type == SN_CAST)
        return 1;
    if ((type >= SN_ADD && type <= SN_LOG_OR) || (type >= SN_EQ && type <= SN_GE) ||
        (type >= SN_SHL && type <= SN_ASHR))
        return 2;
    if (type == SN_REG_OUT)
        return SN_REG_FANIN_COUNT;
    if (type == SN_MEM_OUT)
        return SN_MEM_OUT_FANIN_COUNT;
    if (type == SN_MEM_READ)
        return SN_MEM_READ_FANIN_COUNT;
    if (type == SN_MEM_WRITE)
        return SN_MEM_WRITE_FANIN_COUNT;
    if (type == SN_MUX)
        return SN_MUX_FANIN_COUNT;
    if (type == SN_BMUX)
        return SN_BMUX_FANIN_COUNT;
    if (type == SN_PMUX)
        return SN_PMUX_FANIN_COUNT;
    return -1;
}

static inline bool sn_check_module_core(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    const sn_design_t* design = module ? module->design : NULL;
    size_t object_count;
    size_t offset = 0;
    bool safe = module && design;
    SN_CHECK(ctx, module, SN_INVALID_ID, module != NULL, "null module pointer");
    if (!safe)
        return false;
    SN_CHECK(ctx, module, SN_INVALID_ID, module->id < design->modules.size, "module ID %u is out of range", module->id);
    if (module->id < design->modules.size)
        SN_CHECK(ctx, module, SN_INVALID_ID, sn_vec_at(sn_module_t*, &design->modules, module->id) == module,
                 "module table does not point back to this module");
    SN_CHECK(ctx, module, SN_INVALID_ID, module->name < design->names.names.size, "module name ID %u is out of range",
             module->name);
    SN_CHECK(ctx, module, SN_INVALID_ID, (module->flags & ~SN_MODULE_ALL_FLAGS) == 0,
             "module flags 0x%x contain unsupported bits", module->flags);
    if (module->name < design->names.names.size)
    {
        const char* module_name = sn_name_get(&design->names, module->name);
        SN_CHECK(ctx, module, SN_INVALID_ID, module_name != NULL && module_name[0] != '\0',
                 "module name is null or empty");
        if (module_name && strncmp(module_name, "__sn_", 5) == 0)
            SN_CHECK(ctx, module, SN_INVALID_ID, sn_module_is_technology_primitive(module),
                     "module uses the reserved internal prefix __sn_");
    }

    safe &= sn_check_vec(ctx, module, &module->obj_types, "obj_types");
    safe &= sn_check_vec(ctx, module, &module->width_signed, "width_signed");
    safe &= sn_check_vec(ctx, module, &module->fanin_counts, "fanin_counts");
    safe &= sn_check_vec(ctx, module, &module->fanin_offsets, "fanin_offsets");
    safe &= sn_check_vec(ctx, module, &module->type_ids, "type_ids");
    safe &= sn_check_vec(ctx, module, &module->name_ids, "name_ids");
    safe &= sn_check_vec(ctx, module, &module->fanins, "fanins");
    if (!safe)
        return false;
    object_count = module->obj_types.size;
    SN_CHECK(ctx, module, SN_INVALID_ID, object_count < SN_INVALID_ID, "object count %zu is too large", object_count);
#define SN_CHECK_OBJECT_VECTOR(field)                                                                                  \
    SN_CHECK(ctx, module, SN_INVALID_ID, module->field.size == object_count,                                           \
             #field " size %zu differs from object count %zu", module->field.size, object_count)
    SN_CHECK_OBJECT_VECTOR(width_signed);
    SN_CHECK_OBJECT_VECTOR(fanin_counts);
    SN_CHECK_OBJECT_VECTOR(fanin_offsets);
    SN_CHECK_OBJECT_VECTOR(type_ids);
    SN_CHECK_OBJECT_VECTOR(name_ids);
#undef SN_CHECK_OBJECT_VECTOR
    if (module->width_signed.size != object_count || module->fanin_counts.size != object_count ||
        module->fanin_offsets.size != object_count || module->type_ids.size != object_count ||
        module->name_ids.size != object_count)
        return false;

    for (uint32_t type = 0; type < SN_OBJ_TYPE_COUNT; type++)
        safe &= sn_check_vec(ctx, module, &module->type_objects[type], "type_objects");
    if (!safe)
        return false;

    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_vec_at(sn_obj_type_t, &module->obj_types, object);
        uint32_t packed_width = sn_vec_at(uint32_t, &module->width_signed, object);
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object);
        uint32_t stored_offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
        uint32_t type_id = sn_vec_at(uint32_t, &module->type_ids, object);
        uint32_t name_id = sn_vec_at(uint32_t, &module->name_ids, object);
        bool type_valid = type > SN_NONE && type < SN_OBJ_TYPE_COUNT;
        SN_CHECK(ctx, module, object, type_valid, "object type %u is invalid", (unsigned)type);
        SN_CHECK(ctx, module, object, (packed_width >> 1) != 0 || type == SN_INST,
                 "object width is zero (only structural multi-output insts may have zero width)");
        SN_CHECK(ctx, module, object, stored_offset == offset, "fanin offset %u should be %zu", stored_offset, offset);
        SN_CHECK(ctx, module, object, offset <= module->fanins.size && count <= module->fanins.size - offset,
                 "fanin span [%zu, %zu) exceeds fanin storage size %zu", offset, offset + count, module->fanins.size);
        SN_CHECK(ctx, module, object, name_id == SN_INVALID_ID || name_id < design->names.names.size,
                 "name ID %u is out of range", name_id);
        if (type_valid && (type == SN_PI || type == SN_PO || type == SN_GATE))
        {
            const char* object_name = name_id < design->names.names.size
                                          ? sn_name_get(&design->names, name_id)
                                          : NULL;
            SN_CHECK(ctx, module, object,
                     object_name != NULL && object_name[0] != '\0',
                     "type %u requires a nonempty Verilog name", (unsigned)type);
        }
        if (type_valid)
        {
            int expected = sn_check_fixed_fanin_count(type);
            SN_CHECK(ctx, module, object, expected < 0 || count == (uint32_t)expected,
                     "type %u has %u fanins; expected %d", (unsigned)type, count, expected);
            SN_CHECK(ctx, module, object, type_id < module->type_objects[type].size,
                     "type ID %u is out of range for type %u", type_id, (unsigned)type);
            if (type_id < module->type_objects[type].size)
                SN_CHECK(ctx, module, object, sn_vec_at(sn_obj_id_t, &module->type_objects[type], type_id) == object,
                         "reverse type-object entry does not point back to this object");
        }
        if (offset <= module->fanins.size && count <= module->fanins.size - offset)
            for (uint32_t i = 0; i < count; i++)
            {
                sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset + i);
                SN_CHECK(ctx, module, object, fanin < object_count ||
                             (fanin == SN_INVALID_ID && type_valid &&
                              sn_obj_fanin_may_be_invalid(module, type, i)),
                         "fanin %u has invalid object ID %u", i, fanin);
            }
        offset += count;
    }
    SN_CHECK(ctx, module, SN_INVALID_ID, offset == module->fanins.size,
             "fanin spans use %zu entries but storage contains %zu", offset, module->fanins.size);

    if (sn_module_is_blackbox(module))
        for (sn_obj_id_t object = 0; object < object_count; object++)
        {
            sn_obj_type_t type = sn_vec_at(sn_obj_type_t, &module->obj_types, object);
            SN_CHECK(ctx, module, object, type == SN_PI || type == SN_PO,
                     "black-box module contains non-port object of type %u", (unsigned)type);
            if (type == SN_PO)
            {
                uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object);
                uint32_t po_offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
                SN_CHECK(ctx, module, object,
                         count == 1 && po_offset < module->fanins.size &&
                         sn_vec_at(sn_obj_id_t, &module->fanins, po_offset) == SN_INVALID_ID,
                         "black-box output must have one intentionally undriven fanin");
            }
        }

    for (uint32_t type = 0; type < SN_OBJ_TYPE_COUNT; type++)
        for (size_t type_id = 0; type_id < module->type_objects[type].size; type_id++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[type], type_id);
            SN_CHECK(ctx, module, object, object < object_count, "reverse type-object ID is out of range");
            if (object < object_count)
            {
                SN_CHECK(ctx, module, object, sn_vec_at(sn_obj_type_t, &module->obj_types, object) == type,
                         "reverse type-object entry has the wrong type");
                SN_CHECK(ctx, module, object, sn_vec_at(uint32_t, &module->type_ids, object) == type_id,
                         "reverse type-object entry has the wrong type ID");
            }
        }
    return true;
}

static inline bool sn_check_type_metadata(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    bool safe = true;
#define SN_CHECK_TYPE_VECTOR(field, type)                                                                              \
    do {                                                                                                               \
        safe &= sn_check_vec(ctx, module, &module->field, #field);                                                     \
        SN_CHECK(ctx, module, SN_INVALID_ID, module->field.size == module->type_objects[type].size,                    \
                 #field " size %zu differs from type %u count %zu", module->field.size, (unsigned)(type),             \
                 module->type_objects[type].size);                                                                     \
        safe &= module->field.size == module->type_objects[type].size;                                                 \
    } while (false)
    SN_CHECK_TYPE_VECTOR(reg_flags, SN_REG_OUT);
    SN_CHECK_TYPE_VECTOR(mem_depths, SN_MEM_OUT);
    SN_CHECK_TYPE_VECTOR(inst_modules, SN_INST);
    SN_CHECK_TYPE_VECTOR(fan_insts, SN_FAN);
    SN_CHECK_TYPE_VECTOR(slice_infos, SN_SLICE);
    SN_CHECK_TYPE_VECTOR(repeat_counts, SN_REPLICATE);
    SN_CHECK_TYPE_VECTOR(const_word_offsets, SN_CONST);
    SN_CHECK_TYPE_VECTOR(lut_truths, SN_LUT);
    SN_CHECK_TYPE_VECTOR(gate_ids, SN_GATE);
#undef SN_CHECK_TYPE_VECTOR
    return safe;
}

static inline void sn_check_pairs(sn_check_ctx_t* ctx, const sn_module_t* module, sn_obj_type_t out_type,
                                  sn_obj_type_t in_type, uint32_t pair_slot)
{
    size_t out_count = module->type_objects[out_type].size;
    size_t in_count = module->type_objects[in_type].size;
    SN_CHECK(ctx, module, SN_INVALID_ID, out_count == in_count, "pair types %u/%u have %zu/%zu objects",
             (unsigned)out_type, (unsigned)in_type, out_count, in_count);
    for (size_t i = 0; i < out_count && i < in_count; i++)
    {
        sn_obj_id_t out = sn_vec_at(sn_obj_id_t, &module->type_objects[out_type], i);
        sn_obj_id_t in = sn_vec_at(sn_obj_id_t, &module->type_objects[in_type], i);
        if (out >= module->obj_types.size || in >= module->obj_types.size)
            continue;
        SN_CHECK(ctx, module, out, sn_vec_at(uint32_t, &module->type_ids, out) == i &&
                     sn_vec_at(uint32_t, &module->type_ids, in) == i, "paired objects do not share type ID %zu", i);
        SN_CHECK(ctx, module, out, sn_vec_at(uint32_t, &module->width_signed, out) ==
                     sn_vec_at(uint32_t, &module->width_signed, in), "paired objects differ in width or signedness");
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, out);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, out);
        if (pair_slot < count && offset + pair_slot < module->fanins.size)
            SN_CHECK(ctx, module, out, sn_vec_at(sn_obj_id_t, &module->fanins, offset + pair_slot) == in,
                     "OUT object does not reference its paired IN object");
    }
}

static inline void sn_check_memories(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    size_t object_count = module->obj_types.size;
    uint32_t* owners = object_count ? (uint32_t*)calloc(object_count, sizeof(uint32_t)) : NULL;
    sn_obj_id_t* owner_memories = object_count ? (sn_obj_id_t*)malloc(object_count * sizeof(sn_obj_id_t)) : NULL;
    SN_CHECK(ctx, module, SN_INVALID_ID, object_count == 0 || (owners != NULL && owner_memories != NULL),
             "cannot allocate memory ownership map");
    if (object_count && (!owners || !owner_memories))
    {
        free(owners);
        free(owner_memories);
        return;
    }
    for (size_t i = 0; i < object_count; i++)
        owner_memories[i] = SN_INVALID_ID;
    for (size_t i = 0; i < module->type_objects[SN_MEM_OUT].size && i < module->mem_depths.size; i++)
    {
        sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_OUT], i);
        SN_CHECK(ctx, module, memory, sn_vec_at(uint32_t, &module->mem_depths, i) != 0, "memory depth is zero");
        if (memory >= object_count)
            continue;
        uint64_t init_width = (uint64_t)(sn_vec_at(uint32_t, &module->width_signed, memory) >> 1) *
                              sn_vec_at(uint32_t, &module->mem_depths, i);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, memory);
        for (uint32_t slot = SN_MEM_INIT_DATA; slot <= SN_MEM_INIT_MASK; slot++)
        {
            sn_obj_id_t value = sn_vec_at(sn_obj_id_t, &module->fanins, offset + slot);
            if (value == SN_INVALID_ID || value >= object_count)
                continue;
            SN_CHECK(ctx, module, memory, sn_check_const_type(sn_vec_at(sn_obj_type_t, &module->obj_types, value)),
                     "memory initialization slot %u is not driven by a constant", slot);
            SN_CHECK(ctx, module, memory, init_width <= UINT32_MAX &&
                         (sn_vec_at(uint32_t, &module->width_signed, value) >> 1) == init_width,
                     "memory initialization slot %u has the wrong width", slot);
        }
    }
    for (size_t i = 0; i < module->type_objects[SN_MEM_IN].size; i++)
    {
        sn_obj_id_t memory_in = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_IN], i);
        if (memory_in >= object_count)
            continue;
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, memory_in);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, memory_in);
        for (uint32_t j = 0; j < count; j++)
        {
            sn_obj_id_t write = sn_vec_at(sn_obj_id_t, &module->fanins, offset + j);
            SN_CHECK(ctx, module, memory_in, write < object_count &&
                         sn_vec_at(sn_obj_type_t, &module->obj_types, write) == SN_MEM_WRITE,
                     "memory input fanin %u is not a memory-write object", j);
            if (write < object_count && sn_vec_at(sn_obj_type_t, &module->obj_types, write) == SN_MEM_WRITE)
            {
                owners[write]++;
                if (owner_memories[write] == SN_INVALID_ID)
                    owner_memories[write] = memory_in;
            }
        }
    }
    for (size_t i = 0; i < module->type_objects[SN_MEM_WRITE].size; i++)
    {
        sn_obj_id_t write = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_WRITE], i);
        if (write >= object_count)
            continue;
        SN_CHECK(ctx, module, write, owners[write] == 1, "memory-write object has %u owners", owners[write]);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, write);
        sn_obj_id_t clock = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_WRITE_CLOCK);
        sn_obj_id_t enable = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_WRITE_ENABLE);
        sn_obj_id_t data = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_WRITE_DATA);
        if (clock < object_count)
            SN_CHECK(ctx, module, write, (sn_vec_at(uint32_t, &module->width_signed, clock) >> 1) == 1,
                     "memory-write clock is not one bit");
        if (enable < object_count)
            SN_CHECK(ctx, module, write, (sn_vec_at(uint32_t, &module->width_signed, enable) >> 1) == 1,
                     "memory-write enable is not one bit");
        if (data < object_count && owners[write] == 1)
        {
            sn_obj_id_t memory_in = owner_memories[write];
            SN_CHECK(ctx, module, write, memory_in < object_count &&
                         (sn_vec_at(uint32_t, &module->width_signed, data) >> 1) ==
                             (sn_vec_at(uint32_t, &module->width_signed, memory_in) >> 1),
                     "memory-write data width differs from its memory");
        }
    }
    for (size_t i = 0; i < module->type_objects[SN_MEM_READ].size; i++)
    {
        sn_obj_id_t read = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_READ], i);
        if (read >= object_count)
            continue;
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, read);
        sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_READ_MEMORY);
        sn_obj_id_t clock = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_READ_CLOCK);
        sn_obj_id_t enable = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_READ_ENABLE);
        SN_CHECK(ctx, module, read, memory < object_count &&
                     sn_vec_at(sn_obj_type_t, &module->obj_types, memory) == SN_MEM_OUT,
                 "memory-read object is not owned by a memory output");
        if (memory < object_count && sn_vec_at(sn_obj_type_t, &module->obj_types, memory) == SN_MEM_OUT)
            SN_CHECK(ctx, module, read, sn_vec_at(uint32_t, &module->width_signed, read) ==
                         sn_vec_at(uint32_t, &module->width_signed, memory),
                     "memory-read result differs from its memory width or signedness");
        if (clock < object_count)
            SN_CHECK(ctx, module, read, (sn_vec_at(uint32_t, &module->width_signed, clock) >> 1) == 1,
                     "memory-read clock is not one bit");
        if (enable < object_count)
            SN_CHECK(ctx, module, read, (sn_vec_at(uint32_t, &module->width_signed, enable) >> 1) == 1,
                     "memory-read enable is not one bit");
    }
    free(owner_memories);
    free(owners);
}

static inline void sn_check_instances(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    const sn_design_t* design = module->design;
    size_t object_count = module->obj_types.size;
    for (size_t i = 0; i < module->type_objects[SN_INST].size && i < module->inst_modules.size; i++)
    {
        sn_obj_id_t inst = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i);
        sn_module_id_t child_id = sn_vec_at(sn_module_id_t, &module->inst_modules, i);
        SN_CHECK(ctx, module, inst, child_id < design->modules.size, "referenced module ID %u is out of range",
                 child_id);
        if (inst >= object_count || child_id >= design->modules.size)
            continue;
        const sn_module_t* child = sn_vec_at(sn_module_t*, &design->modules, child_id);
        SN_CHECK(ctx, module, inst, child != NULL, "referenced module pointer is null");
        if (!child)
            continue;
        uint32_t inputs = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, inst);
        uint32_t input_offset = sn_vec_at(uint32_t, &module->fanin_offsets, inst);
        uint32_t outputs = (uint32_t)child->type_objects[SN_PO].size;
        SN_CHECK(ctx, module, inst, inputs == child->type_objects[SN_PI].size,
                 "inst has %u inputs but child module has %zu", inputs, child->type_objects[SN_PI].size);
        for (uint32_t input_index = 0; input_index < inputs && input_index < child->type_objects[SN_PI].size;
             input_index++)
        {
            sn_obj_id_t input = sn_vec_at(sn_obj_id_t, &module->fanins, input_offset + input_index);
            sn_obj_id_t port = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PI], input_index);
            if (input < object_count && port < child->width_signed.size)
                SN_CHECK(ctx, module, inst, (sn_vec_at(uint32_t, &module->width_signed, input) >> 1) ==
                             (sn_vec_at(uint32_t, &child->width_signed, port) >> 1),
                         "inst input %u width differs from the child port", input_index);
        }
        SN_CHECK(ctx, module, inst, outputs != 0, "instantiated module has no outputs");
        if (outputs == 1)
        {
            sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], 0);
            SN_CHECK(ctx, module, inst, sn_vec_at(uint32_t, &module->width_signed, inst) ==
                         sn_vec_at(uint32_t, &child->width_signed, output),
                     "single-output inst differs from its child output width or signedness");
        }
        else
        {
            SN_CHECK(ctx, module, inst, (sn_vec_at(uint32_t, &module->width_signed, inst) >> 1) == 0,
                     "multi-output inst must have zero structural width");
            for (uint32_t output_index = 0; output_index < outputs; output_index++)
            {
                sn_obj_id_t fan = inst + 1 + output_index;
                SN_CHECK(ctx, module, inst, fan < object_count &&
                             sn_vec_at(sn_obj_type_t, &module->obj_types, fan) == SN_FAN,
                         "output %u is not represented by the adjacent FAN object %u", output_index, fan);
                if (fan >= object_count || sn_vec_at(sn_obj_type_t, &module->obj_types, fan) != SN_FAN)
                    continue;
                uint32_t fan_id = sn_vec_at(uint32_t, &module->type_ids, fan);
                sn_obj_id_t child_output = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], output_index);
                SN_CHECK(ctx, module, fan, fan_id < module->fan_insts.size &&
                             sn_vec_at(sn_obj_id_t, &module->fan_insts, fan_id) == inst,
                         "FAN ownership does not reference its adjacent inst");
                SN_CHECK(ctx, module, fan, sn_vec_at(uint32_t, &module->width_signed, fan) ==
                             sn_vec_at(uint32_t, &child->width_signed, child_output),
                         "FAN differs from its child output width or signedness");
            }
        }
    }
    for (size_t i = 0; i < module->type_objects[SN_FAN].size && i < module->fan_insts.size; i++)
    {
        sn_obj_id_t fan = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_FAN], i);
        sn_obj_id_t inst = sn_vec_at(sn_obj_id_t, &module->fan_insts, i);
        SN_CHECK(ctx, module, fan, inst < fan && inst < object_count &&
                     sn_vec_at(sn_obj_type_t, &module->obj_types, inst) == SN_INST,
                 "FAN owner %u is not an earlier inst", inst);
        if (fan < object_count)
        {
            uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, fan);
            SN_CHECK(ctx, module, fan, offset < module->fanins.size &&
                         sn_vec_at(sn_obj_id_t, &module->fanins, offset) == inst,
                     "FAN data fanin does not reference its owning inst");
        }
        if (inst < object_count && sn_vec_at(sn_obj_type_t, &module->obj_types, inst) == SN_INST)
        {
            uint32_t inst_id = sn_vec_at(uint32_t, &module->type_ids, inst);
            if (inst_id < module->inst_modules.size)
            {
                sn_module_id_t child_id = sn_vec_at(sn_module_id_t, &module->inst_modules, inst_id);
                if (child_id < design->modules.size && sn_vec_at(sn_module_t*, &design->modules, child_id))
                {
                    const sn_module_t* child = sn_vec_at(sn_module_t*, &design->modules, child_id);
                    uint32_t output_index = fan - inst - 1;
                    SN_CHECK(ctx, module, fan, output_index < child->type_objects[SN_PO].size,
                             "FAN is outside its inst's natural adjacent output block");
                }
            }
        }
    }
}

static inline void sn_check_special_objects(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    size_t object_count = module->obj_types.size;
    size_t reg_count = module->reg_flags.size < module->type_objects[SN_REG_OUT].size
                           ? module->reg_flags.size
                           : module->type_objects[SN_REG_OUT].size;
    for (size_t i = 0; i < reg_count; i++)
    {
        sn_obj_id_t reg = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        uint32_t flags = sn_vec_at(uint32_t, &module->reg_flags, i);
        SN_CHECK(ctx, module, reg, (flags & ~SN_REG_FLAGS_ALL) == 0, "register flags 0x%x are invalid", flags);
        if (reg >= object_count)
            continue;
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, reg);
        sn_obj_id_t data = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_INIT_DATA);
        sn_obj_id_t mask = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_INIT_MASK);
        SN_CHECK(ctx, module, reg, data != SN_INVALID_ID || mask == SN_INVALID_ID,
                 "register init mask is present without init data");
        for (uint32_t slot = SN_REG_INIT_DATA; slot <= SN_REG_INIT_MASK; slot++)
        {
            sn_obj_id_t value = sn_vec_at(sn_obj_id_t, &module->fanins, offset + slot);
            if (value == SN_INVALID_ID || value >= object_count)
                continue;
            SN_CHECK(ctx, module, reg, sn_check_const_type(sn_vec_at(sn_obj_type_t, &module->obj_types, value)),
                     "register initialization slot %u is not a constant", slot);
            SN_CHECK(ctx, module, reg, (sn_vec_at(uint32_t, &module->width_signed, value) >> 1) ==
                         (sn_vec_at(uint32_t, &module->width_signed, reg) >> 1),
                     "register initialization slot %u has the wrong width", slot);
        }
    }
    size_t repeat_count = module->repeat_counts.size < module->type_objects[SN_REPLICATE].size
                              ? module->repeat_counts.size
                              : module->type_objects[SN_REPLICATE].size;
    for (size_t i = 0; i < repeat_count; i++)
        SN_CHECK(ctx, module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REPLICATE], i),
                 sn_vec_at(uint32_t, &module->repeat_counts, i) != 0, "repetition count is zero");
    size_t slice_count = module->slice_infos.size < module->type_objects[SN_SLICE].size
                             ? module->slice_infos.size
                             : module->type_objects[SN_SLICE].size;
    for (size_t i = 0; i < slice_count; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_SLICE], i);
        const sn_slice_info_t* info = &sn_vec_at(sn_slice_info_t, &module->slice_infos, i);
        SN_CHECK(ctx, module, object, (info->flags & ~SN_SLICE_DESCENDING) == 0, "slice flags are invalid");
        SN_CHECK(ctx, module, object, ((info->flags & SN_SLICE_DESCENDING) != 0) ==
                     (info->left_index >= info->right_index), "slice direction flag disagrees with its indices");
        if (object < object_count)
        {
            uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
            sn_obj_id_t value = sn_vec_at(sn_obj_id_t, &module->fanins, offset);
            if (value < object_count)
            {
                uint32_t source_width = sn_vec_at(uint32_t, &module->width_signed, value) >> 1;
                uint64_t slice_width = info->left_index >= info->right_index
                                           ? (uint64_t)(int64_t)info->left_index - info->right_index + 1
                                           : (uint64_t)(int64_t)info->right_index - info->left_index + 1;
                SN_CHECK(ctx, module, object, info->left_index >= 0 && (uint32_t)info->left_index < source_width,
                         "slice left index %d is outside source width %u", info->left_index, source_width);
                SN_CHECK(ctx, module, object, info->right_index >= 0 && (uint32_t)info->right_index < source_width,
                         "slice right index %d is outside source width %u", info->right_index, source_width);
                SN_CHECK(ctx, module, object, slice_width ==
                             (sn_vec_at(uint32_t, &module->width_signed, object) >> 1),
                         "slice width does not match its index range");
            }
        }
    }
    size_t const_count = module->const_word_offsets.size < module->type_objects[SN_CONST].size
                             ? module->const_word_offsets.size
                             : module->type_objects[SN_CONST].size;
    for (size_t i = 0; i < const_count; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_CONST], i);
        if (object >= object_count)
            continue;
        uint32_t words = ((sn_vec_at(uint32_t, &module->width_signed, object) >> 1) + 31) / 32;
        uint32_t offset = sn_vec_at(uint32_t, &module->const_word_offsets, i);
        SN_CHECK(ctx, module, object, offset <= module->design->constant_words.size &&
                     words <= module->design->constant_words.size - offset,
                 "constant word span [%u, %u) exceeds storage size %zu", offset, offset + words,
                 module->design->constant_words.size);
    }
    size_t lut_count = module->lut_truths.size < module->type_objects[SN_LUT].size
                           ? module->lut_truths.size
                           : module->type_objects[SN_LUT].size;
    for (size_t i = 0; i < lut_count; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_LUT], i);
        if (object >= object_count)
            continue;
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
        uint64_t truth = sn_vec_at(uint64_t, &module->lut_truths, i);
        SN_CHECK(ctx, module, object, (sn_vec_at(uint32_t, &module->width_signed, object) >> 1) == 1 &&
                     !(sn_vec_at(uint32_t, &module->width_signed, object) & 1),
                 "LUT output must be one-bit unsigned");
        SN_CHECK(ctx, module, object, count <= 6, "LUT has %u inputs; at most 6 are supported", count);
        if (count < 6)
            SN_CHECK(ctx, module, object, (truth >> (1u << count)) == 0,
                     "LUT truth table has nonzero unused high bits");
        for (uint32_t j = 0; j < count; j++)
        {
            sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset + j);
            if (fanin < object_count)
                SN_CHECK(ctx, module, object, (sn_vec_at(uint32_t, &module->width_signed, fanin) >> 1) == 1,
                         "LUT input %u is not one bit", j);
        }
    }
    size_t gate_count = module->gate_ids.size < module->type_objects[SN_GATE].size
                            ? module->gate_ids.size
                            : module->type_objects[SN_GATE].size;
    for (size_t i = 0; i < gate_count; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_GATE], i);
        if (object >= object_count)
            continue;
        SN_CHECK(ctx, module, object, sn_vec_at(uint32_t, &module->gate_ids, i) != SN_INVALID_ID,
                 "gate ID is invalid");
        SN_CHECK(ctx, module, object, (sn_vec_at(uint32_t, &module->width_signed, object) >> 1) == 1,
                 "gate output is not one bit");
    }
}

static inline void sn_check_operator_shapes(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    size_t object_count = module->obj_types.size;
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_vec_at(sn_obj_type_t, &module->obj_types, object);
        uint32_t width = sn_vec_at(uint32_t, &module->width_signed, object) >> 1;
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
        if (type == SN_CONCAT)
        {
            uint64_t packed_width = 0;
            for (uint32_t i = 0; i < count; i++)
            {
                sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset + i);
                if (fanin < object_count)
                    packed_width += sn_vec_at(uint32_t, &module->width_signed, fanin) >> 1;
            }
            SN_CHECK(ctx, module, object, packed_width == width,
                     "concatenation fanins contain %llu bits but output width is %u",
                     (unsigned long long)packed_width, width);
        }
        else if (type == SN_REPLICATE && count == 1)
        {
            sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset);
            uint32_t type_id = sn_vec_at(uint32_t, &module->type_ids, object);
            if (fanin < object_count && type_id < module->repeat_counts.size)
            {
                uint64_t packed_width = (uint64_t)(sn_vec_at(uint32_t, &module->width_signed, fanin) >> 1) *
                                        sn_vec_at(uint32_t, &module->repeat_counts, type_id);
                SN_CHECK(ctx, module, object, packed_width == width,
                         "repetition produces %llu bits but output width is %u",
                         (unsigned long long)packed_width, width);
            }
        }
        else if (type == SN_MUX && count == SN_MUX_FANIN_COUNT)
        {
            sn_obj_id_t select = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MUX_SELECT);
            sn_obj_id_t selected = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MUX_SELECTED);
            sn_obj_id_t default_value = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MUX_DEFAULT);
            if (select < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, select) >> 1) == 1,
                         "mux select is not one bit");
            if (selected < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, selected) >> 1) == width,
                         "mux selected branch width differs from output width");
            if (default_value < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, default_value) >> 1) == width,
                         "mux default branch width differs from output width");
        }
        else if (type == SN_BMUX && count == SN_BMUX_FANIN_COUNT)
        {
            sn_obj_id_t select = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_BMUX_SELECT);
            sn_obj_id_t alternatives = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_BMUX_ALTERNATIVES);
            if (select < object_count && alternatives < object_count)
            {
                uint32_t select_width = sn_vec_at(uint32_t, &module->width_signed, select) >> 1;
                uint32_t alternatives_width = sn_vec_at(uint32_t, &module->width_signed, alternatives) >> 1;
                bool valid = select_width < 31 && ((uint64_t)width << select_width) == alternatives_width;
                SN_CHECK(ctx, module, object, valid,
                         "binary mux alternatives width %u does not equal %u * 2^%u",
                         alternatives_width, width, select_width);
            }
        }
        else if (type == SN_PMUX && count == SN_PMUX_FANIN_COUNT)
        {
            sn_obj_id_t select = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_PMUX_SELECT);
            sn_obj_id_t alternatives = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_PMUX_ALTERNATIVES);
            sn_obj_id_t default_value = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_PMUX_DEFAULT);
            if (select < object_count && alternatives < object_count)
            {
                uint32_t select_width = sn_vec_at(uint32_t, &module->width_signed, select) >> 1;
                uint32_t alternatives_width = sn_vec_at(uint32_t, &module->width_signed, alternatives) >> 1;
                SN_CHECK(ctx, module, object, (uint64_t)width * select_width == alternatives_width,
                         "priority mux alternatives width %u does not equal %u * %u",
                         alternatives_width, width, select_width);
            }
            if (default_value < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, default_value) >> 1) == width,
                         "priority mux default width differs from output width");
        }
        else if (type == SN_REG_IN || type == SN_LOOP_IN)
        {
            if (count == 1)
            {
                sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset);
                if (fanin < object_count)
                    SN_CHECK(ctx, module, object,
                             (sn_vec_at(uint32_t, &module->width_signed, fanin) >> 1) == width,
                             "state input data width differs from state width");
            }
        }
        else if (type == SN_PO && count == 1)
        {
            sn_obj_id_t driver = sn_vec_at(sn_obj_id_t, &module->fanins, offset);
            if (driver < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, driver) >> 1) == width,
                         "primary-output driver width differs from output width");
        }
        else if (type == SN_MEM_READ && count == SN_MEM_READ_FANIN_COUNT)
        {
            sn_obj_id_t clock = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_READ_CLOCK);
            sn_obj_id_t enable = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_MEM_READ_ENABLE);
            SN_CHECK(ctx, module, object, clock != SN_INVALID_ID || enable == SN_INVALID_ID,
                     "memory read enable is present without a clock");
            if (clock < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, clock) >> 1) == 1,
                         "memory read clock is not one bit");
            if (enable < object_count)
                SN_CHECK(ctx, module, object,
                         (sn_vec_at(uint32_t, &module->width_signed, enable) >> 1) == 1,
                         "memory read enable is not one bit");
        }
    }

    for (size_t i = 0; i < module->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t reg = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        if (reg >= object_count)
            continue;
        uint32_t width = sn_vec_at(uint32_t, &module->width_signed, reg) >> 1;
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, reg);
        uint32_t flags = sn_vec_at(uint32_t, &module->reg_flags, i);
        sn_obj_id_t clock = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_CLOCK);
        sn_obj_id_t enable = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_ENABLE);
        sn_obj_id_t set = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_SET);
        sn_obj_id_t reset = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_RESET);
        if (flags & SN_REG_LATCH)
        {
            SN_CHECK(ctx, module, reg, clock == SN_INVALID_ID, "latch has a clock fanin");
            SN_CHECK(ctx, module, reg, enable < object_count, "latch has no enable fanin");
            SN_CHECK(ctx, module, reg, set == SN_INVALID_ID && reset == SN_INVALID_ID,
                     "latch has unsupported set or reset controls");
            SN_CHECK(ctx, module, reg, (flags & ~SN_REG_LATCH) == 0,
                     "latch has edge-triggered register flags 0x%x", flags & ~SN_REG_LATCH);
        }
        else
            SN_CHECK(ctx, module, reg, clock < object_count, "edge-triggered register has no clock fanin");
        const uint32_t one_bit_slots[] = {SN_REG_CLOCK, SN_REG_ENABLE, SN_REG_SET, SN_REG_RESET};
        for (size_t slot_index = 0; slot_index < sizeof(one_bit_slots) / sizeof(one_bit_slots[0]); slot_index++)
        {
            uint32_t slot = one_bit_slots[slot_index];
            sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset + slot);
            if (fanin < object_count)
                SN_CHECK(ctx, module, reg,
                         (sn_vec_at(uint32_t, &module->width_signed, fanin) >> 1) == 1,
                         "register control slot %u is not one bit", slot);
        }
        sn_obj_id_t reset_value = sn_vec_at(sn_obj_id_t, &module->fanins, offset + SN_REG_RESET_VALUE);
        if (reset_value < object_count)
            SN_CHECK(ctx, module, reg,
                     (sn_vec_at(uint32_t, &module->width_signed, reset_value) >> 1) == width,
                     "register reset value width differs from register width");
    }

    for (size_t i = 0; i < module->type_objects[SN_GATE].size; i++)
    {
        sn_obj_id_t gate = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_GATE], i);
        if (gate >= object_count)
            continue;
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, gate);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, gate);
        for (uint32_t j = 0; j < count; j++)
        {
            sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset + j);
            if (fanin < object_count)
                SN_CHECK(ctx, module, gate,
                         (sn_vec_at(uint32_t, &module->width_signed, fanin) >> 1) == 1,
                         "gate input %u is not one bit", j);
        }
    }
}

static inline void sn_check_auxiliary_storage(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    size_t object_count = module->obj_types.size;
    bool hash_safe = sn_check_vec(ctx, module, &module->const_hash_buckets, "constant hash buckets");
    hash_safe &= sn_check_vec(ctx, module, &module->const_hash_entries, "constant hash entries");
    if (hash_safe && !module->const_hash_buckets.size)
        SN_CHECK(ctx, module, SN_INVALID_ID, module->const_hash_entries.size == 0,
                 "constant hash entries exist without buckets");
    else if (hash_safe)
    {
        size_t bucket_count = module->const_hash_buckets.size;
        SN_CHECK(ctx, module, SN_INVALID_ID, (bucket_count & (bucket_count - 1)) == 0,
                 "constant hash bucket count %zu is not a power of two", bucket_count);
        uint8_t* seen = module->const_hash_entries.size
                            ? (uint8_t*)calloc(module->const_hash_entries.size, 1)
                            : NULL;
        SN_CHECK(ctx, module, SN_INVALID_ID, module->const_hash_entries.size == 0 || seen != NULL,
                 "cannot allocate constant-hash validation state");
        if (seen || !module->const_hash_entries.size)
            for (size_t bucket = 0; bucket < bucket_count; bucket++)
            {
                uint32_t entry_id = sn_vec_at(uint32_t, &module->const_hash_buckets, bucket);
                size_t steps = 0;
                while (entry_id != SN_INVALID_ID && entry_id < module->const_hash_entries.size &&
                       steps++ <= module->const_hash_entries.size)
                {
                    const sn_const_hash_entry_t* entry =
                        &sn_vec_at(sn_const_hash_entry_t, &module->const_hash_entries, entry_id);
                    SN_CHECK(ctx, module, entry->object, !seen[entry_id],
                             "constant hash entry %u appears more than once", entry_id);
                    seen[entry_id] = 1;
                    SN_CHECK(ctx, module, entry->object, (entry->hash & (bucket_count - 1)) == bucket,
                             "constant hash entry %u is in the wrong bucket", entry_id);
                    SN_CHECK(ctx, module, entry->object, entry->object < object_count,
                             "constant hash entry %u has an invalid object", entry_id);
                    if (entry->object < object_count)
                    {
                        sn_obj_type_t type = sn_vec_at(sn_obj_type_t, &module->obj_types, entry->object);
                        SN_CHECK(ctx, module, entry->object, sn_check_const_type(type),
                                 "constant hash entry refers to a nonconstant object");
                        SN_CHECK(ctx, module, entry->object,
                                 sn_vec_at(uint32_t, &module->name_ids, entry->object) == SN_INVALID_ID,
                                 "named constants must not appear in the interning cache");
                    }
                    entry_id = entry->next;
                }
                SN_CHECK(ctx, module, SN_INVALID_ID, entry_id == SN_INVALID_ID,
                         "constant hash bucket %zu has an invalid or cyclic chain", bucket);
            }
        if (seen)
            for (size_t i = 0; i < module->const_hash_entries.size; i++)
                SN_CHECK(ctx, module, SN_INVALID_ID, seen[i], "constant hash entry %zu is unreachable", i);
        free(seen);
    }

    bool fanout_safe = sn_check_vec(ctx, module, &module->fanout_counts, "fanout_counts");
    fanout_safe &= sn_check_vec(ctx, module, &module->fanout_offsets, "fanout_offsets");
    fanout_safe &= sn_check_vec(ctx, module, &module->fanouts, "fanouts");
    if (fanout_safe && !module->fanouts_valid)
        SN_CHECK(ctx, module, SN_INVALID_ID, module->fanout_counts.size == 0 &&
                     module->fanout_offsets.size == 0 && module->fanouts.size == 0,
                 "invalidated fanout cache is not empty");
    else if (fanout_safe)
    {
        SN_CHECK(ctx, module, SN_INVALID_ID, module->fanout_counts.size == object_count &&
                     module->fanout_offsets.size == object_count,
                 "valid fanout cache does not have one count and offset per object");
        if (module->fanout_counts.size == object_count && module->fanout_offsets.size == object_count)
        {
            size_t offset = 0;
            for (sn_obj_id_t object = 0; object < object_count; object++)
            {
                uint32_t stored = sn_vec_at(uint32_t, &module->fanout_offsets, object);
                uint32_t count = sn_vec_at(uint32_t, &module->fanout_counts, object);
                SN_CHECK(ctx, module, object, stored == offset, "fanout offset %u should be %zu", stored, offset);
                SN_CHECK(ctx, module, object, offset <= module->fanouts.size && count <= module->fanouts.size - offset,
                         "fanout span exceeds fanout storage");
                offset += count;
            }
            SN_CHECK(ctx, module, SN_INVALID_ID, offset == module->fanouts.size,
                     "fanout spans use %zu entries but storage contains %zu", offset, module->fanouts.size);
            for (size_t i = 0; i < module->fanouts.size; i++)
                SN_CHECK(ctx, module, SN_INVALID_ID, sn_vec_at(sn_obj_id_t, &module->fanouts, i) < object_count,
                         "fanout entry %zu has an invalid object ID", i);
        }
    }

    bool copy_safe = sn_check_vec(ctx, module, &module->copy_ids, "copy_ids");
    if (copy_safe && !module->copy_ids.size)
        SN_CHECK(ctx, module, SN_INVALID_ID, module->copy_module == SN_INVALID_ID,
                 "copy target exists without a copy map");
    else if (copy_safe)
    {
        SN_CHECK(ctx, module, SN_INVALID_ID, module->copy_ids.size == object_count,
                 "copy map size %zu differs from object count %zu", module->copy_ids.size, object_count);
        SN_CHECK(ctx, module, SN_INVALID_ID, module->copy_module < module->design->modules.size,
                 "copy target module ID %u is out of range", module->copy_module);
        if (module->copy_module < module->design->modules.size)
        {
            const sn_module_t* target = sn_vec_at(sn_module_t*, &module->design->modules, module->copy_module);
            if (target)
                for (size_t i = 0; i < module->copy_ids.size; i++)
                {
                    sn_obj_id_t copy = sn_vec_at(sn_obj_id_t, &module->copy_ids, i);
                    SN_CHECK(ctx, module, (sn_obj_id_t)i, copy == SN_INVALID_ID || copy < target->obj_types.size,
                             "copy object ID %u is out of range", copy);
                }
        }
    }
}

static inline void sn_check_topology(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    size_t object_count = module->obj_types.size;
    size_t pi_count = module->type_objects[SN_PI].size;
    size_t po_count = module->type_objects[SN_PO].size;
    bool valid = pi_count + po_count <= object_count;
    if (valid)
        for (size_t i = 0; i < pi_count; i++)
            valid &= sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], i) == i;
    if (valid)
        for (size_t i = 0; i < po_count; i++)
            valid &= sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], i) == object_count - po_count + i;
    for (sn_obj_id_t object = 0; valid && object < object_count; object++)
    {
        sn_obj_type_t type = sn_vec_at(sn_obj_type_t, &module->obj_types, object);
        sn_obj_id_t pair_in = SN_INVALID_ID;
        if (type == SN_REG_OUT || type == SN_MEM_OUT || type == SN_LOOP_OUT)
        {
            sn_obj_type_t in_type = type == SN_REG_OUT ? SN_REG_IN : type == SN_MEM_OUT ? SN_MEM_IN : SN_LOOP_IN;
            uint32_t type_id = sn_vec_at(uint32_t, &module->type_ids, object);
            if (type_id >= module->type_objects[in_type].size)
                valid = false;
            else
                pair_in = sn_vec_at(sn_obj_id_t, &module->type_objects[in_type], type_id);
            valid &= pair_in > object;
        }
        uint32_t count = sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object);
        uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
        for (uint32_t i = 0; valid && i < count; i++)
        {
            sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, offset + i);
            if (fanin == SN_INVALID_ID || fanin == pair_in)
                continue;
            valid &= pair_in != SN_INVALID_ID ? fanin < pair_in : fanin < object;
        }
    }
    SN_CHECK(ctx, module, SN_INVALID_ID, valid, "objects are not in legal SN topological order");
}

static inline bool sn_check_parse_u32(const char** cursor, uint32_t* value, char delimiter)
{
    char* end;
    unsigned long parsed;
    if (!cursor || !*cursor || !value || **cursor < '0' || **cursor > '9')
        return false;
    parsed = strtoul(*cursor, &end, 10);
    if (end == *cursor || parsed > UINT32_MAX || *end != delimiter)
        return false;
    *value = (uint32_t)parsed;
    *cursor = delimiter ? end + 1 : end;
    return true;
}

static inline bool sn_check_slice_bit(const sn_module_t* module, sn_obj_id_t object, sn_obj_id_t source,
                                      uint32_t bit)
{
    if (object == SN_INVALID_ID || object >= module->obj_types.size || sn_obj_type(module, object) != SN_SLICE ||
        sn_obj_fanin(module, object, 0) != source)
        return false;
    const sn_slice_info_t* info = sn_obj_slice_info(module, object);
    return info->left_index == (int32_t)bit && info->right_index == (int32_t)bit;
}

static inline void sn_check_carry_primitive(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    size_t pi_count = module->type_objects[SN_PI].size;
    size_t po_count = module->type_objects[SN_PO].size;
    const uint32_t pi_widths[] = {1, 1, 4, 4};
    SN_CHECK(ctx, module, SN_INVALID_ID, pi_count == 4 && po_count == 2,
             "carry primitive interface must have 4 inputs and 2 outputs");
    for (size_t i = 0; i < pi_count && i < 4; i++)
    {
        sn_obj_id_t pi = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], i);
        SN_CHECK(ctx, module, pi, sn_obj_width(module, pi) == pi_widths[i],
                 "carry primitive input %zu has the wrong width", i);
    }
    for (size_t i = 0; i < po_count; i++)
    {
        sn_obj_id_t po = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], i);
        SN_CHECK(ctx, module, po, sn_obj_width(module, po) == 4,
                 "carry primitive output %zu has the wrong width", i);
    }
    if (pi_count != 4 || po_count != 2)
        return;
    sn_obj_id_t ci = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 0);
    sn_obj_id_t cyinit = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 1);
    sn_obj_id_t di = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 2);
    sn_obj_id_t s = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 3);
    sn_obj_id_t o = sn_obj_fanin(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], 0), 0);
    sn_obj_id_t co = sn_obj_fanin(module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], 1), 0);
    bool packed = sn_obj_type(module, o) == SN_CONCAT && sn_obj_fanin_count(module, o) == 4 &&
                  sn_obj_type(module, co) == SN_CONCAT && sn_obj_fanin_count(module, co) == 4;
    SN_CHECK(ctx, module, SN_INVALID_ID, packed,
             "carry primitive outputs must be four-bit concatenations");
    if (!packed)
        return;
    sn_obj_id_t first_o = sn_obj_fanin(module, o, 0);
    sn_obj_id_t carry = sn_obj_type(module, first_o) == SN_BIT_XOR && sn_obj_fanin_count(module, first_o) == 2
                            ? sn_obj_fanin(module, first_o, 1)
                            : SN_INVALID_ID;
    bool initial = carry != SN_INVALID_ID && sn_obj_type(module, carry) == SN_BIT_OR &&
                   sn_obj_fanin_count(module, carry) == 2 &&
                   ((sn_obj_fanin(module, carry, 0) == ci && sn_obj_fanin(module, carry, 1) == cyinit) ||
                    (sn_obj_fanin(module, carry, 0) == cyinit && sn_obj_fanin(module, carry, 1) == ci));
    SN_CHECK(ctx, module, carry, initial, "carry primitive has an invalid initial carry expression");
    for (uint32_t bit = 0; bit < 4; bit++)
    {
        sn_obj_id_t o_bit = sn_obj_fanin(module, o, bit);
        sn_obj_id_t co_bit = sn_obj_fanin(module, co, bit);
        bool o_valid = sn_obj_type(module, o_bit) == SN_BIT_XOR && sn_obj_fanin_count(module, o_bit) == 2;
        bool co_valid = sn_obj_type(module, co_bit) == SN_MUX && sn_obj_fanin_count(module, co_bit) == 3;
        sn_obj_id_t s_bit = o_valid ? sn_obj_fanin(module, o_bit, 0) : SN_INVALID_ID;
        sn_obj_id_t di_bit = co_valid ? sn_obj_fanin(module, co_bit, SN_MUX_DEFAULT) : SN_INVALID_ID;
        o_valid &= s_bit != SN_INVALID_ID && sn_obj_fanin(module, o_bit, 1) == carry &&
                   sn_check_slice_bit(module, s_bit, s, bit);
        co_valid &= s_bit != SN_INVALID_ID && di_bit != SN_INVALID_ID &&
                    sn_obj_fanin(module, co_bit, SN_MUX_SELECT) == s_bit &&
                    sn_obj_fanin(module, co_bit, SN_MUX_SELECTED) == carry &&
                    sn_check_slice_bit(module, di_bit, di, bit);
        SN_CHECK(ctx, module, o_bit, o_valid, "carry primitive O[%u] has invalid logic", bit);
        SN_CHECK(ctx, module, co_bit, co_valid, "carry primitive CO[%u] has invalid logic", bit);
        carry = co_bit;
    }
}

static inline void sn_check_dsp_primitive(sn_check_ctx_t* ctx, const sn_module_t* module, const char* name)
{
    size_t pi_count = module->type_objects[SN_PI].size;
    size_t po_count = module->type_objects[SN_PO].size;
    size_t mul_count = module->type_objects[SN_MUL].size;
    SN_CHECK(ctx, module, SN_INVALID_ID, pi_count == 2 && po_count == 1,
             "DSP primitive interface must have 2 inputs and 1 output");
    SN_CHECK(ctx, module, SN_INVALID_ID, mul_count == 1,
             "DSP primitive behavioral wrapper must contain one multiplier");
    const char* shape = strstr(name, "_mul_");
    uint32_t a_width = 0, b_width = 0, y_width = 0;
    bool parsed = shape != NULL;
    const char* cursor = parsed ? shape + 5 : NULL;
    parsed &= sn_check_parse_u32(&cursor, &a_width, '_');
    parsed &= sn_check_parse_u32(&cursor, &b_width, '_');
    parsed &= sn_check_parse_u32(&cursor, &y_width, '_');
    parsed &= cursor && cursor[0] == 's' && (cursor[1] == '0' || cursor[1] == '1') &&
              (cursor[2] == '0' || cursor[2] == '1') && cursor[3] == '\0';
    SN_CHECK(ctx, module, SN_INVALID_ID, parsed, "DSP primitive name does not encode a valid interface");
    if (pi_count != 2 || po_count != 1 || mul_count != 1 || !parsed)
        return;
    bool a_signed = cursor[1] == '1';
    bool b_signed = cursor[2] == '1';
    sn_obj_id_t a = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 0);
    sn_obj_id_t b = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 1);
    sn_obj_id_t mul = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MUL], 0);
    sn_obj_id_t po = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], 0);
    bool valid = sn_obj_width(module, a) == a_width && sn_obj_is_signed(module, a) == a_signed &&
                 sn_obj_width(module, b) == b_width && sn_obj_is_signed(module, b) == b_signed &&
                 sn_obj_width(module, mul) == y_width && sn_obj_is_signed(module, mul) == (a_signed || b_signed) &&
                 sn_obj_fanin_count(module, mul) == 2 && sn_obj_fanin(module, mul, 0) == a &&
                 sn_obj_fanin(module, mul, 1) == b && sn_obj_width(module, po) == y_width &&
                 sn_obj_is_signed(module, po) == (a_signed || b_signed) && sn_obj_fanin(module, po, 0) == mul;
    SN_CHECK(ctx, module, SN_INVALID_ID, valid,
             "DSP primitive behavior does not match its encoded interface");
}

static inline uint32_t sn_check_address_width(uint32_t depth)
{
    uint32_t width = 0;
    for (uint32_t value = depth - 1; value; value >>= 1)
        width++;
    return width ? width : 1;
}

static inline void sn_check_memory_primitive(sn_check_ctx_t* ctx, const sn_module_t* module, const char* name)
{
    const char* marker = strstr(name, "_tdp_tile_");
    bool tdp = marker != NULL;
    bool legacy = false;
    if (!marker)
        marker = strstr(name, "_tile_");
    if (!marker)
    {
        marker = strstr(name, "_mem_");
        legacy = marker != NULL;
    }
    const char* cursor = marker ? marker + (tdp ? 10 : legacy ? 5 : 6) : NULL;
    uint32_t width = 0, depth = 0;
    bool parsed = marker && sn_check_parse_u32(&cursor, &width, '_') &&
                  sn_check_parse_u32(&cursor, &depth, '\0') && cursor && *cursor == '\0' && width && depth;
    SN_CHECK(ctx, module, SN_INVALID_ID, parsed, "memory primitive name does not encode valid dimensions");
    size_t pi_count = module->type_objects[SN_PI].size;
    size_t po_count = module->type_objects[SN_PO].size;
    size_t reads = module->type_objects[SN_MEM_READ].size;
    size_t writes = module->type_objects[SN_MEM_WRITE].size;
    SN_CHECK(ctx, module, SN_INVALID_ID, module->type_objects[SN_MEM_OUT].size == 1,
             "memory primitive wrapper must contain one memory");
    SN_CHECK(ctx, module, SN_INVALID_ID, reads == (tdp ? 2u : 1u) && writes == (tdp ? 2u : 1u),
             "memory primitive wrapper has the wrong number of read or write ports");
    SN_CHECK(ctx, module, SN_INVALID_ID, pi_count == (tdp ? 8u : 5u) && po_count == reads,
             "memory primitive interface has the wrong number of ports");
    if (!parsed || module->type_objects[SN_MEM_OUT].size != 1 || reads != (tdp ? 2u : 1u) ||
        writes != (tdp ? 2u : 1u) || pi_count != (tdp ? 8u : 5u) || po_count != reads)
        return;
    sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_OUT], 0);
    uint32_t address_width = legacy ? 32 : sn_check_address_width(depth);
    bool valid = sn_obj_width(module, memory) == width && sn_obj_mem_depth(module, memory) == depth;
    for (uint32_t port = 0; port < reads; port++)
    {
        uint32_t base = tdp ? 4 * port : 0;
        sn_obj_id_t clock = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], base);
        sn_obj_id_t enable = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], base + 1);
        sn_obj_id_t address = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], base + 2);
        sn_obj_id_t data = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], base + 3);
        sn_obj_id_t read_address = tdp ? address : sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], 4);
        sn_obj_id_t write = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_WRITE], port);
        sn_obj_id_t read = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_READ], port);
        sn_obj_id_t po = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], port);
        valid &= sn_obj_width(module, clock) == 1 && sn_obj_width(module, enable) == 1 &&
                 sn_obj_width(module, address) == address_width && sn_obj_width(module, data) == width &&
                 sn_obj_fanin(module, write, SN_MEM_WRITE_CLOCK) == clock &&
                 sn_obj_fanin(module, write, SN_MEM_WRITE_ENABLE) == enable &&
                 sn_obj_fanin(module, write, SN_MEM_WRITE_DATA) == data &&
                 sn_obj_fanin(module, write, SN_MEM_WRITE_ADDRESS) == address &&
                 sn_obj_fanin(module, read, SN_MEM_READ_MEMORY) == memory &&
                 sn_obj_fanin(module, read, SN_MEM_READ_CLOCK) == SN_INVALID_ID &&
                 sn_obj_fanin(module, read, SN_MEM_READ_ENABLE) == SN_INVALID_ID &&
                 sn_obj_width(module, read_address) == address_width &&
                 sn_obj_fanin(module, read, SN_MEM_READ_ADDRESS) == read_address &&
                 sn_obj_width(module, po) == width && sn_obj_fanin(module, po, 0) == read;
    }
    SN_CHECK(ctx, module, SN_INVALID_ID, valid,
             "memory primitive behavior does not match its encoded interface");
}

static inline void sn_check_primitive(sn_check_ctx_t* ctx, const sn_module_t* module)
{
    const char* name = sn_check_module_name(module);
    bool carry = strncmp(name, "__sn_CARRY", 10) == 0;
    bool dsp = strncmp(name, "__sn_DSP", 8) == 0;
    bool memory = strncmp(name, "__sn_RAM", 8) == 0 || strncmp(name, "__sn_URAM", 9) == 0;
    if (!carry && !dsp && !memory)
        return;
    if (sn_module_is_blackbox(module))
    {
        SN_CHECK(ctx, module, SN_INVALID_ID, false,
                 "reserved __sn_ technology primitives must have a validated behavioral body");
        return;
    }
    if (carry)
        sn_check_carry_primitive(ctx, module);
    else if (dsp)
        sn_check_dsp_primitive(ctx, module, name);
    else
        sn_check_memory_primitive(ctx, module, name);
}

typedef struct sn_check_hierarchy_frame_t
{
    sn_module_id_t module;
    size_t next_inst;
} sn_check_hierarchy_frame_t;

static inline void sn_check_hierarchy_visit(sn_check_ctx_t* ctx, const sn_design_t* design, sn_module_id_t root,
                                            uint8_t* states)
{
    sn_vec_t stack;
    sn_vec_init(&stack);
    states[root] = 1;
    sn_check_hierarchy_frame_t* first = sn_vec_push(sn_check_hierarchy_frame_t, &stack);
    first->module = root;
    first->next_inst = 0;
    while (stack.size)
    {
        sn_check_hierarchy_frame_t* frame =
            &sn_vec_at(sn_check_hierarchy_frame_t, &stack, stack.size - 1);
        const sn_module_t* module = sn_vec_at(sn_module_t*, &design->modules, frame->module);
        size_t inst_count = module ? module->inst_modules.size < module->type_objects[SN_INST].size
                                         ? module->inst_modules.size
                                         : module->type_objects[SN_INST].size
                                   : 0;
        if (frame->next_inst >= inst_count)
        {
            states[frame->module] = 2;
            stack.size--;
            continue;
        }
        size_t inst_index = frame->next_inst++;
        sn_module_id_t child = sn_vec_at(sn_module_id_t, &module->inst_modules, inst_index);
        if (child >= design->modules.size)
            continue;
        if (states[child] == 1)
            sn_check_error(ctx, module, sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], inst_index),
                           "recursive instantiation reaches module \"%s\"", sn_check_module_name(
                               sn_vec_at(sn_module_t*, &design->modules, child)));
        else if (states[child] == 0)
        {
            states[child] = 1;
            sn_check_hierarchy_frame_t* child_frame = sn_vec_push(sn_check_hierarchy_frame_t, &stack);
            child_frame->module = child;
            child_frame->next_inst = 0;
        }
    }
    sn_vec_destroy(&stack);
}

static inline bool sn_design_check(const sn_design_t* design, FILE* out, bool verbose)
{
    sn_check_ctx_t ctx = {out ? out : stderr, 0, 0, 0, verbose};
    bool safe = design != NULL;
    SN_CHECK(&ctx, NULL, SN_INVALID_ID, design != NULL, "null design pointer");
    if (!safe)
        return false;
    safe &= sn_check_vec(&ctx, NULL, &design->modules, "modules");
    safe &= sn_check_vec(&ctx, NULL, &design->names.names, "names");
    safe &= sn_check_vec(&ctx, NULL, &design->names.links, "name links");
    safe &= sn_check_vec(&ctx, NULL, &design->names.buckets, "name buckets");
    safe &= sn_check_vec(&ctx, NULL, &design->constant_words, "constant words");
    if (!safe)
        return false;
    SN_CHECK(&ctx, NULL, SN_INVALID_ID, design->modules.size < SN_INVALID_ID, "module count is too large");
    SN_CHECK(&ctx, NULL, SN_INVALID_ID, design->names.names.size == design->names.links.size,
             "name and link vector sizes differ");
    SN_CHECK(&ctx, NULL, SN_INVALID_ID, design->names.buckets.size != 0 &&
                 (design->names.buckets.size & (design->names.buckets.size - 1)) == 0,
             "name bucket count %zu is not a nonzero power of two", design->names.buckets.size);
    if (design->names.names.size != design->names.links.size)
        return false;
    for (size_t i = 0; i < design->names.names.size; i++)
    {
        const char* name = sn_vec_at(char*, &design->names.names, i);
        SN_CHECK(&ctx, NULL, SN_INVALID_ID, name != NULL, "name %zu has a null string", i);
        if (name)
            SN_CHECK(&ctx, NULL, SN_INVALID_ID, sn_check_name_is_emittable(name),
                     "name %zu cannot be emitted losslessly as a Verilog identifier", i);
    }
    uint8_t* name_seen = design->names.names.size ? (uint8_t*)calloc(design->names.names.size, 1) : NULL;
    SN_CHECK(&ctx, NULL, SN_INVALID_ID, design->names.names.size == 0 || name_seen != NULL,
             "cannot allocate name-hash validation state");
    for (size_t i = 0; i < design->names.buckets.size; i++)
    {
        uint32_t id = sn_vec_at(uint32_t, &design->names.buckets, i);
        size_t steps = 0;
        while (id != SN_INVALID_ID && id < design->names.names.size && steps++ <= design->names.names.size)
        {
            const char* name = sn_vec_at(char*, &design->names.names, id);
            if (name_seen)
            {
                SN_CHECK(&ctx, NULL, SN_INVALID_ID, !name_seen[id],
                         "name %u appears more than once in hash chains", id);
                name_seen[id] = 1;
            }
            if (name)
                SN_CHECK(&ctx, NULL, SN_INVALID_ID,
                         ((size_t)sn_name_hash(name) & (design->names.buckets.size - 1)) == i,
                         "name %u is linked from the wrong hash bucket", id);
            id = sn_vec_at(uint32_t, &design->names.links, id);
        }
        SN_CHECK(&ctx, NULL, SN_INVALID_ID, id == SN_INVALID_ID, "name bucket %zu has an invalid or cyclic chain", i);
    }
    if (name_seen)
        for (size_t i = 0; i < design->names.names.size; i++)
        {
            SN_CHECK(&ctx, NULL, SN_INVALID_ID, name_seen[i], "name %zu is unreachable from the hash table", i);
        }
    free(name_seen);
    sn_module_id_t* module_name_owners = design->names.names.size
                                             ? (sn_module_id_t*)malloc(design->names.names.size *
                                                                      sizeof(sn_module_id_t))
                                             : NULL;
    SN_CHECK(&ctx, NULL, SN_INVALID_ID, design->names.names.size == 0 || module_name_owners != NULL,
             "cannot allocate module-name validation state");
    for (size_t i = 0; module_name_owners && i < design->names.names.size; i++)
        module_name_owners[i] = SN_INVALID_ID;
    for (sn_module_id_t id = 0; id < design->modules.size; id++)
    {
        sn_module_t* module = sn_vec_at(sn_module_t*, &design->modules, id);
        size_t before = ctx.errors;
        SN_CHECK(&ctx, module, SN_INVALID_ID, module != NULL, "module table entry %u is null", id);
        if (module)
        {
            SN_CHECK(&ctx, module, SN_INVALID_ID, module->design == design,
                     "module points to a different owning design");
            if (module_name_owners && module->name < design->names.names.size)
            {
                SN_CHECK(&ctx, module, SN_INVALID_ID, module_name_owners[module->name] == SN_INVALID_ID,
                         "module name duplicates module %u", module_name_owners[module->name]);
                if (module_name_owners[module->name] == SN_INVALID_ID)
                    module_name_owners[module->name] = id;
            }
        }
        size_t before_core = ctx.errors;
        if (module && module->design == design && sn_check_module_core(&ctx, module) && ctx.errors == before_core)
        {
            bool metadata_safe = sn_check_type_metadata(&ctx, module);
            if (metadata_safe)
            {
                sn_check_pairs(&ctx, module, SN_REG_OUT, SN_REG_IN, SN_REG_DATA);
                sn_check_pairs(&ctx, module, SN_MEM_OUT, SN_MEM_IN, SN_MEM_STATE);
                sn_check_pairs(&ctx, module, SN_LOOP_OUT, SN_LOOP_IN, 0);
                sn_check_memories(&ctx, module);
                sn_check_instances(&ctx, module);
                sn_check_special_objects(&ctx, module);
                sn_check_operator_shapes(&ctx, module);
            }
            sn_check_auxiliary_storage(&ctx, module);
            sn_check_topology(&ctx, module);
            sn_check_primitive(&ctx, module);
        }
        ctx.modules++;
        if (module)
            ctx.objects += module->obj_types.size;
        if (verbose)
            fprintf(ctx.out, "SN check: module \"%s\": %zu object(s), %zu error(s).\n",
                    sn_check_module_name(module), module ? module->obj_types.size : 0, ctx.errors - before);
    }
    free(module_name_owners);
    if (design->modules.size)
    {
        uint8_t* states = (uint8_t*)calloc(design->modules.size, 1);
        SN_CHECK(&ctx, NULL, SN_INVALID_ID, states != NULL, "cannot allocate hierarchy traversal state");
        if (states)
        {
            for (sn_module_id_t id = 0; id < design->modules.size; id++)
                if (states[id] == 0)
                    sn_check_hierarchy_visit(&ctx, design, id, states);
            free(states);
        }
    }
    if (verbose || ctx.errors)
        fprintf(ctx.out, "SN check: %zu module(s), %zu object(s), %zu error(s).\n", ctx.modules, ctx.objects,
                ctx.errors);
    return ctx.errors == 0;
}

// Binary input is external data. Decode its byte-level representation first, then run the same non-aborting
// consistency checker used by @check before exposing any structural IDs or offsets to ordinary SN accessors.
static inline sn_design_t* sn_design_read_binary_checked(FILE* in, FILE* errors)
{
    sn_binary_read_status_t status = SN_BINARY_READ_OK;
    uint32_t version = 0;
    sn_design_t* design = sn_design_read_binary_raw_status(in, &status, &version);
    if (!design)
    {
        FILE* out = errors ? errors : stderr;
        if (status == SN_BINARY_READ_VERSION)
            fprintf(out, "Cannot read SN binary format version %u; this build supports versions %u through %u.\n",
                    version, SN_BINARY_MIN_READ_VERSION, SN_BINARY_FORMAT_VERSION);
        else if (status == SN_BINARY_READ_MAGIC)
            fprintf(out, "Input is not an SN binary file.\n");
        else if (status == SN_BINARY_READ_LAYOUT)
            fprintf(out, "SN binary layout does not match this build.\n");
        else if (status == SN_BINARY_READ_IO)
            fprintf(out, "Cannot read the SN binary header.\n");
        else
            fprintf(out, "Malformed or truncated SN binary input.\n");
        return NULL;
    }
    if (!sn_design_check(design, errors, false))
    {
        sn_design_destroy(design);
        return NULL;
    }
    return design;
}

static inline sn_design_t* sn_design_read_binary(FILE* in)
{
    return sn_design_read_binary_checked(in, stderr);
}

static inline sn_design_t* sn_design_read_binary_file(const char* path)
{
    if (!path)
        return NULL;
    FILE* in = fopen(path, "rb");
    if (!in)
        return NULL;
    sn_design_t* design = sn_design_read_binary_checked(in, stderr);
    if (!design)
    {
        fclose(in);
        return NULL;
    }
    int extra = fgetc(in);
    int status = ferror(in);
    status |= fclose(in) != 0;
    bool valid = extra == EOF && !status;
    if (!valid)
    {
        sn_design_destroy(design);
        return NULL;
    }
    return design;
}

#undef SN_CHECK

ABC_NAMESPACE_HEADER_END

#endif
