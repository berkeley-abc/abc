/**CFile****************************************************************

  FileName    [snLowerMem.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Selected native memory lowering to registers and read muxes.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snLowerMem.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__base__sn__snLowerMem_h
#define ABC__base__sn__snLowerMem_h
#include "sn.h"
ABC_NAMESPACE_HEADER_START

// Selection paths are relative to the chosen root (or prefixed by its module
// name). A path names a memory or an instance subtree, never a glob. Size is
// width * depth in bits, per native array, not per architectural RAM bank.
typedef struct sn_lower_mem_t
{
    sn_design_t* design;
    const char* root_name;
    const char** paths;
    size_t path_count;
    unsigned char* matched;
    uint64_t max_bits, memories, storage_bits, read_reg_bits, mux_bits, excluded;
    bool all, preview, valid;
    FILE* out;
    sn_module_id_t* cache;
} sn_lower_mem_t;

static inline char* sn_lower_mem_path(const char* prefix, const sn_module_t* module, sn_obj_id_t obj)
{
    char fallback[32];
    snprintf(fallback, sizeof(fallback), "@%u", obj);
    const char* name = sn_obj_name_id(module, obj) == SN_INVALID_ID ? fallback : sn_obj_name(module, obj);
    size_t size = strlen(prefix) + strlen(name) + 2;
    char* path = (char*)malloc(size);
    assert(path);
    snprintf(path, size, "%s%s%s", prefix, *prefix ? "/" : "", name);
    return path;
}

static inline bool sn_lower_mem_selected(sn_lower_mem_t* ctx, const char* path, uint64_t bits)
{
    bool select = ctx->all || ctx->path_count == 0;
    for (size_t i = 0; i < ctx->path_count; i++)
    {
        const char* p = ctx->paths[i];
        size_t root_length = strlen(ctx->root_name);
        if (!strncmp(p, ctx->root_name, root_length) && (p[root_length] == '/' || !p[root_length]))
            p += root_length + (p[root_length] == '/');
        size_t length = strlen(p);
        if (!length || (!strncmp(path, p, length) && (!path[length] || path[length] == '/')))
        {
            ctx->matched[i] = 1;
            select = true;
        }
    }
    if (select && ctx->max_bits && bits > ctx->max_bits)
    {
        if (ctx->preview && ++ctx->excluded <= 10)
            fprintf(ctx->out, "  %s: excluded by -S (%llu bits > %llu).\n", path,
                    (unsigned long long)bits, (unsigned long long)ctx->max_bits);
        return false;
    }
    return select;
}

// Without writes a fully initialized array is a constant table, not state.
static inline bool sn_lower_mem_constant_rom(const sn_module_t* m, sn_obj_id_t mem)
{
    if (sn_obj_mem_write_count(m, mem) || sn_obj_mem_init_data(m, mem) == SN_INVALID_ID) return false;
    sn_obj_id_t mask = sn_obj_mem_init_mask(m, mem);
    if (mask == SN_INVALID_ID) return true;
    uint64_t bits = (uint64_t)sn_obj_width(m, mem) * sn_obj_mem_depth(m, mem);
    if (bits > UINT32_MAX) return false;
    for (uint32_t b = 0; b < bits; b++)
        if (!sn_const_bit(m, mask, b)) return false;
    return true;
}

// Preserve all existing object IDs until the final topo rebuild. Ports and
// untouched states retain their type ordering; removed memory boundaries are
// harmless unused constants, and memory reads become buffers of the new logic.
static inline void sn_lower_mem_retype(sn_module_t* m, sn_obj_id_t obj, sn_obj_type_t type,
                                        sn_obj_id_t fanin)
{
    sn_obj_type_t old = sn_obj_type(m, obj);
    sn_vec_t* list = &m->type_objects[old];
    size_t k = 0;
    while (k < list->size && sn_vec_at(sn_obj_id_t, list, k) != obj) k++;
    assert(k < list->size);
    for (size_t i = k + 1; i < list->size; i++)
    {
        sn_obj_id_t moved = sn_vec_at(sn_obj_id_t, list, i);
        sn_vec_at(sn_obj_id_t, list, i - 1) = moved;
        if (sn_obj_type_has_dense_index(old)) sn_vec_at(uint32_t, &m->obj_data, moved) = (uint32_t)i - 1;
    }
    list->size--;
    sn_vec_at(sn_obj_type_t, &m->obj_types, obj) = type;
    sn_vec_at(uint32_t, &m->obj_data, obj) = (uint32_t)m->type_objects[type].size;
    if (type == SN_CONST0)
    {
        uint32_t zero = 0;
        sn_vec_at(uint32_t, &m->obj_data, obj) = sn_design_intern_const(m->design, 1, &zero);
    }
    *sn_vec_push(sn_obj_id_t, &m->type_objects[type]) = obj;
    sn_vec_at(uint16_t, &m->fanin_counts, obj) = fanin == SN_INVALID_ID ? 0 : 1;
    if (fanin != SN_INVALID_ID) sn_obj_connect(m, obj, 0, fanin);
}

static inline sn_obj_id_t sn_lower_mem_const_slice(sn_module_t* m, sn_obj_id_t constant,
                                                   uint32_t start, uint32_t width)
{
    if (constant == SN_INVALID_ID) return SN_INVALID_ID;
    uint32_t* words = (uint32_t*)calloc(((size_t)width + 31) / 32, sizeof(uint32_t));
    assert(words);
    for (uint32_t b = 0; b < width; b++)
        if (sn_const_bit(m, constant, start + b)) words[b / 32] |= UINT32_C(1) << (b % 32);
    sn_obj_id_t result = sn_module_add_const(m, width, false, words, NULL);
    free(words);
    return result;
}

static inline sn_obj_id_t sn_lower_mem_op2(sn_module_t* m, sn_obj_type_t type, uint32_t width,
                                           sn_obj_id_t a, sn_obj_id_t b)
{
    sn_obj_id_t inputs[2] = {a, b};
    return sn_module_add_operator(m, type, width, false, 2, inputs, NULL);
}

static inline sn_obj_id_t sn_lower_mem_decode(sn_module_t* m, sn_obj_id_t addr, uint32_t word)
{
    uint32_t width = sn_obj_width(m, addr);
    if (width < 32 && word >= (UINT32_C(1) << width))
        return sn_module_add_named_obj(m, SN_CONST0, 1, false, 0, NULL);
    if (sn_obj_is_signed(m, addr) && width <= 32 && word >= (UINT32_C(1) << (width - 1)))
        return sn_module_add_named_obj(m, SN_CONST0, 1, false, 0, NULL);
    uint32_t* bits = (uint32_t*)calloc(((size_t)width + 31) / 32, sizeof(uint32_t));
    assert(bits);
    bits[0] = word;
    sn_obj_id_t index = sn_module_add_const(m, width, false, bits, NULL);
    free(bits);
    return sn_lower_mem_op2(m, SN_EQ, 1, addr, index);
}

// One writer has unambiguous NBA semantics. Each address becomes a word register;
// a clocked read adds a separate enabled register and observes pre-write data.
// Out-of-range writes do nothing; out-of-range reads follow SN's two-state zero
// policy. X addresses are outside that two-state contract. No-write memories
// with unknown bits keep state in disabled registers driven by a constant clock;
// fully known read-only arrays become constants.
static inline void sn_lower_mem_expand(sn_module_t* m, sn_obj_id_t mem)
{
    assert(sn_obj_mem_write_count(m, mem) <= 1);
    uint32_t width = sn_obj_width(m, mem), depth = sn_obj_mem_depth(m, mem);
    sn_obj_id_t in = sn_mem_in(m, mem), data = sn_obj_mem_init_data(m, mem);
    sn_obj_id_t mask = sn_obj_mem_init_mask(m, mem);
    sn_obj_id_t write = sn_obj_mem_write_count(m, mem) ? sn_obj_mem_write(m, mem, 0) : SN_INVALID_ID;
    bool constant_rom = sn_lower_mem_constant_rom(m, mem);
    sn_obj_id_t zero = constant_rom ? SN_INVALID_ID : sn_module_add_named_obj(m, SN_CONST0, 1, false, 0, NULL);
    sn_obj_id_t clock = write == SN_INVALID_ID ? zero : sn_obj_fanin(m, write, SN_MEM_WRITE_CLOCK);
    sn_obj_id_t* words = (sn_obj_id_t*)malloc((size_t)depth * sizeof(sn_obj_id_t));
    assert(words);
    char* base = sn_lower_mem_path("", m, mem);
    char* name = (char*)malloc(strlen(base) + 32);
    char* sec_source = NULL;
    size_t sec_path_length = 0;
    long long sec_first = 0;
    unsigned sec_depth = 0, sec_width = 0;
    int sec_left = 0, sec_right = 0;
    for (size_t j = 0; j < m->attribute_records.size; j++)
    {
        const sn_attribute_record_t* attr = &sn_vec_at(sn_attribute_record_t, &m->attribute_records, j);
        if (attr->object != mem ||
            strcmp(sn_name_get(&m->design->names, attr->name), "sn_sec_memory"))
            continue;
        const char* value = sn_name_get(&m->design->names, attr->value);
        const char* separator = strrchr(value, '|');
        char extra;
        if (sec_source || !separator || separator == value ||
            sscanf(separator + 1, "%lld:%u:%d:%d:%u%c", &sec_first, &sec_depth,
                   &sec_left, &sec_right, &sec_width, &extra) != 5 ||
            sec_depth != depth || sec_width != width ||
            (sec_left >= sec_right ? (int64_t)sec_left - sec_right + 1 :
                                      (int64_t)sec_right - sec_left + 1) != width)
        {
            free(sec_source);
            sec_source = NULL;
            break;
        }
        sec_path_length = (size_t)(separator - value);
        sec_source = (char*)malloc(sec_path_length + 1);
        assert(sec_source);
        memcpy(sec_source, value, sec_path_length);
        sec_source[sec_path_length] = 0;
    }
    assert(name);
    for (uint32_t i = 0; i < depth; i++)
    {
        if (constant_rom)
        {
            words[i] = sn_lower_mem_const_slice(m, data, i * width, width);
            continue;
        }
        snprintf(name, strlen(base) + 32, "%s_word%u", base, i);
        sn_obj_pair_t reg = sn_module_add_reg_pair(m, width, sn_obj_is_signed(m, mem), name, NULL, clock);
        words[i] = reg.out;
        if (sec_source)
        {
            size_t identity_size = sec_path_length + 96;
            char* identity = (char*)malloc(identity_size);
            assert(identity);
            int written = snprintf(identity, identity_size, "%.*s[%lld]|%d:%d:%u",
                (int)sec_path_length, sec_source, sec_first + i, sec_left, sec_right, width);
            assert(written > 0 && (size_t)written < identity_size);
            (void)written;
            sn_module_add_attribute_record(m, reg.out, "sn_sec_identity", identity);
            free(identity);
        }
        sn_obj_id_t enable = zero, next = reg.out;
        if (write != SN_INVALID_ID)
        {
            enable = sn_lower_mem_decode(m, sn_obj_fanin(m, write, SN_MEM_WRITE_ADDRESS), i);
            sn_obj_id_t we = sn_obj_fanin(m, write, SN_MEM_WRITE_ENABLE);
            if (we != SN_INVALID_ID) enable = sn_lower_mem_op2(m, SN_BIT_AND, 1, enable, we);
            next = sn_obj_fanin(m, write, SN_MEM_WRITE_DATA);
        }
        sn_reg_set_fanin(m, reg.out, SN_REG_ENABLE, enable);
        sn_reg_set_fanin(m, reg.out, SN_REG_DATA, next);
        sn_obj_id_t initial = sn_lower_mem_const_slice(m, data, i * width, width);
        sn_obj_id_t valid = sn_lower_mem_const_slice(m, mask, i * width, width);
        sn_reg_set_init(m, reg.out, initial, valid);
    }
    free(name);
    free(base);
    free(sec_source);
    // Decode once per word/read port. A balanced OR tree combines disjoint
    // selected words without padding large, non-power-of-two memories.
    for (size_t k = 0; k < m->type_objects[SN_MEM_READ].size;)
    {
        sn_obj_id_t read = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_MEM_READ], k);
        if (sn_obj_fanin(m, read, SN_MEM_READ_MEMORY) != mem) { k++; continue; }
        sn_obj_id_t addr = sn_obj_fanin(m, read, SN_MEM_READ_ADDRESS);
        sn_obj_id_t rc = sn_obj_fanin(m, read, SN_MEM_READ_CLOCK);
        sn_obj_id_t re = sn_obj_fanin(m, read, SN_MEM_READ_ENABLE);
        sn_obj_id_t* terms = (sn_obj_id_t*)malloc((size_t)depth * sizeof(sn_obj_id_t));
        assert(terms);
        sn_obj_id_t empty = sn_module_add_named_obj(m, SN_CONST0, width, false, 0, NULL);
        for (uint32_t i = 0; i < depth; i++)
            terms[i] = sn_module_add_mux(m, sn_lower_mem_decode(m, addr, i), words[i], empty, NULL);
        uint32_t count = depth;
        while (count > 1)
        {
            uint32_t next = 0;
            for (uint32_t i = 0; i < count; i += 2)
                terms[next++] = i + 1 == count ? terms[i] :
                    sn_lower_mem_op2(m, SN_BIT_OR, width, terms[i], terms[i + 1]);
            count = next;
        }
        sn_obj_id_t value = terms[0];
        free(terms);
        if (rc != SN_INVALID_ID)
        {
            sn_obj_pair_t reg = sn_module_add_reg_pair(m, width, sn_obj_is_signed(m, mem), NULL, NULL, rc);
            sn_reg_set_fanin(m, reg.out, SN_REG_ENABLE, re);
            sn_reg_set_fanin(m, reg.out, SN_REG_DATA, value);
            value = reg.out;
        }
        sn_lower_mem_retype(m, read, SN_BUF, value);
    }
    free(words);
    if (write != SN_INVALID_ID) sn_lower_mem_retype(m, write, SN_CONST0, SN_INVALID_ID);
    sn_lower_mem_retype(m, in, SN_CONST0, SN_INVALID_ID);
    sn_lower_mem_retype(m, mem, SN_CONST0, SN_INVALID_ID);
}

// Copy-on-change hierarchy traversal: an occurrence selected by path receives
// its own specialized definition. Unselected siblings continue using the old
// definition. With no paths, or with explicit all-selection, memoization reuses
// each rewritten definition. Preview still counts all physical occurrences.
static inline sn_module_id_t sn_lower_mem_visit(sn_lower_mem_t* ctx, sn_module_id_t id, const char* path)
{
    bool memoize = ctx->all || !ctx->path_count;
    if (!ctx->preview && memoize && ctx->cache[id] != SN_INVALID_ID) return ctx->cache[id];
    sn_module_t* m = sn_design_get_module(ctx->design, id);
    if (sn_module_is_technology_primitive(m)) return id;
    size_t nmem = m->type_objects[SN_MEM_OUT].size, ninst = m->type_objects[SN_INST].size;
    unsigned char* chosen = (unsigned char*)calloc(nmem + 1, 1);
    sn_module_id_t* children = (sn_module_id_t*)malloc((ninst + 1) * sizeof(sn_module_id_t));
    assert(chosen && children);
    bool changed = false;
    for (size_t i = 0; i < nmem; i++)
    {
        sn_obj_id_t mem = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_MEM_OUT], i);
        uint32_t width = sn_obj_width(m, mem), depth = sn_obj_mem_depth(m, mem);
        uint64_t bits = (uint64_t)width * depth;
        char* full = sn_lower_mem_path(path, m, mem);
        if (sn_lower_mem_selected(ctx, full, bits))
        {
            chosen[i] = 1;
            changed = true;
            if (ctx->preview)
            {
                ctx->memories++;
                if (!sn_lower_mem_constant_rom(m, mem)) ctx->storage_bits += bits;
                if (ctx->memories <= 32) fprintf(ctx->out, "  %s: %u x %u = %llu storage bits\n",
                                                full, depth, width, (unsigned long long)bits);
                for (size_t r = 0; r < m->type_objects[SN_MEM_READ].size; r++)
                {
                    sn_obj_id_t read = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_MEM_READ], r);
                    if (sn_obj_fanin(m, read, SN_MEM_READ_MEMORY) != mem) continue;
                    ctx->mux_bits += (uint64_t)width * depth;
                    if (sn_obj_fanin(m, read, SN_MEM_READ_CLOCK) != SN_INVALID_ID) ctx->read_reg_bits += width;
                }
                if (sn_obj_mem_write_count(m, mem) > 1 || bits > UINT32_MAX)
                {
                    fprintf(ctx->out, "Cannot lower %s: %s.\n", full,
                            bits > UINT32_MAX ? "storage width exceeds supported limit" : "multiple write ports");
                    ctx->valid = false;
                }
            }
        }
        free(full);
    }
    for (size_t i = 0; i < ninst; i++)
    {
        sn_obj_id_t inst = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_INST], i);
        char* full = sn_lower_mem_path(path, m, inst);
        sn_module_id_t child = sn_inst_module_id(m, inst);
        children[i] = sn_lower_mem_visit(ctx, child, full);
        changed |= children[i] != child;
        free(full);
    }
    sn_module_id_t result = id;
    if (!ctx->preview && changed)
    {
        const char* source_name = sn_name_get(&ctx->design->names, m->name);
        size_t name_size = strlen(source_name) + 48;
        char* name = (char*)malloc(name_size);
        assert(name);
        uint32_t suffix = 0;
        do
            snprintf(name, name_size, "%s_lower_mem_%u", source_name, suffix++);
        while (sn_design_find_module(ctx->design, name) != SN_INVALID_ID);
        result = sn_design_dup_module_topo(ctx->design, id, name);
        free(name);
        sn_module_t* target = sn_design_get_module(ctx->design, result);
        for (size_t i = 0; i < ninst; i++)
        {
            sn_obj_id_t old = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_INST], i);
            sn_obj_set_data(target, sn_vec_at(sn_obj_id_t, &m->copy_ids, old), children[i]);
        }
        for (size_t i = 0; i < nmem; i++)
            if (chosen[i])
            {
                sn_obj_id_t old = sn_vec_at(sn_obj_id_t, &m->type_objects[SN_MEM_OUT], i);
                sn_lower_mem_expand(target, sn_vec_at(sn_obj_id_t, &m->copy_ids, old));
            }
        sn_design_reorder_module_topo(ctx->design, result);
    }
    if (!ctx->preview && memoize) ctx->cache[id] = result;
    free(chosen);
    free(children);
    return result;
}
ABC_NAMESPACE_HEADER_END
#endif
