/**CFile****************************************************************

  FileName    [sn.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Simple hierarchical word-level netlist data structures and core APIs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sn.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_H
#define SN_H

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_HEADER_START

// Simple Netlist (sn)
// -------------------
//
// A design owns a dense array of modules. A module owns a dense array of
// objects. There are no separate pin or net records: an object is identified
// by its module-local integer ID, and its fanins are object IDs in the same
// module. Fanouts are not stored by default; they can be derived and cached on
// demand.
//
// Core object properties use structure-of-arrays storage. Therefore an object
// ID is also the index of that object's type, width / signedness, fanin count,
// fanin offset, type ID, and name ID. A type ID indexes the dense array of
// objects of that type and any type-specific metadata.
//
// Ordered bit collections use LSB-first significance order throughout SN.
// Index zero denotes the least-significant bit, word, or concatenation operand;
// increasing indices denote increasingly significant data. This is an IR
// convention, independent of how SystemVerilog writes ranges and concatenations.
// Importers and writers must translate between the two conventions.
//
// All normal operators have one output, represented by the operator object
// itself. A single-output module inst is represented the same way. A
// multi-output module inst is immediately followed by one SN_FAN object
// per output in the referenced module's natural SN_PO order. Every SN_FAN has
// the inst as its sole fanin and stores only that inst ID as type-
// specific data. The invariant fan_id == inst_id + 1 + output_index makes
// the output index derived rather than stored.
//
// UINT32_MAX denotes an illegal, unused, or not-yet-connected fanin. This lets
// builders allocate objects before all dependencies have been translated.
//
// Registers, memories, and loop breakers are state / ordering boundaries made
// from adjacent OUT and IN objects. REG_OUT has fixed fanin slots for clock,
// data (= its paired REG_IN), enable, set, reset, packed initial data, an
// equally wide per-bit initialization-validity mask, and an optional nonzero/
// non-one reset value. REG_IN has one initially unresolved fanin for
// next-state data. MEM_OUT has fixed fanins for its paired MEM_IN, packed
// initialization data, and an equally wide per-bit validity mask. MEM_IN has
// zero or more MEM_WRITE fanins. MEM_READ objects consume MEM_OUT and
// represent individual read ports.
// Topological algorithms must not traverse OUT-to-IN structural edges as
// combinational dependencies.
//
// Each REG_OUT/REG_IN, MEM_OUT/MEM_IN, and LOOP_OUT/LOOP_IN pair shares one
// type ID. For pair index k, type_objects[OUT_TYPE][k] and
// type_objects[IN_TYPE][k] are the corresponding objects. This provides
// bidirectional lookup without storing another object ID. Constructors create
// adjacent OUT/IN objects, but topologically reordered modules need not retain
// that adjacency; the shared type ID is the authoritative pairing invariant.
//
// A module marked SN_MODULE_BLACKBOX retains only its declared PI/PO interface.
// Its implementation is intentionally opaque: hierarchy collapse preserves its
// insts, AIG construction abstracts their outputs as CIs and inputs as COs, and
// the Verilog writer emits a black-box module declaration without a body. Each
// black-box PO has SN_INVALID_ID as its sole fanin, denoting an unimplemented
// boundary value rather than an ordinary undriven net or a zero constant. An
// inout port is represented by same-named PI and PO objects.

#define SN_INVALID_ID UINT32_MAX

typedef uint32_t sn_obj_id_t;
typedef uint32_t sn_module_id_t;
typedef uint32_t sn_name_id_t;
typedef uint32_t sn_type_id_t;
typedef uint16_t sn_fanin_count_t;

typedef enum sn_module_flag_t
{
    SN_MODULE_NO_FLAGS = 0,
    SN_MODULE_BLACKBOX = 1u << 0
} sn_module_flag_t;

#define SN_MODULE_ALL_FLAGS ((uint32_t)SN_MODULE_BLACKBOX)

// A C-style generic vector. Cap and size are measured in elements.
// Access macros take the element type explicitly, for example:
//
//     sn_vec_t values;
//     sn_vec_init(&values);
//     *sn_vec_push(int, &values) = 42;
//     int value = sn_vec_at(int, &values, 0);
//
// The same API supports pointer element types:
//
//     *sn_vec_push(void *, &values) = pointer;
typedef struct sn_vec_t
{
    void* data;
    size_t cap;
    size_t size;
} sn_vec_t;

static inline void sn_vec_init(sn_vec_t* vec)
{
    assert(vec);
    vec->data = NULL;
    vec->cap = 0;
    vec->size = 0;
}

static inline void sn_vec_destroy(sn_vec_t* vec)
{
    assert(vec);
    free(vec->data);
    sn_vec_init(vec);
}

static inline void sn_vec_reserve_raw(sn_vec_t* vec, size_t size, size_t cap)
{
    assert(vec);
    assert(size);
    if (cap <= vec->cap)
        return;

    size_t new_cap = vec->cap ? vec->cap : 8;
    while (new_cap < cap)
    {
        assert(new_cap <= SIZE_MAX / 2);
        new_cap *= 2;
    }
    assert(new_cap <= SIZE_MAX / size);

    void* data = realloc(vec->data, new_cap * size);
    assert(data);
    vec->data = data;
    vec->cap = new_cap;
}

static inline void sn_vec_resize_raw(sn_vec_t* vec, size_t size, size_t count)
{
    assert(vec);
    size_t old_size = vec->size;
    sn_vec_reserve_raw(vec, size, count);
    if (count > old_size)
        memset((char*)vec->data + old_size * size, 0, (count - old_size) * size);
    vec->size = count;
}

static inline void* sn_vec_push_raw(sn_vec_t* vec, size_t size)
{
    assert(vec);
    assert(vec->size < SIZE_MAX);
    sn_vec_reserve_raw(vec, size, vec->size + 1);
    void* slot = (char*)vec->data + vec->size * size;
    memset(slot, 0, size);
    vec->size++;
    return slot;
}

static inline void sn_vec_dup_raw(sn_vec_t* target, const sn_vec_t* source, size_t element_size)
{
    assert(target && source && element_size && target->data == NULL && target->size == 0 && target->cap == 0);
    sn_vec_resize_raw(target, element_size, source->size);
    if (source->size)
        memcpy(target->data, source->data, source->size * element_size);
}

#define sn_vec_data(type, vec) ((type*)((vec)->data))
#define sn_vec_at(type, vec, index) (sn_vec_data(type, vec)[(index)])
#define sn_vec_reserve(type, vec, cap) sn_vec_reserve_raw((vec), sizeof(type), (cap))
#define sn_vec_resize(type, vec, count) sn_vec_resize_raw((vec), sizeof(type), (count))
#define sn_vec_push(type, vec) ((type*)sn_vec_push_raw((vec), sizeof(type)))
#define sn_vec_dup(type, target, source) sn_vec_dup_raw((target), (source), sizeof(type))

typedef uint8_t sn_obj_type_t;

enum sn_obj_type_enum
{
    SN_NONE = 0,

    // Design interface and structural objects.
    SN_PI,
    SN_PO,
    SN_CONST0,
    SN_CONST1,
    SN_CONST,
    SN_BUF,
    SN_FAN,
    SN_INST,

    // State and ordering boundaries.
    SN_REG_OUT,
    SN_REG_IN,
    SN_MEM_OUT,
    SN_MEM_IN,
    SN_MEM_READ,
    SN_MEM_WRITE,
    SN_LOOP_OUT,
    SN_LOOP_IN,

    // Unary operators.
    SN_POS,
    SN_NEG,
    SN_BIT_NOT,
    SN_LOG_NOT,
    SN_REDUCE_AND,
    SN_REDUCE_NAND,
    SN_REDUCE_OR,
    SN_REDUCE_NOR,
    SN_REDUCE_XOR,
    SN_REDUCE_XNOR,

    // Arithmetic operators.
    SN_ADD,
    SN_SUB,
    // Multiplication fanins retain their independent native widths and signedness. The SN_MUL width is the required
    // result width; blasting and mapping resize the product at its output rather than widening both operands first.
    SN_MUL,
    SN_DIV,
    SN_MOD,
    SN_POW,

    // Bitwise and logical operators.
    SN_BIT_AND,
    SN_BIT_OR,
    SN_BIT_XOR,
    SN_BIT_XNOR,
    SN_LOG_AND,
    SN_LOG_OR,

    // Comparison operators.
    SN_EQ,
    SN_NE,
    SN_CASE_EQ,
    SN_CASE_NE,
    SN_WILDCARD_EQ,
    SN_WILDCARD_NE,
    SN_LT,
    SN_LE,
    SN_GT,
    SN_GE,

    // Shift and word-construction operators.
    SN_SHL,
    SN_SHR,
    SN_ASHL,
    SN_ASHR,

    // Mux fanins always put the control first and any default value last.
    //
    // SN_MUX:  [select, selected_when_one, default_when_zero]
    // SN_BMUX: [binary_select, packed_alternatives]
    // SN_PMUX: [one_hot_select, packed_alternatives, default_when_zero]
    //
    // Packed alternatives use LSB-first significance order. Alternative i
    // occupies bits [i * output_width +: output_width]. SN_PMUX produces its
    // default when the select is zero and is undefined for a multi-hot select.
    SN_MUX,
    SN_BMUX,
    SN_PMUX,

    // Concatenation uses LSB-first significance order: fanin zero supplies the
    // least-significant result bits, and later fanins supply successively more-
    // significant bits. Repetition has one fanin and a type-indexed repeat count.
    // Slice has one fanin and type-indexed left, right, and direction data.
    // Cast also has one fanin. Its object width and signedness define the result:
    // widening sign-extends a signed result and zero-extends an unsigned result;
    // narrowing retains the LSB-first low-order bits; equal-width conversion
    // changes only the signedness annotation.
    SN_CONCAT,
    SN_REPLICATE,
    SN_SLICE,
    SN_CAST,

    // One-bit FPGA lookup table. Fanin zero is truth-table variable I0.
    // The low 2^fanin_count bits of the type-indexed uint64_t are significant.
    SN_LUT,

    // One-bit technology-mapped gate. Its uint32_t gate ID identifies the gate
    // in the technology library; fanins follow the library cell's input order.
    SN_GATE,

    SN_OBJ_TYPE_COUNT
};

// Use a negative-size array as a compile-time check because ABC is also built
// as C by MSVC, whose C frontend does not accept the C11 _Static_assert keyword.
typedef char sn_obj_type_count_must_fit_in_uint8_t[(SN_OBJ_TYPE_COUNT <= UINT8_MAX) ? 1 : -1];

typedef enum sn_mux_fanin_t
{
    SN_MUX_SELECT = 0,
    SN_MUX_SELECTED,
    SN_MUX_DEFAULT,
    SN_MUX_FANIN_COUNT
} sn_mux_fanin_t;

typedef enum sn_bmux_fanin_t
{
    SN_BMUX_SELECT = 0,
    SN_BMUX_ALTERNATIVES,
    SN_BMUX_FANIN_COUNT
} sn_bmux_fanin_t;

typedef enum sn_pmux_fanin_t
{
    SN_PMUX_SELECT = 0,
    SN_PMUX_ALTERNATIVES,
    SN_PMUX_DEFAULT,
    SN_PMUX_FANIN_COUNT
} sn_pmux_fanin_t;

enum
{
    SN_REG_CLOCK_NEGEDGE = 1u << 0,
    SN_REG_RESET_NEGEDGE = 1u << 1,
    SN_REG_RESET_ASYNC = 1u << 2,
    SN_REG_SET_NEGEDGE = 1u << 3,
    SN_REG_SET_ASYNC = 1u << 4,
    // A level-sensitive latch uses SN_REG_ENABLE as its gate and has no clock fanin.
    SN_REG_LATCH = 1u << 5,
    SN_REG_FLAGS_ALL =
        SN_REG_CLOCK_NEGEDGE | SN_REG_RESET_NEGEDGE | SN_REG_RESET_ASYNC | SN_REG_SET_NEGEDGE | SN_REG_SET_ASYNC |
        SN_REG_LATCH
};

typedef enum sn_reg_fanin_t
{
    SN_REG_CLOCK = 0,
    SN_REG_DATA,
    SN_REG_ENABLE,
    SN_REG_SET,
    SN_REG_RESET,
    SN_REG_INIT_DATA,
    SN_REG_INIT = SN_REG_INIT_DATA,
    SN_REG_INIT_MASK,
    // UINT32_MAX means the reset value is the implicit all-zero constant.
    SN_REG_RESET_VALUE,
    SN_REG_FANIN_COUNT
} sn_reg_fanin_t;

typedef struct sn_slice_info_t
{
    int32_t left_index;
    int32_t right_index;
    uint32_t flags;
} sn_slice_info_t;

enum
{
    SN_SLICE_DESCENDING = 1u << 0
};

// UINT32_MAX in the clock slot denotes an asynchronous read. UINT32_MAX in
// an enable slot denotes an always-enabled port.
typedef enum sn_mem_read_fanin_t
{
    SN_MEM_READ_MEMORY = 0,
    SN_MEM_READ_CLOCK,
    SN_MEM_READ_ENABLE,
    SN_MEM_READ_ADDRESS,
    SN_MEM_READ_FANIN_COUNT
} sn_mem_read_fanin_t;

typedef enum sn_mem_write_fanin_t
{
    SN_MEM_WRITE_CLOCK = 0,
    SN_MEM_WRITE_ENABLE,
    SN_MEM_WRITE_DATA,
    SN_MEM_WRITE_ADDRESS,
    SN_MEM_WRITE_FANIN_COUNT
} sn_mem_write_fanin_t;

// Memory initialization uses the same LSB-first packed layout for data and
// validity: entry zero occupies the least-significant word-width bits. A mask
// bit of one means that the corresponding data bit has a specified initial
// value. UINT32_MAX in either init slot means that the slot is absent; an
// absent mask with present data means that every data bit is valid.
typedef enum sn_mem_out_fanin_t
{
    SN_MEM_STATE = 0,
    SN_MEM_INIT_DATA,
    SN_MEM_INIT_MASK,
    SN_MEM_OUT_FANIN_COUNT
} sn_mem_out_fanin_t;

typedef struct sn_obj_pair_t
{
    sn_obj_id_t out;
    sn_obj_id_t in;
} sn_obj_pair_t;

typedef struct sn_name_mgr_t
{
    // char* entries owned by this manager and indexed by sn_name_id_t.
    sn_vec_t names;

    // Chained hash table. Buckets and links contain name IDs.
    sn_vec_t buckets;
    sn_vec_t links;
} sn_name_mgr_t;

typedef struct sn_design_t sn_design_t;

typedef struct sn_const_hash_entry_t
{
    uint64_t hash;
    sn_obj_id_t object;
    uint32_t next;
} sn_const_hash_entry_t;

typedef struct sn_module_t
{
    sn_design_t* design;
    sn_module_id_t id;
    sn_name_id_t name;
    uint32_t flags;

    // Core object attributes, all indexed by sn_obj_id_t.
    sn_vec_t obj_types;
    sn_vec_t width_signed;
    sn_vec_t fanin_counts;
    sn_vec_t fanin_offsets;
    sn_vec_t type_ids;
    sn_vec_t name_ids;

    // Concatenated fanin spans for all objects.
    sn_vec_t fanins;

    // For each object type, type_objects[type][type_id] is an object ID.
    sn_vec_t type_objects[SN_OBJ_TYPE_COUNT];

    // Type-specific metadata indexed by the corresponding OUT / object type ID.
    // uint32_t flags indexed by SN_REG_OUT type ID.
    sn_vec_t reg_flags;
    // uint32_t entry count indexed by SN_MEM_OUT type ID.
    sn_vec_t mem_depths;
    // Referenced sn_module_id_t indexed by SN_INST type ID.
    sn_vec_t inst_modules;
    // Owning sn_obj_id_t indexed by SN_FAN type ID.
    sn_vec_t fan_insts;
    sn_vec_t slice_infos;
    // uint32_t repetition count indexed by SN_REPLICATE type ID.
    sn_vec_t repeat_counts;
    // uint32_t offset into design->constant_words indexed by SN_CONST type ID.
    sn_vec_t const_word_offsets;
    // Derived chained hash table for unnamed constant interning. It is rebuilt lazily after binary loading.
    sn_vec_t const_hash_buckets;
    sn_vec_t const_hash_entries;
    // uint64_t truth table indexed by SN_LUT type ID.
    sn_vec_t lut_truths;
    // uint32_t technology-library gate ID indexed by SN_GATE type ID.
    sn_vec_t gate_ids;

    // Optional derived fanout cache, indexed like the fanin representation.
    sn_vec_t fanout_counts;
    sn_vec_t fanout_offsets;
    sn_vec_t fanouts;
    bool fanouts_valid;

    // PI and PO lists become immutable once this module is instantiated.
    bool interface_locked;

    // Most recent duplication map: old object ID -> object ID in copy_module.
    // It belongs to this source module and is released with the module.
    sn_vec_t copy_ids;
    sn_module_id_t copy_module;
} sn_module_t;

struct sn_design_t
{
    // sn_module_t* entries indexed by sn_module_id_t.
    sn_vec_t modules;
    sn_name_mgr_t names;

    // SN_CONST values other than zero and one, packed as 32-bit words in
    // LSB-first significance order. The module's const_word_offsets array
    // stores each constant's starting word offset.
    sn_vec_t constant_words;
};

// Memory accounting distinguishes populated payload bytes from reserved heap
// cap. Allocated bytes are the bytes requested from malloc/realloc; they
// do not include allocator headers or size-class rounding.
typedef struct sn_mem_size_t
{
    size_t used_bytes;
    size_t allocated_bytes;
} sn_mem_size_t;

// A module owns its struct and the payload allocations listed below. Vector
// headers are embedded in module_struct and are therefore not counted again.
typedef struct sn_module_mem_usage_t
{
    sn_mem_size_t module_struct;
    sn_mem_size_t obj_types;
    sn_mem_size_t width_signed;
    sn_mem_size_t fanin_counts;
    sn_mem_size_t fanin_offsets;
    sn_mem_size_t type_ids;
    sn_mem_size_t name_ids;
    sn_mem_size_t fanins;
    sn_mem_size_t type_objects[SN_OBJ_TYPE_COUNT];
    sn_mem_size_t reg_flags;
    sn_mem_size_t mem_depths;
    sn_mem_size_t inst_modules;
    sn_mem_size_t fan_insts;
    sn_mem_size_t slice_infos;
    sn_mem_size_t repeat_counts;
    sn_mem_size_t const_word_offsets;
    sn_mem_size_t const_hash_buckets;
    sn_mem_size_t const_hash_entries;
    sn_mem_size_t lut_truths;
    sn_mem_size_t gate_ids;
    sn_mem_size_t fanout_counts;
    sn_mem_size_t fanout_offsets;
    sn_mem_size_t fanouts;
    sn_mem_size_t copy_ids;
    sn_mem_size_t total;
} sn_module_mem_usage_t;

// modules is the sum of all module structs and their payloads. names is the
// sum of the name pointer/index/hash arrays and the separately allocated
// zero-terminated strings. constant_words is reported separately as requested.
typedef struct sn_design_mem_usage_t
{
    sn_mem_size_t design_struct;
    sn_mem_size_t module_table;
    sn_mem_size_t modules;
    sn_module_mem_usage_t module_attributes;
    sn_mem_size_t name_pointers;
    sn_mem_size_t name_buckets;
    sn_mem_size_t name_links;
    sn_mem_size_t name_strings;
    sn_mem_size_t names;
    sn_mem_size_t constant_words;
    sn_mem_size_t total;
} sn_design_mem_usage_t;

static inline sn_mem_size_t sn_mem_size_make(size_t used_bytes, size_t allocated_bytes)
{
    sn_mem_size_t usage = {used_bytes, allocated_bytes};
    return usage;
}

static inline sn_mem_size_t sn_vec_mem_usage(const sn_vec_t* vec, size_t size)
{
    assert(vec);
    assert(size);
    assert(vec->size <= vec->cap);
    assert(vec->cap <= SIZE_MAX / size);
    sn_mem_size_t usage = {vec->size * size, vec->cap * size};
    return usage;
}

static inline void sn_mem_size_add(sn_mem_size_t* total, sn_mem_size_t usage)
{
    assert(total);
    assert(total->used_bytes <= SIZE_MAX - usage.used_bytes);
    assert(total->allocated_bytes <= SIZE_MAX - usage.allocated_bytes);
    total->used_bytes += usage.used_bytes;
    total->allocated_bytes += usage.allocated_bytes;
}

static inline void sn_module_get_mem_usage(const sn_module_t* module, sn_module_mem_usage_t* usage)
{
    assert(module);
    assert(usage);
    memset(usage, 0, sizeof(*usage));
    usage->module_struct = sn_mem_size_make(sizeof(*module), sizeof(*module));
    usage->obj_types = sn_vec_mem_usage(&module->obj_types, sizeof(sn_obj_type_t));
    usage->width_signed = sn_vec_mem_usage(&module->width_signed, sizeof(uint32_t));
    usage->fanin_counts = sn_vec_mem_usage(&module->fanin_counts, sizeof(sn_fanin_count_t));
    usage->fanin_offsets = sn_vec_mem_usage(&module->fanin_offsets, sizeof(uint32_t));
    usage->type_ids = sn_vec_mem_usage(&module->type_ids, sizeof(uint32_t));
    usage->name_ids = sn_vec_mem_usage(&module->name_ids, sizeof(uint32_t));
    usage->fanins = sn_vec_mem_usage(&module->fanins, sizeof(sn_obj_id_t));
    for (size_t i = 0; i < SN_OBJ_TYPE_COUNT; i++)
        usage->type_objects[i] = sn_vec_mem_usage(&module->type_objects[i], sizeof(sn_obj_id_t));
    usage->reg_flags = sn_vec_mem_usage(&module->reg_flags, sizeof(uint32_t));
    usage->mem_depths = sn_vec_mem_usage(&module->mem_depths, sizeof(uint32_t));
    usage->inst_modules = sn_vec_mem_usage(&module->inst_modules, sizeof(sn_module_id_t));
    usage->fan_insts = sn_vec_mem_usage(&module->fan_insts, sizeof(sn_obj_id_t));
    usage->slice_infos = sn_vec_mem_usage(&module->slice_infos, sizeof(sn_slice_info_t));
    usage->repeat_counts = sn_vec_mem_usage(&module->repeat_counts, sizeof(uint32_t));
    usage->const_word_offsets = sn_vec_mem_usage(&module->const_word_offsets, sizeof(uint32_t));
    usage->const_hash_buckets = sn_vec_mem_usage(&module->const_hash_buckets, sizeof(uint32_t));
    usage->const_hash_entries = sn_vec_mem_usage(&module->const_hash_entries, sizeof(sn_const_hash_entry_t));
    usage->lut_truths = sn_vec_mem_usage(&module->lut_truths, sizeof(uint64_t));
    usage->gate_ids = sn_vec_mem_usage(&module->gate_ids, sizeof(uint32_t));
    usage->fanout_counts = sn_vec_mem_usage(&module->fanout_counts, sizeof(uint32_t));
    usage->fanout_offsets = sn_vec_mem_usage(&module->fanout_offsets, sizeof(uint32_t));
    usage->fanouts = sn_vec_mem_usage(&module->fanouts, sizeof(sn_obj_id_t));
    usage->copy_ids = sn_vec_mem_usage(&module->copy_ids, sizeof(sn_obj_id_t));

    usage->total = usage->module_struct;
#define SN_MEM_ADD_FIELD(field) sn_mem_size_add(&usage->total, usage->field)
    SN_MEM_ADD_FIELD(obj_types);
    SN_MEM_ADD_FIELD(width_signed);
    SN_MEM_ADD_FIELD(fanin_counts);
    SN_MEM_ADD_FIELD(fanin_offsets);
    SN_MEM_ADD_FIELD(type_ids);
    SN_MEM_ADD_FIELD(name_ids);
    SN_MEM_ADD_FIELD(fanins);
    for (size_t i = 0; i < SN_OBJ_TYPE_COUNT; i++)
        sn_mem_size_add(&usage->total, usage->type_objects[i]);
    SN_MEM_ADD_FIELD(reg_flags);
    SN_MEM_ADD_FIELD(mem_depths);
    SN_MEM_ADD_FIELD(inst_modules);
    SN_MEM_ADD_FIELD(fan_insts);
    SN_MEM_ADD_FIELD(slice_infos);
    SN_MEM_ADD_FIELD(repeat_counts);
    SN_MEM_ADD_FIELD(const_word_offsets);
    SN_MEM_ADD_FIELD(const_hash_buckets);
    SN_MEM_ADD_FIELD(const_hash_entries);
    SN_MEM_ADD_FIELD(lut_truths);
    SN_MEM_ADD_FIELD(gate_ids);
    SN_MEM_ADD_FIELD(fanout_counts);
    SN_MEM_ADD_FIELD(fanout_offsets);
    SN_MEM_ADD_FIELD(fanouts);
    SN_MEM_ADD_FIELD(copy_ids);
#undef SN_MEM_ADD_FIELD
}

static inline void sn_module_mem_usage_add(sn_module_mem_usage_t* total, const sn_module_mem_usage_t* usage)
{
    assert(total);
    assert(usage);
#define SN_MEM_ADD_MODULE_FIELD(field) sn_mem_size_add(&total->field, usage->field)
    SN_MEM_ADD_MODULE_FIELD(module_struct);
    SN_MEM_ADD_MODULE_FIELD(obj_types);
    SN_MEM_ADD_MODULE_FIELD(width_signed);
    SN_MEM_ADD_MODULE_FIELD(fanin_counts);
    SN_MEM_ADD_MODULE_FIELD(fanin_offsets);
    SN_MEM_ADD_MODULE_FIELD(type_ids);
    SN_MEM_ADD_MODULE_FIELD(name_ids);
    SN_MEM_ADD_MODULE_FIELD(fanins);
    for (size_t i = 0; i < SN_OBJ_TYPE_COUNT; i++)
        sn_mem_size_add(&total->type_objects[i], usage->type_objects[i]);
    SN_MEM_ADD_MODULE_FIELD(reg_flags);
    SN_MEM_ADD_MODULE_FIELD(mem_depths);
    SN_MEM_ADD_MODULE_FIELD(inst_modules);
    SN_MEM_ADD_MODULE_FIELD(fan_insts);
    SN_MEM_ADD_MODULE_FIELD(slice_infos);
    SN_MEM_ADD_MODULE_FIELD(repeat_counts);
    SN_MEM_ADD_MODULE_FIELD(const_word_offsets);
    SN_MEM_ADD_MODULE_FIELD(const_hash_buckets);
    SN_MEM_ADD_MODULE_FIELD(const_hash_entries);
    SN_MEM_ADD_MODULE_FIELD(lut_truths);
    SN_MEM_ADD_MODULE_FIELD(gate_ids);
    SN_MEM_ADD_MODULE_FIELD(fanout_counts);
    SN_MEM_ADD_MODULE_FIELD(fanout_offsets);
    SN_MEM_ADD_MODULE_FIELD(fanouts);
    SN_MEM_ADD_MODULE_FIELD(copy_ids);
    SN_MEM_ADD_MODULE_FIELD(total);
#undef SN_MEM_ADD_MODULE_FIELD
}

static inline void sn_design_get_mem_usage(const sn_design_t* design, sn_design_mem_usage_t* usage)
{
    assert(design);
    assert(usage);
    memset(usage, 0, sizeof(*usage));
    usage->design_struct = sn_mem_size_make(sizeof(*design), sizeof(*design));
    usage->module_table = sn_vec_mem_usage(&design->modules, sizeof(sn_module_t*));
    usage->name_pointers = sn_vec_mem_usage(&design->names.names, sizeof(char*));
    usage->name_buckets = sn_vec_mem_usage(&design->names.buckets, sizeof(uint32_t));
    usage->name_links = sn_vec_mem_usage(&design->names.links, sizeof(uint32_t));
    for (size_t i = 0; i < design->names.names.size; i++)
    {
        size_t string_bytes = strlen(sn_vec_at(char*, &design->names.names, i)) + 1;
        sn_mem_size_add(&usage->name_strings, sn_mem_size_make(string_bytes, string_bytes));
    }
    usage->names = usage->name_pointers;
    sn_mem_size_add(&usage->names, usage->name_buckets);
    sn_mem_size_add(&usage->names, usage->name_links);
    sn_mem_size_add(&usage->names, usage->name_strings);
    usage->constant_words = sn_vec_mem_usage(&design->constant_words, sizeof(uint32_t));
    for (size_t i = 0; i < design->modules.size; i++)
    {
        sn_module_mem_usage_t module_usage;
        sn_module_get_mem_usage(sn_vec_at(sn_module_t*, &design->modules, i), &module_usage);
        sn_module_mem_usage_add(&usage->module_attributes, &module_usage);
    }
    usage->modules = usage->module_attributes.total;
    usage->total = usage->design_struct;
    sn_mem_size_add(&usage->total, usage->module_table);
    sn_mem_size_add(&usage->total, usage->modules);
    sn_mem_size_add(&usage->total, usage->names);
    sn_mem_size_add(&usage->total, usage->constant_words);
}

static inline uint64_t sn_name_hash(const char* text)
{
    assert(text);
    uint64_t hash = UINT64_C(1469598103934665603);
    while (*text)
    {
        hash ^= (unsigned char)*text++;
        hash *= UINT64_C(1099511628211);
    }
    return hash;
}

static inline char* sn_string_dup(const char* text)
{
    assert(text);
    size_t size = strlen(text) + 1;
    char* copy = (char*)malloc(size);
    assert(copy);
    memcpy(copy, text, size);
    return copy;
}

static inline void sn_name_mgr_rehash(sn_name_mgr_t* mgr, size_t bucket_count)
{
    assert(mgr);
    assert(bucket_count >= 8);
    assert((bucket_count & (bucket_count - 1)) == 0);

    sn_vec_t buckets;
    sn_vec_init(&buckets);
    sn_vec_resize(uint32_t, &buckets, bucket_count);
    for (size_t i = 0; i < bucket_count; i++)
        sn_vec_at(uint32_t, &buckets, i) = SN_INVALID_ID;

    assert(mgr->links.size == mgr->names.size);
    for (size_t i = 0; i < mgr->names.size; i++)
    {
        const char* name = sn_vec_at(char*, &mgr->names, i);
        size_t bucket = (size_t)sn_name_hash(name) & (bucket_count - 1);
        sn_vec_at(uint32_t, &mgr->links, i) = sn_vec_at(uint32_t, &buckets, bucket);
        sn_vec_at(uint32_t, &buckets, bucket) = (uint32_t)i;
    }

    sn_vec_destroy(&mgr->buckets);
    mgr->buckets = buckets;
}

static inline void sn_name_mgr_init(sn_name_mgr_t* mgr)
{
    assert(mgr);
    sn_vec_init(&mgr->names);
    sn_vec_init(&mgr->buckets);
    sn_vec_init(&mgr->links);
    sn_name_mgr_rehash(mgr, 64);
}

static inline void sn_name_mgr_destroy(sn_name_mgr_t* mgr)
{
    assert(mgr);
    for (size_t i = 0; i < mgr->names.size; i++)
        free(sn_vec_at(char*, &mgr->names, i));
    sn_vec_destroy(&mgr->names);
    sn_vec_destroy(&mgr->buckets);
    sn_vec_destroy(&mgr->links);
}

static inline sn_name_id_t sn_name_find(const sn_name_mgr_t* mgr, const char* text)
{
    assert(mgr);
    assert(text);
    assert(mgr->buckets.size);

    size_t bucket = (size_t)sn_name_hash(text) & (mgr->buckets.size - 1);
    uint32_t id = sn_vec_at(uint32_t, &mgr->buckets, bucket);
    while (id != SN_INVALID_ID)
    {
        assert(id < mgr->names.size);
        if (strcmp(sn_vec_at(char*, &mgr->names, id), text) == 0)
            return id;
        id = sn_vec_at(uint32_t, &mgr->links, id);
    }
    return SN_INVALID_ID;
}

static inline sn_name_id_t sn_name_intern(sn_name_mgr_t* mgr, const char* text)
{
    assert(mgr);
    assert(text);

    sn_name_id_t id = sn_name_find(mgr, text);
    if (id != SN_INVALID_ID)
        return id;

    assert(mgr->names.size < SN_INVALID_ID);
    if ((mgr->names.size + 1) * 4 >= mgr->buckets.size * 3)
        sn_name_mgr_rehash(mgr, mgr->buckets.size * 2);

    id = (sn_name_id_t)mgr->names.size;
    size_t bucket = (size_t)sn_name_hash(text) & (mgr->buckets.size - 1);
    *sn_vec_push(char*, &mgr->names) = sn_string_dup(text);
    *sn_vec_push(uint32_t, &mgr->links) = sn_vec_at(uint32_t, &mgr->buckets, bucket);
    sn_vec_at(uint32_t, &mgr->buckets, bucket) = id;
    return id;
}

// Removes a temporary name that was the most recently interned entry. Reordering helpers use this after replacing a
// provisional module, preventing internal __sn_* names from accumulating in serialized designs.
static inline void sn_name_remove_last(sn_name_mgr_t* mgr, sn_name_id_t id)
{
    assert(mgr && mgr->names.size && id + 1 == mgr->names.size && mgr->links.size == mgr->names.size);
    const char* name = sn_vec_at(char*, &mgr->names, id);
    size_t bucket = (size_t)sn_name_hash(name) & (mgr->buckets.size - 1);
    uint32_t current = sn_vec_at(uint32_t, &mgr->buckets, bucket);
    uint32_t previous = SN_INVALID_ID;
    while (current != id)
    {
        assert(current != SN_INVALID_ID && current < id);
        previous = current;
        current = sn_vec_at(uint32_t, &mgr->links, current);
    }
    uint32_t next = sn_vec_at(uint32_t, &mgr->links, id);
    if (previous == SN_INVALID_ID)
        sn_vec_at(uint32_t, &mgr->buckets, bucket) = next;
    else
        sn_vec_at(uint32_t, &mgr->links, previous) = next;
    free(sn_vec_at(char*, &mgr->names, id));
    mgr->names.size--;
    mgr->links.size--;
}

static inline const char* sn_name_get(const sn_name_mgr_t* mgr, sn_name_id_t id)
{
    assert(mgr);
    assert(id < mgr->names.size);
    return sn_vec_at(char*, &mgr->names, id);
}

static inline void sn_module_init(sn_module_t* module, sn_design_t* design, sn_module_id_t id, sn_name_id_t name)
{
    assert(module);
    assert(design);
    module->design = design;
    module->id = id;
    module->name = name;
    module->flags = SN_MODULE_NO_FLAGS;

    sn_vec_init(&module->obj_types);
    sn_vec_init(&module->width_signed);
    sn_vec_init(&module->fanin_counts);
    sn_vec_init(&module->fanin_offsets);
    sn_vec_init(&module->type_ids);
    sn_vec_init(&module->name_ids);
    sn_vec_init(&module->fanins);
    for (size_t i = 0; i < SN_OBJ_TYPE_COUNT; i++)
        sn_vec_init(&module->type_objects[i]);
    sn_vec_init(&module->reg_flags);
    sn_vec_init(&module->mem_depths);
    sn_vec_init(&module->inst_modules);
    sn_vec_init(&module->fan_insts);
    sn_vec_init(&module->slice_infos);
    sn_vec_init(&module->repeat_counts);
    sn_vec_init(&module->const_word_offsets);
    sn_vec_init(&module->const_hash_buckets);
    sn_vec_init(&module->const_hash_entries);
    sn_vec_init(&module->lut_truths);
    sn_vec_init(&module->gate_ids);
    sn_vec_init(&module->fanout_counts);
    sn_vec_init(&module->fanout_offsets);
    sn_vec_init(&module->fanouts);
    module->fanouts_valid = false;
    module->interface_locked = false;
    sn_vec_init(&module->copy_ids);
    module->copy_module = SN_INVALID_ID;
}

static inline void sn_module_destroy(sn_module_t* module)
{
    assert(module);
    sn_vec_destroy(&module->obj_types);
    sn_vec_destroy(&module->width_signed);
    sn_vec_destroy(&module->fanin_counts);
    sn_vec_destroy(&module->fanin_offsets);
    sn_vec_destroy(&module->type_ids);
    sn_vec_destroy(&module->name_ids);
    sn_vec_destroy(&module->fanins);
    for (size_t i = 0; i < SN_OBJ_TYPE_COUNT; i++)
        sn_vec_destroy(&module->type_objects[i]);
    sn_vec_destroy(&module->reg_flags);
    sn_vec_destroy(&module->mem_depths);
    sn_vec_destroy(&module->inst_modules);
    sn_vec_destroy(&module->fan_insts);
    sn_vec_destroy(&module->slice_infos);
    sn_vec_destroy(&module->repeat_counts);
    sn_vec_destroy(&module->const_word_offsets);
    sn_vec_destroy(&module->const_hash_buckets);
    sn_vec_destroy(&module->const_hash_entries);
    sn_vec_destroy(&module->lut_truths);
    sn_vec_destroy(&module->gate_ids);
    sn_vec_destroy(&module->fanout_counts);
    sn_vec_destroy(&module->fanout_offsets);
    sn_vec_destroy(&module->fanouts);
    sn_vec_destroy(&module->copy_ids);
}

static inline sn_design_t* sn_design_create(void)
{
    sn_design_t* design = (sn_design_t*)calloc(1, sizeof(sn_design_t));
    assert(design);
    sn_vec_init(&design->modules);
    sn_name_mgr_init(&design->names);
    sn_vec_init(&design->constant_words);
    return design;
}

static inline void sn_design_destroy(sn_design_t* design)
{
    if (!design)
        return;
    for (size_t i = 0; i < design->modules.size; i++)
    {
        sn_module_t* module = sn_vec_at(sn_module_t*, &design->modules, i);
        sn_module_destroy(module);
        free(module);
    }
    sn_vec_destroy(&design->modules);
    sn_name_mgr_destroy(&design->names);
    sn_vec_destroy(&design->constant_words);
    free(design);
}

static inline sn_module_id_t sn_design_add_module_name_id(sn_design_t* design, sn_name_id_t name)
{
    assert(design);
    assert(name < design->names.names.size);
    assert(design->modules.size < SN_INVALID_ID);
    sn_module_id_t id = (sn_module_id_t)design->modules.size;
    sn_module_t* module = (sn_module_t*)calloc(1, sizeof(sn_module_t));
    assert(module);
    sn_module_init(module, design, id, name);
    *sn_vec_push(sn_module_t*, &design->modules) = module;
    return id;
}

static inline sn_module_id_t sn_design_add_module(sn_design_t* design, const char* name)
{
    assert(design);
    assert(name);
    sn_name_id_t name_id = sn_name_intern(&design->names, name);
    for (size_t i = 0; i < design->modules.size; i++)
        assert(sn_vec_at(sn_module_t*, &design->modules, i)->name != name_id);
    return sn_design_add_module_name_id(design, name_id);
}

static inline sn_module_t* sn_design_get_module(sn_design_t* design, sn_module_id_t id)
{
    assert(design);
    assert(id < design->modules.size);
    return sn_vec_at(sn_module_t*, &design->modules, id);
}

static inline const sn_module_t* sn_design_get_module_const(const sn_design_t* design, sn_module_id_t id)
{
    assert(design);
    assert(id < design->modules.size);
    return sn_vec_at(sn_module_t*, &design->modules, id);
}

static inline sn_module_id_t sn_design_find_module(const sn_design_t* design, const char* name)
{
    assert(design);
    assert(name);
    sn_name_id_t name_id = sn_name_find(&design->names, name);
    if (name_id == SN_INVALID_ID)
        return SN_INVALID_ID;
    for (sn_module_id_t id = 0; id < design->modules.size; id++)
        if (sn_design_get_module_const(design, id)->name == name_id)
            return id;
    return SN_INVALID_ID;
}

static inline bool sn_module_is_blackbox(const sn_module_t* module)
{
    assert(module);
    return (module->flags & SN_MODULE_BLACKBOX) != 0;
}

static inline void sn_module_set_blackbox(sn_module_t* module, bool blackbox)
{
    assert(module);
    if (blackbox)
        module->flags |= SN_MODULE_BLACKBOX;
    else
        module->flags &= ~((uint32_t)SN_MODULE_BLACKBOX);
}

// Deep-copy the semantic design state directly in memory. Derived constant-interner tables are intentionally left
// empty and rebuilt lazily, matching binary roundtrip behavior. Fanout caches and optional object-copy maps are
// preserved because callers may intentionally retain them between transformations.
static inline sn_design_t* sn_design_dup(const sn_design_t* source)
{
    assert(source);
    sn_design_t* target = sn_design_create();
    for (size_t i = 0; i < source->names.names.size; i++)
    {
        sn_name_id_t name = sn_name_intern(&target->names, sn_name_get(&source->names, (sn_name_id_t)i));
        assert(name == i);
    }
    sn_vec_dup(uint32_t, &target->constant_words, &source->constant_words);
    for (sn_module_id_t module_id = 0; module_id < source->modules.size; module_id++)
    {
        const sn_module_t* old_module = sn_design_get_module_const(source, module_id);
        sn_module_id_t new_id = sn_design_add_module(target, sn_name_get(&source->names, old_module->name));
        assert(new_id == module_id);
        sn_module_t* new_module = sn_design_get_module(target, new_id);
        new_module->flags = old_module->flags;
        new_module->fanouts_valid = old_module->fanouts_valid;
        new_module->interface_locked = old_module->interface_locked;
        new_module->copy_module = old_module->copy_module;
#define SN_DUP_MODULE_VECTOR(type, field) sn_vec_dup(type, &new_module->field, &old_module->field)
        SN_DUP_MODULE_VECTOR(sn_obj_type_t, obj_types);
        SN_DUP_MODULE_VECTOR(uint32_t, width_signed);
        SN_DUP_MODULE_VECTOR(sn_fanin_count_t, fanin_counts);
        SN_DUP_MODULE_VECTOR(uint32_t, fanin_offsets);
        SN_DUP_MODULE_VECTOR(uint32_t, type_ids);
        SN_DUP_MODULE_VECTOR(uint32_t, name_ids);
        SN_DUP_MODULE_VECTOR(sn_obj_id_t, fanins);
        for (uint32_t type = 0; type < SN_OBJ_TYPE_COUNT; type++)
            sn_vec_dup(sn_obj_id_t, &new_module->type_objects[type], &old_module->type_objects[type]);
        SN_DUP_MODULE_VECTOR(uint32_t, reg_flags);
        SN_DUP_MODULE_VECTOR(uint32_t, mem_depths);
        SN_DUP_MODULE_VECTOR(sn_module_id_t, inst_modules);
        SN_DUP_MODULE_VECTOR(sn_obj_id_t, fan_insts);
        SN_DUP_MODULE_VECTOR(sn_slice_info_t, slice_infos);
        SN_DUP_MODULE_VECTOR(uint32_t, repeat_counts);
        SN_DUP_MODULE_VECTOR(uint32_t, const_word_offsets);
        SN_DUP_MODULE_VECTOR(uint64_t, lut_truths);
        SN_DUP_MODULE_VECTOR(uint32_t, gate_ids);
        SN_DUP_MODULE_VECTOR(uint32_t, fanout_counts);
        SN_DUP_MODULE_VECTOR(uint32_t, fanout_offsets);
        SN_DUP_MODULE_VECTOR(sn_obj_id_t, fanouts);
        SN_DUP_MODULE_VECTOR(sn_obj_id_t, copy_ids);
#undef SN_DUP_MODULE_VECTOR
    }
    return target;
}

static inline uint32_t sn_design_module_output_count(const sn_design_t* design, sn_module_id_t module_id)
{
    const sn_module_t* module = sn_design_get_module_const(design, module_id);
    assert(module->type_objects[SN_PO].size <= UINT32_MAX);
    return (uint32_t)module->type_objects[SN_PO].size;
}

static inline uint32_t sn_pack_width_signed(uint32_t width, bool is_signed)
{
    assert(width <= UINT32_MAX >> 1);
    return (width << 1) | (is_signed ? 1u : 0u);
}

static inline uint32_t sn_obj_width(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(object < module->width_signed.size);
    return sn_vec_at(uint32_t, &module->width_signed, object) >> 1;
}

static inline bool sn_obj_is_signed(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(object < module->width_signed.size);
    return (sn_vec_at(uint32_t, &module->width_signed, object) & 1u) != 0;
}

static inline sn_obj_type_t sn_obj_type(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(object < module->obj_types.size);
    return sn_vec_at(sn_obj_type_t, &module->obj_types, object);
}

static inline sn_type_id_t sn_obj_type_id(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(object < module->type_ids.size);
    return sn_vec_at(uint32_t, &module->type_ids, object);
}

static inline sn_name_id_t sn_obj_name_id(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(object < module->name_ids.size);
    return sn_vec_at(uint32_t, &module->name_ids, object);
}

static inline const char* sn_obj_name(const sn_module_t* module, sn_obj_id_t object)
{
    sn_name_id_t name = sn_obj_name_id(module, object);
    assert(name != SN_INVALID_ID);
    return sn_name_get(&module->design->names, name);
}

static inline void sn_module_invalidate_fanouts(sn_module_t* module)
{
    assert(module);
    module->fanouts_valid = false;
    module->fanout_counts.size = 0;
    module->fanout_offsets.size = 0;
    module->fanouts.size = 0;
}

static inline sn_obj_id_t sn_module_add_obj(sn_module_t* module, sn_obj_type_t type, uint32_t width, bool is_signed,
                                            uint32_t fanin_count, sn_name_id_t name)
{
    assert(module);
    assert(type > SN_NONE && type < SN_OBJ_TYPE_COUNT);
    assert(module->obj_types.size < SN_INVALID_ID);
    assert(fanin_count <= UINT16_MAX);
    assert(module->fanins.size + fanin_count <= UINT32_MAX);
    assert(name == SN_INVALID_ID || name < module->design->names.names.size);

    size_t object_count = module->obj_types.size + 1;
    sn_vec_reserve(sn_obj_type_t, &module->obj_types, object_count);
    sn_vec_reserve(uint32_t, &module->width_signed, object_count);
    sn_vec_reserve(sn_fanin_count_t, &module->fanin_counts, object_count);
    sn_vec_reserve(uint32_t, &module->fanin_offsets, object_count);
    sn_vec_reserve(uint32_t, &module->type_ids, object_count);
    sn_vec_reserve(uint32_t, &module->name_ids, object_count);
    sn_vec_reserve(sn_obj_id_t, &module->fanins, module->fanins.size + fanin_count);

    sn_vec_t* objects_of_type = &module->type_objects[type];
    assert(objects_of_type->size < SN_INVALID_ID);
    sn_vec_reserve(sn_obj_id_t, objects_of_type, objects_of_type->size + 1);

    if (type == SN_REG_OUT)
        sn_vec_reserve(uint32_t, &module->reg_flags, module->reg_flags.size + 1);
    else if (type == SN_MEM_OUT)
        sn_vec_reserve(uint32_t, &module->mem_depths, module->mem_depths.size + 1);
    else if (type == SN_INST)
        sn_vec_reserve(sn_module_id_t, &module->inst_modules, module->inst_modules.size + 1);
    else if (type == SN_FAN)
        sn_vec_reserve(sn_obj_id_t, &module->fan_insts, module->fan_insts.size + 1);
    else if (type == SN_SLICE)
        sn_vec_reserve(sn_slice_info_t, &module->slice_infos, module->slice_infos.size + 1);
    else if (type == SN_REPLICATE)
        sn_vec_reserve(uint32_t, &module->repeat_counts, module->repeat_counts.size + 1);
    else if (type == SN_CONST)
        sn_vec_reserve(uint32_t, &module->const_word_offsets, module->const_word_offsets.size + 1);
    else if (type == SN_LUT)
        sn_vec_reserve(uint64_t, &module->lut_truths, module->lut_truths.size + 1);
    else if (type == SN_GATE)
        sn_vec_reserve(uint32_t, &module->gate_ids, module->gate_ids.size + 1);

    sn_obj_id_t object = (sn_obj_id_t)module->obj_types.size;
    sn_type_id_t type_id = (sn_type_id_t)objects_of_type->size;
    uint32_t fanin_offset = (uint32_t)module->fanins.size;

    *sn_vec_push(sn_obj_type_t, &module->obj_types) = type;
    *sn_vec_push(uint32_t, &module->width_signed) = sn_pack_width_signed(width, is_signed);
    *sn_vec_push(sn_fanin_count_t, &module->fanin_counts) = (sn_fanin_count_t)fanin_count;
    *sn_vec_push(uint32_t, &module->fanin_offsets) = fanin_offset;
    *sn_vec_push(uint32_t, &module->type_ids) = type_id;
    *sn_vec_push(uint32_t, &module->name_ids) = name;
    *sn_vec_push(sn_obj_id_t, objects_of_type) = object;

    for (uint32_t i = 0; i < fanin_count; i++)
        *sn_vec_push(sn_obj_id_t, &module->fanins) = SN_INVALID_ID;

    if (type == SN_REG_OUT)
    {
        assert(type_id == module->reg_flags.size);
        sn_vec_push(uint32_t, &module->reg_flags);
    }
    else if (type == SN_MEM_OUT)
    {
        assert(type_id == module->mem_depths.size);
        sn_vec_push(uint32_t, &module->mem_depths);
    }
    else if (type == SN_INST)
    {
        assert(type_id == module->inst_modules.size);
        *sn_vec_push(sn_module_id_t, &module->inst_modules) = SN_INVALID_ID;
    }
    else if (type == SN_FAN)
    {
        assert(type_id == module->fan_insts.size);
        *sn_vec_push(sn_obj_id_t, &module->fan_insts) = SN_INVALID_ID;
    }
    else if (type == SN_SLICE)
    {
        assert(type_id == module->slice_infos.size);
        sn_vec_push(sn_slice_info_t, &module->slice_infos);
    }
    else if (type == SN_REPLICATE)
    {
        assert(type_id == module->repeat_counts.size);
        sn_vec_push(uint32_t, &module->repeat_counts);
    }
    else if (type == SN_CONST)
    {
        assert(type_id == module->const_word_offsets.size);
        sn_vec_push(uint32_t, &module->const_word_offsets);
    }
    else if (type == SN_LUT)
    {
        assert(type_id == module->lut_truths.size);
        sn_vec_push(uint64_t, &module->lut_truths);
    }
    else if (type == SN_GATE)
    {
        assert(type_id == module->gate_ids.size);
        sn_vec_push(uint32_t, &module->gate_ids);
    }

    sn_module_invalidate_fanouts(module);
    return object;
}

static inline sn_obj_id_t sn_module_add_named_obj(sn_module_t* module, sn_obj_type_t type, uint32_t width,
                                                  bool is_signed, uint32_t fanin_count, const char* name)
{
    assert(module);
    sn_name_id_t name_id = name ? sn_name_intern(&module->design->names, name) : SN_INVALID_ID;
    return sn_module_add_obj(module, type, width, is_signed, fanin_count, name_id);
}

static inline uint32_t sn_obj_fanin_count(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(object < module->fanin_counts.size);
    return sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object);
}

static inline sn_obj_id_t sn_obj_fanin(const sn_module_t* module, sn_obj_id_t object, uint32_t input_index)
{
    assert(module);
    assert(object < module->fanin_counts.size);
    assert(input_index < sn_obj_fanin_count(module, object));
    uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
    assert((size_t)offset + input_index < module->fanins.size);
    return sn_vec_at(sn_obj_id_t, &module->fanins, offset + input_index);
}

static inline void sn_obj_connect(sn_module_t* module, sn_obj_id_t object, uint32_t input_index, sn_obj_id_t fanin)
{
    assert(module);
    assert(object < module->obj_types.size);
    assert(fanin == SN_INVALID_ID || fanin < module->obj_types.size);
    assert(input_index < sn_obj_fanin_count(module, object));
    uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
    sn_vec_at(sn_obj_id_t, &module->fanins, offset + input_index) = fanin;
    sn_module_invalidate_fanouts(module);
}

static inline void sn_obj_add_fanins(sn_module_t* module, sn_obj_id_t object, uint32_t added_count,
                                     const sn_obj_id_t* added_fanins)
{
    assert(module);
    assert(object < module->obj_types.size);
    assert(added_count == 0 || added_fanins);
    assert(module->fanins.size + added_count <= UINT32_MAX);
    for (uint32_t i = 0; i < added_count; i++)
        assert(added_fanins[i] < module->obj_types.size);
    if (!added_count)
        return;

    uint32_t offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
    uint32_t count = sn_obj_fanin_count(module, object);
    assert(added_count <= UINT16_MAX - count);
    size_t insertion = (size_t)offset + count;
    assert(insertion <= module->fanins.size);

    size_t old_size = module->fanins.size;
    sn_vec_resize(sn_obj_id_t, &module->fanins, old_size + added_count);
    sn_obj_id_t* fanins = sn_vec_data(sn_obj_id_t, &module->fanins);
    memmove(fanins + insertion + added_count, fanins + insertion, (old_size - insertion) * sizeof(*fanins));
    memcpy(fanins + insertion, added_fanins, (size_t)added_count * sizeof(*fanins));
    sn_vec_at(sn_fanin_count_t, &module->fanin_counts, object) = (sn_fanin_count_t)(count + added_count);

    // Preserve fanin-span order for every object after the modified object.
    for (sn_obj_id_t other = object + 1; other < module->obj_types.size; other++)
    {
        uint32_t other_offset = sn_vec_at(uint32_t, &module->fanin_offsets, other);
        if (other_offset >= insertion)
            sn_vec_at(uint32_t, &module->fanin_offsets, other) = other_offset + added_count;
    }
    sn_module_invalidate_fanouts(module);
}

static inline void sn_obj_add_fanin(sn_module_t* module, sn_obj_id_t object, sn_obj_id_t fanin)
{
    sn_obj_add_fanins(module, object, 1, &fanin);
}

static inline sn_obj_id_t sn_module_add_pi(sn_module_t* module, uint32_t width, bool is_signed, const char* name)
{
    assert(module);
    assert(!module->interface_locked);
    return sn_module_add_named_obj(module, SN_PI, width, is_signed, 0, name);
}

static inline sn_obj_id_t sn_module_add_po(sn_module_t* module, uint32_t width, bool is_signed, const char* name,
                                           sn_obj_id_t driver)
{
    assert(module);
    assert(!sn_module_is_blackbox(module));
    assert(!module->interface_locked);
    assert(driver < module->obj_types.size);
    assert(sn_obj_width(module, driver) == width);
    sn_obj_id_t output = sn_module_add_named_obj(module, SN_PO, width, is_signed, 1, name);
    sn_obj_connect(module, output, 0, driver);
    return output;
}

// Adds an output port to an opaque module. Unlike an ordinary SN_PO, whose
// only fanin is its RTL driver, a black-box output deliberately has no driver
// inside SN. Parent insts expose it through their normal SN_INST/SN_FAN
// boundary objects; collapse preserves that boundary and blasting abstracts
// the value as a new combinational input.
static inline sn_obj_id_t sn_module_add_blackbox_po(sn_module_t* module, uint32_t width, bool is_signed,
                                                    const char* name)
{
    assert(module);
    assert(sn_module_is_blackbox(module));
    assert(!module->interface_locked);
    return sn_module_add_named_obj(module, SN_PO, width, is_signed, 1, name);
}

static inline bool sn_obj_fanin_may_be_invalid(const sn_module_t* module, sn_obj_type_t type, uint32_t index)
{
    assert(module);
    if (type == SN_PO)
        return sn_module_is_blackbox(module) && index == 0;
    if (type == SN_REG_OUT)
        return index != SN_REG_DATA;
    if (type == SN_MEM_OUT)
        return index == SN_MEM_INIT_DATA || index == SN_MEM_INIT_MASK;
    if (type == SN_MEM_READ)
        return index == SN_MEM_READ_CLOCK || index == SN_MEM_READ_ENABLE;
    if (type == SN_MEM_WRITE)
        return index == SN_MEM_WRITE_ENABLE;
    return false;
}

static inline bool sn_obj_type_is_operator(sn_obj_type_t type)
{
    return type == SN_BUF || (type >= SN_POS && type < SN_OBJ_TYPE_COUNT);
}

static inline sn_obj_id_t sn_module_add_operator(sn_module_t* module, sn_obj_type_t type, uint32_t width,
                                                 bool is_signed, uint32_t fanin_count, const sn_obj_id_t* fanins,
                                                 const char* name)
{
    assert(sn_obj_type_is_operator(type));
    assert(fanin_count == 0 || fanins);
    sn_obj_id_t object = sn_module_add_named_obj(module, type, width, is_signed, fanin_count, name);
    for (uint32_t i = 0; i < fanin_count; i++)
        sn_obj_connect(module, object, i, fanins[i]);
    return object;
}

static inline sn_obj_id_t sn_module_add_lut(sn_module_t* module, uint32_t fanin_count,
                                            const sn_obj_id_t* fanins, uint64_t truth, const char* name)
{
    assert(module && fanin_count <= 6);
    assert(fanin_count == 0 || fanins);
    for (uint32_t i = 0; i < fanin_count; i++)
        assert(fanins[i] < module->obj_types.size && sn_obj_width(module, fanins[i]) == 1);
    if (fanin_count < 6)
        truth &= (UINT64_C(1) << (UINT32_C(1) << fanin_count)) - 1;
    sn_obj_id_t object = sn_module_add_operator(module, SN_LUT, 1, false, fanin_count, fanins, name);
    sn_vec_at(uint64_t, &module->lut_truths, sn_obj_type_id(module, object)) = truth;
    return object;
}

static inline uint64_t sn_obj_lut_truth(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module && sn_obj_type(module, object) == SN_LUT);
    return sn_vec_at(uint64_t, &module->lut_truths, sn_obj_type_id(module, object));
}

static inline sn_obj_id_t sn_module_add_gate(sn_module_t* module, uint32_t fanin_count,
                                             const sn_obj_id_t* fanins, uint32_t gate_id, const char* name)
{
    assert(module);
    assert(gate_id != SN_INVALID_ID);
    assert(fanin_count == 0 || fanins);
    for (uint32_t i = 0; i < fanin_count; i++)
        assert(fanins[i] < module->obj_types.size && sn_obj_width(module, fanins[i]) == 1);
    sn_obj_id_t object = sn_module_add_operator(module, SN_GATE, 1, false, fanin_count, fanins, name);
    sn_vec_at(uint32_t, &module->gate_ids, sn_obj_type_id(module, object)) = gate_id;
    return object;
}

static inline uint32_t sn_obj_gate_id(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module && sn_obj_type(module, object) == SN_GATE);
    return sn_vec_at(uint32_t, &module->gate_ids, sn_obj_type_id(module, object));
}

static inline sn_obj_id_t sn_module_add_mux(sn_module_t* module, sn_obj_id_t select, sn_obj_id_t selected,
                                            sn_obj_id_t default_value, const char* name)
{
    assert(module);
    assert(select < module->obj_types.size);
    assert(selected < module->obj_types.size);
    assert(default_value < module->obj_types.size);
    assert(sn_obj_width(module, select) == 1);
    assert(sn_obj_width(module, selected) == sn_obj_width(module, default_value));
    sn_obj_id_t fanins[SN_MUX_FANIN_COUNT] = {select, selected, default_value};
    return sn_module_add_operator(module, SN_MUX, sn_obj_width(module, default_value),
                                  sn_obj_is_signed(module, default_value), SN_MUX_FANIN_COUNT, fanins, name);
}

static inline sn_obj_id_t sn_module_add_bmux(sn_module_t* module, sn_obj_id_t select, sn_obj_id_t packed_alternatives,
                                             uint32_t output_width, bool is_signed, const char* name)
{
    assert(module);
    assert(select < module->obj_types.size);
    assert(packed_alternatives < module->obj_types.size);
    assert(output_width);
    uint32_t select_width = sn_obj_width(module, select);
    assert(select_width < 31);
    uint64_t packed_width = (uint64_t)output_width << select_width;
    assert(packed_width <= UINT32_MAX >> 1);
    assert(sn_obj_width(module, packed_alternatives) == packed_width);
    (void)packed_width;
    sn_obj_id_t fanins[SN_BMUX_FANIN_COUNT] = {select, packed_alternatives};
    return sn_module_add_operator(module, SN_BMUX, output_width, is_signed, SN_BMUX_FANIN_COUNT, fanins, name);
}

static inline sn_obj_id_t sn_module_add_pmux(sn_module_t* module, sn_obj_id_t select, sn_obj_id_t packed_alternatives,
                                             sn_obj_id_t default_value, const char* name)
{
    assert(module);
    assert(select < module->obj_types.size);
    assert(packed_alternatives < module->obj_types.size);
    assert(default_value < module->obj_types.size);
    uint32_t select_width = sn_obj_width(module, select);
    uint32_t output_width = sn_obj_width(module, default_value);
    assert(select_width);
    assert(output_width);
    uint64_t packed_width = (uint64_t)output_width * select_width;
    assert(packed_width <= UINT32_MAX >> 1);
    assert(sn_obj_width(module, packed_alternatives) == packed_width);
    (void)packed_width;
    sn_obj_id_t fanins[SN_PMUX_FANIN_COUNT] = {select, packed_alternatives, default_value};
    return sn_module_add_operator(module, SN_PMUX, output_width, sn_obj_is_signed(module, default_value),
                                  SN_PMUX_FANIN_COUNT, fanins, name);
}

static inline uint32_t sn_const_word_count(uint32_t width)
{
    assert(width);
    return (width + 31u) / 32u;
}

static inline uint64_t sn_const_hash_words(uint32_t width, bool is_signed, const uint32_t* words)
{
    uint64_t hash = UINT64_C(1469598103934665603);
    hash = (hash ^ width) * UINT64_C(1099511628211);
    hash = (hash ^ (is_signed ? 1u : 0u)) * UINT64_C(1099511628211);
    for (uint32_t i = 0; i < sn_const_word_count(width); i++)
        hash = (hash ^ words[i]) * UINT64_C(1099511628211);
    return hash;
}

static inline uint64_t sn_const_object_hash(const sn_module_t* module, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    uint32_t width = sn_obj_width(module, object);
    uint64_t hash = UINT64_C(1469598103934665603);
    hash = (hash ^ width) * UINT64_C(1099511628211);
    hash = (hash ^ (sn_obj_is_signed(module, object) ? 1u : 0u)) * UINT64_C(1099511628211);
    const uint32_t* words = NULL;
    if (type == SN_CONST)
    {
        uint32_t type_id = sn_obj_type_id(module, object);
        uint32_t offset = sn_vec_at(uint32_t, &module->const_word_offsets, type_id);
        words = &sn_vec_at(uint32_t, &module->design->constant_words, offset);
    }
    for (uint32_t i = 0; i < sn_const_word_count(width); i++)
    {
        uint32_t word = type == SN_CONST0 ? 0 : type == SN_CONST1 ? (i == 0 ? 1u : 0u) : words[i];
        hash = (hash ^ word) * UINT64_C(1099511628211);
    }
    return hash;
}

static inline void sn_const_cache_rehash(sn_module_t* module, size_t bucket_count)
{
    assert(module && bucket_count >= 64 && (bucket_count & (bucket_count - 1)) == 0);
    sn_vec_t buckets;
    sn_vec_init(&buckets);
    sn_vec_resize(uint32_t, &buckets, bucket_count);
    for (size_t i = 0; i < bucket_count; i++)
        sn_vec_at(uint32_t, &buckets, i) = SN_INVALID_ID;
    for (size_t i = 0; i < module->const_hash_entries.size; i++)
    {
        sn_const_hash_entry_t* entry = &sn_vec_at(sn_const_hash_entry_t, &module->const_hash_entries, i);
        size_t bucket = (size_t)entry->hash & (bucket_count - 1);
        entry->next = sn_vec_at(uint32_t, &buckets, bucket);
        sn_vec_at(uint32_t, &buckets, bucket) = (uint32_t)i;
    }
    sn_vec_destroy(&module->const_hash_buckets);
    module->const_hash_buckets = buckets;
}

static inline void sn_const_cache_insert(sn_module_t* module, sn_obj_id_t object, uint64_t hash)
{
    if ((module->const_hash_entries.size + 1) * 4 >= module->const_hash_buckets.size * 3)
        sn_const_cache_rehash(module, module->const_hash_buckets.size * 2);
    assert(module->const_hash_entries.size < SN_INVALID_ID);
    size_t bucket = (size_t)hash & (module->const_hash_buckets.size - 1);
    sn_const_hash_entry_t* entry = sn_vec_push(sn_const_hash_entry_t, &module->const_hash_entries);
    entry->hash = hash;
    entry->object = object;
    entry->next = sn_vec_at(uint32_t, &module->const_hash_buckets, bucket);
    sn_vec_at(uint32_t, &module->const_hash_buckets, bucket) = (uint32_t)(module->const_hash_entries.size - 1);
}

static inline void sn_const_cache_ensure(sn_module_t* module)
{
    if (module->const_hash_buckets.size)
        return;
    sn_const_cache_rehash(module, 64);
    for (sn_obj_id_t object = 0; object < module->obj_types.size; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if ((type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST) &&
            sn_obj_name_id(module, object) == SN_INVALID_ID)
            sn_const_cache_insert(module, object, sn_const_object_hash(module, object));
    }
}

static inline bool sn_const_object_equal(const sn_module_t* module, sn_obj_id_t object, sn_obj_type_t type,
                                         uint32_t width, bool is_signed, const uint32_t* words)
{
    if (sn_obj_type(module, object) != type || sn_obj_width(module, object) != width ||
        sn_obj_is_signed(module, object) != is_signed)
        return false;
    if (type != SN_CONST)
        return true;
    uint32_t type_id = sn_obj_type_id(module, object);
    uint32_t offset = sn_vec_at(uint32_t, &module->const_word_offsets, type_id);
    const uint32_t* existing = &sn_vec_at(uint32_t, &module->design->constant_words, offset);
    return memcmp(existing, words, (size_t)sn_const_word_count(width) * sizeof(uint32_t)) == 0;
}

static inline sn_obj_id_t sn_module_add_const(sn_module_t* module, uint32_t width, bool is_signed,
                                              const uint32_t* words, const char* name)
{
    assert(module);
    assert(width);
    assert(words);
    uint32_t word_count = sn_const_word_count(width);
    uint32_t final_bits = width & 31u;
    if (final_bits)
        assert((words[word_count - 1] >> final_bits) == 0);

    bool is_zero = true;
    bool is_one = words[0] == 1;
    for (uint32_t i = 0; i < word_count; i++)
    {
        is_zero = is_zero && words[i] == 0;
        if (i != 0)
            is_one = is_one && words[i] == 0;
    }

    sn_obj_type_t type = is_zero ? SN_CONST0 : (is_one ? SN_CONST1 : SN_CONST);
    uint64_t hash = sn_const_hash_words(width, is_signed, words);
    if (!name)
    {
        sn_const_cache_ensure(module);
        size_t bucket = (size_t)hash & (module->const_hash_buckets.size - 1);
        uint32_t entry_id = sn_vec_at(uint32_t, &module->const_hash_buckets, bucket);
        while (entry_id != SN_INVALID_ID)
        {
            const sn_const_hash_entry_t* entry =
                &sn_vec_at(sn_const_hash_entry_t, &module->const_hash_entries, entry_id);
            if (entry->hash == hash &&
                sn_const_object_equal(module, entry->object, type, width, is_signed, words))
                return entry->object;
            entry_id = entry->next;
        }
    }
    sn_obj_id_t object = sn_module_add_named_obj(module, type, width, is_signed, 0, name);
    if (type == SN_CONST)
    {
        assert(module->design->constant_words.size + word_count <= UINT32_MAX);
        uint32_t offset = (uint32_t)module->design->constant_words.size;
        for (uint32_t i = 0; i < word_count; i++)
            *sn_vec_push(uint32_t, &module->design->constant_words) = words[i];
        sn_vec_at(uint32_t, &module->const_word_offsets, sn_obj_type_id(module, object)) = offset;
    }
    if (!name)
        sn_const_cache_insert(module, object, hash);
    return object;
}

static inline const uint32_t* sn_const_words(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(sn_obj_type(module, object) == SN_CONST);
    uint32_t word_offset = sn_vec_at(uint32_t, &module->const_word_offsets, sn_obj_type_id(module, object));
    assert(word_offset + sn_const_word_count(sn_obj_width(module, object)) <= module->design->constant_words.size);
    return &sn_vec_at(uint32_t, &module->design->constant_words, word_offset);
}

static inline sn_obj_id_t sn_module_add_concat(sn_module_t* module, uint32_t fanin_count, const sn_obj_id_t* fanins,
                                               const char* name)
{
    // fanins[0] contributes the least-significant result bits.
    assert(fanin_count);
    assert(fanins);
    uint64_t width = 0;
    bool all_constant = true;
    for (uint32_t i = 0; i < fanin_count; i++)
    {
        assert(fanins[i] < module->obj_types.size);
        width += sn_obj_width(module, fanins[i]);
        sn_obj_type_t type = sn_obj_type(module, fanins[i]);
        all_constant = all_constant && (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
    }
    assert(width <= UINT32_MAX >> 1);
    if (all_constant)
    {
        uint32_t result_width = (uint32_t)width;
        uint32_t* words = (uint32_t*)calloc(sn_const_word_count(result_width), sizeof(uint32_t));
        assert(words);
        uint32_t offset = 0;
        for (uint32_t i = 0; i < fanin_count; i++)
        {
            sn_obj_id_t fanin = fanins[i];
            sn_obj_type_t type = sn_obj_type(module, fanin);
            uint32_t fanin_width = sn_obj_width(module, fanin);
            const uint32_t* source = type == SN_CONST ? sn_const_words(module, fanin) : NULL;
            for (uint32_t bit = 0; bit < fanin_width; bit++)
            {
                bool value = type == SN_CONST1 ? bit == 0
                                               : type == SN_CONST && ((source[bit >> 5] >> (bit & 31)) & 1u);
                if (value)
                    words[(offset + bit) >> 5] |= 1u << ((offset + bit) & 31);
            }
            offset += fanin_width;
        }
        assert(offset == result_width);
        sn_obj_id_t result = sn_module_add_const(module, result_width, false, words, name);
        free(words);
        return result;
    }
    if (fanin_count > UINT16_MAX)
    {
        uint32_t chunk_count = 1 + (fanin_count - 1) / UINT16_MAX;
        sn_obj_id_t* chunks = (sn_obj_id_t*)malloc((size_t)chunk_count * sizeof(sn_obj_id_t));
        assert(chunks);
        for (uint32_t chunk = 0; chunk < chunk_count; chunk++)
        {
            uint32_t offset = chunk * UINT16_MAX;
            uint32_t count = fanin_count - offset < UINT16_MAX ? fanin_count - offset : UINT16_MAX;
            chunks[chunk] = sn_module_add_concat(module, count, fanins + offset, NULL);
        }
        sn_obj_id_t result = sn_module_add_concat(module, chunk_count, chunks, name);
        free(chunks);
        return result;
    }
    return sn_module_add_operator(module, SN_CONCAT, (uint32_t)width, false, fanin_count, fanins, name);
}

static inline sn_obj_id_t sn_module_add_repeat(sn_module_t* module, sn_obj_id_t value, uint32_t count, const char* name)
{
    assert(module);
    assert(value < module->obj_types.size);
    assert(count);
    uint64_t width = (uint64_t)sn_obj_width(module, value) * count;
    assert(width <= UINT32_MAX >> 1);
    sn_obj_id_t object = sn_module_add_named_obj(module, SN_REPLICATE, (uint32_t)width, false, 1, name);
    sn_obj_connect(module, object, 0, value);
    sn_vec_at(uint32_t, &module->repeat_counts, sn_obj_type_id(module, object)) = count;
    return object;
}

static inline uint32_t sn_obj_repeat_count(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(sn_obj_type(module, object) == SN_REPLICATE);
    return sn_vec_at(uint32_t, &module->repeat_counts, sn_obj_type_id(module, object));
}

static inline sn_obj_id_t sn_module_add_slice(sn_module_t* module, sn_obj_id_t value, int32_t left_index,
                                              int32_t right_index, const char* name)
{
    assert(module);
    assert(value < module->obj_types.size);
    assert(left_index >= 0 && (uint32_t)left_index < sn_obj_width(module, value));
    assert(right_index >= 0 && (uint32_t)right_index < sn_obj_width(module, value));
    int64_t difference = (int64_t)left_index - (int64_t)right_index;
    uint64_t width = (uint64_t)(difference < 0 ? -difference : difference) + 1;
    assert(width <= UINT32_MAX >> 1);
    sn_obj_id_t object = sn_module_add_named_obj(module, SN_SLICE, (uint32_t)width, false, 1, name);
    sn_obj_connect(module, object, 0, value);
    sn_slice_info_t* info = &sn_vec_at(sn_slice_info_t, &module->slice_infos, sn_obj_type_id(module, object));
    info->left_index = left_index;
    info->right_index = right_index;
    info->flags = left_index >= right_index ? SN_SLICE_DESCENDING : 0;
    return object;
}

static inline const sn_slice_info_t* sn_obj_slice_info(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(sn_obj_type(module, object) == SN_SLICE);
    return &sn_vec_at(sn_slice_info_t, &module->slice_infos, sn_obj_type_id(module, object));
}

static inline sn_obj_id_t sn_obj_pair_in(const sn_module_t* module, sn_obj_id_t out)
{
    assert(module);
    sn_obj_type_t out_type = sn_obj_type(module, out);
    sn_obj_type_t in_type = SN_NONE;
    if (out_type == SN_REG_OUT)
        in_type = SN_REG_IN;
    else if (out_type == SN_MEM_OUT)
        in_type = SN_MEM_IN;
    else if (out_type == SN_LOOP_OUT)
        in_type = SN_LOOP_IN;
    else
        assert(false);

    sn_type_id_t pair_id = sn_obj_type_id(module, out);
    assert(pair_id < module->type_objects[in_type].size);
    sn_obj_id_t in = sn_vec_at(sn_obj_id_t, &module->type_objects[in_type], pair_id);
    assert(sn_obj_type_id(module, in) == pair_id);
    return in;
}

static inline sn_obj_id_t sn_obj_pair_out(const sn_module_t* module, sn_obj_id_t in)
{
    assert(module);
    sn_obj_type_t in_type = sn_obj_type(module, in);
    sn_obj_type_t out_type = SN_NONE;
    if (in_type == SN_REG_IN)
        out_type = SN_REG_OUT;
    else if (in_type == SN_MEM_IN)
        out_type = SN_MEM_OUT;
    else if (in_type == SN_LOOP_IN)
        out_type = SN_LOOP_OUT;
    else
        assert(false);

    sn_type_id_t pair_id = sn_obj_type_id(module, in);
    assert(pair_id < module->type_objects[out_type].size);
    sn_obj_id_t out = sn_vec_at(sn_obj_id_t, &module->type_objects[out_type], pair_id);
    assert(sn_obj_type_id(module, out) == pair_id);
    return out;
}

static inline sn_obj_pair_t sn_module_add_pair(sn_module_t* module, sn_obj_type_t out_type, sn_obj_type_t in_type,
                                               uint32_t width, bool is_signed, const char* out_name,
                                               const char* in_name)
{
    assert(module);
    assert((out_type == SN_REG_OUT && in_type == SN_REG_IN) || (out_type == SN_MEM_OUT && in_type == SN_MEM_IN) ||
           (out_type == SN_LOOP_OUT && in_type == SN_LOOP_IN));
    assert(module->type_objects[out_type].size == module->type_objects[in_type].size);

    uint32_t out_fanin_count = out_type == SN_REG_OUT     ? SN_REG_FANIN_COUNT
                               : out_type == SN_MEM_OUT   ? SN_MEM_OUT_FANIN_COUNT
                                                         : 1;
    uint32_t in_fanin_count = in_type == SN_MEM_IN ? 0 : 1;

    sn_obj_pair_t pair;
    pair.out = sn_module_add_named_obj(module, out_type, width, is_signed, out_fanin_count, out_name);
    pair.in = sn_module_add_named_obj(module, in_type, width, is_signed, in_fanin_count, in_name);
    assert(sn_obj_type_id(module, pair.out) == sn_obj_type_id(module, pair.in));
    assert(pair.in == pair.out + 1);
    assert(sn_obj_pair_in(module, pair.out) == pair.in);
    assert(sn_obj_pair_out(module, pair.in) == pair.out);
    uint32_t pair_slot = out_type == SN_REG_OUT ? SN_REG_DATA
                         : out_type == SN_MEM_OUT ? SN_MEM_STATE
                                                   : 0;
    sn_obj_connect(module, pair.out, pair_slot, pair.in);
    return pair;
}

static inline sn_obj_pair_t sn_module_add_reg_pair(sn_module_t* module, uint32_t width, bool is_signed,
                                                   const char* out_name, const char* in_name, sn_obj_id_t clock)
{
    assert(clock == SN_INVALID_ID || clock < module->obj_types.size);
    sn_obj_pair_t pair = sn_module_add_pair(module, SN_REG_OUT, SN_REG_IN, width, is_signed, out_name, in_name);
    sn_obj_connect(module, pair.out, SN_REG_CLOCK, clock);
    return pair;
}

static inline uint32_t sn_obj_reg_flags(const sn_module_t* module, sn_obj_id_t reg_out)
{
    assert(module);
    assert(sn_obj_type(module, reg_out) == SN_REG_OUT);
    return sn_vec_at(uint32_t, &module->reg_flags, sn_obj_type_id(module, reg_out));
}

static inline void sn_reg_set_flags(sn_module_t* module, sn_obj_id_t reg_out, uint32_t flags)
{
    assert(module);
    assert(sn_obj_type(module, reg_out) == SN_REG_OUT);
    assert((flags & ~SN_REG_FLAGS_ALL) == 0);
    sn_vec_at(uint32_t, &module->reg_flags, sn_obj_type_id(module, reg_out)) = flags;
}

static inline void sn_reg_set_fanin(sn_module_t* module, sn_obj_id_t reg_out, sn_reg_fanin_t slot, sn_obj_id_t fanin)
{
    assert(module);
    assert(sn_obj_type(module, reg_out) == SN_REG_OUT);
    assert(slot < SN_REG_FANIN_COUNT);
    assert(slot != SN_REG_DATA);
    if ((slot == SN_REG_INIT_DATA || slot == SN_REG_INIT_MASK) && fanin != SN_INVALID_ID)
    {
        sn_obj_type_t type = sn_obj_type(module, fanin);
        assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
        assert(sn_obj_width(module, fanin) == sn_obj_width(module, reg_out));
        (void)type;
    }
    sn_obj_connect(module, reg_out, (uint32_t)slot, fanin);
}

// Register initialization uses the same aligned representation as memory
// initialization: mask bit i describes data bit i, and a set mask bit means
// that the corresponding data bit is initialized. No data means no init; data
// with no mask means all bits valid. Builders normally provide both constants.
static inline void sn_reg_set_init(sn_module_t* module, sn_obj_id_t reg_out, sn_obj_id_t data, sn_obj_id_t mask)
{
    assert(data != SN_INVALID_ID || mask == SN_INVALID_ID);
    sn_reg_set_fanin(module, reg_out, SN_REG_INIT_DATA, data);
    sn_reg_set_fanin(module, reg_out, SN_REG_INIT_MASK, mask);
}

static inline sn_obj_id_t sn_obj_reg_init_data(const sn_module_t* module, sn_obj_id_t reg_out)
{
    assert(module && sn_obj_type(module, reg_out) == SN_REG_OUT);
    return sn_obj_fanin(module, reg_out, SN_REG_INIT_DATA);
}

static inline sn_obj_id_t sn_obj_reg_init_mask(const sn_module_t* module, sn_obj_id_t reg_out)
{
    assert(module && sn_obj_type(module, reg_out) == SN_REG_OUT);
    return sn_obj_fanin(module, reg_out, SN_REG_INIT_MASK);
}

static inline sn_obj_pair_t sn_module_add_mem_pair(sn_module_t* module, uint32_t width, bool is_signed, uint32_t depth,
                                                   const char* out_name, const char* in_name)
{
    assert(depth);
    sn_obj_pair_t pair = sn_module_add_pair(module, SN_MEM_OUT, SN_MEM_IN, width, is_signed, out_name, in_name);
    sn_vec_at(uint32_t, &module->mem_depths, sn_obj_type_id(module, pair.out)) = depth;
    return pair;
}

static inline uint32_t sn_obj_mem_depth(const sn_module_t* module, sn_obj_id_t mem_out)
{
    assert(module);
    assert(sn_obj_type(module, mem_out) == SN_MEM_OUT);
    uint32_t depth = sn_vec_at(uint32_t, &module->mem_depths, sn_obj_type_id(module, mem_out));
    assert(depth);
    return depth;
}

static inline uint32_t sn_obj_mem_init_width(const sn_module_t* module, sn_obj_id_t mem_out)
{
    assert(module);
    assert(sn_obj_type(module, mem_out) == SN_MEM_OUT);
    uint64_t width = (uint64_t)sn_obj_width(module, mem_out) * sn_obj_mem_depth(module, mem_out);
    assert(width <= UINT32_MAX);
    return (uint32_t)width;
}

static inline void sn_mem_set_init(sn_module_t* module, sn_obj_id_t mem_out, sn_obj_id_t data, sn_obj_id_t mask)
{
    assert(module);
    assert(sn_obj_type(module, mem_out) == SN_MEM_OUT);
    assert(data != SN_INVALID_ID || mask == SN_INVALID_ID);
    uint32_t init_width = sn_obj_mem_init_width(module, mem_out);
    if (data != SN_INVALID_ID)
    {
        sn_obj_type_t type = sn_obj_type(module, data);
        assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
        assert(sn_obj_width(module, data) == init_width);
    }
    if (mask != SN_INVALID_ID)
    {
        sn_obj_type_t type = sn_obj_type(module, mask);
        assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
        assert(sn_obj_width(module, mask) == init_width);
    }
    sn_obj_connect(module, mem_out, SN_MEM_INIT_DATA, data);
    sn_obj_connect(module, mem_out, SN_MEM_INIT_MASK, mask);
}

static inline sn_obj_id_t sn_obj_mem_init_data(const sn_module_t* module, sn_obj_id_t mem_out)
{
    assert(module);
    assert(sn_obj_type(module, mem_out) == SN_MEM_OUT);
    return sn_obj_fanin(module, mem_out, SN_MEM_INIT_DATA);
}

static inline sn_obj_id_t sn_obj_mem_init_mask(const sn_module_t* module, sn_obj_id_t mem_out)
{
    assert(module);
    assert(sn_obj_type(module, mem_out) == SN_MEM_OUT);
    return sn_obj_fanin(module, mem_out, SN_MEM_INIT_MASK);
}

static inline sn_obj_id_t sn_module_add_mem_read(sn_module_t* module, sn_obj_id_t mem_out, sn_obj_id_t clock,
                                                 sn_obj_id_t enable, sn_obj_id_t address, const char* name)
{
    assert(module);
    assert(sn_obj_type(module, mem_out) == SN_MEM_OUT);
    assert(clock == SN_INVALID_ID || clock < module->obj_types.size);
    assert(enable == SN_INVALID_ID || enable < module->obj_types.size);
    assert(clock != SN_INVALID_ID || enable == SN_INVALID_ID);
    assert(address < module->obj_types.size);
    sn_obj_id_t read = sn_module_add_named_obj(module, SN_MEM_READ, sn_obj_width(module, mem_out),
                                               sn_obj_is_signed(module, mem_out), SN_MEM_READ_FANIN_COUNT, name);
    sn_obj_connect(module, read, SN_MEM_READ_MEMORY, mem_out);
    sn_obj_connect(module, read, SN_MEM_READ_CLOCK, clock);
    sn_obj_connect(module, read, SN_MEM_READ_ENABLE, enable);
    sn_obj_connect(module, read, SN_MEM_READ_ADDRESS, address);
    return read;
}

static inline sn_obj_id_t sn_module_add_mem_write_unlinked(sn_module_t* module, sn_obj_id_t mem_in,
                                                           sn_obj_id_t clock, sn_obj_id_t enable,
                                                           sn_obj_id_t data, sn_obj_id_t address,
                                                           const char* name)
{
    assert(module);
    assert(sn_obj_type(module, mem_in) == SN_MEM_IN);
    assert(clock < module->obj_types.size);
    assert(enable == SN_INVALID_ID || enable < module->obj_types.size);
    assert(data < module->obj_types.size);
    assert(address < module->obj_types.size);
    assert(sn_obj_width(module, data) == sn_obj_width(module, mem_in));
    sn_obj_id_t write = sn_module_add_named_obj(module, SN_MEM_WRITE, sn_obj_width(module, mem_in),
                                                sn_obj_is_signed(module, mem_in), SN_MEM_WRITE_FANIN_COUNT, name);
    sn_obj_connect(module, write, SN_MEM_WRITE_CLOCK, clock);
    sn_obj_connect(module, write, SN_MEM_WRITE_ENABLE, enable);
    sn_obj_connect(module, write, SN_MEM_WRITE_DATA, data);
    sn_obj_connect(module, write, SN_MEM_WRITE_ADDRESS, address);
    return write;
}

static inline sn_obj_id_t sn_module_add_mem_write(sn_module_t* module, sn_obj_id_t mem_in, sn_obj_id_t clock,
                                                  sn_obj_id_t enable, sn_obj_id_t data, sn_obj_id_t address,
                                                  const char* name)
{
    sn_obj_id_t write = sn_module_add_mem_write_unlinked(module, mem_in, clock, enable, data, address, name);
    sn_obj_add_fanin(module, mem_in, write);
    return write;
}

static inline sn_obj_pair_t sn_module_add_loop_pair(sn_module_t* module, uint32_t width, bool is_signed,
                                                    const char* out_name, const char* in_name)
{
    return sn_module_add_pair(module, SN_LOOP_OUT, SN_LOOP_IN, width, is_signed, out_name, in_name);
}

static inline sn_obj_id_t sn_module_add_inst(sn_module_t* module, sn_module_id_t referenced_module,
                                                 uint32_t input_count, const sn_obj_id_t* inputs, const char* name,
                                                 const char* const* output_names)
{
    assert(module);
    assert(referenced_module < module->design->modules.size);
    assert(input_count == 0 || inputs);
    sn_module_t* child = sn_design_get_module(module->design, referenced_module);
    assert(child->type_objects[SN_PI].size == input_count);
    uint32_t output_count = sn_design_module_output_count(module->design, referenced_module);
    assert(output_count != 0);
    child->interface_locked = true;

    sn_obj_id_t first_output = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], 0);
    uint32_t inst_width = output_count == 1 ? sn_obj_width(child, first_output) : 0;
    bool inst_signedness = output_count == 1 ? sn_obj_is_signed(child, first_output) : false;
    sn_obj_id_t inst =
        sn_module_add_named_obj(module, SN_INST, inst_width, inst_signedness, input_count, name);
    for (uint32_t i = 0; i < input_count; i++)
        sn_obj_connect(module, inst, i, inputs[i]);

    sn_vec_at(sn_module_id_t, &module->inst_modules, sn_obj_type_id(module, inst)) = referenced_module;

    // A one-output inst is itself the output value. Multi-output insts
    // are followed immediately by one SN_FAN per output.
    if (output_count > 1)
    {
        for (uint32_t i = 0; i < output_count; i++)
        {
            sn_obj_id_t child_output = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], i);
            const char* output_name = output_names ? output_names[i] : NULL;
            sn_obj_id_t fan = sn_module_add_named_obj(module, SN_FAN, sn_obj_width(child, child_output),
                                                      sn_obj_is_signed(child, child_output), 1, output_name);
            assert(fan == inst + 1 + i);
            sn_obj_connect(module, fan, 0, inst);
            sn_vec_at(sn_obj_id_t, &module->fan_insts, sn_obj_type_id(module, fan)) = inst;
        }
    }
    return inst;
}

static inline sn_module_id_t sn_inst_module_id(const sn_module_t* module, sn_obj_id_t inst)
{
    assert(module);
    assert(sn_obj_type(module, inst) == SN_INST);
    sn_module_id_t module_id = sn_vec_at(sn_module_id_t, &module->inst_modules, sn_obj_type_id(module, inst));
    assert(module_id < module->design->modules.size);
    return module_id;
}

static inline sn_obj_id_t sn_fan_inst_id(const sn_module_t* module, sn_obj_id_t fan)
{
    assert(module);
    assert(sn_obj_type(module, fan) == SN_FAN);
    sn_obj_id_t inst = sn_vec_at(sn_obj_id_t, &module->fan_insts, sn_obj_type_id(module, fan));
    assert(inst < fan);
    assert(sn_obj_type(module, inst) == SN_INST);
    assert(sn_obj_fanin_count(module, fan) == 1);
    assert(sn_obj_fanin(module, fan, 0) == inst);
    return inst;
}

static inline uint32_t sn_fan_output_index(const sn_module_t* module, sn_obj_id_t fan)
{
    sn_obj_id_t inst = sn_fan_inst_id(module, fan);
    uint32_t output_index = fan - inst - 1;
    sn_module_id_t child_id = sn_inst_module_id(module, inst);
    assert(output_index < sn_design_module_output_count(module->design, child_id));
    (void)child_id;
    return output_index;
}

static inline sn_obj_id_t sn_inst_output(const sn_module_t* module, sn_obj_id_t inst, uint32_t output_index)
{
    assert(module);
    assert(sn_obj_type(module, inst) == SN_INST);
    sn_module_id_t child_id = sn_inst_module_id(module, inst);
    uint32_t output_count = sn_design_module_output_count(module->design, child_id);
    assert(output_index < output_count);
    if (output_count == 1)
        return inst;

    sn_obj_id_t fan = inst + 1 + output_index;
    assert(fan < module->obj_types.size);
    assert(sn_obj_type(module, fan) == SN_FAN);
    assert(sn_obj_fanin(module, fan, 0) == inst);
    assert(sn_fan_inst_id(module, fan) == inst);
    assert(sn_fan_output_index(module, fan) == output_index);
    return fan;
}

// Print the elaborated module-inst hierarchy rooted at module_id. Children
// follow the natural SN_INST order of their parent module. A module is
// printed once per inst, so repeated insts remain visible. Recursive
// instantiation is invalid for synthesis, but is marked and stopped rather
// than causing unbounded recursion in this diagnostic routine.
static inline void sn_design_print_hierarchy_rec(FILE* out, const sn_design_t* design, sn_module_id_t module_id,
                                                 size_t depth, bool is_last, bool* ancestor_has_next,
                                                 bool* active_modules)
{
    assert(out);
    assert(design);
    assert(module_id < design->modules.size);
    assert(ancestor_has_next);
    assert(active_modules);

    if (depth)
    {
        for (size_t level = 0; level + 1 < depth; level++)
            fputs(ancestor_has_next[level] ? "│  " : "   ", out);
        fputs(is_last ? "└─ " : "├─ ", out);
    }

    const sn_module_t* module = sn_design_get_module_const(design, module_id);
    fputs(sn_name_get(&design->names, module->name), out);
    if (active_modules[module_id])
    {
        fputs(" [recursive]\n", out);
        return;
    }
    if (sn_module_is_blackbox(module))
    {
        fputs(" [blackbox]\n", out);
        return;
    }
    fputc('\n', out);

    active_modules[module_id] = true;
    size_t inst_count = module->type_objects[SN_INST].size;
    for (size_t i = 0; i < inst_count; i++)
    {
        sn_obj_id_t inst = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], i);
        ancestor_has_next[depth] = i + 1 < inst_count;
        sn_design_print_hierarchy_rec(out, design, sn_inst_module_id(module, inst), depth + 1,
                                      i + 1 == inst_count, ancestor_has_next, active_modules);
    }
    active_modules[module_id] = false;
}

static inline void sn_design_print_hierarchy(FILE* out, const sn_design_t* design, sn_module_id_t top_module_id)
{
    assert(out);
    assert(design);
    assert(top_module_id < design->modules.size);

    bool* ancestor_has_next = (bool*)calloc(design->modules.size, sizeof(bool));
    bool* active_modules = (bool*)calloc(design->modules.size, sizeof(bool));
    assert(ancestor_has_next);
    assert(active_modules);
    sn_design_print_hierarchy_rec(out, design, top_module_id, 0, true, ancestor_has_next, active_modules);
    free(active_modules);
    free(ancestor_has_next);
}

static inline void sn_module_build_fanouts(sn_module_t* module)
{
    assert(module);
    size_t object_count = module->obj_types.size;
    sn_vec_resize(uint32_t, &module->fanout_counts, object_count);
    sn_vec_resize(uint32_t, &module->fanout_offsets, object_count);
    memset(module->fanout_counts.data, 0, object_count * sizeof(uint32_t));

    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        uint32_t count = sn_obj_fanin_count(module, object);
        for (uint32_t i = 0; i < count; i++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, object, i);
            if (fanin == SN_INVALID_ID)
                continue;
            assert(fanin < object_count);
            uint32_t* fanout_count = &sn_vec_at(uint32_t, &module->fanout_counts, fanin);
            assert(*fanout_count < UINT32_MAX);
            (*fanout_count)++;
        }
    }

    uint32_t total = 0;
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_vec_at(uint32_t, &module->fanout_offsets, object) = total;
        uint32_t count = sn_vec_at(uint32_t, &module->fanout_counts, object);
        assert(total <= UINT32_MAX - count);
        total += count;
    }
    sn_vec_resize(sn_obj_id_t, &module->fanouts, total);

    uint32_t* cursor = (uint32_t*)calloc(object_count ? object_count : 1, sizeof(uint32_t));
    assert(cursor);
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        uint32_t count = sn_obj_fanin_count(module, object);
        for (uint32_t i = 0; i < count; i++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, object, i);
            if (fanin == SN_INVALID_ID)
                continue;
            uint32_t offset = sn_vec_at(uint32_t, &module->fanout_offsets, fanin);
            assert(cursor[fanin] < sn_vec_at(uint32_t, &module->fanout_counts, fanin));
            sn_vec_at(sn_obj_id_t, &module->fanouts, offset + cursor[fanin]++) = object;
        }
    }
    free(cursor);
    module->fanouts_valid = true;
}

static inline uint32_t sn_obj_fanout_count(const sn_module_t* module, sn_obj_id_t object)
{
    assert(module);
    assert(module->fanouts_valid);
    assert(object < module->fanout_counts.size);
    return sn_vec_at(uint32_t, &module->fanout_counts, object);
}

static inline sn_obj_id_t sn_obj_fanout(const sn_module_t* module, sn_obj_id_t object, uint32_t output_index)
{
    assert(module);
    assert(module->fanouts_valid);
    assert(output_index < sn_obj_fanout_count(module, object));
    uint32_t offset = sn_vec_at(uint32_t, &module->fanout_offsets, object);
    return sn_vec_at(sn_obj_id_t, &module->fanouts, offset + output_index);
}

// Sequential topological traversal treats state OUT objects as sources and
// emits all of them immediately after the PIs. Their paired IN objects remain
// ordinary sinks: each IN follows the OUT, the OUT's non-pair control fanins,
// and its own functional fanins. Pre-emitting every OUT is important when an
// OUT is first discovered from inside its own next-state cone.
enum
{
    SN_TOPO_UNSEEN = 0,
    SN_TOPO_VISITING,
    SN_TOPO_DONE
};

typedef struct sn_topo_context_t
{
    const sn_module_t* module;
    sn_vec_t* order;
    uint8_t* marks;
} sn_topo_context_t;

typedef struct sn_topo_frame_t
{
    sn_obj_id_t object;
    uint32_t index;
    uint8_t phase;
} sn_topo_frame_t;

static inline bool sn_obj_type_is_pair_out(sn_obj_type_t type)
{
    return type == SN_REG_OUT || type == SN_MEM_OUT || type == SN_LOOP_OUT;
}

static inline bool sn_obj_type_is_pair_in(sn_obj_type_t type)
{
    return type == SN_REG_IN || type == SN_MEM_IN || type == SN_LOOP_IN;
}

static inline void sn_module_topo_push(sn_topo_context_t* context, sn_vec_t* stack, sn_obj_id_t object)
{
    const sn_module_t* module = context->module;
    assert(object < module->obj_types.size);
    if (context->marks[object] == SN_TOPO_DONE)
        return;
    assert(context->marks[object] == SN_TOPO_UNSEEN);
    sn_obj_type_t type = sn_obj_type(module, object);
    assert(type != SN_PI && type != SN_PO);
    context->marks[object] = SN_TOPO_VISITING;
    sn_topo_frame_t* frame = sn_vec_push(sn_topo_frame_t, stack);
    frame->object = object;
    frame->index = 0;
    frame->phase = 0;
}

static inline void sn_module_topo_visit(sn_topo_context_t* context, sn_obj_id_t object)
{
    assert(context);
    const sn_module_t* module = context->module;
    sn_vec_t stack;
    sn_vec_init(&stack);
    sn_module_topo_push(context, &stack, object);
    while (stack.size)
    {
        sn_topo_frame_t* frame = &sn_vec_at(sn_topo_frame_t, &stack, stack.size - 1);
        object = frame->object;
        if (context->marks[object] == SN_TOPO_DONE)
        {
            stack.size--;
            continue;
        }
        sn_obj_type_t type = sn_obj_type(module, object);

        if (sn_obj_type_is_pair_out(type))
        {
            *sn_vec_push(sn_obj_id_t, context->order) = object;
            context->marks[object] = SN_TOPO_DONE;
            stack.size--;
            continue;
        }

        if (frame->phase == 0)
        {
            frame->phase = 1;
            frame->index = 0;
            if (sn_obj_type_is_pair_in(type))
            {
                sn_obj_id_t pair_out = sn_obj_pair_out(module, object);
                assert(context->marks[pair_out] != SN_TOPO_VISITING);
                if (context->marks[pair_out] == SN_TOPO_UNSEEN)
                    sn_module_topo_push(context, &stack, pair_out);
                continue;
            }
        }

        if (frame->phase == 1)
        {
            if (sn_obj_type_is_pair_in(type))
            {
                sn_obj_id_t pair_out = sn_obj_pair_out(module, object);
                bool pushed = false;
                while (frame->index < sn_obj_fanin_count(module, pair_out))
                {
                    sn_obj_id_t fanin = sn_obj_fanin(module, pair_out, frame->index++);
                    if (fanin == SN_INVALID_ID || fanin == object)
                        continue;
                    assert(context->marks[fanin] != SN_TOPO_VISITING);
                    if (context->marks[fanin] == SN_TOPO_UNSEEN)
                    {
                        sn_module_topo_push(context, &stack, fanin);
                        pushed = true;
                        break;
                    }
                }
                if (pushed)
                    continue;
            }
            frame = &sn_vec_at(sn_topo_frame_t, &stack, stack.size - 1);
            frame->phase = 2;
            frame->index = 0;
        }

        bool pushed = false;
        while (frame->index < sn_obj_fanin_count(module, object))
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, object, frame->index++);
            if (fanin == SN_INVALID_ID)
                continue;
            assert(context->marks[fanin] != SN_TOPO_VISITING);
            if (context->marks[fanin] == SN_TOPO_UNSEEN)
            {
                sn_module_topo_push(context, &stack, fanin);
                pushed = true;
                break;
            }
        }
        if (pushed)
            continue;

        if (type == SN_INST)
        {
            *sn_vec_push(sn_obj_id_t, context->order) = object;
            context->marks[object] = SN_TOPO_DONE;
            uint32_t output_count = sn_design_module_output_count(module->design, sn_inst_module_id(module, object));
            if (output_count > 1)
                for (uint32_t i = 0; i < output_count; i++)
                {
                    sn_obj_id_t fan = sn_inst_output(module, object, i);
                    assert(context->marks[fan] != SN_TOPO_DONE);
                    *sn_vec_push(sn_obj_id_t, context->order) = fan;
                    context->marks[fan] = SN_TOPO_DONE;
                }
        }
        else if (context->marks[object] != SN_TOPO_DONE)
        {
            *sn_vec_push(sn_obj_id_t, context->order) = object;
            context->marks[object] = SN_TOPO_DONE;
        }
        stack.size--;
    }

    sn_vec_destroy(&stack);
}

// Returns all module object IDs exactly once. The caller owns the returned
// vector and must call sn_vec_destroy(). PIs occupy the prefix in natural port
// order, POs occupy the suffix in natural port order, and every state OUT
// precedes its paired IN. A normalized combinational cycle triggers assert().
static inline sn_vec_t sn_module_topo_order(const sn_module_t* module)
{
    assert(module);
    sn_vec_t order;
    sn_vec_init(&order);
    size_t object_count = module->obj_types.size;
    sn_vec_reserve(sn_obj_id_t, &order, object_count);

    uint8_t* marks = NULL;
    if (object_count)
    {
        marks = (uint8_t*)calloc(object_count, sizeof(uint8_t));
        assert(marks);
    }

    sn_topo_context_t context;
    context.module = module;
    context.order = &order;
    context.marks = marks;

    // Place every PI first, including unused inputs.
    for (size_t i = 0; i < module->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t input = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], i);
        assert(marks[input] == SN_TOPO_UNSEEN);
        marks[input] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = input;
    }

    // State values are combinational sources. Emit every OUT before exploring
    // any next-state cone so feedback through the corresponding IN cannot
    // encounter an in-progress combinational node.
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        if (!sn_obj_type_is_pair_out(sn_obj_type(module, object)))
            continue;
        assert(marks[object] == SN_TOPO_UNSEEN);
        marks[object] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = object;
    }

    // Traverse PO cones first. POs themselves are deliberately delayed.
    for (size_t i = 0; i < module->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], i);
        for (uint32_t j = 0; j < sn_obj_fanin_count(module, output); j++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, output, j);
            if (fanin != SN_INVALID_ID)
                sn_module_topo_visit(&context, fanin);
        }
    }

    // Include disconnected and otherwise unreachable internal objects.
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if (type != SN_PI && type != SN_PO && marks[object] == SN_TOPO_UNSEEN)
            sn_module_topo_visit(&context, object);
    }

    // Place every PO last in natural port order.
    for (size_t i = 0; i < module->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], i);
        assert(marks[output] == SN_TOPO_UNSEEN);
        marks[output] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = output;
    }

    assert(order.size == object_count);
    free(marks);
    return order;
}

// Accepts any legal SN topological order, not only the particular depth-first
// order returned by sn_module_topo_order(). PIs and POs must form their natural-
// order prefix and suffix. Ordinary fanins precede their users. State OUT may
// precede its structural paired-IN fanin, and its controls may occur after OUT,
// but every such dependency must precede the paired IN. Instance FANs retain
// their immediate natural-order block.
static inline bool sn_module_is_topo(const sn_module_t* module)
{
    assert(module);
    size_t object_count = module->obj_types.size;
    size_t input_count = module->type_objects[SN_PI].size;
    size_t output_count = module->type_objects[SN_PO].size;
    if (input_count + output_count > object_count)
        return false;

    for (size_t i = 0; i < input_count; i++)
        if (sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], i) != i)
            return false;
    size_t output_begin = object_count - output_count;
    for (size_t i = 0; i < output_count; i++)
        if (sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PO], i) != output_begin + i)
            return false;

    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if (object < input_count && type != SN_PI)
            return false;
        if (object >= output_begin && type != SN_PO)
            return false;

        sn_obj_id_t pair_in = SN_INVALID_ID;
        if (sn_obj_type_is_pair_out(type))
        {
            pair_in = sn_obj_pair_in(module, object);
            if (pair_in <= object)
                return false;
        }
        for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, object, i);
            if (fanin == SN_INVALID_ID || fanin == pair_in)
                continue;
            if (pair_in != SN_INVALID_ID)
            {
                if (fanin >= pair_in)
                    return false;
            }
            else if (fanin >= object)
                return false;
        }

        if (type == SN_INST)
        {
            sn_module_id_t child_id = sn_inst_module_id(module, object);
            uint32_t child_outputs = sn_design_module_output_count(module->design, child_id);
            if (child_outputs > 1)
            {
                for (uint32_t i = 0; i < child_outputs; i++)
                    if (sn_inst_output(module, object, i) != object + 1 + i)
                        return false;
            }
        }
        else if (type == SN_FAN)
        {
            sn_obj_id_t inst = sn_fan_inst_id(module, object);
            if (object != inst + 1 + sn_fan_output_index(module, object))
                return false;
        }
    }
    return true;
}

static inline bool sn_design_is_topo(const sn_design_t* design)
{
    assert(design);
    for (size_t i = 0; i < design->modules.size; i++)
        if (!sn_module_is_topo(sn_design_get_module_const(design, (sn_module_id_t)i)))
            return false;
    return true;
}

// Returns the target module and object mapping from the source module's most
// recent duplication. A new duplication replaces the previous mapping. The
// mapping remains owned by the source module until another duplication or
// until that module is destroyed.
static inline sn_module_id_t sn_module_dup_target(const sn_module_t* source)
{
    assert(source);
    assert(source->copy_module < source->design->modules.size);
    return source->copy_module;
}

static inline sn_obj_id_t sn_obj_dup(const sn_module_t* source, sn_obj_id_t old_object)
{
    assert(source);
    assert(source->copy_module < source->design->modules.size);
    assert(source->copy_ids.size == source->obj_types.size);
    assert(old_object < source->copy_ids.size);
    sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
    const sn_module_t* target = sn_design_get_module_const(source->design, source->copy_module);
    assert(new_object < target->obj_types.size);
    (void)target;
    return new_object;
}

static inline void sn_design_invalidate_copies_to_module_except(sn_design_t* design, sn_module_id_t module_id,
                                                                const sn_module_t* preserve)
{
    for (size_t i = 0; i < design->modules.size; i++)
    {
        sn_module_t* module = sn_vec_at(sn_module_t*, &design->modules, i);
        if (!module || module == preserve || module->copy_module != module_id)
            continue;
        sn_vec_destroy(&module->copy_ids);
        sn_vec_init(&module->copy_ids);
        module->copy_module = SN_INVALID_ID;
    }
}

static inline void sn_design_invalidate_copies_to_module(sn_design_t* design, sn_module_id_t module_id)
{
    sn_design_invalidate_copies_to_module_except(design, module_id, NULL);
}

// Duplicates a module in topological order within the same design. Object
// names and design-wide constant words are shared by ID; all module-local
// object references and type-specific object IDs are rebuilt. The old-to-new
// object map is retained in the source module as its most recent copy map.
static inline sn_obj_id_t sn_module_dup_obj_skeleton(sn_module_t* target, const sn_module_t* source,
                                                     sn_obj_id_t old_object)
{
    assert(target);
    assert(source);
    return sn_module_add_obj(target, sn_obj_type(source, old_object), sn_obj_width(source, old_object),
                             sn_obj_is_signed(source, old_object), sn_obj_fanin_count(source, old_object),
                             sn_obj_name_id(source, old_object));
}

// Copies metadata whose value does not contain a module-local object ID.
// SN_FAN ownership is remapped separately, while collapsing omits insts
// and fans entirely.
static inline void sn_module_dup_obj_metadata(sn_module_t* target, sn_type_id_t target_type_id,
                                              const sn_module_t* source, sn_obj_id_t old_object)
{
    assert(target);
    assert(source);
    sn_obj_type_t type = sn_obj_type(source, old_object);
    sn_type_id_t source_type_id = sn_obj_type_id(source, old_object);
    if (type == SN_REG_OUT)
        sn_vec_at(uint32_t, &target->reg_flags, target_type_id) =
            sn_vec_at(uint32_t, &source->reg_flags, source_type_id);
    else if (type == SN_MEM_OUT)
        sn_vec_at(uint32_t, &target->mem_depths, target_type_id) =
            sn_vec_at(uint32_t, &source->mem_depths, source_type_id);
    else if (type == SN_INST)
    {
        sn_module_id_t child_id = sn_vec_at(sn_module_id_t, &source->inst_modules, source_type_id);
        assert(child_id < target->design->modules.size);
        sn_vec_at(sn_module_id_t, &target->inst_modules, target_type_id) = child_id;
        sn_design_get_module(target->design, child_id)->interface_locked = true;
    }
    else if (type == SN_SLICE)
        sn_vec_at(sn_slice_info_t, &target->slice_infos, target_type_id) =
            sn_vec_at(sn_slice_info_t, &source->slice_infos, source_type_id);
    else if (type == SN_REPLICATE)
        sn_vec_at(uint32_t, &target->repeat_counts, target_type_id) =
            sn_vec_at(uint32_t, &source->repeat_counts, source_type_id);
    else if (type == SN_CONST)
        sn_vec_at(uint32_t, &target->const_word_offsets, target_type_id) =
            sn_vec_at(uint32_t, &source->const_word_offsets, source_type_id);
    else if (type == SN_LUT)
        sn_vec_at(uint64_t, &target->lut_truths, target_type_id) =
            sn_vec_at(uint64_t, &source->lut_truths, source_type_id);
    else if (type == SN_GATE)
        sn_vec_at(uint32_t, &target->gate_ids, target_type_id) =
            sn_vec_at(uint32_t, &source->gate_ids, source_type_id);
}

static inline sn_module_id_t sn_design_dup_module_topo(sn_design_t* design, sn_module_id_t source_module_id,
                                                       const char* new_name)
{
    assert(design);
    assert(source_module_id < design->modules.size);
    assert(new_name);

    sn_module_t* source = sn_design_get_module(design, source_module_id);
    sn_vec_t order = sn_module_topo_order(source);
    sn_module_id_t target_module_id = sn_design_add_module(design, new_name);
    sn_module_t* target = sn_design_get_module(design, target_module_id);
    target->flags = source->flags;

    sn_vec_resize(sn_obj_id_t, &source->copy_ids, source->obj_types.size);
    for (size_t i = 0; i < source->copy_ids.size; i++)
        sn_vec_at(sn_obj_id_t, &source->copy_ids, i) = SN_INVALID_ID;

    // Create all objects first so every old fanin has a known new object ID.
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_module_dup_obj_skeleton(target, source, old_object);
        assert(new_object == i);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = new_object;
    }

    // Type IDs are semantically significant (notably for OUT/IN pairing), so
    // preserve them and rebuild each inverse type_objects mapping.
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        sn_obj_type_t type = sn_obj_type(source, old_object);
        sn_type_id_t type_id = sn_obj_type_id(source, old_object);
        assert(type_id < target->type_objects[type].size);
        sn_vec_at(uint32_t, &target->type_ids, new_object) = type_id;
        sn_vec_at(sn_obj_id_t, &target->type_objects[type], type_id) = new_object;
    }

    // Copy the compact type-specific arrays. Entries in these arrays use the
    // preserved source type IDs, except fan owner IDs which are module-local.
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        sn_obj_type_t type = sn_obj_type(source, old_object);
        sn_type_id_t type_id = sn_obj_type_id(source, old_object);
        (void)new_object;

        sn_module_dup_obj_metadata(target, type_id, source, old_object);
        if (type == SN_FAN)
        {
            sn_obj_id_t old_inst = sn_vec_at(sn_obj_id_t, &source->fan_insts, type_id);
            assert(old_inst < source->copy_ids.size);
            sn_obj_id_t new_inst = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_inst);
            assert(new_inst != SN_INVALID_ID);
            sn_vec_at(sn_obj_id_t, &target->fan_insts, type_id) = new_inst;
        }
    }

    // Reconnect all module-local fanins through the persistent copy map.
    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        for (uint32_t j = 0; j < sn_obj_fanin_count(source, old_object); j++)
        {
            sn_obj_id_t old_fanin = sn_obj_fanin(source, old_object, j);
            sn_obj_id_t new_fanin =
                old_fanin == SN_INVALID_ID ? SN_INVALID_ID : sn_vec_at(sn_obj_id_t, &source->copy_ids, old_fanin);
            assert(new_fanin == SN_INVALID_ID || new_fanin < target->obj_types.size);
            sn_obj_connect(target, new_object, j, new_fanin);
        }
    }

    // Validate the invariants that are sensitive to physical reordering.
    for (sn_obj_id_t object = 0; object < target->obj_types.size; object++)
    {
        sn_obj_type_t type = sn_obj_type(target, object);
        if (sn_obj_type_is_pair_out(type))
        {
            sn_obj_id_t pair_in = sn_obj_pair_in(target, object);
            assert(object < pair_in);
            assert(sn_obj_pair_out(target, pair_in) == object);
            (void)pair_in;
        }
        else if (type == SN_FAN)
        {
            sn_obj_id_t inst = sn_fan_inst_id(target, object);
            uint32_t output_index = sn_fan_output_index(target, object);
            assert(object == inst + 1 + output_index);
            (void)inst;
            (void)output_index;
        }
    }

    source->copy_module = target_module_id;
    sn_vec_destroy(&order);
    return target_module_id;
}

// Reorders one module in place using the same dependency-aware duplication as
// sn_design_dup_module_topo(). Its module ID and name are preserved, so existing
// insts remain valid. Pointers and object IDs into the old module become
// invalid; callers must reacquire the module and rebuild any object mappings.
static inline void sn_design_reorder_module_topo(sn_design_t* design, sn_module_id_t module_id)
{
    assert(design);
    assert(module_id < design->modules.size);
    if (sn_module_is_topo(sn_design_get_module_const(design, module_id)))
        return;

    char temporary_name[96];
    uint32_t suffix = 0;
    do
    {
        int length = snprintf(temporary_name, sizeof(temporary_name), "__sn_topo_%u_%u", module_id, suffix++);
        assert(length >= 0 && (size_t)length < sizeof(temporary_name));
        assert(suffix != 0);
    } while (sn_name_find(&design->names, temporary_name) != SN_INVALID_ID);

    size_t old_module_count = design->modules.size;
    sn_module_t* source = sn_design_get_module(design, module_id);
    sn_name_id_t source_name = source->name;
    bool interface_locked = source->interface_locked;
    sn_module_id_t reordered_id = sn_design_dup_module_topo(design, module_id, temporary_name);
    assert(reordered_id == old_module_count);
    sn_module_t* reordered = sn_design_get_module(design, reordered_id);
    sn_name_id_t temporary_name_id = reordered->name;

    sn_design_invalidate_copies_to_module(design, module_id);
    sn_module_destroy(source);
    free(source);
    reordered->id = module_id;
    reordered->name = source_name;
    reordered->interface_locked = interface_locked;
    sn_vec_at(sn_module_t*, &design->modules, module_id) = reordered;
    design->modules.size--;
    sn_name_remove_last(&design->names, temporary_name_id);
    assert(sn_module_is_topo(reordered));
}

typedef struct sn_const_zero_frame_t
{
    sn_obj_id_t object;
    uint32_t next_fanin;
} sn_const_zero_frame_t;

static inline uint32_t sn_const_zero_dependency_count(const sn_module_t* module, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_CAST || type == SN_SLICE || type == SN_REPLICATE)
        return 1;
    if (type == SN_CONCAT || type == SN_BIT_AND || type == SN_LOG_AND || type == SN_BIT_OR ||
        type == SN_BIT_XOR || type == SN_LOG_OR)
        return sn_obj_fanin_count(module, object);
    if (type == SN_MUX || type == SN_PMUX)
        return 3;
    return 0;
}

static inline bool sn_const_zero_cached(const uint8_t* cache, sn_obj_id_t object)
{
    return object != SN_INVALID_ID && cache[object] == 1;
}

static inline bool sn_const_zero_evaluate(const sn_module_t* module, sn_obj_id_t object, const uint8_t* cache)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_CONST0)
        return true;
    if (type == SN_CONST)
    {
        const uint32_t* words = sn_const_words(module, object);
        for (uint32_t i = 0; i < sn_const_word_count(sn_obj_width(module, object)); i++)
            if (words[i])
                return false;
        return true;
    }
    if (type == SN_CAST || type == SN_SLICE || type == SN_REPLICATE)
        return sn_const_zero_cached(cache, sn_obj_fanin(module, object, 0));
    if (type == SN_CONCAT || type == SN_BIT_OR || type == SN_BIT_XOR || type == SN_LOG_OR)
    {
        for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
            if (!sn_const_zero_cached(cache, sn_obj_fanin(module, object, i)))
                return false;
        return true;
    }
    if (type == SN_BIT_AND || type == SN_LOG_AND)
    {
        for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
            if (sn_const_zero_cached(cache, sn_obj_fanin(module, object, i)))
                return true;
        return false;
    }
    if (type == SN_MUX)
    {
        sn_obj_id_t select = sn_obj_fanin(module, object, SN_MUX_SELECT);
        sn_obj_id_t selected = sn_obj_fanin(module, object, SN_MUX_SELECTED);
        sn_obj_id_t default_value = sn_obj_fanin(module, object, SN_MUX_DEFAULT);
        return sn_const_zero_cached(cache, select)
                   ? sn_const_zero_cached(cache, default_value)
                   : sn_const_zero_cached(cache, selected) && sn_const_zero_cached(cache, default_value);
    }
    if (type == SN_PMUX)
    {
        sn_obj_id_t select = sn_obj_fanin(module, object, SN_PMUX_SELECT);
        sn_obj_id_t alternatives = sn_obj_fanin(module, object, SN_PMUX_ALTERNATIVES);
        sn_obj_id_t default_value = sn_obj_fanin(module, object, SN_PMUX_DEFAULT);
        return sn_const_zero_cached(cache, select)
                   ? sn_const_zero_cached(cache, default_value)
                   : sn_const_zero_cached(cache, alternatives) && sn_const_zero_cached(cache, default_value);
    }
    return false;
}

// Returns true for the constant-zero forms needed by sequential cleanup. The explicit stack bounds native call-stack
// use even for very deep expression chains; ordinary combinational constant propagation remains a separate pass.
static inline bool sn_obj_is_const_zero_rec(const sn_module_t* module, sn_obj_id_t object, uint8_t* cache)
{
    assert(module);
    if (object == SN_INVALID_ID)
        return false;
    bool owns_cache = cache == NULL;
    if (owns_cache)
    {
        cache = (uint8_t*)calloc(module->obj_types.size, 1);
        assert(cache);
    }
    if (!cache[object])
    {
        sn_vec_t stack;
        sn_vec_init(&stack);
        cache[object] = 3;
        sn_const_zero_frame_t* first = sn_vec_push(sn_const_zero_frame_t, &stack);
        first->object = object;
        first->next_fanin = 0;
        while (stack.size)
        {
            sn_const_zero_frame_t* frame =
                &sn_vec_at(sn_const_zero_frame_t, &stack, stack.size - 1);
            uint32_t dependency_count = sn_const_zero_dependency_count(module, frame->object);
            if (frame->next_fanin < dependency_count)
            {
                sn_obj_id_t dependency = sn_obj_fanin(module, frame->object, frame->next_fanin++);
                if (dependency != SN_INVALID_ID && cache[dependency] == 0)
                {
                    cache[dependency] = 3;
                    sn_const_zero_frame_t* child = sn_vec_push(sn_const_zero_frame_t, &stack);
                    child->object = dependency;
                    child->next_fanin = 0;
                }
                continue;
            }
            cache[frame->object] = sn_const_zero_evaluate(module, frame->object, cache) ? 1 : 2;
            stack.size--;
        }
        sn_vec_destroy(&stack);
    }
    bool result = cache[object] == 1;
    if (owns_cache)
        free(cache);
    return result;
}

static inline bool sn_obj_is_const_zero(const sn_module_t* module, sn_obj_id_t object)
{
    return sn_obj_is_const_zero_rec(module, object, NULL);
}

// Under SN's two-state sequential convention, an unspecified or unknown
// initial state starts at zero. A register therefore remains zero when it has
// no active set, has no nonzero explicit initialization/reset value, and its
// data is zero (or its enable is permanently disabled).
static inline bool sn_reg_is_const_zero(const sn_module_t* module, sn_obj_id_t reg_out, uint8_t* cache)
{
    assert(module);
    assert(sn_obj_type(module, reg_out) == SN_REG_OUT);
    sn_obj_id_t set = sn_obj_fanin(module, reg_out, SN_REG_SET);
    sn_obj_id_t init = sn_obj_fanin(module, reg_out, SN_REG_INIT_DATA);
    sn_obj_id_t reset_value = sn_obj_fanin(module, reg_out, SN_REG_RESET_VALUE);
    if ((set != SN_INVALID_ID && !sn_obj_is_const_zero_rec(module, set, cache)) ||
        (init != SN_INVALID_ID && !sn_obj_is_const_zero_rec(module, init, cache)) ||
        (reset_value != SN_INVALID_ID && !sn_obj_is_const_zero_rec(module, reset_value, cache)))
        return false;

    sn_obj_id_t enable = sn_obj_fanin(module, reg_out, SN_REG_ENABLE);
    if (enable != SN_INVALID_ID && sn_obj_is_const_zero_rec(module, enable, cache))
        return true;
    sn_obj_id_t reg_in = sn_obj_pair_in(module, reg_out);
    sn_obj_id_t data = sn_obj_fanin(module, reg_in, 0);
    return data == reg_out || sn_obj_is_const_zero_rec(module, data, cache);
}

typedef struct sn_clean_topo_context_t
{
    const sn_module_t* module;
    sn_vec_t* order;
    uint8_t* marks;
    uint8_t* const_zero_objects;
    uint8_t* const_zero_cache;
} sn_clean_topo_context_t;

static inline void sn_module_clean_topo_push(sn_clean_topo_context_t* context, sn_vec_t* stack,
                                             sn_obj_id_t object)
{
    const sn_module_t* module = context->module;
    assert(object < module->obj_types.size);
    if (context->marks[object] == SN_TOPO_DONE)
        return;
    assert(context->marks[object] == SN_TOPO_UNSEEN);
    sn_obj_type_t type = sn_obj_type(module, object);
    assert(type != SN_PI && type != SN_PO);
    if (context->const_zero_objects[object] || sn_obj_is_const_zero_rec(module, object, context->const_zero_cache))
    {
        context->const_zero_objects[object] = 1;
        context->marks[object] = SN_TOPO_DONE;
        return;
    }
    context->marks[object] = SN_TOPO_VISITING;
    sn_topo_frame_t* frame = sn_vec_push(sn_topo_frame_t, stack);
    frame->object = object;
    frame->index = 0;
    frame->phase = 0;
}

static inline void sn_module_clean_topo_visit(sn_clean_topo_context_t* context, sn_obj_id_t object)
{
    assert(context);
    const sn_module_t* module = context->module;
    sn_vec_t stack;
    sn_vec_init(&stack);
    sn_module_clean_topo_push(context, &stack, object);
    while (stack.size)
    {
        sn_topo_frame_t* frame = &sn_vec_at(sn_topo_frame_t, &stack, stack.size - 1);
        object = frame->object;
        if (context->marks[object] == SN_TOPO_DONE)
        {
            stack.size--;
            continue;
        }
        sn_obj_type_t type = sn_obj_type(module, object);
        if (sn_obj_type_is_pair_out(type))
        {
            *sn_vec_push(sn_obj_id_t, context->order) = object;
            context->marks[object] = SN_TOPO_DONE;
            stack.size--;
            continue;
        }
        if (frame->phase == 0)
        {
            frame->phase = 1;
            frame->index = 0;
            if (sn_obj_type_is_pair_in(type))
            {
                sn_obj_id_t pair_out = sn_obj_pair_out(module, object);
                assert(context->marks[pair_out] != SN_TOPO_VISITING);
                if (context->marks[pair_out] == SN_TOPO_UNSEEN)
                    sn_module_clean_topo_push(context, &stack, pair_out);
                continue;
            }
        }
        if (frame->phase == 1)
        {
            if (sn_obj_type_is_pair_in(type))
            {
                sn_obj_id_t pair_out = sn_obj_pair_out(module, object);
                bool pushed = false;
                while (frame->index < sn_obj_fanin_count(module, pair_out))
                {
                    sn_obj_id_t fanin = sn_obj_fanin(module, pair_out, frame->index++);
                    if (fanin == SN_INVALID_ID || fanin == object)
                        continue;
                    assert(context->marks[fanin] != SN_TOPO_VISITING);
                    if (context->marks[fanin] == SN_TOPO_UNSEEN)
                    {
                        sn_module_clean_topo_push(context, &stack, fanin);
                        pushed = true;
                        break;
                    }
                }
                if (pushed)
                    continue;
            }
            frame = &sn_vec_at(sn_topo_frame_t, &stack, stack.size - 1);
            frame->phase = 2;
            frame->index = 0;
        }
        bool pushed = false;
        while (frame->index < sn_obj_fanin_count(module, object))
        {
            sn_obj_id_t fanin = sn_obj_fanin(module, object, frame->index++);
            if (fanin == SN_INVALID_ID)
                continue;
            assert(context->marks[fanin] != SN_TOPO_VISITING);
            if (context->marks[fanin] == SN_TOPO_UNSEEN)
            {
                sn_module_clean_topo_push(context, &stack, fanin);
                pushed = true;
                break;
            }
        }
        if (pushed)
            continue;
        if (type == SN_INST)
        {
            *sn_vec_push(sn_obj_id_t, context->order) = object;
            context->marks[object] = SN_TOPO_DONE;
            uint32_t output_count = sn_design_module_output_count(module->design, sn_inst_module_id(module, object));
            if (output_count > 1)
                for (uint32_t i = 0; i < output_count; i++)
                {
                    sn_obj_id_t fan = sn_inst_output(module, object, i);
                    assert(context->marks[fan] != SN_TOPO_DONE);
                    *sn_vec_push(sn_obj_id_t, context->order) = fan;
                    context->marks[fan] = SN_TOPO_DONE;
                }
        }
        else if (context->marks[object] != SN_TOPO_DONE)
        {
            *sn_vec_push(sn_obj_id_t, context->order) = object;
            context->marks[object] = SN_TOPO_DONE;
        }
        stack.size--;
    }
    sn_vec_destroy(&stack);
}

static inline void sn_module_clean_rebuild_pair_ids(sn_module_t* target, const sn_module_t* source,
                                                    sn_obj_type_t out_type, sn_obj_type_t in_type)
{
    assert(target);
    assert(source);
    size_t next_type_id = 0;
    for (size_t i = 0; i < source->type_objects[out_type].size; i++)
    {
        sn_obj_id_t old_out = sn_vec_at(sn_obj_id_t, &source->type_objects[out_type], i);
        sn_obj_id_t new_out = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_out);
        if (new_out == SN_INVALID_ID || sn_obj_type(target, new_out) != out_type)
            continue;
        sn_obj_id_t old_in = sn_obj_pair_in(source, old_out);
        sn_obj_id_t new_in = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_in);
        assert(new_in != SN_INVALID_ID && sn_obj_type(target, new_in) == in_type);
        assert(next_type_id < target->type_objects[out_type].size);
        assert(next_type_id < target->type_objects[in_type].size);
        sn_vec_at(uint32_t, &target->type_ids, new_out) = (uint32_t)next_type_id;
        sn_vec_at(uint32_t, &target->type_ids, new_in) = (uint32_t)next_type_id;
        sn_vec_at(sn_obj_id_t, &target->type_objects[out_type], next_type_id) = new_out;
        sn_vec_at(sn_obj_id_t, &target->type_objects[in_type], next_type_id) = new_in;
        next_type_id++;
    }
    assert(next_type_id == target->type_objects[out_type].size);
    assert(next_type_id == target->type_objects[in_type].size);
}

// Duplicates only the sequential transitive fanin cone of the module outputs.
// A reached state OUT makes its paired IN, next-state logic, and controls
// reachable. Unreached state and logic are omitted. Registers proven to remain
// zero are replaced by constants, so their pairs are never constructed. PIs
// and POs are always preserved in natural interface order.
static inline sn_module_id_t sn_design_dup_module_clean_topo(sn_design_t* design,
                                                             sn_module_id_t source_module_id,
                                                             const char* new_name)
{
    assert(design);
    assert(source_module_id < design->modules.size);
    assert(new_name);
    sn_module_t* source = sn_design_get_module(design, source_module_id);
    size_t object_count = source->obj_types.size;
    uint8_t* marks = object_count ? (uint8_t*)calloc(object_count, sizeof(uint8_t)) : NULL;
    uint8_t* const_zero_objects = object_count ? (uint8_t*)calloc(object_count, sizeof(uint8_t)) : NULL;
    uint8_t* const_zero_cache = object_count ? (uint8_t*)calloc(object_count, sizeof(uint8_t)) : NULL;
    assert(!object_count || (marks && const_zero_objects && const_zero_cache));

    for (size_t i = 0; i < source->type_objects[SN_REG_OUT].size; i++)
    {
        sn_obj_id_t reg_out = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_REG_OUT], i);
        if (!sn_reg_is_const_zero(source, reg_out, const_zero_cache))
            continue;
        const_zero_objects[reg_out] = 1;
        marks[sn_obj_pair_in(source, reg_out)] = SN_TOPO_DONE;
    }

    sn_vec_t order;
    sn_vec_init(&order);
    sn_vec_reserve(sn_obj_id_t, &order, object_count);
    for (size_t i = 0; i < source->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t input = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PI], i);
        marks[input] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = input;
    }
    sn_clean_topo_context_t context = {source, &order, marks, const_zero_objects, const_zero_cache};
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        for (uint32_t j = 0; j < sn_obj_fanin_count(source, output); j++)
        {
            sn_obj_id_t fanin = sn_obj_fanin(source, output, j);
            if (fanin != SN_INVALID_ID)
                sn_module_clean_topo_visit(&context, fanin);
        }
    }
    // State OUTs break sequential cycles. After discovering them from the PO
    // cones, traverse their paired IN cones separately. Those cones can expose
    // more live state, so iterate to a fixed point.
    bool added_state;
    do
    {
        added_state = false;
        for (sn_obj_id_t object = 0; object < object_count; object++)
        {
            sn_obj_type_t type = sn_obj_type(source, object);
            if (!sn_obj_type_is_pair_out(type) || const_zero_objects[object] ||
                marks[object] != SN_TOPO_DONE)
                continue;
            sn_obj_id_t pair_in = sn_obj_pair_in(source, object);
            if (marks[pair_in] == SN_TOPO_DONE)
                continue;
            sn_module_clean_topo_visit(&context, pair_in);
            added_state = true;
        }
    } while (added_state);
    for (size_t i = 0; i < source->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t output = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
        marks[output] = SN_TOPO_DONE;
        *sn_vec_push(sn_obj_id_t, &order) = output;
    }

    sn_module_id_t target_id = sn_design_add_module(design, new_name);
    sn_module_t* target = sn_design_get_module(design, target_id);
    target->flags = source->flags;
    sn_vec_resize(sn_obj_id_t, &source->copy_ids, object_count);
    for (size_t i = 0; i < object_count; i++)
        sn_vec_at(sn_obj_id_t, &source->copy_ids, i) = SN_INVALID_ID;

    size_t input_count = source->type_objects[SN_PI].size;
    for (size_t i = 0; i < input_count; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) =
            sn_module_dup_obj_skeleton(target, source, old_object);
    }
    for (sn_obj_id_t old_object = 0; old_object < object_count; old_object++)
    {
        if (!const_zero_objects[old_object] || marks[old_object] != SN_TOPO_DONE)
            continue;
        uint32_t bits = sn_obj_width(source, old_object);
        uint32_t* words = (uint32_t*)calloc(sn_const_word_count(bits), sizeof(uint32_t));
        sn_name_id_t source_name_id = sn_obj_name_id(source, old_object);
        const char* source_name = source_name_id == SN_INVALID_ID ? NULL :
                                  sn_name_get(&source->design->names, source_name_id);
        char* name = source_name ? (char*)malloc(strlen(source_name) + 1) : NULL;
        assert(words);
        if (source_name)
        {
            assert(name);
            memcpy(name, source_name, strlen(source_name) + 1);
        }
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) =
            sn_module_add_const(target, bits, sn_obj_is_signed(source, old_object), words, name);
        free(name);
        free(words);
    }
    for (size_t i = input_count; i < order.size; i++)
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
        sn_type_id_t target_type_id = sn_obj_type_id(target, new_object);
        sn_module_dup_obj_metadata(target, target_type_id, source, old_object);
        if (type == SN_FAN)
        {
            sn_obj_id_t old_inst = sn_fan_inst_id(source, old_object);
            sn_vec_at(sn_obj_id_t, &target->fan_insts, target_type_id) =
                sn_vec_at(sn_obj_id_t, &source->copy_ids, old_inst);
        }
    }

    for (size_t i = 0; i < order.size; i++)
    {
        sn_obj_id_t old_object = sn_vec_at(sn_obj_id_t, &order, i);
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
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
    free(const_zero_objects);
    free(const_zero_cache);
    assert(sn_module_is_topo(target));
    return target_id;
}

// Reconstructs one module in place using the observable-cone cleanup above.
// Existing module IDs and interface names remain stable for hierarchical insts.
static inline void sn_design_cleanup_module_topo(sn_design_t* design, sn_module_id_t module_id)
{
    assert(design);
    assert(module_id < design->modules.size);
    // A loop-breaker can separate output-specific dependencies of a
    // multi-output child instance. This local traversal conservatively treats
    // every instance output as depending on every input, which can recreate an
    // artificial cycle. Preserve such modules with the ordinary topo rebuild.
    if (sn_design_get_module_const(design, module_id)->type_objects[SN_LOOP_OUT].size)
    {
        sn_design_reorder_module_topo(design, module_id);
        return;
    }
    char temporary_name[96];
    uint32_t suffix = 0;
    do
    {
        int length = snprintf(temporary_name, sizeof(temporary_name), "__sn_clean_%u_%u", module_id, suffix++);
        assert(length >= 0 && (size_t)length < sizeof(temporary_name));
        assert(suffix != 0);
    } while (sn_name_find(&design->names, temporary_name) != SN_INVALID_ID);

    sn_module_t* source = sn_design_get_module(design, module_id);
    sn_name_id_t source_name = source->name;
    bool interface_locked = source->interface_locked;
    sn_module_id_t clean_id = sn_design_dup_module_clean_topo(design, module_id, temporary_name);
    sn_module_t* clean = sn_design_get_module(design, clean_id);
    sn_name_id_t temporary_name_id = clean->name;
    sn_design_invalidate_copies_to_module(design, module_id);
    sn_module_destroy(source);
    free(source);
    clean->id = module_id;
    clean->name = source_name;
    clean->interface_locked = interface_locked;
    sn_vec_at(sn_module_t*, &design->modules, module_id) = clean;
    design->modules.size--;
    sn_name_remove_last(&design->names, temporary_name_id);
    assert(sn_module_is_topo(clean));
}

typedef struct sn_collapse_context_t
{
    sn_design_t* design;
    sn_module_t* target;
    uint8_t* active_modules;
    bool preserve_technology_primitives;
} sn_collapse_context_t;

static inline bool sn_module_is_technology_primitive(const sn_module_t* module)
{
    assert(module);
    if (sn_module_is_blackbox(module))
        return true;
    const char* name = sn_name_get(&module->design->names, module->name);
    return strncmp(name, "__sn_RAM", 8) == 0 || strncmp(name, "__sn_URAM", 9) == 0 ||
           strncmp(name, "__sn_DSP", 8) == 0 || strncmp(name, "__sn_CARRY", 10) == 0;
}

static inline bool sn_collapse_preserves_object(const sn_collapse_context_t* context,
                                                const sn_module_t* source, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(source, object);
    sn_obj_id_t inst = type == SN_INST ? object : type == SN_FAN ? sn_fan_inst_id(source, object)
                                                                        : SN_INVALID_ID;
    if (inst == SN_INVALID_ID)
        return false;
    const sn_module_t* child = sn_design_get_module_const(context->design, sn_inst_module_id(source, inst));
    if (sn_module_is_blackbox(child))
        return true;
    return context->preserve_technology_primitives && sn_module_is_technology_primitive(child);
}

static inline bool sn_collapse_obj_is_copied(sn_obj_type_t type, bool is_top)
{
    if (type == SN_INST || type == SN_FAN)
        return false;
    if (!is_top && (type == SN_PI || type == SN_PO))
        return false;
    return true;
}

static inline void sn_module_collapse_into(sn_collapse_context_t* context, sn_module_id_t source_module_id,
                                           const sn_obj_id_t* input_bindings, uint32_t input_count, bool is_top,
                                           sn_vec_t* output_bindings)
{
    assert(context);
    assert(source_module_id < context->design->modules.size);
    assert(!context->active_modules[source_module_id]);
    sn_module_t* source = sn_design_get_module(context->design, source_module_id);
    assert(sn_module_is_topo(source));
    assert(is_top || input_count == source->type_objects[SN_PI].size);
    assert(is_top || input_count == 0 || input_bindings);
    (void)input_count;
    context->active_modules[source_module_id] = 1;

    sn_vec_resize(sn_obj_id_t, &source->copy_ids, source->obj_types.size);
    for (size_t i = 0; i < source->copy_ids.size; i++)
        sn_vec_at(sn_obj_id_t, &source->copy_ids, i) = SN_INVALID_ID;
    source->copy_module = context->target->id;

    for (sn_obj_id_t old_object = 0; old_object < source->obj_types.size; old_object++)
    {
        sn_obj_type_t type = sn_obj_type(source, old_object);
        if (type == SN_PI && !is_top)
        {
            sn_type_id_t port_index = sn_obj_type_id(source, old_object);
            assert(port_index < input_count);
            sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = input_bindings[port_index];
            continue;
        }
        if (type == SN_PO && !is_top)
        {
            assert(sn_obj_fanin_count(source, old_object) == 1);
            sn_obj_id_t driver = sn_obj_fanin(source, old_object, 0);
            assert(driver < source->copy_ids.size);
            sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = sn_vec_at(sn_obj_id_t, &source->copy_ids, driver);
            continue;
        }
        if (type == SN_FAN)
        {
            if (sn_collapse_preserves_object(context, source, old_object))
            {
                sn_obj_id_t new_object = sn_module_dup_obj_skeleton(context->target, source, old_object);
                sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = new_object;
                sn_obj_id_t old_inst = sn_fan_inst_id(source, old_object);
                sn_vec_at(sn_obj_id_t, &context->target->fan_insts,
                          sn_obj_type_id(context->target, new_object)) =
                    sn_vec_at(sn_obj_id_t, &source->copy_ids, old_inst);
            }
            else
                assert(sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) != SN_INVALID_ID);
            continue;
        }
        if (type == SN_INST)
        {
            if (sn_collapse_preserves_object(context, source, old_object))
            {
                sn_obj_id_t new_object = sn_module_dup_obj_skeleton(context->target, source, old_object);
                sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = new_object;
                sn_module_dup_obj_metadata(context->target, sn_obj_type_id(context->target, new_object),
                                           source, old_object);
                continue;
            }
            sn_module_id_t child_id = sn_inst_module_id(source, old_object);
            const sn_module_t* child = sn_design_get_module_const(context->design, child_id);
            uint32_t child_input_count = (uint32_t)child->type_objects[SN_PI].size;
            assert(child_input_count == sn_obj_fanin_count(source, old_object));

            sn_vec_t child_inputs;
            sn_vec_t child_outputs;
            sn_vec_init(&child_inputs);
            sn_vec_init(&child_outputs);
            sn_vec_resize(sn_obj_id_t, &child_inputs, child_input_count);
            for (uint32_t i = 0; i < child_input_count; i++)
            {
                sn_obj_id_t old_fanin = sn_obj_fanin(source, old_object, i);
                assert(old_fanin < source->copy_ids.size);
                sn_obj_id_t new_fanin = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_fanin);
                assert(new_fanin < context->target->obj_types.size);
                sn_vec_at(sn_obj_id_t, &child_inputs, i) = new_fanin;
            }

            sn_module_collapse_into(context, child_id, sn_vec_data(sn_obj_id_t, &child_inputs), child_input_count,
                                    false, &child_outputs);
            uint32_t output_count = sn_design_module_output_count(context->design, child_id);
            assert(child_outputs.size == output_count);
            if (output_count == 1)
                sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = sn_vec_at(sn_obj_id_t, &child_outputs, 0);
            else
            {
                for (uint32_t i = 0; i < output_count; i++)
                {
                    sn_obj_id_t fan = sn_inst_output(source, old_object, i);
                    sn_vec_at(sn_obj_id_t, &source->copy_ids, fan) = sn_vec_at(sn_obj_id_t, &child_outputs, i);
                }
            }
            sn_vec_destroy(&child_outputs);
            sn_vec_destroy(&child_inputs);
            continue;
        }

        sn_obj_id_t new_object = sn_module_dup_obj_skeleton(context->target, source, old_object);
        sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object) = new_object;
        sn_module_dup_obj_metadata(context->target, sn_obj_type_id(context->target, new_object), source, old_object);
    }

    // Patch fanins after every source object has a mapping. This is needed for
    // the deliberate forward structural edge from a state OUT to its IN and
    // for REG_OUT control fanins which can appear between the pair endpoints.
    for (sn_obj_id_t old_object = 0; old_object < source->obj_types.size; old_object++)
    {
        sn_obj_type_t type = sn_obj_type(source, old_object);
        if (!sn_collapse_obj_is_copied(type, is_top) &&
            !sn_collapse_preserves_object(context, source, old_object))
            continue;
        sn_obj_id_t new_object = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_object);
        assert(new_object < context->target->obj_types.size);
        for (uint32_t i = 0; i < sn_obj_fanin_count(source, old_object); i++)
        {
            sn_obj_id_t old_fanin = sn_obj_fanin(source, old_object, i);
            sn_obj_id_t new_fanin =
                old_fanin == SN_INVALID_ID ? SN_INVALID_ID : sn_vec_at(sn_obj_id_t, &source->copy_ids, old_fanin);
            assert(new_fanin == SN_INVALID_ID || new_fanin < context->target->obj_types.size);
            sn_obj_connect(context->target, new_object, i, new_fanin);
        }
    }

    if (output_bindings)
    {
        size_t output_count = source->type_objects[SN_PO].size;
        sn_vec_resize(sn_obj_id_t, output_bindings, output_count);
        for (size_t i = 0; i < output_count; i++)
        {
            sn_obj_id_t old_output = sn_vec_at(sn_obj_id_t, &source->type_objects[SN_PO], i);
            sn_obj_id_t new_output = sn_vec_at(sn_obj_id_t, &source->copy_ids, old_output);
            if (is_top)
                new_output = sn_obj_fanin(context->target, new_output, 0);
            assert(new_output < context->target->obj_types.size);
            sn_vec_at(sn_obj_id_t, output_bindings, i) = new_output;
        }
    }
    context->active_modules[source_module_id] = 0;
}

static inline void sn_module_rebuild_pair_type_ids(sn_module_t* module, sn_obj_type_t out_type, sn_obj_type_t in_type,
                                                   uint32_t pair_fanin_slot)
{
    assert(module);
    assert(module->type_objects[out_type].size == module->type_objects[in_type].size);
    for (size_t i = 0; i < module->type_objects[out_type].size; i++)
    {
        sn_obj_id_t out = sn_vec_at(sn_obj_id_t, &module->type_objects[out_type], i);
        sn_obj_id_t in = sn_obj_fanin(module, out, pair_fanin_slot);
        assert(sn_obj_type(module, in) == in_type);
        sn_vec_at(uint32_t, &module->type_ids, out) = (sn_type_id_t)i;
        sn_vec_at(uint32_t, &module->type_ids, in) = (sn_type_id_t)i;
        sn_vec_at(sn_obj_id_t, &module->type_objects[in_type], i) = in;
    }
}

static inline char* sn_design_flat_module_name(const sn_design_t* design, sn_module_id_t source_module_id)
{
    const sn_module_t* source = sn_design_get_module_const(design, source_module_id);
    const char* source_name = sn_name_get(&design->names, source->name);
    size_t cap = strlen(source_name) + 32;
    char* candidate = (char*)malloc(cap);
    assert(candidate);
    for (uint32_t suffix = 0;; suffix++)
    {
        int length = suffix == 0 ? snprintf(candidate, cap, "%s_flat", source_name)
                                 : snprintf(candidate, cap, "%s_flat_%u", source_name, suffix);
        assert(length >= 0 && (size_t)length < cap);
        (void)length;
        bool found = false;
        for (size_t i = 0; i < design->modules.size; i++)
        {
            const sn_module_t* module = sn_design_get_module_const(design, (sn_module_id_t)i);
            found = found || strcmp(candidate, sn_name_get(&design->names, module->name)) == 0;
        }
        if (!found)
            return candidate;
        assert(suffix != UINT32_MAX);
    }
}

// Flattens the selected top module into a newly created module. Every existing
// design module must already satisfy sn_module_is_topo(). The generated name is
// <top>_flat, with a numeric suffix when needed.
static inline sn_module_id_t sn_design_collapse_module_internal(sn_design_t* design, sn_module_id_t top_module_id,
                                                                bool preserve_technology_primitives)
{
    assert(design);
    assert(top_module_id < design->modules.size);
    bool design_is_topo = sn_design_is_topo(design);
    assert(design_is_topo);
    (void)design_is_topo;

    size_t source_module_count = design->modules.size;
    char* flat_name = sn_design_flat_module_name(design, top_module_id);
    sn_module_id_t flat_module_id = sn_design_add_module(design, flat_name);
    free(flat_name);
    sn_module_t* flat = sn_design_get_module(design, flat_module_id);

    uint8_t* active_modules = NULL;
    if (source_module_count)
    {
        active_modules = (uint8_t*)calloc(source_module_count, sizeof(uint8_t));
        assert(active_modules);
    }
    sn_collapse_context_t context;
    context.design = design;
    context.target = flat;
    context.active_modules = active_modules;
    context.preserve_technology_primitives = preserve_technology_primitives;
    sn_module_collapse_into(&context, top_module_id, NULL, 0, true, NULL);
    free(active_modules);

    sn_module_rebuild_pair_type_ids(flat, SN_REG_OUT, SN_REG_IN, SN_REG_DATA);
    sn_module_rebuild_pair_type_ids(flat, SN_MEM_OUT, SN_MEM_IN, SN_MEM_STATE);
    sn_module_rebuild_pair_type_ids(flat, SN_LOOP_OUT, SN_LOOP_IN, 0);

    for (size_t i = 0; i < flat->inst_modules.size; i++)
        assert(sn_module_is_technology_primitive(
            sn_design_get_module_const(design, sn_vec_at(sn_module_id_t, &flat->inst_modules, i))));
    assert(sn_module_is_topo(flat));
    return flat_module_id;
}

static inline sn_module_id_t sn_design_collapse_module(sn_design_t* design, sn_module_id_t top_module_id)
{
    return sn_design_collapse_module_internal(design, top_module_id, false);
}

// Flattens user hierarchy while retaining technology primitive leaf insts.
static inline sn_module_id_t sn_design_collapse_module_tech(sn_design_t* design, sn_module_id_t top_module_id)
{
    return sn_design_collapse_module_internal(design, top_module_id, true);
}

// The initial Verilog writer is a structural debugging aid. It preserves
// hierarchy and supports ports, insts, constants, common combinational
// operators, slices, and concatenations. It asserts on state and memory
// objects until their exact behavioral Verilog policy is finalized.

static inline const char* sn_verilog_unary_token(sn_obj_type_t type)
{
    switch (type)
    {
    case SN_POS:
        return "+";
    case SN_NEG:
        return "-";
    case SN_BIT_NOT:
        return "~";
    case SN_LOG_NOT:
        return "!";
    case SN_REDUCE_AND:
        return "&";
    case SN_REDUCE_NAND:
        return "~&";
    case SN_REDUCE_OR:
        return "|";
    case SN_REDUCE_NOR:
        return "~|";
    case SN_REDUCE_XOR:
        return "^";
    case SN_REDUCE_XNOR:
        return "~^";
    default:
        return NULL;
    }
}

static inline const char* sn_verilog_binary_token(sn_obj_type_t type)
{
    switch (type)
    {
    case SN_ADD:
        return "+";
    case SN_SUB:
        return "-";
    case SN_MUL:
        return "*";
    case SN_DIV:
        return "/";
    case SN_MOD:
        return "%";
    case SN_POW:
        return "**";
    case SN_BIT_AND:
        return "&";
    case SN_BIT_OR:
        return "|";
    case SN_BIT_XOR:
        return "^";
    case SN_BIT_XNOR:
        return "~^";
    case SN_LOG_AND:
        return "&&";
    case SN_LOG_OR:
        return "||";
    case SN_EQ:
        return "==";
    case SN_NE:
        return "!=";
    case SN_CASE_EQ:
        return "===";
    case SN_CASE_NE:
        return "!==";
    case SN_WILDCARD_EQ:
        return "==?";
    case SN_WILDCARD_NE:
        return "!=?";
    case SN_LT:
        return "<";
    case SN_LE:
        return "<=";
    case SN_GT:
        return ">";
    case SN_GE:
        return ">=";
    case SN_SHL:
        return "<<";
    case SN_SHR:
        return ">>";
    case SN_ASHL:
        return "<<<";
    case SN_ASHR:
        return ">>>";
    default:
        return NULL;
    }
}

static inline void sn_write_verilog_range(FILE* out, const sn_module_t* module, sn_obj_id_t object)
{
    uint32_t width = sn_obj_width(module, object);
    assert(width);
    if (sn_obj_is_signed(module, object))
        fputs("signed ", out);
    if (width > 1)
        fprintf(out, "[%u:0] ", width - 1);
}

static inline bool sn_verilog_is_keyword(const char* text)
{
    static const char* const keywords[] = {
        "accept_on", "alias", "always", "always_comb", "always_ff", "always_latch", "and", "assert",
        "assign", "assume", "automatic", "before", "begin", "bind", "bins", "binsof", "bit", "break",
        "buf", "bufif0", "bufif1", "byte", "case", "casex", "casez", "cell", "chandle", "checker", "class",
        "clocking", "cmos", "config", "const", "constraint", "context", "continue", "cover", "covergroup",
        "coverpoint", "cross", "deassign", "default", "defparam", "design", "disable", "dist", "do", "edge",
        "else", "end", "endcase", "endchecker", "endclass", "endclocking", "endconfig", "endfunction",
        "endgenerate", "endgroup", "endinterface", "endmodule", "endpackage", "endprimitive", "endprogram",
        "endproperty", "endsequence", "endspecify", "endtable", "endtask", "enum", "event", "eventually",
        "expect", "export", "extends", "extern", "final", "first_match", "for", "force", "foreach", "forever",
        "fork", "forkjoin", "function", "generate", "genvar", "global", "highz0", "highz1", "if", "iff",
        "ifnone", "ignore_bins", "illegal_bins", "implements", "implies", "import", "incdir", "include",
        "initial", "inout", "input", "inside", "instance", "int", "integer", "interconnect", "interface",
        "intersect", "join", "join_any", "join_none", "large", "let", "liblist", "library", "local", "localparam",
        "logic", "longint", "macromodule", "matches", "medium", "modport", "module", "nand", "negedge", "nettype",
        "new", "nmos", "nor", "noshowcancelled", "not", "notif0", "notif1", "null", "or", "output", "package",
        "packed", "parameter", "pmos", "posedge", "primitive", "priority", "program", "property", "protected",
        "pull0", "pull1", "pulldown", "pullup", "pulsestyle_ondetect", "pulsestyle_onevent", "pure", "rand",
        "randc", "randcase", "randsequence", "rcmos", "real", "realtime", "ref", "reg", "reject_on", "release",
        "repeat", "restrict", "return", "rnmos", "rpmos", "rtran", "rtranif0", "rtranif1", "s_always",
        "s_eventually", "s_nexttime", "s_until", "s_until_with", "scalared", "sequence", "shortint", "shortreal",
        "showcancelled", "signed", "small", "soft", "solve", "specify", "specparam", "static", "string", "strong",
        "strong0", "strong1", "struct", "super", "supply0", "supply1", "sync_accept_on", "sync_reject_on",
        "table", "tagged", "task", "this", "throughout", "time", "timeprecision", "timeunit", "tran", "tranif0",
        "tranif1", "tri", "tri0", "tri1", "triand", "trior", "trireg", "type", "typedef", "union", "unique",
        "unique0", "unsigned", "untyped", "use", "uwire", "var", "vectored", "virtual", "void", "wait", "wait_order",
        "wand", "weak", "weak0", "weak1", "while", "wildcard", "wire", "with", "within", "wor", "xnor", "xor"
    };
    for (size_t i = 0; i < sizeof(keywords) / sizeof(keywords[0]); i++)
        if (strcmp(text, keywords[i]) == 0)
            return true;
    return false;
}

static inline bool sn_verilog_is_simple_identifier(const char* text)
{
    assert(text && text[0]);
    unsigned char first = (unsigned char)text[0];
    if (!((first >= 'a' && first <= 'z') || (first >= 'A' && first <= 'Z') || first == '_'))
        return false;
    for (size_t i = 1; text[i]; i++)
    {
        unsigned char c = (unsigned char)text[i];
        if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_' ||
              c == '$'))
            return false;
    }
    return !sn_verilog_is_keyword(text);
}

// Escaped Verilog identifiers terminate at whitespace. SN names containing whitespace or a backslash cannot be emitted
// losslessly and are rejected as construction errors; all other non-simple names and language keywords are escaped.
static inline void sn_write_verilog_identifier(FILE* out, const char* text)
{
    assert(out && text && text[0]);
    if (sn_verilog_is_simple_identifier(text))
    {
        fputs(text, out);
        return;
    }
    for (size_t i = 0; text[i]; i++)
        assert((unsigned char)text[i] > 32 && (unsigned char)text[i] < 127 && text[i] != '\\');
    fputc('\\', out);
    fputs(text, out);
    fputc(' ', out);
}

// Internal names retain the compact historical spelling unless a user name collides with it. The fallback includes the
// module, object, and object role and is checked against the global name manager as well.
static inline void sn_write_verilog_generated_name(FILE* out, const sn_module_t* module, const char* role,
                                                   sn_obj_id_t object)
{
    assert(out && module && role);
    char name[160];
    if (strcmp(role, "obj") == 0)
        snprintf(name, sizeof(name), "_sn_%u", object);
    else
        snprintf(name, sizeof(name), "_sn_%s_%u", role, object);
    if (sn_name_find(&module->design->names, name) == SN_INVALID_ID)
    {
        fputs(name, out);
        return;
    }
    uint32_t suffix = 0;
    do
    {
        int count = snprintf(name, sizeof(name), "__sn_generated_%u_%s_%u_%u", module->id, role, object, suffix++);
        assert(count > 0 && (size_t)count < sizeof(name));
        (void)count;
    } while (sn_name_find(&module->design->names, name) != SN_INVALID_ID);
    fputs(name, out);
}

static inline bool sn_const_bit(const sn_module_t* module, sn_obj_id_t object, uint32_t bit)
{
    assert(bit < sn_obj_width(module, object));
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_CONST0)
        return false;
    if (type == SN_CONST1)
        return bit == 0;
    assert(type == SN_CONST);
    return (sn_const_words(module, object)[bit / 32] >> (bit % 32)) & 1u;
}

static inline void sn_write_verilog_constant_chunk(FILE* out, const sn_module_t* module, sn_obj_id_t object,
                                                   uint32_t offset, uint32_t width)
{
    fprintf(out, "%u'h", width);
    uint32_t nibble_count = (width + 3) / 4;
    for (uint32_t nibble = nibble_count; nibble > 0; nibble--)
    {
        uint32_t digit = 0;
        for (uint32_t bit = 0; bit < 4; bit++)
        {
            uint32_t index = (nibble - 1) * 4 + bit;
            if (index < width && sn_const_bit(module, object, offset + index))
                digit |= 1u << bit;
        }
        fputc("0123456789abcdef"[digit], out);
    }
}

static inline void sn_write_verilog_constant(FILE* out, const sn_module_t* module, sn_obj_id_t object)
{
    uint32_t width = sn_obj_width(module, object);
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_CONST0 || type == SN_CONST1)
    {
        fprintf(out, "%u", width);
        fputc(39, out);
        if (sn_obj_is_signed(module, object))
            fputc(115, out);
        fprintf(out, "d%u", type == SN_CONST1 ? 1u : 0u);
        return;
    }
    assert(type == SN_CONST);
    if (width <= 4096)
    {
        fprintf(out, "%u", width);
        fputc(39, out);
        if (sn_obj_is_signed(module, object))
            fputc(115, out);
        fputc(104, out);
        const uint32_t* words = sn_const_words(module, object);
        uint32_t count = sn_const_word_count(width);
        fprintf(out, "%x", words[count - 1]);
        while (--count)
            fprintf(out, "%08x", words[count - 1]);
        return;
    }

    if (sn_obj_is_signed(module, object))
        fputs("$signed(", out);
    fputs("{\n", out);
    uint32_t remaining = width;
    while (remaining)
    {
        uint32_t chunk_width = remaining > 1024 ? 1024 : remaining;
        uint32_t offset = remaining - chunk_width;
        fputs("    ", out);
        sn_write_verilog_constant_chunk(out, module, object, offset, chunk_width);
        remaining = offset;
        fputs(remaining ? ",\n" : "\n", out);
    }
    fputc(125, out);
    if (sn_obj_is_signed(module, object))
        fputc(41, out);
}

static inline void sn_write_verilog_ref(FILE* out, const sn_module_t* module, sn_obj_id_t object)
{
    assert(object < module->obj_types.size);
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_PI || type == SN_PO)
        sn_write_verilog_identifier(out, sn_obj_name(module, object));
    else if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
        sn_write_verilog_constant(out, module, object);
    else
        sn_write_verilog_generated_name(out, module, "obj", object);
}

static inline void sn_write_verilog_constant_slice(FILE* out, const sn_module_t* module, sn_obj_id_t object,
                                                   const sn_slice_info_t* info, uint32_t width)
{
    assert(info);
    assert(info->left_index >= 0 && info->right_index >= 0);
    assert((uint32_t)info->left_index < sn_obj_width(module, object));
    assert((uint32_t)info->right_index < sn_obj_width(module, object));
    fprintf(out, "%u'h", width);
    uint32_t nibble_count = (width + 3) / 4;
    for (uint32_t nibble = nibble_count; nibble > 0; nibble--)
    {
        uint32_t digit = 0;
        for (uint32_t offset = 0; offset < 4; offset++)
        {
            uint32_t result_bit = (nibble - 1) * 4 + offset;
            if (result_bit >= width)
                continue;
            int64_t source_bit = info->left_index >= info->right_index ? (int64_t)info->right_index + result_bit
                                                                       : (int64_t)info->right_index - result_bit;
            assert(source_bit >= 0 && (uint64_t)source_bit < sn_obj_width(module, object));
            digit |= (uint32_t)sn_const_bit(module, object, (uint32_t)source_bit) << offset;
        }
        fputc("0123456789abcdef"[digit], out);
    }
}

static inline void sn_write_verilog_expression(FILE* out, const sn_module_t* module, sn_obj_id_t object)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    const char* unary_token = sn_verilog_unary_token(type);
    if (unary_token)
    {
        assert(sn_obj_fanin_count(module, object) == 1);
        fputc(40, out);
        fputs(unary_token, out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
        fputc(41, out);
        return;
    }
    const char* token = sn_verilog_binary_token(type);
    if (token)
    {
        assert(sn_obj_fanin_count(module, object) == 2);
        fputc(40, out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
        fprintf(out, " %s ", token);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 1));
        fputc(41, out);
        return;
    }
    if (type == SN_BUF)
    {
        assert(sn_obj_fanin_count(module, object) == 1);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
        return;
    }
    if (type == SN_CAST)
    {
        assert(sn_obj_fanin_count(module, object) == 1);
        fputs(sn_obj_is_signed(module, object) ? "$signed(" : "$unsigned(", out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
        fputc(41, out);
        return;
    }
    if (type == SN_MUX)
    {
        assert(sn_obj_fanin_count(module, object) == SN_MUX_FANIN_COUNT);
        fputc(40, out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, SN_MUX_SELECT));
        fputs(" ? ", out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, SN_MUX_SELECTED));
        fputs(" : ", out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, SN_MUX_DEFAULT));
        fputc(41, out);
        return;
    }
    if (type == SN_BMUX)
    {
        assert(sn_obj_fanin_count(module, object) == SN_BMUX_FANIN_COUNT);
        fputc(40, out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, SN_BMUX_ALTERNATIVES));
        fputs(" >> (", out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, SN_BMUX_SELECT));
        fprintf(out, " * %u))", sn_obj_width(module, object));
        return;
    }
    if (type == SN_PMUX)
    {
        assert(sn_obj_fanin_count(module, object) == SN_PMUX_FANIN_COUNT);
        sn_obj_id_t select = sn_obj_fanin(module, object, SN_PMUX_SELECT);
        sn_obj_id_t alternatives = sn_obj_fanin(module, object, SN_PMUX_ALTERNATIVES);
        uint32_t select_width = sn_obj_width(module, select);
        uint32_t output_width = sn_obj_width(module, object);
        for (uint32_t i = 0; i < select_width; i++)
        {
            fputs("(((", out);
            sn_write_verilog_ref(out, module, select);
            fprintf(out, " >> %u) & 1'd1) ? (", i);
            sn_write_verilog_ref(out, module, alternatives);
            fprintf(out, " >> %u) : ", i * output_width);
        }
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, SN_PMUX_DEFAULT));
        for (uint32_t i = 0; i < select_width; i++)
            fputc(41, out);
        return;
    }
    if (type == SN_CONCAT)
    {
        fputc(123, out);
        uint32_t count = sn_obj_fanin_count(module, object);
        for (uint32_t i = count; i > 0; i--)
        {
            if (i != count)
                fputs(", ", out);
            sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, i - 1));
        }
        fputc(125, out);
        return;
    }
    if (type == SN_REPLICATE)
    {
        assert(sn_obj_fanin_count(module, object) == 1);
        fputc(123, out);
        fprintf(out, "%u", sn_obj_repeat_count(module, object));
        fputc(123, out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
        fputc(125, out);
        fputc(125, out);
        return;
    }
    if (type == SN_SLICE)
    {
        sn_obj_id_t value = sn_obj_fanin(module, object, 0);
        const sn_slice_info_t* info = sn_obj_slice_info(module, object);
        sn_obj_type_t value_type = sn_obj_type(module, value);
        if (value_type == SN_CONST0 || value_type == SN_CONST1 || value_type == SN_CONST)
        {
            sn_write_verilog_constant_slice(out, module, value, info, sn_obj_width(module, object));
            return;
        }
        if (sn_obj_width(module, value) == 1 && info->left_index == 0 && info->right_index == 0)
        {
            sn_write_verilog_ref(out, module, value);
            return;
        }
        if (info->left_index >= info->right_index)
        {
            sn_write_verilog_ref(out, module, value);
            fprintf(out, "[%d:%d]", info->left_index, info->right_index);
        }
        else
        {
            // SN values use LSB-first significance order. For an ascending slice, result bit 0 is value[right],
            // which cannot be expressed as an ascending part-select of SN's normalized [width-1:0] wires.
            fputc('{', out);
            for (int64_t index = info->left_index; index <= info->right_index; index++)
            {
                if (index != info->left_index)
                    fputs(", ", out);
                sn_write_verilog_ref(out, module, value);
                fprintf(out, "[%lld]", (long long)index);
            }
            fputc('}', out);
        }
        return;
    }
    assert(false);
}

static inline sn_obj_id_t sn_module_find_named_type_object(const sn_module_t* module, sn_obj_type_t type,
                                                           sn_name_id_t name)
{
    if (name == SN_INVALID_ID)
        return SN_INVALID_ID;
    for (size_t i = 0; i < module->type_objects[type].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[type], i);
        if (sn_obj_name_id(module, object) == name)
            return object;
    }
    return SN_INVALID_ID;
}

static inline void sn_write_verilog_inst(FILE* out, const sn_module_t* module, sn_obj_id_t inst)
{
    sn_module_id_t child_id = sn_inst_module_id(module, inst);
    const sn_module_t* child = sn_design_get_module_const(module->design, child_id);
    assert(sn_obj_fanin_count(module, inst) == child->type_objects[SN_PI].size);
    fputs("  ", out);
    sn_write_verilog_identifier(out, sn_name_get(&module->design->names, child->name));
    fputc(' ', out);
    sn_write_verilog_generated_name(out, module, "inst", inst);
    fputs(" (", out);
    fputc(10, out);
    size_t connection = 0;
    size_t inout_count = 0;
    for (size_t i = 0; i < child->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t port = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PI], i);
        inout_count += sn_module_find_named_type_object(child, SN_PO, sn_obj_name_id(child, port)) != SN_INVALID_ID;
    }
    size_t connection_count = child->type_objects[SN_PI].size + child->type_objects[SN_PO].size - inout_count;
    for (size_t i = 0; i < child->type_objects[SN_PI].size; i++, connection++)
    {
        sn_obj_id_t port = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PI], i);
        sn_obj_id_t output_port = sn_module_find_named_type_object(child, SN_PO, sn_obj_name_id(child, port));
        fputs("    .", out);
        sn_write_verilog_identifier(out, sn_obj_name(child, port));
        fputc('(', out);
        if (output_port == SN_INVALID_ID)
            sn_write_verilog_ref(out, module, sn_obj_fanin(module, inst, (uint32_t)i));
        else
            sn_write_verilog_ref(out, module,
                                 sn_inst_output(module, inst, sn_obj_type_id(child, output_port)));
        fprintf(out, ")%s", connection + 1 == connection_count ? "" : ",");
        fputc(10, out);
    }
    for (size_t i = 0; i < child->type_objects[SN_PO].size; i++)
    {
        sn_obj_id_t port = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PO], i);
        if (sn_module_find_named_type_object(child, SN_PI, sn_obj_name_id(child, port)) != SN_INVALID_ID)
            continue;
        fputs("    .", out);
        sn_write_verilog_identifier(out, sn_obj_name(child, port));
        fputc('(', out);
        sn_write_verilog_ref(out, module, sn_inst_output(module, inst, (uint32_t)i));
        fprintf(out, ")%s", connection + 1 == connection_count ? "" : ",");
        fputc(10, out);
        connection++;
    }
    fputs("  );", out);
    fputc(10, out);
    for (size_t i = 0; i < child->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t port = sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PI], i);
        sn_obj_id_t output_port = sn_module_find_named_type_object(child, SN_PO, sn_obj_name_id(child, port));
        if (output_port == SN_INVALID_ID)
            continue;
        fputs("  assign ", out);
        sn_write_verilog_ref(out, module,
                             sn_inst_output(module, inst, sn_obj_type_id(child, output_port)));
        fputs(" = ", out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, inst, (uint32_t)i));
        fputs(";\n", out);
    }
}

static inline void sn_write_verilog_lut(FILE* out, const sn_module_t* module, sn_obj_id_t object)
{
    assert(sn_obj_type(module, object) == SN_LUT);
    uint32_t count = sn_obj_fanin_count(module, object);
    uint64_t truth = sn_obj_lut_truth(module, object);
    if (count == 0)
    {
        fputs("  assign ", out);
        sn_write_verilog_generated_name(out, module, "obj", object);
        fprintf(out, " = 1'b%u;\n", (unsigned)(truth & 1));
        return;
    }
    uint32_t truth_bits = UINT32_C(1) << count;
    uint32_t hex_digits = (truth_bits + 3) / 4;
    // A variable bit-select is portable synthesizable Verilog and does not require vendor LUT simulation models.
    // Fanin 0 is the least-significant truth-table index bit, matching the SN_LUT convention.
    fputs("  assign ", out);
    sn_write_verilog_generated_name(out, module, "obj", object);
    fprintf(out, " = %u'h%0*llx >> {", truth_bits, (int)hex_digits, (unsigned long long)truth);
    for (uint32_t i = count; i-- > 0; )
    {
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, i));
        if (i)
            fputs(", ", out);
    }
    fputs("};\n", out);
}

// SN_GATE names created by ABC reconstruction are the current library cell names. Mini-mapping orders each cell's
// fanins in library pin order. Structural Verilog uses the conventional output-first positional cell interface so it
// remains independent of ABC's in-memory Mio pin objects after the SN design has been serialized.
static inline void sn_write_verilog_gate(FILE* out, const sn_module_t* module, sn_obj_id_t object)
{
    assert(sn_obj_type(module, object) == SN_GATE);
    const char* gate_name = sn_obj_name(module, object);
    assert(gate_name);
    fputs("  ", out);
    sn_write_verilog_identifier(out, gate_name);
    fputc(' ', out);
    sn_write_verilog_generated_name(out, module, "gate", object);
    fputs(" (", out);
    sn_write_verilog_generated_name(out, module, "obj", object);
    for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
    {
        fputs(", ", out);
        sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, i));
    }
    fputs(");\n", out);
}

static inline void sn_write_verilog_active_control(FILE* out, const sn_module_t* module, sn_obj_id_t control,
                                                   bool active_low)
{
    if (active_low)
        fputc('!', out);
    sn_write_verilog_ref(out, module, control);
}

static inline void sn_write_verilog_register(FILE* out, const sn_module_t* module, sn_obj_id_t reg_out)
{
    assert(sn_obj_type(module, reg_out) == SN_REG_OUT);
    uint32_t flags = sn_obj_reg_flags(module, reg_out);
    sn_obj_id_t clock = sn_obj_fanin(module, reg_out, SN_REG_CLOCK);
    sn_obj_id_t enable = sn_obj_fanin(module, reg_out, SN_REG_ENABLE);
    sn_obj_id_t set = sn_obj_fanin(module, reg_out, SN_REG_SET);
    sn_obj_id_t reset = sn_obj_fanin(module, reg_out, SN_REG_RESET);
    sn_obj_id_t initial_value = sn_obj_reg_init_data(module, reg_out);
    sn_obj_id_t initial_mask = sn_obj_reg_init_mask(module, reg_out);
    sn_obj_id_t reset_value = sn_obj_fanin(module, reg_out, SN_REG_RESET_VALUE);
    sn_obj_id_t reg_in = sn_obj_pair_in(module, reg_out);
    sn_obj_id_t data = sn_obj_fanin(module, reg_in, 0);
    assert(data != SN_INVALID_ID);
    assert((flags & SN_REG_LATCH) ? clock == SN_INVALID_ID : clock != SN_INVALID_ID);

    if (initial_value != SN_INVALID_ID)
    {
        fputs("  initial begin\n    ", out);
        sn_write_verilog_ref(out, module, reg_out);
        fputs(" = ", out);
        if (initial_mask == SN_INVALID_ID)
            sn_write_verilog_ref(out, module, initial_value);
        else
        {
            uint32_t width = sn_obj_width(module, reg_out);
            fprintf(out, "%u'b", width);
            for (uint32_t bit = width; bit-- > 0;)
                fputc(!sn_const_bit(module, initial_mask, bit) ? 'x'
                      : sn_const_bit(module, initial_value, bit) ? '1'
                                                               : '0',
                      out);
        }
        fputs(";\n  end\n", out);
    }

    if (flags & SN_REG_LATCH)
    {
        assert(enable != SN_INVALID_ID && set == SN_INVALID_ID && reset == SN_INVALID_ID);
        fputs("  always @* begin\n    if (", out);
        sn_write_verilog_ref(out, module, enable);
        fputs(") ", out);
        sn_write_verilog_ref(out, module, reg_out);
        fputs(" <= ", out);
        sn_write_verilog_ref(out, module, data);
        fputs(";\n  end\n", out);
        return;
    }

    fputs("  always @(", out);
    fputs(flags & SN_REG_CLOCK_NEGEDGE ? "negedge " : "posedge ", out);
    sn_write_verilog_ref(out, module, clock);
    if (reset != SN_INVALID_ID && (flags & SN_REG_RESET_ASYNC))
    {
        fputs(flags & SN_REG_RESET_NEGEDGE ? " or negedge " : " or posedge ", out);
        sn_write_verilog_ref(out, module, reset);
    }
    if (set != SN_INVALID_ID && (flags & SN_REG_SET_ASYNC))
    {
        fputs(flags & SN_REG_SET_NEGEDGE ? " or negedge " : " or posedge ", out);
        sn_write_verilog_ref(out, module, set);
    }
    fputs(") begin\n", out);

    bool has_condition = false;
    if (reset != SN_INVALID_ID)
    {
        fputs("    if (", out);
        sn_write_verilog_active_control(out, module, reset, flags & SN_REG_RESET_NEGEDGE);
        fputs(") ", out);
        sn_write_verilog_ref(out, module, reg_out);
        fputs(" <= ", out);
        if (reset_value == SN_INVALID_ID)
            fprintf(out, "%u'd0", sn_obj_width(module, reg_out));
        else
            sn_write_verilog_ref(out, module, reset_value);
        fputs(";\n", out);
        has_condition = true;
    }
    if (set != SN_INVALID_ID)
    {
        fputs(has_condition ? "    else if (" : "    if (", out);
        sn_write_verilog_active_control(out, module, set, flags & SN_REG_SET_NEGEDGE);
        fputs(") ", out);
        sn_write_verilog_ref(out, module, reg_out);
        fprintf(out, " <= {%u{1'b1}};\n", sn_obj_width(module, reg_out));
        has_condition = true;
    }
    if (enable != SN_INVALID_ID)
    {
        fputs(has_condition ? "    else if (" : "    if (", out);
        sn_write_verilog_ref(out, module, enable);
        fputs(") ", out);
        sn_write_verilog_ref(out, module, reg_out);
        fputs(" <= ", out);
        sn_write_verilog_ref(out, module, data);
        fputs(";\n", out);
    }
    else
    {
        fputs(has_condition ? "    else " : "    ", out);
        sn_write_verilog_ref(out, module, reg_out);
        fputs(" <= ", out);
        sn_write_verilog_ref(out, module, data);
        fputs(";\n", out);
    }
    fputs("  end\n", out);
}

static inline void sn_write_verilog_memory_read(FILE* out, const sn_module_t* module, sn_obj_id_t read)
{
    assert(sn_obj_type(module, read) == SN_MEM_READ);
    sn_obj_id_t memory = sn_obj_fanin(module, read, SN_MEM_READ_MEMORY);
    sn_obj_id_t clock = sn_obj_fanin(module, read, SN_MEM_READ_CLOCK);
    sn_obj_id_t enable = sn_obj_fanin(module, read, SN_MEM_READ_ENABLE);
    sn_obj_id_t address = sn_obj_fanin(module, read, SN_MEM_READ_ADDRESS);
    assert(sn_obj_type(module, memory) == SN_MEM_OUT);
    assert(clock != SN_INVALID_ID || enable == SN_INVALID_ID);
    if (clock == SN_INVALID_ID)
        fputs("  assign ", out);
    else
    {
        fputs("  always @(posedge ", out);
        sn_write_verilog_ref(out, module, clock);
        fputs(") begin\n    ", out);
        if (enable != SN_INVALID_ID)
        {
            fputs("if (", out);
            sn_write_verilog_ref(out, module, enable);
            fputs(") ", out);
        }
    }
    sn_write_verilog_ref(out, module, read);
    fputs(clock == SN_INVALID_ID ? " = " : " <= ", out);
    sn_write_verilog_generated_name(out, module, "mem", memory);
    fputc('[', out);
    sn_write_verilog_ref(out, module, address);
    fputs(clock == SN_INVALID_ID ? "];\n" : "];\n  end\n", out);
}

static inline void sn_write_verilog_memory_init(FILE* out, const sn_module_t* module, sn_obj_id_t memory)
{
    assert(sn_obj_type(module, memory) == SN_MEM_OUT);
    sn_obj_id_t data = sn_obj_mem_init_data(module, memory);
    sn_obj_id_t mask = sn_obj_mem_init_mask(module, memory);
    if (data == SN_INVALID_ID)
        return;

    uint32_t width = sn_obj_width(module, memory);
    uint32_t depth = sn_obj_mem_depth(module, memory);
    fputs("  initial begin\n", out);
    for (uint32_t entry = 0; entry < depth; entry++)
    {
        uint64_t offset = (uint64_t)entry * width;
        bool has_valid_bit = mask == SN_INVALID_ID;
        if (mask != SN_INVALID_ID)
            for (uint32_t bit = 0; bit < width; bit++)
                has_valid_bit = has_valid_bit || sn_const_bit(module, mask, (uint32_t)offset + bit);
        if (!has_valid_bit)
            continue;

        fputs("    ", out);
        sn_write_verilog_generated_name(out, module, "mem", memory);
        fprintf(out, "[%u] = %u'b", entry, width);
        for (uint32_t bit = width; bit-- > 0;)
        {
            uint32_t init_bit = (uint32_t)offset + bit;
            if (mask != SN_INVALID_ID && !sn_const_bit(module, mask, init_bit))
                fputc('x', out);
            else
                fputc(sn_const_bit(module, data, init_bit) ? '1' : '0', out);
        }
        fputs(";\n", out);
    }
    fputs("  end\n", out);
}

static inline void sn_write_verilog_memory_write(FILE* out, const sn_module_t* module, sn_obj_id_t write,
                                                 sn_obj_id_t memory)
{
    assert(sn_obj_type(module, write) == SN_MEM_WRITE);
    assert(sn_obj_type(module, memory) == SN_MEM_OUT);
    sn_obj_id_t clock = sn_obj_fanin(module, write, SN_MEM_WRITE_CLOCK);
    sn_obj_id_t enable = sn_obj_fanin(module, write, SN_MEM_WRITE_ENABLE);
    sn_obj_id_t data = sn_obj_fanin(module, write, SN_MEM_WRITE_DATA);
    sn_obj_id_t address = sn_obj_fanin(module, write, SN_MEM_WRITE_ADDRESS);
    assert(clock != SN_INVALID_ID && data != SN_INVALID_ID && address != SN_INVALID_ID);
    fputs("  always @(posedge ", out);
    sn_write_verilog_ref(out, module, clock);
    fputs(") begin\n", out);
    if (enable != SN_INVALID_ID)
    {
        fputs("    if (", out);
        sn_write_verilog_ref(out, module, enable);
        fputs(")\n      ", out);
    }
    else
        fputs("    ", out);
    sn_write_verilog_generated_name(out, module, "mem", memory);
    fputc('[', out);
    sn_write_verilog_ref(out, module, address);
    fputs("] <= ", out);
    sn_write_verilog_ref(out, module, data);
    fputs(";\n  end\n", out);
}

static inline void sn_module_write_verilog_as(FILE* out, const sn_module_t* module, const char* emitted_name)
{
    assert(out);
    assert(module);
    assert(emitted_name);
    size_t write_count = module->type_objects[SN_MEM_WRITE].size;
    sn_obj_id_t* write_memories = write_count ? (sn_obj_id_t*)malloc(write_count * sizeof(sn_obj_id_t)) : NULL;
    assert(write_memories || !write_count);
    for (size_t i = 0; i < write_count; i++)
        write_memories[i] = SN_INVALID_ID;
    for (size_t i = 0; i < module->type_objects[SN_MEM_IN].size; i++)
    {
        sn_obj_id_t mem_in = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_IN], i);
        sn_obj_id_t memory = sn_obj_pair_out(module, mem_in);
        for (uint32_t j = 0; j < sn_obj_fanin_count(module, mem_in); j++)
        {
            sn_obj_id_t write = sn_obj_fanin(module, mem_in, j);
            assert(sn_obj_type(module, write) == SN_MEM_WRITE);
            uint32_t write_id = sn_obj_type_id(module, write);
            assert(write_id < write_count && write_memories[write_id] == SN_INVALID_ID);
            write_memories[write_id] = memory;
        }
    }
    if (sn_module_is_blackbox(module))
        fputs("(* blackbox *) ", out);
    fputs("module ", out);
    sn_write_verilog_identifier(out, emitted_name);
    fputs(" (", out);
    fputc(10, out);
    size_t inout_count = 0;
    for (size_t i = 0; i < module->type_objects[SN_PI].size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_PI], i);
        inout_count +=
            sn_module_find_named_type_object(module, SN_PO, sn_obj_name_id(module, object)) != SN_INVALID_ID;
    }
    size_t port_count = module->type_objects[SN_PI].size + module->type_objects[SN_PO].size - inout_count;
    size_t port_index = 0;
    for (uint32_t type = SN_PI; type <= SN_PO; type++)
        for (size_t i = 0; i < module->type_objects[type].size; i++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[type], i);
            if (type == SN_PO &&
                sn_module_find_named_type_object(module, SN_PI, sn_obj_name_id(module, object)) != SN_INVALID_ID)
                continue;
            fputs("  ", out);
            sn_write_verilog_identifier(out, sn_obj_name(module, object));
            fputs(port_index + 1 == port_count ? "" : ",", out);
            fputc(10, out);
            port_index++;
        }
    fputs(");", out);
    fputc(10, out);

    for (uint32_t type = SN_PI; type <= SN_PO; type++)
        for (size_t i = 0; i < module->type_objects[type].size; i++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[type], i);
            sn_obj_id_t matching = sn_module_find_named_type_object(
                module, type == SN_PI ? SN_PO : SN_PI, sn_obj_name_id(module, object));
            if (type == SN_PO && matching != SN_INVALID_ID)
                continue;
            fprintf(out, "  %s wire ", matching != SN_INVALID_ID ? "inout" : type == SN_PI ? "input" : "output");
            sn_write_verilog_range(out, module, object);
            sn_write_verilog_identifier(out, sn_obj_name(module, object));
            fputc(';', out);
            fputc(10, out);
        }

    if (sn_module_is_blackbox(module))
    {
        fputs("endmodule\n\n", out);
        free(write_memories);
        return;
    }

    for (sn_obj_id_t object = 0; object < module->obj_types.size; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if (type == SN_PI || type == SN_PO || type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
            continue;
        if (type == SN_INST)
        {
            sn_module_id_t child_id = sn_inst_module_id(module, object);
            if (sn_design_module_output_count(module->design, child_id) > 1)
                continue;
        }
        if (type == SN_MEM_OUT)
        {
            fputs("  reg ", out);
            sn_write_verilog_range(out, module, object);
            sn_write_verilog_generated_name(out, module, "mem", object);
            fprintf(out, " [0:%u];", sn_obj_mem_depth(module, object) - 1);
            fputc(10, out);
            continue;
        }
        if (type == SN_MEM_IN || type == SN_MEM_WRITE)
            continue;
        bool procedural = type == SN_REG_OUT ||
                          (type == SN_MEM_READ && sn_obj_fanin(module, object, SN_MEM_READ_CLOCK) != SN_INVALID_ID);
        fputs(procedural ? "  reg " : "  wire ", out);
        sn_write_verilog_range(out, module, object);
        sn_write_verilog_generated_name(out, module, "obj", object);
        fputc(';', out);
        sn_name_id_t name = sn_obj_name_id(module, object);
        if (name != SN_INVALID_ID)
            fprintf(out, "  // %s", sn_name_get(&module->design->names, name));
        fputc(10, out);
    }
    fputc(10, out);

    for (size_t i = 0; i < module->type_objects[SN_MEM_OUT].size; i++)
    {
        sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_OUT], i);
        sn_write_verilog_memory_init(out, module, memory);
    }

    for (sn_obj_id_t object = 0; object < module->obj_types.size; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if (type == SN_PO)
        {
            fputs("  assign ", out);
            sn_write_verilog_ref(out, module, object);
            fputs(" = ", out);
            sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
            fputs(";", out);
            fputc(10, out);
        }
        else if (type == SN_INST)
            sn_write_verilog_inst(out, module, object);
        else if (type == SN_REG_OUT)
            sn_write_verilog_register(out, module, object);
        else if (type == SN_REG_IN)
        {
            fputs("  assign ", out);
            sn_write_verilog_ref(out, module, object);
            fputs(" = ", out);
            sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
            fputs(";\n", out);
        }
        else if (type == SN_LOOP_OUT || type == SN_LOOP_IN)
        {
            // Loop pairs are transparent buffers. Their OUT half is treated as a source only by graph traversal.
            fputs("  assign ", out);
            sn_write_verilog_ref(out, module, object);
            fputs(" = ", out);
            sn_write_verilog_ref(out, module, sn_obj_fanin(module, object, 0));
            fputs(";\n", out);
        }
        else if (type == SN_MEM_READ)
            sn_write_verilog_memory_read(out, module, object);
        else if (type == SN_MEM_WRITE)
        {
            sn_obj_id_t memory = write_memories[sn_obj_type_id(module, object)];
            assert(memory != SN_INVALID_ID);
            sn_write_verilog_memory_write(out, module, object, memory);
        }
        else if (type == SN_LUT)
            sn_write_verilog_lut(out, module, object);
        else if (type == SN_GATE)
            sn_write_verilog_gate(out, module, object);
        else if (sn_obj_type_is_operator(type))
        {
            fputs("  assign ", out);
            sn_write_verilog_ref(out, module, object);
            fputs(" = ", out);
            sn_write_verilog_expression(out, module, object);
            fputs(";", out);
            fputc(10, out);
        }
    }
    fputs("endmodule", out);
    fputc(10, out);
    fputc(10, out);
    free(write_memories);
}

static inline void sn_module_write_verilog(FILE* out, const sn_module_t* module)
{
    assert(module);
    sn_module_write_verilog_as(out, module, sn_name_get(&module->design->names, module->name));
}

static inline void sn_design_write_module_verilog(FILE* out, const sn_design_t* design, sn_module_id_t module_id,
                                                  const char* emitted_name)
{
    assert(out);
    assert(design);
    assert(module_id < design->modules.size);
    const sn_module_t* module = sn_design_get_module_const(design, module_id);
    sn_module_write_verilog_as(out, module,
                               emitted_name ? emitted_name : sn_name_get(&design->names, module->name));
}

static inline void sn_design_write_module_verilog_file(const sn_design_t* design, sn_module_id_t module_id,
                                                       const char* emitted_name, const char* path)
{
    assert(path);
    FILE* out = fopen(path, "w");
    assert(out);
    sn_design_write_module_verilog(out, design, module_id, emitted_name);
    fclose(out);
}

static inline void sn_design_write_module_verilog_deps_rec(FILE* out, const sn_design_t* design,
                                                           sn_module_id_t module_id, sn_module_id_t root,
                                                           bool* active, bool* written)
{
    assert(out && design && module_id < design->modules.size && active && written);
    if (written[module_id])
        return;
    assert(!active[module_id]);
    active[module_id] = true;
    const sn_module_t* module = sn_design_get_module_const(design, module_id);
    for (size_t i = 0; i < module->inst_modules.size; i++)
        sn_design_write_module_verilog_deps_rec(
            out, design, sn_vec_at(sn_module_id_t, &module->inst_modules, i), root, active, written);
    active[module_id] = false;
    written[module_id] = true;
    if (module_id != root)
        sn_module_write_verilog(out, module);
}

// Writes one selected module plus only the module definitions reachable from
// its insts. Dependencies precede the selected module, whose emitted name
// may differ from its internal SN name. This is useful for a collapsed design
// that intentionally retains technology primitive insts.
static inline void sn_design_write_module_verilog_with_deps(FILE* out, const sn_design_t* design,
                                                            sn_module_id_t module_id, const char* emitted_name)
{
    assert(out && design && module_id < design->modules.size);
    bool* active = (bool*)calloc(design->modules.size, sizeof(bool));
    bool* written = (bool*)calloc(design->modules.size, sizeof(bool));
    assert(active && written);
    sn_design_write_module_verilog_deps_rec(out, design, module_id, module_id, active, written);
    sn_design_write_module_verilog(out, design, module_id, emitted_name);
    free(active);
    free(written);
}

static inline void sn_design_write_module_verilog_with_deps_file(const sn_design_t* design,
                                                                 sn_module_id_t module_id,
                                                                 const char* emitted_name, const char* path)
{
    assert(path);
    FILE* out = fopen(path, "w");
    assert(out);
    sn_design_write_module_verilog_with_deps(out, design, module_id, emitted_name);
    fclose(out);
}

static inline void sn_design_write_verilog(FILE* out, const sn_design_t* design)
{
    assert(out);
    assert(design);
    for (size_t i = 0; i < design->modules.size; i++)
        sn_module_write_verilog(out, sn_design_get_module_const(design, (sn_module_id_t)i));
}

static inline void sn_design_write_verilog_file(const sn_design_t* design, const char* path)
{
    assert(design);
    assert(path);
    FILE* out = fopen(path, "w");
    assert(out);
    sn_design_write_verilog(out, design);
    fclose(out);
}

// SN binary format
// ----------------
//
// The binary representation is a versioned, little-endian semantic dump, not
// a native-memory image. Vector capacities, pointers, and name hash buckets are
// process-local details and are reconstructed when reading. IDs, vector sizes,
// names, constants, object attributes, type-specific attributes, optional
// fanout caches, and duplication maps are preserved exactly.
//
// File order is:
//   header; names; constant words; module count; module records.
// A module record follows sn_module_t's semantic field order:
//   module flags; core object vectors; fanins; type-object vectors;
//   type-specific vectors; fanout vectors; copy map.
//
// Size fields are unsigned 64-bit values. IDs, flags, enum values, and stored
// data words are unsigned 32-bit values. A format change must increment the
// version below.

#define SN_BINARY_FORMAT_VERSION 6u
#define SN_BINARY_MIN_READ_VERSION 5u

// The format version covers field-layout changes. This signature additionally binds every serialized object type to
// its numeric value, so reordering the enum cannot silently reinterpret an otherwise same-sized binary design.
static inline uint32_t sn_binary_layout_signature(void)
{
    static const sn_obj_type_t types[] = {
        SN_NONE,       SN_PI,          SN_PO,          SN_CONST0,      SN_CONST1,      SN_CONST,
        SN_BUF,        SN_FAN,         SN_INST,        SN_REG_OUT,     SN_REG_IN,      SN_MEM_OUT,
        SN_MEM_IN,     SN_MEM_READ,    SN_MEM_WRITE,   SN_LOOP_OUT,    SN_LOOP_IN,     SN_POS,
        SN_NEG,        SN_BIT_NOT,     SN_LOG_NOT,     SN_REDUCE_AND,  SN_REDUCE_NAND, SN_REDUCE_OR,
        SN_REDUCE_NOR, SN_REDUCE_XOR,  SN_REDUCE_XNOR, SN_ADD,         SN_SUB,         SN_MUL,
        SN_DIV,        SN_MOD,         SN_POW,         SN_BIT_AND,     SN_BIT_OR,      SN_BIT_XOR,
        SN_BIT_XNOR,   SN_LOG_AND,     SN_LOG_OR,      SN_EQ,          SN_NE,          SN_CASE_EQ,
        SN_CASE_NE,    SN_WILDCARD_EQ, SN_WILDCARD_NE, SN_LT,          SN_LE,          SN_GT,
        SN_GE,         SN_SHL,         SN_SHR,         SN_ASHL,        SN_ASHR,         SN_MUX,
        SN_BMUX,       SN_PMUX,        SN_CONCAT,      SN_REPLICATE,   SN_SLICE,       SN_CAST,
        SN_LUT,        SN_GATE};
    uint32_t hash = UINT32_C(2166136261);
    for (size_t i = 0; i < sizeof(types) / sizeof(types[0]); i++)
    {
        hash ^= types[i];
        hash *= UINT32_C(16777619);
        hash ^= (uint32_t)i;
        hash *= UINT32_C(16777619);
    }
    return hash;
}

typedef struct sn_binary_writer_t
{
    FILE* out;
    bool valid;
} sn_binary_writer_t;

static inline sn_binary_writer_t sn_binary_writer_start(FILE* out)
{
    sn_binary_writer_t writer = {out, out != NULL};
    return writer;
}

static inline bool sn_binary_write_bytes(sn_binary_writer_t* writer, const void* data, size_t size)
{
    assert(data || !size);
    if (!writer || !writer->valid)
        return false;
    if (size && fwrite(data, 1, size, writer->out) != size)
        writer->valid = false;
    return writer->valid;
}

typedef struct sn_binary_reader_t
{
    FILE* in;
    uint64_t remaining;
    bool valid;
} sn_binary_reader_t;

static inline sn_binary_reader_t sn_binary_reader_start(FILE* in)
{
    sn_binary_reader_t reader = {in, UINT64_MAX, in != NULL};
#if defined(_WIN32)
    __int64 position;
#else
    long position;
#endif
    if (!in)
        return reader;
#if defined(_WIN32)
    position = _ftelli64(in);
    if (position >= 0 && _fseeki64(in, 0, SEEK_END) == 0)
    {
        __int64 end = _ftelli64(in);
        if (end >= position && _fseeki64(in, position, SEEK_SET) == 0)
#else
    position = ftell(in);
    if (position >= 0 && fseek(in, 0, SEEK_END) == 0)
    {
        long end = ftell(in);
        if (end >= position && fseek(in, position, SEEK_SET) == 0)
#endif
            reader.remaining = (uint64_t)(end - position);
        else
            reader.valid = false;
    }
    else
        clearerr(in);
    return reader;
}

static inline bool sn_binary_read_bytes(sn_binary_reader_t* reader, void* data, size_t size)
{
    assert(data || !size);
    if (!reader || !reader->valid || (uint64_t)size > reader->remaining)
    {
        if (reader)
            reader->valid = false;
        return false;
    }
    if (size && fread(data, 1, size, reader->in) != size)
    {
        reader->valid = false;
        return false;
    }
    if (reader->remaining != UINT64_MAX)
        reader->remaining -= size;
    return true;
}

static inline void sn_binary_write_u32(sn_binary_writer_t* writer, uint32_t value)
{
    uint8_t bytes[4];
    for (uint32_t i = 0; i < 4; i++)
        bytes[i] = (uint8_t)(value >> (8 * i));
    sn_binary_write_bytes(writer, bytes, sizeof(bytes));
}

static inline uint32_t sn_binary_read_u32(sn_binary_reader_t* reader)
{
    uint8_t bytes[4] = {0};
    sn_binary_read_bytes(reader, bytes, sizeof(bytes));
    uint32_t value = 0;
    for (uint32_t i = 0; i < 4; i++)
        value |= (uint32_t)bytes[i] << (8 * i);
    return value;
}

static inline void sn_binary_write_u64(sn_binary_writer_t* writer, uint64_t value)
{
    uint8_t bytes[8];
    for (uint32_t i = 0; i < 8; i++)
        bytes[i] = (uint8_t)(value >> (8 * i));
    sn_binary_write_bytes(writer, bytes, sizeof(bytes));
}

static inline uint64_t sn_binary_read_u64(sn_binary_reader_t* reader)
{
    uint8_t bytes[8] = {0};
    sn_binary_read_bytes(reader, bytes, sizeof(bytes));
    uint64_t value = 0;
    for (uint32_t i = 0; i < 8; i++)
        value |= (uint64_t)bytes[i] << (8 * i);
    return value;
}

static inline size_t sn_binary_read_size(sn_binary_reader_t* reader)
{
    uint64_t size = sn_binary_read_u64(reader);
    if (size > SIZE_MAX)
    {
        reader->valid = false;
        return 0;
    }
    return (size_t)size;
}

static inline bool sn_binary_read_vec_size(sn_binary_reader_t* reader, size_t element_bytes, size_t* size)
{
    *size = sn_binary_read_size(reader);
    if (!reader->valid || *size >= SN_INVALID_ID || (element_bytes && *size > reader->remaining / element_bytes))
    {
        reader->valid = false;
        return false;
    }
    return true;
}

static inline void sn_binary_write_u32_vec(sn_binary_writer_t* writer, const sn_vec_t* vec)
{
    assert(vec);
    sn_binary_write_u64(writer, vec->size);
#if defined(_WIN32) || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
    sn_binary_write_bytes(writer, vec->data, vec->size * sizeof(uint32_t));
#else
    for (size_t i = 0; i < vec->size; i++)
        sn_binary_write_u32(writer, sn_vec_at(uint32_t, vec, i));
#endif
}

static inline void sn_binary_read_u32_vec(sn_binary_reader_t* reader, sn_vec_t* vec)
{
    assert(vec);
    size_t size;
    if (!sn_binary_read_vec_size(reader, 4, &size))
        return;
    sn_vec_resize(uint32_t, vec, size);
#if defined(_WIN32) || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
    sn_binary_read_bytes(reader, vec->data, size * sizeof(uint32_t));
#else
    for (size_t i = 0; i < size; i++)
        sn_vec_at(uint32_t, vec, i) = sn_binary_read_u32(reader);
#endif
}

// Fanin counts use 16 bits in memory but retain their historical 32-bit binary representation.
static inline void sn_binary_write_fanin_count_vec(sn_binary_writer_t* writer, const sn_vec_t* vec)
{
    assert(vec);
    sn_binary_write_u64(writer, vec->size);
    for (size_t i = 0; i < vec->size; i++)
        sn_binary_write_u32(writer, sn_vec_at(sn_fanin_count_t, vec, i));
}

static inline void sn_binary_read_fanin_count_vec(sn_binary_reader_t* reader, sn_vec_t* vec)
{
    assert(vec);
    size_t size;
    if (!sn_binary_read_vec_size(reader, 4, &size))
        return;
    sn_vec_resize(sn_fanin_count_t, vec, size);
    for (size_t i = 0; i < size; i++)
    {
        uint32_t count = sn_binary_read_u32(reader);
        if (count > UINT16_MAX)
        {
            reader->valid = false;
            return;
        }
        sn_vec_at(sn_fanin_count_t, vec, i) = (sn_fanin_count_t)count;
    }
}

static inline void sn_binary_write_u64_vec(sn_binary_writer_t* writer, const sn_vec_t* vec)
{
    assert(vec);
    sn_binary_write_u64(writer, vec->size);
#if defined(_WIN32) || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
    sn_binary_write_bytes(writer, vec->data, vec->size * sizeof(uint64_t));
#else
    for (size_t i = 0; i < vec->size; i++)
        sn_binary_write_u64(writer, sn_vec_at(uint64_t, vec, i));
#endif
}

static inline void sn_binary_read_u64_vec(sn_binary_reader_t* reader, sn_vec_t* vec)
{
    assert(vec);
    size_t size;
    if (!sn_binary_read_vec_size(reader, 8, &size))
        return;
    sn_vec_resize(uint64_t, vec, size);
#if defined(_WIN32) || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
    sn_binary_read_bytes(reader, vec->data, size * sizeof(uint64_t));
#else
    for (size_t i = 0; i < size; i++)
        sn_vec_at(uint64_t, vec, i) = sn_binary_read_u64(reader);
#endif
}

static inline void sn_binary_write_type_vec(sn_binary_writer_t* writer, const sn_vec_t* vec)
{
    assert(vec);
    sn_binary_write_u64(writer, vec->size);
    for (size_t i = 0; i < vec->size; i++)
        sn_binary_write_u32(writer, (uint32_t)sn_vec_at(sn_obj_type_t, vec, i));
}

static inline void sn_binary_read_type_vec(sn_binary_reader_t* reader, sn_vec_t* vec)
{
    assert(vec);
    size_t size;
    if (!sn_binary_read_vec_size(reader, 4, &size))
        return;
    sn_vec_resize(sn_obj_type_t, vec, size);
    for (size_t i = 0; i < size; i++)
    {
        uint32_t type = sn_binary_read_u32(reader);
        if (type >= SN_OBJ_TYPE_COUNT)
        {
            reader->valid = false;
            return;
        }
        sn_vec_at(sn_obj_type_t, vec, i) = (sn_obj_type_t)type;
    }
}

static inline void sn_binary_write_slice_vec(sn_binary_writer_t* writer, const sn_vec_t* vec)
{
    assert(vec);
    sn_binary_write_u64(writer, vec->size);
    for (size_t i = 0; i < vec->size; i++)
    {
        const sn_slice_info_t* info = &sn_vec_at(sn_slice_info_t, vec, i);
        sn_binary_write_u32(writer, (uint32_t)info->left_index);
        sn_binary_write_u32(writer, (uint32_t)info->right_index);
        sn_binary_write_u32(writer, info->flags);
    }
}

static inline void sn_binary_read_slice_vec(sn_binary_reader_t* reader, sn_vec_t* vec)
{
    assert(vec);
    size_t size;
    if (!sn_binary_read_vec_size(reader, 12, &size))
        return;
    sn_vec_resize(sn_slice_info_t, vec, size);
    for (size_t i = 0; i < size; i++)
    {
        sn_slice_info_t* info = &sn_vec_at(sn_slice_info_t, vec, i);
        info->left_index = (int32_t)sn_binary_read_u32(reader);
        info->right_index = (int32_t)sn_binary_read_u32(reader);
        info->flags = sn_binary_read_u32(reader);
    }
}

static inline void sn_module_assert_valid(const sn_module_t* module)
{
    assert(module);
    assert(module->design);
    assert(module->id < module->design->modules.size);
    assert(sn_design_get_module_const(module->design, module->id) == module);
    assert(module->name < module->design->names.names.size);
    assert((module->flags & ~SN_MODULE_ALL_FLAGS) == 0);

    size_t object_count = module->obj_types.size;
    assert(object_count < SN_INVALID_ID);
    assert(module->width_signed.size == object_count);
    assert(module->fanin_counts.size == object_count);
    assert(module->fanin_offsets.size == object_count);
    assert(module->type_ids.size == object_count);
    assert(module->name_ids.size == object_count);

    size_t expected_fanin_offset = 0;
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_vec_at(sn_obj_type_t, &module->obj_types, object);
        uint32_t type_id = sn_vec_at(uint32_t, &module->type_ids, object);
        uint32_t fanin_count = sn_obj_fanin_count(module, object);
        uint32_t fanin_offset = sn_vec_at(uint32_t, &module->fanin_offsets, object);
        uint32_t name = sn_vec_at(uint32_t, &module->name_ids, object);
        assert(type > SN_NONE && type < SN_OBJ_TYPE_COUNT);
        assert(type_id < module->type_objects[type].size);
        assert(sn_vec_at(sn_obj_id_t, &module->type_objects[type], type_id) == object);
        assert(fanin_offset == expected_fanin_offset);
        assert(expected_fanin_offset + fanin_count <= module->fanins.size);
        assert(name == SN_INVALID_ID || name < module->design->names.names.size);
        for (uint32_t i = 0; i < fanin_count; i++)
        {
            sn_obj_id_t fanin = sn_vec_at(sn_obj_id_t, &module->fanins, fanin_offset + i);
            assert(fanin < object_count ||
                   (fanin == SN_INVALID_ID && sn_obj_fanin_may_be_invalid(module, type, i)));
        }
        expected_fanin_offset += fanin_count;
    }
    assert(expected_fanin_offset == module->fanins.size);

    if (sn_module_is_blackbox(module))
        for (sn_obj_id_t object = 0; object < object_count; object++)
        {
            sn_obj_type_t type = sn_obj_type(module, object);
            assert(type == SN_PI || type == SN_PO);
            if (type == SN_PO)
                assert(sn_obj_fanin_count(module, object) == 1 &&
                       sn_obj_fanin(module, object, 0) == SN_INVALID_ID);
        }

    for (uint32_t type = 0; type < SN_OBJ_TYPE_COUNT; type++)
        for (uint32_t type_id = 0; type_id < module->type_objects[type].size; type_id++)
        {
            sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[type], type_id);
            assert(object < object_count);
            assert(sn_vec_at(sn_obj_type_t, &module->obj_types, object) == (sn_obj_type_t)type);
            assert(sn_vec_at(uint32_t, &module->type_ids, object) == type_id);
        }

    assert(module->reg_flags.size == module->type_objects[SN_REG_OUT].size);
    assert(module->mem_depths.size == module->type_objects[SN_MEM_OUT].size);
    assert(module->inst_modules.size == module->type_objects[SN_INST].size);
    assert(module->fan_insts.size == module->type_objects[SN_FAN].size);
    assert(module->slice_infos.size == module->type_objects[SN_SLICE].size);
    assert(module->repeat_counts.size == module->type_objects[SN_REPLICATE].size);
    assert(module->const_word_offsets.size == module->type_objects[SN_CONST].size);
    assert(module->lut_truths.size == module->type_objects[SN_LUT].size);
    assert(module->gate_ids.size == module->type_objects[SN_GATE].size);
    assert(module->type_objects[SN_REG_OUT].size == module->type_objects[SN_REG_IN].size);
    assert(module->type_objects[SN_MEM_OUT].size == module->type_objects[SN_MEM_IN].size);
    assert(module->type_objects[SN_LOOP_OUT].size == module->type_objects[SN_LOOP_IN].size);

    for (size_t i = 0; i < module->reg_flags.size; i++)
    {
        assert((sn_vec_at(uint32_t, &module->reg_flags, i) & ~SN_REG_FLAGS_ALL) == 0);
        sn_obj_id_t reg = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], i);
        assert(sn_obj_fanin_count(module, reg) == SN_REG_FANIN_COUNT);
        sn_obj_id_t data = sn_obj_reg_init_data(module, reg);
        sn_obj_id_t mask = sn_obj_reg_init_mask(module, reg);
        assert(data != SN_INVALID_ID || mask == SN_INVALID_ID);
        if (data != SN_INVALID_ID)
        {
            sn_obj_type_t type = sn_obj_type(module, data);
            assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
            assert(sn_obj_width(module, data) == sn_obj_width(module, reg));
        }
        if (mask != SN_INVALID_ID)
        {
            sn_obj_type_t type = sn_obj_type(module, mask);
            assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
            assert(sn_obj_width(module, mask) == sn_obj_width(module, reg));
        }
    }
    for (size_t i = 0; i < module->mem_depths.size; i++)
    {
        assert(sn_vec_at(uint32_t, &module->mem_depths, i));
        sn_obj_id_t memory = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_MEM_OUT], i);
        assert(sn_obj_fanin_count(module, memory) == SN_MEM_OUT_FANIN_COUNT);
        assert(sn_obj_fanin(module, memory, SN_MEM_STATE) == sn_obj_pair_in(module, memory));
        sn_obj_id_t data = sn_obj_mem_init_data(module, memory);
        sn_obj_id_t mask = sn_obj_mem_init_mask(module, memory);
        assert(data != SN_INVALID_ID || mask == SN_INVALID_ID);
        uint32_t init_width = sn_obj_mem_init_width(module, memory);
        if (data != SN_INVALID_ID)
        {
            sn_obj_type_t type = sn_obj_type(module, data);
            assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
            assert(sn_obj_width(module, data) == init_width);
        }
        if (mask != SN_INVALID_ID)
        {
            sn_obj_type_t type = sn_obj_type(module, mask);
            assert(type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST);
            assert(sn_obj_width(module, mask) == init_width);
        }
    }
    for (size_t i = 0; i < module->inst_modules.size; i++)
        assert(sn_vec_at(sn_module_id_t, &module->inst_modules, i) < module->design->modules.size);
    for (size_t i = 0; i < module->slice_infos.size; i++)
        assert((sn_vec_at(sn_slice_info_t, &module->slice_infos, i).flags & ~SN_SLICE_DESCENDING) == 0);
    for (size_t i = 0; i < module->repeat_counts.size; i++)
        assert(sn_vec_at(uint32_t, &module->repeat_counts, i));

    for (size_t i = 0; i < module->const_word_offsets.size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_CONST], i);
        uint32_t offset = sn_vec_at(uint32_t, &module->const_word_offsets, i);
        assert((size_t)offset + sn_const_word_count(sn_obj_width(module, object)) <=
               module->design->constant_words.size);
    }
    for (size_t i = 0; i < module->lut_truths.size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_LUT], i);
        uint32_t fanin_count = sn_obj_fanin_count(module, object);
        assert(sn_obj_width(module, object) == 1 && !sn_obj_is_signed(module, object) && fanin_count <= 6);
        for (uint32_t k = 0; k < fanin_count; k++)
            assert(sn_obj_width(module, sn_obj_fanin(module, object, k)) == 1);
        if (fanin_count < 6)
            assert((sn_obj_lut_truth(module, object) >> (UINT32_C(1) << fanin_count)) == 0);
    }
    for (size_t i = 0; i < module->gate_ids.size; i++)
    {
        sn_obj_id_t object = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_GATE], i);
        assert(sn_obj_width(module, object) == 1);
        assert(sn_obj_gate_id(module, object) != SN_INVALID_ID);
        for (uint32_t j = 0; j < sn_obj_fanin_count(module, object); j++)
            assert(sn_obj_width(module, sn_obj_fanin(module, object, j)) == 1);
    }

    for (size_t i = 0; i < module->fan_insts.size; i++)
    {
        sn_obj_id_t fan = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_FAN], i);
        sn_obj_id_t inst = sn_vec_at(sn_obj_id_t, &module->fan_insts, i);
        assert(inst < object_count);
        assert(sn_obj_type(module, inst) == SN_INST);
        assert(sn_obj_fanin_count(module, fan) == 1);
        assert(sn_obj_fanin(module, fan, 0) == inst);
        assert(fan > inst);
        uint32_t output_index = fan - inst - 1;
        sn_module_id_t child = sn_vec_at(sn_module_id_t, &module->inst_modules,
                                         sn_obj_type_id(module, inst));
        assert(output_index < sn_design_module_output_count(module->design, child));
    }

    if (module->fanouts_valid)
    {
        assert(module->fanout_counts.size == object_count);
        assert(module->fanout_offsets.size == object_count);
        size_t offset = 0;
        for (sn_obj_id_t object = 0; object < object_count; object++)
        {
            assert(sn_vec_at(uint32_t, &module->fanout_offsets, object) == offset);
            offset += sn_vec_at(uint32_t, &module->fanout_counts, object);
            assert(offset <= module->fanouts.size);
        }
        assert(offset == module->fanouts.size);
        for (size_t i = 0; i < module->fanouts.size; i++)
            assert(sn_vec_at(sn_obj_id_t, &module->fanouts, i) < object_count);
    }
    else
    {
        assert(module->fanout_counts.size == 0);
        assert(module->fanout_offsets.size == 0);
        assert(module->fanouts.size == 0);
    }

    if (module->copy_ids.size)
    {
        assert(module->copy_ids.size == object_count);
        assert(module->copy_module < module->design->modules.size);
        size_t copy_count = sn_design_get_module_const(module->design, module->copy_module)->obj_types.size;
        for (size_t i = 0; i < module->copy_ids.size; i++)
        {
            sn_obj_id_t copy = sn_vec_at(sn_obj_id_t, &module->copy_ids, i);
            assert(copy == SN_INVALID_ID || copy < copy_count);
        }
    }
    else
        assert(module->copy_module == SN_INVALID_ID);
}

static inline void sn_design_assert_valid(const sn_design_t* design)
{
    assert(design);
    assert(design->modules.size < SN_INVALID_ID);
    assert(design->names.names.size < SN_INVALID_ID);
    assert(design->names.links.size == design->names.names.size);
    assert(design->names.buckets.size);
    for (size_t i = 0; i < design->names.names.size; i++)
    {
        const char* name = sn_vec_at(char*, &design->names.names, i);
        assert(name);
        assert(sn_name_find(&design->names, name) == i);
    }
    for (sn_module_id_t i = 0; i < design->modules.size; i++)
    {
        const sn_module_t* module = sn_design_get_module_const(design, i);
        assert(module->id == i);
        for (sn_module_id_t previous = 0; previous < i; previous++)
            assert(module->name != sn_design_get_module_const(design, previous)->name);
        sn_module_assert_valid(module);
    }
}

static inline void sn_binary_write_module(sn_binary_writer_t* writer, const sn_module_t* module)
{
    sn_binary_write_u32(writer, module->name);
    sn_binary_write_u32(writer, module->flags);
    sn_binary_write_u32(writer, module->fanouts_valid ? 1u : 0u);
    sn_binary_write_u32(writer, module->interface_locked ? 1u : 0u);
    sn_binary_write_u32(writer, module->copy_module);
    sn_binary_write_type_vec(writer, &module->obj_types);
    sn_binary_write_u32_vec(writer, &module->width_signed);
    sn_binary_write_fanin_count_vec(writer, &module->fanin_counts);
    sn_binary_write_u32_vec(writer, &module->fanin_offsets);
    sn_binary_write_u32_vec(writer, &module->type_ids);
    sn_binary_write_u32_vec(writer, &module->name_ids);
    sn_binary_write_u32_vec(writer, &module->fanins);
    for (uint32_t type = 0; type < SN_OBJ_TYPE_COUNT; type++)
        sn_binary_write_u32_vec(writer, &module->type_objects[type]);
    sn_binary_write_u32_vec(writer, &module->reg_flags);
    sn_binary_write_u32_vec(writer, &module->mem_depths);
    sn_binary_write_u32_vec(writer, &module->inst_modules);
    sn_binary_write_u32_vec(writer, &module->fan_insts);
    sn_binary_write_slice_vec(writer, &module->slice_infos);
    sn_binary_write_u32_vec(writer, &module->repeat_counts);
    sn_binary_write_u32_vec(writer, &module->const_word_offsets);
    sn_binary_write_u64_vec(writer, &module->lut_truths);
    sn_binary_write_u32_vec(writer, &module->gate_ids);
    sn_binary_write_u32_vec(writer, &module->fanout_counts);
    sn_binary_write_u32_vec(writer, &module->fanout_offsets);
    sn_binary_write_u32_vec(writer, &module->fanouts);
    sn_binary_write_u32_vec(writer, &module->copy_ids);
}

static inline bool sn_binary_read_module(sn_binary_reader_t* reader, sn_design_t* design, sn_module_id_t expected_id,
                                         uint32_t version, uint8_t* module_name_seen)
{
    sn_name_id_t name = sn_binary_read_u32(reader);
    uint32_t flags = version >= 6 ? sn_binary_read_u32(reader) : SN_MODULE_NO_FLAGS;
    uint32_t fanouts_valid = sn_binary_read_u32(reader);
    uint32_t interface_locked = sn_binary_read_u32(reader);
    sn_module_id_t copy_module = sn_binary_read_u32(reader);
    if (!reader->valid || name >= design->names.names.size || module_name_seen[name] ||
        (flags & ~SN_MODULE_ALL_FLAGS) != 0 || fanouts_valid > 1 || interface_locked > 1)
    {
        reader->valid = false;
        return false;
    }

    module_name_seen[name] = 1;
    sn_module_id_t id = sn_design_add_module_name_id(design, name);
    assert(id == expected_id);
    sn_module_t* module = sn_design_get_module(design, id);
    assert(module->name == name);
    module->flags = flags;
    module->fanouts_valid = fanouts_valid != 0;
    module->interface_locked = interface_locked != 0;
    module->copy_module = copy_module;

    sn_binary_read_type_vec(reader, &module->obj_types);
    sn_binary_read_u32_vec(reader, &module->width_signed);
    sn_binary_read_fanin_count_vec(reader, &module->fanin_counts);
    sn_binary_read_u32_vec(reader, &module->fanin_offsets);
    sn_binary_read_u32_vec(reader, &module->type_ids);
    sn_binary_read_u32_vec(reader, &module->name_ids);
    sn_binary_read_u32_vec(reader, &module->fanins);
    for (uint32_t type = 0; type < SN_OBJ_TYPE_COUNT; type++)
        sn_binary_read_u32_vec(reader, &module->type_objects[type]);
    sn_binary_read_u32_vec(reader, &module->reg_flags);
    sn_binary_read_u32_vec(reader, &module->mem_depths);
    sn_binary_read_u32_vec(reader, &module->inst_modules);
    sn_binary_read_u32_vec(reader, &module->fan_insts);
    sn_binary_read_slice_vec(reader, &module->slice_infos);
    sn_binary_read_u32_vec(reader, &module->repeat_counts);
    sn_binary_read_u32_vec(reader, &module->const_word_offsets);
    sn_binary_read_u64_vec(reader, &module->lut_truths);
    sn_binary_read_u32_vec(reader, &module->gate_ids);
    sn_binary_read_u32_vec(reader, &module->fanout_counts);
    sn_binary_read_u32_vec(reader, &module->fanout_offsets);
    sn_binary_read_u32_vec(reader, &module->fanouts);
    sn_binary_read_u32_vec(reader, &module->copy_ids);
    return reader->valid;
}

static inline bool sn_design_write_binary(FILE* out, const sn_design_t* design)
{
    static const uint8_t magic[8] = {'S', 'N', 'B', 'I', 'N', '\r', '\n', 0x1a};
    if (!out || !design)
        return false;
    sn_design_assert_valid(design);
    sn_binary_writer_t writer = sn_binary_writer_start(out);
    sn_binary_write_bytes(&writer, magic, sizeof(magic));
    sn_binary_write_u32(&writer, SN_BINARY_FORMAT_VERSION);
    sn_binary_write_u32(&writer, sn_binary_layout_signature());
    sn_binary_write_u32(&writer, SN_OBJ_TYPE_COUNT);
    sn_binary_write_u32(&writer, SN_REG_FANIN_COUNT);
    sn_binary_write_u32(&writer, SN_MEM_OUT_FANIN_COUNT);

    sn_binary_write_u64(&writer, design->names.names.size);
    for (size_t i = 0; i < design->names.names.size; i++)
    {
        const char* name = sn_vec_at(char*, &design->names.names, i);
        size_t length = strlen(name);
        sn_binary_write_u64(&writer, length);
        sn_binary_write_bytes(&writer, name, length);
    }
    sn_binary_write_u32_vec(&writer, &design->constant_words);
    sn_binary_write_u64(&writer, design->modules.size);
    for (size_t i = 0; i < design->modules.size; i++)
        sn_binary_write_module(&writer, sn_design_get_module_const(design, (sn_module_id_t)i));
    return writer.valid && ferror(out) == 0;
}

static inline bool sn_design_write_binary_file(const sn_design_t* design, const char* path)
{
    if (!design || !path)
        return false;
    FILE* out = fopen(path, "wb");
    if (!out)
        return false;
    bool success = sn_design_write_binary(out, design);
    if (fclose(out) != 0)
        success = false;
    return success;
}

// This routine validates the binary encoding while reconstructing its vectors, but intentionally does not dereference
// structural IDs or offsets. Callers must pass the result through sn_design_check() before installing or using it.
typedef enum sn_binary_read_status_t
{
    SN_BINARY_READ_OK,
    SN_BINARY_READ_IO,
    SN_BINARY_READ_MAGIC,
    SN_BINARY_READ_VERSION,
    SN_BINARY_READ_LAYOUT,
    SN_BINARY_READ_MALFORMED
} sn_binary_read_status_t;

static inline sn_design_t* sn_design_read_binary_raw_status(FILE* in, sn_binary_read_status_t* returned_status,
                                                            uint32_t* returned_version)
{
    static const uint8_t expected_magic[8] = {'S', 'N', 'B', 'I', 'N', '\r', '\n', 0x1a};
    sn_binary_read_status_t status = SN_BINARY_READ_OK;
    sn_binary_reader_t reader = sn_binary_reader_start(in);
    uint8_t magic[8] = {0};
    sn_binary_read_bytes(&reader, magic, sizeof(magic));
    uint32_t version = sn_binary_read_u32(&reader);
    uint32_t layout_signature = sn_binary_read_u32(&reader);
    uint32_t object_type_count = sn_binary_read_u32(&reader);
    uint32_t register_fanin_count = sn_binary_read_u32(&reader);
    uint32_t memory_fanin_count = sn_binary_read_u32(&reader);
    if (returned_version)
        *returned_version = version;
    if (!reader.valid)
        status = SN_BINARY_READ_IO;
    else if (memcmp(magic, expected_magic, sizeof(magic)) != 0)
        status = SN_BINARY_READ_MAGIC;
    else if (version < SN_BINARY_MIN_READ_VERSION || version > SN_BINARY_FORMAT_VERSION)
        status = SN_BINARY_READ_VERSION;
    else if (layout_signature != sn_binary_layout_signature() || object_type_count != SN_OBJ_TYPE_COUNT ||
             register_fanin_count != SN_REG_FANIN_COUNT ||
             memory_fanin_count != SN_MEM_OUT_FANIN_COUNT)
        status = SN_BINARY_READ_LAYOUT;
    if (status != SN_BINARY_READ_OK)
    {
        if (returned_status)
            *returned_status = status;
        return NULL;
    }

    sn_design_t* design = sn_design_create();
    size_t name_count = sn_binary_read_size(&reader);
    if (!reader.valid || name_count >= SN_INVALID_ID || name_count > reader.remaining / 8)
        reader.valid = false;
    for (size_t i = 0; i < name_count; i++)
    {
        size_t length = sn_binary_read_size(&reader);
        if (!reader.valid || length == SIZE_MAX || length > reader.remaining)
        {
            reader.valid = false;
            break;
        }
        char* name = (char*)malloc(length + 1);
        if (!name)
        {
            reader.valid = false;
            break;
        }
        sn_binary_read_bytes(&reader, name, length);
        name[length] = 0;
        if (memchr(name, 0, length) != NULL)
        {
            free(name);
            reader.valid = false;
            break;
        }
        sn_name_id_t id = sn_name_intern(&design->names, name);
        free(name);
        if (id != i)
        {
            reader.valid = false;
            break;
        }
    }
    sn_binary_read_u32_vec(&reader, &design->constant_words);
    size_t module_count = sn_binary_read_size(&reader);
    if (!reader.valid || module_count >= SN_INVALID_ID || module_count > reader.remaining / 16)
        reader.valid = false;
    uint8_t* module_name_seen = name_count ? (uint8_t*)calloc(name_count, 1) : NULL;
    if (reader.valid && module_count && !module_name_seen)
        reader.valid = false;
    for (sn_module_id_t i = 0; reader.valid && i < module_count; i++)
        sn_binary_read_module(&reader, design, i, version, module_name_seen);
    free(module_name_seen);
    if (!reader.valid)
    {
        sn_design_destroy(design);
        if (returned_status)
            *returned_status = SN_BINARY_READ_MALFORMED;
        return NULL;
    }
    if (returned_status)
        *returned_status = SN_BINARY_READ_OK;
    return design;
}

static inline sn_design_t* sn_design_read_binary_raw(FILE* in)
{
    return sn_design_read_binary_raw_status(in, NULL, NULL);
}

ABC_NAMESPACE_HEADER_END

#endif // SN_H
