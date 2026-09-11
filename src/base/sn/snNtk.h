/**CFile****************************************************************

  FileName    [snNtk.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Checked physical-cell reconstruction from an ABC network.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snNtk.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snNtk_h
#define ABC__base__sn__snNtk_h

#include "base/abc/abc.h"
#include "snMio.h"
#include "snMiniGate.h"

ABC_NAMESPACE_HEADER_START

// One record per ABC node; twins share a physical owner, not a logic output.
// The mini-mapping strings below are private node IDs, never cell-name IDs.
typedef struct sn_ntk_node_t
{
    const sn_mio_binding_t* binding;
    uint32_t owner, inputs;
    sn_obj_id_t object;
    bool present, paired;
} sn_ntk_node_t;

typedef struct sn_ntk_context_t
{
    sn_ntk_node_t* nodes;
    uint32_t count;
    uint64_t next_name; // monotonic across all nodes in one reconstruction
} sn_ntk_context_t;

static inline uint32_t sn_ntk_resolve(void* context, const char* name)
{
    const sn_ntk_context_t* state = (const sn_ntk_context_t*)context;
    if (*name++ != 'n' || !*name)
        return SN_INVALID_ID;
    uint64_t id = 0;
    do
    {
        if (*name < '0' || *name > '9')
            return SN_INVALID_ID;
        id = 10 * id + (unsigned)(*name++ - '0');
        if (id >= state->count)
            return SN_INVALID_ID;
    } while (*name);
    return (uint32_t)id;
}

static inline bool sn_ntk_validate(void* context, uint32_t id, uint32_t count)
{
    const sn_ntk_context_t* state = (const sn_ntk_context_t*)context;
    return id < state->count && state->nodes[id].present && state->nodes[id].inputs == count;
}

static inline sn_obj_id_t sn_ntk_construct(void* context, sn_module_t* module, uint32_t id,
                                          const sn_obj_id_t* inputs)
{
    sn_ntk_context_t* state = (sn_ntk_context_t*)context;
    const sn_mio_binding_t* binding = state->nodes[id].binding;
    sn_ntk_node_t* owner = &state->nodes[state->nodes[id].owner];
    if (!binding) // explicit ABC barrier buffer, not a physical library buffer
        return inputs[0];
    if (owner->object == SN_INVALID_ID)
    {
        if (binding->kind == SN_MIO_CONST0 || binding->kind == SN_MIO_CONST1)
        {
            uint32_t value = binding->kind == SN_MIO_CONST1;
            owner->object = sn_module_add_const(module, 1, false, &value, NULL);
        }
        else
        {
            sn_obj_id_t pins[SN_MIO_TRUTH_MAX_INPUTS];
            char name[64];
            for (uint32_t i = 0; i < binding->input_count; ++i)
                pins[i] = inputs[binding->inputs[i]];
            // The name pool is design-wide. Restarting at the local object
            // count for every gate repeatedly scans names from earlier mapped
            // modules, making hierarchical reconstruction quadratic.
            do { snprintf(name, sizeof(name), "__sn_mapped_%llu", (unsigned long long)state->next_name++); }
            while (sn_name_find(&module->design->names, name) != SN_INVALID_ID);
            owner->object = sn_module_add_library_gate(module, binding->cell, pins, name, NULL);
        }
    }
    if (binding->kind != SN_MIO_CELL || sn_gate_output_count(module, owner->object) == 1)
        return owner->object;
    return sn_owner_output(module, owner->object, binding->output);
}

// All cells, pin permutations, twin connections and topology are checked before
// adding a module. Call on a replacement design and install only after sn_check.
// Main-network connectivity and Mio IDs are never changed by this adapter.
static inline sn_module_id_t sn_design_add_mapped_network(sn_design_t* design, sn_module_id_t source,
    Abc_Ntk_t* network, Mio_Library_t* mio, const sn_blast_boundary_t* boundary, const char* name,
    const char** reason)
{
    sn_module_id_t result = SN_INVALID_ID;
    sn_ntk_context_t state = {NULL, 0, design->names.names.size};
    sn_mio_binding_t* bindings = NULL;
    bool* checked = NULL;
    int* indices = NULL;
    Vec_Ptr_t* nodes = NULL;
    Vec_Int_t* mapping = NULL;
    Vec_Str_t* names = NULL;
    st__table* gates = NULL;
    Mio_Gate_t* gate;
    Abc_Obj_t *node, *fanin;
    int i, k, gate_count = 0;
    *reason = "expected a combinational mapped network bound to the current SN/Mio library";
    if (!design->library || !network || !mio || !Abc_NtkIsLogic(network) || !Abc_NtkHasMapping(network) ||
        network->pManFunc != mio || Abc_NtkLatchNum(network) || Abc_NtkBoxNum(network) ||
        (size_t)Abc_NtkCiNum(network) != boundary->cis.size ||
        (size_t)Abc_NtkCoNum(network) != boundary->cos.size || !sn_library_compile(design->library))
        return result;
    if (!Abc_NtkIsAcyclic(network))
    {
        *reason = "mapped network has a combinational cycle";
        return result;
    }
    *reason = "out of memory preparing mapped-network reconstruction";
    state.count = (uint32_t)Abc_NtkObjNumMax(network);
    gate_count = Mio_LibraryReadGateNum(mio);
    state.nodes = (sn_ntk_node_t*)calloc(state.count, sizeof(*state.nodes));
    indices = (int*)malloc((size_t)state.count * sizeof(*indices));
    bindings = (sn_mio_binding_t*)calloc((size_t)gate_count, sizeof(*bindings));
    checked = (bool*)calloc((size_t)gate_count, sizeof(*checked));
    gates = st__init_table(st__ptrcmp, st__ptrhash);
    if (!state.nodes || !indices || !bindings || !checked || !gates)
        goto cleanup;
    for (uint32_t id = 0; id < state.count; ++id)
    {
        indices[id] = -1;
        state.nodes[id].owner = id;
        state.nodes[id].object = SN_INVALID_ID;
    }
    i = 0;
    Mio_LibraryForEachGate(mio, gate)
    {
        if (i >= gate_count || st__insert(gates, (char*)gate, (char*)&bindings[i++]) == st__OUT_OF_MEM)
            goto cleanup;
    }
    nodes = Abc_NtkDfs(network, 0);
    Abc_NtkForEachCi(network, node, i)
        indices[Abc_ObjId(node)] = i;
    Vec_PtrForEachEntry(Abc_Obj_t*, nodes, node, i)
    {
        uint32_t id = (uint32_t)Abc_ObjId(node);
        sn_mio_binding_t* binding = NULL;
        state.nodes[id].present = true;
        state.nodes[id].inputs = (uint32_t)Abc_ObjFaninNum(node);
        *reason = "mapped nodes must not carry complemented edges";
        if (Abc_ObjFaninC0(node) || Abc_ObjFaninC1(node))
            goto cleanup;
        *reason = "mapped network is not topological";
        Abc_ObjForEachFanin(node, fanin, k)
            if (indices[Abc_ObjId(fanin)] < 0)
                goto cleanup;
        indices[id] = Abc_NtkCiNum(network) + i;
        if (Abc_ObjIsBarBuf(node))
            continue;
        *reason = "node gate does not belong to the selected mapping library";
        if (!st__lookup(gates, (char*)node->pData, (char**)&binding))
            goto cleanup;
        if (!checked[binding - bindings])
        {
            checked[binding - bindings] = true;
            if (!sn_mio_bind_gate(design->library, (Mio_Gate_t*)node->pData, binding))
            {
                *reason = binding->reason;
                goto cleanup;
            }
        }
        *reason = "mapped node has the wrong number of physical inputs";
        if (binding->input_count != state.nodes[id].inputs)
            goto cleanup;
        state.nodes[id].binding = binding;
    }
    // Pair in physical object order, never DFS order: FetchTwinNode looks only
    // forward, so the second output of one pair can appear to twin with the
    // first output of the next pair. Consume both, including unused outputs.
    // Reciprocal gate links and physical pin connections must also agree.
    Abc_NtkForEachNode(network, node, i)
    {
        uint32_t id = (uint32_t)Abc_ObjId(node);
        if (Abc_ObjIsBarBuf(node) || state.nodes[id].paired)
            continue;
        Abc_Obj_t* twin = Abc_NtkFetchTwinNode(node);
        if (!twin)
            continue;
        uint32_t other = (uint32_t)Abc_ObjId(twin);
        if (state.nodes[other].paired ||
            Mio_GateReadTwin((Mio_Gate_t*)twin->pData) != (Mio_Gate_t*)node->pData)
            continue;
        state.nodes[id].paired = state.nodes[other].paired = true;
        if (!state.nodes[id].present || !state.nodes[other].present)
            continue;
        const sn_mio_binding_t* left = state.nodes[id].binding;
        const sn_mio_binding_t* right = state.nodes[other].binding;
        *reason = "twin nodes disagree on their physical cell or pin connections";
        if (!left || !right || left->kind != SN_MIO_CELL || right->kind != SN_MIO_CELL ||
            left->cell != right->cell || left->output == right->output || left->input_count != right->input_count)
            goto cleanup;
        for (uint32_t p = 0; p < left->input_count; ++p)
            if (Abc_ObjFanin(node, (int)left->inputs[p]) != Abc_ObjFanin(twin, (int)right->inputs[p]))
                goto cleanup;
        state.nodes[other].owner = id;
    }
    mapping = Vec_IntAlloc(1024);
    names = Vec_StrAlloc(1024);
    Vec_IntPush(mapping, Abc_NtkCiNum(network));
    Vec_IntPush(mapping, Abc_NtkCoNum(network));
    Vec_IntPush(mapping, Vec_PtrSize(nodes));
    Vec_IntPush(mapping, 0);
    Vec_PtrForEachEntry(Abc_Obj_t*, nodes, node, i)
    {
        char key[32];
        Vec_IntPush(mapping, Abc_ObjFaninNum(node));
        Abc_ObjForEachFanin(node, fanin, k)
            Vec_IntPush(mapping, indices[Abc_ObjId(fanin)]);
        snprintf(key, sizeof(key), "n%u", (unsigned)Abc_ObjId(node));
        Vec_StrPrintStr(names, key);
        Vec_StrPush(names, '\0');
    }
    Abc_NtkForEachCo(network, node, i)
    {
        *reason = "mapped output has an absent or complemented driver";
        if (Abc_ObjFaninNum(node) != 1 || Abc_ObjFaninC0(node) || indices[Abc_ObjFaninId0(node)] < 0)
            goto cleanup;
        Vec_IntPush(mapping, indices[Abc_ObjFaninId0(node)]);
    }
    while (!Vec_StrSize(names) || Vec_StrSize(names) % sizeof(int))
        Vec_StrPush(names, '\0');
    for (i = 0; i < Vec_StrSize(names); i += (int)sizeof(int))
    {
        int value;
        memcpy(&value, Vec_StrArray(names) + i, sizeof(value));
        Vec_IntPush(mapping, value);
    }
    *reason = "checked mini-mapping reconstruction failed";
    result = sn_design_add_bound_gate_module(design, source, Vec_IntArray(mapping), (size_t)Vec_IntSize(mapping),
        boundary, sn_ntk_resolve, &state, name, sn_ntk_validate, sn_ntk_construct);
    if (result != SN_INVALID_ID)
        *reason = NULL;
cleanup:
    if (bindings)
        for (i = 0; i < gate_count; ++i)
            sn_mio_binding_destroy(&bindings[i]);
    free(bindings);
    free(checked);
    free(state.nodes);
    free(indices);
    if (gates) st__free_table(gates);
    if (nodes) Vec_PtrFree(nodes);
    if (mapping) Vec_IntFree(mapping);
    if (names) Vec_StrFree(names);
    return result;
}

ABC_NAMESPACE_HEADER_END
#endif
