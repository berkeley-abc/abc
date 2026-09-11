/**CFile****************************************************************

  FileName    [snClock.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Checked clock projection and typed state-action proof signatures.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snClock.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snClock_h
#define ABC__base__sn__snClock_h

#include "snStitch.h"
#include "snSeq.h"

ABC_NAMESPACE_HEADER_START

typedef struct sn_clock_options_t
{
    bool transition; // free corresponding state, not a zero-start sequential AIG
    bool assume_zero; // explicit analysis assumption for unspecified initial bits
    const int* pi_values; // top PI bits in interface order: -1 free, 0/1 constrained
    size_t pi_count;
    bool allow_macros; // explicitly conditional relation, with named opaque cuts
    bool named_states; // physical instance/register identity instead of candidate index-order pairing
    // Separate combinational proof signature: retain arbitrary clocks and emit
    // each state's guarded update AND trigger function. Not a time-step model,
    // sequential AIG, or delta-cycle/glitch proof. Requires transition + names.
    bool state_actions;
    bool verbose; // per-bit identity/phase manifest; summaries always printed
} sn_clock_options_t;

typedef struct sn_clock_state_t
{
    uint32_t occurrence, object, bit;
    int next, clock, phase;
    bool cell, explicit_init, latch;
} sn_clock_state_t;

static inline int sn_clock_co(Gia_Man_t* gia, uint32_t index)
{
    assert(index < (uint32_t)Gia_ManCoNum(gia));
    return Gia_ObjFaninLit0p(gia, Gia_ManCo(gia, (int)index));
}

static inline int sn_clock_control(Gia_Man_t* gia, const sn_blast_register_t* reg,
                                   uint32_t slot, int absent)
{
    return reg->control_co_begin[slot] == SN_INVALID_ID ? absent : sn_clock_co(gia, reg->control_co_begin[slot]);
}

static inline bool sn_clock_names_unique(Vec_Ptr_t* names)
{
    sn_name_mgr_t seen;
    bool unique = true;
    sn_name_mgr_init(&seen);
    for (int i = 0; i < Vec_PtrSize(names); ++i)
    {
        const char* name = (const char*)Vec_PtrEntry(names, i);
        if (sn_name_find(&seen, name) != SN_INVALID_ID) { unique = false; break; }
        sn_name_intern(&seen, name);
    }
    sn_name_mgr_destroy(&seen);
    return unique;
}

// Local conversion avoids modifying either ABC workspace during preflight.
static inline Gia_Man_t* sn_clock_from_mini(Mini_Aig_t* mini)
{
    int* copy = ABC_ALLOC(int, Mini_AigNodeNum(mini));
    if (!copy) return NULL;
    Gia_Man_t* gia = Gia_ManStart(Mini_AigNodeNum(mini));
    Gia_ManHashAlloc(gia);
    copy[0] = 0;
    for (int i = 1; i < Mini_AigNodeNum(mini); ++i)
    {
        if (Mini_AigNodeIsPi(mini, i))
            copy[i] = Gia_ManAppendCi(gia);
        else
        {
            int left = Mini_AigNodeFanin0(mini, i);
            left = Abc_LitNotCond(copy[Abc_Lit2Var(left)], Abc_LitIsCompl(left));
            if (Mini_AigNodeIsPo(mini, i))
                copy[i] = Gia_ManAppendCo(gia, left);
            else
            {
                int right = Mini_AigNodeFanin1(mini, i);
                copy[i] = Gia_ManHashAnd(gia, left,
                    Abc_LitNotCond(copy[Abc_Lit2Var(right)], Abc_LitIsCompl(right)));
            }
        }
    }
    ABC_FREE(copy);
    return gia; // hash table remains active while next-state graphs are added
}

// Normally a closed edge-sampled projection: latches and unsupported clocks
// refuse. The separate state_actions option emits only a combinational proof
// signature with typed FF/latch triggers and guarded updates. It retains clock
// inputs and cannot be used as a time-step/settling model. Neither mode mutates
// SN, implicitly assumes reset, or expands Liberty functions into SN operators.
// CI order: primary/opaque inputs, phase-normalized state. CO order: primary/
// opaque outputs, state updates, then triggers in state_actions mode only.
static inline Gia_Man_t* sn_design_clock_abstract(const sn_design_t* design, sn_module_id_t top,
                                                 sn_clock_options_t options, FILE* report,
                                                 const char** reason)
{
    sn_blast_boundary_t boundary;
    sn_blast_options_t blast = sn_blast_default_options();
    sn_blast_hier_stats_t stats;
    Mini_Aig_t* mini = NULL;
    Gia_Man_t *source = NULL, *joined = NULL, *result = NULL;
    Vec_Int_t *aliases = Vec_IntAlloc(100), *roots = Vec_IntAlloc(100), *asyncs = Vec_IntAlloc(20);
    Vec_Int_t *unused_cis = Vec_IntAlloc(20);
    sn_vec_t states;
    int cycle_ci = -1, outputs = 0, primary_inputs = 0, retained_inputs = 0, common_clock = -1;
    int macro_inputs = 0, macro_outputs = 0, final_outputs = 0;
    int* final_aliases = NULL;
    int* final_roots = NULL;
    signed char** phase_maps = NULL;
    sn_name_id_t** state_name_maps = NULL;
    *reason = NULL;
    sn_vec_init(&states);
    sn_blast_boundary_init(&boundary);
    if (options.state_actions && (!options.transition || !options.named_states || options.assume_zero))
    { *reason = "state-action proof requires named free state, not a sequential or zero-start model"; goto cleanup; }
    blast.mode = SN_BLAST_COMB;
    blast.opaque_sequential_gates = true;
    blast.probe_all_register_controls = true;
    blast.flatten_latch_modules = options.state_actions;
    mini = sn_design_blast_hier_boundary_options(design, top, blast, &stats, &boundary);
    if (!mini) { *reason = "combinational preflight extraction failed"; goto cleanup; }
    source = sn_clock_from_mini(mini);
    if (!source) { *reason = "allocation failure converting extraction"; goto cleanup; }
    if (report)
    {
        size_t native_bits = 0, native_latch_bits = 0, ff_cells = 0, latch_cells = 0, macros = 0, loop_bits = 0;
        for (size_t i = 0; i < boundary.registers.size; ++i)
        {
            const sn_blast_register_t* reg = &sn_vec_at(sn_blast_register_t, &boundary.registers, i);
            const sn_blast_occurrence_t* occurrence = &sn_vec_at(sn_blast_occurrence_t, &boundary.occurrences, reg->occurrence);
            const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
            if (sn_obj_reg_flags(module, reg->reg_out) & SN_REG_LATCH) native_latch_bits += reg->width;
            else native_bits += reg->width;
        }
        for (size_t i = 0; i < boundary.primitives.size; ++i)
        {
            const sn_blast_primitive_t* primitive = &sn_vec_at(sn_blast_primitive_t, &boundary.primitives, i);
            const sn_blast_occurrence_t* occurrence = &sn_vec_at(sn_blast_occurrence_t, &boundary.occurrences, primitive->occurrence);
            const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
            if (primitive->module != SN_INVALID_ID) ++macros;
            else if (sn_library_latch_boundary(design->library, sn_obj_gate_id(module, primitive->inst))) ++latch_cells;
            else ++ff_cells;
        }
        for (size_t i = 0; i < boundary.loops.size; ++i) loop_bits += sn_vec_at(sn_blast_loop_t, &boundary.loops, i).width;
        fprintf(report, "Clock preflight: native FF bits=%zu; FF cells=%zu; native latch bits=%zu; latch cells=%zu; macros=%zu; memories=%llu; LOOP bits=%zu.\n",
                native_bits, ff_cells, native_latch_bits, latch_cells, macros,
                (unsigned long long)stats.memory_count, loop_bits);
    }
    phase_maps = (signed char**)calloc(design->modules.size, sizeof(*phase_maps));
    state_name_maps = (sn_name_id_t**)calloc(design->modules.size, sizeof(*state_name_maps));
    if (!phase_maps || !state_name_maps) { *reason = "allocation failure indexing state correspondence"; goto cleanup; }
    if (stats.memory_count || (stats.multiplier_count && !options.allow_macros))
    { *reason = "memory or arithmetic macro cuts prevent a closed clock model"; goto cleanup; }
    Vec_IntFill(aliases, Gia_ManCiNum(source), -1);
    for (size_t i = 0; i < boundary.cis.size; ++i)
    {
        const sn_blast_boundary_bit_t* bit = &sn_vec_at(sn_blast_boundary_bit_t, &boundary.cis, i);
        if (bit->kind == SN_BLAST_BOUNDARY_TOP_PI)
        {
            int value = options.pi_values && (size_t)primary_inputs < options.pi_count ?
                options.pi_values[primary_inputs] : -1;
            if (value < -1 || value > 1) { *reason = "invalid input constraint"; goto cleanup; }
            Vec_IntWriteEntry(aliases, (int)i, value);
            retained_inputs += value < 0;
            ++primary_inputs;
        }
        else if (bit->kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT)
        {
            const sn_blast_loop_t* loop = &sn_vec_at(sn_blast_loop_t, &boundary.loops, bit->owner);
            Vec_IntWriteEntry(aliases, (int)i, sn_clock_co(source, loop->co_begin + bit->port));
        }
        else if (bit->kind != SN_BLAST_BOUNDARY_REG_OUTPUT && bit->kind != SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT)
        { *reason = "unsupported non-state input cut"; goto cleanup; }
        if (bit->kind == SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT &&
            sn_vec_at(sn_blast_primitive_t, &boundary.primitives, bit->owner).module != SN_INVALID_ID)
            ++macro_inputs;
    }
    if (options.pi_values && options.pi_count != (size_t)primary_inputs)
    { *reason = "input constraint count does not match top interface"; goto cleanup; }
    for (size_t i = 0; i < boundary.cos.size; ++i)
        if (sn_vec_at(sn_blast_boundary_bit_t, &boundary.cos, i).kind == SN_BLAST_BOUNDARY_TOP_PO)
            Vec_IntPush(roots, sn_clock_co(source, (uint32_t)i));
    for (size_t i = 0; i < boundary.cos.size; ++i)
    {
        const sn_blast_boundary_bit_t* bit = &sn_vec_at(sn_blast_boundary_bit_t, &boundary.cos, i);
        if (bit->kind == SN_BLAST_BOUNDARY_PRIMITIVE_INPUT &&
            sn_vec_at(sn_blast_primitive_t, &boundary.primitives, bit->owner).module != SN_INVALID_ID)
        {
            Vec_IntPush(roots, sn_clock_co(source, (uint32_t)i));
            ++macro_outputs;
        }
    }
    outputs = Vec_IntSize(roots);
    for (size_t i = 0; i < boundary.registers.size; ++i)
    {
        const sn_blast_register_t* reg = &sn_vec_at(sn_blast_register_t, &boundary.registers, i);
        const sn_blast_occurrence_t* occurrence = &sn_vec_at(sn_blast_occurrence_t, &boundary.occurrences, reg->occurrence);
        const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
        uint32_t flags = sn_obj_reg_flags(module, reg->reg_out);
        int clock = sn_clock_control(source, reg, SN_REG_CLOCK, -1);
        int enable = sn_clock_control(source, reg, SN_REG_ENABLE, 1);
        int set = sn_clock_control(source, reg, SN_REG_SET, (flags & SN_REG_SET_NEGEDGE) != 0) ^
            ((flags & SN_REG_SET_NEGEDGE) != 0);
        int reset = sn_clock_control(source, reg, SN_REG_RESET, (flags & SN_REG_RESET_NEGEDGE) != 0) ^
            ((flags & SN_REG_RESET_NEGEDGE) != 0);
        bool latch = (flags & SN_REG_LATCH) != 0;
        if (latch && !options.state_actions)
        { *reason = "transparent latch prevents a closed edge-triggered model"; goto cleanup; }
        if (latch)
        {
            if (flags & ~SN_REG_LATCH)
            { *reason = "state-action proof supports only plain native latches"; goto cleanup; }
            clock = enable; // level-sensitive trigger, not an edge clock
        }
        if (clock < 0) { *reason = "register has no clock probe"; goto cleanup; }
        clock ^= (flags & SN_REG_CLOCK_NEGEDGE) != 0;
        if (flags & SN_REG_SET_ASYNC) Vec_IntPush(asyncs, set);
        if (flags & SN_REG_RESET_ASYNC) Vec_IntPush(asyncs, reset);
        for (uint32_t bit = 0; bit < reg->width; ++bit)
        {
            sn_obj_id_t init = sn_obj_reg_init_data(module, reg->reg_out);
            sn_obj_id_t mask = sn_obj_reg_init_mask(module, reg->reg_out);
            bool explicit_init = init != SN_INVALID_ID && (mask == SN_INVALID_ID || sn_const_bit(module, mask, bit));
            int phase = explicit_init && sn_const_bit(module, init, bit);
            int state = Gia_ManAppendCi(source) ^ phase;
            int next = sn_clock_co(source, reg->co_begin + bit);
            sn_clock_state_t* record;
            if (!explicit_init && !options.transition && !options.assume_zero)
            { *reason = "unspecified initial state: use a free-state transition relation or explicitly assume zero"; goto cleanup; }
            Vec_IntPush(aliases, -1);
            Vec_IntWriteEntry(aliases, (int)(reg->ci_begin + bit), state);
            next = Gia_ManHashMux(source, enable, next, state);
            if (!(flags & SN_REG_SET_ASYNC)) next = Gia_ManHashMux(source, set, 1, next);
            if (!(flags & SN_REG_RESET_ASYNC))
            {
                int value = reg->control_co_begin[SN_REG_RESET_VALUE] == SN_INVALID_ID ? 0 :
                    sn_clock_co(source, reg->control_co_begin[SN_REG_RESET_VALUE] + bit);
                next = Gia_ManHashMux(source, reset, value, next);
            }
            record = sn_vec_push(sn_clock_state_t, &states);
            record->occurrence = reg->occurrence; record->object = reg->reg_out; record->bit = bit;
            record->next = next ^ phase; record->clock = clock; record->phase = phase;
            record->cell = false; record->explicit_init = explicit_init;
            record->latch = latch;
        }
    }
    for (size_t i = 0; i < boundary.primitives.size; ++i)
    {
        const sn_blast_primitive_t* primitive = &sn_vec_at(sn_blast_primitive_t, &boundary.primitives, i);
        const sn_blast_occurrence_t* occurrence = &sn_vec_at(sn_blast_occurrence_t, &boundary.occurrences, primitive->occurrence);
        const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
        sn_seq_info_t info;
        int* values;
        uint32_t cell, inputs;
        bool oom = false;
        if (primitive->module != SN_INVALID_ID)
        {
            // Ordinary combinational extraction also boxes latch-bearing RTL
            // modules. -u authorizes declared opaque macros, not implicitly
            // dropping known behavioral state just because it sits in a child.
            const sn_module_t* child = sn_design_get_module_const(design, primitive->module);
            if (!sn_module_is_blackbox(child))
            { *reason = "behavioral module cut (including native latches) is not a declared opaque macro"; goto cleanup; }
            if (options.allow_macros) continue;
        }
        if (primitive->module != SN_INVALID_ID || sn_obj_type(module, primitive->inst) != SN_GATE)
        { *reason = "opaque macro prevents a closed clock model"; goto cleanup; }
        cell = sn_obj_gate_id(module, primitive->inst);
        if (!sn_library_seq_info(design->library, cell, &info))
        { sn_seq_info_destroy(&info); *reason = "allocation failure deriving cell descriptor"; goto cleanup; }
        // Asynchronous projections may be admitted only after the composed
        // input constraints prove BOTH controls inactive; collision states
        // are then unreachable under this explicit contract.
        if (!sn_seq_proof_eligible(&info, options.state_actions))
        { *reason = info.abstract_reason; sn_seq_info_destroy(&info); goto cleanup; }
        if (info.latch && !options.state_actions)
        { *reason = "transparent cell latch prevents a closed edge-triggered model"; sn_seq_info_destroy(&info); goto cleanup; }
        if (info.latch && (info.state->clear != SN_LIB_NONE || info.state->preset != SN_LIB_NONE))
        { *reason = "state-action proof supports only plain cell latches"; sn_seq_info_destroy(&info); goto cleanup; }
        if (!options.transition && !options.assume_zero)
        { *reason = "Liberty state has no power-up value: explicitly assume zero or request free-state transition";
          sn_seq_info_destroy(&info); goto cleanup; }
        inputs = design->library->cells[cell].input_count;
        values = ABC_ALLOC(int, info.graph.inputs + info.graph.count + 1);
        if (!values) { *reason = "allocation failure lowering cell graph"; sn_seq_info_destroy(&info); goto cleanup; }
        values[0] = 0;
        for (uint32_t input = 0; input < inputs; ++input)
            values[input + 1] = sn_clock_co(source, primitive->co_begin + input);
        // Default canonical state is the first physical output. Legalization
        // can instead record its logical-source-Q phase. This selects an
        // encoding, not a behavioral assumption; transition CEC checks the
        // resulting correspondence. Index sparse attributes once per module.
        int phase = sn_seq_projection(&info.graph, info.graph.roots[SN_SEQ_OUTPUT], &oom) & 1;
        if (!phase_maps[module->id])
        {
            phase_maps[module->id] = sn_module_state_phase_map(module);
            if (!phase_maps[module->id])
            { ABC_FREE(values); sn_seq_info_destroy(&info); *reason = "allocation failure indexing state phases"; goto cleanup; }
        }
        if (phase_maps[module->id][primitive->inst] == -2)
        { ABC_FREE(values); sn_seq_info_destroy(&info); *reason = "ambiguous or malformed sn_state_phase correspondence"; goto cleanup; }
        if (phase_maps[module->id][primitive->inst] >= 0)
            phase = phase_maps[module->id][primitive->inst];
        int state = Gia_ManAppendCi(source);
        Vec_IntPush(aliases, -1);
        values[inputs + 1] = state ^ phase;
        for (uint32_t node = 0; node < info.graph.count; ++node)
        {
            sn_expr_node_t pair = info.graph.nodes[node];
            values[info.graph.inputs + node + 1] = Gia_ManHashAnd(source,
                values[pair.left >> 1] ^ (pair.left & 1), values[pair.right >> 1] ^ (pair.right & 1));
        }
        for (uint32_t output = 0; output < primitive->output_count; ++output)
        {
            sn_expr_lit_t root = info.graph.roots[SN_SEQ_OUTPUT + output];
            Vec_IntWriteEntry(aliases, (int)(primitive->ci_begin + output), values[root >> 1] ^ (root & 1));
        }
        for (int control = SN_SEQ_CLEAR; control <= SN_SEQ_PRESET; ++control)
        {
            sn_expr_lit_t root = info.graph.roots[control];
            Vec_IntPush(asyncs, values[root >> 1] ^ (root & 1));
        }
        sn_expr_lit_t data = info.graph.roots[SN_SEQ_DATA], clk = info.graph.roots[SN_SEQ_CLOCK];
        sn_clock_state_t* record = sn_vec_push(sn_clock_state_t, &states);
        record->occurrence = primitive->occurrence; record->object = primitive->inst; record->bit = 0;
        record->next = values[data >> 1] ^ (data & 1) ^ phase;
        record->clock = values[clk >> 1] ^ (clk & 1); record->phase = phase;
        record->cell = true; record->explicit_init = false;
        record->latch = info.latch;
        if (info.latch)
            record->next = Gia_ManHashMux(source, record->clock, record->next, state);
        ABC_FREE(values);
        sn_seq_info_destroy(&info);
        if (oom) { *reason = "allocation failure recognizing state phase"; goto cleanup; }
    }
    if (!states.size) { *reason = "no state to abstract"; goto cleanup; }
    for (size_t i = 0; i < states.size; ++i)
        Vec_IntPush(roots, sn_vec_at(sn_clock_state_t, &states, i).next);
    for (size_t i = 0; i < states.size; ++i)
        Vec_IntPush(roots, sn_vec_at(sn_clock_state_t, &states, i).clock);
    Vec_IntAppend(roots, asyncs);
    Gia_ManHashStop(source);
    joined = sn_gia_substitute_cis_tracked(source, Vec_IntArray(aliases), Vec_IntArray(roots), Vec_IntSize(roots), reason, &cycle_ci, unused_cis);
    if (joined && report)
    {
        int unused_loops = 0, ci, index;
        Vec_IntForEachEntry(unused_cis, ci, index)
            if ((size_t)ci < boundary.cis.size &&
                sn_vec_at(sn_blast_boundary_bit_t, &boundary.cis, ci).kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT)
                ++unused_loops;
        fprintf(report, "Cone-of-influence reduction: %d unobserved LOOP bits omitted; their cycles are not checked. CLOSED refers only to the retained behavior.\n", unused_loops);
    }
    if (!joined)
    {
        // cycle_ci belongs to the original extraction here. Later substitution
        // uses a reduced interface, so its indices must not index this boundary.
        if (report && cycle_ci >= 0 && (size_t)cycle_ci < boundary.cis.size)
        {
            bool canonical = true;
            char* name = sn_blast_boundary_bit_name(design, &boundary,
                &sn_vec_at(sn_blast_boundary_bit_t, &boundary.cis, cycle_ci), &canonical);
            if (name) fprintf(report, "Clock cycle boundary: %s%s\n", name,
                              canonical ? "" : " (generated identity)");
            free(name);
        }
        goto cleanup;
    }
    for (size_t i = 0; !options.state_actions && i < states.size; ++i)
    {
        int clock = sn_clock_co(joined, (uint32_t)(outputs + states.size + i));
        Gia_Obj_t* node = Gia_ManObj(joined, Abc_Lit2Var(clock));
        if (!Gia_ObjIsCi(node) || Gia_ObjCioId(node) >= retained_inputs)
        { *reason = "generated, gated or constrained clock is not a free top-level input projection"; goto cleanup; }
        if (common_clock >= 0 && common_clock != clock)
        { *reason = "multiple clock roots or mixed effective edges"; goto cleanup; }
        common_clock = clock;
    }
    for (int i = 0; i < Vec_IntSize(asyncs); ++i)
        if (sn_clock_co(joined, (uint32_t)(outputs + 2 * states.size + i)) != 0)
        { *reason = "async controls are not proved inactive under the supplied input constraints"; goto cleanup; }
    final_aliases = ABC_ALLOC(int, Gia_ManCiNum(joined));
    if (states.size > (size_t)(INT_MAX - outputs) / (options.state_actions ? 2 : 1))
    { *reason = "state proof output count exceeds the AIG limit"; goto cleanup; }
    final_outputs = outputs + (int)states.size * (options.state_actions ? 2 : 1);
    final_roots = ABC_ALLOC(int, final_outputs);
    if (!final_aliases || !final_roots) { *reason = "allocation failure finalizing clock model"; goto cleanup; }
    for (int i = 0; i < Gia_ManCiNum(joined); ++i) final_aliases[i] = -1;
    if (!options.state_actions)
        final_aliases[Gia_ObjCioId(Gia_ManObj(joined, Abc_Lit2Var(common_clock)))] = 1 ^ (common_clock & 1);
    for (int i = 0; i < final_outputs; ++i) final_roots[i] = sn_clock_co(joined, (uint32_t)i);
    result = sn_gia_substitute_cis(joined, final_aliases, final_roots, final_outputs, reason, &cycle_ci);
    if (!result) goto cleanup;
    Gia_ManSetRegNum(result, options.transition ? 0 : (int)states.size);
    result->vNamesIn = Vec_PtrAlloc(Gia_ManCiNum(result));
    result->vNamesOut = Vec_PtrAlloc(Gia_ManCoNum(result));
    {
        int retained = 0, input_index = 0;
        int clock_index = options.state_actions ? -1 : Gia_ObjCioId(Gia_ManObj(joined, Abc_Lit2Var(common_clock)));
        for (size_t i = 0; i < boundary.cis.size; ++i)
        {
            const sn_blast_boundary_bit_t* bit = &sn_vec_at(sn_blast_boundary_bit_t, &boundary.cis, i);
            if (bit->kind != SN_BLAST_BOUNDARY_TOP_PI) continue;
            bool canonical = true;
            char* name = sn_blast_boundary_bit_name(design, &boundary, bit, &canonical);
            int value = Vec_IntEntry(aliases, (int)i);
            bool clock = value < 0 && retained == clock_index;
            if (report && (options.verbose || value >= 0))
                fprintf(report, "input[%d]: %s role=%s value=%d\n", input_index, name,
                        value >= 0 ? "constant-contract" : clock ? "clock" : "data",
                        value >= 0 ? value : clock ? 1 ^ (common_clock & 1) : -1);
            if (value < 0 && !clock)
            {
                char* label = ABC_ALLOC(char, strlen(name) + 4);
                sprintf(label, "pi:%s", name);
                Vec_PtrPush(result->vNamesIn, label);
            }
            retained += value < 0;
            ++input_index;
            free(name);
        }
        for (size_t i = 0; i < boundary.cos.size; ++i)
        {
            const sn_blast_boundary_bit_t* bit = &sn_vec_at(sn_blast_boundary_bit_t, &boundary.cos, i);
            if (bit->kind != SN_BLAST_BOUNDARY_TOP_PO) continue;
            bool canonical = true;
            char* name = sn_blast_boundary_bit_name(design, &boundary, bit, &canonical);
            char* label = ABC_ALLOC(char, strlen(name) + 4);
            sprintf(label, "po:%s", name);
            Vec_PtrPush(result->vNamesOut, label);
            free(name);
        }
        for (int direction = 0; direction < 2; ++direction)
        {
            const sn_vec_t* bits = direction ? &boundary.cos : &boundary.cis;
            for (size_t i = 0; i < bits->size; ++i)
            {
                const sn_blast_boundary_bit_t* bit = &sn_vec_at(sn_blast_boundary_bit_t, bits, i);
                if (bit->kind != (direction ? SN_BLAST_BOUNDARY_PRIMITIVE_INPUT : SN_BLAST_BOUNDARY_PRIMITIVE_OUTPUT) ||
                    sn_vec_at(sn_blast_primitive_t, &boundary.primitives, bit->owner).module == SN_INVALID_ID) continue;
                bool canonical = true;
                char* name = sn_blast_boundary_bit_name(design, &boundary, bit, &canonical);
                char* label = ABC_ALLOC(char, strlen(name) + 9);
                sprintf(label, "%s:%s", direction ? "cut-out" : "cut-in", name);
                Vec_PtrPush(direction ? result->vNamesOut : result->vNamesIn, label);
                if (report) fprintf(report, "macro-cut: %s\n", label);
                free(name);
            }
        }
        for (size_t i = 0; i < states.size; ++i)
        {
            if (options.named_states)
            {
                const sn_clock_state_t* state = &sn_vec_at(sn_clock_state_t, &states, i);
                const sn_blast_occurrence_t* occurrence = &sn_vec_at(sn_blast_occurrence_t, &boundary.occurrences, state->occurrence);
                const sn_module_t* module = sn_design_get_module_const(design, occurrence->module);
                sn_blast_name_t name = {NULL, 0, 0};
                bool canonical = true;
                sn_blast_occurrence_path(design, &boundary, state->occurrence, &name, &canonical);
                sn_name_id_t logical_name = SN_INVALID_ID;
                if (state->cell)
                {
                    if (!state_name_maps[module->id])
                        state_name_maps[module->id] = sn_module_state_name_map(module);
                    if (!state_name_maps[module->id])
                    { free(name.text); *reason = "allocation failure indexing logical state names"; goto cleanup; }
                    logical_name = state_name_maps[module->id][state->object];
                    if (logical_name == SN_INVALID_ID - 1)
                    { free(name.text); *reason = "ambiguous or malformed sn_state_name correspondence"; goto cleanup; }
                }
                if (logical_name != SN_INVALID_ID)
                    sn_blast_name_append(&name, sn_name_get(&design->names, logical_name));
                else
                {
                    sn_blast_name_object(module, state->object, state->cell ? "cell" : "reg", &name, &canonical);
                    sn_blast_name_append_bit(&name, state->bit);
                }
                if (!canonical)
                { free(name.text); *reason = "named state correspondence requires unique source identities"; goto cleanup; }
                for (int direction = 0; direction < 2; ++direction)
                {
                    char* label = ABC_ALLOC(char, strlen(name.text) + 20);
                    if (options.state_actions)
                        sprintf(label, "%s-%s:%s", state->latch ? "latch" : "ff",
                                direction ? "action" : "state", name.text);
                    else
                        sprintf(label, "%s:%s", direction ? "next" : "state", name.text);
                    Vec_PtrPush(direction ? result->vNamesOut : result->vNamesIn, label);
                }
                free(name.text);
                continue;
            }
            char label[64];
            snprintf(label, sizeof(label), "state:%zu", i);
            Vec_PtrPush(result->vNamesIn, Abc_UtilStrsav(label));
            snprintf(label, sizeof(label), "next:%zu", i);
            Vec_PtrPush(result->vNamesOut, Abc_UtilStrsav(label));
        }
        // Trigger outputs follow all action outputs, matching final_roots.
        if (options.state_actions)
            for (size_t i = 0; i < states.size; ++i)
            {
                const sn_clock_state_t* state = &sn_vec_at(sn_clock_state_t, &states, i);
                const char* action = (const char*)Vec_PtrEntry(result->vNamesOut, outputs + (int)i);
                const char* identity = strchr(action, ':') + 1;
                char* label = ABC_ALLOC(char, strlen(identity) + 20);
                sprintf(label, "%s:%s", state->latch ? "latch-gate" : "ff-clock", identity);
                Vec_PtrPush(result->vNamesOut, label);
            }
    }
    if (!sn_clock_names_unique(result->vNamesIn) || !sn_clock_names_unique(result->vNamesOut))
    { *reason = "duplicate boundary names; preserve generated-scope identities before clock abstraction"; goto cleanup; }
    if (report)
    {
        fprintf(report, "%s: %s %s; %zu state bits, %d data inputs, %d outputs; LOOPs joined.\n",
                options.state_actions ? "State action relation" : "Clock abstraction",
                macro_inputs || macro_outputs ? "CONDITIONAL" : "CLOSED",
                options.state_actions ? "combinational proof signature" :
                options.transition ? "free-state transition relation" : "sequential AIG", states.size,
                retained_inputs - !options.state_actions, outputs);
        if (macro_inputs || macro_outputs)
            fprintf(report, "Macro contract: %d free output bits / %d observed input bits; no macro transition semantics. NOT a closed sequential model.\n",
                    macro_inputs, macro_outputs);
        if (options.state_actions)
            fprintf(report, "Contract: corresponding state, outputs, guarded updates and typed clock/gate functions; arbitrary clocks; constant input constraints; async controls inactive. NOT a time-step/settling model or glitch/timing proof.\n");
        else
            fprintf(report, "Contract: sample each %s edge; outputs use current state, D updates next state; clock at active level; constrained inputs constant; async controls inactive.\n",
                    (common_clock & 1) ? "falling" : "rising");
        fprintf(report, "Initial state: %s. This is an analysis contract, not a cell power-up guarantee.\n",
                options.transition ? "arbitrary corresponding state" : "explicit native initial bits; otherwise assumed encoded state zero (see phase manifest)");
        for (size_t i = 0; options.verbose && i < states.size; ++i)
        {
            sn_clock_state_t state = sn_vec_at(sn_clock_state_t, &states, i);
            fprintf(report, "state[%zu]: occurrence=%u object=%u bit=%u kind=%s phase=%d init=%s\n",
                    i, state.occurrence, state.object, state.bit,
                    state.latch ? (state.cell ? "cell-latch-IQ" : "native-latch-Q") : state.cell ? "cell-IQ" : "native-Q",
                    state.phase, state.explicit_init ? "explicit" : options.transition ? "free" : "assumed");
        }
    }
cleanup:
    if (*reason && report)
        fprintf(report, "%s refused: %s (native words=%zu, cell/macro cuts=%zu, LOOP words=%zu).\n",
                options.state_actions ? "State-action signature" : "Clock abstraction",
                *reason, boundary.registers.size, boundary.primitives.size, boundary.loops.size);
    ABC_FREE(final_aliases);
    ABC_FREE(final_roots);
    if (phase_maps)
    {
        for (size_t i = 0; i < design->modules.size; ++i) free(phase_maps[i]);
        free(phase_maps);
    }
    if (state_name_maps)
    {
        for (size_t i = 0; i < design->modules.size; ++i) free(state_name_maps[i]);
        free(state_name_maps);
    }
    if (source) Gia_ManStop(source);
    if (joined) Gia_ManStop(joined);
    if (mini) Mini_AigStop(mini);
    Vec_IntFree(aliases); Vec_IntFree(roots); Vec_IntFree(asyncs);
    Vec_IntFree(unused_cis);
    sn_vec_destroy(&states);
    sn_blast_boundary_destroy(&boundary);
    if (*reason && result) { Gia_ManStop(result); result = NULL; }
    return result;
}

ABC_NAMESPACE_HEADER_END
#endif
