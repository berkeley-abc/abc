/**CFile****************************************************************

  FileName    [snMapFf.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Conservative native-register legalization into Liberty cells.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMapFf.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snMapFf_h
#define ABC__base__sn__snMapFf_h

#include "snBoundary.h"
#include "snSeq.h"

ABC_NAMESPACE_HEADER_START

typedef struct sn_ff_map_stats_t
{
    size_t modules, registers, bits, latches, clock_inversions, inactive_ties;
} sn_ff_map_stats_t;

static inline sn_obj_id_t sn_ff_invert(sn_module_t* module, sn_obj_id_t input,
                                      sn_obj_id_t* cache, size_t cache_size)
{
    if (input < cache_size && cache[input] != SN_INVALID_ID)
        return cache[input];
    sn_obj_id_t result = sn_module_add_operator(module, SN_BIT_NOT, sn_obj_width(module, input),
                                               sn_obj_is_signed(module, input), 1, &input, NULL);
    if (input < cache_size)
        cache[input] = result;
    return result;
}
static inline sn_obj_id_t sn_ff_bit(sn_module_t* module, sn_obj_id_t word, uint32_t bit)
{
    return sn_obj_width(module, word) == 1 ? word : sn_module_add_slice(module, word, (int32_t)bit, (int32_t)bit, NULL);
}

// Native latch data is observable only while its active-high gate is open.
// Cofactor its RTL-operator cone by gate=1 before physical-cell emission. In
// particular, do not carry the frontend's masked default-zero data into a cell:
// it needlessly makes D switch on the closing gate edge. State/instance/gate
// objects are boundaries, never expanded or duplicated as elementary logic.
static inline sn_obj_id_t sn_ff_latch_data(sn_module_t* module, sn_obj_id_t data, sn_obj_id_t gate)
{
    size_t count = module->obj_types.size;
    sn_obj_id_t* copies = (sn_obj_id_t*)malloc(count * sizeof(*copies));
    sn_obj_id_t* stack = (sn_obj_id_t*)malloc(count * sizeof(*stack));
    if (!copies || !stack)
    {
        free(copies); free(stack);
        return SN_INVALID_ID;
    }
    for (size_t object = 0; object < count; ++object)
        copies[object] = SN_INVALID_ID;
    uint32_t one = 1;
    copies[gate] = sn_module_add_const(module, 1, false, &one, NULL);
    // The frontend may express a Boolean enable as sel ? 1 : 0, while
    // the data mux uses sel directly. Follow this exact identity (and its
    // complement) so the cofactor reaches the actual shared predicate.
    uint32_t active_value = 1;
    sn_obj_id_t predicate = gate;
    while (sn_obj_width(module, predicate) == 1)
    {
        sn_obj_type_t type = sn_obj_type(module, predicate);
        sn_obj_id_t next = SN_INVALID_ID;
        if (type == SN_MUX)
        {
            sn_obj_id_t yes = sn_obj_fanin(module, predicate, SN_MUX_SELECTED);
            sn_obj_id_t no = sn_obj_fanin(module, predicate, SN_MUX_DEFAULT);
            bool positive = sn_obj_is_const_one_bit(module, yes) && sn_obj_is_const_zero(module, no);
            bool negative = sn_obj_is_const_zero(module, yes) && sn_obj_is_const_one_bit(module, no);
            if (positive || negative)
            {
                next = sn_obj_fanin(module, predicate, SN_MUX_SELECT);
                active_value ^= negative;
            }
        }
        else if (type == SN_CAST || type == SN_POS || type == SN_BIT_NOT || type == SN_LOG_NOT)
        {
            sn_obj_id_t input = sn_obj_fanin(module, predicate, 0);
            if (sn_obj_width(module, input) == 1)
            {
                next = input;
                active_value ^= type == SN_BIT_NOT || type == SN_LOG_NOT;
            }
        }
        if (next == SN_INVALID_ID)
            break;
        predicate = next;
        copies[predicate] = sn_module_add_const(module, 1, false, &active_value, NULL);
    }
    size_t depth = 0;
    stack[depth++] = data;
    while (depth)
    {
        sn_obj_id_t object = stack[depth - 1];
        if (copies[object] != SN_INVALID_ID)
        {
            --depth;
            continue;
        }
        if (!sn_obj_type_is_operator(sn_obj_type(module, object)))
        {
            copies[object] = object;
            --depth;
            continue;
        }
        bool changed = false;
        sn_obj_id_t pending = SN_INVALID_ID;
        uint32_t fanins = sn_obj_fanin_count(module, object);
        for (uint32_t pin = 0; pin < fanins; ++pin)
        {
            sn_obj_id_t input = sn_obj_fanin(module, object, pin);
            if (copies[input] == SN_INVALID_ID)
                pending = input;
            changed |= copies[input] != input;
        }
        if (pending != SN_INVALID_ID)
        {
            stack[depth++] = pending;
            continue;
        }
        copies[object] = object;
        if (changed)
        {
            copies[object] = sn_module_dup_obj_skeleton(module, module, object);
            sn_module_dup_obj_metadata(module, copies[object], module, object);
            for (uint32_t pin = 0; pin < fanins; ++pin)
                sn_obj_connect(module, copies[object], pin, copies[sn_obj_fanin(module, object, pin)]);
        }
        --depth;
    }
    sn_obj_id_t result = copies[data];
    free(copies); free(stack);
    return result;
}

// Mutates only a disposable replacement design. The command owns the outer
// transaction and must discard it on any failure. Definitions are visited once
// and replaced at stable IDs; repeated instances remain shared.
static inline bool sn_design_map_ff(sn_design_t* design, sn_module_id_t root, const uint8_t* target_cells,
                                    sn_ff_map_stats_t* stats, FILE* diagnostics)
{
    sn_library_t* library = design->library;
    sn_seq_info_t* candidates = NULL;
    uint8_t* reachable = NULL;
    sn_obj_id_t *replacement = NULL, *inverted = NULL, *bit_outputs = NULL;
    uint8_t* remove = NULL;
    sn_vec_t pending;
    const char* reason = NULL;
    sn_module_id_t module_id = root;
    sn_obj_id_t reg = SN_INVALID_ID;
    uint32_t bit = 0;
    size_t module_count = design->modules.size;
    memset(stats, 0, sizeof(*stats));
    sn_vec_init(&pending);
    if (!library || !target_cells || !sn_library_compile(library))
    {
        reason = "no checked mapping-target library";
        goto cleanup;
    }
    candidates = (sn_seq_info_t*)calloc(library->cell_count, sizeof(*candidates));
    reachable = (uint8_t*)calloc(module_count, 1);
    if (!candidates || !reachable)
    {
        reason = "allocation failure";
        goto cleanup;
    }
    for (uint32_t cell = 0; cell < library->cell_count; ++cell)
        if (target_cells[cell] && !sn_library_seq_info(library, cell, &candidates[cell]))
        {
            reason = "allocation failure in sequential descriptor";
            goto cleanup;
        }
    *sn_vec_push(sn_module_id_t, &pending) = root;
    while (pending.size)
    {
        sn_module_id_t id = sn_vec_at(sn_module_id_t, &pending, --pending.size);
        if (reachable[id])
            continue;
        reachable[id] = 1;
        const sn_module_t* module = sn_design_get_module_const(design, id);
        for (size_t instance = 0; instance < module->type_objects[SN_INST].size; ++instance)
            *sn_vec_push(sn_module_id_t, &pending) = sn_inst_module_id(module,
                sn_vec_at(sn_obj_id_t, &module->type_objects[SN_INST], instance));
    }
    for (module_id = 0; module_id < module_count; ++module_id)
    {
        sn_module_t* module = sn_design_get_module(design, module_id);
        size_t object_count = module->obj_types.size;
        size_t register_count = module->type_objects[SN_REG_OUT].size;
        if (!reachable[module_id] || !register_count)
            continue;
        replacement = (sn_obj_id_t*)malloc(object_count * sizeof(*replacement));
        inverted = (sn_obj_id_t*)malloc(object_count * sizeof(*inverted));
        if (!replacement || !inverted)
        {
            reason = "allocation failure in register replacement";
            goto cleanup;
        }
        for (size_t object = 0; object < object_count; ++object)
            replacement[object] = inverted[object] = SN_INVALID_ID;
        // The REG vector never grows or shrinks in this loop. Removal is one
        // filtered topological copy after every consumer has been redirected.
        for (size_t index = 0; index < register_count; ++index)
        {
            reg = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], index);
            uint32_t width = sn_obj_width(module, reg), flags = sn_obj_reg_flags(module, reg);
            bool latch = (flags & SN_REG_LATCH) != 0;
            sn_obj_id_t data = sn_reg_fanin(module, reg, SN_REG_DATA);
            sn_obj_id_t clock = sn_reg_fanin(module, reg, latch ? SN_REG_ENABLE : SN_REG_CLOCK);
            sn_obj_id_t enable = latch ? SN_INVALID_ID : sn_reg_fanin(module, reg, SN_REG_ENABLE);
            sn_obj_id_t set = sn_reg_fanin(module, reg, SN_REG_SET);
            sn_obj_id_t reset = sn_reg_fanin(module, reg, SN_REG_RESET);
            sn_obj_id_t reset_value = sn_reg_fanin(module, reg, SN_REG_RESET_VALUE);
            sn_obj_id_t initial = sn_obj_reg_init_data(module, reg), mask = sn_obj_reg_init_mask(module, reg);
            bool async_reset = reset != SN_INVALID_ID && (flags & SN_REG_RESET_ASYNC);
            bool async_set = set != SN_INVALID_ID && (flags & SN_REG_SET_ASYNC);
            if (clock == SN_INVALID_ID || data == SN_INVALID_ID ||
                (latch && (set != SN_INVALID_ID || reset != SN_INVALID_ID || flags != SN_REG_LATCH)))
            {
                reason = "register/latch has an unsupported control interface";
                goto cleanup;
            }
            if (reset_value != SN_INVALID_ID && sn_obj_width(module, reset_value) < width)
            {
                reason = "reset value is narrower than the register";
                goto cleanup;
            }
            if (async_set && reset != SN_INVALID_ID)
            {
                reason = "async set with higher-priority reset requires joint control semantics";
                goto cleanup;
            }
            if (async_reset && reset_value != SN_INVALID_ID &&
                sn_obj_type(module, reset_value) != SN_CONST && sn_obj_type(module, reset_value) != SN_CONST0 &&
                sn_obj_type(module, reset_value) != SN_CONST1)
            {
                reason = "asynchronous reset value is not constant";
                goto cleanup;
            }
            if (latch)
            {
                data = sn_ff_latch_data(module, data, clock);
                if (data == SN_INVALID_ID)
                {
                    reason = "allocation failure while cofactoring latch data";
                    goto cleanup;
                }
            }
            sn_obj_pair_t feedback = sn_module_add_loop_pair(module, width, sn_obj_is_signed(module, reg), NULL, NULL);
            sn_vec_at(sn_name_id_t, &module->name_ids, feedback.out) = sn_obj_name_id(module, reg);
            sn_module_dup_obj_annotations(module, feedback.out, module, reg);
            sn_module_dup_obj_annotations(module, feedback.in, module, sn_obj_pair_in(module, reg));
            replacement[reg] = feedback.out;
            bit_outputs = (sn_obj_id_t*)malloc(width * sizeof(*bit_outputs));
            if (!bit_outputs)
            {
                reason = "allocation failure in register bits";
                goto cleanup;
            }
            for (bit = 0; bit < width; ++bit)
            {
                uint32_t chosen = SN_LIB_NONE;
                bool phase = false, output_phase = false;
                double best_area = HUGE_VAL;
                bool reset_bit = async_set || (async_reset && reset_value != SN_INVALID_ID && sn_const_bit(module, reset_value, bit));
                if (initial != SN_INVALID_ID && (mask == SN_INVALID_ID || sn_const_bit(module, mask, bit)))
                {
                    reason = "explicit initialization cannot be guaranteed by an ordinary Liberty cell";
                    goto cleanup;
                }
                for (uint32_t cell = 0; cell < library->cell_count; ++cell)
                {
                    const sn_seq_info_t* candidate = &candidates[cell];
                    if (!target_cells[cell] || !candidate->state || candidate->map_reason || candidate->latch != latch ||
                        ((async_reset || async_set) && candidate->clear == 0 && candidate->preset == 0))
                        continue;
                    const sn_library_cell_t* cell_interface = &library->cells[cell];
                    double area = cell_interface->model->cells[cell_interface->local_id].area;
                    if (area >= best_area)
                        continue; // equal costs keep parser-order cell ID
                    bool oom = false;
                    sn_expr_lit_t output = sn_seq_projection(&candidate->graph,
                        candidate->graph.roots[SN_SEQ_OUTPUT], &oom);
                    if (oom)
                    {
                        reason = "allocation failure in output projection";
                        goto cleanup;
                    }
                    chosen = cell;
                    best_area = area;
                    output_phase = (output & 1) != 0;
                    // Prefer clear when both controls exist; the unused
                    // control is tied inactive, making collisions unreachable.
                    phase = async_reset || async_set ? reset_bit != (candidate->clear == 0) : output_phase;
                }
                if (chosen == SN_LIB_NONE)
                {
                    reason = "no legal sequential cell in the selected target models";
                    goto cleanup;
                }
                const sn_seq_info_t* candidate = &candidates[chosen];
                uint32_t pin_count = library->cells[chosen].input_count;
                sn_obj_id_t pins[4]; // clock, data, clear, preset; every role is distinct
                if (pin_count > 4)
                { reason = "candidate exceeds the four distinct sequential pin roles"; goto cleanup; }
                sn_obj_id_t next = sn_ff_bit(module, data, bit);
                if (enable != SN_INVALID_ID)
                    next = sn_module_add_mux(module, enable, next, sn_ff_bit(module, feedback.out, bit), NULL);
                if (set != SN_INVALID_ID && !async_set)
                {
                    sn_obj_id_t active = flags & SN_REG_SET_NEGEDGE ? sn_ff_invert(module, set, inverted, object_count) : set;
                    uint32_t one = 1;
                    next = sn_module_add_mux(module, active, sn_module_add_const(module, 1, false, &one, NULL), next, NULL);
                }
                if (reset != SN_INVALID_ID && !async_reset)
                {
                    sn_obj_id_t active = flags & SN_REG_RESET_NEGEDGE ? sn_ff_invert(module, reset, inverted, object_count) : reset;
                    uint32_t zero = 0;
                    sn_obj_id_t value = reset_value == SN_INVALID_ID ?
                        sn_module_add_const(module, 1, false, &zero, NULL) : sn_ff_bit(module, reset_value, bit);
                    next = sn_module_add_mux(module, active, value, next, NULL);
                }
                if (phase != ((candidate->data & 1) != 0))
                    next = sn_ff_invert(module, next, inverted, object_count);
                pins[(candidate->data >> 1) - 1] = next;
                bool invert_clock = ((candidate->clock & 1) != 0) != (!latch && (flags & SN_REG_CLOCK_NEGEDGE));
                pins[(candidate->clock >> 1) - 1] = invert_clock ? sn_ff_invert(module, clock, inverted, object_count) : clock;
                stats->clock_inversions += invert_clock;
                if (async_reset || async_set)
                {
                    sn_obj_id_t control = async_reset ? reset : set;
                    bool active_low = (flags & (async_reset ? SN_REG_RESET_NEGEDGE : SN_REG_SET_NEGEDGE)) != 0;
                    sn_expr_lit_t port = candidate->clear ? candidate->clear : candidate->preset;
                    pins[(port >> 1) - 1] = active_low != ((port & 1) != 0) ?
                        sn_ff_invert(module, control, inverted, object_count) : control;
                }
                sn_expr_lit_t active_port = async_reset || async_set ?
                    (candidate->clear ? candidate->clear : candidate->preset) : 0;
                sn_expr_lit_t async_ports[] = {candidate->clear, candidate->preset};
                for (unsigned port = 0; port < 2; ++port)
                    if (async_ports[port] && async_ports[port] != active_port)
                    {
                        uint32_t inactive = async_ports[port] & 1;
                        pins[(async_ports[port] >> 1) - 1] = sn_module_add_const(module, 1, false, &inactive, NULL);
                        ++stats->inactive_ties;
                    }
                char name[80];
                snprintf(name, sizeof(name), "sn_ff_%u_%u", reg, bit);
                sn_obj_id_t gate = sn_module_add_library_gate(module, chosen, pins, name, NULL);
                // Proof correspondence only: logical source Q = cell IQ XOR
                // phase. This survives SN round trips and combinational @put;
                // it does not claim any physical initialization requirement.
                sn_module_add_attribute_record(module, gate, "sn_state_phase", phase ? "1" : "0");
                if (sn_obj_name_id(module, reg) != SN_INVALID_ID)
                {
                    // Preserve the logical source bit separately from the
                    // generated physical cell instance name. Copy pool text
                    // before adding an attribute can grow the name manager.
                    const char* source_name = sn_obj_name(module, reg);
                    char* state_name = (char*)malloc(strlen(source_name) + 32);
                    if (!state_name) { reason = "allocation failure naming mapped state"; goto cleanup; }
                    sprintf(state_name, "%s[%u]", source_name, bit);
                    sn_module_add_attribute_record(module, gate, "sn_state_name", state_name);
                    free(state_name);
                }
                sn_obj_id_t output = sn_owner_output(module, gate, 0);
                if (phase != output_phase)
                    output = sn_ff_invert(module, output, inverted, object_count);
                bit_outputs[bit] = output;
                ++stats->bits;
                stats->latches += latch;
            }
            sn_obj_id_t packed = width == 1 ? bit_outputs[0] : sn_module_add_concat(module, width, bit_outputs, NULL);
            sn_obj_connect(module, feedback.in, 0, packed);
            free(bit_outputs);
            bit_outputs = NULL;
            ++stats->registers;
        }
        remove = (uint8_t*)calloc(module->obj_types.size, 1);
        if (!remove)
        {
            reason = "allocation failure in register removal";
            goto cleanup;
        }
        for (size_t index = 0; index < register_count; ++index)
        {
            reg = sn_vec_at(sn_obj_id_t, &module->type_objects[SN_REG_OUT], index);
            remove[reg] = remove[sn_obj_pair_in(module, reg)] = 1;
        }
        for (sn_obj_id_t object = 0; object < module->obj_types.size; ++object)
            if (!remove[object])
                for (uint32_t pin = 0; pin < sn_obj_fanin_count(module, object); ++pin)
                {
                    sn_obj_id_t fanin = sn_obj_fanin(module, object, pin);
                    if (fanin < object_count && replacement[fanin] != SN_INVALID_ID)
                        sn_obj_connect(module, object, pin, replacement[fanin]);
                }
        sn_name_id_t name = module->name;
        char temporary[80];
        uint32_t suffix = (uint32_t)design->modules.size;
        do { snprintf(temporary, sizeof(temporary), "sn_ff_module_%u", suffix++); }
        while (sn_design_find_module(design, temporary) != SN_INVALID_ID);
        sn_module_id_t rebuilt = sn_boundary_dup_filtered_topo(design, module_id, remove, temporary);
        sn_design_replace_appended_module(design, module_id, name, rebuilt);
        free(remove); remove = NULL;
        free(replacement); replacement = NULL;
        free(inverted); inverted = NULL;
        ++stats->modules;
    }
cleanup:
    if (reason && diagnostics)
        fprintf(diagnostics, "Cannot map FF: module %u, register %u, bit %u: %s.\n", module_id, reg, bit, reason);
    if (candidates)
        for (uint32_t cell = 0; cell < library->cell_count; ++cell)
            sn_seq_info_destroy(&candidates[cell]);
    free(candidates);
    free(reachable);
    free(replacement);
    free(inverted);
    free(bit_outputs);
    free(remove);
    sn_vec_destroy(&pending);
    return !reason;
}

ABC_NAMESPACE_HEADER_END
#endif
