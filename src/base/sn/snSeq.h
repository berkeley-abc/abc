/**CFile****************************************************************

  FileName    [snSeq.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Semantic sequential-cell descriptors for mapping and analysis.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snSeq.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snSeq_h
#define ABC__base__sn__snSeq_h

#include "snLibrary.h"

ABC_NAMESPACE_HEADER_START

enum { SN_SEQ_CLOCK, SN_SEQ_DATA, SN_SEQ_CLEAR, SN_SEQ_PRESET, SN_SEQ_OUTPUT };
// Machine-readable proof requirements. Diagnostics are not an eligibility API.
enum {
    SN_SEQ_PROOF_UNSUPPORTED = 1u << 0,
    SN_SEQ_REQUIRE_RESET_INACTIVE = 1u << 1,
    SN_SEQ_REQUIRE_DUAL_ASYNC = 1u << 2,
    SN_SEQ_REQUIRE_LATCH_ACTIONS = 1u << 3
};
typedef struct sn_seq_info_t
{
    const sn_lib_state_t* state; // borrowed; includes both collision values
    sn_expr_t graph; // physical inputs, then one state bit; roots in the order above
    sn_expr_lit_t clock, data, clear, preset; // semantic projections, or INVALID
    const char *preserve_reason, *sample_reason, *abstract_reason, *map_reason;
    unsigned proof_conditions;
    bool latch;
} sn_seq_info_t;

static inline const char* sn_seq_proof_reason(const sn_seq_info_t* info)
{
    if (info->proof_conditions & SN_SEQ_PROOF_UNSUPPORTED) return info->abstract_reason;
    if (info->proof_conditions & SN_SEQ_REQUIRE_DUAL_ASYNC)
        return "dual async controls require independent collision-state semantics";
    if (info->proof_conditions & SN_SEQ_REQUIRE_LATCH_ACTIONS)
        return "a transparent latch is not an edge-triggered state bit";
    if (info->proof_conditions & SN_SEQ_REQUIRE_RESET_INACTIVE)
        return "requires an explicit reset-inactive abstraction contract";
    return NULL;
}

static inline bool sn_seq_proof_eligible(const sn_seq_info_t* info, bool latch_actions)
{
    unsigned admitted = SN_SEQ_REQUIRE_RESET_INACTIVE | SN_SEQ_REQUIRE_DUAL_ASYNC;
    if (latch_actions) admitted |= SN_SEQ_REQUIRE_LATCH_ACTIONS;
    return (info->proof_conditions & ~admitted) == 0;
}

static inline void sn_seq_info_destroy(sn_seq_info_t* info)
{
    sn_expr_destroy(&info->graph);
    memset(info, 0, sizeof(*info));
}

// Recognize constants or signed input projections semantically, not by Liberty
// spelling or graph shape. Exhaustive fallback is bounded to 12 graph inputs
// (including state); direct literals need no enumeration. Allocation failure
// is reported separately from an unsupported Boolean function.
static inline sn_expr_lit_t sn_seq_projection(const sn_expr_t* graph, sn_expr_lit_t root, bool* oom)
{
    uint64_t candidates;
    unsigned char* values;
    if (!sn_expr_lit_valid(graph, root))
        return SN_EXPR_INVALID;
    if ((root >> 1) <= graph->inputs)
        return root;
    if (graph->inputs > 12)
        return SN_EXPR_INVALID;
    values = (unsigned char*)malloc((size_t)graph->inputs + graph->count + 1);
    if (!values)
    {
        *oom = true;
        return SN_EXPR_INVALID;
    }
    candidates = (UINT64_C(1) << (2 * (graph->inputs + 1))) - 1;
    for (uint32_t pattern = 0; candidates && pattern < (1u << graph->inputs); ++pattern)
    {
        values[0] = 0;
        for (uint32_t input = 0; input < graph->inputs; ++input)
            values[input + 1] = (pattern >> input) & 1;
        for (uint32_t node = 0; node < graph->count; ++node)
        {
            sn_expr_node_t pair = graph->nodes[node];
            values[graph->inputs + node + 1] =
                (values[pair.left >> 1] ^ (pair.left & 1)) &
                (values[pair.right >> 1] ^ (pair.right & 1));
        }
        unsigned value = values[root >> 1] ^ (root & 1);
        for (uint32_t literal = 0; literal < 2 * (graph->inputs + 1); ++literal)
            if ((values[literal >> 1] ^ (literal & 1)) != value)
                candidates &= ~(UINT64_C(1) << literal);
    }
    free(values);
    for (uint32_t literal = 0; candidates && literal < 2 * (graph->inputs + 1); ++literal)
        if (candidates & (UINT64_C(1) << literal))
            return literal;
    return SN_EXPR_INVALID;
}

// True means a descriptor was produced, not that every operation is legal.
// NULL reason means eligible for that capability. The one-state graph assumes
// complementary state variables; callers must honor abstract_reason. Mapping
// a dual-async candidate is legal only with one or both controls tied inactive;
// mapping jointly active source controls remains outside this descriptor's contract.
// No cell functions are converted into SN operators.
static inline bool sn_library_seq_info(const sn_library_t* library, uint32_t cell, sn_seq_info_t* info)
{
    const sn_lib_t* model;
    const sn_lib_cell_t* record;
    const sn_lib_state_t* state = NULL;
    sn_expr_lit_t *roots = NULL, raw[2];
    uint32_t inputs, outputs;
    bool oom = false, success = true;
    memset(info, 0, sizeof(*info));
    sn_expr_init(&info->graph, 0);
    info->proof_conditions = SN_SEQ_PROOF_UNSUPPORTED;
    info->clock = info->data = info->clear = info->preset = SN_EXPR_INVALID;
    info->preserve_reason = info->sample_reason = info->abstract_reason = info->map_reason =
        "not a supported scalar sequential cell";
    if (!sn_library_scalar_cell(library, cell))
        return true;
    model = library->cells[cell].model;
    record = &model->cells[library->cells[cell].local_id];
    if (record->invalid)
        return true;
    // Readability is independent of behavioral support: valid scalar cells
    // can remain opaque even when a state table or bank is not lowered.
    info->preserve_reason = NULL;
    if (record->statetable_count)
        return true;
    for (uint32_t index = record->state_first; index < record->state_first + record->state_count; ++index)
    {
        const sn_lib_state_t* candidate = &model->states[index];
        if (candidate->in_test_cell)
            continue;
        if (state || candidate->invalid || candidate->bits != 1 || candidate->clocked_on_also != SN_LIB_NONE)
            return true;
        state = candidate;
    }
    if (!state)
    {
        info->sample_reason = info->abstract_reason = info->map_reason = "cell has no scalar sequential state";
        return true;
    }
    info->state = state;
    info->latch = state->is_latch;
    if (library->compiled && library->transitions[cell].outputs)
        info->sample_reason = NULL;
    inputs = library->cells[cell].input_count;
    outputs = library->cells[cell].output_count;
    if (!outputs)
    {
        info->abstract_reason = info->map_reason = "cell has no signal output";
        return true;
    }
    sn_expr_init(&info->graph, inputs + 1);
    raw[0] = sn_expr_input(&info->graph, inputs);
    raw[1] = sn_expr_not(raw[0]);
    roots = (sn_expr_lit_t*)malloc(((size_t)outputs + SN_SEQ_OUTPUT) * sizeof(*roots));
    if (!roots)
        return false;
    roots[SN_SEQ_CLOCK] = sn_library_lower(library, cell, sn_lib_expr(model, state->clocked_on), &info->graph);
    roots[SN_SEQ_DATA] = sn_library_lower_bound(library, cell, sn_lib_expr(model, state->next_state),
                                               &info->graph, state, raw);
    roots[SN_SEQ_CLEAR] = state->clear == SN_LIB_NONE ? 0 :
        sn_library_lower(library, cell, sn_lib_expr(model, state->clear), &info->graph);
    roots[SN_SEQ_PRESET] = state->preset == SN_LIB_NONE ? 0 :
        sn_library_lower(library, cell, sn_lib_expr(model, state->preset), &info->graph);
    for (uint32_t output = 0; output < outputs; ++output)
    {
        const sn_lib_pin_t* pin = &model->pins[sn_library_pin(library, cell, SN_LIB_OUTPUT, output)];
        roots[SN_SEQ_OUTPUT + output] = sn_library_output_can_compile(pin) ?
            sn_library_lower_bound(library, cell, sn_lib_expr(model, pin->function), &info->graph, state, raw) :
            SN_EXPR_INVALID;
    }
    for (uint32_t index = 0; index < outputs + SN_SEQ_OUTPUT; ++index)
        success &= roots[index] != SN_EXPR_INVALID;
    if (!success || !sn_expr_finish(&info->graph, outputs + SN_SEQ_OUTPUT, roots))
    {
        info->abstract_reason = info->map_reason = "unsupported sequential expression or output function (including three-state)";
        free(roots);
        return !info->graph.failed;
    }
    info->clock = sn_seq_projection(&info->graph, roots[SN_SEQ_CLOCK], &oom);
    info->data = sn_seq_projection(&info->graph, roots[SN_SEQ_DATA], &oom);
    info->clear = sn_seq_projection(&info->graph, roots[SN_SEQ_CLEAR], &oom);
    info->preset = sn_seq_projection(&info->graph, roots[SN_SEQ_PRESET], &oom);
    free(roots);
    info->abstract_reason = info->map_reason = NULL;
    if (info->clock == SN_EXPR_INVALID || (info->clock >> 1) == 0 || (info->clock >> 1) > inputs)
        info->abstract_reason = info->map_reason = "clock/gate is not a physical-pin projection";
    else if (info->clear == SN_EXPR_INVALID || info->preset == SN_EXPR_INVALID ||
             (info->clear && ((info->clear >> 1) == 0 || (info->clear >> 1) > inputs)) ||
             (info->preset && ((info->preset >> 1) == 0 || (info->preset >> 1) > inputs)))
        info->abstract_reason = info->map_reason = "async control is not a physical-pin projection";
    for (uint32_t output = 0; output < outputs && !info->abstract_reason; ++output)
    {
        sn_expr_lit_t projection = sn_seq_projection(&info->graph, info->graph.roots[SN_SEQ_OUTPUT + output], &oom);
        if ((projection >> 1) != inputs + 1)
            info->abstract_reason = info->map_reason = "output is not a state projection under complementarity";
    }
    if (!info->abstract_reason)
    {
        info->proof_conditions = state->is_latch ? SN_SEQ_REQUIRE_LATCH_ACTIONS : 0;
        if (state->clear != SN_LIB_NONE || state->preset != SN_LIB_NONE)
            info->proof_conditions |= SN_SEQ_REQUIRE_RESET_INACTIVE;
        if (state->clear != SN_LIB_NONE && state->preset != SN_LIB_NONE)
            info->proof_conditions |= SN_SEQ_REQUIRE_DUAL_ASYNC;
    }
    if (!info->map_reason)
    {
        if (info->data == SN_EXPR_INVALID || (info->data >> 1) == 0 || (info->data >> 1) > inputs)
            info->map_reason = "candidate data is not a physical-pin projection; sequential control absorption is unavailable";
        else
        {
            // Every physical input must have exactly one verified role. No
            // guessing scan values or tying otherwise unexplained inputs.
            for (uint32_t input = 1; input <= inputs; ++input)
            {
                unsigned roles = ((info->clock >> 1) == input) + ((info->data >> 1) == input) +
                                 ((info->clear >> 1) == input) + ((info->preset >> 1) == input);
                if (roles != 1)
                    info->map_reason = "unassigned or shared physical input role; verified ties are required";
            }
        }
    }
    if (!info->map_reason && state->is_latch && (state->clear != SN_LIB_NONE || state->preset != SN_LIB_NONE))
        info->map_reason = "only plain latch candidates are supported";
    if (!info->map_reason && record->dont_use)
        info->map_reason = "cell is marked dont_use";
    if (!info->map_reason && (!isfinite(record->area) || record->area < 0))
        info->map_reason = "cell has no usable area for deterministic selection";
    if (info->map_reason && info->graph.inputs > 12 &&
        (info->clock == SN_EXPR_INVALID || info->data == SN_EXPR_INVALID ||
         info->clear == SN_EXPR_INVALID || info->preset == SN_EXPR_INVALID))
    {
        info->map_reason = "projection not established: exhaustive fallback limited to 12 graph inputs";
        if (info->proof_conditions & SN_SEQ_PROOF_UNSUPPORTED) info->abstract_reason = info->map_reason;
    }
    info->abstract_reason = sn_seq_proof_reason(info);
    return !oom;
}

ABC_NAMESPACE_HEADER_END
#endif
