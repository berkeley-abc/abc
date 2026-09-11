/**CFile****************************************************************

  FileName    [snLibrary.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Shared Liberty library ownership and gate-function compilation.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snLibrary.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_LIBRARY_H
#define SN_LIBRARY_H

#include "snLiberty.h"
#include "snExpr.h"
ABC_NAMESPACE_HEADER_START

// Shared, immutable interface/model ownership. Cell IDs concatenate parser indices in file order.
// Derived expressions are compiled by the ABC library-loading path, not by the
// frontend. Each output root belongs to the same graph, with explicit pin order.
typedef struct sn_library_cell_t
{
    sn_lib_t* model;
    uint32_t local_id;
    uint32_t input_first, input_count;
    uint32_t output_first, output_count;
    bool scalar;
    const char* unsupported_reason; // static diagnostic; NULL for a compiled cell
} sn_library_cell_t;

typedef struct sn_library_t
{
    uint32_t references;
    sn_lib_t* model;
    sn_lib_t** models; // independent namespaces; model aliases models[0] for single-library callers
    uint32_t model_count, cell_count, pin_count;
    sn_expr_t* functions;
    sn_expr_t* transitions; // FF roots: var1', var2', previous-clock'; three local state inputs after pins
    sn_library_cell_t* cells;
    uint32_t* pins;             // grouped inputs then outputs per cell; indices into model->pins
    size_t blast_scratch_count; // largest replay map plus roots, shared by all occurrences in a frame
    uint32_t unsupported_count;
    bool compiled;
} sn_library_t;

// Takes ownership of model on every path, including failure.
static inline sn_library_t* sn_library_create(sn_lib_t* model)
{
    if (!sn_lib_ok(model))
    {
        sn_lib_destroy(model);
        return NULL;
    }
    sn_library_t* library = (sn_library_t*)calloc(1, sizeof(*library));
    if (!library)
    {
        sn_lib_destroy(model);
        return NULL;
    }
    library->references = 1;
    library->model = model;
    library->models = (sn_lib_t**)malloc(sizeof(*library->models));
    library->cells = (sn_library_cell_t*)calloc(model->cells_count, sizeof(*library->cells));
    library->pins = (uint32_t*)malloc((size_t)model->pins_count * sizeof(*library->pins));
    if (!library->models || (model->cells_count && !library->cells) || (model->pins_count && !library->pins))
    {
        free(library->cells);
        free(library->pins);
        free(library->models);
        sn_lib_destroy(model);
        free(library);
        return NULL;
    }
    library->models[0] = model;
    library->model_count = 1;
    library->cell_count = model->cells_count;
    uint32_t next = 0;
    for (uint32_t cell = 0; cell < model->cells_count; cell++)
    {
        const sn_lib_cell_t* source = &model->cells[cell];
        sn_library_cell_t* cell_interface = &library->cells[cell];
        cell_interface->model = model;
        cell_interface->local_id = cell;
        cell_interface->scalar = !source->invalid;
        for (uint32_t pin_id = source->pin_first; pin_id < source->pin_first + source->pin_count; pin_id++)
        {
            const sn_lib_pin_t* pin = &model->pins[pin_id];
            if (pin->in_test_cell || pin->kind == SN_LIB_PIN_PG || pin->direction == SN_LIB_INTERNAL)
                continue;
            if (pin->invalid || pin->kind != SN_LIB_PIN_SCALAR ||
                (pin->direction != SN_LIB_INPUT && pin->direction != SN_LIB_OUTPUT))
                cell_interface->scalar = false;
        }
        cell_interface->input_first = next;
        for (uint32_t pin_id = source->pin_first; pin_id < source->pin_first + source->pin_count; pin_id++)
        {
            const sn_lib_pin_t* pin = &model->pins[pin_id];
            if (!pin->in_test_cell && pin->kind == SN_LIB_PIN_SCALAR && pin->direction == SN_LIB_INPUT)
                library->pins[next++] = pin_id;
        }
        cell_interface->input_count = next - cell_interface->input_first;
        cell_interface->output_first = next;
        for (uint32_t pin_id = source->pin_first; pin_id < source->pin_first + source->pin_count; pin_id++)
        {
            const sn_lib_pin_t* pin = &model->pins[pin_id];
            if (!pin->in_test_cell && pin->kind == SN_LIB_PIN_SCALAR && pin->direction == SN_LIB_OUTPUT)
                library->pins[next++] = pin_id;
        }
        cell_interface->output_count = next - cell_interface->output_first;
        cell_interface->scalar &= cell_interface->output_count != 0;
    }
    library->pin_count = next;
    return library;
}
static inline sn_library_t* sn_library_retain(sn_library_t* library)
{
    if (library)
        library->references++;
    return library;
}
static inline void sn_library_release(sn_library_t* library)
{
    if (!library || --library->references)
        return;
    if (library->functions)
        for (uint32_t cell_index = 0; cell_index < library->cell_count; cell_index++)
        {
            sn_expr_destroy(&library->functions[cell_index]);
            sn_expr_destroy(&library->transitions[cell_index]);
        }
    free(library->cells);
    free(library->pins);
    free(library->functions);
    free(library->transitions);
    for (uint32_t index = 0; index < library->model_count; index++)
        sn_lib_destroy(library->models[index]);
    free(library->models);
    free(library);
}

static inline const char* sn_library_cell_name(const sn_library_t* library, uint32_t cell)
{
    const sn_library_cell_t* entry = &library->cells[cell];
    return sn_lib_name(entry->model, entry->model->cells[entry->local_id].name);
}

static inline uint32_t sn_library_find_cell(const sn_library_t* library, const char* name)
{
    uint32_t offset = 0;
    for (uint32_t index = 0; library && index < library->model_count; index++)
    {
        uint32_t local = sn_lib_find_cell(library->models[index], name);
        if (local != SN_LIB_NONE)
            return offset + local;
        offset += library->models[index]->cells_count;
    }
    return SN_LIB_NONE;
}

static inline uint64_t sn_library_warning_count(const sn_library_t* library)
{
    uint64_t count = 0;
    for (uint32_t index = 0; library && index < library->model_count; index++)
        count += library->models[index]->warnings_count;
    return count;
}

// Append before sharing/compilation. On success consumes addition; on failure
// neither owner changes. Duplicate cell names are rejected, not rebound.
static inline bool sn_library_append(sn_library_t* library, sn_library_t* addition)
{
    if (!library || !addition || library == addition || library->references != 1 ||
        addition->references != 1 || library->compiled || addition->compiled ||
        addition->cell_count > UINT32_MAX - library->cell_count ||
        addition->pin_count > UINT32_MAX - library->pin_count ||
        addition->model_count > UINT32_MAX - library->model_count)
        return false;
    for (uint32_t cell = 0; cell < addition->cell_count; cell++)
        if (sn_library_find_cell(library, sn_library_cell_name(addition, cell)) != SN_LIB_NONE)
            return false;
    size_t cell_count = (size_t)library->cell_count + addition->cell_count;
    size_t pin_count = (size_t)library->pin_count + addition->pin_count;
    size_t model_count = (size_t)library->model_count + addition->model_count;
    if (cell_count > SIZE_MAX / sizeof(*library->cells) || pin_count > SIZE_MAX / sizeof(*library->pins) ||
        model_count > SIZE_MAX / sizeof(*library->models))
        return false;
    sn_library_cell_t* cells = (sn_library_cell_t*)malloc((cell_count + !cell_count) * sizeof(*cells));
    uint32_t* pins = (uint32_t*)malloc((pin_count + !pin_count) * sizeof(*pins));
    sn_lib_t** models = (sn_lib_t**)malloc(model_count * sizeof(*models));
    if (!cells || !pins || !models)
    {
        free(cells);
        free(pins);
        free(models);
        return false;
    }
    for (uint32_t cell = 0; cell < library->cell_count; cell++)
        cells[cell] = library->cells[cell];
    for (uint32_t cell = 0; cell < addition->cell_count; cell++)
    {
        cells[library->cell_count + cell] = addition->cells[cell];
        cells[library->cell_count + cell].input_first += library->pin_count;
        cells[library->cell_count + cell].output_first += library->pin_count;
    }
    for (uint32_t pin = 0; pin < library->pin_count; pin++)
        pins[pin] = library->pins[pin];
    for (uint32_t pin = 0; pin < addition->pin_count; pin++)
        pins[library->pin_count + pin] = addition->pins[pin];
    memcpy(models, library->models, library->model_count * sizeof(*models));
    memcpy(models + library->model_count, addition->models, addition->model_count * sizeof(*models));
    free(library->cells);
    free(library->pins);
    free(library->models);
    library->cells = cells;
    library->pins = pins;
    library->models = models;
    library->cell_count = (uint32_t)cell_count;
    library->pin_count = (uint32_t)pin_count;
    library->model_count = (uint32_t)model_count;
    addition->model_count = 0; // models have transferred; only its derived index arrays remain
    sn_library_release(addition);
    return true;
}
static inline uint32_t sn_library_pin(const sn_library_t* library, uint32_t cell, uint32_t direction,
                                      uint32_t index)
{
    if (!library || cell >= library->cell_count)
        return SN_LIB_NONE;
    const sn_library_cell_t* cell_interface = &library->cells[cell];
    if (direction == SN_LIB_INPUT && index < cell_interface->input_count)
        return library->pins[cell_interface->input_first + index];
    if (direction == SN_LIB_OUTPUT && index < cell_interface->output_count)
        return library->pins[cell_interface->output_first + index];
    return SN_LIB_NONE;
}

// Copy the immutable models through the checked functional codec. This gives
// append/rebinding transactions exclusive ownership without copying timing
// tables that are deliberately outside an SN design's persisted contract.
static inline sn_library_t* sn_library_clone_models(const sn_library_t* source)
{
    sn_library_t* result = NULL;
    sn_lib_binary_options_t options = {true};
    for (uint32_t index = 0; source && index < source->model_count; ++index)
    {
        uint8_t* bytes = NULL;
        size_t size = 0;
        if (!sn_lib_encode_binary(source->models[index], &options, &bytes, &size))
        {
            sn_library_release(result);
            return NULL;
        }
        sn_lib_t* model = sn_lib_decode_binary(bytes, size, source->models[index]->path);
        free(bytes);
        sn_library_t* addition = sn_library_create(model);
        if (!addition || (result && !sn_library_append(result, addition)))
        {
            sn_library_release(addition);
            sn_library_release(result);
            return NULL;
        }
        if (!result)
            result = addition;
    }
    return result;
}
static inline uint32_t sn_library_port_count(const sn_library_t* library, uint32_t cell, uint32_t direction)
{
    if (!library || cell >= library->cell_count)
        return 0;
    return direction == SN_LIB_INPUT    ? library->cells[cell].input_count
           : direction == SN_LIB_OUTPUT ? library->cells[cell].output_count
                                        : 0;
}
static inline bool sn_library_scalar_cell(const sn_library_t* library, uint32_t cell)
{
    return library && cell < library->cell_count && library->cells[cell].scalar;
}

static inline const char* sn_library_pin_name(const sn_library_t* library, uint32_t cell, uint32_t direction,
                                              uint32_t index)
{
    uint32_t pin = sn_library_pin(library, cell, direction, index);
    if (pin == SN_LIB_NONE)
        return NULL;
    const sn_lib_t* model = library->cells[cell].model;
    return sn_lib_name(model, model->pins[pin].name);
}

// Lower one already-parsed Liberty expression into a shared local graph. No
// textual reparse through Mio, whose operator precedence differs from Liberty.
static inline sn_expr_lit_t sn_library_lower_bound(const sn_library_t* library, uint32_t cell,
                                                   const sn_liberty_expr_t* parsed, sn_expr_t* graph,
                                                   const sn_lib_state_t* state, const sn_expr_lit_t* values)
{
    if (!parsed || parsed->root >= parsed->count)
        return SN_EXPR_INVALID;
    const sn_lib_t* model = library->cells[cell].model;
    sn_expr_lit_t* map = (sn_expr_lit_t*)malloc((size_t)parsed->count * sizeof(*map));
    if (!map)
    {
        graph->failed = true;
        return SN_EXPR_INVALID;
    }
    bool ok = true;
    for (uint32_t i = 0; ok && i < parsed->count; i++)
    {
        const sn_liberty_node_t* node = &parsed->nodes[i];
        sn_expr_lit_t literal = SN_EXPR_INVALID;
        if (node->op == SN_LIBERTY_CONST0 || node->op == SN_LIBERTY_CONST1)
            literal = node->op == SN_LIBERTY_CONST1;
        else if (node->op == SN_LIBERTY_PIN)
        {
            const char* name = sn_liberty_expr_pin_name(parsed, i);
            for (uint32_t input_index = 0; input_index < sn_library_port_count(library, cell, SN_LIB_INPUT);
                 input_index++)
            {
                uint32_t pin = sn_library_pin(library, cell, SN_LIB_INPUT, input_index);
                if (strcmp(name, sn_lib_name(model, model->pins[pin].name)) == 0)
                {
                    literal = sn_expr_input(graph, input_index);
                    break;
                }
            }
            if (state && literal == SN_EXPR_INVALID)
            {
                if (!strcmp(name, sn_lib_name(model, state->var1)))
                    literal = values[0];
                else if (state->var2 != SN_LIB_NONE && !strcmp(name, sn_lib_name(model, state->var2)))
                    literal = values[1];
            }
        }
        else if (node->left < i && node->op == SN_LIBERTY_NOT)
            literal = sn_expr_not(map[node->left]);
        else if (node->left < i && node->right < i)
        {
            if (node->op == SN_LIBERTY_AND)
                literal = sn_expr_and(graph, map[node->left], map[node->right]);
            else if (node->op == SN_LIBERTY_OR)
                literal = sn_expr_or(graph, map[node->left], map[node->right]);
            else if (node->op == SN_LIBERTY_XOR)
                literal = sn_expr_xor(graph, map[node->left], map[node->right]);
        }
        map[i] = literal;
        ok = literal != SN_EXPR_INVALID;
    }
    sn_expr_lit_t result = ok ? map[parsed->root] : SN_EXPR_INVALID;
    free(map);
    return result;
}
static inline sn_expr_lit_t sn_library_lower(const sn_library_t* library, uint32_t cell,
                                             const sn_liberty_expr_t* parsed, sn_expr_t* graph)
{
    return sn_library_lower_bound(library, cell, parsed, graph, NULL, NULL);
}

// Latch behavior is not lowered to sampled FFs. Valid scalar latch cells can
// instead be retained as opaque gates with every signal pin on the boundary.
static inline bool sn_library_latch_boundary(const sn_library_t* library, uint32_t cell)
{
    if (!sn_library_scalar_cell(library, cell))
        return false;
    const sn_lib_t* model = library->cells[cell].model;
    const sn_lib_cell_t* info = &model->cells[library->cells[cell].local_id];
    if (info->invalid || info->statetable_count)
        return false;
    for (uint32_t i = 0; i < library->cells[cell].output_count; i++)
        if (model->pins[sn_library_pin(library, cell, SN_LIB_OUTPUT, i)].three_state != SN_LIB_NONE)
            return false;
    bool found = false;
    for (uint32_t i = info->state_first; i < info->state_first + info->state_count; i++)
    {
        const sn_lib_state_t* state = &model->states[i];
        if (state->in_test_cell)
            continue;
        if (state->invalid || !state->is_latch || state->bits != 1)
            return false;
        found = true;
    }
    return found;
}

static inline const sn_lib_state_t* sn_library_ff(const sn_library_t* library, uint32_t cell)
{
    const sn_lib_t* model = library->cells[cell].model;
    const sn_lib_cell_t* cell_info = &model->cells[library->cells[cell].local_id];
    const sn_lib_state_t* result = NULL;
    if (cell_info->statetable_count)
        return NULL;
    for (uint32_t state_index = cell_info->state_first;
         state_index < cell_info->state_first + cell_info->state_count; state_index++)
    {
        const sn_lib_state_t* state = &model->states[state_index];
        if (state->in_test_cell)
            continue;
        // Power-off state corruption is outside the nominal powered model, just
        // like output-pin power_down_function. Keep the annotation in the model.
        if (result || state->invalid || state->is_latch || state->bits != 1 ||
            state->clocked_on_also != SN_LIB_NONE)
            return NULL;
        result = state;
    }
    return result;
}
// Scalar edge-triggered cells that can stand as opaque black-box boundaries, the way latches always do, when a
// caller wants to keep flip-flop cells intact around a transformed combinational cloud (@blast -f; @put).
static inline bool sn_library_ff_boundary(const sn_library_t* library, uint32_t cell)
{
    if (!library || cell >= library->cell_count || !sn_library_scalar_cell(library, cell))
        return false;
    const sn_lib_t* model = library->cells[cell].model;
    const sn_lib_cell_t* info = &model->cells[library->cells[cell].local_id];
    if (info->invalid)
        return false;
    for (uint32_t i = 0; i < library->cells[cell].output_count; i++)
        if (model->pins[sn_library_pin(library, cell, SN_LIB_OUTPUT, i)].three_state != SN_LIB_NONE)
            return false;
    return sn_library_ff(library, cell) != NULL;
}

static inline sn_expr_lit_t sn_library_mux(sn_expr_t* expression, sn_expr_lit_t select, sn_expr_lit_t yes,
                                           sn_expr_lit_t no)
{
    sn_expr_lit_t a = sn_expr_and(expression, select, yes);
    sn_expr_lit_t b = sn_expr_and(expression, sn_expr_not(select), no);
    return sn_expr_or(expression, a, b);
}
// Preserve the two state variables independently: collision values need not be
// complements. X/unspecified and toggle collisions cannot be guessed in two-state AIGs.
static inline sn_expr_lit_t sn_library_async(sn_expr_t* expression, sn_expr_lit_t value, sn_expr_lit_t held,
                                             sn_expr_lit_t clear, sn_expr_lit_t preset, uint32_t collision,
                                             bool inverse, bool has_both)
{
    sn_expr_lit_t result = sn_library_mux(expression, preset, inverse ? 0 : 1, value);
    result = sn_library_mux(expression, clear, inverse ? 1 : 0, result);
    if (has_both)
    {
        sn_expr_lit_t both = sn_expr_and(expression, clear, preset);
        sn_expr_lit_t v = collision == SN_LIB_COLLISION_LOW    ? 0
                          : collision == SN_LIB_COLLISION_HIGH ? 1
                          : collision == SN_LIB_COLLISION_HOLD ? held
                                                               : SN_EXPR_INVALID;
        if (v == SN_EXPR_INVALID)
            return v;
        result = sn_library_mux(expression, both, v, result);
    }
    return result;
}
// Compile nominal powered, two-state behavior. Pin power_down_function and
// x_function describe corruption to X, which this model deliberately does not
// simulate. Keep those expressions in the parsed model, but do not lower them.
// A high-impedance output is a real connectivity condition and stays unsupported.
static inline bool sn_library_output_can_compile(const sn_lib_pin_t* pin)
{
    return pin->function != SN_LIB_NONE && pin->three_state == SN_LIB_NONE;
}

static inline bool sn_library_compile_ff(const sn_library_t* library, uint32_t cell,
                                         const sn_lib_state_t* state, sn_expr_t* expression, bool transition)
{
    const sn_lib_t* model = library->cells[cell].model;
    uint32_t pins = sn_library_port_count(library, cell, SN_LIB_INPUT);
    sn_expr_init(expression, pins + 3);
    sn_expr_lit_t raw[] = {sn_expr_input(expression, pins), sn_expr_input(expression, pins + 1)};
    sn_expr_lit_t clear = state->clear == SN_LIB_NONE
                              ? 0
                              : sn_library_lower(library, cell, sn_lib_expr(model, state->clear), expression);
    sn_expr_lit_t preset =
        state->preset == SN_LIB_NONE
            ? 0
            : sn_library_lower(library, cell, sn_lib_expr(model, state->preset), expression);
    if (clear == SN_EXPR_INVALID || preset == SN_EXPR_INVALID)
        return false;
    bool both = state->clear != SN_LIB_NONE && state->preset != SN_LIB_NONE;
    sn_expr_lit_t visible[2];
    visible[0] =
        sn_library_async(expression, raw[0], raw[0], clear, preset, state->collision_var1, false, both);
    visible[1] =
        sn_library_async(expression, raw[1], raw[1], clear, preset, state->collision_var2, true, both);
    if (visible[0] == SN_EXPR_INVALID || visible[1] == SN_EXPR_INVALID)
        return false;
    if (transition)
    {
        sn_expr_lit_t clock =
            sn_library_lower(library, cell, sn_lib_expr(model, state->clocked_on), expression);
        sn_expr_lit_t data = sn_library_lower_bound(library, cell, sn_lib_expr(model, state->next_state),
                                                    expression, state, visible);
        if (clock == SN_EXPR_INVALID || data == SN_EXPR_INVALID)
            return false;
        sn_expr_lit_t edge = sn_expr_and(expression, clock, sn_expr_not(sn_expr_input(expression, pins + 2)));
        sn_expr_lit_t roots[3];
        roots[0] = sn_library_mux(expression, edge, data, raw[0]);
        roots[1] = sn_library_mux(expression, edge, sn_expr_not(data), raw[1]);
        roots[0] =
            sn_library_async(expression, roots[0], raw[0], clear, preset, state->collision_var1, false, both);
        roots[1] =
            sn_library_async(expression, roots[1], raw[1], clear, preset, state->collision_var2, true, both);
        roots[2] = clock;
        return sn_expr_finish(expression, 3, roots);
    }
    uint32_t outputs = sn_library_port_count(library, cell, SN_LIB_OUTPUT);
    sn_expr_lit_t* roots = (sn_expr_lit_t*)malloc(outputs * sizeof(*roots));
    if (!roots)
    {
        expression->failed = true;
        return false;
    }
    bool ok = true;
    for (uint32_t output_index = 0; output_index < outputs && ok; output_index++)
    {
        const sn_lib_pin_t* pin = &model->pins[sn_library_pin(library, cell, SN_LIB_OUTPUT, output_index)];
        ok = sn_library_output_can_compile(pin);
        if (ok)
        {
            roots[output_index] = sn_library_lower_bound(library, cell, sn_lib_expr(model, pin->function),
                                                         expression, state, visible);
            ok = roots[output_index] != SN_EXPR_INVALID;
        }
    }
    if (ok)
        ok = sn_expr_finish(expression, outputs, roots);
    free(roots);
    return ok;
}
// Unsupported functions remain absent, never replaced with zero. Returns false
// only on allocation failure. Query sn_expr_check per cell before blasting.
static inline bool sn_library_compile(sn_library_t* library)
{
    if (!library)
        return false;
    if (library->compiled)
        return true;
    uint32_t count = library->cell_count;
    sn_expr_t* functions = count ? (sn_expr_t*)calloc(count, sizeof(*functions)) : NULL;
    sn_expr_t* transitions = count ? (sn_expr_t*)calloc(count, sizeof(*transitions)) : NULL;
    if (count && (!functions || !transitions))
    {
        free(functions);
        free(transitions);
        return false;
    }
    bool success = true;
    for (uint32_t cell_index = 0; cell_index < count && success; cell_index++)
    {
        const sn_lib_t* model = library->cells[cell_index].model;
        sn_expr_t* expression = &functions[cell_index];
        sn_expr_init(expression, sn_library_port_count(library, cell_index, SN_LIB_INPUT));
        if (!sn_library_scalar_cell(library, cell_index))
            continue;
        if (sn_lib_cell_is_sequential(model, library->cells[cell_index].local_id))
        {
            const sn_lib_state_t* state = sn_library_ff(library, cell_index);
            bool supported =
                state && sn_library_compile_ff(library, cell_index, state, expression, false) &&
                sn_library_compile_ff(library, cell_index, state, &transitions[cell_index], true);
            success = !expression->failed && !transitions[cell_index].failed;
            if (!supported)
            {
                sn_expr_destroy(expression);
                sn_expr_destroy(&transitions[cell_index]);
            }
            continue;
        }
        uint32_t outputs = sn_library_port_count(library, cell_index, SN_LIB_OUTPUT);
        sn_expr_lit_t* roots = (sn_expr_lit_t*)malloc((size_t)outputs * sizeof(*roots));
        if (!roots)
        {
            success = false;
            break;
        }
        bool supported = true;
        for (uint32_t output_index = 0; output_index < outputs && supported; output_index++)
        {
            const sn_lib_pin_t* pin =
                &model->pins[sn_library_pin(library, cell_index, SN_LIB_OUTPUT, output_index)];
            if (!sn_library_output_can_compile(pin))
                supported = false;
            else
            {
                roots[output_index] =
                    sn_library_lower(library, cell_index, sn_lib_expr(model, pin->function), expression);
                supported = roots[output_index] != SN_EXPR_INVALID;
            }
        }
        if (supported)
            supported = sn_expr_finish(expression, outputs, roots);
        success = !expression->failed;
        if (!supported)
            sn_expr_destroy(expression);
        free(roots);
    }
    if (!success)
    {
        for (uint32_t cell_index = 0; cell_index < count; cell_index++)
        {
            sn_expr_destroy(&functions[cell_index]);
            sn_expr_destroy(&transitions[cell_index]);
        }
        free(functions);
        free(transitions);
        return false;
    }
    library->unsupported_count = 0;
    library->blast_scratch_count = 0;
    for (uint32_t cell = 0; cell < count; cell++)
    {
        const char* reason = NULL;
        if (!sn_library_scalar_cell(library, cell))
            reason = "invalid or non-scalar interface";
        else if (!sn_expr_check(&functions[cell]))
            reason = sn_lib_cell_is_sequential(library->cells[cell].model, library->cells[cell].local_id)
                         ? "unsupported sequential state, control, collision, or output function"
                         : "missing or unsupported two-state output function";
        library->cells[cell].unsupported_reason = reason;
        library->unsupported_count += reason != NULL;
        const sn_expr_t* graphs[] = {&functions[cell], &transitions[cell]};
        for (uint32_t graph = 0; graph < 2; graph++)
            if (sn_expr_check(graphs[graph]))
            {
                size_t needed =
                    (size_t)graphs[graph]->inputs + graphs[graph]->count + 1 + graphs[graph]->outputs;
                if (needed > library->blast_scratch_count)
                    library->blast_scratch_count = needed;
            }
    }
    library->functions = functions;
    library->transitions = transitions;
    library->compiled = true;
    return true;
}
ABC_NAMESPACE_HEADER_END
#endif
