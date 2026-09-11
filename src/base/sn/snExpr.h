/**CFile****************************************************************

  FileName    [snExpr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Shared multi-root expression graphs, simulation, and AIG replay.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snExpr.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_EXPR_H
#define SN_EXPR_H

// Immutable-after-build, multi-root local AIG. Variable 0 is constant false;
// variables 1..inputs are inputs; subsequent variables are appended ANDs.
// Literal = 2*variable + inversion. No SN or ABC runtime dependencies.
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "misc/util/abc_namespaces.h"
ABC_NAMESPACE_HEADER_START

#define SN_EXPR_INVALID UINT32_MAX
typedef uint32_t sn_expr_lit_t;
typedef struct sn_expr_node_t
{
    sn_expr_lit_t left, right;
} sn_expr_node_t;
typedef struct sn_expr_t
{
    uint32_t inputs, count, capacity, outputs;
    sn_expr_node_t* nodes;
    sn_expr_lit_t* roots;
    bool failed;
} sn_expr_t;

static inline void sn_expr_init(sn_expr_t* expression, uint32_t inputs)
{
    memset(expression, 0, sizeof(*expression));
    expression->inputs = inputs;
    expression->failed = inputs >= UINT32_MAX / 2;
}
static inline void sn_expr_destroy(sn_expr_t* expression)
{
    free(expression->nodes);
    free(expression->roots);
    sn_expr_init(expression, 0);
}
static inline bool sn_expr_lit_valid(const sn_expr_t* expression, sn_expr_lit_t lit)
{
    return lit != SN_EXPR_INVALID && (uint64_t)(lit >> 1) <= (uint64_t)expression->inputs + expression->count;
}
static inline sn_expr_lit_t sn_expr_input(const sn_expr_t* expression, uint32_t index)
{
    return index < expression->inputs ? 2 * (index + 1) : SN_EXPR_INVALID;
}
static inline sn_expr_lit_t sn_expr_not(sn_expr_lit_t lit)
{
    return lit == SN_EXPR_INVALID ? lit : lit ^ 1;
}
static inline sn_expr_lit_t sn_expr_and(sn_expr_t* expression, sn_expr_lit_t a, sn_expr_lit_t b)
{
    if (expression->failed || expression->roots || !sn_expr_lit_valid(expression, a) ||
        !sn_expr_lit_valid(expression, b))
    {
        expression->failed = true;
        return SN_EXPR_INVALID;
    }
    if (!a || !b || a == (b ^ 1))
        return 0;
    if (a == 1 || a == b)
        return b;
    if (b == 1)
        return a;
    if ((uint64_t)expression->inputs + expression->count + 1 >= UINT32_MAX / 2)
    {
        expression->failed = true;
        return SN_EXPR_INVALID;
    }
    if (expression->count == expression->capacity)
    {
        uint32_t new_capacity = expression->capacity ? expression->capacity * 2 : 16;
        if (new_capacity < expression->capacity ||
            (uint64_t)new_capacity * sizeof(*expression->nodes) > SIZE_MAX)
        {
            expression->failed = true;
            return SN_EXPR_INVALID;
        }
        void* allocation = realloc(expression->nodes, (size_t)new_capacity * sizeof(*expression->nodes));
        if (!allocation)
        {
            expression->failed = true;
            return SN_EXPR_INVALID;
        }
        expression->nodes = (sn_expr_node_t*)allocation;
        expression->capacity = new_capacity;
    }
    expression->nodes[expression->count].left = a < b ? a : b;
    expression->nodes[expression->count].right = a < b ? b : a;
    return 2 * (expression->inputs + ++expression->count);
}
static inline sn_expr_lit_t sn_expr_or(sn_expr_t* expression, sn_expr_lit_t a, sn_expr_lit_t b)
{
    return sn_expr_not(sn_expr_and(expression, sn_expr_not(a), sn_expr_not(b)));
}
static inline sn_expr_lit_t sn_expr_xor(sn_expr_t* expression, sn_expr_lit_t a, sn_expr_lit_t b)
{
    sn_expr_lit_t left_value = sn_expr_and(expression, a, sn_expr_not(b));
    sn_expr_lit_t right_value = sn_expr_and(expression, sn_expr_not(a), b);
    return sn_expr_or(expression, left_value, right_value);
}
// Finalize once. Root storage is copied, so caller storage may be transient.
static inline bool sn_expr_finish(sn_expr_t* expression, uint32_t count, const sn_expr_lit_t* roots)
{
    if (expression->failed || expression->roots || !count || !roots ||
        (uint64_t)count * sizeof(*roots) > SIZE_MAX)
        return false;
    for (uint32_t i = 0; i < count; i++)
        if (!sn_expr_lit_valid(expression, roots[i]))
        {
            expression->failed = true;
            return false;
        }
    expression->roots = (sn_expr_lit_t*)malloc((size_t)count * sizeof(*roots));
    if (!expression->roots)
    {
        expression->failed = true;
        return false;
    }
    memcpy(expression->roots, roots, (size_t)count * sizeof(*roots));
    expression->outputs = count;
    return true;
}
static inline bool sn_expr_check(const sn_expr_t* expression)
{
    if (!expression || expression->failed || !expression->outputs || !expression->roots ||
        expression->count > expression->capacity || (expression->count && !expression->nodes) ||
        (uint64_t)expression->inputs + expression->count >= UINT32_MAX / 2)
        return false;
    for (uint32_t i = 0; i < expression->count; i++)
        if ((uint64_t)(expression->nodes[i].left >> 1) >= (uint64_t)expression->inputs + i + 1 ||
            (uint64_t)(expression->nodes[i].right >> 1) >= (uint64_t)expression->inputs + i + 1)
            return false;
    for (uint32_t i = 0; i < expression->outputs; i++)
        if (!sn_expr_lit_valid(expression, expression->roots[i]))
            return false;
    return true;
}
// Destination literals use the same inversion bit and 0/1 constants (MiniAIG/GIA).
// The callback can hash ANDs. INVALID signals destination failure. Replay scratch
// is caller-owned and can be reused for many gate occurrences; roots never mutate.
typedef sn_expr_lit_t (*sn_expr_and_fn)(void*, sn_expr_lit_t, sn_expr_lit_t);
static inline bool sn_expr_blast(const sn_expr_t* expression, const sn_expr_lit_t* inputs,
                                 sn_expr_and_fn and_fn, void* context, sn_expr_lit_t* scratch,
                                 size_t scratch_count, sn_expr_lit_t* outputs)
{
    if (!sn_expr_check(expression) || !and_fn || !scratch || !outputs || (expression->inputs && !inputs) ||
        scratch_count < (uint64_t)expression->inputs + expression->count + 1)
        return false;
    scratch[0] = 0;
    for (uint32_t i = 0; i < expression->inputs; i++)
    {
        if (inputs[i] == SN_EXPR_INVALID)
            return false;
        scratch[i + 1] = inputs[i];
    }
    for (uint32_t i = 0; i < expression->count; i++)
    {
        sn_expr_lit_t a = expression->nodes[i].left, b = expression->nodes[i].right;
        sn_expr_lit_t literal = and_fn(context, scratch[a >> 1] ^ (a & 1), scratch[b >> 1] ^ (b & 1));
        if (literal == SN_EXPR_INVALID)
            return false;
        scratch[expression->inputs + i + 1] = literal;
    }
    for (uint32_t i = 0; i < expression->outputs; i++)
        outputs[i] = scratch[expression->roots[i] >> 1] ^ (expression->roots[i] & 1);
    return true;
}
static inline bool sn_expr_simulate(const sn_expr_t* expression, const uint64_t* inputs, uint64_t* scratch,
                                    size_t scratch_count, uint64_t* outputs)
{
    if (!sn_expr_check(expression) || !scratch || !outputs || (expression->inputs && !inputs) ||
        scratch_count < (uint64_t)expression->inputs + expression->count + 1)
        return false;
    scratch[0] = 0;
    for (uint32_t i = 0; i < expression->inputs; i++)
        scratch[i + 1] = inputs[i];
    for (uint32_t i = 0; i < expression->count; i++)
    {
        sn_expr_lit_t a = expression->nodes[i].left, b = expression->nodes[i].right;
        uint64_t left_value = scratch[a >> 1], right_value = scratch[b >> 1];
        scratch[expression->inputs + i + 1] =
            (a & 1 ? ~left_value : left_value) & (b & 1 ? ~right_value : right_value);
    }
    for (uint32_t i = 0; i < expression->outputs; i++)
    {
        sn_expr_lit_t literal = expression->roots[i];
        outputs[i] = literal & 1 ? ~scratch[literal >> 1] : scratch[literal >> 1];
    }
    return true;
}
ABC_NAMESPACE_HEADER_END
#endif
