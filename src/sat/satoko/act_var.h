//===--- act_var.h ----------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#ifndef satoko__act_var_h
#define satoko__act_var_h

#include "solver.h"
#include "types.h"
#include "utils/heap.h"

#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

#if defined SATOKO_ACT_VAR_DBLE
/** Re-scale the activity value for all variables.
 */
static inline void var_act_rescale(solver_t *s)
{
    unsigned i;
    act_t *activity = vec_act_data(s->activity);

    for (i = 0; i < vec_act_size(s->activity); i++)
        activity[i] *= s->opts.var_act_rescale;
    s->var_act_inc *= s->opts.var_act_rescale;
}

/** Increment the activity value of one variable ('var')
 */
static inline void var_act_bump(solver_t *s, unsigned var)
{
    act_t *activity = vec_act_data(s->activity);

    activity[var] += s->var_act_inc;
    if (activity[var] > s->opts.var_act_limit)
        var_act_rescale(s);
    if (heap_in_heap(s->var_order, var))
        heap_decrease(s->var_order, var);
}

/** Increment the value by which variables activity values are incremented
 */
static inline void var_act_decay(solver_t *s)
{
    s->var_act_inc *= (1 / s->opts.var_decay);
}

#elif defined(SATOKO_ACT_VAR_FIXED)

static inline void var_act_rescale(solver_t *s)
{
    unsigned i;
    act_t *activity = (act_t *)vec_act_data(s->activity);

    for (i = 0; i < vec_act_size(s->activity); i++)
        activity[i] = fixed_mult(activity[i], VAR_ACT_RESCALE);
    s->var_act_inc = fixed_mult(s->var_act_inc, VAR_ACT_RESCALE);
}

static inline void var_act_bump(solver_t *s, unsigned var)
{
    act_t *activity = (act_t *)vec_act_data(s->activity);

    activity[var] = fixed_add(activity[var], s->var_act_inc);
    if (activity[var] > VAR_ACT_LIMIT)
        var_act_rescale(s);
    if (heap_in_heap(s->var_order, var))
        heap_decrease(s->var_order, var);
}

static inline void var_act_decay(solver_t *s)
{
    s->var_act_inc = fixed_mult(s->var_act_inc, dble2fixed(1 / s->opts.var_decay));
}

#else

static inline void var_act_rescale(solver_t *s)
{
    unsigned i;
    act_t *activity = vec_act_data(s->activity);

    for (i = 0; i < vec_act_size(s->activity); i++)
        activity[i] >>= 19;
    s->var_act_inc = stk_uint_max((s->var_act_inc >> 19), (1 << 5));
}

static inline void var_act_bump(solver_t *s, unsigned var)
{
    act_t *activity = vec_act_data(s->activity);

    activity[var] += s->var_act_inc;
    if (activity[var] & 0xF0000000)
        var_act_rescale(s);
    if (heap_in_heap(s->var_order, var))
        heap_decrease(s->var_order, var);
}

static inline void var_act_decay(solver_t *s)
{
    s->var_act_inc += (s->var_act_inc >> 4);
}

#endif /* SATOKO_ACT_VAR_DBLE || SATOKO_ACT_VAR_FIXED */

ABC_NAMESPACE_HEADER_END
#endif /* satoko__act_var_h */
