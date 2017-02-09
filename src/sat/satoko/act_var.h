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

#if defined SATOKO_ACT_VAR_DBLE || defined SATOKO_ACT_VAR_FLOAT
/** Re-scale the activity value for all variables.
 */
static inline void var_act_rescale(solver_t *s)
{
    unsigned i;
    act_t *activity = vec_act_data(s->activity);

    for (i = 0; i < vec_act_size(s->activity); i++)
        activity[i] *= VAR_ACT_RESCALE;
    s->var_act_inc *= VAR_ACT_RESCALE;
}

/** Increment the activity value of one variable ('var')
 */
static inline void var_act_bump(solver_t *s, unsigned var)
{
    act_t *activity = vec_act_data(s->activity);

    activity[var] += s->var_act_inc;
    if (activity[var] > VAR_ACT_LIMIT)
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

#endif /* SATOKO_ACT_VAR_DBLE || SATOKO_ACT_VAR_FLOAT */

ABC_NAMESPACE_HEADER_END
#endif /* satoko__act_var_h */
