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

#ifdef SATOKO_ACT_VAR_DBLE
/** Re-scale the activity value for all variables.
 */
static inline void var_act_rescale(solver_t *s)
{
    unsigned i;
    double *activity = vec_dble_data(s->activity);

    for (i = 0; i < vec_dble_size(s->activity); i++)
        activity[i] *= 1e-100;
    s->var_act_inc *= 1e-100;
}

/** Increment the activity value of one variable ('var')
 */
static inline void var_act_bump(solver_t *s, unsigned var)
{
    double *activity = vec_dble_data(s->activity);

    activity[var] += s->var_act_inc;
    if (activity[var] > 1e100)
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

#else /* SATOKO_ACT_VAR_DBLE */

static inline void var_act_rescale(solver_t *s)
{
    unsigned i;
    unsigned *activity = vec_uint_data(s->activity);

    for (i = 0; i < vec_uint_size(s->activity); i++)
        activity[i] >>= 19;
    s->var_act_inc >>= 19;
    s->var_act_inc = mkt_uint_max(s->var_act_inc, (1 << 5));
}

static inline void var_act_bump(solver_t *s, unsigned var)
{
    unsigned *activity = vec_uint_data(s->activity);

    activity[var] += s->var_act_inc;
    if (activity[var] & 0x80000000)
        var_act_rescale(s);
    if (heap_in_heap(s->var_order, var))
        heap_decrease(s->var_order, var);
}

static inline void var_act_decay(solver_t *s)
{
    s->var_act_inc += (s->var_act_inc >> 4);
}

#endif /* SATOKO_ACT_VAR_DBLE */

ABC_NAMESPACE_HEADER_END
#endif /* satoko__act_var_h */
