//===--- act_var.h ----------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#ifndef satoko__act_clause_h
#define satoko__act_clause_h

#include "solver.h"
#include "types.h"

#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

#ifdef SATOKO_ACT_CLAUSE_FLOAT

/** Re-scale the activity value for all clauses.
 */
static inline void clause_act_rescale(solver_t *s)
{
    unsigned i, cref;
    struct clause *clause;

    vec_uint_foreach(s->learnts, cref, i) {
        clause = clause_read(s, cref);
        clause->data[clause->size].act *= (float)1e-20;
    }
    s->clause_act_inc  *= (float)1e-20;
}

/** Increment the activity value of one clause ('clause')
 */
static inline void clause_act_bump(solver_t *s, struct clause *clause)
{
    clause->data[clause->size].act += s->clause_act_inc;
    if (clause->data[clause->size].act > 1e20)
        clause_act_rescale(s);
}

/** Increment the value by which clauses activity values are incremented
 */
static inline void clause_act_decay(solver_t *s)
{
    s->clause_act_inc *= (1 / s->opts.clause_decay);
}

#else /* SATOKO_ACT_CLAUSE_FLOAT */

static inline void clause_act_rescale(solver_t *s)
{
    unsigned i, cref;
    struct clause *clause;

    vec_uint_foreach(s->learnts, cref, i) {
        clause = clause_read(s, cref);
        clause->data[clause->size].act >>= 10;
    }
    s->clause_act_inc = stk_uint_max((s->clause_act_inc >> 10), (1 << 11));
}

static inline void clause_act_bump(solver_t *s, struct clause *clause)
{
    clause->data[clause->size].act += s->clause_act_inc;
    if (clause->data[clause->size].act & 0x80000000)
        clause_act_rescale(s);
}

static inline void clause_act_decay(solver_t *s)
{
    s->clause_act_inc += (s->clause_act_inc >> 10);
}

#endif /* SATOKO_ACT_CLAUSE_FLOAT */

ABC_NAMESPACE_HEADER_END
#endif /* satoko__act_clause_h */
