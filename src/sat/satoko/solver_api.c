//===--- solver_api.h -------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <math.h>

#include "act_var.h"
#include "solver.h"
#include "utils/misc.h"

#include "misc/util/abc_global.h"
ABC_NAMESPACE_IMPL_START

//===------------------------------------------------------------------------===
// Satoko internal functions
//===------------------------------------------------------------------------===
static inline void solver_rebuild_order(solver_t *s)
{
    unsigned var;
    vec_uint_t *vars = vec_uint_alloc(vec_char_size(s->assigns));

    for (var = 0; var < vec_char_size(s->assigns); var++)
        if (var_value(s, var) == VAR_UNASSING)
            vec_uint_push_back(vars, var);
    heap_build(s->var_order, vars);
    vec_uint_free(vars);
}

static inline int clause_is_satisfied(solver_t *s, struct clause *clause)
{
    unsigned i;
    unsigned *lits = &(clause->data[0].lit);
    for (i = 0; i < clause->size; i++)
        if (lit_value(s, lits[i]) == LIT_TRUE)
            return SATOKO_OK;
    return SATOKO_ERR;
}

static inline void print_opts(solver_t *s)
{
    printf( "+-[ BLACK MAGIC - PARAMETERS ]-+\n");
    printf( "|                              |\n");
    printf( "|--> Restarts heuristic        |\n");
    printf( "|    * LBD Queue   = %6d    |\n", s->opts.sz_lbd_bqueue);
    printf( "|    * Trail Queue = %6d    |\n", s->opts.sz_trail_bqueue);
    printf( "|    * f_rst       = %6.2f    |\n", s->opts.f_rst);
    printf( "|    * b_rst       = %6.2f    |\n", s->opts.b_rst);
    printf( "|                              |\n");
    printf( "|--> Clause DB reduction:      |\n");
    printf( "|    * First       = %6d    |\n", s->opts.n_conf_fst_reduce);
    printf( "|    * Inc         = %6d    |\n", s->opts.inc_reduce);
    printf( "|    * Special Inc = %6d    |\n", s->opts.inc_special_reduce);
    printf( "|    * Protected (LBD) < %2d    |\n", s->opts.lbd_freeze_clause);
    printf( "|                              |\n");
    printf( "|--> Binary resolution:        |\n");
    printf( "|    * Clause size < %3d       |\n", s->opts.clause_max_sz_bin_resol);
    printf( "|    * Clause lbd  < %3d       |\n", s->opts.clause_min_lbd_bin_resol);
    printf( "+------------------------------+\n\n");
}

static inline void print_stats(solver_t *s)
{
    printf("starts        : %10d\n", s->stats.n_starts);
    printf("conflicts     : %10ld\n", s->stats.n_conflicts);
    printf("decisions     : %10ld\n", s->stats.n_decisions);
    printf("propagations  : %10ld\n", s->stats.n_propagations);
}

//===------------------------------------------------------------------------===
// Satoko external functions
//===------------------------------------------------------------------------===
solver_t * satoko_create()
{
    solver_t *s = satoko_calloc(solver_t, 1);

    satoko_default_opts(&s->opts);
    /* User data */
    s->assumptions = vec_uint_alloc(0);
    s->final_conflict = vec_uint_alloc(0);
    /* Clauses Database */
    s->all_clauses = cdb_alloc(0);
    s->originals = vec_uint_alloc(0);
    s->learnts = vec_uint_alloc(0);
    s->watches = vec_wl_alloc(0);
    /* Activity heuristic */
    s->var_act_inc = VAR_ACT_INIT_INC;
    s->clause_act_inc = CLAUSE_ACT_INIT_INC;
    /* Variable Information */
    s->activity = vec_act_alloc(0);
    s->var_order = heap_alloc(s->activity);
    s->levels = vec_uint_alloc(0);
    s->reasons = vec_uint_alloc(0);
    s->assigns = vec_char_alloc(0);
    s->polarity = vec_char_alloc(0);
    /* Assignments */
    s->trail = vec_uint_alloc(0);
    s->trail_lim = vec_uint_alloc(0);
    /* Temporary data used by Search method */
    s->bq_trail = b_queue_alloc(s->opts.sz_trail_bqueue);
    s->bq_lbd = b_queue_alloc(s->opts.sz_lbd_bqueue);
    s->n_confl_bfr_reduce = s->opts.n_conf_fst_reduce;
    s->RC1 = 1;
    s->RC2 = s->opts.n_conf_fst_reduce;
    /* Temporary data used by Analyze */
    s->temp_lits = vec_uint_alloc(0);
    s->seen = vec_char_alloc(0);
    s->tagged = vec_uint_alloc(0);
    s->stack = vec_uint_alloc(0);
    s->last_dlevel = vec_uint_alloc(0);
    /* Misc temporary */
    s->stamps = vec_uint_alloc(0);
    return s;
}

void satoko_destroy(solver_t *s)
{
    vec_uint_free(s->assumptions);
    vec_uint_free(s->final_conflict);
    cdb_free(s->all_clauses);
    vec_uint_free(s->originals);
    vec_uint_free(s->learnts);
    vec_wl_free(s->watches);
    vec_act_free(s->activity);
    heap_free(s->var_order);
    vec_uint_free(s->levels);
    vec_uint_free(s->reasons);
    vec_char_free(s->assigns);
    vec_char_free(s->polarity);
    vec_uint_free(s->trail);
    vec_uint_free(s->trail_lim);
    b_queue_free(s->bq_lbd);
    b_queue_free(s->bq_trail);
    vec_uint_free(s->temp_lits);
    vec_char_free(s->seen);
    vec_uint_free(s->tagged);
    vec_uint_free(s->stack);
    vec_uint_free(s->last_dlevel);
    vec_uint_free(s->stamps);
    if (s->marks)
        vec_char_free(s->marks);
    satoko_free(s);
}

void satoko_default_opts(satoko_opts_t *opts)
{
    memset(opts, 0, sizeof(satoko_opts_t));
    opts->verbose = 0;
    /* Limits */
    opts->conf_limit = 0;
    opts->prop_limit  = 0;
    /* Constants used for restart heuristic */
    opts->f_rst = 0.8;
    opts->b_rst = 1.4;
    opts->fst_block_rst   = 10000;
    opts->sz_lbd_bqueue   = 50;
    opts->sz_trail_bqueue = 5000;
    /* Constants used for clause database reduction heuristic */
    opts->n_conf_fst_reduce = 2000;
    opts->inc_reduce = 300;
    opts->inc_special_reduce = 1000;
    opts->lbd_freeze_clause = 30;
    opts->learnt_ratio = 0.5;
    /* VSIDS heuristic */
    opts->var_act_limit = VAR_ACT_LIMIT;
    opts->var_act_rescale = VAR_ACT_RESCALE;
    opts->var_decay = 0.95;
    opts->clause_decay = (clause_act_t) 0.995;
    /* Binary resolution */
    opts->clause_max_sz_bin_resol = 30;
    opts->clause_min_lbd_bin_resol = 6;

    opts->garbage_max_ratio = (float) 0.3;
}

/**
 * TODO: sanity check on configuration options
 */
void satoko_configure(satoko_t *s, satoko_opts_t *user_opts)
{
    assert(user_opts);
    memcpy(&s->opts, user_opts, sizeof(satoko_opts_t));
}

int satoko_simplify(solver_t * s)
{
    unsigned i, j = 0;
    unsigned cref;

    assert(solver_dlevel(s) == 0);
    if (solver_propagate(s) != UNDEF)
        return SATOKO_ERR;
    if (s->n_assigns_simplify == vec_uint_size(s->trail) || s->n_props_simplify > 0)
        return SATOKO_OK;

    vec_uint_foreach(s->originals, cref, i) {
        struct clause *clause = clause_read(s, cref);

    if (clause_is_satisfied(s, clause)) {
            clause->f_mark = 1;
            s->stats.n_original_lits -= clause->size;
            clause_unwatch(s, cref);
        } else
            vec_uint_assign(s->originals, j++, cref);
    }
    vec_uint_shrink(s->originals, j);
    solver_rebuild_order(s);
    s->n_assigns_simplify = vec_uint_size(s->trail);
    s->n_props_simplify = s->stats.n_original_lits + s->stats.n_learnt_lits;
    return SATOKO_OK;
}

void satoko_add_variable(solver_t *s, char sign)
{
    unsigned var = vec_act_size(s->activity);
    vec_wl_push(s->watches);
    vec_wl_push(s->watches);
    vec_act_push_back(s->activity, 0);
    vec_uint_push_back(s->levels, 0);
    vec_char_push_back(s->assigns, VAR_UNASSING);
    vec_char_push_back(s->polarity, sign);
    vec_uint_push_back(s->reasons, UNDEF);
    vec_uint_push_back(s->stamps, 0);
    vec_char_push_back(s->seen, 0);
    heap_insert(s->var_order, var);
    if (s->marks)
        vec_char_push_back(s->marks, 0);
}

int satoko_add_clause(solver_t *s, unsigned *lits, unsigned size)
{
    unsigned i, j;
    unsigned prev_lit;
    unsigned max_var;
    unsigned cref;

    qsort((void *) lits, size, sizeof(unsigned), stk_uint_compare);
    max_var = lit2var(lits[size - 1]);
    while (max_var >= vec_act_size(s->activity))
        satoko_add_variable(s, LIT_FALSE);

    vec_uint_clear(s->temp_lits);
    j = 0;
    prev_lit = UNDEF;
    for (i = 0; i < size; i++) {
        if (lits[i] == lit_neg(prev_lit) || lit_value(s, lits[i]) == LIT_TRUE)
            return SATOKO_OK;
        else if (lits[i] != prev_lit && var_value(s, lit2var(lits[i])) == VAR_UNASSING) {
            prev_lit = lits[i];
            vec_uint_push_back(s->temp_lits, lits[i]);
        }
    }

    if (vec_uint_size(s->temp_lits) == 0)
        return SATOKO_ERR;
    if (vec_uint_size(s->temp_lits) == 1) {
        solver_enqueue(s, vec_uint_at(s->temp_lits, 0), UNDEF);
        return (solver_propagate(s) == UNDEF);
    }

    cref = solver_clause_create(s, s->temp_lits, 0);
    clause_watch(s, cref);
    return SATOKO_OK;
}

void satoko_assump_push(solver_t *s, unsigned lit)
{
    vec_uint_push_back(s->assumptions, lit);
}

void satoko_assump_pop(solver_t *s)
{
    assert(vec_uint_size(s->assumptions) > 0);
    vec_uint_pop_back(s->assumptions);
    solver_cancel_until(s, vec_uint_size(s->assumptions));
}

int satoko_solve(solver_t *s)
{
    char status = SATOKO_UNDEC;

    assert(s);
    //if (s->opts.verbose)
    //    print_opts(s);

    while (status == SATOKO_UNDEC) {
        status = solver_search(s);
        if (solver_check_limits(s) == 0)
            break;
    }
    if (s->opts.verbose)
        print_stats(s);
    solver_cancel_until(s, vec_uint_size(s->assumptions));
    return status;
}

int satoko_final_conflict(solver_t *s, unsigned *out)
{
    if (vec_uint_size(s->final_conflict) == 0)
        return -1;
    out = satoko_alloc(unsigned, vec_uint_size(s->final_conflict));
    memcpy(out, vec_uint_data(s->final_conflict),
           sizeof(unsigned) * vec_uint_size(s->final_conflict));
    return vec_uint_size(s->final_conflict);

}

satoko_stats_t satoko_stats(satoko_t *s)
{
    return s->stats;
}

void satoko_bookmark(satoko_t *s)
{
    assert(solver_dlevel(s) == 0);
    s->book_cl_orig = vec_uint_size(s->originals);
    s->book_cl_lrnt = vec_uint_size(s->learnts);
    s->book_vars = vec_char_size(s->assigns);
    s->book_trail = vec_uint_size(s->trail);
}

void satoko_unbookmark(satoko_t *s)
{
    s->book_cl_orig = 0;
    s->book_cl_lrnt = 0;
    s->book_vars = 0;
    s->book_trail = 0;
}

void satoko_rollback(satoko_t *s)
{
    unsigned i, cref;
    unsigned n_originals = vec_uint_size(s->originals) - s->book_cl_orig;
    unsigned n_learnts = vec_uint_size(s->learnts) - s->book_cl_lrnt;
    struct clause **cl_to_remove;

    assert(solver_dlevel(s) == 0);
    cl_to_remove = satoko_alloc(struct clause *, n_originals + n_learnts);
    /* Mark clauses */
    vec_uint_foreach_start(s->originals, cref, i, s->book_cl_orig)
        cl_to_remove[i] = clause_read(s, cref);
    vec_uint_foreach_start(s->learnts, cref, i, s->book_cl_lrnt)
        cl_to_remove[n_originals + i] = clause_read(s, cref);
    for (i = 0; i < n_originals + n_learnts; i++) {
        clause_unwatch(s, cdb_cref(s->all_clauses, (unsigned *)cl_to_remove[i]));
        cl_to_remove[i]->f_mark = 1;
    }
    vec_uint_shrink(s->originals, s->book_cl_orig);
    vec_uint_shrink(s->learnts, s->book_cl_lrnt);
    /* Shrink variable related vectors */
    vec_act_shrink(s->activity, s->book_vars);
    vec_uint_shrink(s->levels, s->book_vars);
    vec_uint_shrink(s->reasons, s->book_vars);
    vec_char_shrink(s->assigns, s->book_vars);
    vec_char_shrink(s->polarity, s->book_vars);
    solver_rebuild_order(s);
    /* Rewind solver and cancel level 0 assignments to the trail */
    solver_cancel_until(s, 0);
    vec_uint_shrink(s->trail, s->book_trail);
    s->book_cl_orig = 0;
    s->book_cl_lrnt = 0;
    s->book_vars = 0;
    s->book_trail = 0;
}

void satoko_mark_cone(satoko_t *s, int * pvars, int n_vars)
{
    int i;
    if (!solver_has_marks(s))
        s->marks = vec_char_init(solver_varnum(s), 0);
    for (i = 0; i < n_vars; i++) {
        var_set_mark(s, pvars[i]);
        if (!heap_in_heap(s->var_order, pvars[i]))
            heap_insert(s->var_order, pvars[i]);
    }
}

void satoko_unmark_cone(satoko_t *s, int *pvars, int n_vars)
{
    int i;
    assert(solver_has_marks(s));
    for (i = 0; i < n_vars; i++)
        var_clean_mark(s, pvars[i]);
}

ABC_NAMESPACE_IMPL_END
