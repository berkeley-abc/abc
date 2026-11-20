/*
 * Revision Control Information
 *
 * $Source$
 * $Author$
 * $Revision$
 * $Date$
 *
 */
#ifndef ABC__misc__espresso__mincov_int_h
#define ABC__misc__espresso__mincov_int_h

//#include "port.h"
//#include "utility.h"
#include "sparse.h"
#include "mincov.h"

ABC_NAMESPACE_HEADER_START


typedef struct stats_struct stats_t;
struct stats_struct {
    int debug;            /* 1 if debugging is enabled */
    int max_print_depth;    /* dump stats for levels up to this level */
    int max_depth;        /* deepest the recursion has gone */
    int nodes;            /* total nodes visited */
    int component;        /* currently solving a component */
    int comp_count;        /* number of components detected */
    int gimpel_count;        /* number of times Gimpel reduction applied */
    int gimpel;            /* currently inside Gimpel reduction */
    long start_time;        /* cpu time when the covering started */
    int no_branching;
    int lower_bound;
};



typedef struct solution_struct solution_t;
struct solution_struct {
    sm_row *row;
    int cost;
};


extern solution_t *solution_alloc(void);
extern void solution_free(solution_t *sol);
extern solution_t *solution_dup(solution_t *sol);
extern void solution_accept(solution_t *sol, sm_matrix *A, int *weight, int col);
extern void solution_reject(solution_t *sol, sm_matrix *A, int *weight, int col);
extern void solution_add(solution_t *sol, int *weight, int col);
extern solution_t *solution_choose_best(solution_t *best1, solution_t *best2);

extern solution_t *sm_maximal_independent_set(sm_matrix *A, int *weight);
extern solution_t *sm_mincov(sm_matrix *A, solution_t *select, int *weight, int lb, int bound, int depth, stats_t *stats);
extern int gimpel_reduce(sm_matrix *A, solution_t *select, int *weight, int lb, int bound, int depth, stats_t *stats, solution_t **best);


#define WEIGHT(weight, col) ((weight) == NIL(int) ? 1 : (weight)[col])

ABC_NAMESPACE_HEADER_END

#endif
