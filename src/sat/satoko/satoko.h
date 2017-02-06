//===--- satoko.h -----------------------------------------------------------===
//
//                     satoko: Satisfiability solver
//
// This file is distributed under the BSD 2-Clause License.
// See LICENSE for details.
//
//===------------------------------------------------------------------------===
#ifndef satoko__satoko_h
#define satoko__satoko_h

#include "misc/util/abc_global.h"
ABC_NAMESPACE_HEADER_START

/** Return valeus */
enum {
    SATOKO_ERR = 0,
    SATOKO_OK  = 1
};

enum {
    SATOKO_UNDEC = 0, /* Undecided */
    SATOKO_SAT   = 1,
    SATOKO_UNSAT = -1
};

struct solver_t_;
typedef struct solver_t_ satoko_t;

typedef struct satoko_opts satoko_opts_t;
struct satoko_opts {
    /* Limits */
    long long conf_limit;  /* Limit on the n.of conflicts */
    long long prop_limit;  /* Limit on the n.of implications */

    /* Constants used for restart heuristic */
    double f_rst;          /* Used to force a restart */
    double b_rst;          /* Used to block a restart */
    unsigned fst_block_rst;   /* Lower bound n.of conflicts for start blocking restarts */
    unsigned sz_lbd_bqueue;   /* Size of the moving avarege queue for LBD (force restart) */
    unsigned sz_trail_bqueue; /* Size of the moving avarege queue for Trail size (block restart) */

    /* Constants used for clause database reduction heuristic */
    unsigned n_conf_fst_reduce;  /* N.of conflicts before first reduction */
    unsigned inc_reduce;         /* Increment to reduce */
    unsigned inc_special_reduce; /* Special increment to reduce */
    unsigned lbd_freeze_clause;

    /* VSIDS heuristic */
    float clause_decay;
    double var_decay;

    /* Binary resolution */
    unsigned clause_max_sz_bin_resol;
    unsigned clause_min_lbd_bin_resol;
    float garbage_max_ratio;
    char verbose;
};

//===------------------------------------------------------------------------===
extern satoko_t *satoko_create(void);
extern void satoko_destroy(satoko_t *);
extern void satoko_default_opts(satoko_opts_t *);
extern void satoko_configure(satoko_t *, satoko_opts_t *);
extern int  satoko_parse_dimacs(char *, satoko_t **);
extern void satoko_add_variable(satoko_t *, char);
extern int  satoko_add_clause(satoko_t *, unsigned *, unsigned);
extern void satoko_assump_push(satoko_t *s, unsigned);
extern void satoko_assump_pop(satoko_t *s);
extern int  satoko_simplify(satoko_t *);
extern int  satoko_solve(satoko_t *);

/* If problem is unsatisfiable under assumptions, this function is used to
 * obtain the final conflict clause expressed in the assumptions.
 *
 *  - It receives as inputs the solver and a pointer to a array where clause
 * will be copied. The memory is allocated by the solver, but must be freed by
 * the caller.
 *  - The return value is either the size of the array or -1 in case the final
 * conflict cluase was not generated.
 */
extern int  satoko_final_conflict(satoko_t *, unsigned *);

ABC_NAMESPACE_HEADER_END
#endif /* satoko__satoko_h */
