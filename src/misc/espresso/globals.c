/*
 * Revision Control Information
 *
 * $Source$
 * $Author$
 * $Revision$
 * $Date$
 *
 */
#include "espresso.h"

ABC_NAMESPACE_IMPL_START


/*
 *    Global Variable Declarations
 */

ABC_THREAD_LOCAL unsigned int debug;              /* debug parameter */
ABC_THREAD_LOCAL espresso_bool verbose_debug;              /* -v:  whether to print a lot */
ABC_THREAD_LOCAL const char *total_name[TIME_COUNT];    /* basic function names */
ABC_THREAD_LOCAL long total_time[TIME_COUNT];     /* time spent in basic fcts */
ABC_THREAD_LOCAL int total_calls[TIME_COUNT];     /* # calls to each fct */

ABC_THREAD_LOCAL espresso_bool echo_comments;         /* turned off by -eat option */
ABC_THREAD_LOCAL espresso_bool echo_unknown_commands;     /* always true ?? */
ABC_THREAD_LOCAL espresso_bool force_irredundant;          /* -nirr command line option */
ABC_THREAD_LOCAL espresso_bool skip_make_sparse;
ABC_THREAD_LOCAL espresso_bool kiss;                       /* -kiss command line option */
ABC_THREAD_LOCAL espresso_bool pos;                        /* -pos command line option */
ABC_THREAD_LOCAL espresso_bool print_solution;             /* -x command line option */
ABC_THREAD_LOCAL espresso_bool recompute_onset;            /* -onset command line option */
ABC_THREAD_LOCAL espresso_bool remove_essential;           /* -ness command line option */
ABC_THREAD_LOCAL espresso_bool single_expand;              /* -fast command line option */
ABC_THREAD_LOCAL espresso_bool summary;                    /* -s command line option */
ABC_THREAD_LOCAL espresso_bool trace;                      /* -t command line option */
ABC_THREAD_LOCAL espresso_bool unwrap_onset;               /* -nunwrap command line option */
ABC_THREAD_LOCAL espresso_bool use_random_order;         /* -random command line option */
ABC_THREAD_LOCAL espresso_bool use_super_gasp;         /* -strong command line option */
ABC_THREAD_LOCAL char *filename;             /* filename PLA was read from */

const struct pla_types_struct pla_types[] = {
    {"-f", F_type},
    {"-r", R_type},
    {"-d", D_type},
    {"-fd", FD_type},
    {"-fr", FR_type},
    {"-dr", DR_type},
    {"-fdr", FDR_type},
    {"-fc", F_type | CONSTRAINTS_type},
    {"-rc", R_type | CONSTRAINTS_type},
    {"-dc", D_type | CONSTRAINTS_type},
    {"-fdc", FD_type | CONSTRAINTS_type},
    {"-frc", FR_type | CONSTRAINTS_type},
    {"-drc", DR_type | CONSTRAINTS_type},
    {"-fdrc", FDR_type | CONSTRAINTS_type},
    {"-pleasure", PLEASURE_type},
    {"-eqn", EQNTOTT_type},
    {"-eqntott", EQNTOTT_type},
    {"-kiss", KISS_type},
    {"-cons", CONSTRAINTS_type},
    {"-scons", SYMBOLIC_CONSTRAINTS_type},
    {0, 0}
};


ABC_THREAD_LOCAL struct cube_struct cube, temp_cube_save;
ABC_THREAD_LOCAL struct cdata_struct cdata, temp_cdata_save;

void Espresso_Reset(void)
{
    memset(&cube, 0, sizeof(cube));
    memset(&cdata, 0, sizeof(cdata));
    memset(total_time, 0, sizeof(total_time));
    memset(total_calls, 0, sizeof(total_calls));
    filename = NULL;
}

const int bit_count[256] = {
  0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
  1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
  1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
  2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
  1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
  2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
  2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
  3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
};
ABC_NAMESPACE_IMPL_END

