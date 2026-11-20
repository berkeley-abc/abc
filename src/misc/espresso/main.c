/*
 * Revision Control Information
 *
 * $Source$
 * $Author$
 * $Revision$
 * $Date$
 *
 */
/*
 *  Main driver for espresso
 *
 *  Old style -do xxx, -out xxx, etc. are still supported.
 */

#include <setjmp.h>
#include "espresso.h"

ABC_NAMESPACE_IMPL_START
        /* table definitions for options */
#include "main.h"

static ABC_THREAD_LOCAL FILE *last_fp;
static ABC_THREAD_LOCAL jmp_buf espresso_abort;
ABC_THREAD_LOCAL FILE *espresso_out, *espresso_err;

/* Every block is zero-filled, including the tail added by a reallocation,
   so that the inherited reads of unset words (for example, the SIZE field of
   cubes built by dsharp and sorted by sf_union) do not depend on heap contents.
   The header has four pointer-sized fields to keep the payload aligned. */
typedef struct espresso_block {
    struct espresso_block *prev, *next;
    size_t size;
    size_t unused;
} espresso_block;
static ABC_THREAD_LOCAL espresso_block *blocks;
static ABC_THREAD_LOCAL char *text_buffers[3];
static ABC_THREAD_LOCAL size_t text_capacity[3];

char * Espresso_Buffer(int i, size_t n)
{
    if (text_capacity[i] < n) {
        text_buffers[i] = REALLOC(char, text_buffers[i], n);
        text_capacity[i] = n;
    }
    return text_buffers[i];
}


void Espresso_Fail(void)
{
    longjmp(espresso_abort, 1);
}

void * Espresso_Realloc(void *ptr, size_t n, size_t size)
{
    espresso_block *old = ptr ? (espresso_block *)ptr - 1 : NULL;
    espresso_block *prev = old ? old->prev : NULL;
    espresso_block *next = old ? old->next : blocks;
    size_t old_size = old ? old->size : 0;
    espresso_block *b;
    if (n > ((size_t)-1 - sizeof(*b)) / size)
        fatal("allocation too large");
    b = (espresso_block *)realloc(old, sizeof(*b) + n*size);
    if (!b)
        fatal("out of memory");
    if (n*size > old_size)
        memset((char *)(b + 1) + old_size, 0, n*size - old_size);
    b->size = n*size;
    b->prev = prev;
    b->next = next;
    if (prev) prev->next = b;
    else blocks = b;
    if (next) next->prev = b;
    return b + 1;
}

void * Espresso_Alloc(size_t n, size_t size)
{
    return Espresso_Realloc(NULL, n, size);
}

void Espresso_Free(void *ptr)
{
    espresso_block *b;
    if (!ptr) return;
    b = (espresso_block *)ptr - 1;
    if (b->prev) b->prev->next = b->next;
    else blocks = b->next;
    if (b->next) b->next->prev = b->prev;
    free(b);
}

char * Espresso_Strdup(const char *s)
{
    return s ? strcpy(ALLOC(char, strlen(s) + 1), s) : NULL;
}

const char * Espresso_PrintTime(long ms)
{
    static ABC_THREAD_LOCAL char buf[40];
    snprintf(buf, sizeof(buf), "%ld.%02ld sec", ms / 1000, ms % 1000 / 10);
    return buf;
}

static void getPLA(int, int, char **, int, pPLA *, int);
static void runtime(void);
static void init_runtime(void);
static void usage(void);
static void delete_arg(int *, char **, int);
static int check_arg(int *, char **, const char *);
static void backward_compatibility_hack(int *, char **, int *, int *, const struct esp_option *);

static int next_option(int argc, char **argv, int *index, const char **scan, const char **arg)
{
    const char *spec = "D:S:de:ho:r:stv:x";
    const char *opt;
    int c;
    *arg = NULL;
    if (!**scan) {
        const char *s = *index < argc ? argv[*index] : "";
        if (s[0] != '-' || !s[1]) return EOF;
        ++*index;
        if (!strcmp(s, "--")) return EOF;
        *scan = s + 1;
    }
    c = *(*scan)++;
    opt = strchr(spec, c);
    if (!opt || c == ':') return '?';
    if (opt[1] == ':') {
        if (**scan) *arg = *scan;
        else if (*index < argc) *arg = argv[(*index)++];
        else return '?';
        *scan = "";
    }
    return c;
}

static ABC_THREAD_LOCAL int input_type = FD_type;


static int espresso_run(int argc, char *argv[])
{
    int i, j, first, last, strategy, out_type, option;
    pPLA PLA, PLA1;
    pcover F, Fold, Dold;
    pset last1, p;
    cost_t cost;
    espresso_bool error, exact_cover;
    long start;
    int util_optind = 1;
    const char *util_optarg;
    const char *scan = "";
    const struct esp_option esp_opt_table[] = {
        {"eat", &echo_comments, FALSE},
        {"eatdots", &echo_unknown_commands, FALSE},
        {"fast", &single_expand, TRUE},
        {"kiss", &kiss, TRUE},
        {"ness", &remove_essential, FALSE},
        {"nirr", &force_irredundant, FALSE},
        {"nunwrap", &unwrap_onset, FALSE},
        {"onset", &recompute_onset, TRUE},
        {"pos", &pos, TRUE},
        {"random", &use_random_order, TRUE},
        {"strong", &use_super_gasp, TRUE},
        {0, NULL, 0}
    };


    start = ptime();

    input_type = FD_type;
    skip_make_sparse = FALSE;
    espresso_reduce_toggle = TRUE;
    error = FALSE;
    init_runtime();
#ifdef RANDOM
    srandom(314973);
#endif

    option = 0;            /* default -D: ESPRESSO */
    out_type = F_type;        /* default -o: default is ON-set only */
    debug = 0;            /* default -d: no debugging info */
    verbose_debug = FALSE;    /* default -v: not verbose */
    print_solution = TRUE;    /* default -x: print the solution (!) */
    summary = FALSE;        /* default -s: no summary */
    trace = FALSE;        /* default -t: no trace information */
    strategy = 0;        /* default -S: strategy number */
    first = -1;            /* default -R: select range */
    last = -1;
    remove_essential = TRUE;    /* default -e: */
    force_irredundant = TRUE;
    unwrap_onset = TRUE;
    single_expand = FALSE;
    pos = FALSE;
    recompute_onset = FALSE;
    use_super_gasp = FALSE;
    use_random_order = FALSE;
    kiss = FALSE;
    echo_comments = TRUE;
    echo_unknown_commands = TRUE;
    exact_cover = FALSE;    /* for -qm option, the default */

    backward_compatibility_hack(&argc, argv, &option, &out_type, esp_opt_table);


    /* parse command line options*/
    while ((i = next_option(argc, argv, &util_optind, &scan, &util_optarg)) != EOF) {
    switch(i) {
        case 'D':        /* -Dcommand invokes a subcommand */
        for(j = 0; option_table[j].name != 0; j++) {
            if (strcmp(util_optarg, option_table[j].name) == 0) {
            option = j;
            break;
            }
        }
        if (option_table[j].name == 0) {
            (void) fprintf(espresso_err, "%s: bad subcommand \"%s\"\n",
            argv[0], util_optarg);
            Espresso_Fail();
        }
        break;

        case 'o':        /* -ooutput selects and output option */
        for(j = 0; pla_types[j].key != 0; j++) {
            if (strcmp(util_optarg, pla_types[j].key+1) == 0) {
            out_type = pla_types[j].value;
            break;
            }
        }
        if (pla_types[j].key == 0) {
            (void) fprintf(espresso_err, "%s: bad output type \"%s\"\n",
            argv[0], util_optarg);
            Espresso_Fail();
        }
        break;

        case 'e':        /* -eespresso selects an option for espresso */
        for(j = 0; esp_opt_table[j].name != 0; j++) {
            if (strcmp(util_optarg, esp_opt_table[j].name) == 0) {
            *(esp_opt_table[j].variable) = esp_opt_table[j].value;
            break;
            }
        }
        if (esp_opt_table[j].name == 0) {
            (void) fprintf(espresso_err, "%s: bad espresso option \"%s\"\n",
            argv[0], util_optarg);
            Espresso_Fail();
        }
        break;

        case 'd':        /* -d turns on (softly) all debug switches */
        debug = debug_table[0].value;
        trace = TRUE;
        summary = TRUE;
        break;

        case 'v':        /* -vdebug invokes a debug option */
        verbose_debug = TRUE;
        for(j = 0; debug_table[j].name != 0; j++) {
            if (strcmp(util_optarg, debug_table[j].name) == 0) {
            debug |= debug_table[j].value;
            break;
            }
        }
        if (debug_table[j].name == 0) {
            (void) fprintf(espresso_err, "%s: bad debug type \"%s\"\n",
            argv[0], util_optarg);
            Espresso_Fail();
        }
        break;

        case 't':
        trace = TRUE;
        break;

        case 's':
        summary = TRUE;
        break;

        case 'x':        /* -x suppress printing of results */
        print_solution = FALSE;
        break;

        case 'S':        /* -S sets a strategy for several cmds */
        strategy = atoi(util_optarg);
        break;

        case 'r':        /* -r selects range (outputs or vars) */
        if (sscanf(util_optarg, "%d-%d", &first, &last) < 2) {
            (void) fprintf(espresso_err, "%s: bad output range \"%s\"\n",
            argv[0], util_optarg);
            Espresso_Fail();
        }
        break;

        case 'h':
        usage();
        return 0;

        default:
        usage();
        Espresso_Fail();
    }
    }

    /* provide version information and summaries */
    if (summary || trace) {
    /* echo command line and arguments */
    espresso_printf("#");
    for(i = 0; i < argc; i++) {
        espresso_printf(" %s", argv[i]);
    }
    espresso_printf("\n");
    espresso_printf("# %s\n", VERSION);
    }

    /* the remaining arguments are argv[util_optind ... argc-1] */
    PLA = PLA1 = NIL(PLA_t);
    switch(option_table[option].num_plas) {
    case 2:
        if (util_optind+2 < argc) fatal("trailing arguments on command line");
        getPLA(util_optind++, argc, argv, option, &PLA, out_type);
        getPLA(util_optind++, argc, argv, option, &PLA1, out_type);
        break;
    case 1:
        if (util_optind+1 < argc) fatal("trailing arguments on command line");
        getPLA(util_optind++, argc, argv, option, &PLA, out_type);
        break;
    }
    if (util_optind < argc) fatal("trailing arguments on command line");

    if (summary || trace) {
    if (PLA != NIL(PLA_t)) PLA_summary(PLA);
    if (PLA1 != NIL(PLA_t)) PLA_summary(PLA1);
    }

/*
 *  Now a case-statement to decide what to do
 */

    switch(option_table[option].key) {
    case KEY_unknown:
    return 1;


/******************** Espresso operations ********************/

    case KEY_ESPRESSO:
    Fold = sf_save(PLA->F);
    PLA->F = espresso(PLA->F, PLA->D, PLA->R);
    EXECUTE(error=verify(PLA->F,Fold,PLA->D), VERIFY_TIME, PLA->F, cost);
    if (error) {
        print_solution = FALSE;
        PLA->F = Fold;
        (void) check_consistency(PLA);
    } else {
        free_cover(Fold);
    }
    break;

    case KEY_MANY_ESPRESSO: {
    int pla_type;
    do {
        EXEC(PLA->F=espresso(PLA->F,PLA->D,PLA->R),"ESPRESSO   ",PLA->F);
        if (print_solution) {
        fprint_pla(espresso_out, PLA, out_type);
        (void) fflush(espresso_out);
        }
        pla_type = PLA->pla_type;
        free_PLA(PLA);
        setdown_cube();
        FREE(cube.part_size);
    } while (read_pla(last_fp, TRUE, TRUE, pla_type, &PLA) != EOF);
    return 0;
    }

    case KEY_simplify:
    EXEC(PLA->F = simplify(cube1list(PLA->F)), "SIMPLIFY  ", PLA->F);
    break;

    case KEY_so:            /* minimize all functions as single-output */
    if (strategy < 0 || strategy > 1) {
        strategy = 0;
    }
    so_espresso(PLA, strategy);
    break;

    case KEY_so_both:        /* minimize all functions as single-output */
    if (strategy < 0 || strategy > 1) {
        strategy = 0;
    }
    so_both_espresso(PLA, strategy);
    break;

    case KEY_expand:            /* execute expand */
    EXECUTE(PLA->F=expand(PLA->F,PLA->R,FALSE),EXPAND_TIME, PLA->F, cost);
    break;

    case KEY_irred:             /* extract minimal irredundant subset */
    EXECUTE(PLA->F = irredundant(PLA->F, PLA->D), IRRED_TIME, PLA->F, cost);
    break;

    case KEY_reduce:            /* perform reduction */
    EXECUTE(PLA->F = reduce(PLA->F, PLA->D), REDUCE_TIME, PLA->F, cost);
    break;

    case KEY_essen:             /* check for essential primes */
    foreach_set(PLA->F, last1, p) {
        SET(p, RELESSEN);
        RESET(p, NONESSEN);
    }
    EXECUTE(F = essential(&(PLA->F), &(PLA->D)), ESSEN_TIME, PLA->F, cost);
    free_cover(F);
    break;

    case KEY_super_gasp:
    PLA->F = super_gasp(PLA->F, PLA->D, PLA->R, &cost);
    break;

    case KEY_gasp:
    PLA->F = last_gasp(PLA->F, PLA->D, PLA->R, &cost);
    break;

    case KEY_make_sparse:       /* make_sparse step of Espresso */
    PLA->F = make_sparse(PLA->F, PLA->D, PLA->R);
    break;

    case KEY_exact:
    case KEY_qm:
    exact_cover = option_table[option].key == KEY_exact;
    Fold = sf_save(PLA->F);
    PLA->F = minimize_exact(PLA->F, PLA->D, PLA->R, exact_cover);
    EXECUTE(error=verify(PLA->F,Fold,PLA->D), VERIFY_TIME, PLA->F, cost);
    if (error) {
        print_solution = FALSE;
        PLA->F = Fold;
        (void) check_consistency(PLA);
    }
    free_cover(Fold);
    break;

    case KEY_primes:            /* generate all prime implicants */
    EXEC(PLA->F = primes_consensus(cube2list(PLA->F, PLA->D)), 
                            "PRIMES     ", PLA->F);
    break;

    case KEY_map:               /* print out a Karnaugh map of function */
    map(PLA->F);
    print_solution = FALSE;
    break;



/******************** Output phase and bit pairing ********************/

    case KEY_opo:               /* sasao output phase assignment */
    phase_assignment(PLA, strategy);
    break;

    case KEY_opoall:        /* try all phase assignments (!) */
    if (first < 0 || first >= cube.part_size[cube.output]) {
        first = 0;
    }
    if (last < 0 || last >= cube.part_size[cube.output]) {
        last = cube.part_size[cube.output] - 1;
    }
    opoall(PLA, first, last, strategy);
    break;

    case KEY_pair:              /* find an optimal pairing */
    find_optimal_pairing(PLA, strategy);
    break;

    case KEY_pairall:        /* try all pairings !! */
    pair_all(PLA, strategy);
    break;



/******************** Simple cover operations ********************/

    case KEY_echo:                /* echo the PLA */
    break;

    case KEY_taut:                /* tautology check */
    espresso_printf("ON-set is%sa tautology\n",
        tautology(cube1list(PLA->F)) ? " " : " not ");
    print_solution = FALSE;
    break;

    case KEY_contain:                /* single cube containment */
    PLA->F = sf_contain(PLA->F);
    break;

    case KEY_intersect:                /* cover intersection */
    PLA->F = cv_intersect(PLA->F, PLA1->F);
    break;

    case KEY_union:                /* cover union */
    PLA->F = sf_union(PLA->F, PLA1->F);
    break;

    case KEY_disjoint:                /* make cover disjoint */
    PLA->F = make_disjoint(PLA->F);
    break;

    case KEY_dsharp:                /* cover disjoint-sharp */
    PLA->F = cv_dsharp(PLA->F, PLA1->F);
    break;

    case KEY_sharp:                /* cover sharp */
    PLA->F = cv_sharp(PLA->F, PLA1->F);
    break;

    case KEY_lexsort:                /* lexical sort order */
    PLA->F = lex_sort(PLA->F);
    break;

    case KEY_stats:                /* print info on size */
    if (! summary) PLA_summary(PLA);
    print_solution = FALSE;
    break;

    case KEY_minterms:                /* explode into minterms */
    if (first < 0 || first >= cube.num_vars) {
        first = 0;
    }
    if (last < 0 || last >= cube.num_vars) {
        last = cube.num_vars - 1;
    }
    PLA->F = sf_dupl(unravel_range(PLA->F, first, last));
    break;

    case KEY_d1merge:                /* distance-1 merge */
    if (first < 0 || first >= cube.num_vars) {
        first = 0;
    }
    if (last < 0 || last >= cube.num_vars) {
        last = cube.num_vars - 1;
    }
    for(i = first; i <= last; i++) {
        PLA->F = d1merge(PLA->F, i);
    }
    break;

    case KEY_d1merge_in:        /* distance-1 merge inputs only */
    for(i = 0; i < cube.num_binary_vars; i++) {
        PLA->F = d1merge(PLA->F, i);
    }
    break;

    case KEY_PLA_verify:        /* check two PLAs for equivalence */
    EXECUTE(error = PLA_verify(PLA, PLA1), VERIFY_TIME, PLA->F, cost);
    if (error) {
        espresso_printf("PLA comparison failed; the PLA's are not equivalent\n");
        Espresso_Fail();
    } else {
        espresso_printf("PLA's compared equal\n");
        return 0;
    }
    break;    /* silly */

    case KEY_verify:            /* check two covers for equivalence */
    Fold = PLA->F;    Dold = PLA->D;    F = PLA1->F;
    EXECUTE(error=verify(F, Fold, Dold), VERIFY_TIME, PLA->F, cost);
    if (error) {
        espresso_printf("PLA comparison failed; the PLA's are not equivalent\n");
        Espresso_Fail();
    } else {
        espresso_printf("PLA's compared equal\n");
        return 0;
    }    
    break;    /* silly */

    case KEY_check:            /* check consistency */
    (void) check_consistency(PLA);
    print_solution = FALSE;
    break;

    case KEY_mapdc:            /* compute don't care set */
    map_dcset(PLA);
    out_type = FD_type;
    break;

    case KEY_equiv:
    find_equiv_outputs(PLA);
    print_solution = FALSE;
    break;

    case KEY_separate:            /* remove PLA->D from PLA->F */
    PLA->F = complement(cube2list(PLA->D, PLA->R));
    break;

    case KEY_xor: {
    pcover T1 = cv_intersect(PLA->F, PLA1->R);
    pcover T2 = cv_intersect(PLA1->F, PLA->R);
    free_cover(PLA->F);
    PLA->F = sf_contain(sf_join(T1, T2));
    free_cover(T1);
    free_cover(T2);
    break;
    }

    case KEY_fsm: {
    disassemble_fsm(PLA, summary);
    print_solution = FALSE;
    break;
    }

    case KEY_test: {
    pcover T, E;
    T = sf_join(PLA->D, PLA->R);
    E = new_cover(10);
    sf_free(PLA->F);
    EXECUTE(PLA->F = complement(cube1list(T)), COMPL_TIME, PLA->F, cost);
    EXECUTE(PLA->F = expand(PLA->F, T, FALSE), EXPAND_TIME, PLA->F, cost);
    EXECUTE(PLA->F = irredundant(PLA->F, E), IRRED_TIME, PLA->F, cost);
    sf_free(T);
    T = sf_join(PLA->F, PLA->R);
    EXECUTE(PLA->D = expand(PLA->D, T, FALSE), EXPAND_TIME, PLA->D, cost);
    EXECUTE(PLA->D = irredundant(PLA->D, E), IRRED_TIME, PLA->D, cost);
    sf_free(T);
    sf_free(E);
    break;
    }


    }

    /* Print a runtime summary if trace mode enabled */
    if (trace) {
    runtime();
    }

    /* Print total runtime */
    if (summary || trace) {
    print_trace(PLA->F, option_table[option].name, ptime()-start);
    }

    /* Output the solution */
    if (print_solution) {
    EXECUTE(fprint_pla(espresso_out, PLA, out_type), WRITE_TIME, PLA->F, cost);
    }

    /* Crash and burn if there was a verify error */
    if (error) {
    fatal("cover verification failed");
    }

    /* cleanup all used memory */
    free_PLA(PLA);
    FREE(cube.part_size);
    setdown_cube();             /* free the cube/cdata structure data */
    sf_cleanup();               /* free unused set structures */
    sm_cleanup();               /* sparse matrix cleanup */

    return 0;
}


static void getPLA(int opt, int argc, char *argv[], int option, pPLA *PLA, int out_type)
{
    FILE *fp;
    int needs_dcset, needs_offset;
    const char *fname;

    if (last_fp && last_fp != stdin) fclose(last_fp);
    last_fp = NULL;
    if (opt >= argc) {
    fp = stdin;
    fname = "(stdin)";
    } else {
    fname = argv[opt];
    if (strcmp(fname, "-") == 0) {
        fp = stdin;
    } else if ((fp = fopen(argv[opt], "r")) == NULL) {
        (void) fprintf(espresso_err, "%s: Unable to open %s\n", argv[0], fname);
        Espresso_Fail();
    }
    }
    if (option_table[option].key == KEY_echo) {
    needs_dcset = (out_type & D_type) != 0;
    needs_offset = (out_type & R_type) != 0;
    } else {
    needs_dcset = option_table[option].needs_dcset;
    needs_offset = option_table[option].needs_offset;
    }

    last_fp = fp;
    if (read_pla(fp, needs_dcset, needs_offset, input_type, PLA) == EOF) {
    (void) fprintf(espresso_err, "%s: Unable to find PLA on file %s\n", argv[0], fname);
    Espresso_Fail();
    }
    (*PLA)->filename = util_strsav(fname);
    filename = (*PLA)->filename;

}


static void runtime(void)
{
    int i;
    long total = 1, temp;

    for(i = 0; i < TIME_COUNT; i++) {
    total += total_time[i];
    }
    for(i = 0; i < TIME_COUNT; i++) {
    if (total_calls[i] != 0) {
        temp = 100 * total_time[i];
        espresso_printf("# %s\t%2d call(s) for %s (%2ld.%01ld%%)\n",
        total_name[i], total_calls[i], print_time(total_time[i]),
            temp/total, (10 * (temp%total)) / total);
    }
    }
}


static void init_runtime(void)
{
    total_name[READ_TIME] =     "READ       ";
    total_name[WRITE_TIME] =    "WRITE      ";
    total_name[COMPL_TIME] =    "COMPL      ";
    total_name[REDUCE_TIME] =   "REDUCE     ";
    total_name[EXPAND_TIME] =   "EXPAND     ";
    total_name[ESSEN_TIME] =    "ESSEN      ";
    total_name[IRRED_TIME] =    "IRRED      ";
    total_name[GREDUCE_TIME] =  "REDUCE_GASP";
    total_name[GEXPAND_TIME] =  "EXPAND_GASP";
    total_name[GIRRED_TIME] =   "IRRED_GASP ";
    total_name[MV_REDUCE_TIME] ="MV_REDUCE  ";
    total_name[RAISE_IN_TIME] = "RAISE_IN   ";
    total_name[VERIFY_TIME] =   "VERIFY     ";
    total_name[PRIMES_TIME] =   "PRIMES     ";
    total_name[MINCOV_TIME] =   "MINCOV     ";
}


static void subcommands(void)
{
    int i, col;
    espresso_printf("                ");
    col = 16;
    for(i = 0; option_table[i].name != 0; i++) {
    if ((col + strlen(option_table[i].name) + 1) > 76) {
        espresso_printf(",\n                ");
        col = 16;
    } else if (i != 0) {
        espresso_printf(", ");
    }
    espresso_printf("%s", option_table[i].name);
    col += strlen(option_table[i].name) + 2;
    }
    espresso_printf("\n");
}


static void usage(void)
{
    espresso_printf("usage: espresso [options] [file [file2]]\n");
    espresso_printf("%s\n\n", VERSION);
    espresso_printf("  -d        Enable debugging\n");
    espresso_printf("  -e[opt]   Select espresso option:\n");
    espresso_printf("                fast, ness, nirr, nunwrap, onset, pos, strong,\n");
    espresso_printf("                eat, eatdots, kiss, random\n");
    espresso_printf("  -o[type]  Select output format:\n");
    espresso_printf("                f, fd, fr, fdr, pleasure, eqntott, kiss, cons\n");
    espresso_printf("  -rn-m     Select range for subcommands:\n");
    espresso_printf("                d1merge: first and last variables (0 ... m-1)\n");
    espresso_printf("                minterms: first and last variables (0 ... m-1)\n");
    espresso_printf("                opoall: first and last outputs (0 ... m-1)\n");
    espresso_printf("  -s        Provide short execution summary\n");
    espresso_printf("  -t        Provide longer execution trace\n");
    espresso_printf("  -x        Suppress printing of solution\n");
    espresso_printf("  -v[type]  Verbose debugging detail (-v '' for all)\n");
    espresso_printf("  -D[cmd]   Execute subcommand 'cmd':\n");
    subcommands();
    espresso_printf("  -h        Print this usage message\n");
    espresso_printf("  -Sn       Select strategy for subcommands:\n");
    espresso_printf("                opo: bit2=exact bit1=repeated bit0=skip sparse\n");
    espresso_printf("                opoall: 0=minimize, 1=exact\n");
    espresso_printf("                pair: 0=algebraic, 1=strongd, 2=espresso, 3=exact\n");
    espresso_printf("                pairall: 0=minimize, 1=exact, 2=opo\n");
    espresso_printf("                so_espresso: 0=minimize, 1=exact\n");
    espresso_printf("                so_both: 0=minimize, 1=exact\n");
}

/*
 *  Hack for backward compatibility (ACK! )
 */

static void backward_compatibility_hack(int *argc, char **argv, int *option, int *out_type, const struct esp_option *esp_opt_table)
{
    int i, j;

    /* Scan the argument list for something to do (default is ESPRESSO) */
    *option = 0;
    for(i = 1; i < (*argc)-1; i++) {
    if (strcmp(argv[i], "-do") == 0) {
        for(j = 0; option_table[j].name != 0; j++)
        if (strcmp(argv[i+1], option_table[j].name) == 0) {
            *option = j;
            delete_arg(argc, argv, i+1);
            delete_arg(argc, argv, i);
            break;
        }
        if (option_table[j].name == 0) {
        (void) fprintf(espresso_err,
         "espresso: bad keyword \"%s\" following -do\n",argv[i+1]);
        Espresso_Fail();
        }
        break;
    }
    }

    for(i = 1; i < (*argc)-1; i++) {
    if (strcmp(argv[i], "-out") == 0) {
        for(j = 0; pla_types[j].key != 0; j++)
        if (strcmp(pla_types[j].key+1, argv[i+1]) == 0) {
            *out_type = pla_types[j].value;
            delete_arg(argc, argv, i+1);
            delete_arg(argc, argv, i);
            break;
        }
        if (pla_types[j].key == 0) {
        (void) fprintf(espresso_err,
           "espresso: bad keyword \"%s\" following -out\n",argv[i+1]);
        Espresso_Fail();
        }
        break;
    }
    }

    for(i = 1; i < (*argc); i++) {
    if (argv[i][0] == '-') {
        for(j = 0; esp_opt_table[j].name != 0; j++) {
        if (strcmp(argv[i]+1, esp_opt_table[j].name) == 0) {
            delete_arg(argc, argv, i);
            *(esp_opt_table[j].variable) = esp_opt_table[j].value;
            break;
        }
        }
    }
    }

    if (check_arg(argc, argv, "-fdr")) input_type = FDR_type;
    if (check_arg(argc, argv, "-fr")) input_type = FR_type;
    if (check_arg(argc, argv, "-f")) input_type = F_type;
}


/* delete_arg -- delete an argument from the argument list */
static void delete_arg(int *argc, char *argv[], int num)
{
    int i;
    (*argc)--;
    for(i = num; i < *argc; i++) {
    argv[i] = argv[i+1];
    }
}


/* check_arg -- scan argv for an argument, and return TRUE if found */
static int check_arg(int *argc, char *argv[], const char *s)
{
    int i;
    for(i = 1; i < *argc; i++) {
    if (strcmp(argv[i], s) == 0) {
        delete_arg(argc, argv, i);
        return TRUE;
    }
    }
    return FALSE;
}

int Espresso_Main(int argc, char **argv, FILE *out, FILE *err)
{
    int status;
    char **args;
    espresso_out = out;
    espresso_err = err;
    if (setjmp(espresso_abort))
        status = 1;
    else {
        args = ALLOC(char *, argc + 1);
        memcpy(args, argv, argc * sizeof(*args));
        args[argc] = NULL;
        status = espresso_run(argc, args);
    }
    if (last_fp && last_fp != stdin) fclose(last_fp);
    last_fp = NULL;
    sf_cleanup();
    sm_cleanup();
    while (blocks) Espresso_Free(blocks + 1);
    memset(text_buffers, 0, sizeof(text_buffers));
    memset(text_capacity, 0, sizeof(text_capacity));
    Espresso_Reset();
    espresso_out = espresso_err = NULL;
    return status;
}
ABC_NAMESPACE_IMPL_END

#ifdef ESPRESSO_MAIN
int main(int argc, char **argv)
{
    return ABC_NAMESPACE_PREFIX Espresso_Main(argc, argv, stdout, stderr);
}
#endif

