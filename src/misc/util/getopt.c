/*
 * Revision Control Information
 *
 * /projects/hsis/CVS/utilities/util/getopt.c,v
 * rajeev
 * 1.3
 * 1995/08/08 22:41:22
 *
 */
/* LINTLIBRARY */

#include <stdio.h>
#include "util.h"


/*  File   : getopt.c
 *  Author : Henry Spencer, University of Toronto
 *  Updated: 28 April 1984
 *
 *  Changes: (R Rudell)
 *    changed index() to strchr();
 *    added getopt_reset() to reset the getopt argument parsing
 *
 *  Purpose: get option letter from argv.
 */

char *util_optarg;    /* Global argument pointer. */
int util_optind = 0;    /* Global argv index. */
static char *scan;


void
util_getopt_reset()
{
    util_optarg = 0;
    util_optind = 0;
    scan = 0;
}



int 
util_getopt(argc, argv, optstring)
int argc;
char *argv[];
char *optstring;
{
    register int c;
    register char *place;

    util_optarg = NIL(char);

    if (scan == NIL(char) || *scan == '\0') {
    if (util_optind == 0) util_optind++;
    if (util_optind >= argc) return EOF;
    place = argv[util_optind];
    if (place[0] != '-' || place[1] == '\0') return EOF;
    util_optind++;
    if (place[1] == '-' && place[2] == '\0') return EOF;
    scan = place+1;
    }

    c = *scan++;
    place = strchr(optstring, c);
    if (place == NIL(char) || c == ':') {
    (void) fprintf(stderr, "%s: unknown option %c\n", argv[0], c);
    return '?';
    }
    if (*++place == ':') {
    if (*scan != '\0') {
        util_optarg = scan;
        scan = NIL(char);
    } else {
        if (util_optind >= argc) {
        (void) fprintf(stderr, "%s: %c requires an argument\n", 
            argv[0], c);
        return '?';
        }
        util_optarg = argv[util_optind];
        util_optind++;
    }
    }
    return c;
}
