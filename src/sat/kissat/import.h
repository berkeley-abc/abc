#ifndef _import_h_INLCUDED
#define _import_h_INLCUDED

struct kissat;

unsigned kissat_import_literal (struct kissat *solver, int lit);
unsigned kissat_fresh_literal (struct kissat *solver);

#endif
