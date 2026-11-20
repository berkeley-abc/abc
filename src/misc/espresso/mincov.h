/*
 * Revision Control Information
 *
 * $Source$
 * $Author$
 * $Revision$
 * $Date$
 *
 */
#ifndef ABC__misc__espresso__mincov_h
#define ABC__misc__espresso__mincov_h

#include "sparse.h"

ABC_NAMESPACE_HEADER_START

/* exported */
extern sm_row *sm_minimum_cover(sm_matrix *A, int *weight, int heuristic, int debug_level);

ABC_NAMESPACE_HEADER_END

#endif
