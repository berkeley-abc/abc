#ifndef _reorder_h_INCLUDED
#define _reorder_h_INCLUDED

#include <stdbool.h>

struct kissat;

bool kissat_reordering (struct kissat *);
void kissat_reorder (struct kissat *);

#endif
