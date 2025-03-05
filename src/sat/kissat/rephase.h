#ifndef _rephase_h_INCLUDED
#define _rephase_h_INCLUDED

#include <stdbool.h>

struct kissat;

bool kissat_rephasing (struct kissat *);
void kissat_rephase (struct kissat *);

#endif
