#ifndef _tiers_h_INCLUDED
#define _tiers_h_INCLUDED

#include <stdbool.h>

struct kissat;

void kissat_compute_and_set_tier_limits (struct kissat *);
void kissat_print_tier_usage_statistics (struct kissat *solver,
                                         bool stable);

#endif
