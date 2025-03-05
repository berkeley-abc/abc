#ifndef _deduce_h_INCLUDED
#define _deduce_h_INCLUDED

#include <stdbool.h>

struct clause;
struct kissat;

struct clause *kissat_deduce_first_uip_clause (struct kissat *,
                                               struct clause *);

bool kissat_recompute_and_promote (struct kissat *, struct clause *);

#endif
