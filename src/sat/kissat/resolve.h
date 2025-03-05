#ifndef _resolve_h_INCLUDED
#define _resolve_h_INCLUDED

#include <stdbool.h>

struct kissat;

bool kissat_generate_resolvents (struct kissat *, unsigned idx,
                                 unsigned *lit_ptr);

#endif
