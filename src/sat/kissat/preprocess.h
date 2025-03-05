#ifndef _kissat_preprocess_h_INCLUDED
#define _kissat_preprocess_h_INCLUDED

#include <stdbool.h>

struct kissat;
bool kissat_preprocessing (struct kissat *);
int kissat_preprocess (struct kissat *);

#endif
