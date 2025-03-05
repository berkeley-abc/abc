#ifndef _classify_h_INCLUDED
#define _classify_h_INCLUDED

#include <stdbool.h>

struct kissat;

struct classification {
  bool small;
  bool bigbig;
};

typedef struct classification classification;

void kissat_classify (struct kissat *);

#endif
