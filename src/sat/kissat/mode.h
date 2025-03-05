#ifndef _mode_h_INCLUDED
#define _mode_h_INCLUDED

struct kissat;

typedef struct mode mode;

struct mode {
  uint64_t ticks;
#ifndef QUIET
  double entered;
  uint64_t conflicts;
#ifdef METRICS
  uint64_t propagations;
  uint64_t visits;
#endif
#endif
};

void kissat_init_mode_limit (struct kissat *);
bool kissat_switching_search_mode (struct kissat *);
void kissat_switch_search_mode (struct kissat *);

#endif
