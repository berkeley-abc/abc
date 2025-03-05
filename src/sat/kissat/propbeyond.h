#ifndef _propall_h_INCLUDED
#define _propall_h_INCLUDED

struct kissat;
struct clause;

void kissat_propagate_beyond_conflicts (struct kissat *);

#endif
