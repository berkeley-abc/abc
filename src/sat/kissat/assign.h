#ifndef _assign_h_INCLUDED
#define _assign_h_INCLUDED

#include <stdbool.h>

#define DECISION_REASON UINT_MAX
#define UNIT_REASON (DECISION_REASON - 1)

#define INVALID_LEVEL UINT_MAX
#define INVALID_TRAIL UINT_MAX

typedef struct assigned assigned;
struct clause;

struct assigned {
  unsigned level;
  unsigned trail;

  bool analyzed : 1;
  bool binary : 1;
  bool poisoned : 1;
  bool removable : 1;
  bool shrinkable : 1;

  unsigned reason;
};

#define ASSIGNED(LIT) \
  (assert (VALID_INTERNAL_LITERAL (LIT)), solver->assigned + IDX (LIT))

#define LEVEL(LIT) (ASSIGNED (LIT)->level)
#define TRAIL(LIT) (ASSIGNED (LIT)->trail)
#define REASON(LIT) (ASSIGNED (LIT)->reason)

#ifndef FAST_ASSIGN

#include "reference.h"

struct kissat;
struct clause;

void kissat_assign_unit (struct kissat *, unsigned lit, const char *);
void kissat_learned_unit (struct kissat *, unsigned lit);
void kissat_original_unit (struct kissat *, unsigned lit);

void kissat_assign_decision (struct kissat *, unsigned lit);

void kissat_assign_binary (struct kissat *, unsigned, unsigned);

void kissat_assign_reference (struct kissat *, unsigned lit, reference,
                              struct clause *);

#endif

#endif
