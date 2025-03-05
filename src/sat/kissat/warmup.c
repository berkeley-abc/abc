#include "warmup.h"
#include "backtrack.h"
#include "decide.h"
#include "internal.h"
#include "print.h"
#include "propbeyond.h"
#include "terminate.h"

void kissat_warmup (kissat *solver) {
  assert (!solver->level);
  assert (solver->watching);
  assert (!solver->inconsistent);
  assert (GET_OPTION (warmup));
  START (warmup);
  assert (!solver->warming);
  solver->warming = true;
  INC (warmups);
#ifndef QUIET
  const statistics *stats = &solver->statistics;
  uint64_t propagations = stats->warming_propagations;
  uint64_t decisions = stats->warming_decisions;
#endif
  while (solver->unassigned) {
    if (TERMINATED (warmup_terminated_1))
      break;
    kissat_decide (solver);
    kissat_propagate_beyond_conflicts (solver);
  }
  assert (!solver->inconsistent);
#ifndef QUIET
  decisions = stats->warming_decisions - decisions;
  propagations = stats->warming_propagations - propagations;

  kissat_very_verbose (solver,
                       "warming-up needed %" PRIu64
                       " decisions and %" PRIu64 " propagations",
                       decisions, propagations);

  if (solver->unassigned)
    kissat_verbose (solver,
                    "reached decision level %u "
                    "during warming-up saved phases",
                    solver->level);
  else
    kissat_verbose (solver,
                    "all variables assigned at decision level %u "
                    "during warming-up saved phases",
                    solver->level);
#endif
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (solver->warming);
  solver->warming = false;
  STOP (warmup);
}
