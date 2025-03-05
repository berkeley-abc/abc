#include "trail.h"
#include "backtrack.h"
#include "inline.h"
#include "propsearch.h"

void kissat_flush_trail (kissat *solver) {
  assert (!solver->level);
  assert (solver->unflushed);
  assert (!solver->inconsistent);
  assert (kissat_propagated (solver));
  assert (SIZE_ARRAY (solver->trail) == solver->unflushed);
  LOG ("flushed %zu units from trail", SIZE_ARRAY (solver->trail));
  CLEAR_ARRAY (solver->trail);
  kissat_reset_propagate (solver);
  solver->unflushed = 0;
}

void kissat_mark_reason_clauses (kissat *solver, reference start) {
  LOG ("starting marking reason clauses at clause[%" REFERENCE_FORMAT "]",
       start);
  assert (!solver->unflushed);
#ifdef LOGGING
  unsigned reasons = 0;
#endif
  ward *arena = BEGIN_STACK (solver->arena);
  for (all_stack (unsigned, lit, solver->trail)) {
    assigned *a = ASSIGNED (lit);
    assert (a->level > 0);
    if (a->binary)
      continue;
    const reference ref = a->reason;
    assert (ref != UNIT_REASON);
    if (ref == DECISION_REASON)
      continue;
    if (ref < start)
      continue;
    clause *c = (clause *) (arena + ref);
    assert (kissat_clause_in_arena (solver, c));
    c->reason = true;
#ifdef LOGGING
    reasons++;
#endif
  }
  LOG ("marked %u reason clauses", reasons);
}

bool kissat_flush_and_mark_reason_clauses (kissat *solver,
                                           reference start) {
  assert (solver->watching);
  assert (!solver->inconsistent);
  assert (kissat_propagated (solver));

  if (solver->unflushed) {
    LOG ("need to flush %u units from trail", solver->unflushed);
    kissat_backtrack_propagate_and_flush_trail (solver);
  } else {
    LOG ("no need to flush units from trail (all units already flushed)");
    kissat_mark_reason_clauses (solver, start);
  }

  return true;
}

void kissat_unmark_reason_clauses (kissat *solver, reference start) {
  LOG ("starting unmarking reason clauses at clause[%" REFERENCE_FORMAT "]",
       start);
  assert (!solver->unflushed);
#ifdef LOGGING
  unsigned reasons = 0;
#endif
  ward *arena = BEGIN_STACK (solver->arena);
  for (all_stack (unsigned, lit, solver->trail)) {
    assigned *a = ASSIGNED (lit);
    assert (a->level > 0);
    if (a->binary)
      continue;
    const reference ref = a->reason;
    assert (ref != UNIT_REASON);
    if (ref == DECISION_REASON)
      continue;
    if (ref < start)
      continue;
    clause *c = (clause *) (arena + ref);
    assert (kissat_clause_in_arena (solver, c));
    assert (c->reason);
    c->reason = false;
#ifdef LOGGING
    reasons++;
#endif
  }
  LOG ("unmarked %u reason clauses", reasons);
}
