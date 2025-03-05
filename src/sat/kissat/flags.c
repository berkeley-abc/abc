#include "inline.h"
#include "inlineheap.h"
#include "inlinequeue.h"

static inline void activate_literal (kissat *solver, unsigned lit) {
  const unsigned idx = IDX (lit);
  flags *f = FLAGS (idx);
  if (f->active)
    return;
  lit = STRIP (lit);
  LOG ("activating %s", LOGVAR (idx));
  f->active = true;
  assert (!f->fixed);
  assert (!f->eliminated);
  solver->active++;
  INC (variables_activated);
  kissat_enqueue (solver, idx);
  const double score = 1.0 - 1.0 / solver->statistics.variables_activated;
  kissat_update_heap (solver, &solver->scores, idx, score);
  if (solver->stable) {
    const unsigned lit = LIT (idx);
    if (!VALUE (lit))
      kissat_push_heap (solver, &solver->scores, idx);
  }
  assert (solver->unassigned < UINT_MAX);
  solver->unassigned++;
  kissat_mark_removed_literal (solver, lit);
  kissat_mark_added_literal (solver, lit);
  assert (!VALUE (lit));
  assert (!VALUE (NOT (lit)));
  assert (!SAVED (idx));
  assert (!TARGET (idx));
  assert (!BEST (idx));
}

static inline void deactivate_variable (kissat *solver, flags *f,
                                        unsigned idx) {
  assert (solver->flags + idx == f);
  LOG ("deactivating %s", LOGVAR (idx));
  assert (f->active);
  assert (f->eliminated || f->fixed);
  f->active = false;
  assert (solver->active > 0);
  solver->active--;
  kissat_dequeue (solver, idx);
  if (kissat_heap_contains (SCORES, idx))
    kissat_pop_heap (solver, SCORES, idx);
}

void kissat_activate_literal (kissat *solver, unsigned lit) {
  activate_literal (solver, lit);
}

void kissat_activate_literals (kissat *solver, unsigned size,
                               unsigned *lits) {
  for (unsigned i = 0; i < size; i++)
    activate_literal (solver, lits[i]);
}

void kissat_mark_fixed_literal (kissat *solver, unsigned lit) {
  assert (VALUE (lit) > 0);
  const unsigned idx = IDX (lit);
  LOG ("marking internal %s as fixed", LOGVAR (idx));
  flags *f = FLAGS (idx);
  assert (f->active);
  assert (!f->eliminated);
  assert (!f->fixed);
  f->fixed = true;
  deactivate_variable (solver, f, idx);
  INC (units);
  int elit = kissat_export_literal (solver, lit);
  assert (elit);
  PUSH_STACK (solver->units, elit);
  LOG ("pushed external unit literal %d (internal %u)", elit, lit);
}

void kissat_mark_eliminated_variable (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  assert (!VALUE (lit));
  LOG ("marking internal %s as eliminated", LOGVAR (idx));
  flags *f = FLAGS (idx);
  assert (f->active);
  assert (!f->eliminated);
  assert (!f->fixed);
  f->eliminated = true;
  deactivate_variable (solver, f, idx);
  int elit = kissat_export_literal (solver, lit);
  assert (elit);
  assert (elit != INT_MIN);
  unsigned eidx = ABS (elit);
  import *import = &PEEK_STACK (solver->import, eidx);
  assert (!import->eliminated);
  assert (import->imported);
  assert (STRIP (import->lit) == STRIP (lit));
  size_t pos = SIZE_STACK (solver->eliminated);
  assert (pos < (1u << 30));
  import->lit = pos;
  import->eliminated = true;
  PUSH_STACK (solver->eliminated, (value) 0);
  LOG ("marked external variable %u as eliminated", eidx);
  assert (solver->unassigned > 0);
  solver->unassigned--;
}

void kissat_mark_removed_literals (kissat *solver, unsigned size,
                                   unsigned *lits) {
  for (unsigned i = 0; i < size; i++)
    kissat_mark_removed_literal (solver, lits[i]);
}

void kissat_mark_added_literals (kissat *solver, unsigned size,
                                 unsigned *lits) {
  for (unsigned i = 0; i < size; i++)
    kissat_mark_added_literal (solver, lits[i]);
}
