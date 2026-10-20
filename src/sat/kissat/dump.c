#include "global.h"

#ifndef KISSAT_NDEBUG

#include "inline.h"

#include <inttypes.h>

ABC_NAMESPACE_IMPL_START

static void dump_literal (kissat *solver, unsigned ilit) {
  const int elit = kissat_export_literal (solver, ilit);
  fprintf ( Abc_FrameGlobalGetOut(), "%u(%d)", ilit, elit);
  const int value = VALUE (ilit);
  if (value) {
    const unsigned ilit_level = LEVEL (ilit);
    fprintf ( Abc_FrameGlobalGetOut(), "@%u=%d", ilit_level, value);
  }
}

static void dump_binary (kissat *solver, unsigned a, unsigned b) {
  fprintf ( Abc_FrameGlobalGetOut(), "binary clause ");
  dump_literal (solver, a);
  fputc( ' ', Abc_FrameGlobalGetOut() );
  dump_literal (solver, b);
  fputc( '\n', Abc_FrameGlobalGetOut() );
}

static void dump_clause (kissat *solver, clause *c) {
  if (c->redundant)
    fprintf ( Abc_FrameGlobalGetOut(), "redundant glue %u", c->glue);
  else
    fprintf ( Abc_FrameGlobalGetOut(), "irredundant");
  const reference ref = kissat_reference_clause (solver, c);
  if (c->garbage)
    fprintf ( Abc_FrameGlobalGetOut(), " garbage");
  fprintf ( Abc_FrameGlobalGetOut(), " clause[%u]", ref);
  for (all_literals_in_clause (lit, c)) {
    fputc( ' ', Abc_FrameGlobalGetOut() );
    dump_literal (solver, lit);
  }
  fputc( '\n', Abc_FrameGlobalGetOut() );
}

static void dump_ref (kissat *solver, reference ref) {
  clause *c = kissat_dereference_clause (solver, ref);
  dump_clause (solver, c);
}

static void dump_trail (kissat *solver) {
  unsigned prev = 0;
  for (unsigned level = 0; level <= solver->level; level++) {
    frame *frame = &FRAME (level);
    unsigned next;
    if (level < solver->level)
      next = frame[1].trail;
    else
      next = SIZE_ARRAY (solver->trail);
    if (next == prev)
      fprintf ( Abc_FrameGlobalGetOut(), "frame[%u] has no assignments\n", level);
    else {
      fprintf ( Abc_FrameGlobalGetOut(), "frame[%u] has %u assignments\n", level, next - prev);
      if (prev < next)
        fprintf ( Abc_FrameGlobalGetOut(), "block[%u] = trail[%u..%u]\n", level, prev, next - 1);
    }
    for (unsigned i = prev; i < next; i++) {
      fprintf ( Abc_FrameGlobalGetOut(), "trail[%u] ", i);
      const unsigned lit = PEEK_ARRAY (solver->trail, i);
      dump_literal (solver, lit);
      const unsigned lit_level = LEVEL (lit);
      KISSAT_assert (lit_level <= level);
      if (lit_level < level)
        fprintf ( Abc_FrameGlobalGetOut(), " out-of-order");
      assigned *a = ASSIGNED (lit);
      if (!lit_level) {
        fprintf ( Abc_FrameGlobalGetOut(), " UNIT\n");
        KISSAT_assert (!a->binary);
        KISSAT_assert (a->reason == UNIT_REASON);
      } else {
        fputc( ' ', Abc_FrameGlobalGetOut() );
        if (a->binary) {
          const unsigned other = a->reason;
          dump_binary (solver, lit, other);
        } else if (a->reason == DECISION_REASON)
          fprintf ( Abc_FrameGlobalGetOut(), "DECISION\n");
        else {
          KISSAT_assert (a->reason != UNIT_REASON);
          const reference ref = a->reason;
          dump_ref (solver, ref);
        }
      }
    }
    prev = next;
  }
}

static void dump_values (kissat *solver) {
  for (unsigned idx = 0; idx < VARS; idx++) {
    unsigned lit = LIT (idx);
    int value = solver->values[lit];
    fprintf ( Abc_FrameGlobalGetOut(), "val[%u] = ", lit);
    if (!value)
      fprintf ( Abc_FrameGlobalGetOut(), "unassigned\n");
    else
      fprintf ( Abc_FrameGlobalGetOut(), "%d\n", value);
  }
}

static void dump_queue (kissat *solver) {
  const queue *const queue = &solver->queue;
  fprintf ( Abc_FrameGlobalGetOut(), "queue: first %u, last %u, stamp %u, search %u (stamp %u)\n",
          queue->first, queue->last, queue->stamp, queue->search.idx,
          queue->search.stamp);
  const links *const links = solver->links;
  for (unsigned idx = queue->first; !DISCONNECTED (idx);
       idx = links[idx].next) {
    const struct links *l = links + idx;
    fprintf ( Abc_FrameGlobalGetOut(), "%u ( prev %u, next %u, stamp %u )\n", idx, l->prev, l->next,
            l->stamp);
  }
}

static void dump_scores (kissat *solver) {
  heap *heap = SCORES;
  fprintf ( Abc_FrameGlobalGetOut(), "scores.vars = %u\n", heap->vars);
  fprintf ( Abc_FrameGlobalGetOut(), "scores.size = %u\n", heap->size);
  for (unsigned i = 0; i < SIZE_STACK (heap->stack); i++)
    fprintf ( Abc_FrameGlobalGetOut(), "scores.stack[%u] = %u\n", i, PEEK_STACK (heap->stack, i));
  for (unsigned i = 0; i < heap->vars; i++)
    fprintf ( Abc_FrameGlobalGetOut(), "scores.score[%u] = %g\n", i, heap->score[i]);
  for (unsigned i = 0; i < heap->vars; i++)
    fprintf ( Abc_FrameGlobalGetOut(), "scores.pos[%u] = %u\n", i, heap->pos[i]);
}

static void dump_export (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->export_);
  for (unsigned idx = 0; idx < size; idx++)
    fprintf ( Abc_FrameGlobalGetOut(), "export[%u] = %u\n", LIT (idx),
            PEEK_STACK (solver->export_, idx));
}

void dump_map (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->export_);
  unsigned first = INVALID_LIT;
  for (unsigned idx = 0; idx < size; idx++) {
    const unsigned ilit = LIT (idx);
    const int elit = PEEK_STACK (solver->export_, idx);
    fprintf ( Abc_FrameGlobalGetOut(), "map[%u] -> %d", ilit, elit);
    if (elit) {
      const unsigned eidx = ABS (elit);
      const import *const import = &PEEK_STACK (solver->import, eidx);
      if (import->eliminated)
        fprintf ( Abc_FrameGlobalGetOut(), " -> eliminated[%u]", import->lit);
      else {
        unsigned mlit = import->lit;
        if (elit < 0)
          mlit = NOT (mlit);
        fprintf ( Abc_FrameGlobalGetOut(), " -> %u", mlit);
      }
    }
    if (!LEVEL (ilit) && VALUE (ilit)) {
      if (first == INVALID_LIT) {
        first = ilit;
        fprintf ( Abc_FrameGlobalGetOut(), " #");
      } else
        fprintf ( Abc_FrameGlobalGetOut(), " *");
    }
    fputc( '\n', Abc_FrameGlobalGetOut() );
  }
}

static void dump_import (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->import);
  for (unsigned idx = 1; idx < size; idx++) {
    import *import = &PEEK_STACK (solver->import, idx);
    fprintf ( Abc_FrameGlobalGetOut(), "import[%u] = ", idx);
    if (!import->imported)
      fprintf ( Abc_FrameGlobalGetOut(), "undefined\n");
    else if (import->eliminated) {
      unsigned pos = import->lit;
      fprintf ( Abc_FrameGlobalGetOut(), "eliminated[%u]", pos);
      if (pos < SIZE_STACK (solver->eliminated)) {
        int value = PEEK_STACK (solver->eliminated, pos);
        if (value)
          fprintf ( Abc_FrameGlobalGetOut(), " (assigned to %d)", value);
      }
      fputc( '\n', Abc_FrameGlobalGetOut() );
    } else
      fprintf ( Abc_FrameGlobalGetOut(), "%u\n", import->lit);
  }
}

static void dump_etrail (kissat *solver) {
  for (unsigned i = 0; i < SIZE_STACK (solver->etrail); i++)
    fprintf ( Abc_FrameGlobalGetOut(), "etrail[%u] = %d\n", i, (int) PEEK_STACK (solver->etrail, i));
}

static void dump_extend (kissat *solver) {
  const extension *const begin = BEGIN_STACK (solver->extend);
  const extension *const end = END_STACK (solver->extend);
  for (const extension *p = begin, *q; p != end; p = q) {
    KISSAT_assert (p->blocking);
    fprintf ( Abc_FrameGlobalGetOut(), "extend[%zu] %d", (size_t) (p - begin), p->lit);
    if (!p[1].blocking)
      fputs (" :", Abc_FrameGlobalGetOut());
    for (q = p + 1; q != end && !q->blocking; q++)
      fprintf ( Abc_FrameGlobalGetOut(), " %d", q->lit);
    fputc( '\n', Abc_FrameGlobalGetOut() );
  }
}

static void dump_binaries (kissat *solver) {
  for (all_literals (lit)) {
    if (solver->watching) {
      for (all_binary_blocking_watches (watch, WATCHES (lit))) {
        if (!watch.type.binary)
          continue;
        const unsigned other = watch.binary.lit;
        if (lit > other)
          continue;
        dump_binary (solver, lit, other);
      }
    } else {
      for (all_binary_large_watches (watch, WATCHES (lit))) {
        if (!watch.type.binary)
          continue;
        const unsigned other = watch.binary.lit;
        if (lit > other)
          continue;
        dump_binary (solver, lit, other);
      }
    }
  }
}

static void dump_clauses (kissat *solver) {
  for (all_clauses (c))
    dump_clause (solver, c);
}

void kissat_dump_vectors (kissat *solver) {
  vectors *vectors = &solver->vectors;
  unsigneds *stack = &vectors->stack;
  fprintf ( Abc_FrameGlobalGetOut(), "vectors.size = %zu\n", SIZE_STACK (*stack));
  fprintf ( Abc_FrameGlobalGetOut(), "vectors.capacity = %zu\n", CAPACITY_STACK (*stack));
  fprintf ( Abc_FrameGlobalGetOut(), "vectors.usable = %zu\n", vectors->usable);
  const unsigned *const begin = BEGIN_STACK (*stack);
  const unsigned *const end = END_STACK (*stack);
  if (begin == end)
    return;
  fputc( '-', Abc_FrameGlobalGetOut() );
  for (const unsigned *p = begin + 1; p != end; p++)
    if (*p == INVALID_LIT)
      fputs (" -", Abc_FrameGlobalGetOut());
    else
      fprintf ( Abc_FrameGlobalGetOut(), " %u", *p);
  fputc( '\n', Abc_FrameGlobalGetOut() );
}

int kissat_dump (kissat *solver) {
  if (!solver)
    return 0;
  fprintf ( Abc_FrameGlobalGetOut(), "vars = %u\n", solver->vars);
  fprintf ( Abc_FrameGlobalGetOut(), "size = %u\n", solver->size);
  fprintf ( Abc_FrameGlobalGetOut(), "level = %u\n", solver->level);
  fprintf ( Abc_FrameGlobalGetOut(), "active = %u\n", solver->active);
  fprintf ( Abc_FrameGlobalGetOut(), "assigned = %u\n", kissat_assigned (solver));
  fprintf ( Abc_FrameGlobalGetOut(), "unassigned = %u\n", solver->unassigned);
  dump_import (solver);
  dump_export (solver);
#ifdef LOGGING
  if (solver->compacting)
    dump_map (solver);
#endif
  dump_etrail (solver);
  dump_extend (solver);
  dump_trail (solver);
  fprintf ( Abc_FrameGlobalGetOut(), "stable = %u\n", (unsigned) solver->stable);
  if (solver->stable)
    dump_scores (solver);
  else
    dump_queue (solver);
  dump_values (solver);
  fprintf ( Abc_FrameGlobalGetOut(), "binary = %" PRIu64 "\n", solver->statistics_.clauses_binary);
  fprintf ( Abc_FrameGlobalGetOut(), "irredundant = %" PRIu64 "\n",
          solver->statistics_.clauses_irredundant);
  fprintf ( Abc_FrameGlobalGetOut(), "redundant = %" PRIu64 "\n",
          solver->statistics_.clauses_redundant);
  dump_binaries (solver);
  dump_clauses (solver);
  dump_extend (solver);
  return 0;
}

ABC_NAMESPACE_IMPL_END

#else
ABC_NAMESPACE_IMPL_START
int kissat_dump_dummy_to_avoid_warning;
ABC_NAMESPACE_IMPL_END
#endif
