#include "global.h"

#include "internal.hpp"

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

// The idea of warmup is to reuse the strength of CDCL, namely
// propagating, before calling random walk that is not good at
// propagating long chains. Therefore, we propagate (ignoring all conflicts)
// discovered along the way.
// The asignmend is the same as the normal assignment however, it updates
// the target phases so that local search can pick them up later

// specific warmup version with saving of the target.
inline void Internal::warmup_assign (int lit, Clause *reason) {

  CADICAL_assert (level); // no need to learn unit clauses here
  require_mode (SEARCH);

  const int idx = vidx (lit);
  CADICAL_assert (reason != external_reason);
  CADICAL_assert (!vals[idx]);
  CADICAL_assert (!flags (idx).eliminated () || reason == decision_reason);
  CADICAL_assert (!searching_lucky_phases);
  CADICAL_assert (lrat_chain.empty ());
  Var &v = var (idx);
  int lit_level;
  CADICAL_assert (
      !(reason == external_reason &&
        ((size_t) level <= assumptions.size () + (!!constraint.size ()))));
  CADICAL_assert (reason);
  CADICAL_assert (level || reason == decision_reason);
  // we  purely assign in order here
  lit_level = level;

  v.level = lit_level;
  v.trail = trail.size ();
  v.reason = reason;
  CADICAL_assert ((int) num_assigned < max_var);
  CADICAL_assert (num_assigned == trail.size ());
  num_assigned++;
  const signed char tmp = sign (lit);
  phases.saved[idx] = tmp;
  set_val (idx, tmp);
  CADICAL_assert (val (lit) > 0);
  CADICAL_assert (val (-lit) < 0);

  trail.push_back (lit);
#ifdef LOGGING
  if (!lit_level)
    LOG ("root-level unit assign %d @ 0", lit);
  else
    LOG (reason, "search assign %d @ %d", lit, lit_level);
#endif

  CADICAL_assert (watching ());
  const Watches &ws = watches (-lit);
  if (!ws.empty ()) {
    const Watch &w = ws[0];
#ifndef WIN32
    __builtin_prefetch (&w, 0, 1);
#endif
  }
}

void Internal::warmup_propagate_beyond_conflict () {

  CADICAL_assert (!unsat);

  START (propagate);
  CADICAL_assert (!ignore);

  int64_t before = propagated;

  while (propagated != trail.size ()) {

    const int lit = -trail[propagated++];
    LOG ("propagating %d", -lit);
    Watches &ws = watches (lit);

    const const_watch_iterator eow = ws.end ();
    watch_iterator j = ws.begin ();
    const_watch_iterator i = j;

    while (i != eow) {

      const Watch w = *j++ = *i++;
      const signed char b = val (w.blit);

      if (b > 0)
        continue; // blocking literal satisfied

      if (w.binary ()) {

        // In principle we can ignore garbage binary clauses too, but that
        // would require to dereference the clause pointer all the time with
        //
        // if (w.clause->garbage) { j--; continue; } // (*)
        //
        // This is too costly.  It is however necessary to produce correct
        // proof traces if binary clauses are traced to be deleted ('d ...'
        // line) immediately as soon they are marked as garbage.  Actually
        // finding instances where this happens is pretty difficult (six
        // parallel fuzzing jobs in parallel took an hour), but it does
        // occur.  Our strategy to avoid generating incorrect proofs now is
        // to delay tracing the deletion of binary clauses marked as garbage
        // until they are really deleted from memory.  For large clauses
        // this is not necessary since we have to access the clause anyhow.
        //
        // Thanks go to Mathias Fleury, who wanted me to explain why the
        // line '(*)' above was in the code. Removing it actually really
        // improved running times and thus I tried to find concrete
        // instances where this happens (which I found), and then
        // implemented the described fix.

        // Binary clauses are treated separately since they do not require
        // to access the clause at all (only during conflict analysis, and
        // there also only to simplify the code).

        if (b < 0)
          // ignoring conflict
          ++stats.warmup.conflicts;
        else {
          warmup_assign (w.blit, w.clause);
        }

      } else {
        CADICAL_assert (w.clause->size > 2);

        // The cache line with the clause data is forced to be loaded here
        // and thus this first memory access below is the real hot-spot of
        // the solver.  Note, that this check is positive very rarely and
        // thus branch prediction should be almost perfect here.

        if (w.clause->garbage) {
          j--;
          continue;
        }
        literal_iterator lits = w.clause->begin ();
        const int other = lits[0] ^ lits[1] ^ lit;
        const signed char u = val (other);
        if (u > 0)
          j[-1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const literal_iterator middle = lits + w.clause->pos;
          literal_iterator k = middle;
          signed char v = -1;
          int r = 0;
          while (k != end && (v = val (r = *k)) < 0)
            k++;
          if (v < 0) {
            k = lits + 2;
            CADICAL_assert (w.clause->pos <= size);
            while (k != middle && (v = val (r = *k)) < 0)
              k++;
          }

          w.clause->pos = k - lits; // always save position

          CADICAL_assert (lits + 2 <= k), CADICAL_assert (k <= w.clause->end ());

          if (v > 0) {

            // Replacement satisfied, so just replace 'blit'.

            j[-1].blit = r;

          } else if (!v) {

            // Found new unassigned replacement literal to be watched.

            LOG (w.clause, "unwatch %d in", lit);

            lits[0] = other;
            lits[1] = r;
            *k = lit;

            watch_literal (r, lit, w.clause);

            j--; // Drop this watch from the watch list of 'lit'.

          } else if (!u) {

            CADICAL_assert (v < 0);

            // The other watch is unassigned ('!u') and all other literals
            // assigned to false (still 'v < 0'), thus we found a unit.
            //
            build_chain_for_units (other, w.clause, 0);
            warmup_assign (other, w.clause);
          } else {
            CADICAL_assert (u < 0);
            CADICAL_assert (v < 0);

            // ignoring conflict
            ++stats.warmup.conflicts;
          }
        }
      }
    }

    if (j != i) {
      ws.resize (j - ws.begin ());
    }
  }

  CADICAL_assert (propagated == trail.size ());

  stats.warmup.propagated += (trail.size () - before);
  STOP (propagate);
}

int Internal::warmup_decide () {
  CADICAL_assert (!satisfied ());
  START (decide);
  int res = 0;
  if ((size_t) level < assumptions.size ()) {
    const int lit = assumptions[level];
    CADICAL_assert (assumed (lit));
    const signed char tmp = val (lit);
    if (tmp < 0) {
      LOG ("assumption %d falsified", lit);
      res = 20;
    } else if (tmp > 0) {
      LOG ("assumption %d already satisfied", lit);
      new_trail_level (0);
      LOG ("added pseudo decision level");
    } else {
      LOG ("deciding assumption %d", lit);
      search_assume_decision (lit);
    }
  } else if ((size_t) level == assumptions.size () && constraint.size ()) {

    int satisfied_lit = 0;  // The literal satisfying the constrain.
    int unassigned_lit = 0; // Highest score unassigned literal.
    int previous_lit = 0;   // Move satisfied literals to the front.

    const size_t size_constraint = constraint.size ();

#ifndef CADICAL_NDEBUG
    unsigned sum = 0;
    for (auto lit : constraint)
      sum += lit;
#endif
    for (size_t i = 0; i != size_constraint; i++) {

      // Get literal and move 'constraint[i] = constraint[i-1]'.

      int lit = constraint[i];
      constraint[i] = previous_lit;
      previous_lit = lit;

      const signed char tmp = val (lit);
      if (tmp < 0) {
        LOG ("constraint literal %d falsified", lit);
        continue;
      }

      if (tmp > 0) {
        LOG ("constraint literal %d satisfied", lit);
        satisfied_lit = lit;
        break;
      }

      CADICAL_assert (!tmp);
      LOG ("constraint literal %d unassigned", lit);

      if (!unassigned_lit || better_decision (lit, unassigned_lit))
        unassigned_lit = lit;
    }

    if (satisfied_lit) {

      constraint[0] = satisfied_lit; // Move satisfied to the front.

      LOG ("literal %d satisfies constraint and "
           "is implied by assumptions",
           satisfied_lit);

      new_trail_level (0);
      LOG ("added pseudo decision level for constraint");
      notify_decision ();

    } else {

      // Just move all the literals back.  If we found an unsatisfied
      // literal then it will be satisfied (most likely) at the next
      // decision and moved then to the first position.

      if (size_constraint) {

        for (size_t i = 0; i + 1 != size_constraint; i++)
          constraint[i] = constraint[i + 1];

        constraint[size_constraint - 1] = previous_lit;
      }

      if (unassigned_lit) {

        LOG ("deciding %d to satisfy constraint", unassigned_lit);
        search_assume_decision (unassigned_lit);

      } else {

        LOG ("failing constraint");
        unsat_constraint = true;
        res = 20;
      }
    }

#ifndef CADICAL_NDEBUG
    for (auto lit : constraint)
      sum -= lit;
    CADICAL_assert (!sum); // Checksum of literal should not change!
#endif

  } else {
    const bool target = (stable || opts.target == 2);
    stats.warmup.decision++;
    int idx = next_decision_variable ();
    if (flags (idx).eliminated ())
      ++stats.warmup.dummydecision;
    int decision = decide_phase (idx, target);
    new_trail_level (decision);
    warmup_assign (decision, decision_reason);
  }
  if (res)
    marked_failed = false;
  STOP (decide);
  return res;
}

int Internal::warmup () {
  CADICAL_assert (!unsat);
  CADICAL_assert (!level);
  if (!opts.warmup)
    return 0;
  require_mode (WALK);
  START (warmup);
  ++stats.warmup.count;
  int res = 0;

#ifndef CADICAL_QUIET
  const int64_t warmup_propagated = stats.warmup.propagated;
  const int64_t decision = stats.warmup.decision;
  const int64_t dummydecision = stats.warmup.dummydecision;
#endif
  // first propagate assumptions in case we find a conflict.  One
  // subtle thing, if we find a conflict in the assumption, then we
  // actually do need the notifications. Otherwise, we there should be
  // no notification at all (not even the `backtrack ()` at the end).
  const size_t assms_contraint_level =
      assumptions.size () + !constraint.empty ();
  while (!res && (size_t) level < assms_contraint_level &&
         num_assigned < (size_t) max_var) {
    CADICAL_assert (num_assigned < (size_t) max_var);
    res = warmup_decide ();
    warmup_propagate_beyond_conflict ();
  }
  const bool no_backtrack_notification = (level == 0);

  // now we do not need any notification and can simply propagate
  CADICAL_assert (propagated == trail.size ());
  CADICAL_assert (!private_steps);
  private_steps = true;

  LOG ("propagating beyond conflicts to warm-up walk");
  while (!res && num_assigned < (size_t) max_var) {
    CADICAL_assert (propagated == trail.size ());
    res = warmup_decide ();
    warmup_propagate_beyond_conflict ();
    LOG (lrat_chain, "during warmup with lrat chain:");
  }
  CADICAL_assert (res || num_assigned == (size_t) max_var);
#ifndef CADICAL_QUIET
  // constrains with empty levels break this
  // CADICAL_assert (res || stats.warmup.propagated - warmup_propagated ==
  // (int64_t)num_assigned);
  VERBOSE (3,
           "warming-up needed %" PRIu64 " propagations including %" PRIu64
           " decisions (with %" PRIu64 " dummy ones)",
           stats.warmup.propagated - warmup_propagated,
           stats.warmup.decision - decision,
           stats.warmup.dummydecision - dummydecision);
#endif

  // now we backtrack, notifying only if there was something to
  // notify.
  private_steps = no_backtrack_notification;
  if (!res)
    backtrack_without_updating_phases ();
  private_steps = false;
  STOP (warmup);
  require_mode (WALK);
  return res;
}

} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END
