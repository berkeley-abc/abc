#include "global.h"

#include "internal.hpp"

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

// This function determines the next decision variable on the queue, without
// actually removing it from the decision queue, e.g., calling it multiple
// times without any assignment will return the same result.  This is of
// course used below in 'decide' but also in 'reuse_trail' to determine the
// largest decision level to backtrack to during 'restart' without changing
// the assigned variables (if 'opts.restartreusetrail' is non-zero).

int Internal::next_decision_variable_on_queue () {
  int64_t searched = 0;
  int res = queue.unassigned;
  while (val (res))
    res = link (res).prev, searched++;
  if (searched) {
    stats.searched += searched;
    update_queue_unassigned (res);
  }
  LOG ("next queue decision variable %d bumped %" PRId64 "", res,
       bumped (res));
  return res;
}

// This function determines the best decision with respect to score.
//
int Internal::next_decision_variable_with_best_score () {
  int res = 0;
  for (;;) {
    res = scores.front ();
    if (!val (res))
      break;
    (void) scores.pop_front ();
  }
  LOG ("next decision variable %d with score %g", res, score (res));
  return res;
}

void Internal::start_random_sequence () {
  if (!opts.randec)
    return;

  CADICAL_assert (!stable || opts.randecstable);
  CADICAL_assert (stable || opts.randecfocused);
  CADICAL_assert (!randomized_deciding);

  const uint64_t count = ++stats.randec.random_decision_phases;
  const unsigned length = opts.randeclength * log (count + 10);
  VERBOSE (3,
           "starting random decision sequence "
           "at %" PRId64 " conflicts for %u conflicts",
           stats.conflicts, length);
  randomized_deciding = length;

  const double delta = stats.randec.random_decision_phases *
                       log (stats.randec.random_decision_phases);
  lim.random_decision = stats.conflicts + delta * opts.randecint;
  VERBOSE (3,
           "next random decision sequence "
           "at %" PRId64 " conflicts current conflict: %" PRId64
           " conflicts",
           lim.random_decision, stats.conflicts);
}

int Internal::next_random_decision () {
  CADICAL_assert (max_var);
  if (!opts.randec)
    return 0;
  if (stable && !opts.randecstable)
    return 0;
  if (!stable && !opts.randecfocused)
    return 0;
  if (stats.conflicts < lim.random_decision)
    return 0;
  if (satisfied ())
    return 0;

  if (!randomized_deciding) {
    if (level > (int) assumptions.size () + !!constraint.size ()) {
      LOG ("random decision delayed because too deep");
      return 0;
    }
    start_random_sequence ();
  }
  LOG ("searching for random decision");
  Random random (internal->opts.seed);
  random += stats.decisions;
  ++stats.randec.random_decisions;
  for (;;) {
    int idx = 1 + (random.next () % max_var);
    LOG ("trying lit %s", LOGLIT (idx));
    /*
      // Kissat filters out active literals but we cannot do that because
      // eliminated variables are not actively removed.
    if (!flags (idx).active())
      continue;
    */
    if (val (idx))
      continue;
    return idx;
  }
  CADICAL_assert (false);
#if defined(WIN32) && !defined(__MINGW32__)
  __assume(false);
#else
  __builtin_unreachable ();
#endif
}

int Internal::next_decision_variable () {
  int res = next_random_decision ();
  if (res) {
    LOG ("randomized decision %s", LOGLIT (res));
    return res;
  }
  if (use_scores ())
    return next_decision_variable_with_best_score ();
  else
    return next_decision_variable_on_queue ();
}

/*------------------------------------------------------------------------*/

// Implements phase saving as well using a target phase during
// stabilization unless decision phase is forced to the initial value
// of a phase is forced through the 'phase' option.

int Internal::decide_phase (int idx, bool target) {
  const int initial_phase = opts.phase ? 1 : -1;
  int phase = 0;
  if (force_saved_phase) {
    phase = phases.saved[idx];
    LOG ("trying force_saved_phase, i.e., %d", phase);
  }
  CADICAL_assert (force_saved_phase || !phase);
  if (!phase) {
    phase = phases.forced[idx]; // swapped with opts.forcephase case!
    LOG ("trying forced phase, i.e., %d", phase);
  }
  if (!phase && opts.forcephase) {
    phase = initial_phase;
    LOG ("trying initial phase, i.e., %d", phase);
  }
  if (!phase && target) {
    phase = phases.target[idx];
  }
  if (!phase) {
    // ported from kissat where it does not seem very useful
    if (opts.stubbornIOfocused && opts.rephase == 2)
      switch ((stats.rephased.total >> 1) & 7) {
      case 1:
        phase = initial_phase;
        break;
      case 5: // kissat has 3 but 5 looks better
        phase = -initial_phase;
        break;
      default:
        phase = phases.saved[idx];
        break;
      }
    else
      phase = phases.saved[idx];
  }

  // The following should not be necessary and in some version we had even
  // a hard 'COVER' CADICAL_assertion here to check for this.   Unfortunately it
  // triggered for some users and we could not get to the root cause of
  // 'phase' still not being set here.  The logic for phase and target
  // saving is pretty complex, particularly in combination with local
  // search, and to avoid running in such an issue in the future again, we
  // now use this 'defensive' code here, even though such defensive code is
  // considered bad programming practice.
  //
  if (!phase)
    phase = initial_phase;

  return phase * idx;
}

// The likely phase of an variable used in 'collect' for optimizing
// co-location of clauses likely accessed together during search.

int Internal::likely_phase (int idx) { return decide_phase (idx, false); }

/*------------------------------------------------------------------------*/

// adds new level to control and trail
//
void Internal::new_trail_level (int lit) {
  level++;
  control.push_back (Level (lit, trail.size ()));
}

/*------------------------------------------------------------------------*/

bool Internal::satisfied () {
  if ((size_t) level < assumptions.size () + (!!constraint.size ()))
    return false;
  if (num_assigned < (size_t) max_var)
    return false;
  CADICAL_assert (num_assigned == (size_t) max_var);
  if (propagated < trail.size ())
    return false;
  size_t assigned = num_assigned;
  return (assigned == (size_t) max_var);
}

bool Internal::better_decision (int lit, int other) {
  int lit_idx = abs (lit);
  int other_idx = abs (other);
  if (stable)
    return stab[lit_idx] > stab[other_idx];
  else
    return btab[lit_idx] > btab[other_idx];
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

int Internal::decide () {
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
      notify_decision ();
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

    int decision = ask_decision ();
    if ((size_t) level < assumptions.size () ||
        ((size_t) level == assumptions.size () && constraint.size ())) {
      // Forced backtrack below pseudo decision levels.
      // So one of the two branches above will handle it.
      STOP (decide);
      res = decide (); // STARTS and STOPS profiling
      START (decide);
    } else {
      stats.decisions++;
      if (!decision) {
        int idx = next_decision_variable ();
        const bool target = (opts.target > 1 || (stable && opts.target));
        decision = decide_phase (idx, target);
      }
      search_assume_decision (decision);
    }
  }
  if (res)
    marked_failed = false;
  STOP (decide);
  return res;
}
} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END
