#include "global.h"

#include "internal.hpp"
#include <cstdint>

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Random walk local search based on 'ProbSAT' ideas.
struct Tagged {
  bool binary : 1;
  unsigned counter_pos : 31;
#ifndef CADICAL_NDEBUG
  Clause *c;
#endif
  explicit Tagged () { CADICAL_assert (false); }
  explicit Tagged (Clause *d, unsigned pos)
      : binary (d->size == 2), counter_pos (pos) {
    CADICAL_assert ((pos & (1 << 31)) == 0);
#ifndef CADICAL_NDEBUG
    c = d;
#endif
  }
};

struct Counter {
  unsigned count; // number of false literals
  unsigned pos;   // pos in the broken clauses
  Clause *clause; // pointer to the clause itself
  explicit Counter (unsigned c, unsigned p, Clause *d)
      : count (c), pos (p), clause (d) {}
  explicit Counter (unsigned c, Clause *d)
      : count (c), pos (UINT32_MAX), clause (d) {}
};

struct WalkerFO {

  Internal *internal;

  // for efficiency, storing the model each time an improvement is
  // found is too costly. Instead we store some of the flips since
  // last time and the position of the best model found so far.
  Random random;         // local random number generator
  int64_t ticks;         // ticks to approximate run time
  int64_t limit;         // limit on number of propagations
  vector<Tagged> broken; // currently unsatisfied clauses
  double epsilon;        // smallest considered score
  vector<double> table;  // break value to score table
  vector<double> scores; // scores of candidate literals
  std::vector<int>
      flips; // remember the flips compared to the last best saved model
  int best_trail_pos;
  int64_t minimum = INT64_MAX;
  std::vector<signed char> best_values; // best model found so far
  double score (unsigned);              // compute score from break count

  std::vector<Counter> tclauses;
  std::vector<std::vector<Tagged>> tcounters;

  using TOccs = std::vector<Tagged>;
  TOccs &occs (int lit) {
    const int idx = internal->vlit (lit);
    CADICAL_assert ((size_t) idx < tcounters.size ());
    return tcounters[idx];
  }
  const TOccs &occs (int lit) const {
    const int idx = internal->vlit (lit);
    CADICAL_assert ((size_t) idx < tcounters.size ());
    return tcounters[idx];
  }
  void connect_clause (int lit, Clause *clause, unsigned pos) {
    CADICAL_assert (pos < tclauses.size ());
    CADICAL_assert (tclauses[pos].clause == clause);
    LOG (clause, "connecting clause on %d with already in occurrences %zu",
         lit, occs (lit).size ());
    occs (lit).push_back (Tagged (clause, pos));
  }
  void connect_clause (Clause *clause, unsigned pos) {
    CADICAL_assert (pos < tclauses.size ());
    CADICAL_assert (tclauses[pos].clause == clause);
    for (auto lit : *clause)
      connect_clause (lit, clause, pos);
  }

  void check_occs () const {
#ifndef CADICAL_NDEBUG
    for (auto lit : internal->lits) {
      for (auto w : occs (lit)) {
        CADICAL_assert (w.counter_pos < tclauses.size ());
      }
    }

    unsigned unsatisfied = 0;
    for (auto c : tclauses) {
      unsigned count = 0;
      LOG (c.clause, "checking clause with counter %d:", c.count);
      for (auto lit : *c.clause) {
        if (internal->val (lit) > 0)
          ++count;
      }
      CADICAL_assert (count == c.count);
      if (!count)
        ++unsatisfied;
    }
    CADICAL_assert (broken.size () == unsatisfied);
#endif
  }
  void check_broken () const {
#ifndef CADICAL_NDEBUG
    for (size_t i = 0; i < broken.size (); ++i) {
      const Tagged t = broken[i];
      CADICAL_assert (t.c);
      CADICAL_assert (t.counter_pos < tclauses.size ());
      CADICAL_assert (tclauses[t.counter_pos].clause == t.c);
      for (auto lit : *t.c) {
        CADICAL_assert (internal->val (lit) < 0);
      }
    }
#endif
  }

  void check_all () const {
    check_broken ();
    check_occs ();
  }

  static const uint32_t invalid_position = UINT32_MAX;
  void make_clause (Tagged t);

  WalkerFO (Internal *, double size, int64_t limit);
  void push_flipped (int flipped);
  void save_walker_trail (bool);
  void save_final_minimum (int64_t old_minimum);
  void make_clauses_along_occurrences (int lit);
  void make_clauses_along_unsatisfied (int lit);
  void make_clauses (int lit);
  void break_clauses (int lit);
  unsigned walk_full_occs_pick_clause ();
  void walk_full_occs_flip_lit (int lit);
  int walk_full_occs_pick_lit (Clause *);
  unsigned walk_full_occs_break_value (int lit);
};

// These are in essence the CB values from Adrian Balint's thesis.  They
// denote the inverse 'cb' of the base 'b' of the (probability) weight
// 'b^-i' for picking a literal with the break value 'i' (first column is
// the 'size', second the 'CB' value).

static double cbvals[][2] = {
    {0.0, 2.00}, {3.0, 2.50}, {4.0, 2.85}, {5.0, 3.70},
    {6.0, 5.10}, {7.0, 7.40}, // Adrian has '5.4', but '7.4' looks better.
};

static const int ncbvals = sizeof cbvals / sizeof cbvals[0];

// We interpolate the CB values for uniform random SAT formula to the non
// integer situation of average clause size by piecewise linear functions.
//
//   y2 - y1
//   ------- * (x - x1) + y1
//   x2 - x1
//
// where 'x' is the average size of clauses and 'y' the CB value.

inline static double fitcbval (double size) {
  int i = 0;
  while (i + 2 < ncbvals &&
         (cbvals[i][0] > size || cbvals[i + 1][0] < size))
    i++;
  const double x2 = cbvals[i + 1][0], x1 = cbvals[i][0];
  const double y2 = cbvals[i + 1][1], y1 = cbvals[i][1];
  const double dx = x2 - x1, dy = y2 - y1;
  CADICAL_assert (dx);
  const double res = dy * (size - x1) / dx + y1;
  CADICAL_assert (res > 0);
  return res;
}

// Initialize the data structures for one local search round.

WalkerFO::WalkerFO (Internal *i, double size, int64_t l)
    : internal (i), random (internal->opts.seed), // global random seed
      ticks (0), limit (l), best_trail_pos (-1) {
  random += internal->stats.walk.count; // different seed every time
  flips.reserve (i->max_var / 4);
  best_values.resize (i->max_var + 1, 0);
  tcounters.resize (i->max_var * 2 + 2);

  // This is the magic constant in ProbSAT (also called 'CB'), which we pick
  // according to the average size every second invocation and otherwise
  // just the default '2.0', which turns into the base '0.5'.
  //
  const bool use_size_based_cb = (internal->stats.walk.count & 1);
  const double cb = use_size_based_cb ? fitcbval (size) : 2.0;
  CADICAL_assert (cb);
  const double base = 1 / cb; // scores are 'base^0,base^1,base^2,...

  double next = 1;
  for (epsilon = next; next; next = epsilon * base)
    table.push_back (epsilon = next);

  PHASE ("walk", internal->stats.walk.count,
         "CB %.2f with inverse %.2f as base and table size %zd", cb, base,
         table.size ());
}

// Add the literal to flip to the queue

void WalkerFO::push_flipped (int flipped) {
  LOG ("push literal %s on the flips", LOGLIT (flipped));
  CADICAL_assert (flipped);
  if (best_trail_pos < 0) {
    LOG ("not pushing flipped %s to already invalid trail",
         LOGLIT (flipped));
    return;
  }

  const size_t size_trail = flips.size ();
  const size_t limit = internal->max_var / 4 + 1;
  if (size_trail < limit) {
    flips.push_back (flipped);
    LOG ("pushed flipped %s to trail which now has size %zd",
         LOGLIT (flipped), size_trail + 1);
    return;
  }

  if (best_trail_pos) {
    LOG ("trail reached limit %zd but has best position %d", limit,
         best_trail_pos);
    save_walker_trail (true);
    flips.push_back (flipped);
    LOG ("pushed flipped %s to trail which now has size %zu",
         LOGLIT (flipped), flips.size ());
    return;
  } else {
    LOG ("trail reached limit %zd without best position", limit);
    flips.clear ();
    LOG ("not pushing %s to invalidated trail", LOGLIT (flipped));
    best_trail_pos = -1;
    LOG ("best trail position becomes invalid");
  }
}

void WalkerFO::save_walker_trail (bool keep) {
  CADICAL_assert (best_trail_pos != -1);
  CADICAL_assert ((size_t) best_trail_pos <= flips.size ());
#ifdef LOGGING
  const size_t size_trail = flips.size ();
#endif
  const int kept = flips.size () - best_trail_pos;
  LOG ("saving %d values of flipped literals on trail of size %zd",
       best_trail_pos, size_trail);

  const auto begin = flips.begin ();
  const auto best = flips.begin () + best_trail_pos;
  const auto end = flips.end ();

  auto it = begin;
  for (; it != best; ++it) {
    const int lit = *it;
    CADICAL_assert (lit);
    const signed char value = sign (lit);
    const int idx = std::abs (lit);
    best_values[idx] = value;
  }
  if (!keep) {
    LOG ("no need to shift and keep remaining %u literals", kept);
    return;
  }

#ifndef CADICAL_NDEBUG
  for (auto v : internal->vars) {
    if (internal->active (v))
      CADICAL_assert (best_values[v] == internal->phases.saved[v]);
  }
#endif
  LOG ("flushed %u literals %.0f%% from trail", best_trail_pos,
       percent (best_trail_pos, size_trail));
  CADICAL_assert (it == best);
  auto jt = begin;
  for (; it != end; ++it, ++jt) {
    CADICAL_assert (jt <= it);
    CADICAL_assert (it < end);
    *jt = *it;
  }

  CADICAL_assert ((int) (end - jt) == best_trail_pos);
  CADICAL_assert ((int) (jt - begin) == kept);
  flips.resize (kept);
  LOG ("keeping %u literals %.0f%% on trail", kept,
       percent (kept, size_trail));
  LOG ("reset best trail position to 0");
  best_trail_pos = 0;
}

// finally export_ the final minimum
void WalkerFO::save_final_minimum (int64_t old_init_minimum) {
  CADICAL_assert (minimum <= old_init_minimum);
#ifdef CADICAL_NDEBUG
  (void) old_init_minimum;
#endif

  if (!best_trail_pos || best_trail_pos == -1)
    LOG ("minimum already saved");
  else
    save_walker_trail (false);

  ++internal->stats.walk.improved;
  for (auto v : internal->vars) {
    if (best_values[v])
      internal->phases.saved[v] = best_values[v];
    else
      CADICAL_assert (!internal->active (v));
  }
  internal->copy_phases (internal->phases.prev);
}
// The scores are tabulated for faster computation (to avoid 'pow').

inline double WalkerFO::score (unsigned i) {
  const double res = (i < table.size () ? table[i] : epsilon);
  LOG ("break %u mapped to score %g", i, res);
  return res;
}

/*------------------------------------------------------------------------*/

unsigned WalkerFO::walk_full_occs_pick_clause () {
  internal->require_mode (internal->WALK);
  CADICAL_assert (!broken.empty ());
  int64_t size = broken.size ();
  if (size > INT_MAX)
    size = INT_MAX;
  int pos = random.pick_int (0, size - 1);
  unsigned res = broken[pos].counter_pos;
  LOG (tclauses[res].clause, "picking random position %d", pos);
  return res;
}

/*------------------------------------------------------------------------*/

// Compute the number of clauses which would be become unsatisfied if 'lit'
// is flipped and set to false.  This is called the 'break-count' of 'lit'.

unsigned WalkerFO::walk_full_occs_break_value (int lit) {

  internal->require_mode (internal->WALK);
  CADICAL_assert (internal->val (lit) > 0);
  START (walkbreak);

  const uint64_t old = ticks;
  unsigned res = 0; // The computed break-count of 'lit'.
  ticks +=
      (1 + internal->cache_lines (occs (lit).size (), sizeof (Clause *)));

  for (const auto &w : occs (lit)) {
    const unsigned ref = w.counter_pos;
    CADICAL_assert (ref < tclauses.size ());
    res += (tclauses[ref].count == 1);
  }

  internal->stats.ticks.walkbreak += ticks - old;
  STOP (walkbreak);
  return res;
}

/*------------------------------------------------------------------------*/

// Given an unsatisfied clause 'c', in which we want to flip a literal, we
// first determine the exponential score based on the break-count of its
// literals and then sample the literals based on these scores.  The CB
// value is smaller than one and thus the score is exponentially decreasing
// with the break-count increasing.  The sampling works as in 'ProbSAT' and
// 'YalSAT' by summing up the scores and then picking a random limit in the
// range of zero to the sum, then summing up the scores again and picking
// the first literal which reaches the limit.  Note, that during incremental
// SAT solving we can not flip assumed variables.  Those are assigned at
// decision level one, while the other variables are assigned at two.

int WalkerFO::walk_full_occs_pick_lit (Clause *c) {
  START (walkpick);
  LOG ("picking literal by break-count");
  CADICAL_assert (scores.empty ());
  const int64_t old = ++ticks;
  double sum = 0;
  int64_t propagations = 0;
  for (const auto lit : *c) {
    CADICAL_assert (internal->active (lit));
    if (internal->var (lit).level == 1) {
      LOG ("skipping assumption %d for scoring", -lit);
      continue;
    }
    propagations++;
    unsigned tmp = walk_full_occs_break_value (-lit);
    double score = this->score (tmp);
    LOG ("literal %d break-count %u score %g", lit, tmp, score);
    scores.push_back (score);
    sum += score;
  }
  (void) propagations; // TODO unused?
  LOG ("scored %zd literals", scores.size ());
  CADICAL_assert (!scores.empty ());
  CADICAL_assert (this->scores.size () <= (size_t) c->size);
  const double lim = sum * random.generate_double ();
  LOG ("score sum %g limit %g", sum, lim);

  const auto end = c->end ();
  auto i = c->begin ();
  auto j = scores.begin ();
  int res;
  for (;;) {
    CADICAL_assert (i != end);
    res = *i++;
    if (internal->var (res).level > 1)
      break;
    LOG ("skipping assumption %d without score", -res);
  }
  sum = *j++;
  while (sum <= lim && i != end) {
    res = *i++;
    if (internal->var (res).level == 1) {
      LOG ("skipping assumption %d without score", -res);
      continue;
    }
    sum += *j++;
  }
  scores.clear ();
  LOG ("picking literal %d by break-count", res);
  internal->stats.ticks.walkpick += ticks - old;
  STOP (walkpick);
  return res;
}

/*------------------------------------------------------------------------*/
void WalkerFO::make_clause (Tagged t) {
  CADICAL_assert (t.counter_pos < tclauses.size ());
  // TODO invalidate position in 'unsatisfied'
  auto count = tclauses[t.counter_pos].count++;
  if (count) {
    LOG (tclauses[t.counter_pos].clause,
         "already made with counter %d at position %d",
         tclauses[t.counter_pos].count, tclauses[t.counter_pos].pos);
    CADICAL_assert (tclauses[t.counter_pos].clause == t.c);
    CADICAL_assert (tclauses[t.counter_pos].pos == WalkerFO::invalid_position);
    return;
  }
  LOG (tclauses[t.counter_pos].clause,
       "make with counter %d at position %d", tclauses[t.counter_pos].count,
       tclauses[t.counter_pos].pos);
  CADICAL_assert (tclauses[t.counter_pos].pos != WalkerFO::invalid_position);
  CADICAL_assert (tclauses[t.counter_pos].pos < broken.size ());
  ++ticks;
  auto last = broken.back ();
#ifndef CADICAL_NDEBUG
  CADICAL_assert (tclauses[t.counter_pos].clause == t.c);
  CADICAL_assert (last.counter_pos < tclauses.size ());
  CADICAL_assert (tclauses[last.counter_pos].clause == last.c);
#endif
  unsigned pos = tclauses[t.counter_pos].pos;
  CADICAL_assert (pos < broken.size ());
  broken[pos] = last;
  // the order is important
  tclauses[last.counter_pos].pos = pos;
  tclauses[t.counter_pos].pos = WalkerFO::invalid_position;
  broken.pop_back ();
}

void WalkerFO::make_clauses_along_occurrences (int lit) {
  const auto &occs = this->occs (lit);
  LOG ("making clauses with %s along %zu occurrences", LOGLIT (lit),
       occs.size ());
  CADICAL_assert (internal->val (lit) > 0);
  size_t made = 0;
  ticks += (1 + internal->cache_lines (occs.size (), sizeof (Clause *)));

  for (auto c : occs) {
#if 0
    // only works if make is after break... but we don't want that
    if (broken.empty()) {
      LOG ("early abort: satisfiable!");
      return;
    }
#endif
    this->make_clause (c);
    made++;
  }
  LOG ("made %zu clauses by flipping %d, still %zu broken", made, lit,
       broken.size ());
  LOG ("made %zu clauses with flipped %s", made, LOGLIT (lit));
  (void) made;
}

void WalkerFO::make_clauses_along_unsatisfied (int lit) {
  LOG ("making clauses with %s along %zu unsatisfied", LOGLIT (lit),
       this->broken.size ());
  CADICAL_assert (internal->val (lit) > 0);
  size_t made = 0;
  // TODO flush made clauses from 'unsatisfied' directly.
  // TODO 'stats.make_visited++', 'made++' appropriately.
  size_t j = 0;
  const size_t size = this->broken.size ();
  ticks +=
      (1 + internal->cache_lines (this->broken.size (), sizeof (Clause *)));
  for (size_t i = 0, j = 0; i < size; ++i) {
    CADICAL_assert (i >= j);
    const auto &c = this->broken[i];
    Counter &d = this->tclauses[c.counter_pos];
    this->broken[j++] = this->broken[i];
    CADICAL_assert (d.pos != WalkerFO::invalid_position);
    for (auto other : *d.clause) {
      if (lit == other) {
        ++made;
        --j;
        ++d.count;
        LOG (d.clause, "made with count %d", d.count);
        d.pos = WalkerFO::invalid_position;
        break;
      }
    }
    if (d.pos != WalkerFO::invalid_position)
      LOG (d.clause, "still broken");
    CADICAL_assert (made + j == i + 1); // assertions holds after incrementing 'i'
  }
  CADICAL_assert (j <= size);
  this->broken.resize (j);
  LOG ("made %zu clauses with flipped %s", made, LOGLIT (lit));
  (void) made;
}

void WalkerFO::make_clauses (int lit) {
  START (walkflipWL);
  const int64_t old = ticks;
  // In babywalk this work because there are not counter
  // if (this->occs(lit).size() > broken.size())
  //   make_clauses_along_unsatisfied(lit);
  // else
  make_clauses_along_occurrences (lit);
  internal->stats.ticks.walkflipWL += ticks - old;
  STOP (walkflipWL);
}

void WalkerFO::break_clauses (int lit) {
  START (walkflipbroken);
  const int64_t old = ticks;
  LOG ("breaking clauses on %s", LOGLIT (lit));
  // Finally add all new unsatisfied (broken) clauses.

#ifdef LOGGING
  int64_t broken = 0;
#endif
  const WalkerFO::TOccs &ws = occs (lit);
  ticks += (1 + internal->cache_lines (ws.size (), sizeof (Clause *)));

  LOG ("trying to break %zd clauses", ws.size ());

  for (const auto &w : ws) {
    unsigned pos = w.counter_pos;
    Counter &d = tclauses[pos];
#ifndef CADICAL_NDEBUG
    LOG (d.clause, "trying to break");
#endif
    if (--d.count)
      continue;
    d.pos = this->broken.size ();
    ++ticks;
    this->broken.push_back (w);
#ifdef LOGGING
    broken++;
#endif
  }
  LOG ("broken %" PRId64 " clauses by flipping %d", broken, lit);
  internal->stats.ticks.walkflipbroken += ticks - old;
  STOP (walkflipbroken);
}

void WalkerFO::walk_full_occs_flip_lit (int lit) {

  internal->require_mode (internal->WALK);
  LOG ("flipping assign %d", lit);
  CADICAL_assert (internal->val (lit) < 0);
  const int64_t old = ticks;

  // First flip the literal value.
  //
  const int tmp = sign (lit);
  const int idx = abs (lit);
  internal->set_val (idx, tmp);
  CADICAL_assert (internal->val (lit) > 0);

  make_clauses (lit);
  break_clauses (-lit);

  if (!broken.empty ())
    check_all ();
  internal->stats.ticks.walkflip += ticks - old;
}

/*------------------------------------------------------------------------*/

// Check whether to save the current phases as new global minimum.

inline void Internal::walk_full_occs_save_minimum (WalkerFO &walker) {
  int64_t broken = walker.broken.size ();
  if (broken >= walker.minimum)
    return;
  if (broken <= stats.walk.minimum) {
    stats.walk.minimum = broken;
    VERBOSE (3, "new global minimum %" PRId64 "", broken);
  } else {
    VERBOSE (3, "new walk minimum %" PRId64 "", broken);
  }

  walker.minimum = broken;

#ifndef CADICAL_NDEBUG
  for (auto i : vars) {
    const signed char tmp = vals[i];
    if (tmp)
      phases.saved[i] = tmp;
  }
#endif

  if (walker.best_trail_pos == -1) {
    for (auto i : vars) {
      const signed char tmp = vals[i];
      if (tmp) {
        walker.best_values[i] = tmp;
#ifndef CADICAL_NDEBUG
        CADICAL_assert (tmp == phases.saved[i]);
#endif
      }
    }
    walker.best_trail_pos = 0;
  } else {
    walker.best_trail_pos = walker.flips.size ();
    LOG ("new best trail position %u", walker.best_trail_pos);
  }
}

/*------------------------------------------------------------------------*/

int Internal::walk_full_occs_round (int64_t limit, bool prev) {

  stats.walk.count++;

  reset_watches ();

  // Remove all fixed variables first (assigned at decision level zero).
  //
  if (last.collect.fixed < stats.all.fixed)
    garbage_collection ();

#ifndef CADICAL_QUIET
  // We want to see more messages during initial local search.
  //
  if (localsearching) {
    CADICAL_assert (!force_phase_messages);
    force_phase_messages = true;
  }
#endif

  PHASE ("walk", stats.walk.count,
         "random walk limit of %" PRId64 " propagations", limit);

  // First compute the average clause size for picking the CB constant.
  //
  double size = 0;
  int64_t n = 0;
  for (const auto c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant) {
      if (!opts.walkredundant)
        continue;
      if (!likely_to_be_kept_clause (c))
        continue;
    }
    size += c->size;
    n++;
  }
  double average_size = relative (size, n);

  PHASE ("walk", stats.walk.count,
         "%" PRId64 " clauses average size %.2f over %d variables", n,
         average_size, active ());

  // Instantiate data structures for this local search round.
  //
  WalkerFO walker (internal, average_size, limit);

  bool failed = false; // Inconsistent assumptions?

  level = 1; // Assumed variables assigned at level 1.

  if (assumptions.empty ()) {
    LOG ("no assumptions so assigning all variables to decision phase");
  } else {
    LOG ("assigning assumptions to their forced phase first");
    for (const auto lit : assumptions) {
      signed char tmp = val (lit);
      if (tmp > 0)
        continue;
      if (tmp < 0) {
        LOG ("inconsistent assumption %d", lit);
        failed = true;
        break;
      }
      if (!active (lit))
        continue;
      tmp = sign (lit);
      const int idx = abs (lit);
      LOG ("initial assign %d to assumption phase", tmp < 0 ? -idx : idx);
      set_val (idx, tmp);
      CADICAL_assert (level == 1);
      var (idx).level = 1;
    }
    if (!failed)
      LOG ("now assigning remaining variables to their decision phase");
  }

  level = 2; // All other non assumed variables assigned at level 2.

  if (!failed) {

    const bool target = opts.warmup ? false : stable || opts.target == 2;
    for (auto idx : vars) {
      if (!active (idx)) {
        LOG ("skipping inactive variable %d", idx);
        continue;
      }
      if (vals[idx]) {
        CADICAL_assert (var (idx).level == 1);
        LOG ("skipping assumed variable %d", idx);
        continue;
      }
      int tmp = 0;
      if (prev)
        tmp = phases.prev[idx];
      if (!tmp)
        tmp = sign (decide_phase (idx, target));
      CADICAL_assert (tmp == 1 || tmp == -1);
      set_val (idx, tmp);
      CADICAL_assert (level == 2);
      var (idx).level = 2;
      walker.best_values[idx] = tmp;
      LOG ("initial assign %d to decision phase", tmp < 0 ? -idx : idx);
    }

    LOG ("watching satisfied and registering broken clauses");
#ifdef LOGGING
    int64_t watched = 0;
#endif
    for (const auto c : clauses) {

      if (c->garbage)
        continue;
      if (c->redundant) {
        if (!opts.walkredundant)
          continue;
        if (!likely_to_be_kept_clause (c))
          continue;
      }

      bool satisfiable = false; // contains not only assumptions
      int satisfied = 0;        // clause satisfied?

      int *lits = c->literals;
      const int size = c->size;

      // Move to front satisfied literals and determine whether there
      // is at least one (non-assumed) literal that can be flipped.
      //
      for (int i = 0; i < size; i++) {
        const int lit = lits[i];
        CADICAL_assert (active (lit)); // Due to garbage collection.
        if (val (lit) > 0) {
          swap (lits[satisfied], lits[i]);
          if (!satisfied++)
            LOG ("first satisfying literal %d", lit);
        } else if (!satisfiable && var (lit).level > 1) {
          LOG ("non-assumption potentially satisfying literal %d", lit);
          satisfiable = true;
        }
      }

      if (!satisfied && !satisfiable) {
        LOG (c, "due to assumptions unsatisfiable");
        LOG ("stopping local search since assumptions falsify a clause");
        failed = true;
        break;
      }

      unsigned pos = walker.tclauses.size ();
      walker.tclauses.push_back (Counter (satisfied, c));
      walker.connect_clause (c, pos);

      if (!satisfied) {
        CADICAL_assert (satisfiable); // at least one non-assumed variable ...
        LOG (c, "broken");
        walker.tclauses[pos].pos = walker.broken.size ();
        walker.broken.push_back (Tagged (c, pos));
      } else {
#ifdef LOGGING
        watched++; // to be able to compare the number with walk
#endif
      }
    }
#ifdef LOGGING
    if (!failed) {
      int64_t broken = walker.broken.size ();
      int64_t total = watched + broken;
      MSG ("watching %" PRId64 " clauses %.0f%% "
           "out of %" PRId64 " (watched and broken)",
           watched, percent (watched, total), total);
    }
#endif
  }
  walker.check_all ();
  int res; // Tells caller to continue with local search.

  if (!failed) {

    int64_t broken = walker.broken.size ();
    int64_t initial_minimum = broken;

    PHASE ("walk", stats.walk.count,
           "starting with %" PRId64 " unsatisfied clauses "
           "(%.0f%% out of %" PRId64 ")",
           broken, percent (broken, stats.current.irredundant),
           stats.current.irredundant);

    walk_full_occs_save_minimum (walker);
    CADICAL_assert (stats.walk.minimum <= walker.minimum);

    int64_t minimum = broken;
#ifndef CADICAL_QUIET
    int64_t flips = 0;
#endif
    while (!terminated_asynchronously () && !walker.broken.empty () &&
           walker.ticks < walker.limit) {
#ifndef CADICAL_QUIET
      flips++;
#endif
      stats.walk.flips++;
      stats.walk.broken += broken;
      unsigned pos = walker.walk_full_occs_pick_clause ();
      Clause *c = walker.tclauses[pos].clause;
      const int lit = walker.walk_full_occs_pick_lit (c);
      walker.walk_full_occs_flip_lit (lit);
      walker.push_flipped (lit);
      broken = walker.broken.size ();
      LOG ("now have %" PRId64 " broken clauses in total", broken);
      if (broken >= minimum)
        continue;
      minimum = broken;
      VERBOSE (3, "new phase minimum %" PRId64 " after %" PRId64 " flips",
               minimum, flips);
      walk_full_occs_save_minimum (walker);
    }

    walker.save_final_minimum (initial_minimum);
#ifndef CADICAL_QUIET
    if (minimum == initial_minimum) {
      PHASE ("walk", internal->stats.walk.count,
             "%sno improvement %" PRId64 "%s in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             tout.bright_yellow_code (), minimum, tout.normal_code (),
             flips, walker.ticks);
    } else {
      PHASE ("walk", internal->stats.walk.count,
             "best phase minimum %" PRId64 " in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             minimum, flips, walker.ticks);
    }
#endif

    if (opts.profile >= 2) {
      PHASE ("walk", stats.walk.count, "%.2f million ticks per second",
             1e-6 *
                 relative (walker.ticks, time () - profiles.walk.started));

      PHASE ("walk", stats.walk.count, "%.2f thousand flips per second",
             relative (1e-3 * flips, time () - profiles.walk.started));

    } else {
      PHASE ("walk", stats.walk.count, "%.2f ticks", 1e-6 * walker.ticks);

      PHASE ("walk", stats.walk.count, "%.2f thousand flips", 1e-3 * flips);
    }

    if (minimum > 0) {
      LOG ("minimum %" PRId64 " non-zero thus potentially continue",
           minimum);
      res = 0;
    } else {
      LOG ("minimum is zero thus stop local search");
      res = 10;
    }

  } else {

    res = 20;

    PHASE ("walk", stats.walk.count,
           "aborted due to inconsistent assumptions");
  }

  for (auto idx : vars)
    if (active (idx))
      set_val (idx, 0);

  CADICAL_assert (level == 2);
  level = 0;

  init_watches ();
  connect_watches ();

#ifndef CADICAL_QUIET
  if (localsearching) {
    CADICAL_assert (force_phase_messages);
    force_phase_messages = false;
  }
#endif
  stats.ticks.walk += walker.ticks;
  return res;
}

void Internal::walk_full_occs () {
  START_INNER_WALK ();

  backtrack ();
  if (propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after root level propagation");
    learn_empty_clause ();
    STOP_INNER_WALK ();
    return;
  }

  int res = 0;
  if (opts.warmup)
    res = warmup ();
  if (res) {
    LOG ("stopping walk due to warmup");
    STOP_INNER_WALK ();
    return;
  }
  const int64_t ticks = stats.ticks.search[0] + stats.ticks.search[1];
  int64_t limit = ticks - last.walk.ticks;
  VERBOSE (2,
           "walk scheduling: last %" PRId64 " current %" PRId64
           " delta %" PRId64,
           last.walk.ticks, ticks, limit);
  last.walk.ticks = ticks;
  limit *= 1e-3 * opts.walkeffort;
  if (limit < opts.walkmineff)
    limit = opts.walkmineff;
  // local search is very cache friendly, so we actually really go over a
  // lot of ticks
  if (limit > 1e3 * opts.walkmaxeff) {
    MSG ("reached maximum efficiency %" PRId64, limit);
    limit = 1e3 * opts.walkmaxeff;
  }
  (void) walk_full_occs_round (limit, false);
  STOP_INNER_WALK ();
  CADICAL_assert (!unsat);
}

} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END
