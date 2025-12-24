#include "global.h"

#include "internal.hpp"
#include "message.hpp"
#include "util.hpp"

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

inline void Internal::backbone_lrat_for_units (int lit, Clause *reason) {
  if (!lrat)
    return;
  if (level)
    return; // not decision level 0
  LOG ("backbone building chain for units");
  CADICAL_assert (lrat_chain.empty ());
  CADICAL_assert (reason);
  for (auto &reason_lit : *reason) {
    if (lit == reason_lit)
      continue;
    CADICAL_assert (val (reason_lit));
    if (!val (reason_lit))
      continue;
    const int signed_reason_lit = val (reason_lit) * reason_lit;
    int64_t id = unit_id (signed_reason_lit);
    lrat_chain.push_back (id);
  }
  lrat_chain.push_back (reason->id);
}

inline bool Internal::backbone_propagate (int64_t &ticks) {
  require_mode (BACKBONE);
  CADICAL_assert (!unsat);
  START (propagate);
  int64_t before = propagated2 = propagated;
  for (;;) {
    if (propagated2 != trail.size ()) {
      const int lit = -trail[propagated2++];
      LOG ("backbone propagating %d over binary clauses", -lit);
      Watches &ws = watches (lit);
      ticks +=
          1 + cache_lines (ws.size (), sizeof (const_watch_iterator *));
      for (const auto &w : ws) {
        if (!w.binary ())
          continue;
        const signed char b = val (w.blit);
        if (b > 0)
          continue;
        if (b < 0)
          conflict = w.clause; // but continue
        else {
          ticks++;
          build_chain_for_units (w.blit, w.clause, 0);
          backbone_assign (w.blit, w.clause);
          lrat_chain.clear ();
        }
      }
    } else if (!conflict && propagated != trail.size ()) {
      const int lit = -trail[propagated++];
      LOG ("backbone propagating %d over large clauses", -lit);
      Watches &ws = watches (lit);
      const const_watch_iterator eow = ws.end ();
      const_watch_iterator i = ws.begin ();
      ticks += 1 + cache_lines (ws.size (), sizeof (*i));
      watch_iterator j = ws.begin ();
      while (i != eow) {
        const Watch w = *j++ = *i++;
        if (w.binary ())
          continue;
        if (val (w.blit) > 0)
          continue;
        ticks++;
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
          w.clause->pos = k - lits;
          CADICAL_assert (lits + 2 <= k), CADICAL_assert (k <= w.clause->end ());
          if (v > 0)
            j[-1].blit = r;
          else if (!v) {
            LOG (w.clause, "unwatch %d in", r);
            lits[0] = other;
            lits[1] = r;
            *k = lit;
            ticks++;
            watch_literal (r, lit, w.clause);
            j--;
          } else if (!u) {
            ticks++;
            CADICAL_assert (v < 0);
            build_chain_for_units (other, w.clause, 0);
            backbone_assign_any (other, w.clause);
            lrat_chain.clear ();
          } else {
            if (w.clause == ignore) {
              LOG ("ignoring conflict due to clause to vivify");
              continue;
            }
            CADICAL_assert (u < 0);
            CADICAL_assert (v < 0);
            conflict = w.clause;
            break;
          }
        }
      }
      if (j != i) {
        while (i != eow)
          *j++ = *i++;
        ws.resize (j - ws.begin ());
      }
    } else
      break;
  }
  int64_t delta = propagated2 - before;
  stats.propagations.backbone += delta;
  if (conflict)
    LOG (conflict, "conflict");
  STOP (propagate);
  return !conflict;
}

inline void Internal::backbone_propagate2 (int64_t &ticks) {
  require_mode (BACKBONE);
  CADICAL_assert (propagated2 <= trail.size ());
  int64_t before = propagated2;
  while (propagated2 != trail.size ()) {
    const int lit = -trail[propagated2++];
    LOG ("probe propagating %d over binary clauses", -lit);
    Watches &ws = watches (lit);
    ticks += 1 + cache_lines (ws.size (), sizeof (const_watch_iterator *));
    for (const auto &w : ws) {
      if (!w.binary ())
        break;
      const signed char b = val (w.blit);
      if (b > 0)
        continue;
      ticks++;
      if (b < 0) {
        conflict = w.clause; // no need to continue
        break;
      } else {
        CADICAL_assert (lrat_chain.empty ());
        backbone_lrat_for_units (w.blit, w.clause);
        backbone_assign (w.blit, w.clause);
        lrat_chain.clear ();
      }
    }
  }

  int64_t delta = propagated2 - before;
  stats.propagations.backbone += delta;
}

void Internal::schedule_backbone_cands (std::vector<int> &candidates) {

  unsigned not_rescheduled = 0;
  for (auto v : vars) {
    const Flags f = flags (v);
    if (!f.active ())
      continue;
    if (f.backbone0) {
      LOG ("scheduling backbone literal candidate %s", LOGLIT (v));
      candidates.push_back (v);
    } else
      ++not_rescheduled;
    if (f.backbone1) {
      LOG ("scheduling backbone literal candidate %s", LOGLIT (-v));
      candidates.push_back (-v);
    } else
      ++not_rescheduled;
  }

  if (not_rescheduled) {
    for (auto v : vars) {
      const Flags f = flags (v);
      if (!f.active ())
        continue;
      if (!f.backbone0) {
        LOG ("scheduling backbone literal candidate %s", LOGLIT (v));
        candidates.push_back (v);
      }
      if (!f.backbone1) {
        LOG ("scheduling backbone literal candidate %s", LOGLIT (-v));
        candidates.push_back (-v);
      }
    }
  }
  CADICAL_assert (candidates.size () <= 2 * (size_t) max_var);

  VERBOSE (3,
           "backbone schedule %zu backbone candidates in total %f "
           "(rescheduled: %f%%)",
           candidates.size (), percent (candidates.size (), 2 * max_var),
           percent (not_rescheduled, 2 * max_var));
}

int Internal::backbone_analyze (Clause *, int64_t &ticks) {
  CADICAL_assert (conflict);
  CADICAL_assert (conflict->size == 2);
  analyzed.push_back (std::abs (conflict->literals[0]));
  flags (conflict->literals[0]).seen = true;
  analyzed.push_back (std::abs (conflict->literals[1]));
  flags (conflict->literals[1]).seen = true;
  LOG (conflict, "analyzing conflict");
  if (lrat)
    lrat_chain.push_back (conflict->id);
  conflict = nullptr;

  for (auto t = trail.rbegin ();;) {
    CADICAL_assert (t < trail.rend ());
    int lit = *t++;
    LOG ("analyzing %s", LOGLIT (lit));
    if (!flags (lit).seen)
      continue;
    Clause *reason = var (lit).reason;
    LOG (reason, "resolving with reason of %s", LOGLIT (lit));
    CADICAL_assert (reason), CADICAL_assert (reason != decision_reason);
    ++ticks;
    const int other = reason->literals[0] ^ reason->literals[1] ^ lit;
    Flags &f_o = flags (other);
    if (lrat)
      lrat_chain.push_back (reason->id);
    if (!f_o.seen) {
      f_o.seen = true;
      analyzed.push_back (other);
    } else {
      LOG ("backbone UIP %s", LOGLIT (other));
      for (auto lit : analyzed)
        flags (lit).seen = false;
      analyzed.clear ();
      if (lrat)
        reverse (begin (lrat_chain), end (lrat_chain));
      return other;
    }
  }
}

inline void Internal::backbone_unit_reassign (int lit) {
#ifdef LOGGING
  LOG ("reassigning %s to level 0", LOGLIT (lit));
  CADICAL_assert (val (lit) > 0);
  CADICAL_assert (val (-lit) < 0);
#else
  (void) lit;
#endif
  return;
}

inline void Internal::backbone_unit_assign (int lit) {
  LOG ("assigning %s to level 0", LOGLIT (lit));
  require_mode (BACKBONE);
  const int idx = vidx (lit);
  CADICAL_assert (!vals[idx]);
  Var &v = var (idx);
  v.level = 0;                   // required to reuse decisions
  v.trail = (int) trail.size (); // used in 'vivify_better_watch'
  CADICAL_assert ((int) num_assigned < max_var);
  num_assigned++;
  v.reason = 0; // for conflict analysis
  learn_unit_clause (lit);
  lrat_chain.clear ();
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  CADICAL_assert (val (lit) > 0);
  CADICAL_assert (val (-lit) < 0);
  trail.push_back (lit);
  LOG ("backbone assign %d to level 0", lit);
}

inline void Internal::backbone_assign_any (int lit, Clause *reason) {
  require_mode (BACKBONE);
  const int idx = vidx (lit);
  CADICAL_assert (!vals[idx]);
  CADICAL_assert (!flags (idx).eliminated () || !reason);
  CADICAL_assert (reason == decision_reason || !reason || reason->size >= 2);
  Var &v = var (idx);
  v.level = level;               // required to reuse decisions
  v.trail = (int) trail.size (); // used in 'vivify_better_watch'
  CADICAL_assert ((int) num_assigned < max_var);
  num_assigned++;
  v.reason = level ? reason : 0; // for conflict analysis
  if (!level)
    learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  CADICAL_assert (val (lit) > 0);
  CADICAL_assert (val (-lit) < 0);
  trail.push_back (lit);
  LOG (reason, "backbone assign %d", lit);
}

inline void Internal::backbone_assign (int lit, Clause *reason) {
  require_mode (BACKBONE);
  const int idx = vidx (lit);
  CADICAL_assert (!vals[idx]);
  CADICAL_assert (!flags (idx).eliminated () || !reason);
  CADICAL_assert (reason == decision_reason || !reason || reason->size == 2);
  Var &v = var (idx);
  v.level = level;               // required to reuse decisions
  v.trail = (int) trail.size (); // used in 'vivify_better_watch'
  CADICAL_assert ((int) num_assigned < max_var);
  num_assigned++;
  v.reason = level ? reason : 0; // for conflict analysis
  if (!level)
    learn_unit_clause (lit);
  const signed char tmp = sign (lit);
  vals[idx] = tmp;
  vals[-idx] = -tmp;
  CADICAL_assert (val (lit) > 0);
  CADICAL_assert (val (-lit) < 0);
  trail.push_back (lit);
  LOG (reason, "backbone assign %d", lit);
}

void Internal::backbone_decision (int lit) {
  require_mode (BACKBONE);
  CADICAL_assert (propagated2 == trail.size ());
  new_trail_level (lit);
  notify_decision ();
  LOG ("search decide %d", lit);
  backbone_assign (lit, decision_reason);
}

unsigned Internal::compute_backbone_round (std::vector<int> &candidates,
                                           std::vector<int> &units,
                                           const int64_t ticks_limit,
                                           int64_t &ticks,
                                           unsigned inconsistent) {
  CADICAL_assert (!conflict);
  auto p = begin (candidates);
  auto q = p;
  const auto end = std::end (candidates);
  size_t failed = 0;
  ++stats.backbone.rounds;

  LOG (candidates, "candidates: ");
  ticks += 1 + cache_lines (candidates.size (),
                            sizeof (std::vector<int>::iterator *));
  while (p != end) {
    CADICAL_assert (p < end);
    CADICAL_assert (q <= p);
    CADICAL_assert (!conflict);
    const int probe = (*q = *p);
    ++stats.backbone.probes;

    ++p, ++q;
    const signed char v = val (probe);
    if (v > 0) {
      q--;
      LOG ("removing satisfied backbone probe %s", LOGLIT (probe));
      if (probe < 0)
        flags (probe).backbone1 = false;
      else
        flags (probe).backbone0 = false;
      continue;
    }

    if (v < 0) {
      if (var (probe).level)
        LOG ("skipping falsified backbone probe %s", LOGLIT (probe));
      else {
        LOG ("removing root-level falsified backbone probe %s",
             LOGLIT (probe));
        q--;
      }
      continue;
    }
    if (ticks >= ticks_limit)
      break;
    backbone_decision (probe);
    backbone_propagate2 (ticks);
    if (!conflict) {
      LOG (candidates,
           "propagating backbone probe %s successful; candidates:",
           LOGLIT (probe));
      continue;
    }

    ++failed;
    ++stats.backbone.units;
    int uip = backbone_analyze (conflict, ticks);
    backtrack_without_updating_phases (level - 1);
    backbone_unit_assign (uip);
    ++stats.units;
    CADICAL_assert (!conflict);
    if (external->learner)
      external->export_learned_unit_clause (uip);

    backbone_propagate2 (ticks);
    if (conflict) {
      LOG ("propagating backbone forced %s failed", LOGLIT (uip));
      inconsistent = uip;
      // we have to give up on the current conflict
      conflict = nullptr;
      break;
    }
    units.push_back (uip);
  }
  while (p != end)
    *q++ = *p++;
  CADICAL_assert (q <= end);
  candidates.resize (q - begin (candidates));
  LOG (candidates, "candidates: ");

  if (!inconsistent) {
    LOG ("flushing satisfied probe candidates");
    auto p = begin (candidates);
    auto q = p;
    const auto end = std::end (candidates);

    while (p != end) {
      const int probe = (*q++ = *p++);
      const signed char v = val (probe);
      if (v > 0) {
        q--;
        LOG ("removing satisfied backbone probe %s", LOGLIT (probe));
        if (probe < 0)
          flags (probe).backbone1 = false;
        else
          flags (probe).backbone0 = false;
        continue;
      }

      if (v < 0) {
        LOG ("keeping falsified probe %s", LOGLIT (probe));
        continue;
      }
      CADICAL_assert (!v);
      LOG ("keeping unassigned probe %s", LOGLIT (probe));
    }
    candidates.resize (q - begin (candidates));
  }
  LOG (candidates, "candidates after !inconsistent: ");
  if (level)
    backtrack_without_updating_phases ();
  if (!inconsistent && !units.empty ()) {
    for (auto l : units) {
      backbone_unit_reassign (l);
    }
    units.clear ();
    if (!backbone_propagate (ticks)) {
      LOG (conflict, "final repropagation yielded conflict");
      learn_empty_clause ();
    }
  } else {
    if (!backbone_propagate (ticks)) {
      learn_empty_clause ();
    }
  }
  LOG (candidates, "candidates end of loop: ");

  LOG (candidates, "candidates end of backbone_round: ");
  return failed;
}

void Internal::keep_backbone_candidates (
    const std::vector<int> &candidates) {
  size_t remain = 0;
  size_t prioritized = 0;
  for (auto v : candidates) {
    const Flags &f = flags (v);
    if (!f.active ())
      continue;
    ++remain;
    if (v < 0)
      prioritized += f.backbone1;
    else
      prioritized += f.backbone0;
  }
  CADICAL_assert (prioritized <= remain);
  if (!remain) {
#ifndef CADICAL_NDEBUG
    for (auto v : candidates) {
      const Flags &f = flags (v);
      if (!f.active ())
        continue;
      CADICAL_assert (!f.backbone0);
      CADICAL_assert (!f.backbone1);
    }
#endif
    return;
  }
  if (prioritized == remain) {
    LOG ("keeping all remaining backbones");
  } else if (!prioritized) {
    for (auto v : candidates) {
      Flags &f = flags (v);
      if (!f.active ())
        continue;
      ++remain;
      if (v < 0) {
        CADICAL_assert (!f.backbone1);
        f.backbone1 = true;
      } else {
        CADICAL_assert (!f.backbone0);
        f.backbone0 = true;
      }
    }
  }
}

unsigned Internal::compute_backbone () {
  size_t failed = 0;

  int64_t ticks = 0;
  backbone_propagate2 (ticks);
  CADICAL_assert (!conflict);

  std::vector<int> candidates, units;
  unsigned inconsistent = 0;
  CADICAL_assert (!conflict);

  ++stats.backbone.phases;
  schedule_backbone_cands (candidates);

  const size_t max_rounds = opts.backbonemaxrounds;
  size_t round_limit = opts.backbonerounds;
  round_limit *= stats.backbone.phases;
  if (round_limit > max_rounds)
    round_limit = max_rounds;

  SET_EFFORT_LIMIT (totalticks, backbone, false);
  int64_t ticks_limit = totalticks - stats.ticks.backbone;
  PHASE ("backbone", stats.backbone.phases,
         "backbone limit of %" PRId64 " ticks", ticks_limit);
  size_t rounds = 0;
  for (; ++rounds;) {
    if (rounds >= round_limit) {
      LOG ("backround round limit %zu rounds", rounds);
      break;
    }
    if (ticks >= ticks_limit) {
      LOG ("backround round limit %" PRIu64 " ticks", ticks);
      break;
    }
    VERBOSE (3,
             "backbone round %zu of %zu with %" PRId64
             " ticks  (%f %% done) with %zu failed so far",
             rounds, max_rounds, ticks, percent (ticks, ticks_limit),
             failed);
    size_t new_failed = compute_backbone_round (
        candidates, units, ticks_limit, ticks, inconsistent);
    failed += new_failed;
    if (inconsistent)
      break;
    if (candidates.empty ())
      break;
    if (unsat)
      break;
  }

  if (inconsistent && !unsat) {
    LOG ("using forced unit %s by repropagating at level 0",
         LOGLIT (inconsistent));
    backtrack_without_updating_phases ();
    propagate ();
    learn_empty_clause ();
  }
  if (unsat) {
    PHASE ("backbone", stats.backbone.phases,
           "inconsistent binary clauses");
  } else {
    PHASE ("backbone", stats.backbone.phases,
           "found %zu backbone literals %zu round in %" PRId64 " ticks",
           failed, rounds, ticks);
  }

  keep_backbone_candidates (candidates);
  if (level) {
    backtrack_without_updating_phases ();
    if (!backbone_propagate (ticks)) {
      learn_empty_clause ();
    }
  }
  stats.ticks.backbone += ticks;
  return failed;
}

void Internal::binary_clauses_backbone () {
  if (unsat)
    return;
  if (!opts.backbone)
    return;
  if (level)
    backtrack_without_updating_phases ();
  propagated2 = 0; // TODO: why?
  if (!propagate ()) {
    LOG ("propagation after connecting watches in inconsistency");
    learn_empty_clause ();
    return;
  }

  for (auto lit : lits) {
    Watches &w = watches (lit);
    std::stable_partition (begin (w), end (w),
                           [] (Watch w) { return w.binary (); });
  }
  CADICAL_assert (propagated2 <= trail.size ());
  private_steps = true;

  CADICAL_assert (watching ());
  START_SIMPLIFIER (backbone, BACKBONE);
  int failed = compute_backbone ();
  CADICAL_assert (!level);
  private_steps = false;

  report ('k', !failed);
  STOP_SIMPLIFIER (backbone, BACKBONE);
}

} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END
