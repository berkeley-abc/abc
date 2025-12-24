#include "global.h"

#include "internal.hpp"
#include "util.hpp"
#include <string>

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

void Internal::recompute_tier () {
  if (!opts.recomputetier)
    return;

  ++stats.tierecomputed;
  const int64_t delta =
      stats.tierecomputed >= 16 ? 1u << 16 : (1u << stats.tierecomputed);
  lim.recompute_tier = stats.conflicts + delta;
  LOG ("rescheduling in %" PRId64 " at %" PRId64 " (conflicts at %" PRId64
       ")",
       delta, lim.recompute_tier, stats.conflicts);
#ifndef CADICAL_NDEBUG
  uint64_t total_used = 0;
  for (auto u : stats.used[stable])
    total_used += u;
  CADICAL_assert (total_used == stats.bump_used[stable]);
#endif

  if (!stats.bump_used[stable]) {
    tier1[stable] = opts.reducetier1glue;
    tier2[stable] = opts.reducetier2glue;
    LOG ("tier1 limit = %d", tier1[stable]);
    LOG ("tier2 limit = %d", tier2[stable]);
    return;
  } else {
    uint64_t accumulated_tier1_limit =
        stats.bump_used[stable] * opts.tier1limit / 100;
    uint64_t accumulated_tier2_limit =
        stats.bump_used[stable] * opts.tier2limit / 100;
    tier1[stable] = 1;
    tier2[stable] = 1;
    uint64_t accumulated_used = stats.used[stable][0];
    size_t glue = 1;
    for (; glue < stats.used[stable].size (); ++glue) {
      const uint64_t u = stats.used[stable][glue];
      accumulated_used += u;
      if (accumulated_used >= accumulated_tier1_limit) {
        tier1[stable] = glue;
        break;
      }
    }
    for (; glue < stats.used[stable].size (); ++glue) {
      const uint64_t u = stats.used[stable][glue];
      accumulated_used += u;
      if (accumulated_used >= accumulated_tier2_limit) {
        tier2[stable] = glue;
        break;
      }
    }
  }

  CADICAL_assert (tier1[stable] > 0);

  CADICAL_assert (tier1[stable]);
  CADICAL_assert (tier2[stable]);

  if (tier1[stable] < opts.tier1minglue) {
    LOG ("tier1 limit of %d is too low, setting %d instead", tier1[stable],
         opts.tier1minglue);
    tier1[stable] = opts.tier1minglue;
  }
  if (tier2[stable] < opts.tier2minglue) {
    LOG ("tier2 limit of %d is too low, setting %d instead", tier2[stable],
         opts.tier2minglue);
    tier2[stable] = opts.tier2minglue;
  }
  if (tier1[stable] >= tier2[stable])
    tier2[stable] = tier1[stable] + 1;
  CADICAL_assert (tier2[stable] > tier1[stable]);

  PHASE ("retiered", stats.tierecomputed,
         "tier1 limit = %d in %s mode, tier2 limit = %d in %s mode",
         tier1[stable], stable ? "stable" : "focused", tier2[stable],
         stable ? "stable" : "focused");
}

void Internal::print_tier_usage_statistics () {
  recompute_tier ();

  for (auto stable : {false, true}) {
    unsigned total_used = 0;
    for (size_t glue = 0; glue < stats.used[stable].size (); ++glue)
      total_used += stats.used[stable][glue];

    const std::string mode = stable ? "stable" : "focused";
    const size_t tier1 = internal->tier1[stable];
    const size_t tier2 = internal->tier2[stable];
    if (tier1 > tier2 && opts.reducetier1glue > opts.reducetier2glue) {
      MSG ("tier1 > tier 2 due to the options, giving up");
      break;
    }
    CADICAL_assert (tier1 <= tier2);
    unsigned prefix, suffix;
    unsigned span = tier2 - tier1 + 1;
    const unsigned max_printed = 5;
    CADICAL_assert (max_printed & 1), CADICAL_assert (max_printed / 2 > 0);
    if (span > max_printed) {
      prefix = tier1 + max_printed / 2 - 1;
      suffix = tier2 - max_printed / 2 + 1;
    } else
      prefix = UINT_MAX, suffix = 0;

    uint64_t accumulated_middle = 0;
    int glue_digits = 1, clauses_digits = 1;
    for (unsigned glue = 0; glue <= stats.used[stable].size (); glue++) {
      if (glue < tier1)
        continue;
      uint64_t used = stats.used[stable][glue];
      int tmp_glue = 0, tmp_clauses = 0;
      if (glue <= prefix || suffix <= glue) {
        tmp_glue = glue;
        tmp_clauses = used;
      } else {
        accumulated_middle += used;
        if (glue + 1 == suffix) {
          tmp_glue = (prefix + 1) + (glue) + 1;
          tmp_clauses = (accumulated_middle);
        }
      }
      if (tmp_glue > glue_digits)
        glue_digits = tmp_glue;
      if (tmp_clauses > clauses_digits)
        clauses_digits = tmp_clauses;
      if (glue == tier2)
        break;
    }

    accumulated_middle = 0;
    uint64_t accumulated = 0;
    std::string output;
    for (unsigned glue = 0; glue <= stats.used[stable].size (); glue++) {
      uint64_t used = stats.used[stable][glue];
      accumulated += used;
      if (glue < tier1)
        continue;
      if (glue <= prefix || suffix <= glue + 1) {
        output += mode + " glue ";
      }
      if (glue <= prefix || suffix <= glue) {
        std::string glue_str = std::to_string (glue);
        output += glue_str;
        output += " used " + std::to_string (used);
        output +=
            " clauses " +
            std::to_string (percent (used, total_used)).substr (0, 5) + "%";
        output += " accumulated " +
                  std::to_string (percent (accumulated, total_used))
                      .substr (0, 5) +
                  "%";
        if (glue == tier1)
          output += " tier1";
        if (glue == tier2)
          output += " tier2";
        MSG ("%s", output.c_str ());
        output.clear ();
      } else {
        accumulated_middle += used;
        if (glue + 1 == suffix) {
          std::string glue_str = std::to_string (prefix + 1) + "-" +
                                 std::to_string (suffix - 1);
          output +=
              glue_str + " used " + std::to_string (accumulated_middle);
          output +=
              " clauses " +
              std::to_string (percent (accumulated_middle, total_used))
                  .substr (0, 5) +
              "%";
          output += " accumulated " +
                    std::to_string (percent (accumulated, total_used))
                        .substr (0, 5) +
                    "%";
          MSG ("%s", output.c_str ());
          output.clear ();
        }
      }
      if (glue == tier2)
        break;
    }

    LINE ();
  }
}
} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END
