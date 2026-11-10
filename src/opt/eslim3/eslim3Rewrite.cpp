/**CFile****************************************************************

  FileName    [eslim3Rewrite.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM3).]

  Synopsis    [Restructuring with choices, target-aware balancing, and area recovery.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 9, 2026.]

***********************************************************************/

#include "rewrite.h"
#include "aig/gia/giaAig.h"
#include "map/if/if.h"
#include "proof/dch/dch.h"
#include <algorithm>
#include <memory>
ABC_NAMESPACE_IMPL_START
namespace eSLIM3 {
/**Function*************************************************************

  Synopsis    [Returns an improved owned AIG, or null if the original is preferable.]

  Description [The input remains owned by the caller. Native stages use local
  parameters. They are indivisible, so each needs a remaining-time reserve.
  Only a nonincreasing-area result meeting the depth constraint is returned.]

***********************************************************************/
  Gia_Man_t* rewriteWithChoices(Gia_Man_t* original, unsigned target,
      unsigned bound, unsigned attempt, std::chrono::steady_clock::time_point deadline,
      bool area_only) {
    auto remaining = [&]() { return std::chrono::duration<double>(deadline - std::chrono::steady_clock::now()).count(); };
    const double reserve = std::max(2.0, 0.0001 * Gia_ManAndNum(original));
    if (remaining() <= reserve) return nullptr;
    using OwnedGia = std::unique_ptr<Gia_Man_t, decltype(&Gia_ManStop)>;
    OwnedGia best(nullptr, &Gia_ManStop);
    const int original_area = Gia_ManAndNum(original);
    auto preferable = [&](Gia_Man_t* candidate, Gia_Man_t* incumbent) {
      const int area = Gia_ManAndNum(candidate), old_area = Gia_ManAndNum(incumbent);
      const unsigned depth = Gia_ManLevelNum(candidate), old_depth = Gia_ManLevelNum(incumbent);
      if (area > original_area || depth > bound) return false;
      // First reach the requested depth, then minimize area within that
      // constraint. Extra depth reduction must not discard a smaller AIG.
      if (!area_only) {
        if ((depth <= target) != (old_depth <= target)) return depth <= target;
        // If neither candidate reaches the target, keep progress toward it.
        // Area-first tie breaking here can repeatedly discard a shallower
        // graph, even though it stays within the incumbent's area budget.
        if (depth > target && depth != old_depth) return depth < old_depth;
      }
      return area < old_area || (area == old_area && depth < old_depth);
    };
    Gia_Man_t* compressed = Gia_ManCompress2(original, 1, 0);
    if (compressed && preferable(compressed, original)) best.reset(compressed);
    else if (compressed) Gia_ManStop(compressed);
    if (remaining() <= reserve) return best.release();
    Gia_Man_t* source = best ? best.get() : original;
    Dch_Pars_t choices;
    Dch_ManSetDefaultParams(&choices);
    choices.fLightSynth = 1;
    choices.fVerbose = 0;
    OwnedGia expanded(Gia_ManPerformDch(source, &choices), &Gia_ManStop);
    if (!expanded) return best.release();
    if (remaining() <= reserve) return best.release();
    If_Par_t mapping;
    If_ManSetDefaultPars(&mapping);
    // Different cut sizes expose different AIG decompositions. Keep the
    // initial six-input pass, then revisit with four- and five-input cuts.
    static constexpr unsigned cut_sizes[] = {6, 4, 5};
    mapping.nLutSize = cut_sizes[attempt % 3]; mapping.nCutsMax = 8;
    mapping.fDelayOpt = 1; mapping.fTruth = 1; mapping.fCutMin = 1;
    // Area-first mapping explores different decompositions than DC2, while
    // the acceptance check still enforces the caller's absolute depth bound.
    mapping.fArea = area_only;
    mapping.fExpRed = 0; mapping.fVerbose = 0; mapping.fNoDelayWarn = 1;
    // A distant target can make mapping spend area that the acceptance rule
    // cannot allow. Try one level of progress first, then the requested goal.
    // Both use the same choices and retain the better legal intermediate AIG.
    const unsigned current = Gia_ManLevelNum(source);
    unsigned targets[2] = {target, target};
    unsigned attempts = 1;
    if (!area_only && current > target && current - target > 1) {
      targets[0] = current - 1;
      attempts = 2;
    }
    double cleanup_reserve = reserve;
    for (unsigned index = 0; index < attempts && remaining() > cleanup_reserve; ++index) {
      If_Par_t pass_mapping = mapping;
      pass_mapping.DelayTarget = area_only || !targets[index] ? -1.0f : float(targets[index]);
      OwnedGia candidate(Gia_ManPerformMapping(expanded.get(), &pass_mapping), &Gia_ManStop);
      if (!candidate) continue;
      // Recover sharing in a wider support than the local exact-synthesis
      // cuts. This public pass preserves levels and owns its mutable graph.
      if (remaining() > cleanup_reserve) {
        Gia_Man_t* shared = Rsub_ManPerform(candidate.get(), 16, 1, 1, 1, 0);
        if (shared) candidate.reset(shared);
      }
      for (unsigned pass = 0; pass < 3 && remaining() > cleanup_reserve; ++pass) {
        const auto started = std::chrono::steady_clock::now();
        Gia_Man_t* next = Gia_ManDc3(candidate.get(), 1, 0);
        cleanup_reserve = std::max(cleanup_reserve,
            2 * std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count() + 0.01);
        if (!next) break;
        candidate.reset(next);
      }
      if (preferable(candidate.get(), best ? best.get() : original)) best = std::move(candidate);
    }
    return best.release();
  }
}
ABC_NAMESPACE_IMPL_END
