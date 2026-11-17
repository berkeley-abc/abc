/**CFile****************************************************************

  FileName    [eslim2LutRewrite.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM2).]

  Synopsis    [Owned LUT restructuring with explicit area and depth bounds.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 16, 2026.]

***********************************************************************/

#include "rewrite.h"
#include "eslim2CirMan.h"
#include "aig/aig/aig.h"
#include "map/if/if.h"
#include "opt/sfm/sfm.h"
#include "proof/dch/dch.h"
#include <algorithm>
#include <memory>

ABC_NAMESPACE_IMPL_START
namespace eSLIM2 {
/**Function*************************************************************

  Synopsis    [Returns an improved LUT circuit, or an empty circuit on no gain.]

  Description [Only the supplied circuit's duplicate is exported: export may
  simplify repeated fanins. Mapping and SAT sweeping use owned ABC networks.
  Both intermediate mappings and swept results are checked in the internal
  cost model, which absorbs buffers and complemented output connections.]

***********************************************************************/
  eSLIM2CirMan rewriteLutWithChoices(const eSLIM2CirMan& original, unsigned lut_size,
      unsigned target, unsigned bound, unsigned attempt,
      std::chrono::steady_clock::time_point deadline, bool area_only) {
    auto remaining = [&]() {
      return std::chrono::duration<double>(deadline - std::chrono::steady_clock::now()).count();
    };
    const double reserve = std::max(2.0, 0.0005 * original.getNofGates());
    eSLIM2CirMan best(0);
    if (remaining() <= reserve || lut_size < 2 || lut_size > 6) return best;
    using OwnedNtk = std::unique_ptr<Abc_Ntk_t, decltype(&Abc_NtkDelete)>;
    auto exported = original.duplicate();
    OwnedNtk network(exported.eSLIM2CirManToNtk(), &Abc_NtkDelete);
    if (!network) return best;
    OwnedNtk aig(Abc_NtkStrash(network.get(), 0, 1, 0), &Abc_NtkDelete);
    if (!aig || remaining() <= reserve) return best;
    network.reset();
    Dch_Pars_t choices;
    Dch_ManSetDefaultParams(&choices);
    choices.fVerbose = 0;
    // Alternate the synthesis effort without changing the mapping width.
    choices.fLightSynth = attempt % 2;
    OwnedNtk expanded(Abc_NtkDch(aig.get(), &choices), &Abc_NtkDelete);
    if (!expanded || remaining() <= reserve) return best;
    aig.reset();
    auto consider = [&](Abc_Ntk_t* candidate) {
      if (!candidate || Abc_NtkGetFaninMax(candidate) > int(lut_size) ||
          !Abc_NtkToSop(candidate, -1, ABC_INFINITY)) return;
      eSLIM2CirMan circuit(candidate, true);
      const eSLIM2CirMan& incumbent = best.getNofObjs() > 1 ? best : original;
      const unsigned depth = circuit.getDepth(), old_depth = incumbent.getDepth();
      const int area = circuit.getNofGates(), old_area = incumbent.getNofGates();
      if (area > original.getNofGates() || depth > bound) return;
      bool preferable = area < old_area || (area == old_area && depth < old_depth);
      if (!area_only) {
        if ((depth <= target) != (old_depth <= target)) preferable = depth <= target;
        else if (depth > target && depth != old_depth) preferable = depth < old_depth;
      }
      if (preferable) best = std::move(circuit);
    };
    If_Par_t mapping;
    If_ManSetDefaultPars(&mapping);
    mapping.nLutSize = lut_size;
    mapping.nCutsMax = 16;
    mapping.nFlowIters = 2;
    mapping.nAreaIters = 3;
    mapping.fArea = area_only;
    mapping.fNoDelayWarn = 1;
    // As in the if command, choices require disabling structural cut
    // expansion: a choice cut need not cover the representative's cone.
    if (Abc_NtkGetChoiceNum(expanded.get())) mapping.fExpRed = 0;
    // Output objects contribute one level in the internal representation.
    mapping.DelayTarget = target ? float(target - 1) : 0;
    OwnedNtk mapped(Abc_NtkIf(expanded.get(), &mapping), &Abc_NtkDelete);
    consider(mapped.get());
    if (mapped && remaining() > reserve) {
      Sfm_Par_t sweeping;
      Sfm_ParSetDefault(&sweeping);
      if (Abc_NtkPerformMfs(mapped.get(), &sweeping)) consider(mapped.get());
    }
    return best;
  }
}
ABC_NAMESPACE_IMPL_END
