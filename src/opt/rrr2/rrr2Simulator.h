/**HFile****************************************************************

  FileName    [rrr2Simulator.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Experimental redundancy removal and resubstitution.]

  Synopsis    [Redundancy analysis and optimization: Simulator.]

  Author      [Yukio Miyasaka]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 1, 2026.]

  Description [Derived from the rrr package. The original command is unchanged.]

***********************************************************************/

#pragma once

#include <algorithm>
#include <random>
#include <bitset>

#include "rrr2Parameter.h"
#include "rrr2Utils.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace rrr2 {

  template <typename Ntk>
  class Simulator {
  private:
    // aliases
    using word = unsigned long long;
    using itr = std::vector<word>::iterator;
    using citr = std::vector<word>::const_iterator;
    static constexpr word one = 0xffffffffffffffff;
    static constexpr bool fKeepStimula = true;

    // pointer to network
    Ntk *pNtk;

    // parameters
    int nVerbose;
    int nWords;

    // data
    bool fGenerated;
    bool fInitialized;
    int target; // node for which the careset has been computed
    std::vector<word> vValues;
    std::vector<word> vValues2; // simulation with an inverter
    std::vector<word> care; // careset
    std::vector<word> tmp;

    // Cached topological cone; scratch rows hold the original simulation values.
    int coneTarget = -1;
    std::vector<int> vCareCone;
    std::vector<int> vCareOutputs;
    std::vector<unsigned char> vCareMarks;
    int scoreTarget = -1;
    std::vector<word> vScoreOn;
    std::vector<std::vector<word>> vScoreObligations;

    // partial cex
    int iPivot;
    std::vector<word> vAssignedStimuli;

    // updates
    bool fUpdate;
    std::set<int> sUpdates;

    // backups
    std::vector<Simulator> vBackups;

    // stats
    int nCex;
    int nDiscarded;
    int nPackedCountOld;
    std::vector<int> vPackedCount;
    std::vector<int> vPackedCountEvicted;
    double durationSimulation;
    double durationCare;

    // vector computations
    void Clear(int n, itr x) const;
    void Fill(int n, itr x) const;
    void Copy(int n, itr dst, citr src, bool c) const;
    void And(int n, itr dst, citr src0, citr src1, bool c0, bool c1) const;
    void Xor(int n, itr dst, citr src0, citr src1, bool c) const;
    bool IsZero(int n, citr x) const;
    bool IsEq(int n, citr x, citr y) const;
    void Print(int n, citr x) const;

    // callback
    void ActionCallback(Action const &action);

    // simulation
    void SimulateNode(std::vector<word> &v, int id, int to_negate = -1);
    bool ResimulateNode(std::vector<word> &v, int id, int to_negate = -1);
    void SimulateOneWordNode(std::vector<word> &v, int id, int offset, int to_negate = -1);
    void Simulate();
    void Resimulate();
    void SimulateOneWord(int offset);

    // generate stimuli
    void GenerateRandomStimuli();

    // careset computation
    void PrepareCareCone();
    void ComputeCareWords(int offset, int count);
    void ComputeCare(int id);

    // preparation
    void Initialize();

    // save & load
    void Save(int slot);
    void Load(int slot);

  public:
    // constructors
    Simulator();
    Simulator(Parameter const *pPar);
    void AssignNetwork(Ntk *pNtk_, bool fReuse);

    // checks
    bool CheckRedundancy(int id, int idx);
    bool CheckFeasibility(int id, int fi, bool c);
    int CandidateScore(int id, int fi);

    // cex
    void AddCex(std::vector<VarValue> const &vCex);

    // summary
    void ResetSummary();
    summary<int> GetStatsSummary() const;
    summary<double> GetTimesSummary() const;
  };


  // {{{ Vector computations

  template <typename Ntk>
  inline void Simulator<Ntk>::Clear(int n, itr x) const {
    std::fill(x, x + n, 0);
  }

  template <typename Ntk>
  inline void Simulator<Ntk>::Fill(int n, itr x) const {
    std::fill(x, x + n, one);
  }

  template <typename Ntk>
  inline void Simulator<Ntk>::Copy(int n, itr dst, citr src, bool c) const {
    if(!c) {
      for(int i = 0; i < n; i++, dst++, src++) {
        *dst = *src;
      }
    } else {
      for(int i = 0; i < n; i++, dst++, src++) {
        *dst = ~*src;
      }
    }
  }

  template <typename Ntk>
  inline void Simulator<Ntk>::And(int n, itr dst, citr src0, citr src1, bool c0, bool c1) const {
    if(!c0) {
      if(!c1) {
        for(int i = 0; i < n; i++, dst++, src0++, src1++) {
          *dst = *src0 & *src1;
        }
      } else {
        for(int i = 0; i < n; i++, dst++, src0++, src1++) {
          *dst = *src0 & ~*src1;
        }
      }
    } else {
      if(!c1) {
        for(int i = 0; i < n; i++, dst++, src0++, src1++) {
          *dst = ~*src0 & *src1;
        }
      } else {
        for(int i = 0; i < n; i++, dst++, src0++, src1++) {
          *dst = ~*src0 & ~*src1;
        }
      }
    }
  }

  template <typename Ntk>
  inline void Simulator<Ntk>::Xor(int n, itr dst, citr src0, citr src1, bool c) const {
    if(!c) {
      for(int i = 0; i < n; i++, dst++, src0++, src1++) {
        *dst = *src0 ^ *src1;
      }
    } else {
      for(int i = 0; i < n; i++, dst++, src0++, src1++) {
        *dst = *src0 ^ ~*src1;
      }
    }
  }

  template <typename Ntk>
  inline bool Simulator<Ntk>::IsZero(int n, citr x) const {
    for(int i = 0; i < n; i++, x++) {
      if(*x) {
        return false;
      }
    }
    return true;
  }

  template <typename Ntk>
  inline bool Simulator<Ntk>::IsEq(int n, citr x, citr y) const {
    for(int i = 0; i < n; i++, x++, y++) {
      if(*x != *y) {
        return false;
      }
    }
    return true;
  }

  template <typename Ntk>
  inline void Simulator<Ntk>::Print(int n, citr x) const {
    std::cout << std::bitset<64>(*x);
    x++;
    for(int i = 1; i < n; i++, x++) {
      std::cout << std::endl << std::string(10, ' ') << std::bitset<64>(*x);
    }
  }

  // }}}

  // {{{ Callback

  template <typename Ntk>
  void Simulator<Ntk>::ActionCallback(Action const &action) {
    if(action.type != SAVE && action.type != SORT_FANINS) {
      scoreTarget = -1;
    }
    // Fanin sorting and saving do not change reachability. All other actions
    // conservatively discard the cone, including restoration of a snapshot.
    if(action.type != SAVE && action.type != SORT_FANINS) {
      coneTarget = -1;
    }
    switch(action.type) {
    case REMOVE_FANIN:
      assert(fInitialized);
      if(target != -1) {
        if(action.id == target) {
          fUpdate = true;
        } else {
          sUpdates.insert(action.id);
        }
      }
      break;
    case REMOVE_UNUSED:
      break;
    case REMOVE_BUFFER:
    case REMOVE_CONST:
      if(fInitialized) {
        if(target != -1) {
          if(action.id == target) {
            if(fUpdate) {
              for(int fo: action.vFanouts) {
                sUpdates.insert(fo);
              }
              fUpdate = false;
            }
            target = -1;
          } else {
            if(sUpdates.count(action.id)) {
              sUpdates.erase(action.id);
              for(int fo: action.vFanouts) {
                sUpdates.insert(fo);
              }
            }
          }
        }
      }
      break;
    case ADD_FANIN:
      assert(fInitialized);
      if(target != -1) {
        if(action.id == target) {
          fUpdate = true;
        } else {
          sUpdates.insert(action.id);
        }
      }
      break;
    case TRIVIAL_COLLAPSE:
      break;
    case TRIVIAL_DECOMPOSE:
      if(fInitialized) {
        // Saving or restoring a snapshot can clear the target while keeping
        // the reference simulation initialized. New nodes still need rows.
        vValues.resize(nWords * pNtk->GetNumNodes());
        SimulateNode(vValues, action.fi);
        // Time of this simulation is not measured for simplicity.
      }
      break;
    case SORT_FANINS:
      break;
    case READ:
      fInitialized = false;
      if(action.fNew) {
        fGenerated = false;
      }
      break;
    case SAVE:
      Save(action.idx);
      break;
    case LOAD:
      Load(action.idx);
      break;
    case POP_BACK:
      // Do nothing: it may be good to keep the word vector allocated
      break;
    default:
      assert(0);
    }
  }

  // }}}

  // {{{ Simulation

  template <typename Ntk>
  void Simulator<Ntk>::SimulateNode(std::vector<word> &v, int id, int to_negate) {
    itr x = v.end();
    itr y = v.begin() + id * nWords;
    bool cx = false;
    switch(pNtk->GetNodeType(id)) {
    case AND:
      pNtk->ForEachFanin(id, [&](int fi, bool c) {
        if(x == v.end()) {
          x = v.begin() + fi * nWords;
          cx = c ^ (fi == to_negate);
        } else {
          And(nWords, y, x, v.begin() + fi * nWords, cx, c ^ (fi == to_negate));
          x = y;
          cx = false;
        }
      });
      if(x == v.end()) {
        Fill(nWords, y);
      }
      break;
    default:
      assert(0);
    }
  }

  template <typename Ntk>
  bool Simulator<Ntk>::ResimulateNode(std::vector<word> &v, int id, int to_negate) {
    itr x = v.end();
    bool cx = false;
    switch(pNtk->GetNodeType(id)) {
    case AND:
      pNtk->ForEachFanin(id, [&](int fi, bool c) {
        if(x == v.end()) {
          x = v.begin() + fi * nWords;
          cx = c ^ (fi == to_negate);
        } else {
          And(nWords, tmp.begin(), x, v.begin() + fi * nWords, cx, c ^ (fi == to_negate));
          x = tmp.begin();
          cx = false;
        }
      });
      if(x == v.end()) {
        Fill(nWords, tmp.begin());
      }
      break;
    default:
      assert(0);
    }
    itr y = v.begin() + id * nWords;
    if(IsEq(nWords, y, tmp.begin())) {
      return false;
    }
    Copy(nWords, y, tmp.begin(), false);
    return true;
  }

  template <typename Ntk>
  void Simulator<Ntk>::SimulateOneWordNode(std::vector<word> &v, int id, int offset, int to_negate) {
    itr x = v.end();
    itr y = v.begin() + id * nWords + offset;
    bool cx = false;
    switch(pNtk->GetNodeType(id)) {
    case AND:
      pNtk->ForEachFanin(id, [&](int fi, bool c) {
        if(x == v.end()) {
          x = v.begin() + fi * nWords + offset;
          cx = c ^ (fi == to_negate);
        } else {
          And(1, y, x, v.begin() + fi * nWords + offset, cx, c ^ (fi == to_negate));
          x = y;
          cx = false;
        }
      });
      if(x == v.end()) {
        Fill(1, y);
      }
      break;
    default:
      assert(0);
    }
  }

  template <typename Ntk>
  void Simulator<Ntk>::Simulate() {
    time_point timeStart = GetCurrentTime();
    if(nVerbose) {
      std::cout << "simulating" << std::endl;
    }
    pNtk->ForEachInt([&](int id) {
      SimulateNode(vValues, id);
      if(nVerbose) {
        std::cout << "node " << std::setw(3) << id << ": ";
        Print(nWords, vValues.begin() + id * nWords);
        std::cout << std::endl;
      }
    });
    durationSimulation += Duration(timeStart, GetCurrentTime());
  }

  template <typename Ntk>
  void Simulator<Ntk>::Resimulate() {
    time_point timeStart = GetCurrentTime();
    if(nVerbose) {
      std::cout << "resimulating" << std::endl;
    }
    pNtk->ForEachTfosUpdate(sUpdates, false, [&](int fo) {
      bool fUpdated = ResimulateNode(vValues, fo);
      if(nVerbose) {
        std::cout << "node " << std::setw(3) << fo << ": ";
        Print(nWords, vValues.begin() + fo * nWords);
        std::cout << std::endl;
      }
      return fUpdated;
    });
    //  alternative version that updates entire TFO
//     pNtk->ForEachTfos(sUpdates, false, [&](int fo) {
//       SimulateNode(vValues, fo);
//       if(nVerbose) {
//         std::cout << "node " << std::setw(3) << fo << ": ";
//         Print(nWords, vValues.begin() + fo * nWords);
//         std::cout << std::endl;
//       }
//     });
//
    durationSimulation += Duration(timeStart, GetCurrentTime());
  }

  template <typename Ntk>
  void Simulator<Ntk>::SimulateOneWord(int offset) {
    time_point timeStart = GetCurrentTime();
    if(nVerbose) {
      std::cout << "simulating word " << offset << std::endl;
    }
    pNtk->ForEachInt([&](int id) {
      SimulateOneWordNode(vValues, id, offset);
      if(nVerbose) {
        std::cout << "node " << std::setw(3) << id << ": ";
        Print(1, vValues.begin() + id * nWords + offset);
        std::cout << std::endl;
      }
    });
    durationSimulation += Duration(timeStart, GetCurrentTime());
  }

  // }}}

  // {{{ Generate stimuli

  template <typename Ntk>
  void Simulator<Ntk>::GenerateRandomStimuli() {
    if(nVerbose) {
      std::cout << "generating random stimuli" << std::endl;
    }
    std::mt19937_64 rng;
    pNtk->ForEachPi([&](int id) {
      for(int i = 0; i < nWords; i++) {
        vValues[id * nWords + i] = rng();
      }
      if(nVerbose) {
        std::cout << "node " << std::setw(3) << id << ": ";
        Print(nWords, vValues.begin() + id * nWords);
        std::cout << std::endl;
      }
    });
    Clear(nWords * pNtk->GetNumPis(), vAssignedStimuli.begin());
  }

  // }}}

  // {{{ Careset computation

  /**Function*************************************************************

    Synopsis    [Caches the affected nodes and output drivers for this target.]

    Description [Structural callbacks invalidate the cache. The traversal order
    is the same as in the original simulator and requires no input-count bound.]

  ***********************************************************************/
  template <typename Ntk>
  void Simulator<Ntk>::PrepareCareCone() {
    if(coneTarget == target) {
      return;
    }
    vCareCone.clear();
    vCareOutputs.clear();
    vCareMarks.assign(pNtk->GetNumNodes(), 0);
    pNtk->ForEachTfo(target, false, [&](int id) {
      vCareCone.push_back(id);
      vCareMarks[id] = 1;
    });
    pNtk->ForEachPoDriver([&](int fi) {
      if(vCareMarks[fi]) {
        vCareOutputs.push_back(fi);
      }
    });
    coneTarget = target;
  }

  /**Function*************************************************************

    Synopsis    [Simulates and restores only the complemented fanout cone.]

    Description [Each row is saved before being overwritten. All affected rows
    are restored before returning, so the reference simulation remains valid.
    The one-word path is used when a counterexample updates a packed pattern.]

  ***********************************************************************/
  template <typename Ntk>
  void Simulator<Ntk>::ComputeCareWords(int offset, int count) {
    PrepareCareCone();
    vValues2.resize(vValues.size());
    for(int id: vCareCone) {
      int index = id * nWords + offset;
      Copy(count, vValues2.begin() + index, vValues.begin() + index, false);
      if(count == nWords) {
        SimulateNode(vValues, id, target);
      } else {
        assert(count == 1);
        SimulateOneWordNode(vValues, id, offset, target);
      }
      if(nVerbose) {
        std::cout << "node " << std::setw(3) << id << ": ";
        Print(count, vValues.begin() + index);
        std::cout << std::endl;
      }
    }
    Clear(count, care.begin() + offset);
    for(int fi: vCareOutputs) {
      for(int i = offset; i < offset + count; i++) {
        care[i] |= vValues[fi * nWords + i] ^ vValues2[fi * nWords + i];
      }
    }
    for(int id: vCareCone) {
      int index = id * nWords + offset;
      Copy(count, vValues.begin() + index, vValues2.begin() + index, false);
    }
  }

  template <typename Ntk>
  void Simulator<Ntk>::ComputeCare(int id) {
    if(sUpdates.empty() && id == target) {
      return;
    }
    if(fUpdate) {
      sUpdates.insert(target);
      fUpdate = false;
    }
    if(!sUpdates.empty()) {
      Resimulate();
      sUpdates.clear();
    }
    target = id;
    time_point timeStart = GetCurrentTime();
    if(nVerbose) {
      std::cout << "computing careset of " << target << std::endl;
    }
    if(pNtk->IsPoDriver(target)) {
      Fill(nWords, care.begin());
      if(nVerbose) {
        std::cout << "care " << std::setw(3) << target << ": ";
        Print(nWords, care.begin());
        std::cout << std::endl;
      }
      durationCare += Duration(timeStart, GetCurrentTime());
      return;
    }
    ComputeCareWords(0, nWords);
    if(nVerbose) {
      std::cout << "care " << std::setw(3) << target << ": ";
      Print(nWords, care.begin());
      std::cout << std::endl;
    }
    durationCare += Duration(timeStart, GetCurrentTime());
  }

  // }}}

  // {{{ Preparation

  template <typename Ntk>
  void Simulator<Ntk>::Initialize() {
    if(!fGenerated) {
      // TODO: reset nWords to default here maybe, if such a mechanism that changes nWords has been implemneted
      vValues.resize(nWords * pNtk->GetNumNodes());
      iPivot = 0;
      vAssignedStimuli.clear();
      vAssignedStimuli.resize(nWords * pNtk->GetNumPis());
      for(int count: vPackedCount) {
        if(count) {
          vPackedCountEvicted.push_back(count);
        }
      }
      vPackedCount.clear();
      vPackedCount.resize(nWords * 64);
      GenerateRandomStimuli();
      fGenerated = true;
    } else {
      // use same nWords as we are reusing patterns even if nWords has changed
      vValues.resize(nWords * pNtk->GetNumNodes());
    }
    Simulate();
    fInitialized = true;
  }

  // }}}

  // {{{ Save & load

  template <typename Ntk>
  void Simulator<Ntk>::Save(int slot) {
    assert(slot >= 0);
    assert(!check_int_max(slot));
    if(slot >= int_size(vBackups)) {
      vBackups.resize(slot + 1);
    }
    vBackups[slot].nWords = nWords;
    if(sUpdates.empty()) {
      vBackups[slot].target = target;
      vBackups[slot].care = care;
    } else {
      vBackups[slot].target = -1;
      vBackups[slot].care = care;
    }
    if(fUpdate) {
      sUpdates.insert(target);
      fUpdate = false;
    }
    if(!sUpdates.empty()) {
      Resimulate();
      sUpdates.clear();
    }
    vBackups[slot].vValues = vValues;
    vBackups[slot].iPivot = iPivot;
    vBackups[slot].vAssignedStimuli = vAssignedStimuli;
    target = vBackups[slot].target; // assigned to -1 when careset needs updating
    if(!fKeepStimula) {
      vBackups[slot].nCex = nCex;
      vBackups[slot].nPackedCountOld = nPackedCountOld;
      vBackups[slot].vPackedCount = vPackedCount;
      vBackups[slot].vPackedCountEvicted = vPackedCountEvicted;
    }
  }

  template <typename Ntk>
  void Simulator<Ntk>::Load(int slot) {
    assert(slot >= 0);
    assert(slot < int_size(vBackups));
    fUpdate = false;
    sUpdates.clear();
    if(!fKeepStimula) {
      nWords  = vBackups[slot].nWords;
      target  = vBackups[slot].target;
      vValues = vBackups[slot].vValues;
      care    = vBackups[slot].care;
      iPivot  = vBackups[slot].iPivot;
      vAssignedStimuli = vBackups[slot].vAssignedStimuli;
      nDiscarded += nCex - vBackups[slot].nCex;
      nCex = vBackups[slot].nCex;
      nPackedCountOld = vBackups[slot].nPackedCountOld;
      vPackedCount = vBackups[slot].vPackedCount;
      vPackedCountEvicted = vBackups[slot].vPackedCountEvicted;
      tmp.resize(nWords);
    } else {
      std::vector<int> vOffsets;
      for(int i = 0; i < vBackups[slot].nWords; i++) {
        bool fDifferent = false;
        pNtk->ForEachPi([&](int id) {
          // Compare with the snapshot, not with the current row itself.
          if(vBackups[slot].vValues[id * vBackups[slot].nWords + i] != vValues[id * nWords + i]) {
            fDifferent = true;
          }
        });
        if(fDifferent) {
          vOffsets.push_back(i);
        }
      }
      if(nWords == vBackups[slot].nWords) {
        if(vOffsets.empty()) {
          target  = vBackups[slot].target;
          vValues = vBackups[slot].vValues;
          care    = vBackups[slot].care;
        } else {
          target = -1;
          std::vector<std::vector<word>> vInputStimuli(pNtk->GetNumPis());
          pNtk->ForEachPiIdx([&](int idx, int id) {
            vInputStimuli[idx].resize(nWords);
            Copy(nWords, vInputStimuli[idx].begin(), vValues.begin() + id * nWords, false);
          });
          vValues = vBackups[slot].vValues;
          pNtk->ForEachPiIdx([&](int idx, int id) {
            Copy(nWords, vValues.begin() + id * nWords, vInputStimuli[idx].begin(), false);
          });
          for(int i: vOffsets) {
            SimulateOneWord(i);
          }
        }
      } else {
        // TODO: when nWords has changed
        assert(0);
      }
    }
  }

  // }}}

  // {{{ Constructors

  template <typename Ntk>
  Simulator<Ntk>::Simulator() :
    pNtk(NULL),
    nVerbose(0),
    nWords(0),
    fGenerated(false),
    fInitialized(false),
    target(-1),
    iPivot(0),
    fUpdate(false) {
    ResetSummary();
  }

  template <typename Ntk>
  Simulator<Ntk>::Simulator(Parameter const *pPar) :
    pNtk(NULL),
    nVerbose(pPar->nSimulatorVerbose),
    nWords(pPar->nWords),
    fGenerated(false),
    fInitialized(false),
    target(-1),
    iPivot(0),
    fUpdate(false) {
    care.resize(nWords);
    tmp.resize(nWords);
    ResetSummary();
  }

  template <typename Ntk>
  void Simulator<Ntk>::AssignNetwork(Ntk *pNtk_, bool fReuse) {
    scoreTarget = -1;
    if(!fReuse) {
      fGenerated = false;
    }
    fInitialized = false;
    target = -1;
    coneTarget = -1;
    fUpdate = false;
    sUpdates.clear();
    pNtk = pNtk_;
    pNtk->AddCallback(std::bind(&Simulator<Ntk>::ActionCallback, this, std::placeholders::_1));
  }

  // }}}

  // {{{ Checks

  /**Function*************************************************************

    Synopsis    [Rejects a removal as soon as one simulated word witnesses it.]

    Description [Combines the care mask and fanin values without intermediate
    whole-vector products. A passing simulation still requires a SAT proof.]

  ***********************************************************************/
  template <typename Ntk>
  bool Simulator<Ntk>::CheckRedundancy(int id, int idx) {
    if(!fInitialized) {
      Initialize();
    }
    ComputeCare(id);
    assert(pNtk->GetNodeType(id) == AND);
    int fi = pNtk->GetFanin(id, idx);
    bool c = pNtk->GetCompl(id, idx);
    for(int i = 0; i < nWords; i++) {
      word witness = care[i] & (c ? vValues[fi * nWords + i] : ~vValues[fi * nWords + i]);
      for(int k = 0; witness && k < pNtk->GetNumFanins(id); k++) {
        if(k == idx) {
          continue;
        }
        word value = vValues[pNtk->GetFanin(id, k) * nWords + i];
        witness &= pNtk->GetCompl(id, k) ? ~value : value;
      }
      if(witness) {
        return false;
      }
    }
    return true;
  }

  /**Function*************************************************************

    Synopsis    [Rejects an addition as soon as one simulated word witnesses it.]

    Description [Recomputes the target product because its stored simulation
    may be intentionally stale after a fanin edit to the current target.]

  ***********************************************************************/
  template <typename Ntk>
  bool Simulator<Ntk>::CheckFeasibility(int id, int fi, bool c) {
    if(!fInitialized) {
      Initialize();
    }
    ComputeCare(id);
    assert(pNtk->GetNodeType(id) == AND);
    for(int i = 0; i < nWords; i++) {
      word witness = care[i] & (c ? vValues[fi * nWords + i] : ~vValues[fi * nWords + i]);
      for(int k = 0; witness && k < pNtk->GetNumFanins(id); k++) {
        word value = vValues[pNtk->GetFanin(id, k) * nWords + i];
        witness &= pNtk->GetCompl(id, k) ? ~value : value;
      }
      if(witness) {
        return false;
      }
    }
    return true;
  }

  // }}}

  // {{{ Cex

  /**Function*************************************************************

    Synopsis    [Ranks candidates by feasible phases and possible removals.]

    Description [The score only guides search. SAT still proves every edit.
    Prefix and suffix products form all removal obligations in linear time.]

  ***********************************************************************/
  template <typename Ntk>
  int Simulator<Ntk>::CandidateScore(int id, int fi) {
    if(!fInitialized) {
      Initialize();
    }
    ComputeCare(id);
    if(scoreTarget != id) {
      int n = pNtk->GetNumFanins(id);
      vScoreOn.assign(nWords, 0);
      vScoreObligations.assign(n, std::vector<word>(nWords));
      std::vector<word> prefix(n + 1), suffix(n + 1), values(n);
      for(int i = 0; i < nWords; i++) {
        prefix[0] = suffix[n] = one;
        for(int k = 0; k < n; k++) {
          values[k] = vValues[pNtk->GetFanin(id, k) * nWords + i];
          if(pNtk->GetCompl(id, k)) values[k] = ~values[k];
          prefix[k + 1] = prefix[k] & values[k];
        }
        for(int k = n - 1; k >= 0; k--) suffix[k] = suffix[k + 1] & values[k];
        vScoreOn[i] = care[i] & prefix[n];
        for(int k = 0; k < n; k++) {
          vScoreObligations[k][i] = care[i] & prefix[k] & suffix[k + 1] & ~values[k];
        }
      }
      scoreTarget = id;
    }
    int best = -1;
    for(int phase = 0; phase < 2; phase++) {
      bool feasible = true;
      for(int i = 0; i < nWords && feasible; i++) {
        word value = vValues[fi * nWords + i];
        feasible = !(vScoreOn[i] & (phase ? value : ~value));
      }
      if(!feasible) continue;
      int score = 0;
      for(auto const &obligation: vScoreObligations) {
        bool removable = true;
        for(int i = 0; i < nWords && removable; i++) {
          word value = vValues[fi * nWords + i];
          removable = !(obligation[i] & (phase ? ~value : value));
        }
        score += removable;
      }
      best = std::max(best, score);
    }
    return best;
  }

  template <typename Ntk>
  void Simulator<Ntk>::AddCex(std::vector<VarValue> const &vCex) {
    scoreTarget = -1;
    if(nVerbose) {
      std::cout << "cex: ";
      for(VarValue c: vCex) {
        std::cout << GetVarValueChar(c);
      }
      std::cout << std::endl;
    }
    // record care pi indices
    assert(int_size(vCex) == pNtk->GetNumPis());
    std::vector<int> vCarePiIdxs;
    for(int idx = 0; idx < pNtk->GetNumPis(); idx++) {
      switch(vCex[idx]) {
      case TRUE:
        vCarePiIdxs.push_back(idx);
        break;
      case FALSE:
        vCarePiIdxs.push_back(idx);
        break;
      default:
        break;
      }
    }
    assert(!vCarePiIdxs.empty());
    // find compatible word
    int iWord = 0;
    std::vector<word> vCompatibleBits(1);
    itr it = vCompatibleBits.begin();
    for(; iWord < nWords; iWord++) {
      Fill(1, it);
      for(int idx: vCarePiIdxs) {
        int id = pNtk->GetPi(idx);
        bool c;
        if(vCex[idx] == TRUE) {
          c = false;
        } else {
          assert(vCex[idx] == FALSE);
          c = true;
        }
        itr x = vValues.begin() + id * nWords + iWord;
        itr y = vAssignedStimuli.begin() + idx * nWords + iWord;
        And(1, tmp.begin(), x, y, !c, false);
        And(1, it, it, tmp.begin(), false, true);
        if(IsZero(1, it)) {
          break;
        }
      }
      if(!IsZero(1, it)) {
        break;
      }
    }
    // find compatible bit
    int iBit;
    if(iWord < nWords) {
      assert(!IsZero(1, it));
      iBit = 0;
      while(!((*it >> iBit) & 1)) {
        iBit++;
      }
      if(nVerbose) {
        std::cout << "fusing into stimulus word " << iWord << " bit " << iBit << std::endl;
      }
      vPackedCount[iWord * 64 + iBit]++;
    } else {
      // no bits are compatible, so reset at pivot
      iWord = iPivot / 64;
      iBit = iPivot % 64;
      if(nVerbose) {
        std::cout << "resetting stimulus word " << iWord << " bit " << iBit << std::endl;
      }
      if(vPackedCount[iWord * 64 + iBit]) {
        // this can be zero only when stats has been reset
        vPackedCountEvicted.push_back(vPackedCount[iWord * 64 + iBit]);
      }
      vPackedCount[iWord * 64 + iBit] = 1;
      word mask = 1ull << iBit;
      for(int idx = 0; idx < pNtk->GetNumPis(); idx++) {
        vAssignedStimuli[idx * nWords + iWord] &= ~mask;
      }
      iPivot++;
      if(iPivot == 64 * nWords) {
        iPivot = 0;
      }
    }
    // update stimulus
    for(int idx: vCarePiIdxs) {
      int id = pNtk->GetPi(idx);
      word mask = 1ull << iBit;
      if(vCex[idx] == TRUE) {
        vValues[id * nWords + iWord] |= mask;
      } else {
        assert(vCex[idx] == FALSE);
        vValues[id * nWords + iWord] &= ~mask;
      }
      vAssignedStimuli[idx * nWords + iWord] |= mask;
      if(nVerbose) {
        std::cout << "node " << std::setw(3) << id << ": ";
        Print(1, vValues.begin() + id * nWords + iWord);
        std::cout << std::endl;
        std::cout << "asgn " << std::setw(3) << id << ": ";
        Print(1, vAssignedStimuli.begin() + idx * nWords + iWord);
        std::cout << std::endl;
      }
    }
    // simulate
    SimulateOneWord(iWord);
    // recompute care with new stimulus
    time_point timeStart = GetCurrentTime();
    if(target != -1 && !pNtk->IsPoDriver(target)) {
      if(nVerbose) {
        std::cout << "recomputing careset of " << target << std::endl;
      }
      ComputeCareWords(iWord, 1);
      if(nVerbose) {
        std::cout << "care " << std::setw(3) << target << ": ";
        Print(1, care.begin() + iWord);
        std::cout << std::endl;
      }
    }
    durationCare += Duration(timeStart, GetCurrentTime());
    nCex++;
  }

  // }}}

  // {{{ Summary

  template <typename Ntk>
  void Simulator<Ntk>::ResetSummary() {
    nCex = 0;
    nDiscarded = 0;
    nPackedCountOld = 0;
    for(int count: vPackedCount) {
      if(count) {
        nPackedCountOld++;
      }
    }
    vPackedCountEvicted.clear();
    durationSimulation = 0;
    durationCare = 0;
  };

  template <typename Ntk>
  summary<int> Simulator<Ntk>::GetStatsSummary() const {
    summary<int> v;
    v.emplace_back("sim cex", nCex);
    if(!fKeepStimula) {
      v.emplace_back("sim discarded cex", nDiscarded);
    }
    int nPackedCount = vPackedCountEvicted.size() - nPackedCountOld;
    for(int count: vPackedCount) {
      if(count) {
        nPackedCount++;
      }
    }
    v.emplace_back("sim packed pattern", nPackedCount);
    v.emplace_back("sim evicted pattern", vPackedCountEvicted.size());
    return v;
  };

  template <typename Ntk>
  summary<double> Simulator<Ntk>::GetTimesSummary() const {
    summary<double> v;
    v.emplace_back("sim simulation", durationSimulation);
    v.emplace_back("sim care computation", durationCare);
    return v;
  };

  // }}}

}

ABC_NAMESPACE_CXX_HEADER_END
