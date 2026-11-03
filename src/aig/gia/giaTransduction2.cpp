/**CFile****************************************************************

  FileName    [giaTransduction2.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experimental single-threaded transduction optimization.]

  Author      [Yukio Miyasaka and ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 30, 2026.]

  Description [Based on the original transduction implementation of May 2023.]

***********************************************************************/
#include "misc/util/abc_print.h"

#include "giaTransduction2.h"
#include "giaNewBdd.h"
#include "giaNewTt2.h"

ABC_NAMESPACE_IMPL_START

namespace Transduction2 {
// The BDD engine remains available for circuits too large for exhaustive tables.
class BddMan : public NewBdd::Man {
public:
  BddMan(int nVars, NewBdd::Param p) : NewBdd::Man(nVars, p) {}
  NewBdd::lit Xor(NewBdd::lit x, NewBdd::lit y) {
    NewBdd::lit f = And(x, LitNot(y));
    IncRef(f);
    NewBdd::lit g = And(LitNot(x), y);
    IncRef(g);
    NewBdd::lit r = Or(f, g);
    DecRef(f);
    DecRef(g);
    return r;
  }
  bool OrIsConst1(NewBdd::lit x, NewBdd::lit y) {
    return IsConst1(Or(x, y));
  }
  bool OrIsConst1(NewBdd::lit x, NewBdd::lit y, NewBdd::lit z) {
    NewBdd::lit t = Or(x, y);
    IncRef(t);
    bool r = IsConst1(Or(t, z));
    DecRef(t);
    return r;
  }
  // BDDs use the generic, reference-counted cone simulation.
  template<class Adjacency>
  bool MspfG(int, const std::list<int> &,
             const Adjacency &,
             const Adjacency &,
             const std::vector<NewBdd::lit> &, const std::vector<int> &,
             const std::vector<NewBdd::lit> &,
             const std::vector<std::vector<NewBdd::lit> > &, NewBdd::lit &) {
    return false;
  }
};
}


/**Function*************************************************************

  Synopsis    [Runs the experimental engine using growable BDD storage.]

***********************************************************************/
Gia_Man_t *Gia_ManTransduction2BddPolicy(Gia_Man_t *pGia, int nType, int fMspf, unsigned nRandom, int nSortType, int nPiShuffle, int nParameter, int fLevel, Gia_Man_t *pExdc, int fNewLine, int nVerbose, int nCandidates, int nMspfRestarts, int fHybrid, int fLocal, abctime deadline) {
  if(nRandom) {
    srand(nRandom);
    nSortType = rand() % 4;
    nPiShuffle = rand();
    nParameter = rand() % 16;
  }
  NewBdd::Param p;
  // Small graphs need thousands, rather than a million, initial BDD slots.
  p.nObjsAllocLog = 12;
  Transduction2::Transduction<Transduction2::BddMan, NewBdd::Param, NewBdd::lit, 0xffffffff> t(pGia, nVerbose, fNewLine, nSortType, nPiShuffle, fLevel, pExdc, p);
  t.SetSearchPolicy(nCandidates, nMspfRestarts, fHybrid != 0, fLocal != 0, deadline);
  int count = t.CountWires();
  switch(nType) {
  case 0:
    count -= fMspf? t.Mspf(): t.Cspf();
    break;
  case 1:
    count -= t.Resub(fMspf);
    break;
  case 2:
    count -= t.ResubMono(fMspf);
    break;
  case 3:
    count -= t.ResubShared(fMspf);
    break;
  case 4:
    count -= t.RepeatResub(false, fMspf);
    break;
  case 5:
    count -= t.RepeatResub(true, fMspf);
    break;
  case 6: {
    bool fInner = (nParameter / 4) % 2;
    count -= t.RepeatInner(fMspf, fInner);
    break;
  }
  case 7: {
    bool fInner = (nParameter / 4) % 2;
    bool fOuter = (nParameter / 8) % 2;
    count -= t.RepeatOuter(fMspf, fInner, fOuter);
    break;
  }
  case 8: {
    bool fFirstMerge = nParameter % 2;
    bool fMspfMerge = fMspf? (nParameter / 2) % 2: false;
    bool fInner = (nParameter / 4) % 2;
    bool fOuter = (nParameter / 8) % 2;
    count -= t.RepeatAll(fFirstMerge, fMspfMerge, fMspf, fInner, fOuter);
    break;
  }
  default:
    ABC_PRINT_STREAM( stdout, true, "Unknown transduction type " << nType << "\n" );
  }
  assert(t.Verify());
  assert(count == t.CountWires());
  return t.GenerateAig();
}

/**Function*************************************************************

  Synopsis    [Runs the experimental engine using exact truth tables.]

***********************************************************************/
Gia_Man_t *Gia_ManTransduction2TtPolicy(Gia_Man_t *pGia, int nType, int fMspf, unsigned nRandom, int nSortType, int nPiShuffle, int nParameter, int fLevel, Gia_Man_t *pExdc, int fNewLine, int nVerbose, int nCandidates, int nMspfRestarts, int fHybrid, int fLocal, abctime deadline) {
  if(nRandom) {
    srand(nRandom);
    nSortType = rand() % 4;
    nPiShuffle = rand();
    nParameter = rand() % 16;
  }
  NewTt2::Param p;
  p.nGbc = 2;
  Transduction2::Transduction<NewTt2::Man, NewTt2::Param, NewTt2::lit, 0xffffffff> t(pGia, nVerbose, fNewLine, nSortType, nPiShuffle, fLevel, pExdc, p);
  t.SetSearchPolicy(nCandidates, nMspfRestarts, fHybrid != 0, fLocal != 0, deadline);
  int count = t.CountWires();
  switch(nType) {
  case 0:
    count -= fMspf? t.Mspf(): t.Cspf();
    break;
  case 1:
    count -= t.Resub(fMspf);
    break;
  case 2:
    count -= t.ResubMono(fMspf);
    break;
  case 3:
    count -= t.ResubShared(fMspf);
    break;
  case 4:
    count -= t.RepeatResub(false, fMspf);
    break;
  case 5:
    count -= t.RepeatResub(true, fMspf);
    break;
  case 6: {
    bool fInner = (nParameter / 4) % 2;
    count -= t.RepeatInner(fMspf, fInner);
    break;
  }
  case 7: {
    bool fInner = (nParameter / 4) % 2;
    bool fOuter = (nParameter / 8) % 2;
    count -= t.RepeatOuter(fMspf, fInner, fOuter);
    break;
  }
  case 8: {
    bool fFirstMerge = nParameter % 2;
    bool fMspfMerge = fMspf? (nParameter / 2) % 2: false;
    bool fInner = (nParameter / 4) % 2;
    bool fOuter = (nParameter / 8) % 2;
    count -= t.RepeatAll(fFirstMerge, fMspfMerge, fMspf, fInner, fOuter);
    break;
  }
  default:
    ABC_PRINT_STREAM( stdout, true, "Unknown transduction type " << nType << "\n" );
  }
  assert(t.Verify());
  assert(count == t.CountWires());
  return t.GenerateAig();
}

/**Function*************************************************************

  Synopsis    [Retains the original search settings for existing callers.]

***********************************************************************/
Gia_Man_t *Gia_ManTransduction2Bdd(Gia_Man_t *pGia, int nType, int fMspf, unsigned nRandom, int nSortType, int nPiShuffle, int nParameter, int fLevel, Gia_Man_t *pExdc, int fNewLine, int nVerbose) {
  return Gia_ManTransduction2BddPolicy(pGia, nType, fMspf, nRandom, nSortType, nPiShuffle, nParameter, fLevel, pExdc, fNewLine, nVerbose, 0, 0, 0, 0, 0);
}

/**Function*************************************************************

  Synopsis    [Retains the original search settings for existing callers.]

***********************************************************************/
Gia_Man_t *Gia_ManTransduction2Tt(Gia_Man_t *pGia, int nType, int fMspf, unsigned nRandom, int nSortType, int nPiShuffle, int nParameter, int fLevel, Gia_Man_t *pExdc, int fNewLine, int nVerbose) {
  return Gia_ManTransduction2TtPolicy(pGia, nType, fMspf, nRandom, nSortType, nPiShuffle, nParameter, fLevel, pExdc, fNewLine, nVerbose, 0, 0, 0, 0, 0);
}

ABC_NAMESPACE_IMPL_END
