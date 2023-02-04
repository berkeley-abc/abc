#ifndef ABC__aig__gia__giaTransduction_h
#define ABC__aig__gia__giaTransduction_h

#include <iostream>
#include <iomanip>
#include <list>
#include <algorithm>
#include <cassert>

#include "giaNewBdd.h"

ABC_NAMESPACE_HEADER_START

class Transduction {
public:
  struct Backup {
    int state;
    int nObjsAlloc;
    std::list<int> vGates;
    std::vector<std::vector<int> > vvFis;
    std::vector<std::vector<int> > vvFos;
    std::vector<NewBdd::Node> vFs;
    std::vector<NewBdd::Node> vGs;
    std::vector<std::vector<NewBdd::Node> > vvCs;
    std::vector<bool> vUpdates;
    std::vector<bool> vPfUpdates;
    std::vector<bool> vFoConeShared;
  };

public:
  Transduction(Gia_Man_t * pGia, int nVerbose = 0, int SortType = 0);
  ~Transduction();

  void ShufflePis(int seed);

  Gia_Man_t * Aig() const;

  inline int CountGates() const;
  inline int CountWires() const;
  inline int CountNodes() const;
  inline void PrintStats() const;
  inline bool Verify() const;

  Backup * Save() const;
  inline void Load(Backup const * b);

  int TrivialMerge();
  int TrivialDecompose();
  int Merge(bool fMspf = false);
  int Decompose();

  int Cspf(bool fSortRemove = false, int block = -1, int block_i0 = -1);
  bool CspfDebug();

  int Mspf(bool fSort = false, int block = -1, int block_i0 = -1);
  bool MspfDebug();

  int Pf(bool fSort = false);
  bool PfDebug();

  int Resub(bool fMspf = false);
  int ResubMono(bool fMspf = false);

  int RepeatResub(bool fMono, bool fMspf);
  int RepeatResubInner(bool fMspf, bool fInner);
  int RepeatResubOuter(bool fMspf, bool fInner, bool fOuter);
  int Optimize(bool fFirstMerge, bool fMspfMerge, bool fMspfResub, bool fInner, bool fOuter);

private:
  int nVerbose;
  int SortType;

  int state;

  int nObjsAlloc;
  std::vector<int> vPis;
  std::vector<int> vPos;
  std::list<int> vGates;
  std::vector<std::vector<int> > vvFis;
  std::vector<std::vector<int> > vvFos;

  NewBdd::Man * bdd;
  std::vector<NewBdd::Node> vFs;
  std::vector<NewBdd::Node> vGs;
  std::vector<std::vector<NewBdd::Node> > vvCs;
  std::vector<NewBdd::Node> vPoFs;

  std::vector<bool> vUpdates;
  std::vector<bool> vPfUpdates;
  std::vector<bool> vFoConeShared;

  inline bool AllFalse(std::vector<bool> const & v) const;

  inline void Connect(int i, int f, bool fSort = false, bool fUpdate = true, NewBdd::Node c = NewBdd::Node());
  inline unsigned FindFi(int i, int i0) const;
  inline void Disconnect(int i, int i0, unsigned j, bool fUpdate = true, bool fPfUpdate = true);

  inline int RemoveFis(int i, bool fPfUpdate = true);
  inline int Replace(int i, int f, bool fUpdate = true);
  inline int ReplaceByConst(int i, bool c);
  inline void CreateNewGate(int & pos);

  void SortObjs_rec(std::list<int>::iterator const & it);

  void MarkFiCone_rec(std::vector<bool> & vMarks, int i) const;
  void MarkFoCone_rec(std::vector<bool> & vMarks, int i) const;

  void Build(int i, std::vector<NewBdd::Node> & vFs_) const;
  void Build(bool fPfUpdate = true);
  bool BuildDebug();

  bool RankCompare(int a, int b) const;
  bool SortFis(int i);

  int TrivialMergeOne(int i);
  int TrivialDecomposeOne(std::list<int>::iterator const & it, int & pos);

  int RemoveRedundantFis(int i, int block_i0 = -1, unsigned j = 0);
  void CalcG(int i);
  int CalcC(int i);

  bool IsFoConeShared_rec(std::vector<int> & vVisits, int i, int visitor) const;
  bool IsFoConeShared(int i) const;
  void BuildFoConeCompl(int i, std::vector<NewBdd::Node> & vPoFsCompl) const;
  bool MspfCalcG(int i);
  int MspfCalcC(int i, int block_i0 = -1);

  bool TryConnect(int i, int f);
};

int Transduction::CountGates() const {
  return vGates.size();
}
int Transduction::CountWires() const {
  int count = 0;
  for(std::list<int>::const_iterator it = vGates.begin(); it != vGates.end(); it++) {
    count += vvFis[*it].size();
  }
  return count;
}
int Transduction::CountNodes() const {
  return CountWires() - CountGates();
}
void Transduction::PrintStats() const {
  int gates = CountGates();
  int wires = CountWires();
  int nodes = wires - gates;
  std::cout << "nodes " << std::setw(5) << nodes << " gates " << std::setw(5) << gates << " wires " << std::setw(5) << wires << std::endl;
}
bool Transduction::Verify() const {
  for(unsigned j = 0; j < vPos.size(); j++) {
    int i0 = vvFis[vPos[j]][0] >> 1;
    bool c0 = vvFis[vPos[j]][0] & 1;
    if((vFs[i0] ^ c0) != vPoFs[j]) {
      return false;
    }
  }
  return true;
}

Transduction::Backup * Transduction::Save() const {
  Transduction::Backup * b = new Transduction::Backup;
  b->state = state;
  b->nObjsAlloc = nObjsAlloc;
  b->vGates = vGates;
  b->vvFis = vvFis;
  b->vvFos = vvFos;
  b->vFs = vFs;
  b->vGs = vGs;
  b->vvCs = vvCs;
  b->vUpdates = vUpdates;
  b->vPfUpdates = vPfUpdates;
  b->vFoConeShared = vFoConeShared;
  return b;
}
void Transduction::Load(Transduction::Backup const * b) {
  state = b->state;
  nObjsAlloc = b->nObjsAlloc;
  vGates = b->vGates;
  vvFis = b->vvFis;
  vvFos = b->vvFos;
  vFs = b->vFs;
  vGs = b->vGs;
  vvCs = b->vvCs;
  vUpdates = b->vUpdates;
  vPfUpdates = b->vPfUpdates;
  vFoConeShared = b->vFoConeShared;
}

bool Transduction::AllFalse(std::vector<bool> const & v) const {
  for(std::list<int>::const_iterator it = vGates.begin(); it != vGates.end(); it++) {
    if(v[*it]) {
      return false;
    }
  }
  return true;
}

void Transduction::Connect(int i, int f, bool fSort, bool fUpdate, NewBdd::Node c) {
  int i0 = f >> 1;
  if(nVerbose > 5) {
    std::cout << "\t\t\t\t\tConnect " << i0 << "(" << (f & 1) << ")" << " to " << i << std::endl;
  }
  assert(std::find(vvFis[i].begin(), vvFis[i].end(), f) == vvFis[i].end());
  vvFis[i].push_back(f);
  vvFos[i0].push_back(i);
  if(fUpdate) {
    vUpdates[i] = true;
  }
  vvCs[i].push_back(c);
  if(fSort && !vvFos[i].empty() && !vvFis[i0].empty()) {
    std::list<int>::iterator it = std::find(vGates.begin(), vGates.end(), i);
    std::list<int>::iterator it_i0 = std::find(it, vGates.end(), i0);
    if(it_i0 != vGates.end()) {
      if(nVerbose > 6) {
        std::cout << "\t\t\t\t\t\tMove " << i0 << " before " << *it << std::endl;
      }
      vGates.erase(it_i0);
      it_i0 = vGates.insert(it, i0);
      SortObjs_rec(it_i0);
    }
  }
}
unsigned Transduction::FindFi(int i, int i0) const {
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    if((vvFis[i][j] >> 1) == i0) {
      return j;
    }
  }
  abort();
}
void Transduction::Disconnect(int i, int i0, unsigned j, bool fUpdate, bool fPfUpdate) {
  if(nVerbose > 5) {
    std::cout << "\t\t\t\t\tDisconnect " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " from " << i << std::endl;
  }
  vvFos[i0].erase(std::find(vvFos[i0].begin(), vvFos[i0].end(), i));
  vvFis[i].erase(vvFis[i].begin() + j);
  vvCs[i].erase(vvCs[i].begin() + j);
  if(fUpdate) {
    vUpdates[i] = true;
  }
  if(fPfUpdate) {
    vPfUpdates[i0] = true;
  }
}

int Transduction::RemoveFis(int i, bool fPfUpdate) {
  if(nVerbose > 4) {
    std::cout << "\t\t\t\tRemove " << i << std::endl;
  }
  assert(vvFos[i].empty());
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    int i0 = vvFis[i][j] >> 1;
    vvFos[i0].erase(std::find(vvFos[i0].begin(), vvFos[i0].end(), i));
    if(fPfUpdate) {
      vPfUpdates[i0] = true;
    }
  }
  int count = vvFis[i].size();
  vvFis[i].clear();
  vFs[i] = vGs[i] = NewBdd::Node();
  vvCs[i].clear();
  vUpdates[i] = vPfUpdates[i] = false;
  return count;
}
int Transduction::Replace(int i, int f, bool fUpdate) {
  if(nVerbose > 4) {
    std::cout << "\t\t\t\tReplace " << i << " by " << (f >> 1) << "(" << (f & 1) << ")" << std::endl;
  }
  assert(i != (f >> 1));
  int count = 0;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    unsigned l = FindFi(k, i);
    int fc = f ^ (vvFis[k][l] & 1);
    std::vector<int>::iterator it = std::find(vvFis[k].begin(), vvFis[k].end(), fc);
    if(it != vvFis[k].end()) {
      assert(state == 0);
      vvCs[k].erase(vvCs[k].begin() + l);
      vvFis[k].erase(vvFis[k].begin() + l);
      count++;
    } else {
      vvFis[k][l] = f ^ (vvFis[k][l] & 1);
      vvFos[f >> 1].push_back(k);
    }
    if(fUpdate) {
      vUpdates[k] = true;
    }
  }
  vvFos[i].clear();
  vPfUpdates[f >> 1] = true;
  return count + RemoveFis(i);
}
int Transduction::ReplaceByConst(int i, bool c) {
  if(nVerbose > 4) {
    std::cout << "\t\t\t\tReplace " << i << " by " << c << std::endl;
  }
  int count = 0;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    unsigned l = FindFi(k, i);
    bool fc = c ^ (vvFis[k][l] & 1);
    vvFis[k].erase(vvFis[k].begin() + l);
    vvCs[k].erase(vvCs[k].begin() + l);
    if(fc) {
      if(vvFis[k].size() == 1) {
        count += Replace(k, vvFis[k][0]);
      } else {
        vUpdates[k] = true;
      }
    } else {
      count += ReplaceByConst(k, 0);
    }
  }
  count += vvFos[i].size();
  vvFos[i].clear();
  return count + RemoveFis(i);
}
void Transduction::CreateNewGate(int & pos) {
  while(pos != nObjsAlloc && (!vvFis[pos].empty() || !vvFos[pos].empty())) {
    pos++;
  }
  if(nVerbose > 4) {
    std::cout << "\t\t\t\tCreate " << pos << std::endl;
  }
  if(pos == nObjsAlloc) {
    nObjsAlloc++;
    vvFis.resize(nObjsAlloc);
    vvFos.resize(nObjsAlloc);
    vFs.resize(nObjsAlloc);
    vGs.resize(nObjsAlloc);
    vvCs.resize(nObjsAlloc);
    vUpdates.resize(nObjsAlloc);
    vPfUpdates.resize(nObjsAlloc);
  }
}
  
ABC_NAMESPACE_HEADER_END

#endif
