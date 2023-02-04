#ifdef _WIN32
#ifndef __MINGW32__
#pragma warning(disable : 4786) // warning C4786: identifier was truncated to '255' characters in the browser information
#endif
#endif

#include <set>
#include <map>

#include "giaTransduction.h"

ABC_NAMESPACE_IMPL_START

using namespace std;

namespace Transduction {

Transduction::Transduction(Gia_Man_t * pGia, int nVerbose, int SortType) : nVerbose(nVerbose), SortType(SortType), state(PfState::none) {
  int i;
  Gia_Obj_t * pObj;
  if(nVerbose > 2) {
    cout << "\t\tImport aig" << endl;
  }
  // allocation
  bdd = new NewBdd::Man(Gia_ManCiNum(pGia), true);
  nObjsAlloc = Gia_ManObjNum(pGia);
  vvFis.resize(nObjsAlloc);
  vvFos.resize(nObjsAlloc);
  vFs.resize(nObjsAlloc);
  vGs.resize(nObjsAlloc);
  vvCs.resize(nObjsAlloc);
  vUpdates.resize(nObjsAlloc);
  vPfUpdates.resize(nObjsAlloc);
  // import
  int nObjs = 0;
  vector<int> v(Gia_ManObjNum(pGia), -1);
  // constant
  vFs[nObjs] = NewBdd::Node::Const0(bdd);
  v[Gia_ObjId(pGia, Gia_ManConst0(pGia))] = nObjs << 1;
  nObjs++;
  // inputs
  Gia_ManForEachCi(pGia, pObj, i) {
    vFs[nObjs] = NewBdd::Node::IthVar(bdd, i);
    v[Gia_ObjId(pGia, pObj)] = nObjs << 1;
    vPis.push_back(nObjs);
    nObjs++;
  }
  // nodes
  Gia_ManForEachAnd(pGia, pObj, i) {
    int id = Gia_ObjId(pGia, pObj);
    if(nVerbose > 3) {
      cout << "\t\t\tImport node " << id << endl;
    }
    int i0 = Gia_ObjId(pGia, Gia_ObjFanin0(pObj));
    int i1 = Gia_ObjId(pGia, Gia_ObjFanin1(pObj));
    int c0 = Gia_ObjFaninC0(pObj);
    int c1 = Gia_ObjFaninC1(pObj);
    if(i0 == i1) {
      if(c0 == c1) {
        v[id] = v[i0] ^ c0;
      } else {
        v[id] = 0;
      }
    } else {
      Connect(nObjs , v[i0] ^ c0);
      Connect(nObjs, v[i1] ^ c1);
      v[id] = nObjs << 1;
      vObjs.push_back(nObjs);
      nObjs++;
    }
  }
  // outputs
  Gia_ManForEachCo(pGia, pObj, i) {
    if(nVerbose > 3) {
      cout << "\t\t\tImport po " << i << endl;
    }
    int i0 = Gia_ObjId(pGia, Gia_ObjFanin0(pObj));
    bool c0 = Gia_ObjFaninC0(pObj);
    Connect(nObjs, v[i0] ^ c0);
    vvCs[nObjs][0] = NewBdd::Node::Const0(bdd);
    vPos.push_back(nObjs);
    nObjs++;
  }
  // build bdd
  bdd->SetParameters(1, 12);
  Build(false);
  bdd->Reorder();
  bdd->SetParameters(1);
  // check and store outputs
  bool fRemoved = false;
  for(unsigned i = 0; i < vPos.size(); i++) {
    int i0 = vvFis[vPos[i]][0] >> 1;
    bool c0 = vvFis[vPos[i]][0] & 1;
    NewBdd::Node x = vFs[i0] ^ c0;
    if(i0) {
      if((x | vvCs[vPos[i]][0]).IsConst1()) {
        if(nVerbose > 3) {
          cout << "\t\t\tConst 1 output : po " << i << endl;
        }
        Disconnect(vPos[i], i0, 0, false, false);
        Connect(vPos[i], 1, false, false);
        x = NewBdd::Node::Const1(bdd);
        fRemoved |= vvFos[i0].empty();
      } else if((~x | vvCs[vPos[i]][0]).IsConst1()) {
        if(nVerbose > 3) {
          cout << "\t\t\tConst 0 output : po " << i << endl;
        }
        Disconnect(vPos[i], i0, 0, false, false);
        Connect(vPos[i], 0, false, false);
        x = NewBdd::Node::Const0(bdd);
        fRemoved |= vvFos[i0].empty();
      }
    }
    vPoFs.push_back(x);
  }
  // remove unused nodes
  if(fRemoved) {
    if(nVerbose > 3) {
      cout << "\t\t\tRemove unused" << endl;
    }
    for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
      if(vvFos[*it].empty()) {
        RemoveFis(*it, false);
        it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
        continue;
      }
      it++;
    }
  }
}
Transduction::~Transduction() {
  vFs.clear();
  vGs.clear();
  vvCs.clear();
  vPoFs.clear();
  delete bdd;
}

void Transduction::ShufflePis(int seed) {
  srand(seed);
  for(int i = (int)vPis.size() - 1; i > 0; i--) {
    swap(vPis[i], vPis[rand() % (i + 1)]);
  }
}

Gia_Man_t * Transduction::Aig() const {
  Gia_Man_t * pGia, *pTemp;
  pGia = Gia_ManStart(1 + vPis.size() + CountNodes() + vPos.size());
  Gia_ManHashAlloc(pGia);
  vector<int> values(nObjsAlloc);
  values[0] = Gia_ManConst0Lit();
  for(unsigned i = 0; i < vPis.size(); i++) {
    values[vPis[i]] = Gia_ManAppendCi(pGia);
  }
  for(list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    assert(vvFis[*it].size() > 1);
    int i0 = vvFis[*it][0] >> 1;
    int i1 = vvFis[*it][1] >> 1;
    int c0 = vvFis[*it][0] & 1;
    int c1 = vvFis[*it][1] & 1;
    int r = Gia_ManHashAnd(pGia, Abc_LitNotCond(values[i0], c0), Abc_LitNotCond(values[i1], c1));
    for(unsigned i = 2; i < vvFis[*it].size(); i++) {
      int ii = vvFis[*it][i] >> 1;
      int ci = vvFis[*it][i] & 1;
      r = Gia_ManHashAnd(pGia, r, Abc_LitNotCond(values[ii], ci));
    }
    values[*it] = r;
  }
  for(unsigned i = 0; i < vPos.size(); i++) {
    int i0 = vvFis[vPos[i]][0] >> 1;
    int c0 = vvFis[vPos[i]][0] & 1;
    Gia_ManAppendCo(pGia, Abc_LitNotCond(values[i0], c0));
  }
  pGia = Gia_ManCleanup(pTemp = pGia);
  Gia_ManStop(pTemp);
  return pGia;
}

void Transduction::SortObjs_rec(list<int>::iterator const & it) {
  for(unsigned j = 0; j < vvFis[*it].size(); j++) {
    int i0 = vvFis[*it][j] >> 1;
    if(!vvFis[i0].empty()) {
      list<int>::iterator it_i0 = find(it, vObjs.end(), i0);
      if(it_i0 != vObjs.end()) {
        if(nVerbose > 6) {
          cout << "\t\t\t\t\t\tMove " << i0 << " before " << *it << endl;
        }
        vObjs.erase(it_i0);
        it_i0 = vObjs.insert(it, i0);
        SortObjs_rec(it_i0);
      }
    }
  }
}

void Transduction::MarkFiCone_rec(vector<bool> & vMarks, int i) const {
  if(vMarks[i]) {
    return;
  }
  vMarks[i] = true;
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    MarkFiCone_rec(vMarks, vvFis[i][j] >> 1);
  }
}
void Transduction::MarkFoCone_rec(vector<bool> & vMarks, int i) const {
  if(vMarks[i]) {
    return;
  }
  vMarks[i] = true;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    MarkFoCone_rec(vMarks, vvFos[i][j]);
  }
}

void Transduction::Build(int i, vector<NewBdd::Node> & vFs_) const {
  if(nVerbose > 4) {
    cout << "\t\t\t\tBuild " << i << endl;
  }
  vFs_[i] = NewBdd::Node::Const1(bdd);
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    vFs_[i] = vFs_[i] & (vFs_[i0] ^ c0);
  }
}
void Transduction::Build(bool fPfUpdate) {
  if(nVerbose > 3) {
    cout << "\t\t\tBuild" << endl;
  }
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    if(vUpdates[*it]) {
      NewBdd::Node x = vFs[*it];
      Build(*it, vFs);
      if(x != vFs[*it]) {
        for(unsigned j = 0; j < vvFos[*it].size(); j++) {
          vUpdates[vvFos[*it][j]] = true;
        }
      }
    }
  }
  if(fPfUpdate) {
    for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
      vPfUpdates[*it] = vPfUpdates[*it] || vUpdates[*it];
    }
  }
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    vUpdates[*it] = false;
  }
  assert(AllFalse(vUpdates));
}
bool Transduction::BuildDebug() {
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    vUpdates[*it] = true;
  }
  vector<NewBdd::Node> vFsOld = vFs;
  Build(false);
  return vFsOld != vFs;
}

bool Transduction::RankCompare(int a, int b) const {
  int a0 = a >> 1;
  int b0 = b >> 1;
  if(vvFis[a0].empty() && vvFis[b0].empty()) {
    return find(find(vPis.begin(), vPis.end(), a0), vPis.end(), b0) != vPis.end();
  }
  if(vvFis[a0].empty() && !vvFis[b0].empty()) {
    return false;
  }
  if(!vvFis[a0].empty() && vvFis[b0].empty()) {
    return true;
  }
  if(vvFos[a0].size() > vvFos[b0].size()) {
    return false;
  }
  if(vvFos[a0].size() < vvFos[b0].size()) {
    return true;
  }
  bool ac = a & 1;
  bool bc = b & 1;
  switch(SortType) {
  case 0:
    return find(find(vObjs.begin(), vObjs.end(), a0), vObjs.end(), b0) == vObjs.end();
  case 1:
    return (vFs[a0] ^ ac).OneCount() < (vFs[b0] ^ bc).OneCount();
  case 2:
    return vFs[a0].OneCount() < vFs[b0].OneCount();
  case 3:
    return vFs[a0].ZeroCount() < vFs[b0].OneCount();
  default:
    throw invalid_argument("Invalid sort type");
  }
}
bool Transduction::SortFis(int i) {
  if(nVerbose > 4) {
    cout << "\t\t\t\tSort fanins " << i << endl;
  }
  bool fSort = false;
  for(int p = 1; p < (int)vvFis[i].size(); p++) {
    int f = vvFis[i][p];
    NewBdd::Node c = vvCs[i][p];
    int q = p - 1;
    for(; q >= 0 && RankCompare(f, vvFis[i][q]); q--) {
      vvFis[i][q + 1] = vvFis[i][q];
      vvCs[i][q + 1] = vvCs[i][q];
    }
    if(q + 1 != p) {
      fSort = true;
      vvFis[i][q + 1] = f;
      vvCs[i][q + 1] = c;
    }
  }
  if(nVerbose > 5) {
    for(unsigned j = 0; j < vvFis[i].size(); j++) {
      cout << "\t\t\t\t\tFanin " << j << " : " << (vvFis[i][j] >> 1) << "(" << (vvFis[i][j] & 1) << ")" << endl;
    }
  }
  return fSort;
}

int Transduction::RemoveRedundantFis(int i, int block_i0, unsigned j) {
  int count = 0;
  for(; j < vvFis[i].size(); j++) {
    if(block_i0 == (vvFis[i][j] >> 1)) {
      continue;
    }
    NewBdd::Node x = NewBdd::Node::Const1(bdd);
    for(unsigned jj = 0; jj < vvFis[i].size(); jj++) {
      if(j != jj) {
        int i0 = vvFis[i][jj] >> 1;
        bool c0 = vvFis[i][jj] & 1;
        x = x & (vFs[i0] ^ c0);
      }
    }
    x = ~x | vGs[i];
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    x = x | (vFs[i0] ^ c0);
    if(x.IsConst1()) {
      if(nVerbose > 4) {
        cout << "\t\t\t\tRRF remove wire " << i0 << "(" << c0 << ")" << " -> " << i << endl;
      }
      Disconnect(i, i0, j--);
      count++;
    }
  }
  return count;
}

void Transduction::CalcG(int i) {
  vGs[i] = NewBdd::Node::Const1(bdd);
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    unsigned l = FindFi(k, i);
    vGs[i] = vGs[i] & vvCs[k][l];
  }
}

int Transduction::CalcC(int i) {
  int count = 0;
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    // x = Not(And(FIs with larger rank))
    NewBdd::Node x = NewBdd::Node::Const1(bdd);
    for(unsigned jj = j + 1; jj < vvFis[i].size(); jj++) {
      int i0 = vvFis[i][jj] >> 1;
      bool c0 = vvFis[i][jj] & 1;
      x = x & (vFs[i0] ^ c0);
    }
    x = ~x;
    // c = Or(x, g[i])
    NewBdd::Node c = x | vGs[i];
    x = NewBdd::Node();
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    // Or(c, f[i_j]) == const1 -> redundant
    if((c | (vFs[i0] ^ c0)).IsConst1()) {
      if(nVerbose > 4) {
        cout << "\t\t\t\tCspf remove wire " << i0 << "(" << c0 << ")" << " -> " << i << endl;
      }
      Disconnect(i, i0, j--);
      count++;
    } else if(vvCs[i][j] != c) {
      vvCs[i][j] = c;
      vPfUpdates[i0] = true;
    }
  }
  return count;
}

int Transduction::Cspf(bool fSortRemove, int block, int block_i0) {
  if(nVerbose > 2) {
    cout << "\t\tCspf";
    if(block_i0 != -1) {
      cout << " (block " << block_i0 << " -> " << block << ")";
    } else if(block != -1) {
      cout << " (block " << block << ")";
    }
    cout << endl;
  }
  if(state != PfState::cspf) {
    for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
      vPfUpdates[*it] = true;
    }
    state = PfState::cspf;
  }
  int count = 0;
  for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
    if(vvFos[*it].empty()) {
      if(nVerbose > 3) {
        cout << "\t\t\tRemove unused " << *it << endl;
      }
      count += RemoveFis(*it);
      it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
      continue;
    }
    if(!vPfUpdates[*it]) {
      it++;
      continue;
    }
    if(nVerbose > 3) {
      cout << "\t\t\tCspf " << *it << endl;
    }
    CalcG(*it);
    if(fSortRemove) {
      if(*it != block) {
        SortFis(*it);
        count += RemoveRedundantFis(*it);
      } else if(block_i0 != -1) {
        count += RemoveRedundantFis(*it, block_i0);
      }
    }
    count += CalcC(*it);
    vPfUpdates[*it] = false;
    assert(!vvFis[*it].empty());
    if(vvFis[*it].size() == 1) {
      count += Replace(*it, vvFis[*it][0]);
      it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
      continue;
    }
    it++;
  }
  Build(false);
  assert(AllFalse(vPfUpdates));
  return count;
}

bool Transduction::CspfDebug() {
  vector<NewBdd::Node> vGsOld = vGs;
  vector<vector<NewBdd::Node> > vvCsOld = vvCs;
  state = PfState::none;
  Cspf();
  return vGsOld != vGs || vvCsOld != vvCs;
}

bool Transduction::IsFoConeShared_rec(vector<int> & vVisits, int i, int visitor) const {
  if(vVisits[i] == visitor) {
    return false;
  }
  if(vVisits[i]) {
    return true;
  }
  vVisits[i] = visitor;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    if(IsFoConeShared_rec(vVisits, vvFos[i][j], visitor)) {
      return true;
    }
  }
  return false;
}
bool Transduction::IsFoConeShared(int i) const {
  vector<int> vVisits(nObjsAlloc);
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    if(IsFoConeShared_rec(vVisits, vvFos[i][j], j + 1)) {
      return true;
    }
  }
  return false;
}

void Transduction::BuildFoConeCompl(int i, vector<NewBdd::Node> & vPoFsCompl) const {
  if(nVerbose > 3) {
    cout << "\t\t\tBuild with complemented " << i << endl;
  }
  vector<NewBdd::Node> vFsCompl = vFs;
  vFsCompl[i] = ~vFs[i];
  vector<bool> vUpdatesCompl(nObjsAlloc);
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    vUpdatesCompl[vvFos[i][j]] = true;
  }
  for(list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    if(vUpdatesCompl[*it]) {
      NewBdd::Node x = vFsCompl[*it];
      Build(*it, vFsCompl);
      if(x != vFsCompl[*it]) {
        for(unsigned j = 0; j < vvFos[*it].size(); j++) {
          vUpdatesCompl[vvFos[*it][j]] = true;
        }
      }
    }
  }
  for(unsigned j = 0; j < vPos.size(); j++) {
    int i0 = vvFis[vPos[j]][0] >> 1;
    bool c0 = vvFis[vPos[j]][0] & 1;
    vPoFsCompl.push_back(vFsCompl[i0] ^ c0);
  }
}

bool Transduction::MspfCalcG(int i) {
  NewBdd::Node g = vGs[i];
  vector<NewBdd::Node> vPoFsCompl;
  BuildFoConeCompl(i, vPoFsCompl);
  vGs[i] = NewBdd::Node::Const1(bdd);
  for(unsigned j = 0; j < vPos.size(); j++) {
    NewBdd::Node x = ~(vPoFs[j] ^ vPoFsCompl[j]);
    x = x | vvCs[vPos[j]][0];
    vGs[i] = vGs[i] & x;
  }
  return vGs[i] != g;
}

int Transduction::MspfCalcC(int i, int block_i0) {
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    // x = Not(And(other FIs))
    NewBdd::Node x = NewBdd::Node::Const1(bdd);
    for(unsigned jj = 0; jj < vvFis[i].size(); jj++) {
      if(j != jj) {
        int i0 = vvFis[i][jj] >> 1;
        bool c0 = vvFis[i][jj] & 1;
        x = x & (vFs[i0] ^ c0);
      }
    }
    x = ~x;
    // c = Or(x, g[i])
    NewBdd::Node c = x | vGs[i];
    x = NewBdd::Node();
    // Or(c, f[i_j]) == const1 -> redundant
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    if(i0 != block_i0 && (c | (vFs[i0] ^ c0)).IsConst1()) {
      if(nVerbose > 4) {
        cout << "\t\t\t\tMspf remove wire " << i0 << "(" << c0 << ")" << " -> " << i << endl;
      }
      Disconnect(i, i0, j);
      return RemoveRedundantFis(i, block_i0, j) + 1;
    } else if(vvCs[i][j] != c) {
      vvCs[i][j] = c;
      vPfUpdates[i0] = true;
    }
  }
  return 0;
}

int Transduction::Mspf(bool fSort, int block, int block_i0) {
  if(nVerbose > 2) {
    cout << "\t\tMspf";
    if(block_i0 != -1) {
      cout << " (block " << block_i0 << " -> " << block << ")";
    } else if(block != -1) {
      cout << " (block " << block << ")";
    }
    cout << endl;
  }
  assert(AllFalse(vUpdates));
  vFoConeShared.resize(nObjsAlloc);
  if(state != PfState::mspf) {
    for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
      vPfUpdates[*it] = true;
    }
    state = PfState::mspf;
  }
  int count = 0;
  for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
    if(vvFos[*it].empty()) {
      if(nVerbose > 3) {
        cout << "\t\t\tRemove unused " << *it << endl;
      }
      count += RemoveFis(*it);
      it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
      continue;
    }
    if(!vFoConeShared[*it] && !vPfUpdates[*it] && (vvFos[*it].size() == 1 || !IsFoConeShared(*it))) {
      it++;
      continue;
    }
    if(nVerbose > 3) {
      cout << "\t\t\tMspf " << *it << endl;
    }
    if(vvFos[*it].size() == 1 || !IsFoConeShared(*it)) {
      if(vFoConeShared[*it]) {
        vFoConeShared[*it] = false;
        NewBdd::Node g = vGs[*it];
        CalcG(*it);
        if(g == vGs[*it] && !vPfUpdates[*it]) {
          it++;
          continue;
        }
      } else {
        CalcG(*it);
      }
    } else {
      vFoConeShared[*it] = true;
      if(!MspfCalcG(*it) && !vPfUpdates[*it]) {
        it++;
        continue;
      }
      if((vGs[*it] | vFs[*it]).IsConst1()) {
        count += ReplaceByConst(*it, 1);
        vObjs.erase(--(it.base()));
        Build();
        it = vObjs.rbegin();
        continue;
      }
      if((vGs[*it] | ~vFs[*it]).IsConst1()) {
        count += ReplaceByConst(*it, 0);
        vObjs.erase(--(it.base()));
        Build();
        it = vObjs.rbegin();
        continue;
      }
    }
    if(fSort && block != *it) {
      SortFis(*it);
    }
    if(int diff = (block == *it)? MspfCalcC(*it, block_i0): MspfCalcC(*it)) {
      count += diff;
      assert(!vvFis[*it].empty());
      if(vvFis[*it].size() == 1) {
        count += Replace(*it, vvFis[*it][0]);
        vObjs.erase(--(it.base()));
      }
      Build();
      it = vObjs.rbegin();
      continue;
    }
    vPfUpdates[*it] = false;
    it++;
  }
  assert(AllFalse(vUpdates));
  assert(AllFalse(vPfUpdates));
  return count;
}

bool Transduction::MspfDebug() {
  vector<NewBdd::Node> vGsOld = vGs;
  vector<vector<NewBdd::Node> > vvCsOld = vvCs;
  state = PfState::none;
  Mspf();
  return vGsOld != vGs || vvCsOld != vvCs;
}

bool Transduction::TryConnect(int i, int f) {
  if(find(vvFis[i].begin(), vvFis[i].end(), f) == vvFis[i].end()) {
    int i0 = f >> 1;
    bool c0 = f & 1;
    NewBdd::Node x = ~vFs[i] | vGs[i] | (vFs[i0] ^ c0);
    if(x.IsConst1()) {
      if(nVerbose > 3) {
        cout << "\t\t\tConnect " << (f >> 1) << "(" << (f & 1) << ")" << std::endl;
      }
      Connect(i, f, true);
      return true;
    }
  }
  return false;
}

int Transduction::TrivialMergeOne(int i) {
  if(nVerbose > 3) {
    cout << "\t\t\tTrivial merge " << i << endl;
  }
  int count = 0;
  vector<int> vFisOld = vvFis[i];
  vector<NewBdd::Node> vCsOld = vvCs[i];
  vvFis[i].clear();
  vvCs[i].clear();
  for(unsigned j = 0; j < vFisOld.size(); j++) {
    int i0 = vFisOld[j] >> 1;
    int c0 = vFisOld[j] & 1;
    if(vvFis[i0].empty() || vvFos[i0].size() > 1 || c0) {
      if(nVerbose > 5) {
        cout << "\t\t\t\t\tFanin " << j << " : " << i0 << "(" << c0 << ")" << endl;
      }
      vvFis[i].push_back(vFisOld[j]);
      vvCs[i].push_back(vCsOld[j]);
      continue;
    }
    vPfUpdates[i] = vPfUpdates[i] | vPfUpdates[i0];
    vvFos[i0].erase(std::find(vvFos[i0].begin(), vvFos[i0].end(), i));
    count++;
    vector<int>::iterator itfi = vFisOld.begin() + j;
    vector<NewBdd::Node>::iterator itc = vCsOld.begin() + j;
    for(unsigned jj = 0; jj < vvFis[i0].size(); jj++) {
      int f = vvFis[i0][jj];
      vector<int>::iterator it = find(vvFis[i].begin(), vvFis[i].end(), f);
      if(it == vvFis[i].end()) {
        vvFos[f >> 1].push_back(i);
        itfi = vFisOld.insert(itfi, f);
        itc = vCsOld.insert(itc, vvCs[i0][jj]);
        itfi++;
        itc++;
        count--;
      } else {
        assert(state == PfState::none);
      }
    }
    count += RemoveFis(i0, false);
    vObjs.erase(find(vObjs.begin(), vObjs.end(), i0));
    vFisOld.erase(itfi);
    vCsOld.erase(itc);
    j--;
  }
  return count;
}
int Transduction::TrivialMerge() {
  if(nVerbose > 2) {
    cout << "\t\tTrivial merge" << endl;
  }
  int count = 0;
  for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
    count += TrivialMergeOne(*it);
    it++;
  }
  return count;
}

int Transduction::TrivialDecomposeOne(list<int>::iterator const & it, int & pos) {
  if(nVerbose > 3) {
    cout << "\t\t\tTrivial decompose " << *it << endl;
  }
  assert(vvFis[*it].size() > 2);
  int count = 2 - vvFis[*it].size();
  while(vvFis[*it].size() > 2) {
    int f0 = vvFis[*it].back();
    NewBdd::Node c0 = vvCs[*it].back();
    Disconnect(*it, f0 >> 1, vvFis[*it].size() - 1, false, false);
    int f1 = vvFis[*it].back();
    NewBdd::Node c1 = vvCs[*it].back();
    Disconnect(*it, f1 >> 1, vvFis[*it].size() - 1, false, false);
    CreateNewGate(pos);
    Connect(pos, f1, false, false, c1);
    Connect(pos, f0, false, false, c0);
    if(!vPfUpdates[*it]) {
      if(state == PfState::cspf) {
        vGs[pos] = vGs[*it];
      } else if(state == PfState::mspf) {
        NewBdd::Node x = NewBdd::Node::Const1(bdd);
        for(unsigned j = 0; j < vvFis[*it].size(); j++) {
          int i0 = vvFis[*it][j] >> 1;
          bool c0 = vvFis[*it][j] & 1;
          x = x & (vFs[i0] ^ c0);
        }
        x = ~x;
        vGs[pos] = x | vGs[*it];
      }
    }
    Connect(*it, pos << 1, false, false, vGs[pos]);
    vObjs.insert(it, pos);
    Build(pos, vFs);
  }
  return count;
}
int Transduction::TrivialDecompose() {
  if(nVerbose > 2) {
    cout << "\t\tTrivial decompose" << endl;
  }
  int count = 0;
  int pos = vPis.size() + 1;
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    if(vvFis[*it].size() > 2) {
      count += TrivialDecomposeOne(it, pos);
    }
  }
  return count;
}

int Transduction::Merge(bool fMspf) {
  if(nVerbose) {
    cout << "Merge" << endl;
  }
  int count = fMspf? Mspf(true): Cspf(true);
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1) {
      cout << "\tMerge " << *it << endl;
    }
    if(vvFos[*it].empty()) {
      continue;
    }
    count += TrivialMergeOne(*it);
    bool fConnect = false;
    for(unsigned i = 0; i < vPis.size(); i++) {
      int f = vPis[i] << 1;
      if(TryConnect(*it, f) || TryConnect(*it, f ^ 1)) {
        fConnect |= true;
        count--;
      }
    }
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    for(list<int>::iterator it2 = targets.begin(); it2 != targets.end(); it2++) {
      if(!vMarks[*it2] && !vvFos[*it2].empty()) {
        int f = *it2 << 1;
        if(TryConnect(*it, f) || TryConnect(*it, f ^ 1)) {
          fConnect |= true;
          count--;
        }
      }
    }
    if(fConnect) {
      if(fMspf) {
        Build();
        count += Mspf(true, *it);
      } else {
        vPfUpdates[*it] = true;
        count += Cspf(true, *it);
      }
      if(!vvFos[*it].empty()) {
        vPfUpdates[*it] = true;
        count += fMspf? Mspf(true): Cspf(true);
      }
    }
  }
  return count;
}

int Transduction::Decompose() {
  if(nVerbose) {
    cout << "Decompose" << endl;
  }
  int count = 0;
  int pos = vPis.size() + 1;
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    set<int> s1(vvFis[*it].begin(), vvFis[*it].end());
    assert(s1.size() == vvFis[*it].size());
    list<int>::iterator it2 = it;
    for(it2++; it2 != vObjs.end(); it2++) {
      set<int> s2(vvFis[*it2].begin(), vvFis[*it2].end());
      set<int> s;
      set_intersection(s1.begin(), s1.end(), s2.begin(), s2.end(), inserter(s, s.begin()));
      if(s.size() > 1) {
        if(s == s1) {
          if(s == s2) {
            if(nVerbose > 1) {
              cout << "\tReplace " << *it2 << " by " << *it << endl;
            }
            count += Replace(*it2, *it << 1, false);
            it2 = vObjs.erase(it2);
            it2--;
          } else {
            if(nVerbose > 1) {
              cout << "\tDecompose " << *it2 << " by " << *it << endl;
            }
            for(set<int>::iterator it3 = s.begin(); it3 != s.end(); it3++) {
              unsigned j = find(vvFis[*it2].begin(), vvFis[*it2].end(), *it3) - vvFis[*it2].begin();
              Disconnect(*it2, *it3 >> 1, j, false);
            }
            count += s.size();
            if(find(vvFis[*it2].begin(), vvFis[*it2].end(), *it << 1) == vvFis[*it2].end()) {
              Connect(*it2, *it << 1, false, false);
              count--;
            }
            vPfUpdates[*it2] = true;
          }
          continue;
        }
        if(s == s2) {
          it = vObjs.insert(it, *it2);
          vObjs.erase(it2);
        } else {
          CreateNewGate(pos);
          if(nVerbose > 1) {
            cout << "\tCreate " << pos << " for intersection of " << *it << " and " << *it2  << endl;
          }
          if(nVerbose > 2) {
            cout << "\t\tIntersection :";
            for(set<int>::iterator it3 = s.begin(); it3 != s.end(); it3++) {
              cout << " " << (*it3 >> 1) << "(" << (*it3 & 1) << ")";
            }
            cout << endl;
          }
          for(set<int>::iterator it3 = s.begin(); it3 != s.end(); it3++) {
            Connect(pos, *it3, false, false);
          }
          count -= s.size();
          it = vObjs.insert(it, pos);
          Build(pos, vFs);
          vPfUpdates[*it] = true;
        }
        s1 = s;
        it2 = it;
      }
    }
    if(vvFis[*it].size() > 2) {
      if(nVerbose > 1) {
        cout << "\tTrivial decompose " << *it << endl;
      }
      count += TrivialDecomposeOne(it, pos);
    }
  }
  return count;
}

int Transduction::Resub(bool fMspf) {
  if(nVerbose) {
    cout << "Resubstitution" << endl;
  }
  int count = fMspf? Mspf(true): Cspf(true);
  int nodes = CountNodes();
  TransductionBackup b;
  Save(b);
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1) {
      cout << "\tResubstitute " << *it << endl;
    }
    if(vvFos[*it].empty()) {
      continue;
    }
    int count_ = count;
    // merge
    count += TrivialMergeOne(*it);
    // resub
    bool fConnect = false;
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    list<int> targets2 = vObjs;
    for(list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++) {
      if(!vMarks[*it2] && !vvFos[*it2].empty()) {
        int f = *it2 << 1;
        if(TryConnect(*it, f) || TryConnect(*it, f ^ 1)) {
          fConnect |= true;
          count--;
        }
      }
    }
    if(fConnect) {
      if(fMspf) {
        Build();
        count += Mspf(true, *it);
      } else {
        vPfUpdates[*it] = true;
        count += Cspf(true, *it);
      }
      if(!vvFos[*it].empty()) {
        vPfUpdates[*it] = true;
        count += fMspf? Mspf(true): Cspf(true);
      }
    }
    if(nodes < CountNodes()) {
      Load(b);
      count = count_;
      continue;
    }
    if(!vvFos[*it].empty() && vvFis[*it].size() > 2) {
      // decompose
      list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
      int pos = nObjsAlloc;
      count += TrivialDecomposeOne(it2, pos);
    }
    nodes = CountNodes();
    Save(b);
  }
  return count;
}

int Transduction::ResubMono(bool fMspf) {
  if(nVerbose) {
    cout << "Resubstitution mono" << endl;
  }
  int count = fMspf? Mspf(true): Cspf(true);
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1) {
      cout << "\tResubstitute mono " << *it << endl;
    }
    if(vvFos[*it].empty()) {
      continue;
    }
    // merge
    count += TrivialMergeOne(*it);
    // resub
    TransductionBackup b;
    Save(b);
    for(unsigned i = 0; i < vPis.size(); i++) {
      if(vvFos[*it].empty()) {
        break;
      }
      int f = vPis[i] << 1;
      if(TryConnect(*it, f) || TryConnect(*it, f ^ 1)) {
        count--;
        int diff;
        if(fMspf) {
          Build();
          diff = Mspf(true, *it, f >> 1);
        } else {
          vPfUpdates[*it] = true;
          diff = Cspf(true, *it, f >> 1);
        }
        if(diff) {
          count += diff;
          if(!vvFos[*it].empty()) {
            vPfUpdates[*it] = true;
            count += fMspf? Mspf(true): Cspf(true);
          }
          Save(b);
        } else {
          Load(b);
          count++;
        }
      }
    }
    if(vvFos[*it].empty()) {
      continue;
    }
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    list<int> targets2 = vObjs;
    for(list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++) {
      if(vvFos[*it].empty()) {
        break;
      }
      if(!vMarks[*it2] && !vvFos[*it2].empty()) {
        int f = *it2 << 1;
        if(TryConnect(*it, f) || TryConnect(*it, f ^ 1)) {
          count--;
          int diff;
          if(fMspf) {
            Build();
            diff = Mspf(true, *it, f >> 1);
          } else {
            vPfUpdates[*it] = true;
            diff = Cspf(true, *it, f >> 1);
          }
          if(diff) {
            count += diff;
            if(!vvFos[*it].empty()) {
              vPfUpdates[*it] = true;
              count += fMspf? Mspf(true): Cspf(true);
            }
            Save(b);
          } else {
            Load(b);
            count++;
          }
        }
      }
    }
    if(vvFos[*it].empty()) {
      continue;
    }
    // decompose
    if(vvFis[*it].size() > 2) {
      list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
      int pos = nObjsAlloc;
      count += TrivialDecomposeOne(it2, pos);
    }
  }
  return count;
}

int Transduction::RepeatResub(bool fMono, bool fMspf) {
  int count = 0;
  while(int diff = fMono? ResubMono(fMspf): Resub(fMspf)) {
    count += diff;
  }
  return count;
}

int Transduction::RepeatResubInner(bool fMspf, bool fInner) {
  int count = 0;
  while(int diff = RepeatResub(true, fMspf) + RepeatResub(false, fMspf)) {
    count += diff;
    if(!fInner) {
      break;
    }
  }
  return count;
}

int Transduction::RepeatResubOuter(bool fMspf, bool fInner, bool fOuter) {
  int count = 0;
  while(int diff = fMspf? RepeatResubInner(false, fInner) + RepeatResubInner(true, fInner): RepeatResubInner(false, fInner)) {
    count += diff;
    if(!fOuter) {
      break;
    }
  }
  return count;
}

int Transduction::Optimize(bool fFirstMerge, bool fMspfMerge, bool fMspfResub, bool fInner, bool fOuter) {
  TransductionBackup b;
  Save(b);
  int count = 0;
  int diff = 0;
  if(fFirstMerge) {
    diff = Merge(fMspfMerge) + Decompose();
  }
  diff += RepeatResubOuter(fMspfResub, fInner, fOuter);
  if(diff > 0) {
    count = diff;
    Save(b);
    diff = 0;
  }
  while(true) {
    diff += Merge(fMspfMerge) + Decompose() + RepeatResubOuter(fMspfResub, fInner, fOuter);
    if(diff > 0) {
      count += diff;
      Save(b);
      diff = 0;
    } else {
      Load(b);
      break;
    }
  }
  return count;
}

}

Gia_Man_t * Gia_ManTransductionTest(Gia_Man_t * pGia, int fCspf, int fRandom, int nSortType, int nPiShuffle) {
  srand(time(NULL));
  if(fRandom) {
    nSortType = rand() % 4;
    nPiShuffle = rand();
  }
  cout << "nSortType = " << nSortType << "; nPiShuffle = " << nPiShuffle << ";" << endl;
  // prepare tests
  int N = 100;
  int M = 11;
  if(fCspf) {
    N = 10;
    M = 7;
  }
  vector<int> Tests;
  for(int i = 0; i < N; i++) {
    Tests.push_back(rand() % M);
  }
  cout << "Tests = {";
  string delim;
  for(unsigned i = 0; i < Tests.size(); i++) {
    cout << delim << Tests[i];
    delim = ", ";
  }
  cout << "};" << endl;
  // init
  Transduction::Transduction t(pGia, 0, nSortType);
  if(nPiShuffle) {
    t.ShufflePis(nPiShuffle);
  }
  int nodes = t.CountNodes();
  int count = t.CountWires();
  Transduction::TransductionBackup b;
  t.Save(b);
  // transduction
  for(unsigned i = 0; i < Tests.size(); i++) {
    switch(Tests[i]) {
    case 0:
      count -= t.TrivialMerge();
      if(t.State() == Transduction::PfState::cspf) {
        assert(!t.CspfDebug());
      } else if(t.State() == Transduction::PfState::mspf) {
        assert(!t.MspfDebug());
      }
      break;
    case 1:
      count -= t.TrivialDecompose();
      if(t.State() == Transduction::PfState::cspf) {
        assert(!t.CspfDebug());
      } else if(t.State() == Transduction::PfState::mspf) {
        assert(!t.MspfDebug());
      }
      break;
    case 2:
      count -= t.Decompose();
      if(t.State() == Transduction::PfState::cspf) {
        count -= t.Cspf(true);
        assert(!t.CspfDebug());
      } else if(t.State() == Transduction::PfState::mspf) {
        count -= t.Mspf();
        assert(!t.MspfDebug());
      }
      break;
    case 3:
      count -= t.Cspf(true);
      assert(!t.CspfDebug());
      break;
    case 4:
      count -= t.Resub();
      assert(!t.CspfDebug());
      break;
    case 5:
      count -= t.ResubMono();
      assert(!t.CspfDebug());
      break;
    case 6:
      count -= t.Merge();
      assert(!t.CspfDebug());
      break;
    case 7:
      count -= t.Mspf(true);
      assert(!t.MspfDebug());
      break;
    case 8:
      count -= t.Resub(true);
      assert(!t.MspfDebug());
      break;
    case 9:
      count -= t.ResubMono(true);
      assert(!t.MspfDebug());
      break;
    case 10:
      count -= t.Merge(true);
      assert(!t.MspfDebug());
      break;
    }
    cout << "Test " << setw(2) << Tests[i] << " : ";
    t.PrintStats();
    assert(t.Verify());
    assert(count == t.CountWires());
    if(t.CountNodes() < nodes) {
      nodes = t.CountNodes();
      t.Save(b);
    }
  }
  // write
  t.Load(b);
  cout << "Best    : ";
  t.PrintStats();
  return t.Aig();
}


ABC_NAMESPACE_IMPL_END
