#ifdef _WIN32
#ifndef __MINGW32__
#pragma warning(disable : 4786) // warning C4786: identifier was truncated to '255' characters in the browser information
#endif
#endif

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

}

Gia_Man_t * Gia_ManTransductionTest(Gia_Man_t * pGia) {
  Gia_Man_t * pNew = NULL;
  Transduction::Transduction t(pGia);
  pNew = t.Aig();
  return pNew;
}


ABC_NAMESPACE_IMPL_END
