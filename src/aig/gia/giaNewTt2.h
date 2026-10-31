/**CFile****************************************************************

  FileName    [giaNewTt2.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experimental single-threaded transduction optimization.]

  Author      [Yukio Miyasaka and ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 30, 2026.]

  Description [Based on the original transduction implementation of May 2023.]

***********************************************************************/

#ifndef ABC__aig__gia__giaNewTt2_h
#define ABC__aig__gia__giaNewTt2_h
#include "misc/util/abc_print.h"

#include <cstdlib>
#include <cassert>
#include <algorithm>
#include <limits>
#include <iomanip>
#include <iostream>
#include <vector>
#include <bitset>
#include <list>

ABC_NAMESPACE_CXX_HEADER_START

namespace NewTt2 {

  typedef int                bvar;
  typedef unsigned           lit;
  typedef unsigned short     ref;
  typedef unsigned long long size;

  static inline bvar BvarMax() { return std::numeric_limits<bvar>::max(); }
  static inline lit  LitMax()  { return std::numeric_limits<lit>::max();  }
  static inline ref  RefMax()  { return std::numeric_limits<ref>::max();  }
  static inline size SizeMax() { return std::numeric_limits<size>::max(); }

  static void fatal_error(const char* message) {
    ABC_PRINT_STREAM( stderr, true, message << "\n" );
    std::abort();
  }

  struct Param {
    int  nObjsAllocLog;
    int  nObjsMaxLog;
    int  nVerbose;
    bool fCountOnes;
    int  nGbc;
    int  nReo; // dummy
    std::vector<int> *pVar2Level; // dummy
    Param() {
      nObjsAllocLog = 10;
      nObjsMaxLog   = 20;
      nVerbose      = 0;
      fCountOnes    = false;
      nGbc          = 0;
      nReo          = BvarMax();
    }
  };

  class Man {
  private:
    typedef unsigned long long word;
    typedef std::bitset<64> bsw;
    static inline int ww() { return 64; } // word width
    static inline int lww() { return 6; } // log word width
    static inline word one() {return 0xffffffffffffffffull; }
    static inline word vars(int i) {
      static const word vars[] = {0xaaaaaaaaaaaaaaaaull,
                                  0xccccccccccccccccull,
                                  0xf0f0f0f0f0f0f0f0ull,
                                  0xff00ff00ff00ff00ull,
                                  0xffff0000ffff0000ull,
                                  0xffffffff00000000ull};
      return vars[i];
    }
    static inline word ones(int i) {
      static const word ones[] = {0x0000000000000001ull,
                                  0x0000000000000003ull,
                                  0x000000000000000full,
                                  0x00000000000000ffull,
                                  0x000000000000ffffull,
                                  0x00000000ffffffffull,
                                  0xffffffffffffffffull};
      return ones[i];
    }

  private:
    int  nVars;
    bvar nObjs;
    bvar nObjsAlloc;
    bvar nObjsMax;
    size nSize;
    size nTotalSize;
    std::vector<word> vVals;
    mutable std::vector<size> vOneCounts;
    std::vector<bvar> vDeads;
    std::vector<ref>  vRefs;
    // Cone simulation uses unowned word buffers; it never allocates table
    // literals while pointers into the table arena are live.
    std::vector<word> vSim;
    std::vector<unsigned char> vSimValid, vSimPending;
    int nGbc;
    int nVerbose;

  public:
    inline lit  Bvar2Lit(bvar a)          const { return (lit)a << 1;        }
    inline bvar Lit2Bvar(lit x)           const { return (bvar)(x >> 1);     }
    inline lit  IthVar(int v)             const { return ((lit)v + 1) << 1;  }
    inline lit  LitNot(lit x)             const { return x ^ (lit)1;         }
    inline lit  LitNotCond(lit x, bool c) const { return x ^ (lit)c;         }
    inline bool LitIsCompl(lit x)         const { return x & (lit)1;         }
    inline ref  Ref(lit x)                const { return vRefs[Lit2Bvar(x)]; }
    inline lit  Const0()                  const { return (lit)0;             }
    inline lit  Const1()                  const { return (lit)1;             }
    inline bool IsConst0(lit x)           const {
      bvar a = Lit2Bvar(x);
      word c = LitIsCompl(x)? one(): 0;
      for(size j = 0; j < nSize; j++)
        if(vVals[nSize * a + j] ^ c)
          return false;
      return true;
    }
    inline bool IsConst1(lit x)           const {
      bvar a = Lit2Bvar(x);
      word c = LitIsCompl(x)? one(): 0;
      for(size j = 0; j < nSize; j++)
        if(~(vVals[nSize * a + j] ^ c))
          return false;
      return true;
    }
    inline bool LitIsEq(lit x, lit y)     const {
      if(x == y)
        return true;
      if(x == LitMax() || y == LitMax())
        return false;
      bvar xvar = Lit2Bvar(x);
      bvar yvar = Lit2Bvar(y);
      word c = LitIsCompl(x) ^ LitIsCompl(y)? one(): 0;
      for(size j = 0; j < nSize; j++)
        if(vVals[nSize * xvar + j] ^ vVals[nSize * yvar + j] ^ c)
          return false;
      return true;
    }
    // Test the implication directly, without allocating a result table.
    bool OrIsConst1(lit x, lit y) const {
      size a = nSize * Lit2Bvar(x), b = nSize * Lit2Bvar(y);
      word cx = LitIsCompl(x) ? one() : 0;
      word cy = LitIsCompl(y) ? one() : 0;
      for(size j = 0; j < nSize; j++)
        if(((vVals[a + j] ^ cx) | (vVals[b + j] ^ cy)) != one())
          return false;
      return true;
    }
    bool OrIsConst1(lit x, lit y, lit z) const {
      size a = nSize * Lit2Bvar(x), b = nSize * Lit2Bvar(y), c = nSize * Lit2Bvar(z);
      word cx = LitIsCompl(x) ? one() : 0;
      word cy = LitIsCompl(y) ? one() : 0;
      word cz = LitIsCompl(z) ? one() : 0;
      for(size j = 0; j < nSize; j++)
        if(((vVals[a + j] ^ cx) | (vVals[b + j] ^ cy) | (vVals[c + j] ^ cz)) != one())
          return false;
      return true;
    }
    inline size OneCount(lit x) const {
      bvar a = Lit2Bvar(x);
      size count = vOneCounts[a];
      if(count == SizeMax()) {
        count = 0;
        if(nVars > 6) {
          for(size j = 0; j < nSize; j++)
            count += bsw(vVals[nSize * a + j]).count();
        } else {
          count = bsw(vVals[nSize * a] & ones(nVars)).count();
        }
        vOneCounts[a] = count;
      }
      return LitIsCompl(x) ? ((size)1 << nVars) - count : count;
    }

    // Flip one node and intersect the output observability conditions in a
    // scratch arena. All graph functions and care masks are owned by the caller.
    // Only the final don't-care table needs a managed, reference-counted slot.
    template<class Adjacency>
    bool MspfG(int root, const std::list<int> &order,
               const Adjacency &fis,
               const Adjacency &fos,
               const std::vector<lit> &fs, const std::vector<int> &pos,
               const std::vector<lit> &pofs,
               const std::vector<std::vector<lit> > &cs, lit &g) {
      const size count = nSize;
      // Large forced-table runs retain the generic reference-counted path.
      if(fs.size() > (32u * 1024u * 1024u / sizeof(word)) / count)
        return false;
      bvar result = AllocNode();
      vSim.resize(fs.size() * count);
      vSimValid.assign(fs.size(), 0);
      vSimPending.assign(fs.size(), 0);
      const word *input = vVals.data() + count * Lit2Bvar(fs[root]);
      word *row = vSim.data() + count * root;
      word phase = LitIsCompl(fs[root]) ? 0 : one();
      for(size w = 0; w < count; ++w)
        row[w] = input[w] ^ phase;
      vSimValid[root] = 1;
      for(size_t j = 0; j < fos[root].size(); ++j)
        vSimPending[fos[root][j]] = 1;
      for(std::list<int>::const_iterator it = order.begin(); it != order.end(); ++it) {
        int node = *it;
        if(!vSimPending[node])
          continue;
        row = vSim.data() + count * node;
        assert(!fis[node].empty());
        int f0 = fis[node][0], k0 = f0 >> 1;
        input = vSimValid[k0] ? vSim.data() + count * k0 :
                               vVals.data() + count * Lit2Bvar(fs[k0]);
        phase = ((f0 & 1) ^ (!vSimValid[k0] && LitIsCompl(fs[k0]))) ? one() : 0;
        size_t first = 1;
        if(fis[node].size() > 1) {
          int f1 = fis[node][1], k1 = f1 >> 1;
          const word *other = vSimValid[k1] ? vSim.data() + count * k1 :
                                            vVals.data() + count * Lit2Bvar(fs[k1]);
          word otherPhase = ((f1 & 1) ^ (!vSimValid[k1] && LitIsCompl(fs[k1]))) ? one() : 0;
          for(size w = 0; w < count; ++w)
            row[w] = (input[w] ^ phase) & (other[w] ^ otherPhase);
          first = 2;
        } else {
          for(size w = 0; w < count; ++w)
            row[w] = input[w] ^ phase;
        }
        for(size_t j = first; j < fis[node].size(); ++j) {
          int f = fis[node][j], k = f >> 1;
          input = vSimValid[k] ? vSim.data() + count * k :
                                vVals.data() + count * Lit2Bvar(fs[k]);
          phase = ((f & 1) ^ (!vSimValid[k] && LitIsCompl(fs[k]))) ? one() : 0;
          for(size w = 0; w < count; ++w)
            row[w] &= input[w] ^ phase;
        }
        vSimValid[node] = 1;
        input = vVals.data() + count * Lit2Bvar(fs[node]);
        phase = LitIsCompl(fs[node]) ? one() : 0;
        bool different = false;
        for(size w = 0; w < count; ++w)
          if(row[w] != (input[w] ^ phase)) {
            different = true;
            break;
          }
        if(different)
          for(size_t j = 0; j < fos[node].size(); ++j)
            vSimPending[fos[node][j]] = 1;
      }
      word *output = vVals.data() + count * result;
      std::fill(output, output + count, one());
      for(size_t j = 0; j < pos.size(); ++j) {
        int f = fis[pos[j]][0], k = f >> 1;
        if(!vSimValid[k])
          continue;
        row = vSim.data() + count * k;
        input = vVals.data() + count * Lit2Bvar(pofs[j]);
        lit care = cs[pos[j]][0];
        const word *dc = vVals.data() + count * Lit2Bvar(care);
        word dcPhase = LitIsCompl(care) ? one() : 0;
        phase = ((f & 1) ^ LitIsCompl(pofs[j])) ? one() : 0;
        word nonzero = 0;
        for(size w = 0; w < count; ++w) {
          output[w] &= ~(row[w] ^ input[w] ^ phase) | (dc[w] ^ dcPhase);
          nonzero |= output[w];
        }
        if(!nonzero) {
          g = Const0();
          return true;
        }
      }
      g = IsConst1(Bvar2Lit(result)) ? Const1() : Bvar2Lit(result);
      return true;
    }

  public:
    inline void IncRef(lit x) { if(!vRefs.empty() && Ref(x) != RefMax()) vRefs[Lit2Bvar(x)]++; }
    inline void DecRef(lit x) { if(!vRefs.empty() && Ref(x) != RefMax()) vRefs[Lit2Bvar(x)]--; }

  public:
    bool Resize() {
      if(nObjsAlloc == nObjsMax)
        return false;
      lit nObjsAllocLit = (lit)nObjsAlloc << 1;
      if(nObjsAllocLit > (lit)BvarMax())
        nObjsAlloc = BvarMax();
      else
        nObjsAlloc = (bvar)nObjsAllocLit;
      nTotalSize = nTotalSize << 1;
      if(nVerbose >= 2)
        ABC_PRINT_STREAM( stdout, true, "Reallocating " << nObjsAlloc << " nodes" << "\n" );
      vVals.resize(nTotalSize);
      vOneCounts.resize(nObjsAlloc, SizeMax());
      if(!vRefs.empty())
        vRefs.resize(nObjsAlloc);
      return true;
    }
    bool Gbc() {
      if(nVerbose >= 2)
        { printf( "Garbage collect\n" ); fflush( stdout ); }
      for(bvar a = nVars + 1; a < nObjs; a++)
        if(!vRefs[a])
          vDeads.push_back(a);
      return vDeads.size();
    }

  public:
    Man(int nVars, Param p): nVars(nVars) {
      if(p.nObjsMaxLog < p.nObjsAllocLog)
        fatal_error("nObjsMax must not be smaller than nObjsAlloc");
      if(nVars >= lww())
        nSize = 1ull << (nVars - lww());
      else
        nSize = 1;
      if(!nSize)
        fatal_error("Memout (nVars) in init");
      if(!(nSize << p.nObjsMaxLog))
        fatal_error("Memout (nObjsMax) in init");
      lit nObjsMaxLit = (lit)1 << p.nObjsMaxLog;
      if(!nObjsMaxLit)
        fatal_error("Memout (nObjsMax) in init");
      if(nObjsMaxLit > (lit)BvarMax())
        nObjsMax = BvarMax();
      else
        nObjsMax = (bvar)nObjsMaxLit;
      lit nObjsAllocLit = (lit)1 << p.nObjsAllocLog;
      if(!nObjsAllocLit)
        fatal_error("Memout (nObjsAlloc) in init");
      if(nObjsAllocLit > (lit)BvarMax())
        nObjsAlloc = BvarMax();
      else
        nObjsAlloc = (bvar)nObjsAllocLit;
      if(nObjsAlloc <= (bvar)nVars)
        fatal_error("nObjsAlloc must be larger than nVars");
      nTotalSize = nSize << p.nObjsAllocLog;
      vVals.resize(nTotalSize);
      vOneCounts.resize(nObjsAlloc, SizeMax());
      if(p.fCountOnes && nVars > 63)
        fatal_error("nVars must be less than 64 to count ones");
      nObjs = 1;
      for(int i = 0; i < 6 && i < nVars; i++) {
        for(size j = 0; j < nSize; j++)
          vVals[nSize * nObjs + j] = vars(i);
        nObjs++;
      }
      for(int i = 0; i < nVars - 6; i++) {
        for(size j = 0; j < nSize; j += (2ull << i))
          for(size k = 0; k < (1ull << i); k++)
            vVals[nSize * nObjs + j + k] = one();
        nObjs++;
      }
      nVerbose = p.nVerbose;
      nGbc = p.nGbc;
      if(nGbc || p.nReo != BvarMax())
        vRefs.resize(nObjsAlloc);
    }
    // Recycle unreferenced slots before growing the table arena.
    bvar AllocNode() {
      if(nObjs >= nObjsAlloc && vDeads.empty()) {
        bool fRemoved = false;
        if(nGbc > 1)
          fRemoved = Gbc();
        if(!fRemoved && !Resize() && (nGbc != 1 || !Gbc()))
          fatal_error("Memout (node)");
      }
      bvar zvar;
      if(nObjs < nObjsAlloc)
        zvar = nObjs++;
      else
        zvar = vDeads.back(), vDeads.resize(vDeads.size() - 1);
      vOneCounts[zvar] = SizeMax();
      return zvar;
    }
    inline lit Xor(lit x, lit y) {
      if(x == y) return Const0();
      if(x == LitNot(y)) return Const1();
      if(x == Const0()) return y;
      if(y == Const0()) return x;
      bvar a = Lit2Bvar(x), b = Lit2Bvar(y), c = AllocNode();
      word phase = LitIsCompl(x) != LitIsCompl(y) ? one() : 0;
      const word *pa = vVals.data() + nSize * a;
      const word *pb = vVals.data() + nSize * b;
      word *pc = vVals.data() + nSize * c;
      const size count = nSize;
      for(size j = 0; j < count; j++)
        pc[j] = pa[j] ^ pb[j] ^ phase;
      return Bvar2Lit(c);
    }
    inline lit And(lit x, lit y) {
      if(x == y || y == Const1()) return x;
      if(x == Const1()) return y;
      if(x == Const0() || y == Const0() || x == LitNot(y)) return Const0();
      bvar xvar = Lit2Bvar(x);
      bvar yvar = Lit2Bvar(y);
      word xcompl = LitIsCompl(x)? one(): 0;
      word ycompl = LitIsCompl(y)? one(): 0;
      unsigned j;
      bvar zvar = AllocNode();
      const word *px = vVals.data() + nSize * xvar;
      const word *py = vVals.data() + nSize * yvar;
      word *pz = vVals.data() + nSize * zvar;
      const size count = nSize;
      for(j = 0; j < count; j++)
        pz[j] = (px[j] ^ xcompl) & (py[j] ^ ycompl);
      return zvar << 1;
    }
    inline lit Or(lit x, lit y) {
      return LitNot(And(LitNot(x), LitNot(y)));
    }
    void Reorder() {} // dummy

  public:
    void SetRef(std::vector<lit> const &vLits) {
      vRefs.clear();
      vRefs.resize(nObjsAlloc);
      for(size_t i = 0; i < vLits.size(); i++)
        IncRef(vLits[i]);
    }
    void RemoveRefIfUnused() {
      if(!nGbc)
        vRefs.clear();
    }
    void TurnOffReo() {}
    int GetNumVars() const {
      return nVars;
    }
    void PrintNode(lit x) const {
      bvar a = Lit2Bvar(x);
      word c = LitIsCompl(x)? one(): 0;
      for(size j = 0; j < nSize; j++)
        ABC_PRINT_STREAM( stdout, false, bsw(vVals[nSize * a + j] ^ c) );
      { printf( "\n" ); fflush( stdout ); }
    }
  };

}

ABC_NAMESPACE_CXX_HEADER_END

#endif
