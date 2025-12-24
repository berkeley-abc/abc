/**CFile****************************************************************

  FileName    [rewireMiaig.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Re-wiring.]

  Synopsis    []

  Author      [Jiun-Hao Chen]
  
  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rewireMiaig.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef REWIRE_MIAIG_H
#define REWIRE_MIAIG_H

#define RW_ABC

#ifdef RW_ABC
#include "base/abc/abc.h"
#include "aig/miniaig/miniaig.h"
#include "rewireMap.h"
#define RW_INT_MAX ABC_INT_MAX
#define Rw_MaxInt Abc_MaxInt
#define Rw_MinInt Abc_MinInt
#define Rw_Var2Lit Abc_Var2Lit
#define Rw_Lit2Var Abc_Lit2Var
#define Rw_LitIsCompl Abc_LitIsCompl
#define Rw_LitNot Abc_LitNot
#define Rw_LitNotCond Abc_LitNotCond
#define Rw_LitRegular Abc_LitRegular
#else
#ifdef _WIN32
typedef unsigned __int64 word;   // 32-bit windows
#else
typedef long long unsigned word; // other platforms
#endif
#ifdef _WIN32
typedef __int64 iword;   // 32-bit windows
#else
typedef long long iword; // other platforms
#endif
#define RW_INT_MAX (2147483647)
static inline int Rw_MaxInt( int a, int b )       { return a > b ?  a : b; }
static inline int Rw_MinInt( int a, int b )       { return a < b ?  a : b; }
static inline int Rw_Var2Lit( int Var, int c )    { assert(Var >= 0 && !(c >> 1)); return Var + Var + c;        }
static inline int Rw_Lit2Var( int Lit )           { assert(Lit >= 0); return Lit >> 1;                          }
static inline int Rw_LitIsCompl( int Lit )        { assert(Lit >= 0); return Lit & 1;                           }
static inline int Rw_LitNot( int Lit )            { assert(Lit >= 0); return Lit ^ 1;                           }
static inline int Rw_LitNotCond( int Lit, int c ) { assert(Lit >= 0); return Lit ^ (int)(c > 0);                }
static inline int Rw_LitRegular( int Lit )        { assert(Lit >= 0); return Lit & ~01;                         }
#endif // RW_ABC
#include "rewireVec.h"
#include "rewireTt.h"
#include "rewireTime.h"


#include <vector>
#include <algorithm>

#ifdef RW_ABC
ABC_NAMESPACE_CXX_HEADER_START
#endif // RW_ABC

namespace Rewire {

#if RW_THREADS
// exchange-add operation for atomic operations on reference counters
#if defined __riscv && !defined __riscv_atomic
// riscv target without A extension
static inline int RW_XADD(int *addr, int delta) {
    int tmp = *addr;
    *addr += delta;
    return tmp;
}
#elif defined __INTEL_COMPILER && !(defined WIN32 || defined _WIN32)
// atomic increment on the linux version of the Intel(tm) compiler
#define RW_XADD(addr, delta)    \
    (int)_InterlockedExchangeAdd( \
        const_cast<void *>(reinterpret_cast<volatile void *>(addr)), delta)
#elif defined __GNUC__
#if defined __clang__ && __clang_major__ >= 3 && !defined __ANDROID__ && !defined __EMSCRIPTEN__ && !defined(__CUDACC__)
#ifdef __ATOMIC_ACQ_REL
#define RW_XADD(addr, delta) \
    __c11_atomic_fetch_add((_Atomic(int) *)(addr), delta, __ATOMIC_ACQ_REL)
#else
#define RW_XADD(addr, delta) \
    __atomic_fetch_add((_Atomic(int) *)(addr), delta, 4)
#endif
#else
#if defined __ATOMIC_ACQ_REL && !defined __clang__
// version for gcc >= 4.7
#define RW_XADD(addr, delta)                                     \
    (int)__atomic_fetch_add((unsigned *)(addr), (unsigned)(delta), \
                            __ATOMIC_ACQ_REL)
#else
#define RW_XADD(addr, delta) \
    (int)__sync_fetch_and_add((unsigned *)(addr), (unsigned)(delta))
#endif
#endif
#elif defined _MSC_VER && !defined RC_INVOKED
#define RW_XADD(addr, delta) \
    (int)_InterlockedExchangeAdd((long volatile *)addr, delta)
#else
// thread-unsafe branch
static inline int RW_XADD(int *addr, int delta) {
    int tmp = *addr;
    *addr += delta;
    return tmp;
}
#endif
#else  // RW_THREADS
static inline int RW_XADD(int *addr, int delta) {
    int tmp = *addr;
    *addr += delta;
    return tmp;
}
#endif // RW_THREADS

#define Miaig_CustomForEachConstInput(p, i)         for (i = 0; i <= p->nIns; i++)
#define Miaig_CustomForEachInput(p, i)              for (i = 1; i <= p->nIns; i++)
#define Miaig_CustomForEachNode(p, i)               for (i = 1 + p->nIns; i < p->nObjs - p->nOuts; i++)
#define Miaig_CustomForEachNodeReverse(p, i)        for (i = p->nObjs - p->nOuts - 1; i > 1 + p->nIns; i--)
#define Miaig_CustomForEachInputNode(p, i)          for (i = 1; i < p->nObjs - p->nOuts; i++)
#define Miaig_CustomForEachNodeStart(p, i, s)       for (i = s; i < p->nObjs - p->nOuts; i++)
#define Miaig_CustomForEachOutput(p, i)             for (i = p->nObjs - p->nOuts; i < p->nObjs; i++)
#define Miaig_CustomForEachNodeOutput(p, i)         for (i = 1 + p->nIns; i < p->nObjs; i++)
#define Miaig_CustomForEachNodeOutputStart(p, i, s) for (i = s; i < p->nObjs; i++)
#define Miaig_CustomForEachObj(p, i)                for (i = 0; i < p->nObjs; i++)
#define Miaig_CustomForEachObjFanin(p, i, iLit, k)  Vi_ForEachEntry(&p->pvFanins[i], iLit, k)

#define Miaig_ForEachConstInput(i)         for (i = 0; i <= _data->nIns; i++)
#define Miaig_ForEachInput(i)              for (i = 1; i <= _data->nIns; i++)
#define Miaig_ForEachNode(i)               for (i = 1 + _data->nIns; i < _data->nObjs - _data->nOuts; i++)
#define Miaig_ForEachNodeReverse(i)        for (i = _data->nObjs - p->nOuts - 1; i > 1 + _data->nIns; i--)
#define Miaig_ForEachInputNode(i)          for (i = 1; i < _data->nObjs - _data->nOuts; i++)
#define Miaig_ForEachNodeStart(i, s)       for (i = s; i < _data->nObjs - _data->nOuts; i++)
#define Miaig_ForEachOutput(i)             for (i = _data->nObjs - _data->nOuts; i < _data->nObjs; i++)
#define Miaig_ForEachNodeOutput(i)         for (i = 1 + _data->nIns; i < _data->nObjs; i++)
#define Miaig_ForEachNodeOutputStart(i, s) for (i = s; i < _data->nObjs; i++)
#define Miaig_ForEachObj(i)                for (i = 0; i < _data->nObjs; i++)
#define Miaig_ForEachObjFanin(i, iLit, k)  Vi_ForEachEntry(&_data->pvFanins[i], iLit, k)
#define Miaig_ForEachObjFanout(i, iVar, k)  Vi_ForEachEntry(&_data->pvFanouts[i], iVar, k)
#define Miaig_ForEachObjFaninStart(i, iLit, k, s)  Vi_ForEachEntryStart(&_data->pvFanins[i], iLit, k, s)

static inline int Rw_Lit2LitV(int *pMapV2V, int Lit) {
    assert(Lit >= 0);
    return Rw_Var2Lit(pMapV2V[Rw_Lit2Var(Lit)], Rw_LitIsCompl(Lit));
}

static inline int Rw_Lit2LitL(int *pMapV2L, int Lit) {
    assert(Lit >= 0);
    return Rw_LitNotCond(pMapV2L[Rw_Lit2Var(Lit)], Rw_LitIsCompl(Lit));
}

struct Miaig_Data {
    char *pName;           // network name
    int refcount;          // Reference counter
    int nIns;              // primary inputs
    int nOuts;             // primary outputs
    int nObjs;             // all objects
    int nObjsAlloc;        // allocated space
    int nWords;            // the truth table size
    int nTravIds;          // traversal ID counter
    int *pTravIds;         // traversal IDs
    int *pCopy;            // temp copy
    int *pRefs;            // reference counters
    int minLevel;          // minimum level
    int *pLevel;           // levels
    int *pDist;            // distances
    int *pRequire;         // required times
    word *pTruths[3];      // truth tables
    word *pCare;           // careset
    word *pProd;           // product
    word *pExc;            // Exc 
    vi *vOrder;            // node order
    vi *vOrderF;           // fanin order
    vi *vOrderF2;          // fanin order
    vi *vTfo;              // transitive fanout cone
    vi *pvFanins;          // the array of objects' fanins (literal)
    vi *pvFanouts;         // the array of objects' fanouts (variable)
    vi *vCiArrs;           // the arrival times of CIs (if provided) not owned
    vi *vCoReqs;           // the required times of COs (if provided) not owned
    vi *vTfoArrs;          // the TFO of each
    int *pTable;           // structural hashing table
    int TableSize;         // the size of the hash table
    float objectiveValue;  // objective value
    vi *pNtkMapped;        // mapped network
};

class Miaig {
public:
    Miaig(void);
    ~Miaig(void);
    Miaig(const Miaig &m);
    Miaig &operator=(const Miaig &m);
    Miaig(int nIns, int nOuts, int nObjsAlloc);
#ifdef RW_ABC
    Miaig(Gia_Man_t *pGia);
    Miaig(Abc_Ntk_t *pNtk);
    Miaig(Mini_Aig_t *pMiniAig);
#endif // RW_ABC

public:
#ifdef RW_ABC
    void setExc(Gia_Man_t *pExc);
#endif // RW_ABC

public:
    void addref(void);
    void release(void);
    bool operator==(const Miaig &m) const;

private:
    void create(int nIns, int nOuts, int nObjsAlloc);

public:
    int fromGia(Gia_Man_t *pGia);
    int fromMiniAig(Mini_Aig_t *pMiniAig);

public:
    int &nIns(void);
    int &nOuts(void);
    int &nObjs(void);
    int &nObjsAlloc(void);
    int objIsPi(int i);
    int objIsPo(int i);
    int objIsNode(int i);
    int objPiIdx(int i); // No check isPi
    int objPoIdx(int i); // No check isPo
    void print(void);
    void printNode(int i);
    int appendObj(void);
    void setFanin(int i, int iLit);
    void appendFanin(int i, int iLit);
    int objFaninNum(int i);
    int objFanin0(int i);
    int objFanin1(int i);
    int &objLevel(int i);
    int &objRef(int i);
    int &objTravId(int i);
    int &objCopy(int i);
    int &objDist(int i);
    int &objRequire(int i);
    int &nTravIds(void);
    word *objTruth(int i, int n);
    vi *objFanins(int i);
    vi *objFanouts(int i);
    int objType(int i);
    int nWords(void);
    void refObj(int iObj);
    void derefObj(int iObj);
    void derefObj_rec(int iObj, int iLitSkip);
    void setName(char *pName);
    void setMapped(Vec_Int_t *vMapping, float objectiveValue = 0.0f);
    void attachTiming(vi *vCiArrs, vi *vCoReqs);
    void checkTiming(vi *vCiArrs, vi *vCoReqs);

private:
    int initializeLevels_rec(int iObj);
    void updateLevels_rec(int iObj);
    void initializeLevels(void);
    void initializeRefs(void);
    void verifyRefs(void);
    void initializeTruth(void);
    void initializeDists(void);
    void initializeFanouts(void);
    void initializeRequire_rec(int iObj);
    void updateRequire_rec(int iObj);
    void initializeRequire(void);

private:
    void markDfs_rec(int iObj);
    int markDfs(void);
    void markDistanceN_rec(int iObj, int n, int limit);
    void markDistanceN(int Obj, int n);
    void topoCollect_rec(int iObj);
    vi *topoCollect(void);
    void reduceFanins(vi *v);
    int *createStops(void);
    void collectSuper_rec(int iLit, int *pStop, vi *vSuper);
    int checkConst(int iObj, word *pCare, word *pExc, int fCheck, int fVerbose);
    void truthSimNode(int i);
    word *truthSimNodeSubset(int i, int m);
    word *truthSimNodeSubset2(int i, vi *vFanins, int nFanins);
    void truthUpdate(vi *vTfo, word *pExc = NULL, int fCheck = 0);
    int computeTfo_rec(int iObj);
    vi *computeTfo(int iObj);
    word *computeCareSet(int iObj, word *pExc = NULL);
    vi *createRandomOrder(void);
    void addPair(vi *vPair, int iFan1, int iFan2);
    int findPair(vi *vPair);
    int updateFanins(vi *vFans, int iFan1, int iFan2, int iLit);
    void extractBest(vi *vPairs);
    vi *findPairs(word *pSto, int nWords);
    int findShared(int nNewNodesMax);
    int hashTwo(int l0, int l1, int TableSize);
    int *hashLookup(int *pTable, int l0, int l1, int TableSize);

public:
    float countAnd2(int reset = 0, int fDummy1 = 0, int fDummy2 = 0);
    float countLevel(int reset = 0, int fDummy1 = 0, int fDummy2 = 0);
    // 0: amap 1: &nf 2: &simap
    float countMappedArea(int reset = 0, int nMode = 0, int fDch = 1);
    float countMappedDelay(int reset = 0, int nMode = 0, int fDch = 1);

private:
    void dupDfs_rec(Miaig &pNew, int iObj);
    int buildNodeBalance_rec(Miaig &pNew, vi *vFanins, int begin, int end, int fCprop, int fStrash);

private:
    int buildNode(int l0, int l1, int fCprop, int fStrash);
    int buildNodeBalance(Miaig &pNew, vi *vFanins, int fCprop, int fStrash);
    int buildNodeCascade(Miaig &pNew, vi *vFanins, int fCprop, int fStrash);

private:
    void expandOneHeuristicSort(int *pOrderF, int fTiming);
    void reduceOneHeuristicSort(int *pOrderF, int fTiming);
    int expandOne(int iObj, int nAddedMax, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose);
    int reduceOne(int iObj, int fOnlyConst, int fOnlyBuffer, int fHeuristic, word *pExc, int fTiming, int fCheck, int fVerbose);
    int expandThenReduceOne(int iNode, int nFaninAddLimit, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose);

public:
    Miaig dup(int fRemDangle, int fFanout, int fMapped = 0);
    Miaig dupDfs(void);
    Miaig dupStrash(int fCprop, int fStrash, int fCascade, int fFanout = 0);
    Miaig dupMulti(int nFaninMax, int nGrowth);
    Miaig dupExtend(int nFaninMax, int nGrowth);
    Miaig expand(int nFaninAddLimitAll, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int nVerbose);
    Miaig share(int nNewNodesMax);
    Miaig reduce(word *pExc, int fTiming, int fCheck, int fVerbose);
    Miaig expandThenReduce(int nFaninAddLimit, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose);
    Miaig expandShareReduce(int nFaninAddLimitAll, int nDivs, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int nVerbose);
    Miaig rewire(int nIters, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int fCheck, Gia_ChMan_t *pChMan, int nVerbose);
#ifdef RW_ABC
    Gia_Man_t *toGia(void);
    Abc_Ntk_t *toNtk(int fMapped = 0);
    Mini_Aig_t *toMiniAig(void);
#endif // RW_ABC

private:
    int *_refcount;
    Miaig_Data *_data;
};

inline Miaig::Miaig(void)
    : _refcount(nullptr), _data(nullptr) {
}

inline Miaig::Miaig(int nIns, int nOuts, int nObjsAlloc)
    : Miaig() {
    create(nIns, nOuts, nObjsAlloc);
}

#ifdef RW_ABC
inline Miaig::Miaig(Gia_Man_t *pGia) : Miaig() {
    fromGia(pGia);
}

inline Miaig::Miaig(Abc_Ntk_t *pNtk) : Miaig() {
    Mini_Aig_t *pMiniAig = Abc_ManRewireMiniAigFromNtk(pNtk);
    fromMiniAig(pMiniAig);
    Mini_AigStop(pMiniAig);
}

inline Miaig::Miaig(Mini_Aig_t *pMiniAig) : Miaig() {
    fromMiniAig(pMiniAig);
}
#endif // RW_ABC

inline Miaig::~Miaig(void) {
    release();
}

inline Miaig::Miaig(const Miaig &m)
    : _refcount(m._refcount), _data(m._data) {
    addref();
}

inline Miaig &Miaig::operator=(const Miaig &m) {
    if (this == &m) {
        return *this;
    }

    if (m._refcount) {
        RW_XADD(m._refcount, 1);
    }

    release();

    _refcount = m._refcount;
    _data = m._data;

    return *this;
}

inline void Miaig::addref(void) {
    if (_refcount) {
        RW_XADD(_refcount, 1);
    }
}

inline void Miaig::release(void) {
    if (_refcount && RW_XADD(_refcount, -1) == 1) {
        if (_data) {
            if (_data->pName) free(_data->pName);
            for (int i = 0; i < _data->nObjsAlloc; ++i) {
                if (_data->pvFanins[i].ptr) {
                    free(_data->pvFanins[i].ptr);
                }
            }
            free(_data->pvFanins);
            if (_data->pvFanouts) {
                for (int i = 0; i < _data->nObjsAlloc; ++i) {
                    if (_data->pvFanouts[i].ptr) {
                        free(_data->pvFanouts[i].ptr);
                    }
                }
                free(_data->pvFanouts);
            }
            Vi_Free(_data->vOrder);
            Vi_Free(_data->vOrderF);
            Vi_Free(_data->vOrderF2);
            Vi_Free(_data->vTfo);
            free(_data->pTravIds);
            free(_data->pCopy);
            free(_data->pRefs);
            free(_data->pTruths[0]);
            if (_data->pCare) free(_data->pCare);
            if (_data->pProd) free(_data->pProd);
            if (_data->pExc) free(_data->pExc);
            if (_data->pLevel) free(_data->pLevel);
            if (_data->pDist) free(_data->pDist);
            if (_data->pRequire) free(_data->pRequire);
            if (_data->pTable) free(_data->pTable);
            if (_data->pNtkMapped) Vi_Free(_data->pNtkMapped);
            free(_data);
        }
    }

    _data = nullptr;
    _refcount = nullptr;
}

inline bool Miaig::operator==(const Miaig &m) const {
    return (_data == m._data);
}

inline int &Miaig::nIns(void) {
    return _data->nIns;
}

inline int &Miaig::nOuts(void) {
    return _data->nOuts;
}

inline int &Miaig::nObjs(void) {
    return _data->nObjs;
}

inline int &Miaig::nObjsAlloc(void) {
    return _data->nObjsAlloc;
}

inline int Miaig::objIsPi(int i) {
    return i > 0 && i <= nIns();
}

inline int Miaig::objIsPo(int i) {
    return i >= nObjs() - nOuts();
}

inline int Miaig::objIsNode(int i) {
    return i > nIns() && i < nObjs() - nOuts();
}

inline int Miaig::objPiIdx(int i) {
    // assert(objIsPi(i));
    return i - 1;
}

inline int Miaig::objPoIdx(int i) {
    // assert(objIsPo(i));
    return i - (nObjs() - nOuts());
}

inline int Miaig::appendObj(void) {
    assert(nObjs() < nObjsAlloc());
    return nObjs()++;
}

inline void Miaig::appendFanin(int i, int iLit) {
    Vi_PushOrder(objFanins(i), iLit);
    if (_data->pvFanouts) {
        Vi_PushOrder(objFanouts(Rw_Lit2Var(iLit)), i);
    }
}

inline void Miaig::setFanin(int iObj, int iLit1) {
    derefObj(iObj);
    if (_data->pvFanouts) {
        int iLit2, i;
        Miaig_ForEachObjFanin(iObj, iLit2, i) {
            if (Rw_Lit2Var(iLit1) == Rw_Lit2Var(iLit2)) continue;
            Vi_Remove(objFanouts(Rw_Lit2Var(iLit2)), iObj);
        }
    }
    Vi_Fill(objFanins(iObj), 1, iLit1);
    refObj(iObj);
}

inline int Miaig::objFaninNum(int i) {
    return Vi_Size(objFanins(i));
}

inline int Miaig::objFanin0(int i) {
    return Vi_Read(objFanins(i), 0);
}

inline int Miaig::objFanin1(int i) {
    assert(objFaninNum(i) == 2);
    return Vi_Read(objFanins(i), 1);
}

inline int &Miaig::objLevel(int i) {
    return _data->pLevel[i];
}

inline int &Miaig::objRef(int i) {
    return _data->pRefs[i];
}

inline int &Miaig::objTravId(int i) {
    return _data->pTravIds[i];
}

inline int &Miaig::objCopy(int i) {
    return _data->pCopy[i];
}

inline int &Miaig::objDist(int i) {
    return _data->pDist[i];
}

inline int &Miaig::objRequire(int i) {
    return _data->pRequire[i];
}

inline int &Miaig::nTravIds(void) {
    return _data->nTravIds;
}

inline int Miaig::nWords(void) {
    return _data->nWords;
}

inline float Miaig::countAnd2(int reset, int fDummy1, int fDummy2) {
    (void)fDummy1;
    (void)fDummy2;
    int i, Counter = 0;
    Miaig_ForEachNode(i) {
        Counter += objFaninNum(i) - 1;
    }
    return Counter;
}

inline float Miaig::countLevel(int reset, int fDummy1, int fDummy2) {
    (void)fDummy1;
    (void)fDummy2;
    initializeLevels();
    int i, Level = -1;
    Miaig_ForEachOutput(i) {
        Level = Rw_MaxInt(Level, objLevel(i));
    }
    return Level;
}

inline word *Miaig::objTruth(int i, int n) {
    return _data->pTruths[n] + nWords() * i;
}

inline vi *Miaig::objFanins(int i) {
    return _data->pvFanins + i;
}

inline vi *Miaig::objFanouts(int i) {
    assert(_data->pvFanouts);
    return _data->pvFanouts + i;
}

inline int Miaig::objType(int i) {
    return objTravId(i) == nTravIds();
}

inline void Miaig::attachTiming(vi *vCiArrs, vi *vCoReqs) {
    _data->vCiArrs = vCiArrs;
    _data->vCoReqs = vCoReqs;
    if (vCiArrs) assert(Vi_Size(vCiArrs) == nIns());
    if (vCoReqs) assert(Vi_Size(vCoReqs) == nOuts());
}

} // namespace Rewire

#ifdef RW_ABC
ABC_NAMESPACE_CXX_HEADER_END
#endif // RW_ABC

#endif // REWIRE_MIAIG_H
