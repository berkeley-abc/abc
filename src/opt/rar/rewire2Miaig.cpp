/**CFile****************************************************************

  FileName    [rewire2Miaig.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Miaig.cpp,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rewire2Rar.h"
#include "rewire2Miaig.h"
#include <unordered_set>
#include <utility>

#ifdef RW2_ABC
ABC_NAMESPACE_IMPL_START
#endif // RW2_ABC

#ifdef RW2_ABC
/**Function*************************************************************

  Synopsis    [Moves or copies ABC vector storage into the local representation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static rw2_vi *Rewire2_MoveVecToVi(Vec_Int_t *v) {
    rw2_vi *p = (rw2_vi *)malloc(sizeof(rw2_vi));
    p->size = Vec_IntSize(v);
    p->cap = Vec_IntCap(v);
    p->ptr = Vec_IntArray(v);
    free(v);
    return p;
}

static rw2_vi *Rewire2_CopyVecToVi(Vec_Int_t *v) {
    rw2_vi *p = (rw2_vi *)malloc(sizeof(rw2_vi));
    p->size = Vec_IntSize(v);
    p->cap = Vec_IntCap(v);
    p->ptr = (int *)malloc(sizeof(int) * p->cap);
    memcpy(p->ptr, Vec_IntArray(v), sizeof(int) * p->size);
    return p;
}

namespace Rewire2 {

/**Function*************************************************************

  Synopsis    [Records an AIG exactly, including its object and port order.]

  Description [Names do not affect rewiring and are restored on a hit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void CacheWriteGia(Gia_Man_t *pGia, std::vector<int> &Data) {
    Gia_Obj_t *pObj;
    int i;
    Data.push_back(Gia_ManCiNum(pGia));
    Data.push_back(Gia_ManCoNum(pGia));
    Gia_ManForEachObj1(pGia, pObj, i) {
        if (Gia_ObjIsCi(pObj)) {
            Data.push_back(-1);
            Data.push_back(Gia_ObjCioId(pObj));
        } else {
            Data.push_back(Gia_ObjFaninLit0(pObj, i));
            Data.push_back(Gia_ObjIsCo(pObj) ? -2 - Gia_ObjCioId(pObj) : Gia_ObjFaninLit1(pObj, i));
        }
    }
}

/**Function*************************************************************

  Synopsis    [Restores a cached combinational result without rewriting it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t *CacheReadGia(const std::vector<int> &Data, char *pName) {
    Gia_Man_t *pGia = Gia_ManStart((int)Data.size() / 2);
    pGia->pName = Abc_UtilStrsav(pName);
    for (size_t i = 2; i < Data.size(); i += 2) {
        if (Data[i] == -1) Gia_ManAppendCi(pGia);
        else if (Data[i + 1] <= -2) Gia_ManAppendCo(pGia, Data[i]);
        else Gia_ManAppendAnd(pGia, Data[i], Data[i + 1]);
    }
    assert(Gia_ManCiNum(pGia) == Data[0] && Gia_ManCoNum(pGia) == Data[1]);
    return pGia;
}

struct CacheEntry {
    word Hash;
    std::vector<int> Key, Result;
    size_t bytes() const { return sizeof(CacheEntry) + sizeof(int) * (Key.capacity() + Result.capacity()); }
};

// Only deterministic, untimed, combinational AIG searches enter this cache.
// A hash is merely a filter: the complete graph and options must agree.
// Thread-local ownership avoids sharing mutable state between ABC workers.
class ResultCache {
    std::vector<CacheEntry> Entries;
    size_t Used;
public:
    ResultCache() : Used(0) { Entries.reserve(2048); }
    static word hash(const std::vector<int> &Key) {
        word Value = ABC_CONST(1469598103934665603);
        for (size_t i = 0; i < Key.size(); i++)
            Value = (Value ^ (unsigned)Key[i]) * ABC_CONST(1099511628211);
        return Value;
    }
    Gia_Man_t *find(const std::vector<int> &Key, char *pName) const {
        word Hash = hash(Key);
        for (size_t i = 0; i < Entries.size(); i++)
            if (Entries[i].Hash == Hash && Entries[i].Key == Key)
                return CacheReadGia(Entries[i].Result, pName);
        return NULL;
    }
    void insert(std::vector<int> &Key, Gia_Man_t *pResult) {
        const size_t Budget = 32 * 1024 * 1024;
        CacheEntry Entry;
        Entry.Hash = hash(Key);
        Entry.Key.swap(Key);
        CacheWriteGia(pResult, Entry.Result);
        size_t Bytes = Entry.bytes();
        if (Bytes > Budget / 2) return;
        // Account for vector metadata capacity as well as stored arrays.
        while (!Entries.empty() && (Entries.size() >= 2048 || Used + Bytes + Entries.capacity() * sizeof(CacheEntry) > Budget)) {
            Used -= Entries.front().bytes();
            Entries.erase(Entries.begin());
        }
        Used += Bytes;
        Entries.push_back(std::move(Entry));
    }
};

} // namespace Rewire2

/**Function*************************************************************

  Synopsis    [Checks the dense truth-table allocation before shifting.]

  Description [The estimate leaves room for the temporary expanded graph.
               Larger designs should be optimized through stochmap.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rewire2_CheckSize(int nIns, int nObjs) {
    const size_t Budget = 256 * 1024 * 1024;
    size_t nWords;
    if (nIns > 24) {
        Abc_Print(-1, "Rewire2 uses dense truth tables; use stochmap -N 14 for this input.\n");
        return 0;
    }
    nWords = nIns <= 6 ? 1 : (size_t)1 << (nIns - 6);
    if ((size_t)nObjs > Budget / (8 * sizeof(word) * nWords)) {
        Abc_Print(-1, "Rewire2 truth tables would exceed the 256 MiB budget; use stochmap -N 14.\n");
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks search options and the fanin reservation estimate.]

  Description [Reject invalid divisors and overflowing per-node capacities
               before randomization, allocation, or integer arithmetic.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rewire2_CheckOptions(int nObjs, int nIters, int nStall, int nExpands,
    int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode,
    int nMappedMode, int nDist, int nSeed, int fTiming, int fVerbose) {
    const size_t Budget = 256 * 1024 * 1024;
    if (nObjs < 1 || nIters < 0 || nStall < 0 || nExpands < 1 || nGrowth < 1 ||
        nDivs < -1 || nFaninMax < 2 || nTimeOut < 0 || nMode < 0 || nMode > 1 ||
        nMappedMode < 0 || nMappedMode > 2 || nDist < 0 || nSeed < 0 || fVerbose < 0 ||
        nDivs > ABC_INT_MAX - nObjs || (word)nFaninMax + nGrowth > ABC_INT_MAX) {
        Abc_Print(-1, "Rewire2 search options are invalid or exceed integer limits.\n");
        return 0;
    }
    if (nMode == 1 && fTiming && nMappedMode == 2) {
        Abc_Print(-1, "Rewire2 mapper 2 supports area optimization only.\n");
        return 0;
    }
    if ((size_t)nObjs > Budget / sizeof(int) / (nFaninMax + nGrowth)) {
        Abc_Print(-1, "Rewire2 fanin reservations would exceed 256 MiB; reduce -F or -G.\n");
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks GIA representation, external-care dimensions, and size.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rewire2_CheckGia(Gia_Man_t *pGia) {
    if (Gia_ManXorNum(pGia) || Gia_ManMuxNum(pGia) || Gia_ManBufNum(pGia)) {
        Abc_Print(-1, "Rewire2 requires an AND-only GIA; expand XOR, MUX and buffer objects first.\n");
        return 0;
    }
    return Rewire2_CheckSize(Gia_ManCiNum(pGia), Gia_ManObjNum(pGia));
}

static int Rewire2_CheckCare(int nIns, int nOuts, Gia_Man_t *pExc) {
    if (!pExc) return 1;
    if (Gia_ManRegNum(pExc) || Gia_ManCiNum(pExc) != nIns ||
        (Gia_ManCoNum(pExc) != 1 && Gia_ManCoNum(pExc) != nOuts)) {
        Abc_Print(-1, "Rewire2 external cares need matching inputs and one or matching outputs, without registers.\n");
        return 0;
    }
    return Rewire2_CheckGia(pExc);
}

/**Function*************************************************************

  Synopsis    [Checks the float level bound before conversion to int.]

  Description [Use the same float product as the search to preserve rounding.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rewire2_CheckLevelRatio(Rewire2::Miaig &Ntk, float Ratio) {
    if (Ratio == 0) return 1;
    float Limit = (Ntk.nOuts() ? Ntk.countLevel() : 0) * Ratio;
    if (!(Ratio >= 0 && (double)Ratio <= ABC_INT_MAX &&
          Limit >= 0 && (double)Limit <= ABC_INT_MAX)) {
        Abc_Print(-1, "Rewire2 level bound exceeds the supported integer range.\n");
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Runs independent rewiring with the requested search limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t *Gia_ManRewire2Int(Gia_Man_t *pGia, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fChoices, int fVerbose) {
    if (!Rewire2_CheckOptions(Gia_ManObjNum(pGia), nIters, nStall, nExpands, nGrowth,
        nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, nSeed, fTiming, fVerbose)) return NULL;
    if (!Rewire2_CheckGia(pGia) ||
        !Rewire2_CheckCare(Gia_ManCiNum(pGia), Gia_ManCoNum(pGia), pExc)) return NULL;
    if (fChoices && Gia_ManRegNum(pGia)) {
        Abc_Print(-1, "Rewire2 structural choices require a combinational GIA.\n");
        return NULL;
    }
    Rw2_Random_Num(nSeed == 0 ? 1 + Abc_Random(0) % 10 : nSeed);
#if ABC_HAS_THREAD_LOCAL
    static thread_local Rewire2::ResultCache Cache;
    std::vector<int> Key;
    int fCache = nSeed > 0 && nTimeOut == 0 && nMode == 0 && !fChoices && !fTiming && !pExc &&
                 !Gia_ManRegNum(pGia) && !pGia->vCiArrs && !pGia->vCoReqs;
    if (fCache) {
        int LevelBits = 0;
        static_assert(sizeof(LevelBits) == sizeof(levelGrowRatio), "Expected a 32-bit float");
        memcpy(&LevelBits, &levelGrowRatio, sizeof(LevelBits));
        int Options[] = {nIters, nStall, LevelBits, nExpands, nGrowth, nDivs, nFaninMax, nDist, nSeed, fCheck};
        Key.assign(Options, Options + sizeof(Options) / sizeof(Options[0]));
        Rewire2::CacheWriteGia(pGia, Key);
        Gia_Man_t *pHit = Cache.find(Key, Gia_ManName(pGia));
        if (pHit) {
            if (fVerbose) printf("Reusing an identical rewiring problem with the same seed and effort.\n");
            return pHit;
        }
    }
#endif
    rw2_vi *vCiArrs = (pGia->vCiArrs) ? Rewire2_CopyVecToVi(pGia->vCiArrs) : NULL;
    rw2_vi *vCoReqs = (pGia->vCoReqs) ? Rewire2_CopyVecToVi(pGia->vCoReqs) : NULL;

    Rewire2::Miaig pNtkMiaig(pGia);
    if (pExc)
        pNtkMiaig.setExc(pExc);
    pNtkMiaig.attachTiming(vCiArrs, vCoReqs);
    if (!Rewire2_CheckLevelRatio(pNtkMiaig, levelGrowRatio)) {
        if (vCiArrs) Rw2_Vi_Free(vCiArrs);
        if (vCoReqs) Rw2_Vi_Free(vCoReqs);
        return NULL;
    }
    Gia_ChMan_t *pChMan = fChoices ? Gia_ManDupChoicesStart(pGia) : NULL;
    Rewire2::Miaig pNew = pNtkMiaig.rewire2(nIters, nStall, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, fCheck, pChMan, fVerbose);
    pNew.setName(Gia_ManName(pGia));

    if (vCiArrs) Rw2_Vi_Free(vCiArrs);
    if (vCoReqs) Rw2_Vi_Free(vCoReqs);

    Gia_Man_t *pResult = pChMan ? Gia_ManDupChoicesFinish(pChMan) : pNew.toGia();
    Gia_ManSetRegNum(pResult, Gia_ManRegNum(pGia));
#if ABC_HAS_THREAD_LOCAL
    if (fCache) Cache.insert(Key, pResult);
#endif
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Runs independent rewiring with the requested search limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t *Abc_ManRewire2Int(Abc_Ntk_t *pNtk, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose) {
    if (!Rewire2_CheckOptions(Abc_NtkObjNumMax(pNtk), nIters, nStall, nExpands, nGrowth,
        nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, nSeed, fTiming, fVerbose)) return NULL;
    if (!Rewire2_CheckSize(Abc_NtkCiNum(pNtk), Abc_NtkObjNumMax(pNtk)) ||
        !Rewire2_CheckCare(Abc_NtkCiNum(pNtk), Abc_NtkCoNum(pNtk), pExc)) return NULL;
    Rw2_Random_Num(nSeed == 0 ? 1 + Abc_Random(0) % 10 : nSeed);

    int fMapped = nMode == 1;
    Vec_Int_t *vMapping = (Abc_NtkHasMapping(pNtk)) ? Abc_ManRewire2NtkWriteMiniMapping(pNtk) : NULL;
    float objectiveValue = (vMapping) ? (fTiming ? Abc_NtkDelayTrace(pNtk, 0, 0, 0) : Abc_NtkGetMappedArea(pNtk)) : 0.0f;
    Mini_Aig_t *pMiniAig = Abc_ManRewire2MiniAigFromNtk(pNtk);
    if (!pMiniAig) {
        if (vMapping) Vec_IntFree(vMapping);
        return NULL;
    }
    Rewire2::Miaig pNtkMiaig(pMiniAig);
    Mini_AigStop(pMiniAig);
    if (vMapping)
        pNtkMiaig.setMapped(vMapping, objectiveValue);
    if (!Rewire2_CheckSize(pNtkMiaig.nIns(), pNtkMiaig.nObjs()) ||
        !Rewire2_CheckLevelRatio(pNtkMiaig, levelGrowRatio)) return NULL;
    if (pExc)
        pNtkMiaig.setExc(pExc);
    Rewire2::Miaig pNew = pNtkMiaig.rewire2(nIters, nStall, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, fCheck, NULL, fVerbose);
    pNew.setName(Abc_NtkName(pNtk));

    return pNew.toNtk(fMapped);
}

/**Function*************************************************************

  Synopsis    [Runs independent rewiring with the requested search limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Mini_Aig_t *MiniAig_ManRewire2Int(Mini_Aig_t *pAig, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose) {
    if (!Rewire2_CheckOptions(Mini_AigNodeNum(pAig), nIters, nStall, nExpands, nGrowth,
        nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, nSeed, fTiming, fVerbose)) return NULL;
    if (!Rewire2_CheckSize(Mini_AigPiNum(pAig), Mini_AigNodeNum(pAig)) ||
        !Rewire2_CheckCare(Mini_AigPiNum(pAig), Mini_AigPoNum(pAig), pExc)) return NULL;
    Rw2_Random_Num(nSeed == 0 ? 1 + Abc_Random(0) % 10 : nSeed);

    Rewire2::Miaig pNtkMiaig(pAig);
    if (!Rewire2_CheckLevelRatio(pNtkMiaig, levelGrowRatio)) return NULL;
    if (pExc)
        pNtkMiaig.setExc(pExc);
    Rewire2::Miaig pNew = pNtkMiaig.rewire2(nIters, nStall, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, fCheck, NULL, fVerbose);

    Mini_Aig_t *pResult = pNew.toMiniAig();
    Mini_AigSetRegNum(pResult, Mini_AigRegNum(pAig));
    return pResult;
}
#endif // RW2_ABC

namespace Rewire2 {

void Miaig::create(int nIns, int nOuts, int nObjsAlloc) {
    assert(1 + nIns + nOuts <= nObjsAlloc);
    release();

    _data = (Miaig2_Data *)calloc(sizeof(Miaig2_Data), 1);

    if (_data) {
        _data->nIns = nIns;
        _data->nOuts = nOuts;
        _data->nObjs = 1 + nIns; // const0 + nIns
        _data->nObjsAlloc = nObjsAlloc;
        _data->nWords = Rw2_Tt_WordNum(nIns);
        _data->nTravIds = 0;
        _data->pTravIds = (int *)calloc(sizeof(int), _data->nObjsAlloc);
        _data->pCopy = (int *)calloc(sizeof(int), _data->nObjsAlloc);
        _data->pRefs = (int *)calloc(sizeof(int), _data->nObjsAlloc);
        _data->vOrder = Rw2_Vi_Alloc(1000);
        _data->vOrderF = Rw2_Vi_Alloc(1000);
        _data->vOrderF2 = Rw2_Vi_Alloc(1000);
        _data->vTfo = Rw2_Vi_Alloc(1000);
        _data->pvFanins = (rw2_vi *)calloc(sizeof(rw2_vi), _data->nObjsAlloc);
        _data->pLevel = nullptr;
        _data->pDist = nullptr;
        _data->pTable = nullptr;
        _data->refcount = 1;
        _refcount = &_data->refcount;
    }
}

void Miaig::setName(char *pName) {
    if (_data) {
        if (_data->pName) {
            free(_data->pName);
        }
        if (pName == NULL || pName[0] == '\0') {
            _data->pName = strdup("rewire2_miaig");
        } else {
            _data->pName = strdup(pName);
        }
    }
}

void Miaig::setMapped(Vec_Int_t *vMapping, float objectiveValue) {
    if (_data) {
        if (_data->pNtkMapped) {
            Rw2_Vi_Free(_data->pNtkMapped);
        }
        _data->pNtkMapped = Rewire2_MoveVecToVi(vMapping);
        _data->objectiveValue = objectiveValue;
    }
}

void Miaig::printNode(int i) {
    if (!_data) return;
    int iLit, k;
    if (i == 0) {
        printf("Const0\n");
    } else if (i <= nIns()) {
        printf("Pi%d", i);
        if (!_data->pvFanouts) {
            printf("\n"); return;
        }
        printf(" Fanouts: {");
        Miaig2_ForEachObjFanout(i, iLit, k)
            printf(" %d", iLit); // this is a variable
        printf(" }");
        if (!_data->pRequire) {
            printf("\n"); return;
        }
        printf(" Require: %d\n", objRequire(i));
    } else if (i < nObjs() - nOuts()) {
        printf("Node%d Level: %d Fanins: {", i, objLevel(i));
        Miaig2_ForEachObjFanin(i, iLit, k)
            printf(" %s%d", Rw2_LitIsCompl(iLit) ? "~" : "", Rw2_Lit2Var(iLit)); // this is a literal
        printf(" }");
        if (!_data->pvFanouts) {
            printf("\n"); return;
        }
        printf(" Fanouts: {");
        Miaig2_ForEachObjFanout(i, iLit, k)
            printf(" %d", iLit); // this is a variable
        printf(" }");
        if (!_data->pRequire) {
            printf("\n"); return;
        }
        printf(" Require: %d\n", objRequire(i));
    } else {
        printf("Po%d ", i - nObjs() + nOuts());
        Miaig2_ForEachObjFanin(i, iLit, k)
            printf(" %s%d", Rw2_LitIsCompl(iLit) ? "~" : "", Rw2_Lit2Var(iLit));
        if (!_data->pRequire) {
            printf("\n"); return;
        }
        printf(" Require: %d\n", objRequire(i));
    }
}

void Miaig::print(void) {
    int i;
    printf("\nAIG printout:\n");
    Miaig2_ForEachObj(i) {
        printNode(i);
    }
}

#ifdef RW2_ABC
/**Function*************************************************************

  Synopsis    [Imports the combinational frame, retaining port order.]

  Description [CI/CO counts include register terminals.  The wrapper
               restores the original register count on the returned GIA.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Miaig::fromGia(Gia_Man_t *pGia) {
    Gia_Obj_t *pObj;
    int i;
    int *pCopy = (int *)calloc(sizeof(int), Gia_ManObjNum(pGia));
    create(Gia_ManCiNum(pGia), Gia_ManCoNum(pGia), Gia_ManObjNum(pGia));
    Gia_ManForEachCi(pGia, pObj, i)
        pCopy[Gia_ObjId(pGia, pObj)] = i + 1;
    Gia_ManForEachAnd(pGia, pObj, i) {
        pCopy[i] = appendObj();
        appendFanin(pCopy[i], Rw2_Lit2LitV(pCopy, Gia_ObjFaninLit1(pObj, i)));
        appendFanin(pCopy[i], Rw2_Lit2LitV(pCopy, Gia_ObjFaninLit0(pObj, i)));
    }
    Gia_ManForEachCo(pGia, pObj, i)
        appendFanin(appendObj(), Rw2_Lit2LitV(pCopy, Gia_ObjFaninLit0p(pGia, pObj)));
    free(pCopy);
    return 1;
}

int Miaig::fromMiniAig(Mini_Aig_t *pMiniAig) {
    int *pCopy = (int *)calloc(sizeof(int), Mini_AigNodeNum(pMiniAig)); // obj2obj
    create(Mini_AigPiNum(pMiniAig), Mini_AigPoNum(pMiniAig), Mini_AigNodeNum(pMiniAig));
    int i;
    Miaig2_ForEachInput(i)
        pCopy[i] = i;
    Mini_AigForEachAnd( pMiniAig, i ) {
        pCopy[i] = appendObj();
        assert( pCopy[i] == i );
        appendFanin(pCopy[i], Rw2_Lit2LitV(pCopy, Mini_AigNodeFanin0(pMiniAig, i)));
        appendFanin(pCopy[i], Rw2_Lit2LitV(pCopy, Mini_AigNodeFanin1(pMiniAig, i)));
    }
    Mini_AigForEachPo( pMiniAig, i )
        appendFanin(appendObj(), Rw2_Lit2LitV(pCopy, Mini_AigNodeFanin0(pMiniAig, i)));
    free(pCopy);
    return 1;
}

Gia_Man_t *Miaig::toGia(void) {
    int i, k, iLit, And2 = countAnd2();
    Gia_Man_t *pGia = Gia_ManStart(1 + nIns() + And2 + nOuts()), *pTemp;
    pGia->pName = Abc_UtilStrsav(_data->pName);
    Gia_ManHashAlloc(pGia);
    memset(_data->pCopy, 0, sizeof(int) * nObjs());
    Miaig2_ForEachInput(i)
        objCopy(i) = Gia_ManAppendCi(pGia);
    Miaig2_ForEachNode(i) {
        assert(objFaninNum(i) > 0);
        Miaig2_ForEachObjFanin(i, iLit, k) {
            if (k == 0)
                objCopy(i) = Rw2_Lit2LitL(_data->pCopy, iLit);
            else
                objCopy(i) = Gia_ManHashAnd(pGia, objCopy(i), Rw2_Lit2LitL(_data->pCopy, iLit));
        }
    }
    Miaig2_ForEachOutput(i) {
        assert(objFaninNum(i) == 1);
        Miaig2_ForEachObjFanin(i, iLit, k)
            Gia_ManAppendCo(pGia, Rw2_Lit2LitL(_data->pCopy, iLit));
    }
    // assert(Gia_ManObjNum(pGia) == (1 + nIns() + nOuts() + And2));
    pGia = Gia_ManCleanup(pTemp = pGia);
    Gia_ManStop(pTemp);
    return pGia;
}

Mini_Aig_t *Miaig::toMiniAig(void) {
    int i, k, iLit;
    Mini_Aig_t * pMini = Mini_AigStart();
    memset(_data->pCopy, 0, sizeof(int) * nObjs());
    Miaig2_ForEachInput(i)
        objCopy(i) = Mini_AigCreatePi(pMini);
    Miaig2_ForEachNode(i) {
        assert(objFaninNum(i) > 0);
        Miaig2_ForEachObjFanin(i, iLit, k)
        if (k == 0)
            objCopy(i) = Rw2_Lit2LitL(_data->pCopy, iLit);
        else
            objCopy(i) = Mini_AigAnd(pMini, objCopy(i), Rw2_Lit2LitL(_data->pCopy, iLit));
    }
    Miaig2_ForEachOutput(i) {
        assert(objFaninNum(i) == 1);
        Miaig2_ForEachObjFanin(i, iLit, k)
            Mini_AigCreatePo(pMini, Rw2_Lit2LitL(_data->pCopy, iLit));
    }
    assert(pMini->nSize == 2 * (1 + nIns() + nOuts() + countAnd2()));
    return pMini;
}

Abc_Ntk_t *Miaig::toNtk(int fMapped) {
    Abc_Ntk_t *pNtk;
    if (_data->pNtkMapped && fMapped) {
        pNtk = Abc_ManRewire2NtkFromMiniMapping(Rw2_Vi_Array(_data->pNtkMapped));
        ABC_FREE(pNtk->pName);
        Abc_NtkSetName(pNtk, Abc_UtilStrsav(_data->pName));
        return pNtk;
    }
    Gia_Man_t *pGia = toGia();
    pNtk = Gia_ManRewire2Put(pGia);
    Gia_ManStop(pGia);
    return pNtk;
}

void Miaig::setExc(Gia_Man_t *pExc) {
    int i;
    assert(Gia_ManCiNum(pExc) == nIns());
    assert(Gia_ManCoNum(pExc) == nOuts() || Gia_ManCoNum(pExc) == 1);
    if (Gia_ManCoNum(pExc) != nOuts() && Gia_ManCoNum(pExc) == 1) {
        printf("[Warning] The external careset has only a single output that will be applied to all other outputs.\n");
    }
    if (!_data->pExc) {
        _data->pExc = (word *)malloc(sizeof(word) * nWords() * nOuts());
    }
    Miaig Exc(pExc);
    Exc.initializeTruth();
    for (i = 0; i < nOuts(); ++i) {
        word *tExc = Exc.objTruth(Exc.nObjs() - Exc.nOuts() + std::min(i, Gia_ManCoNum(pExc)-1), 0);
        Rw2_Tt_Dup(_data->pExc + nWords() * i, tExc, nWords());
    }
}
#endif // RW2_ABC

// technology mapping
float Miaig::countMappedArea(int reset, int nMappedMode, int fDch) {
    if (!reset && _data->objectiveValue) return _data->objectiveValue;
#ifdef RW2_ABC
    float area = 0;
    Abc_Ntk_t *pNtkMapped = NULL, *pNtkMappedTemp = NULL;
    if (nMappedMode == 0) {        // amap
        Abc_Ntk_t *pNtk = toNtk();
        if (fDch) {
            Abc_Ntk_t *pNtkDch = Abc_ManRewire2Dch(pNtk);
            Abc_NtkDelete(pNtk);
            pNtk = pNtkDch;
        }
        if (pNtk) {
            pNtkMapped = Abc_ManRewire2MapAmap(pNtk);
            Abc_NtkDelete(pNtk);
        }
    } else if (nMappedMode == 1) { // &nf
        Gia_Man_t *pGia = toGia();
        pNtkMapped = Gia_ManRewire2MapNf(pGia);
        Gia_ManStop(pGia);
    } else if (nMappedMode == 2) { // &simap
        Abc_Ntk_t *pNtk = toNtk();
        pNtkMapped = Abc_ManRewire2MapAmap(pNtk);
        Abc_NtkDelete(pNtk);
        if (!pNtkMapped) return _data->objectiveValue = ABC_INFINITY;
        area = Abc_NtkGetMappedArea(pNtkMapped);
        Gia_Man_t *pGia = toGia();
        while ((pNtkMappedTemp = Gia_ManRewire2MapSimap(pGia, area - 2, 0, 40))) {
            area -= 2;
            Abc_NtkDelete(pNtkMapped);
            pNtkMapped = pNtkMappedTemp;
        }
        Gia_ManStop(pGia);
    }
    if (pNtkMapped) {
        area = Abc_NtkGetMappedArea(pNtkMapped);
        Vec_Int_t *vMapping = Abc_ManRewire2NtkWriteMiniMapping(pNtkMapped);
        setMapped(vMapping, area);
        Abc_NtkDelete(pNtkMapped);
    } else area = ABC_INFINITY;
#else
    float area = countAnd2(reset, 0);
#endif // RW2_ABC

    return _data->objectiveValue = area;
}

float Miaig::countMappedDelay(int reset, int nMappedMode, int fDch) {
    if (!reset && _data->objectiveValue) return _data->objectiveValue;
#ifdef RW2_ABC
    float delay = 0;
    Abc_Ntk_t *pNtkMapped = NULL;
    if (nMappedMode == 0) {        // amap
        Abc_Ntk_t *pNtk = toNtk();
        pNtkMapped = Abc_ManRewire2MapAmap(pNtk);
        Abc_NtkDelete(pNtk);
    } else if (nMappedMode == 1) { // &nf
        Gia_Man_t *pGia = toGia();
        pNtkMapped = Gia_ManRewire2MapNf(pGia);
        Gia_ManStop(pGia);
    } else if (nMappedMode == 2) { // &simap
        printf("[Warning] The &simap mode is not supported for delay optimization.\n");
    }
    if (pNtkMapped) {
        delay = Abc_NtkDelayTrace(pNtkMapped, 0, 0, 0);
        Vec_Int_t *vMapping = Abc_ManRewire2NtkWriteMiniMapping(pNtkMapped);
        setMapped(vMapping, delay);
        Abc_NtkDelete(pNtkMapped);
    } else delay = ABC_INFINITY;
#else
    float delay = countLevel(reset, 0);
#endif // RW2_ABC

    return _data->objectiveValue = delay;
}

// topological collection
void Miaig::topoCollect_rec(int iObj) {
    int i, iLit;
    if (objTravId(iObj) == nTravIds())
        return;
    objTravId(iObj) = nTravIds();
    Rw2_Vi_PushOrder(_data->vOrder, iObj);
    Miaig2_ForEachObjFanin(iObj, iLit, i)
        topoCollect_rec(Rw2_Lit2Var(iLit));
}

rw2_vi *Miaig::topoCollect(void) {
    int i;
    nTravIds()++;
    Rw2_Vi_Shrink(_data->vOrder, 0);
    Miaig2_ForEachConstInput(i)
        objTravId(i) = nTravIds();
    Miaig2_ForEachOutput(i)
        topoCollect_rec(Rw2_Lit2Var(objFanin0(i)));
    return _data->vOrder;
}

// initializeLevels
int Miaig::initializeLevels_rec(int iObj) {
    int i, iLit;
    if (objLevel(iObj) != -1)
        return objLevel(iObj);
    int level = -1;
    Miaig2_ForEachObjFanin(iObj, iLit, i) {
        level = Abc_MaxInt(initializeLevels_rec(Rw2_Lit2Var(iLit)), level);
    }
    return objLevel(iObj) = level + objFaninNum(iObj) - 1;
}

void Miaig::initializeLevels(void) {
    if (_data->pLevel) return;
    _data->pLevel = (int *)malloc(sizeof(int) * nObjs());

    int i;
    Miaig2_ForEachObj(i) {
        objLevel(i) = -1;
    }
    objLevel(0) = 0; // const0 is always at level 0
    Miaig2_ForEachInput(i) {
        objLevel(i) = (_data->vCiArrs) ? Rw2_Vi_Read(_data->vCiArrs, i - 1) : 0; // modify this from external level if provided
    }
    Miaig2_ForEachOutput(i) {
        objLevel(i) = initializeLevels_rec(Rw2_Lit2Var(objFanin0(i)));
    }
}

void Miaig::updateLevels_rec(int iObj) {
    assert(_data->pLevel);
    assert(_data->pvFanouts);
    int i, iLit, level = -1;
    Miaig2_ForEachObjFanin(iObj, iLit, i) {
        level = Abc_MaxInt(objLevel(Rw2_Lit2Var(iLit)), level);
    }
    objLevel(iObj) = level + objFaninNum(iObj) - 1;
    Miaig2_ForEachObjFanout(iObj, iLit, i) {
        updateLevels_rec(iLit); // this is a variable
    }
}

// distance computation
void Miaig::initializeDists(void) {
    if (_data->pDist) return;
    _data->pDist = (int *)malloc(sizeof(int) * nObjs());
}

void Miaig::markDistanceN_rec(int iObj, int n, int limit) {
    int i, iLit;
    if (objDist(iObj) >= 0 && objDist(iObj) <= n)
        return;
    objDist(iObj) = n;
    if (n == limit)
        return;
    Miaig2_ForEachObjFanin(iObj, iLit, i)
        markDistanceN_rec(Rw2_Lit2Var(iLit), n + 1, limit);
}

void Miaig::markDistanceN(int iObj, int n) {
    int i, j, k, iLit;
    memset(_data->pDist, 0xFF, sizeof(int) * nObjs());
    markDistanceN_rec(iObj, 0, n);
    for (i = 0; i < n; ++i) {
        Miaig2_ForEachNode(j) {
            if (objDist(j) >= 0) continue;
            int minDist = nObjs();
            Miaig2_ForEachObjFanin(j, iLit, k) {
                if (objDist(Rw2_Lit2Var(iLit)) == -1) continue;
                minDist = Rw2_MinInt(minDist, objDist(Rw2_Lit2Var(iLit)));
            }
            if (minDist != nObjs()) {
                markDistanceN_rec(j, minDist + 1, n);
            }
        }
    }
}

void Miaig::initializeRequire_rec(int iObj) {
    int i, iLit, requireTime = RW2_INT_MAX;
    if (objIsPo(iObj)) return;
    Miaig2_ForEachObjFanout(iObj, iLit, i) { // this is a variable
        initializeRequire_rec(iLit);
    }
    Miaig2_ForEachObjFanout(iObj, iLit, i) { // this is a variable
        requireTime = Rw2_MinInt(objRequire(iLit) - (objFaninNum(iLit) - 1), requireTime);
    }
    objRequire(iObj) = requireTime;
}

void Miaig::initializeRequire(void) {
    if (_data->pRequire) return;
    _data->pRequire = (int *)malloc(sizeof(int) * nObjs());
    memset(_data->pRequire, 0, sizeof(int) * nObjs());

    int iObj;
    if (_data->vCoReqs) {
        Miaig2_ForEachOutput(iObj) {
            objRequire(iObj) = Rw2_Vi_Read(_data->vCoReqs, iObj - nObjs() + nOuts());
        }
    } else {
        int maxRequireTime = countLevel();
        Miaig2_ForEachOutput(iObj) {
            objRequire(iObj) = maxRequireTime;
        }
    }
    Miaig2_ForEachInput(iObj) {
        initializeRequire_rec(iObj);
    }
}

void Miaig::updateRequire_rec(int iObj) {
    assert(_data->pRequire);
    assert(_data->pvFanouts);
    int i, iLit, requireTime = RW2_INT_MAX;
    Miaig2_ForEachObjFanout(iObj, iLit, i) { // this is a variable
        requireTime = Rw2_MinInt(objRequire(iLit) - (objFaninNum(iLit) - 1), requireTime);
    }
    objRequire(iObj) = requireTime;
    Miaig2_ForEachObjFanin(iObj, iLit, i) {
        updateRequire_rec(Rw2_Lit2Var(iLit));
    }
}

void Miaig::checkTiming(rw2_vi *vCiArrs, rw2_vi *vCoReqs) {
    if (_data->pLevel) free(_data->pLevel), _data->pLevel = nullptr;
    if (_data->pRequire) free(_data->pRequire), _data->pRequire = nullptr;
    this->attachTiming(vCiArrs, vCoReqs);
    initializeLevels();
    initializeRequire();
    int iObj;
    Miaig2_ForEachOutput(iObj) {
        if (objLevel(iObj) > objRequire(iObj)) {
            printf("Timing error: output %d has arrival %d but require %d.\n", iObj, objLevel(iObj), objRequire(iObj));
            exit(1);
        }
    }
}

void Miaig::initializeFanouts(void) {
    if (_data->pvFanouts) return;
    _data->pvFanouts = (rw2_vi *)calloc(sizeof(rw2_vi), _data->nObjsAlloc);
}

// reference counting
void Miaig::refObj(int iObj) {
    int k, iLit;
    Miaig2_ForEachObjFanin(iObj, iLit, k)
        objRef(Rw2_Lit2Var(iLit))++;
}

void Miaig::derefObj(int iObj) {
    int k, iLit;
    Miaig2_ForEachObjFanin(iObj, iLit, k)
        objRef(Rw2_Lit2Var(iLit))--;
}

void Miaig::derefObj_rec(int iObj, int iLitSkip) {
    int k, iLit;
    Miaig2_ForEachObjFanin(iObj, iLit, k) {
        if (iLit != iLitSkip && --objRef(Rw2_Lit2Var(iLit)) == 0 && objIsNode(Rw2_Lit2Var(iLit))) {
            derefObj_rec(Rw2_Lit2Var(iLit), -1);
            Rw2_Vi_Fill(objFanins(Rw2_Lit2Var(iLit)), 1, 0);
            refObj(Rw2_Lit2Var(iLit));
        }
    }
}

void Miaig::initializeRefs(void) {
    int i;
    memset(_data->pRefs, 0, sizeof(int) * _data->nObjs);
    Miaig2_ForEachNodeOutput(i)
        refObj(i);
}

void Miaig::verifyRefs(void) {
    int i;
    Miaig2_ForEachNodeOutput(i)
        derefObj(i);
    for (i = 0; i < nObjs(); i++)
        if (objRef(i))
            printf("Ref count of node %d is incorrect (%d).\n", i, objRef(i));
    initializeRefs();
}

// this procedure marks Const0, PIs, POs, and used nodes with the current trav ID
void Miaig::markDfs_rec(int iObj) {
    int i, iLit;
    if (objTravId(iObj) == nTravIds())
        return;
    objTravId(iObj) = nTravIds();
    Miaig2_ForEachObjFanin(iObj, iLit, i)
        markDfs_rec(Rw2_Lit2Var(iLit));
}

int Miaig::markDfs(void) {
    int i, nUnused = 0;
    nTravIds()++;
    Miaig2_ForEachConstInput(i)
        objTravId(i) = nTravIds();
    Miaig2_ForEachOutput(i)
        markDfs_rec(Rw2_Lit2Var(objFanin0(i)));
    Miaig2_ForEachOutput(i)
        objTravId(i) = nTravIds();
    Miaig2_ForEachNode(i)
        nUnused += (int)(objTravId(i) != nTravIds());
    return nUnused;
}

// simple duplicator (optionally removes unused nodes)
Miaig Miaig::dup(int fRemDangle, int fFanout, int fMapped) {
    Miaig pNew(nIns(), nOuts(), nObjs());
    pNew.attachTiming(_data->vCiArrs, _data->vCoReqs);
    if (fFanout) pNew.initializeFanouts();
    memset(_data->pCopy, 0, sizeof(int) * nObjs());
    int i, k, iLit; // obj2obj
    if (fRemDangle)
        markDfs();
    Miaig2_ForEachInput(i)
        objCopy(i) = i;
    Miaig2_ForEachNodeOutput(i) {
        assert(objFaninNum(i) > 0);
        if (fRemDangle && objTravId(i) != nTravIds())
            continue;
        objCopy(i) = pNew.appendObj();
        Miaig2_ForEachObjFanin(i, iLit, k)
            pNew.appendFanin(objCopy(i), Rw2_Lit2LitV(_data->pCopy, iLit));
    }
    if (_data->pNtkMapped && fMapped) {
        pNew._data->pNtkMapped = Rw2_Vi_Dup(_data->pNtkMapped);
        pNew._data->objectiveValue = _data->objectiveValue;
    }
    return pNew;
}

// duplicator to restore the topological order
// (the input AIG can have "hidden" internal nodes listed after primary outputs)
void Miaig::dupDfs_rec(Miaig &pNew, int iObj) {
    int i, iLit;
    // 1. return if current node is already marked
    if (objCopy(iObj) >= 0)
        return;
    // 2. create fanins for a given node
    Miaig2_ForEachObjFanin(iObj, iLit, i)
        dupDfs_rec(pNew, Rw2_Lit2Var(iLit));
    assert(objCopy(iObj) < 0); // combinational loop catching
    assert(objFaninNum(iObj) > 0);
    // 3. create current node
    objCopy(iObj) = pNew.appendObj();
    // 4. append newly created fanins to the current node
    Miaig2_ForEachObjFanin(iObj, iLit, i)
        pNew.appendFanin(objCopy(iObj), Rw2_Lit2LitV(_data->pCopy, iLit));
}

Miaig Miaig::dupDfs(void) {
    Miaig pNew(nIns(), nOuts(), nObjsAlloc());
    pNew.attachTiming(_data->vCiArrs, _data->vCoReqs);
    // 1. the array is filled with -1 to distinct visited nodes from unvisited
    memset(_data->pCopy, 0xFF, sizeof(int) * nObjsAlloc());
    int i; // obj2obj
    // for each primary input we mark it with it's index
    Miaig2_ForEachConstInput(i)
        objCopy(i) = i;
    // 2. for each primary output we call recursive function for it's fanin
    Miaig2_ForEachOutput(i)
        dupDfs_rec(pNew, Rw2_Lit2Var(objFanin0(i)));
    // 3. for each primary output append it's fanin
    Miaig2_ForEachOutput(i)
        pNew.appendFanin(pNew.appendObj(), Rw2_Lit2LitV(_data->pCopy, objFanin0(i)));
    return pNew;
}

// reduces multi-input and-gate represented by an array of fanin literals
void Miaig::reduceFanins(rw2_vi *v) {
    assert(Rw2_Vi_Size(v) > 0);
    Rw2_Vi_SelectSort(v);

    if (Rw2_Vi_Read(v, 0) == 0) {
        Rw2_Vi_Shrink(v, 1);
        return;
    }
    while (Rw2_Vi_Read(v, 0) == 1)
        Rw2_Vi_Drop(v, 0);
    if (Rw2_Vi_Size(v) == 0) {
        Rw2_Vi_Push(v, 1);
        return;
    }
    if (Rw2_Vi_Size(v) == 1)
        return;
    int i, iLit, iPrev = Rw2_Vi_Read(v, 0);
    Rw2_Vi_ForEachEntryStart(v, iLit, i, 1) {
        if ((iPrev ^ iLit) == 1) {
            Rw2_Vi_Fill(v, 1, 0);
            return;
        }
        if (iPrev == iLit)
            Rw2_Vi_Drop(v, i--);
        else
            iPrev = iLit;
    }
}

int Miaig::hashTwo(int l0, int l1, int TableSize) {
    unsigned Key = 0;
    Key += Rw2_Lit2Var(l0) * 7937;
    Key += Rw2_Lit2Var(l1) * 2971;
    Key += Rw2_LitIsCompl(l0) * 911;
    Key += Rw2_LitIsCompl(l1) * 353;
    return Key % TableSize;
}

int *Miaig::hashLookup(int *pTable, int l0, int l1, int TableSize) {
    int Key = hashTwo(l0, l1, TableSize);
    for (; pTable[3 * Key]; Key = (Key + 1) % TableSize)
        if (pTable[3 * Key] == l0 && pTable[3 * Key + 1] == l1)
            return pTable + 3 * Key + 2;
    assert(pTable[3 * Key] == 0);
    assert(pTable[3 * Key + 1] == 0);
    assert(pTable[3 * Key + 2] == 0);
    pTable[3 * Key] = l0;
    pTable[3 * Key + 1] = l1;
    return pTable + 3 * Key + 2;
}

// this duplicator creates two-input nodes, propagates constants, and does structural hashing
int Miaig::buildNode(int l0, int l1, int fCprop, int fStrash) {
    if (fCprop) {
        if (l0 == 0 || l1 == 0 || (l0 ^ l1) == 1) return 0;
        if (l0 == l1 || l1 == 1) return l0;
        if (l0 == 1) return l1;
    }
    int *pPlace = NULL;
    if (fStrash) {
        pPlace = hashLookup(_data->pTable, Rw2_MinInt(l0, l1), Rw2_MaxInt(l0, l1), _data->TableSize);
        if (*pPlace)
            return *pPlace;
    }
    int iObj = appendObj();
    appendFanin(iObj, Rw2_MinInt(l0, l1));
    appendFanin(iObj, Rw2_MaxInt(l0, l1));
    return pPlace ? (*pPlace = Rw2_Var2Lit(iObj, 0)) : Rw2_Var2Lit(iObj, 0);
}

int Miaig::buildNodeBalance_rec(Miaig &pNew, rw2_vi *vFanins, int begin, int end, int fCprop, int fStrash) {
    int length = end - begin + 1;
    if (length == 1) {
        return Rw2_Lit2LitL(_data->pCopy, Rw2_Vi_Read(vFanins, begin));
    } else if (length == 2) {
        return pNew.buildNode(Rw2_Lit2LitL(_data->pCopy, Rw2_Vi_Read(vFanins, begin)), Rw2_Lit2LitL(_data->pCopy, Rw2_Vi_Read(vFanins, end)), fCprop, fStrash);
    }
    int middle = begin + length / 2;
    int iLit0 = buildNodeBalance_rec(pNew, vFanins, begin, middle - 1, fCprop, fStrash);
    int iLit1 = buildNodeBalance_rec(pNew, vFanins, middle, end, fCprop, fStrash);
    return pNew.buildNode(iLit0, iLit1, fCprop, fStrash);
}

int Miaig::buildNodeBalance(Miaig &pNew, rw2_vi *vFanins, int fCprop, int fStrash) {
    return buildNodeBalance_rec(pNew, vFanins, 0, Rw2_Vi_Size(vFanins) - 1, fCprop, fStrash);
}

int Miaig::buildNodeCascade(Miaig &pNew, rw2_vi *vFanins, int fCprop, int fStrash) {
    int iLit = -1;
    for (int i = 0; i < Rw2_Vi_Size(vFanins); ++i) {
        if (i == 0)
            iLit = Rw2_Lit2LitL(_data->pCopy, Rw2_Vi_Read(vFanins, i));
        else
            iLit = pNew.buildNode(iLit, Rw2_Lit2LitL(_data->pCopy, Rw2_Vi_Read(vFanins, i)), fCprop, fStrash);
    }
    return iLit;
}

Miaig Miaig::dupStrash(int fCprop, int fStrash, int fCascade, int fFanout) {
    int i, nObjsAlloc = 1 + nIns() + nOuts() + countAnd2();
    Miaig pNew(nIns(), nOuts(), nObjsAlloc);
    pNew.attachTiming(_data->vCiArrs, _data->vCoReqs);
    memset(_data->pCopy, 0, sizeof(int) * nObjs()); // obj2lit
    if (fStrash) {
        assert(pNew._data->pTable == NULL);
        pNew._data->TableSize = Abc_PrimeCudd(3 * countAnd2());
        pNew._data->pTable = (int *)calloc(sizeof(int), 3 * pNew._data->TableSize);
    }
    Miaig2_ForEachInput(i)
        objCopy(i) = Rw2_Var2Lit(i, 0);
    Miaig2_ForEachNode(i) {
        assert(objFaninNum(i) > 0);
        if (fCascade)
            objCopy(i) = buildNodeCascade(pNew, objFanins(i), fCprop, fStrash);
        else
            objCopy(i) = buildNodeBalance(pNew, objFanins(i), fCprop, fStrash);
    }
    Miaig2_ForEachOutput(i)
        pNew.appendFanin(pNew.appendObj(), Rw2_Lit2LitL(_data->pCopy, objFanin0(i)));
    return pNew.dup(1, fFanout, 0);
}

// this duplicator converts two-input-node AIG into multi-input-node AIG
int *Miaig::createStops(void) {
    int i, *pStop = (int *)calloc(sizeof(int), nObjs());
    Miaig2_ForEachConstInput(i)
        pStop[i] = 2;
    Miaig2_ForEachNode(i) {
        assert(objFaninNum(i) == 2);
        int iLit0 = objFanin0(i);
        int iLit1 = objFanin1(i);
        pStop[Rw2_Lit2Var(iLit0)] += 1 + Rw2_LitIsCompl(iLit0);
        pStop[Rw2_Lit2Var(iLit1)] += 1 + Rw2_LitIsCompl(iLit1);
    }
    Miaig2_ForEachOutput(i)
        pStop[Rw2_Lit2Var(objFanin0(i))] += 2;
    return pStop;
}

void Miaig::collectSuper_rec(int iLit, int *pStop, rw2_vi *vSuper) {
    if (pStop[Rw2_Lit2Var(iLit)] > 1)
        Rw2_Vi_Push(vSuper, Rw2_Lit2LitL(_data->pCopy, iLit));
    else {
        assert(Rw2_LitIsCompl(iLit) == 0);
        collectSuper_rec(objFanin0(Rw2_Lit2Var(iLit)), pStop, vSuper);
        collectSuper_rec(objFanin1(Rw2_Lit2Var(iLit)), pStop, vSuper);
    }
}

Miaig Miaig::dupMulti(int nFaninMax, int nGrowth) {
    Miaig pNew(nIns(), nOuts(), nObjs());
    pNew.attachTiming(_data->vCiArrs, _data->vCoReqs);
    pNew.initializeFanouts();
    int *pStop = createStops();
    int i, k, iLit;
    rw2_vi *vArray = Rw2_Vi_Alloc(100);
    assert(nFaninMax >= 2 && nGrowth >= 1);
    memset(_data->pCopy, 0, sizeof(int) * nObjs()); // obj2lit
    Miaig2_ForEachConstInput(i)
        objCopy(i) = Rw2_Var2Lit(i, 0);
    Miaig2_ForEachNode(i) {
        if (pStop[i] == 1)
            continue;
        assert(pStop[i] > 1); // no dangling
        Rw2_Vi_Shrink(vArray, 0);
        collectSuper_rec(objFanin0(i), pStop, vArray);
        collectSuper_rec(objFanin1(i), pStop, vArray);
        assert(Rw2_Vi_Size(vArray) > 1);
        reduceFanins(vArray);
        assert(Rw2_Vi_Size(vArray) > 0);
        if (Rw2_Vi_Size(vArray) == 1)
            objCopy(i) = Rw2_Vi_Read(vArray, 0);
        else {
            int nFaninMaxLocal = 2 + (Rw2_Random_Num(0) % (nFaninMax - 1));
            int nGrowthLocal = 1 + (Rw2_Random_Num(0) % nGrowth);
            assert(nFaninMaxLocal >= 2 && nFaninMaxLocal <= nFaninMax);
            assert(nGrowthLocal >= 1 && nGrowthLocal <= nGrowth);

            if (Rw2_Vi_Size(vArray) > nFaninMaxLocal)
                Rw2_Vi_Randomize(vArray);
            // create a cascade of nodes
            while (Rw2_Vi_Size(vArray) > nFaninMaxLocal) {
                int iObj = pNew.appendObj();
                rw2_vi *vFanins = pNew.objFanins(iObj);
                assert(vFanins->ptr == NULL);
                vFanins->cap = nFaninMaxLocal + nGrowthLocal;
                vFanins->ptr = (int *)malloc(sizeof(int) * vFanins->cap);
                Rw2_Vi_ForEachEntryStop(vArray, iLit, k, nFaninMaxLocal)
                    pNew.appendFanin(iObj, iLit);
                assert(Rw2_Vi_Space(vFanins) == nGrowthLocal);
                for (k = 0; k < nFaninMaxLocal; k++)
                    Rw2_Vi_Drop(vArray, 0);
                Rw2_Vi_Push(vArray, Rw2_Var2Lit(iObj, 0));
            }
            // create the last node
            int iObj = pNew.appendObj();
            rw2_vi *vFanins = pNew.objFanins(iObj);
            assert(vFanins->ptr == NULL);
            vFanins->cap = Rw2_Vi_Size(vArray) + nGrowthLocal;
            vFanins->ptr = (int *)malloc(sizeof(int) * vFanins->cap);
            Rw2_Vi_ForEachEntry(vArray, iLit, k)
                pNew.appendFanin(iObj, iLit);
            assert(Rw2_Vi_Space(vFanins) == nGrowthLocal);
            objCopy(i) = Rw2_Var2Lit(iObj, 0);
        }
    }
    Miaig2_ForEachOutput(i)
        pNew.appendFanin(pNew.appendObj(), Rw2_Lit2LitL(_data->pCopy, objFanin0(i)));
    Rw2_Vi_Free(vArray);
    free(pStop);
    return pNew;
}

Miaig Miaig::dupExtend(int nFaninMax, int nGrowth) {
    Miaig pNew(nIns(), nOuts(), nObjs());
    pNew.attachTiming(_data->vCiArrs, _data->vCoReqs);
    pNew.initializeFanouts();
    memset(_data->pCopy, 0, sizeof(int) * nObjs());
    int iObj, k, iLit; // obj2obj
    Miaig2_ForEachInput(iObj)
        objCopy(iObj) = iObj;
    Miaig2_ForEachNodeOutput(iObj) {
        int nFaninMaxLocal = 2 + (Rw2_Random_Num(0) % (nFaninMax - 1));
        int nGrowthLocal = 1 + (Rw2_Random_Num(0) % nGrowth);
        assert(objFaninNum(iObj) > 0);
        objCopy(iObj) = pNew.appendObj();
        rw2_vi *vFanins = pNew.objFanins(iObj);
        assert(vFanins->ptr == NULL);
        vFanins->cap = nFaninMaxLocal + nGrowthLocal;
        vFanins->ptr = (int *)malloc(sizeof(int) * vFanins->cap);
        Miaig2_ForEachObjFanin(iObj, iLit, k)
            pNew.appendFanin(objCopy(iObj), Rw2_Lit2LitV(_data->pCopy, iLit));
    }
    return pNew;
}

// compute truth table of the node
/**Function*************************************************************

  Synopsis    [Simulates small multi-input ANDs with a single output pass.]

  Description [Precompute the input pointers and polarities outside the
               word loop.  All operations are portable unsigned words.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Miaig::truthSimNode(int i, word *pResult) {
    int k, w, iLit, nFans = objFaninNum(i), nSize = nWords();
    if (!nFans) return;
    word *pOut = pResult ? pResult : objTruth(i, objType(i));
    word *pIns[4], Phases[4];
    for (k = 0; k < std::min(nFans, 4); k++) {
        iLit = Rw2_Vi_Read(objFanins(i), k);
        int iVar = Rw2_Lit2Var(iLit);
        pIns[k] = objTruth(iVar, objType(iVar));
        Phases[k] = Rw2_LitIsCompl(iLit) ? ~(word)0 : 0;
    }
    if (nFans == 1) {
        for (w = 0; w < nSize; w++) pOut[w] = pIns[0][w] ^ Phases[0];
    } else if (nFans == 2) {
        for (w = 0; w < nSize; w++) pOut[w] = (pIns[0][w] ^ Phases[0]) & (pIns[1][w] ^ Phases[1]);
    } else if (nFans == 3) {
        for (w = 0; w < nSize; w++) pOut[w] = (pIns[0][w] ^ Phases[0]) & (pIns[1][w] ^ Phases[1]) & (pIns[2][w] ^ Phases[2]);
    } else {
        for (w = 0; w < nSize; w++) pOut[w] = (pIns[0][w] ^ Phases[0]) & (pIns[1][w] ^ Phases[1]) & (pIns[2][w] ^ Phases[2]) & (pIns[3][w] ^ Phases[3]);
        Miaig2_ForEachObjFaninStart(i, iLit, k, 4) {
            int iVar = Rw2_Lit2Var(iLit);
            Rw2_Tt_Sharp(pOut, objTruth(iVar, objType(iVar)), Rw2_LitIsCompl(iLit), nSize);
        }
    }
}

// compute truth table of the node using a subset of its current fanin
word *Miaig::truthSimNodeSubset(int i, int m) {
    int k, iLit, Counter = 0;
    assert(m > 0);
    Miaig2_ForEachObjFanin(i, iLit, k) {
        if ((m >> k) & 1) { // fanin is included in the subset
            if (Counter++ == 0)
                Rw2_Tt_DupC(_data->pProd, objTruth(Rw2_Lit2Var(iLit), 0), Rw2_LitIsCompl(iLit), nWords());
            else
                Rw2_Tt_Sharp(_data->pProd, objTruth(Rw2_Lit2Var(iLit), 0), Rw2_LitIsCompl(iLit), nWords());
        }
    }
    assert(Counter == Rw2_Tt_BitCount16(m));
    return _data->pProd;
}

word *Miaig::truthSimNodeSubset2(int i, rw2_vi *vFanins, int nFanins) {
    int k, iLit;
    Rw2_Vi_ForEachEntryStop(vFanins, iLit, k, nFanins) {
        if (k == 0) Rw2_Tt_DupC(_data->pProd, objTruth(Rw2_Lit2Var(iLit), 0), Rw2_LitIsCompl(iLit), nWords());
        else Rw2_Tt_Sharp(_data->pProd, objTruth(Rw2_Lit2Var(iLit), 0), Rw2_LitIsCompl(iLit), nWords());
    }
    return _data->pProd;
}

void Miaig::initializeTruth(void) {
    int i;
    if (_data->pTruths[0])
        return;
    _data->pTruths[0] = (word *)calloc(sizeof(word), (size_t)3 * nWords() * nObjs());
    _data->pTruths[1] = _data->pTruths[0] + 1 * nWords() * nObjs();
    _data->pTruths[2] = _data->pTruths[0] + 2 * nWords() * nObjs();
    _data->pCare = (word *)calloc(sizeof(word), nWords());
    _data->pProd = (word *)calloc(sizeof(word), nWords());
    float MemMB = 8.0 * nWords() * (3 * nObjs() + 2) / (1 << 20);
    if (MemMB > 100.0)
        printf("Allocated %d truth tables of %d-variable functions (%.2f MB),\n", 3 * nObjs() + 2, nIns(), MemMB);
    nTravIds()++;
    Miaig2_ForEachInput(i)
        Rw2_Tt_ElemInit(objTruth(i, 0), i - 1, nWords());
    Miaig2_ForEachNodeOutput(i)
        truthSimNode(i);
    Miaig2_ForEachOutput(i)
        assert(objFaninNum(i) == 1);
    Miaig2_ForEachOutput(i)
        Rw2_Tt_Dup(objTruth(i, 2), objTruth(i, 0), nWords());
}

/**Function*************************************************************

  Synopsis    [Propagates only function changes through the fanout cone.]

  Description [Structural edits that leave a node's truth table unchanged
               do not invalidate downstream tables.  Scratch copy marks
               are local to this update and independent of traversal IDs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Miaig::truthUpdate(rw2_vi *vTfo, word *pExc, int fCheck) {
    int i, iTemp, nFails = 0;
    nTravIds()++;
    memset(_data->pCopy, 0, sizeof(int) * nObjs());
    Rw2_Vi_ForEachEntry(vTfo, iTemp, i) {
        int k, iLit, fChanged = i == 0;
        Miaig2_ForEachObjFanin(iTemp, iLit, k)
            fChanged |= objCopy(Rw2_Lit2Var(iLit));
        if (fChanged) {
            truthSimNode(iTemp, objTruth(iTemp, 1));
            if (!Rw2_Tt_Equal(objTruth(iTemp, 0), objTruth(iTemp, 1), nWords())) {
                Rw2_Tt_Dup(objTruth(iTemp, 0), objTruth(iTemp, 1), nWords());
                objCopy(iTemp) = 1;
            }
        }
        if (fCheck && objIsPo(iTemp)) {
            int fEqual = pExc ? Rw2_Tt_EqualOnCare(pExc + objPoIdx(iTemp) * nWords(), objTruth(iTemp, 2), objTruth(iTemp, 0), nWords())
                              : Rw2_Tt_Equal(objTruth(iTemp, 2), objTruth(iTemp, 0), nWords());
            if (!fEqual) nFails++;
        }
    }
    if (fCheck && nFails)
        printf("Verification failed for %d outputs after updating node %d.\n", nFails, Rw2_Vi_Read(vTfo, 0));
}

int Miaig::computeTfo_rec(int iObj) {
    int k, iLit, Value = 0;
    if (objTravId(iObj) == nTravIds())
        return 1;
    if (objTravId(iObj) == nTravIds() - 1)
        return 0;
    Miaig2_ForEachObjFanin(iObj, iLit, k) {
        Value |= computeTfo_rec(Rw2_Lit2Var(iLit));
    }
    objTravId(iObj) = nTravIds() - 1 + Value;
    if (Value) Rw2_Vi_Push(_data->vTfo, iObj);
    return Value;
}

rw2_vi *Miaig::computeTfo(int iObj) {
    int i;
    assert(objIsNode(iObj));
    nTravIds() += 2;
    objTravId(iObj) = nTravIds();
    Rw2_Vi_Fill(_data->vTfo, 1, iObj);
    Miaig2_ForEachConstInput(i)
        objTravId(i) = nTravIds() - 1;
    Miaig2_ForEachOutput(i)
        computeTfo_rec(i);
    Miaig2_ForEachNode(i) {
        computeTfo_rec(i);
    }
    return _data->vTfo;
}

word *Miaig::computeCareSet(int iObj, word *pExc) {
    rw2_vi *vTfo = computeTfo(iObj);
    int i, iTemp;
    if (!pExc) {
        Rw2_Vi_ForEachEntryStart(vTfo, iTemp, i, 1) {
            if (objIsPo(iTemp) && Rw2_Lit2Var(objFanin0(iTemp)) == iObj) {
                Rw2_Tt_Fill(_data->pCare, nWords());
                return _data->pCare;
            }
        }
    }
    Rw2_Tt_Not(objTruth(iObj, 1), objTruth(iObj, 0), nWords());
    Rw2_Tt_Clear(_data->pCare, nWords());
    if (!pExc) {
        Rw2_Vi_ForEachEntryStart(vTfo, iTemp, i, 1) {
            truthSimNode(iTemp);
            if (objIsPo(iTemp)) {
                Rw2_Tt_OrXor(_data->pCare, objTruth(iTemp, 0), objTruth(iTemp, 1), nWords());
                if (Rw2_Tt_IsConst1(_data->pCare, nWords())) break;
            }
        }
    } else {
        Rw2_Vi_ForEachEntryStart(vTfo, iTemp, i, 1) {
            truthSimNode(iTemp);
            if (objIsPo(iTemp))
                Rw2_Tt_OrXorAnd(_data->pCare, objTruth(iTemp, 0), objTruth(iTemp, 1), pExc + objPoIdx(iTemp) * nWords(), nWords());
        }
    }
    return _data->pCare;
}

// adds fanin pair to storage
void Miaig::addPair(rw2_vi *vPair, int iFan1, int iFan2) {
    assert(iFan1 < iFan2);
    int i, *pArray = Rw2_Vi_Array(vPair);
    assert(Rw2_Vi_Size(vPair) % 3 == 0);
    for (i = 0; i < Rw2_Vi_Size(vPair); i += 3)
        if (pArray[i] == iFan1 && pArray[i + 1] == iFan2)
            break;
    if (i == Rw2_Vi_Size(vPair)) {
        Rw2_Vi_Push(vPair, iFan1);
        Rw2_Vi_Push(vPair, iFan2);
        Rw2_Vi_Push(vPair, 1);
        pArray = Rw2_Vi_Array(vPair);
    }
    pArray[i + 2]++;
}

// find fanin pair that appears most often
int Miaig::findPair(rw2_vi *vPair) {
    int iBest = -1, BestCost = 0;
    int i, *pArray = Rw2_Vi_Array(vPair);
    assert(Rw2_Vi_Size(vPair) % 3 == 0);
    for (i = 0; i < Rw2_Vi_Size(vPair); i += 3)
        if (BestCost < pArray[i + 2]) {
            BestCost = pArray[i + 2];
            iBest = i;
        }
    //if ( iBest >= 0 ) printf( "Extracting pair (%d, %d) used %d times.\n", pArray[iBest], pArray[iBest+1], pArray[iBest+2] );
    return iBest;
}

// updates one fanin array by replacing the pair with a new literal (iLit)
int Miaig::updateFanins(rw2_vi *vFans, int iFan1, int iFan2, int iLit) {
    int f1, f2, iFan1_, iFan2_;
    Rw2_Vi_ForEachEntry(vFans, iFan1_, f1) if (iFan1_ == iFan1)
        Rw2_Vi_ForEachEntryStart(vFans, iFan2_, f2, f1 + 1) if (iFan2_ == iFan2) {
        assert(f1 < f2);
        Rw2_Vi_Drop(vFans, f2);
        Rw2_Vi_Drop(vFans, f1);
        Rw2_Vi_Push(vFans, iLit);
        return 1;
    }
    return 0;
}

// updates the network by extracting one pair
void Miaig::extractBest(rw2_vi *vPairs) {
    int i, iObj = appendObj();
    int Counter = 0, *pArray = Rw2_Vi_Array(vPairs);
    int iBest = findPair(vPairs);
    assert(iBest >= 0);
    //printf( "Creating node %d with fanins (%d, %d).\n", iObj, pArray[iBest], pArray[iBest+1] );
    assert(Rw2_Vi_Size(objFanins(iObj)) == 0);
    appendFanin(iObj, pArray[iBest]);
    appendFanin(iObj, pArray[iBest + 1]);
    Miaig2_ForEachNode(i)
        Counter += updateFanins(objFanins(i), pArray[iBest], pArray[iBest + 1], Rw2_Var2Lit(iObj, 0));
    assert(Counter == pArray[iBest + 2]);
}

/**Function*************************************************************

  Synopsis    [Finds repeated fanin pairs using dense or sparse storage.]

  Description [The set is used only for membership, never iteration.
               Both representations add pairs on the same visit and thus
               preserve candidate order, counts, and extraction ties.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
rw2_vi *Miaig::findPairs(word *pSto, int nWords) {
    std::unordered_set<word> Seen;
    rw2_vi *vPairs = Rw2_Vi_Alloc(30);
    int i, f1, f2, iFan1, iFan2;
    Miaig2_ForEachNode(i) {
        rw2_vi *vFans = objFanins(i);
        Rw2_Vi_ForEachEntry(vFans, iFan1, f1) {
            word *pRowFan1 = pSto ? pSto + (size_t)iFan1 * nWords : NULL;
            Rw2_Vi_ForEachEntryStart(vFans, iFan2, f2, f1 + 1) {
                if (pRowFan1) {
                    if (Rw2_Tt_GetBit(pRowFan1, iFan2)) addPair(vPairs, iFan1, iFan2);
                    else Rw2_Tt_SetBit(pRowFan1, iFan2);
                } else if (!Seen.insert(((word)(unsigned)iFan1 << 32) | (unsigned)iFan2).second)
                    addPair(vPairs, iFan1, iFan2);
            }
        }
    }
    return vPairs;
}

/**Function*************************************************************

  Synopsis    [Extracts shared fanin pairs without a quadratic memory requirement.]

  Description [Use a bitmap up to 256 MiB, otherwise track only visited pairs.
               Object storage is bounded separately before growing arrays.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Miaig::findShared(int nNewNodesMax) {
    const size_t Budget = 256 * 1024 * 1024;
    if (nNewNodesMax <= 0) return 0;
    if (nNewNodesMax > ABC_INT_MAX - nObjs()) {
        printf("Rewire2: sharing skipped because its node count exceeds integer limits.\n");
        return 0;
    }
    int nAlloc = Rw2_MaxInt(nObjsAlloc(), nObjs() + nNewNodesMax);
    word nLits = (word)2 * nAlloc, nWordsWide = (nLits + 63) / 64;
    if (nLits > ABC_INT_MAX || (size_t)nAlloc > Budget / (sizeof(int) + sizeof(rw2_vi))) {
        printf("Rewire2: sharing skipped because its object storage exceeds supported limits.\n");
        return 0;
    }
    size_t nBytesAll = nWordsWide <= Budget / sizeof(word) / nLits ?
        sizeof(word) * (size_t)nWordsWide * (size_t)nLits : 0;
    word *pSto = nBytesAll ? (word *)malloc(nBytesAll) : NULL;
    if (nAlloc > nObjsAlloc()) {
        int *pCopyNew = (int *)realloc((void *)_data->pCopy, sizeof(int) * (size_t)nAlloc);
        if (!pCopyNew) { free(pSto); return 0; }
        _data->pCopy = pCopyNew;
        rw2_vi *pFaninsNew = (rw2_vi *)realloc((void *)_data->pvFanins, sizeof(rw2_vi) * (size_t)nAlloc);
        if (!pFaninsNew) { free(pSto); return 0; }
        _data->pvFanins = pFaninsNew;
        nObjsAlloc() = nAlloc;
        memset(_data->pCopy + nObjs(), 0, sizeof(int) * (size_t)(nAlloc - nObjs()));
        memset(_data->pvFanins + nObjs(), 0, sizeof(rw2_vi) * (size_t)(nAlloc - nObjs()));
    }
    assert(sizeof(word) == 8);
    int i, nWords = (int)nWordsWide;
    rw2_vi *vPairs;
    for (i = 0; i < nNewNodesMax; i++) {
        if (pSto) memset(pSto, 0, nBytesAll);
        nObjs() -= i;
        vPairs = findPairs(pSto, nWords);
        nObjs() += i;
        if (Rw2_Vi_Size(vPairs) > 0)
            extractBest(vPairs);
        int Size = Rw2_Vi_Size(vPairs);
        Rw2_Vi_Free(vPairs);
        if (Size == 0)
            break;
    }
    free(pSto);
    return i;
}

int Miaig::checkConst(int iObj, word *pCare, word *pExc, int fCheck, int fVerbose) {
    word *pFunc = objTruth(iObj, 0);
    int iLit, i;
    if (!Rw2_Tt_IntersectC(pCare, pFunc, 0, nWords())) {
        derefObj_rec(iObj, -1);
        if (_data->pvFanouts) {
            Miaig2_ForEachObjFanin(iObj, iLit, i) {
                Rw2_Vi_Remove(objFanouts(Rw2_Lit2Var(iLit)), iObj);
            }
        }
        Rw2_Vi_Fill(objFanins(iObj), 1, 0); // const0
        refObj(iObj);
        truthUpdate(_data->vTfo, pExc, fCheck);
        if (fVerbose) printf("Detected Const0 at node %d.\n", iObj);
        return 1;
    }
    if (!Rw2_Tt_IntersectC(pCare, pFunc, 1, nWords())) {
        derefObj_rec(iObj, -1);
        if (_data->pvFanouts) {
            Miaig2_ForEachObjFanin(iObj, iLit, i) {
                Rw2_Vi_Remove(objFanouts(Rw2_Lit2Var(iLit)), iObj);
            }
        }
        Rw2_Vi_Fill(objFanins(iObj), 1, 1); // const1
        refObj(iObj);
        truthUpdate(_data->vTfo, pExc, fCheck);
        if (fVerbose) printf("Detected Const1 at node %d.\n", iObj);
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Preserves the original stable ordering with one comparison.]

  Description [Candidate entries are node IDs.  The original heuristic
               interprets them as literals; keep that convention here so
               fixed-iteration runs retain their original search order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Miaig::expandOneHeuristicSort(int *pOrderF, int fTiming) {
    std::stable_sort(pOrderF, pOrderF + Rw2_Vi_Size(_data->vOrderF), [&](int a, int b) {
        int i = Rw2_Lit2Var(a), j = Rw2_Lit2Var(b);
        int li = objLevel(i), lj = objLevel(j);
        if (fTiming && objRequire(i) - li != objRequire(j) - lj)
            return objRequire(i) - li > objRequire(j) - lj;
        if ((li == 0) != (lj == 0)) return li == 0;
        if (objRef(i) != objRef(j)) return objRef(i) < objRef(j);
        return li > lj;
    });
}

int Miaig::expandOne(int iObj, int nAddedMax, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose) {
    if (fTiming && objRequire(iObj) - objLevel(iObj) < 0) return 0; // skip nodes with slack violations
    int i, k, n, iLit, nAdded = 0;
    word *pCare = computeCareSet(iObj, pExc);
    assert(nAddedMax > 0);
    assert(nAddedMax <= Rw2_Vi_Space(objFanins(iObj)));
    // mark node's fanins
    Miaig2_ForEachObjFanin(iObj, iLit, k)
        objTravId(Rw2_Lit2Var(iLit)) = nTravIds();
    // compute the onset
    word *pOnset = _data->pProd;
    Rw2_Tt_And(pOnset, objTruth(iObj, 0), pCare, nWords());
    // create a random order of fanin candidates
    Rw2_Vi_Shrink(_data->vOrderF, 0);
    if (nDist) markDistanceN(iObj, nDist);
    Miaig2_ForEachInputNode(i) {
        if (nDist && objDist(i) < 0 && !objIsPi(i)) continue;
        // if (nExpandableLevel && objLevel(i) - objLevel(iObj) > nExpandableLevel) continue;
        if (objTravId(i) != nTravIds() && (objIsPi(i) || (objFaninNum(i) > 1 && objRef(i) > 0))) // this node is NOT in the TFO
            Rw2_Vi_Push(_data->vOrderF, i);
    }
    Rw2_Vi_Randomize(_data->vOrderF);

    // Shuffle the full list first to retain random-number consumption and
    // tie order, then discard candidates that cannot imply either phase.
    // Most candidates fail after inspecting only one or two truth words.
    int nKeep = 0;
    Rw2_Vi_ForEachEntry(_data->vOrderF, i, k) {
        if (!Rw2_Tt_IntersectC(pOnset, objTruth(i, 0), 1, nWords()) ||
            !Rw2_Tt_IntersectC(pOnset, objTruth(i, 0), 0, nWords()))
            Rw2_Vi_Write(_data->vOrderF, nKeep++, i);
    }
    Rw2_Vi_Shrink(_data->vOrderF, nKeep);
    this->expandOneHeuristicSort(Rw2_Vi_Array(_data->vOrderF), fTiming);

    // iterate through candidate fanins (nodes that are not in the TFO of iObj)
    Rw2_Vi_ForEachEntry(_data->vOrderF, i, k) {
        assert(objTravId(i) != nTravIds());
        if (fTiming && Rw2_MaxInt(objLevel(iObj), objLevel(i)) + objFaninNum(iObj) > objRequire(iObj)) continue;
        // new fanin can be added if its offset does not intersect with the node's onset
        for (n = 0; n < 2; n++)
            if (!Rw2_Tt_IntersectC(pOnset, objTruth(i, 0), !n, nWords())) {
                if (fVerbose) printf("Adding node %d fanin %d\n", iObj, Rw2_Var2Lit(i, n));
                appendFanin(iObj, Rw2_Var2Lit(i, n));
                objRef(i)++;
                nAdded++;
                if (fTiming) {
                    updateLevels_rec(iObj);
                    updateRequire_rec(iObj);
                    // checkTiming(_data->vCiArrs, _data->vCoReqs);
                }
                break;
            }
        if (nAdded == nAddedMax)
            break;
    }
    if (nAdded)
        truthUpdate(_data->vTfo, pExc, fCheck);
    //assert( objFaninNum(iObj) <= nFaninMax );
    return nAdded;
}

/**Function*************************************************************

  Synopsis    [Combines the two stable fanin-ordering passes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Miaig::reduceOneHeuristicSort(int *pOrderF, int fTiming) {
    std::stable_sort(pOrderF, pOrderF + Rw2_Vi_Size(_data->vOrderF), [&](int a, int b) {
        int i = Rw2_Lit2Var(a), j = Rw2_Lit2Var(b);
        int li = objLevel(i), lj = objLevel(j);
        if ((li == 0) != (lj == 0)) return li == 0;
        if (objRef(i) != objRef(j)) return objRef(i) < objRef(j);
        return li < lj;
    });
}

int Miaig::reduceOne(int iObj, int fOnlyConst, int fOnlyBuffer, int fHeuristic, word *pExc, int fTiming, int fCheck, int fVerbose, int fReuseCare) {
    int n, k, iLit, nFans = objFaninNum(iObj);
    // The caller may have changed only this node's fanins.  Observability
    // is a property of its fanout cone, independent of its own function.
    if (fReuseCare) computeTfo(iObj);
    word *pCare = fReuseCare ? _data->pCare : computeCareSet(iObj, pExc);
    if (checkConst(iObj, pCare, pExc, fCheck, fVerbose))
        return nFans;
    if (fOnlyConst)
        return 0;
    if (nFans == 1)
        return 0;
    // if one fanin can be used, take it
    word *pFunc = objTruth(iObj, 0);
    Miaig2_ForEachObjFanin(iObj, iLit, k) {
        Rw2_Tt_DupC(_data->pProd, objTruth(Rw2_Lit2Var(iLit), 0), Rw2_LitIsCompl(iLit), nWords());
        if (Rw2_Tt_EqualOnCare(pCare, pFunc, _data->pProd, nWords())) {
            setFanin(iObj, iLit);
            truthUpdate(_data->vTfo, pExc, fCheck);
            if (fVerbose) printf("Reducing node %d fanin count from %d to %d.\n", iObj, nFans, objFaninNum(iObj));
            return nFans - 1;
        }
    }
    if (fOnlyBuffer)
        return 0;
    Rw2_Vi_Shrink(_data->vOrderF, 0);
    Miaig2_ForEachObjFanin(iObj, iLit, k)
        Rw2_Vi_Push(_data->vOrderF, iLit);
    Rw2_Vi_Randomize(_data->vOrderF);

    if (fHeuristic) {
        this->reduceOneHeuristicSort(Rw2_Vi_Array(_data->vOrderF), fTiming);
    }

    assert(Rw2_Vi_Size(_data->vOrderF) == nFans);
    // try to remove fanins starting from the end of the list
    for (n = Rw2_Vi_Size(_data->vOrderF) - 1; n >= 0; n--) {
        int iFanin = Rw2_Vi_Drop(_data->vOrderF, n);
        word *pProd = truthSimNodeSubset2(iObj, _data->vOrderF, Rw2_Vi_Size(_data->vOrderF));
        if (!Rw2_Tt_EqualOnCare(pCare, pFunc, pProd, nWords()))
            Rw2_Vi_Push(_data->vOrderF, iFanin);
    }
    assert(Rw2_Vi_Size(_data->vOrderF) >= 1);
    // update the node if it is reduced
    if (Rw2_Vi_Size(_data->vOrderF) < nFans) {
        derefObj(iObj);
        if (_data->pvFanouts) {
            int iLit2, i;
            Miaig2_ForEachObjFanin(iObj, iLit2, i) {
                Rw2_Vi_Remove(objFanouts(Rw2_Lit2Var(iLit2)), iObj);
            }
        }
        Rw2_Vi_Shrink(objFanins(iObj), 0);
        Rw2_Vi_ForEachEntry(_data->vOrderF, iLit, k) {
            if (_data->pvFanouts) {
                Rw2_Vi_PushOrder(objFanouts(Rw2_Lit2Var(iLit)), iObj);
            }
            Rw2_Vi_PushOrder(objFanins(iObj), iLit);
        }
        refObj(iObj);
        truthUpdate(_data->vTfo, pExc, fCheck);
        if (fVerbose) printf("Reducing node %d fanin count from %d to %d.\n", iObj, nFans, objFaninNum(iObj));
        return nFans - Rw2_Vi_Size(_data->vOrderF);
    }
    return 0;
}

int Miaig::expandThenReduceOne(int iNode, int nFaninAddLimit, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose) {
    int fReuseCare = !fTiming || objRequire(iNode) >= objLevel(iNode);
    expandOne(iNode, std::min(Rw2_Vi_Space(objFanins(iNode)), nFaninAddLimit), nDist, nExpandableLevel, pExc, fTiming, fCheck, fVerbose);
    reduceOne(iNode, 0, 0, 0, pExc, fTiming, fCheck, fVerbose, fReuseCare);
    return 0;
}

rw2_vi *Miaig::createRandomOrder(void) {
    int i;
    Rw2_Vi_Shrink(_data->vOrder, 0);
    Miaig2_ForEachNode(i)
        Rw2_Vi_Push(_data->vOrder, i);
    Rw2_Vi_Randomize(_data->vOrder);
    return _data->vOrder;
}

Miaig Miaig::expand(int nFaninAddLimitAll, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose) {
    int i, iNode, nAdded = 0;
    assert(nFaninAddLimitAll > 0);
    rw2_vi *vOrder = createRandomOrder();

    initializeTruth();
    initializeRefs();
    initializeLevels();
    if (nDist) initializeDists();
    if (fTiming) initializeRequire();
    Rw2_Vi_ForEachEntry(vOrder, iNode, i) {
        nAdded += expandOne(iNode, std::min(Rw2_Vi_Space(objFanins(iNode)), nFaninAddLimitAll - nAdded), nDist, nExpandableLevel, pExc, fTiming, fCheck, fVerbose);
        if (nAdded >= nFaninAddLimitAll)
            break;
    }
    assert(nAdded <= nFaninAddLimitAll);
    if (fCheck) verifyRefs();
    return dupDfs();
}

// perform shared logic extraction
Miaig Miaig::share(int nNewNodesMax) {
    Miaig pCopy = dup(0, 0, 0);
    int nNewNodes = pCopy.findShared(nNewNodesMax);
    if (nNewNodes == 0)
        return pCopy;
    // temporarily create "hidden" nodes for DFS duplicator
    pCopy.nObjs() -= nNewNodes;
    Miaig pNew = pCopy.dupDfs();
    pCopy.nObjs() += nNewNodes;
    return pNew;
}

Miaig Miaig::reduce(word *pExc, int fTiming, int fCheck, int fVerbose) {
    int i, iNode;
    rw2_vi *vOrder = topoCollect();

    initializeTruth();
    initializeRefs();
    initializeLevels();
    // works best for final
    Rw2_Vi_ForEachEntry(vOrder, iNode, i)
        reduceOne(iNode, 0, 0, 1, pExc, fTiming, fCheck, fVerbose);
    if (fCheck) verifyRefs();
    return dupStrash(1, 1, !fTiming);
}

Miaig Miaig::expandThenReduce(int nFaninAddLimit, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int fVerbose) {
    int i, iNode;
    rw2_vi *vOrder = topoCollect();

    initializeTruth();
    initializeRefs();
    initializeLevels();
    if (nDist) initializeDists();
    if (fTiming) initializeRequire();
    Rw2_Vi_ForEachEntry(vOrder, iNode, i) {
        expandThenReduceOne(iNode, nFaninAddLimit, nDist, nExpandableLevel, pExc, fTiming, fCheck, fVerbose);
    }
    if (fCheck) verifyRefs();
    return dupDfs().dupStrash(1, 1, !fTiming, 1);
}

Miaig Miaig::expandShareReduce(int nFaninAddLimitAll, int nDivs, int nDist, int nExpandableLevel, word *pExc, int fTiming, int fCheck, int nVerbose) {
    // expand
    Miaig pNew = expand(nFaninAddLimitAll, nDist, nExpandableLevel, pExc, fTiming, fCheck, nVerbose);
    // share
    pNew = pNew.share(nDivs == -1 ? pNew.nObjs() : nDivs);
    // reduce
    pNew = pNew.reduce(pExc, fTiming, fCheck, nVerbose);
    return pNew;
}

void randomAddBest(std::vector<Miaig> &pBests, Miaig pNew, int nBestSave, Gia_ChMan_t *pChMan) {
    if ( pChMan ) {
        Gia_Man_t * pGia = pNew.toGia();
        Gia_ManDupChoicesAdd(pChMan, pGia);
        Gia_ManStop( pGia );
    }
    if (pBests.size() < nBestSave) {
        pBests.push_back(pNew);
    } else {
        int iNum = Rw2_Random_Num(0) % nBestSave;
        pBests[iNum] = pNew;
    }
}

Miaig randomRead(std::vector<Miaig> &pBests) {
    return pBests[Rw2_Random_Num(0) % pBests.size()];
}

Miaig randomReadExcept(std::vector<Miaig> &pBests, Miaig &pExcept) {
    int iNum = Rw2_Random_Num(0) % pBests.size();
    return (pBests[iNum] == pExcept) ? pBests[(iNum + 1) % pBests.size()] : pBests[iNum];
}

Miaig Miaig::rewire2(int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int fCheck, Gia_ChMan_t *pChMan, int nVerbose) {
    const int nRootSave = 8;
    const int nBestSave = 4;
    int iter = 0;
    int nRestart = 5000;
    std::vector<Miaig> pRoots = {this->dup(0, 0, 1)};
    std::vector<Miaig> pBests = {this->dup(0, 0, 1)}; Miaig pInit = pBests[0];
    iword clkStart = Rw2_Time_Clock();
    Miaig pNew;
    Miaig pRoot = pRoots[0];
    Miaig pBest = this->dup(0, 0, 1); int improved = 0;
    float (Miaig::*Miaig2_ObjectiveFunction)(int, int, int) = (nMode == 0) ? (fTiming ? &Miaig::countLevel: &Miaig::countAnd2) : (fTiming ? &Miaig::countMappedDelay : &Miaig::countMappedArea);
    int maxLevel = levelGrowRatio != 0 ? this->countLevel() * levelGrowRatio : 0;
    int nExpandableLevel = maxLevel ? maxLevel - this->countLevel() : 0;
    int fMapped = nMode == 1;
    word *pExc = _data->pExc;

    float initCost = ((&pRoot)->*Miaig2_ObjectiveFunction)(0, nMappedMode, fDch);
    float bestCost = initCost;
    int iterNotImproveAfterRestart = 0;
    if (nVerbose && maxLevel) printf("Max level         : %5d\n", maxLevel);
    if (nVerbose) printf("Initial target    : %5g (AND2 = %5g Level = %3g)\n", bestCost, this->countAnd2(1), this->countLevel());
    for (iter = 0; nIters ? iter < nIters : 1; iter++) {
        if (nVerbose) printf("\rIteration %7d(%zu) : %5g (AND2 = %5g Level = %3g) -> ", iter + 1, pBests.size(), ((&pRoot)->*Miaig2_ObjectiveFunction)(0, nMappedMode, fDch), pRoot.countAnd2(), pRoot.countLevel());
        if (nTimeOut && nTimeOut < 1.0 * (Rw2_Time_Clock() - clkStart) / CLOCKS_PER_SEC) break;
        if (bestCost == 0) break;
        pNew = (fTiming) ? pRoot.dupExtend(nFaninMax, nGrowth) : pRoot.dupMulti(nFaninMax, nGrowth);

        if (iter % 2 == 0) {
            pNew = pNew.expandThenReduce(nGrowth, nDist, nExpandableLevel, pExc, fTiming, fCheck, nVerbose > 1);
        }
        pNew = pNew.expandShareReduce(nExpands, nDivs, nDist, nExpandableLevel, pExc, fTiming, fCheck, nVerbose > 1);

        ++iterNotImproveAfterRestart;
        // report
        float rootTarget = ((&pRoot)->*Miaig2_ObjectiveFunction)(0, nMappedMode, fDch);
        float newTarget = ((&pNew)->*Miaig2_ObjectiveFunction)(1, nMappedMode, fDch);
        if (maxLevel ? pNew.countLevel() > maxLevel : 0) {
        } else if (bestCost >= newTarget) {
            if ((bestCost > newTarget) || (fTiming && (pNew.countAnd2() < pBest.countAnd2()))) {
                if (nVerbose) printf("%5g (AND2 = %5g Level = %3g) ", newTarget, pNew.countAnd2(), pNew.countLevel());
                if (nVerbose) Rw2_Time_PrintEndl("Elapsed time", Rw2_Time_Clock() - clkStart);
                bestCost = newTarget;
                pBests = {pNew.dup(0, 0, fMapped), pNew.dup(0, 0, fMapped)};
                pBest = pNew.dup(0, 0, fMapped), improved = 1;
                iterNotImproveAfterRestart = 0;
            } else if (!fTiming || (fTiming && pNew.countAnd2() <= pBest.countAnd2())) {
                randomAddBest(pBests, pNew.dup(0, 0, fMapped), nBestSave, pChMan);
            }
        }
        // compare
        if (maxLevel ? pNew.countLevel() > maxLevel : 0) {
        } else if (rootTarget < newTarget) {
            if (iterNotImproveAfterRestart > nRestart) {
                pNew = (fTiming) ? randomRead(pBests).dupExtend(nFaninMax, nGrowth) : randomRead(pBests).dupMulti(nFaninMax, nGrowth);
                pNew = pNew.expand(nExpands, nDist, nExpandableLevel, pExc, fTiming, fCheck, nVerbose > 1);
                pNew = pNew.share(nDivs == -1 ? pNew.nObjs() : nDivs);
                pNew = pNew.dupStrash(1, 1, 0);
                pRoots = {pNew};
                iterNotImproveAfterRestart = 0;
            } else if ((!fTiming && (rootTarget * 1.05 > newTarget))) {
                pRoots = {pNew};
            }
        } else if (rootTarget == newTarget) {
            randomAddBest(pRoots, pNew, nRootSave, pChMan);
        } else {
            pRoots = {pNew};
        }
        pRoot = randomRead(pRoots);
        // Keep diversification within a plateau, but let stochmap move to a
        // different partition once this many iterations have found no gain.
        if (nStall && iterNotImproveAfterRestart >= nStall) {
            iter++;
            break;
        }
    }
    if (nVerbose) Rw2_Time_PrintEndl("Total solving time", Rw2_Time_Clock() - clkStart);
    if (nVerbose) printf("Cumulatively reduced %s by %.2f %% (%g -> %g) after %d iterations.\n", fTiming ? "delay" : "area", initCost ? 100.0*(initCost - bestCost) / initCost : 0.0, initCost, bestCost, iter);
    return improved ? pBest : randomReadExcept(pBests, pInit);
}

} // namespace Rewire2

#ifdef RW2_ABC
ABC_NAMESPACE_IMPL_END
#endif // RW2_ABC
