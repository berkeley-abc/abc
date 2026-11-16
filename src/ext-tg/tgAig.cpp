#include "tgLog.h"
/**CFile****************************************************************
  FileName    [tgAig.cpp]
  SystemName  [ABC: Logic synthesis and verification system.]
  Synopsis    [PA-only AIG replacement with cached reverse levels.]
  Author      [Original replacement/helpers: Alan Mishchenko, UC Berkeley.]
  Description [Renamed copies from src/base/abc/abcAig.c; upstream is untouched.
               Hashing, deletion, worklist order, and level values are preserved.
               Only reverse-level fanout maxima are memoized per replacement.]
***********************************************************************/
#include "tgAig.h"
#include "tgProfile.h"
#include <algorithm>
#include <cstdlib>
#include <vector>
#include <climits>
ABC_NAMESPACE_IMPL_START

// The private manager definition is copied verbatim from abcAig.c. Keep it
// synchronized with that file when updating upstream ABC. No layout is changed.
struct Abc_Aig_t_
{
    Abc_Ntk_t *pNtkAig;          // the AIG network
    Abc_Obj_t *pConst1;          // the constant 1 object (not a node!)
    Abc_Obj_t **pBins;           // the table bins
    int nBins;                   // the size of the table
    int nEntries;                // the total number of entries in the table
    Vec_Ptr_t *vNodes;           // the temporary array of nodes
    Vec_Ptr_t *vStackReplaceOld; // the nodes to be replaced
    Vec_Ptr_t *vStackReplaceNew; // the nodes to be used for replacement
    Vec_Vec_t *vLevels;          // the nodes to be updated
    Vec_Vec_t *vLevelsR;         // the nodes to be updated
    Vec_Ptr_t *vAddedCells;      // the added nodes
    Vec_Ptr_t *vUpdatedNets;     // the nodes whose fanouts have changed

    int nStrash0;
    int nStrash1;
    int nStrash5;
    int nStrash2;
};

#define Abc_AigBinForEachEntry(pBin, pEnt) for (pEnt = pBin; pEnt; pEnt = pEnt->pNext)

static unsigned Tg_HashKey2(Abc_Obj_t *p0, Abc_Obj_t *p1, int TableSize);
static Abc_Obj_t *Tg_AigAndCreateFrom(Abc_Aig_t *pMan, Abc_Obj_t *p0, Abc_Obj_t *p1,
                                      Abc_Obj_t *pAnd);
static void Tg_AigAndDelete(Abc_Aig_t *pMan, Abc_Obj_t *pThis);
static void Tg_AigRemoveFromLevelStructure(Vec_Vec_t *vStruct, Abc_Obj_t *pNode);
static void Tg_AigRemoveFromLevelStructureR(Vec_Vec_t *vStruct, Abc_Obj_t *pNode);
static void Tg_AigReplace_int(Abc_Aig_t *pMan, Abc_Obj_t *pOld, Abc_Obj_t *pNew, int fUpdateLevel);
static void Tg_AigUpdateLevel_int(Abc_Aig_t *pMan);

// Preserve ABC's ascending bucket traversal exactly while excluding the
// untouched prefix and suffix. A range has constant-time insertion overhead;
// dense propagation does not pay for a heap entry at every level.
struct Tg_LevelRange
{
    int first = INT_MAX, last = -1;
};
static Tg_LevelRange s_ForwardBuckets, s_ReverseBuckets;
static void Tg_QueueLevel(Vec_Vec_t *buckets, int level, Abc_Obj_t *node, Tg_LevelRange &range)
{
    range.first = std::min(range.first, level);
    range.last = std::max(range.last, level);
    Vec_VecPush(buckets, level, node);
}

// Keep ABC's reverse-level worklist and every update in the same order.
// High-fanout drivers otherwise rescan all sinks each time one sink is visited,
// making an unmapped shared signal's update quadratic in its fanout count.
// Within one replacement the graph is fixed. Cache each driver's sink maximum
// and its multiplicity, and maintain them whenever a sink's level changes.
struct Tg_ReverseMaximum
{
    int maximum = 0, count = 0;
    unsigned stamp = 0;
};
static std::vector<Tg_ReverseMaximum> s_ReverseMaximum;
static unsigned s_ReverseGeneration = 0;

static void Tg_UpdateReverseLevels(Vec_Vec_t *Buckets, Abc_Ntk_t *Network)
{
    TG_PROFILE_SCOPE(ReverseLevels);
    int ObjectMax = Abc_NtkObjNumMax(Network);
    // ABC's accessor grows this same array on demand. Grow it once here: the
    // updater creates no objects and cannot invalidate the array pointer.
    Vec_IntFillExtra(Network->vLevelsR, ObjectMax, 0);
    int *Levels = Vec_IntArray(Network->vLevelsR);
    if (static_cast<int>(s_ReverseMaximum.size()) < ObjectMax)
        s_ReverseMaximum.resize(ObjectMax);
    if (++s_ReverseGeneration == 0)
    {
        for (auto &Entry : s_ReverseMaximum)
            Entry.stamp = 0;
        s_ReverseGeneration = 1;
    }
#ifdef ABC_TG_ENABLE_AUDIT
    bool Audit = ((char *)0) != nullptr;
    unsigned long long Queries = 0;
#endif
    auto Maximum = [&](Abc_Obj_t *Driver)
    {
        auto &Entry = s_ReverseMaximum[Driver->Id];
        bool Cache = Abc_ObjFanoutNum(Driver) >= 8;
        TG_PROFILE_COUNT(ReverseQueries, 1);
        TG_PROFILE_COUNT(ReverseNaivePins, Abc_ObjFanoutNum(Driver));
        if (!Cache || Entry.stamp != s_ReverseGeneration)
        {
            TG_PROFILE_COUNT(ReverseScannedPins, Abc_ObjFanoutNum(Driver));
            Entry.maximum = Entry.count = 0;
            Abc_Obj_t *Sink;
            int j;
            Abc_ObjForEachFanout(Driver, Sink, j)
            {
                int Level = Levels[Sink->Id];
                if (Level > Entry.maximum)
                {
                    Entry.maximum = Level;
                    Entry.count = 1;
                }
                else if (Level == Entry.maximum)
                    ++Entry.count;
            }
            Entry.stamp = Cache ? s_ReverseGeneration : 0;
        }
#ifdef ABC_TG_ENABLE_AUDIT
        if (Audit)
        {
            int Reference = 0;
            Abc_Obj_t *Sink;
            int j;
            Abc_ObjForEachFanout(Driver, Sink, j) Reference =
                std::max(Reference, Abc_ObjReverseLevel(Sink));
            if (Entry.maximum != Reference)
            {
                Abc_Print(-1, "PA reverse maximum mismatch at %d: %d != %d.\n", Driver->Id,
                          Entry.maximum, Reference);
                std::abort();
            }
            ++Queries;
        }
#endif
        return Entry.maximum;
    };
    Abc_Obj_t *Node, *Input;
    Vec_Ptr_t *Bucket;
    int i, k, v;
    for (i = s_ReverseBuckets.first; i <= s_ReverseBuckets.last; ++i)
    {
        Bucket = Vec_VecEntry(Buckets, i);
        Vec_PtrForEachEntry(Abc_Obj_t *, Bucket, Node, k)
        {
            if (Node == nullptr)
                continue;
            assert(Abc_ObjIsNode(Node) && Levels[Node->Id] == i && Node->fMarkB);
            Node->fMarkB = 0;
            Abc_ObjForEachFanin(Node, Input, v)
            {
                if (Abc_ObjIsCi(Input) || Abc_AigNodeIsConst(Input))
                    continue;
                int NewLevel = Maximum(Input) + 1;
                int OldLevel = Levels[Input->Id];
                assert(NewLevel > i);
                if (OldLevel == NewLevel)
                    continue;
                if (Input->fMarkB)
                {
                    Vec_Ptr_t *OldBucket = Vec_VecEntry(Buckets, OldLevel);
                    int Index = Vec_PtrFind(OldBucket, Input);
                    assert(Index >= 0);
                    Vec_PtrWriteEntry(OldBucket, Index, nullptr);
                    Input->fMarkB = 0;
                }
                Levels[Input->Id] = NewLevel;
                // Only these drivers' cached maxima can depend on this value.
                Abc_Obj_t *Driver;
                int j;
                Abc_ObjForEachFanin(Input, Driver, j)
                {
                    auto &Entry = s_ReverseMaximum[Driver->Id];
                    if (Entry.stamp != s_ReverseGeneration)
                        continue;
                    if (OldLevel == Entry.maximum)
                        --Entry.count;
                    if (NewLevel > Entry.maximum)
                    {
                        Entry.maximum = NewLevel;
                        Entry.count = 1;
                    }
                    else if (NewLevel == Entry.maximum)
                        ++Entry.count;
                    if (Entry.count == 0)
                        Entry.stamp = 0;
                }
                Input->fMarkB = 1;
                Tg_QueueLevel(Buckets, NewLevel, Input, s_ReverseBuckets);
            }
        }
        Vec_PtrClear(Bucket);
    }
    s_ReverseBuckets = Tg_LevelRange{};
#ifdef ABC_TG_ENABLE_AUDIT
    if (Audit && Queries)
        TG_VERBOSE("PA reverse maximum audit: %llu queries, no mismatches.\n", Queries);
#endif
}

static unsigned Tg_HashKey2(Abc_Obj_t *p0, Abc_Obj_t *p1, int TableSize)
{
    unsigned Key = 0;
    Key ^= (unsigned)Abc_ObjRegular(p0)->Id * 7937;
    Key ^= (unsigned)Abc_ObjRegular(p1)->Id * 2971;
    Key ^= (unsigned)Abc_ObjIsComplement(p0) * 911;
    Key ^= (unsigned)Abc_ObjIsComplement(p1) * 353;
    return Key % TableSize;
}

static Abc_Obj_t *Tg_AigAndCreateFrom(Abc_Aig_t *pMan, Abc_Obj_t *p0, Abc_Obj_t *p1,
                                      Abc_Obj_t *pAnd)
{
    Abc_Obj_t *pTemp;
    unsigned Key;
    assert(!Abc_ObjIsComplement(pAnd));
    // order the arguments
    if (Abc_ObjRegular(p0)->Id > Abc_ObjRegular(p1)->Id)
        pTemp = p0, p0 = p1, p1 = pTemp;
    // create the new node
    Abc_ObjAddFanin(pAnd, p0);
    Abc_ObjAddFanin(pAnd, p1);
    // set the level of the new node
    pAnd->Level = 1 + Abc_MaxInt(Abc_ObjRegular(p0)->Level, Abc_ObjRegular(p1)->Level);
    pAnd->fExor = Abc_NodeIsExorType(pAnd);
    // add the node to the corresponding linked list in the table
    Key = Tg_HashKey2(p0, p1, pMan->nBins);
    pAnd->pNext = pMan->pBins[Key];
    pMan->pBins[Key] = pAnd;
    pMan->nEntries++;
    // create the cuts if defined
    //    if ( pAnd->pNtk->pManCut )
    //        Abc_NodeGetCuts( pAnd->pNtk->pManCut, pAnd );
    pAnd->pCopy = NULL;
    // add the node to the list of updated nodes
    //    if ( pMan->vAddedCells )
    //        Vec_PtrPush( pMan->vAddedCells, pAnd );
    return pAnd;
}

static void Tg_AigAndDelete(Abc_Aig_t *pMan, Abc_Obj_t *pThis)
{
    Abc_Obj_t *pAnd, *pAnd0, *pAnd1, **ppPlace;
    unsigned Key;
    assert(!Abc_ObjIsComplement(pThis));
    assert(Abc_ObjIsNode(pThis));
    assert(Abc_ObjFaninNum(pThis) == 2);
    assert(pMan->pNtkAig == pThis->pNtk);
    // get the hash key for these two nodes
    pAnd0 = Abc_ObjRegular(Abc_ObjChild0(pThis));
    pAnd1 = Abc_ObjRegular(Abc_ObjChild1(pThis));
    Key = Tg_HashKey2(Abc_ObjChild0(pThis), Abc_ObjChild1(pThis), pMan->nBins);
    // find the matching node in the table
    ppPlace = pMan->pBins + Key;
    Abc_AigBinForEachEntry(pMan->pBins[Key], pAnd)
    {
        if (pAnd != pThis)
        {
            ppPlace = &pAnd->pNext;
            continue;
        }
        *ppPlace = pAnd->pNext;
        break;
    }
    assert(pAnd == pThis);
    pMan->nEntries--;
    // delete the cuts if defined
    if (pThis->pNtk->pManCut)
        Abc_NodeFreeCuts(pThis->pNtk->pManCut, pThis);
}

static void Tg_AigRemoveFromLevelStructure(Vec_Vec_t *vStruct, Abc_Obj_t *pNode)
{
    Vec_Ptr_t *vVecTemp;
    Abc_Obj_t *pTemp;
    int m;
    assert(pNode->fMarkA);
    vVecTemp = Vec_VecEntry(vStruct, pNode->Level);
    Vec_PtrForEachEntry(Abc_Obj_t *, vVecTemp, pTemp, m)
    {
        if (pTemp != pNode)
            continue;
        Vec_PtrWriteEntry(vVecTemp, m, NULL);
        break;
    }
    assert(m < Vec_PtrSize(vVecTemp)); // found
    pNode->fMarkA = 0;
}

static void Tg_AigRemoveFromLevelStructureR(Vec_Vec_t *vStruct, Abc_Obj_t *pNode)
{
    Vec_Ptr_t *vVecTemp;
    Abc_Obj_t *pTemp;
    int m;
    assert(pNode->fMarkB);
    vVecTemp = Vec_VecEntry(vStruct, Abc_ObjReverseLevel(pNode));
    Vec_PtrForEachEntry(Abc_Obj_t *, vVecTemp, pTemp, m)
    {
        if (pTemp != pNode)
            continue;
        Vec_PtrWriteEntry(vVecTemp, m, NULL);
        break;
    }
    assert(m < Vec_PtrSize(vVecTemp)); // found
    pNode->fMarkB = 0;
}

static void Tg_AigReplace_int(Abc_Aig_t *pMan, Abc_Obj_t *pOld, Abc_Obj_t *pNew, int fUpdateLevel)
{
    Abc_Obj_t *pFanin1, *pFanin2, *pFanout, *pFanoutNew, *pFanoutFanout;
    int k, v, iFanin;
    // make sure the old node is regular and has fanouts
    // (the new node can be complemented and can have fanouts)
    assert(!Abc_ObjIsComplement(pOld));
    assert(Abc_ObjFanoutNum(pOld) > 0);
    // look at the fanouts of old node
    Abc_NodeCollectFanouts(pOld, pMan->vNodes);
    Vec_PtrForEachEntry(Abc_Obj_t *, pMan->vNodes, pFanout, k)
    {
        if (Abc_ObjIsCo(pFanout))
        {
            pFanin1 = Abc_ObjRegular(pNew);
            if (pFanin1->fMarkB)
                Tg_AigRemoveFromLevelStructureR(pMan->vLevelsR, pFanin1);
            if (fUpdateLevel && pMan->pNtkAig->vLevelsR)
            {
                // A reused signal may already feed a longer path to another
                // output. Adding this CO must not relax that existing bound.
                Abc_ObjSetReverseLevel(
                    pFanin1, std::max(Abc_ObjReverseLevel(pFanin1), Abc_ObjReverseLevel(pOld)));
                assert(pFanin1->fMarkB == 0);
                if (!Abc_ObjIsCi(pFanin1) && !Abc_AigNodeIsConst(pFanin1))
                {
                    pFanin1->fMarkB = 1;
                    Tg_QueueLevel(pMan->vLevelsR, Abc_ObjReverseLevel(pFanin1), pFanin1,
                                  s_ReverseBuckets);
                }
            }
            Abc_ObjPatchFanin(pFanout, pOld, pNew);
            continue;
        }
        // find the old node as a fanin of this fanout
        iFanin = Vec_IntFind(&pFanout->vFanins, pOld->Id);
        assert(iFanin == 0 || iFanin == 1);
        // get the new fanin
        pFanin1 = Abc_ObjNotCond(pNew, Abc_ObjFaninC(pFanout, iFanin));
        assert(Abc_ObjRegular(pFanin1) != pFanout);
        // get another fanin
        pFanin2 = Abc_ObjChild(pFanout, iFanin ^ 1);
        assert(Abc_ObjRegular(pFanin2) != pFanout);
        // check if the node with these fanins exists
        if ((pFanoutNew = Abc_AigAndLookup(pMan, pFanin1, pFanin2)))
        { // such node exists (it may be a constant)
            // schedule replacement of the old fanout by the new fanout
            Vec_PtrPush(pMan->vStackReplaceOld, pFanout);
            Vec_PtrPush(pMan->vStackReplaceNew, pFanoutNew);
            continue;
        }
        // such node does not exist - modify the old fanout node
        // (this way the change will not propagate all the way to the COs)
        assert(Abc_ObjRegular(pFanin1) != Abc_ObjRegular(pFanin2));

        // if the node is in the level structure, remove it
        if (pFanout->fMarkA)
            Tg_AigRemoveFromLevelStructure(pMan->vLevels, pFanout);
        // if the node is in the level structure, remove it
        if (pFanout->fMarkB)
            Tg_AigRemoveFromLevelStructureR(pMan->vLevelsR, pFanout);

        // remove the old fanout node from the structural hashing table
        Tg_AigAndDelete(pMan, pFanout);
        // remove the fanins of the old fanout
        Abc_ObjRemoveFanins(pFanout);
        // recreate the old fanout with new fanins and add it to the table
        Tg_AigAndCreateFrom(pMan, pFanin1, pFanin2, pFanout);
        assert(Abc_AigNodeIsAcyclic(pFanout, pFanout));

        if (fUpdateLevel)
        {
            // schedule the updated fanout for updating direct level
            assert(pFanout->fMarkA == 0);
            pFanout->fMarkA = 1;
            Tg_QueueLevel(pMan->vLevels, pFanout->Level, pFanout, s_ForwardBuckets);
            // schedule the updated fanout for updating reverse level
            if (pMan->pNtkAig->vLevelsR)
            {
                assert(pFanout->fMarkB == 0);
                pFanout->fMarkB = 1;
                Tg_QueueLevel(pMan->vLevelsR, Abc_ObjReverseLevel(pFanout), pFanout,
                              s_ReverseBuckets);
            }
        }

        // the fanout has changed, update EXOR status of its fanouts
        Abc_ObjForEachFanout(pFanout, pFanoutFanout, v) if (Abc_AigNodeIsAnd(pFanoutFanout))
            pFanoutFanout->fExor = Abc_NodeIsExorType(pFanoutFanout);
    }
    // if the node has no fanouts left, remove its MFFC
    if (Abc_ObjFanoutNum(pOld) == 0)
        Abc_AigDeleteNode(pMan, pOld);
}

static void Tg_AigUpdateLevel_int(Abc_Aig_t *pMan)
{
    Abc_Obj_t *pNode, *pFanout;
    Vec_Ptr_t *vVec;
    int LevelNew, i, k, v;

    // go through the nodes and update the level of their fanouts
    for (i = s_ForwardBuckets.first; i <= s_ForwardBuckets.last; ++i)
    {
        vVec = Vec_VecEntry(pMan->vLevels, i);
        if (Vec_PtrSize(vVec) == 0)
            continue;
        Vec_PtrForEachEntry(Abc_Obj_t *, vVec, pNode, k)
        {
            if (pNode == NULL)
                continue;
            assert(Abc_ObjIsNode(pNode));
            assert((int)pNode->Level == i);
            // clean the mark
            assert(pNode->fMarkA == 1);
            pNode->fMarkA = 0;
            // iterate through the fanouts
            Abc_ObjForEachFanout(pNode, pFanout, v)
            {
                if (Abc_ObjIsCo(pFanout))
                    continue;
                // get the new level of this fanout
                LevelNew =
                    1 + Abc_MaxInt(Abc_ObjFanin0(pFanout)->Level, Abc_ObjFanin1(pFanout)->Level);
                assert(LevelNew > i);
                if ((int)pFanout->Level == LevelNew) // no change
                    continue;
                // if the fanout is present in the data structure, pull it out
                if (pFanout->fMarkA)
                    Tg_AigRemoveFromLevelStructure(pMan->vLevels, pFanout);
                // update the fanout level
                pFanout->Level = LevelNew;
                // add the fanout to the data structure to update its fanouts
                assert(pFanout->fMarkA == 0);
                pFanout->fMarkA = 1;
                Tg_QueueLevel(pMan->vLevels, pFanout->Level, pFanout, s_ForwardBuckets);
            }
        }
        Vec_PtrClear(vVec);
    }
    s_ForwardBuckets = Tg_LevelRange{};
}

// Diagnostic-only independent topological level audit. It is never part of
// production selection, acceptance, or rollback.
static void Tg_AuditLevels(Abc_Ntk_t *n)
{
    return;
}

int Tg_AigReplace(Abc_Aig_t *pMan, Abc_Obj_t *pOld, Abc_Obj_t *pNew, int fUpdateLevel)
{
    TG_PROFILE_SCOPE(Replace);
#ifdef ABC_TG_DISABLE_REVERSE_CACHE
    return Abc_AigReplace(pMan, pOld, pNew, fUpdateLevel);
#else
    assert(s_ForwardBuckets.last < 0 && s_ReverseBuckets.last < 0);
    assert(Vec_PtrSize(pMan->vStackReplaceOld) == 0);
    assert(Vec_PtrSize(pMan->vStackReplaceNew) == 0);
    Vec_PtrPush(pMan->vStackReplaceOld, pOld);
    Vec_PtrPush(pMan->vStackReplaceNew, pNew);
    assert(!Abc_ObjIsComplement(pOld));
    // process the replacements
    while (Vec_PtrSize(pMan->vStackReplaceOld))
    {
        pOld = (Abc_Obj_t *)Vec_PtrPop(pMan->vStackReplaceOld);
        pNew = (Abc_Obj_t *)Vec_PtrPop(pMan->vStackReplaceNew);
        if (Abc_ObjFanoutNum(pOld) == 0)
            // return 0;
            continue;
        Tg_AigReplace_int(pMan, pOld, pNew, fUpdateLevel);
    }
    if (fUpdateLevel)
    {
        Tg_AigUpdateLevel_int(pMan);
        if (pMan->pNtkAig->vLevelsR)
            Tg_UpdateReverseLevels(pMan->vLevelsR, pMan->pNtkAig);
    }
    Tg_AuditLevels(pMan->pNtkAig);
    return 1;
#endif
}

ABC_NAMESPACE_IMPL_END
