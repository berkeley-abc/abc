/**CFile****************************************************************

  FileName    [paAig.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [AIG node replacement with level updates.]

  Author      [Anqi Lu, from abcAig.c by Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paAig.cpp,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"

#include <algorithm>
#include <climits>
#include <vector>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Abc_Aig_t is private to abcAig.c; this definition must match it.
struct Abc_Aig_t_
{
    Abc_Ntk_t * pNtkAig;          // the AIG network
    Abc_Obj_t * pConst1;          // the constant 1 object (not a node!)
    Abc_Obj_t ** pBins;           // the table bins
    int nBins;                    // the size of the table
    int nEntries;                 // the total number of entries in the table
    Vec_Ptr_t * vNodes;           // the temporary array of nodes
    Vec_Ptr_t * vStackReplaceOld; // the nodes to be replaced
    Vec_Ptr_t * vStackReplaceNew; // the nodes to be used for replacement
    Vec_Vec_t * vLevels;          // the nodes to be updated
    Vec_Vec_t * vLevelsR;         // the nodes to be updated
    Vec_Ptr_t * vAddedCells;      // the added nodes
    Vec_Ptr_t * vUpdatedNets;     // the nodes whose fanouts have changed

    int nStrash0;
    int nStrash1;
    int nStrash5;
    int nStrash2;
};

#define Pa_AigBinForEachEntry(pBin, pEnt) for ( pEnt = pBin; pEnt; pEnt = pEnt->pNext )

static unsigned Pa_HashKey2(Abc_Obj_t * p0, Abc_Obj_t * p1, int TableSize);
static Abc_Obj_t * Pa_AigAndCreateFrom(Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1, Abc_Obj_t * pAnd);
static void Pa_AigAndDelete(Abc_Aig_t * pMan, Abc_Obj_t * pThis);
static void Pa_AigRemoveFromLevelStructure(Vec_Vec_t * vStruct, Abc_Obj_t * pNode);
static void Pa_AigRemoveFromLevelStructureR(Vec_Vec_t * vStruct, Abc_Obj_t * pNode);
static void Pa_AigReplace_int(Abc_Aig_t * pMan, Abc_Obj_t * pOld, Abc_Obj_t * pNew, int fUpdateLevel);
static void Pa_AigUpdateLevel_int(Abc_Aig_t * pMan);

// Level worklists are visited in ascending order over the populated range only.
struct Pa_LevelRange
{
    int first = INT_MAX, last = -1;
};
// Per-call scratch of one replacement.
static thread_local Pa_LevelRange s_ForwardBuckets, s_ReverseBuckets;
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds a node to a level worklist and extends its populated range.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_QueueLevel(Vec_Vec_t * buckets, int level, Abc_Obj_t * node, Pa_LevelRange & range)
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
struct Pa_ReverseMaximum
{
    int maximum = 0, count = 0;
    unsigned stamp = 0;
};
static thread_local std::vector<Pa_ReverseMaximum> s_ReverseMaximum;
static thread_local unsigned s_ReverseGeneration = 0;

/**Function*************************************************************

  Synopsis    [Updates the reverse levels after a replacement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_UpdateReverseLevels(Vec_Vec_t * Buckets, Abc_Ntk_t * Network)
{
    int ObjectMax = Abc_NtkObjNumMax(Network);
    // ABC's accessor grows this same array on demand. Grow it once here: the
    // updater creates no objects and cannot invalidate the array pointer.
    Vec_IntFillExtra(Network->vLevelsR, ObjectMax, 0);
    int * Levels = Vec_IntArray(Network->vLevelsR);
    if ( static_cast<int>(s_ReverseMaximum.size()) < ObjectMax )
        s_ReverseMaximum.resize(ObjectMax);
    if ( ++s_ReverseGeneration == 0 )
    {
        for ( auto & Entry : s_ReverseMaximum )
            Entry.stamp = 0;
        s_ReverseGeneration = 1;
    }
    auto Maximum = [&](Abc_Obj_t * Driver)
    {
        auto & Entry = s_ReverseMaximum[Driver->Id];
        bool Cache = Abc_ObjFanoutNum(Driver) >= 8;
        if ( !Cache || Entry.stamp != s_ReverseGeneration )
        {
            Entry.maximum = Entry.count = 0;
            Abc_Obj_t * Sink;
            int j;
            Abc_ObjForEachFanout(Driver, Sink, j)
            {
                int Level = Levels[Sink->Id];
                if ( Level > Entry.maximum )
                {
                    Entry.maximum = Level;
                    Entry.count = 1;
                }
                else if ( Level == Entry.maximum )
                    ++Entry.count;
            }
            Entry.stamp = Cache ? s_ReverseGeneration : 0;
        }
        return Entry.maximum;
    };
    Abc_Obj_t *Node, *Input;
    Vec_Ptr_t * Bucket;
    int i, k, v;
    for ( i = s_ReverseBuckets.first; i <= s_ReverseBuckets.last; ++i )
    {
        Bucket = Vec_VecEntry(Buckets, i);
        Vec_PtrForEachEntry(Abc_Obj_t *, Bucket, Node, k)
        {
            if ( Node == nullptr )
                continue;
            assert(Abc_ObjIsNode(Node) && Levels[Node->Id] == i && Node->fMarkB);
            Node->fMarkB = 0;
            Abc_ObjForEachFanin(Node, Input, v)
            {
                if ( Abc_ObjIsCi(Input) || Abc_AigNodeIsConst(Input) )
                    continue;
                int NewLevel = Maximum(Input) + 1;
                int OldLevel = Levels[Input->Id];
                assert(NewLevel > i);
                if ( OldLevel == NewLevel )
                    continue;
                if ( Input->fMarkB )
                {
                    Vec_Ptr_t * OldBucket = Vec_VecEntry(Buckets, OldLevel);
                    int Index = Vec_PtrFind(OldBucket, Input);
                    assert(Index >= 0);
                    Vec_PtrWriteEntry(OldBucket, Index, nullptr);
                    Input->fMarkB = 0;
                }
                Levels[Input->Id] = NewLevel;
                // Only these drivers' cached maxima can depend on this value.
                Abc_Obj_t * Driver;
                int j;
                Abc_ObjForEachFanin(Input, Driver, j)
                {
                    auto & Entry = s_ReverseMaximum[Driver->Id];
                    if ( Entry.stamp != s_ReverseGeneration )
                        continue;
                    if ( OldLevel == Entry.maximum )
                        --Entry.count;
                    if ( NewLevel > Entry.maximum )
                    {
                        Entry.maximum = NewLevel;
                        Entry.count = 1;
                    }
                    else if ( NewLevel == Entry.maximum )
                        ++Entry.count;
                    if ( Entry.count == 0 )
                        Entry.stamp = 0;
                }
                Input->fMarkB = 1;
                Pa_QueueLevel(Buckets, NewLevel, Input, s_ReverseBuckets);
            }
        }
        Vec_PtrClear(Bucket);
    }
    s_ReverseBuckets = Pa_LevelRange{};
}

/**Function*************************************************************

  Synopsis    [Returns the hash key of a pair of AND fanins.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Pa_HashKey2(Abc_Obj_t * p0, Abc_Obj_t * p1, int TableSize)
{
    unsigned Key = 0;
    Key ^= (unsigned)Abc_ObjRegular(p0)->Id * 7937;
    Key ^= (unsigned)Abc_ObjRegular(p1)->Id * 2971;
    Key ^= (unsigned)Abc_ObjIsComplement(p0) * 911;
    Key ^= (unsigned)Abc_ObjIsComplement(p1) * 353;
    return Key % TableSize;
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Obj_t * Pa_AigAndCreateFrom(Abc_Aig_t * pMan, Abc_Obj_t * p0, Abc_Obj_t * p1, Abc_Obj_t * pAnd)
{
    Abc_Obj_t * pTemp;
    unsigned Key;
    assert(!Abc_ObjIsComplement(pAnd));
    // order the arguments
    if ( Abc_ObjRegular(p0)->Id > Abc_ObjRegular(p1)->Id )
        pTemp = p0, p0 = p1, p1 = pTemp;
    // create the new node
    Abc_ObjAddFanin(pAnd, p0);
    Abc_ObjAddFanin(pAnd, p1);
    // set the level of the new node
    pAnd->Level = 1 + Abc_MaxInt(Abc_ObjRegular(p0)->Level, Abc_ObjRegular(p1)->Level);
    pAnd->fExor = Abc_NodeIsExorType(pAnd);
    // add the node to the corresponding linked list in the table
    Key = Pa_HashKey2(p0, p1, pMan->nBins);
    pAnd->pNext = pMan->pBins[Key];
    pMan->pBins[Key] = pAnd;
    pMan->nEntries++;
    // create the cuts if defined
    pAnd->pCopy = NULL;
    // add the node to the list of updated nodes
    return pAnd;
}

/**Function*************************************************************

  Synopsis    [Deletes an AIG node from the hash table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_AigAndDelete(Abc_Aig_t * pMan, Abc_Obj_t * pThis)
{
    Abc_Obj_t *pAnd, **ppPlace;
    unsigned Key;
    assert(!Abc_ObjIsComplement(pThis));
    assert(Abc_ObjIsNode(pThis));
    assert(Abc_ObjFaninNum(pThis) == 2);
    assert(pMan->pNtkAig == pThis->pNtk);
    // get the hash key for these two nodes
    Key = Pa_HashKey2(Abc_ObjChild0(pThis), Abc_ObjChild1(pThis), pMan->nBins);
    // find the matching node in the table
    ppPlace = pMan->pBins + Key;
    Pa_AigBinForEachEntry(pMan->pBins[Key], pAnd)
    {
        if ( pAnd != pThis )
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
    if ( pThis->pNtk->pManCut )
        Abc_NodeFreeCuts(pThis->pNtk->pManCut, pThis);
}

/**Function*************************************************************

  Synopsis    [Removes the node from the level structure.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_AigRemoveFromLevelStructure(Vec_Vec_t * vStruct, Abc_Obj_t * pNode)
{
    Vec_Ptr_t * vVecTemp;
    Abc_Obj_t * pTemp;
    int m;
    assert(pNode->fMarkA);
    vVecTemp = Vec_VecEntry(vStruct, pNode->Level);
    Vec_PtrForEachEntry(Abc_Obj_t *, vVecTemp, pTemp, m)
    {
        if ( pTemp != pNode )
            continue;
        Vec_PtrWriteEntry(vVecTemp, m, NULL);
        break;
    }
    assert(m < Vec_PtrSize(vVecTemp)); // found
    pNode->fMarkA = 0;
}

/**Function*************************************************************

  Synopsis    [Removes the node from the reverse level structure.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_AigRemoveFromLevelStructureR(Vec_Vec_t * vStruct, Abc_Obj_t * pNode)
{
    Vec_Ptr_t * vVecTemp;
    Abc_Obj_t * pTemp;
    int m;
    assert(pNode->fMarkB);
    vVecTemp = Vec_VecEntry(vStruct, Abc_ObjReverseLevel(pNode));
    Vec_PtrForEachEntry(Abc_Obj_t *, vVecTemp, pTemp, m)
    {
        if ( pTemp != pNode )
            continue;
        Vec_PtrWriteEntry(vVecTemp, m, NULL);
        break;
    }
    assert(m < Vec_PtrSize(vVecTemp)); // found
    pNode->fMarkB = 0;
}

/**Function*************************************************************

  Synopsis    [Performs internal replacement step.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_AigReplace_int(Abc_Aig_t * pMan, Abc_Obj_t * pOld, Abc_Obj_t * pNew, int fUpdateLevel)
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
        if ( Abc_ObjIsCo(pFanout) )
        {
            pFanin1 = Abc_ObjRegular(pNew);
            if ( pFanin1->fMarkB )
                Pa_AigRemoveFromLevelStructureR(pMan->vLevelsR, pFanin1);
            if ( fUpdateLevel && pMan->pNtkAig->vLevelsR )
            {
                // A reused signal may already feed a longer path to another
                // output. Adding this CO must not relax that existing bound.
                Abc_ObjSetReverseLevel(pFanin1, std::max(Abc_ObjReverseLevel(pFanin1), Abc_ObjReverseLevel(pOld)));
                assert(pFanin1->fMarkB == 0);
                if ( !Abc_ObjIsCi(pFanin1) && !Abc_AigNodeIsConst(pFanin1) )
                {
                    pFanin1->fMarkB = 1;
                    Pa_QueueLevel(pMan->vLevelsR, Abc_ObjReverseLevel(pFanin1), pFanin1, s_ReverseBuckets);
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
        if ( (pFanoutNew = Abc_AigAndLookup(pMan, pFanin1, pFanin2)) )
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
        if ( pFanout->fMarkA )
            Pa_AigRemoveFromLevelStructure(pMan->vLevels, pFanout);
        // if the node is in the level structure, remove it
        if ( pFanout->fMarkB )
            Pa_AigRemoveFromLevelStructureR(pMan->vLevelsR, pFanout);

        // remove the old fanout node from the structural hashing table
        Pa_AigAndDelete(pMan, pFanout);
        // remove the fanins of the old fanout
        Abc_ObjRemoveFanins(pFanout);
        // recreate the old fanout with new fanins and add it to the table
        Pa_AigAndCreateFrom(pMan, pFanin1, pFanin2, pFanout);
        assert(Abc_AigNodeIsAcyclic(pFanout, pFanout));

        if ( fUpdateLevel )
        {
            // schedule the updated fanout for updating direct level
            assert(pFanout->fMarkA == 0);
            pFanout->fMarkA = 1;
            Pa_QueueLevel(pMan->vLevels, pFanout->Level, pFanout, s_ForwardBuckets);
            // schedule the updated fanout for updating reverse level
            if ( pMan->pNtkAig->vLevelsR )
            {
                assert(pFanout->fMarkB == 0);
                pFanout->fMarkB = 1;
                Pa_QueueLevel(pMan->vLevelsR, Abc_ObjReverseLevel(pFanout), pFanout, s_ReverseBuckets);
            }
        }

        // the fanout has changed, update EXOR status of its fanouts
        Abc_ObjForEachFanout(pFanout, pFanoutFanout, v) if ( Abc_AigNodeIsAnd(pFanoutFanout) ) pFanoutFanout->fExor =
            Abc_NodeIsExorType(pFanoutFanout);
    }
    // if the node has no fanouts left, remove its MFFC
    if ( Abc_ObjFanoutNum(pOld) == 0 )
        Abc_AigDeleteNode(pMan, pOld);
}

/**Function*************************************************************

  Synopsis    [Updates the level of the node after it has changed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pa_AigUpdateLevel_int(Abc_Aig_t * pMan)
{
    Abc_Obj_t *pNode, *pFanout;
    Vec_Ptr_t * vVec;
    int LevelNew, i, k, v;

    // go through the nodes and update the level of their fanouts
    for ( i = s_ForwardBuckets.first; i <= s_ForwardBuckets.last; ++i )
    {
        vVec = Vec_VecEntry(pMan->vLevels, i);
        if ( Vec_PtrSize(vVec) == 0 )
            continue;
        Vec_PtrForEachEntry(Abc_Obj_t *, vVec, pNode, k)
        {
            if ( pNode == NULL )
                continue;
            assert(Abc_ObjIsNode(pNode));
            assert((int)pNode->Level == i);
            // clean the mark
            assert(pNode->fMarkA == 1);
            pNode->fMarkA = 0;
            // iterate through the fanouts
            Abc_ObjForEachFanout(pNode, pFanout, v)
            {
                if ( Abc_ObjIsCo(pFanout) )
                    continue;
                // get the new level of this fanout
                LevelNew = 1 + Abc_MaxInt(Abc_ObjFanin0(pFanout)->Level, Abc_ObjFanin1(pFanout)->Level);
                assert(LevelNew > i);
                if ( (int)pFanout->Level == LevelNew ) // no change
                    continue;
                // if the fanout is present in the data structure, pull it out
                if ( pFanout->fMarkA )
                    Pa_AigRemoveFromLevelStructure(pMan->vLevels, pFanout);
                // update the fanout level
                pFanout->Level = LevelNew;
                // add the fanout to the data structure to update its fanouts
                assert(pFanout->fMarkA == 0);
                pFanout->fMarkA = 1;
                Pa_QueueLevel(pMan->vLevels, pFanout->Level, pFanout, s_ForwardBuckets);
            }
        }
        Vec_PtrClear(vVec);
    }
    s_ForwardBuckets = Pa_LevelRange{};
}

/**Function*************************************************************

  Synopsis    [Replaces one AIG node by the other.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_AigReplace(Abc_Aig_t * pMan, Abc_Obj_t * pOld, Abc_Obj_t * pNew, int fUpdateLevel)
{
    assert(s_ForwardBuckets.last < 0 && s_ReverseBuckets.last < 0);
    assert(Vec_PtrSize(pMan->vStackReplaceOld) == 0);
    assert(Vec_PtrSize(pMan->vStackReplaceNew) == 0);
    Vec_PtrPush(pMan->vStackReplaceOld, pOld);
    Vec_PtrPush(pMan->vStackReplaceNew, pNew);
    assert(!Abc_ObjIsComplement(pOld));
    // process the replacements
    while ( Vec_PtrSize(pMan->vStackReplaceOld) )
    {
        pOld = (Abc_Obj_t *)Vec_PtrPop(pMan->vStackReplaceOld);
        pNew = (Abc_Obj_t *)Vec_PtrPop(pMan->vStackReplaceNew);
        if ( Abc_ObjFanoutNum(pOld) == 0 )
            // return 0;
            continue;
        Pa_AigReplace_int(pMan, pOld, pNew, fUpdateLevel);
    }
    if ( fUpdateLevel )
    {
        Pa_AigUpdateLevel_int(pMan);
        if ( pMan->pNtkAig->vLevelsR )
            Pa_UpdateReverseLevels(pMan->vLevelsR, pMan->pNtkAig);
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
