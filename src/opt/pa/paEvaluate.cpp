/**CFile****************************************************************

  FileName    [paEvaluate.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Physical evaluation of candidate AIG replacements.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paEvaluate.cpp,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "paInt.h"
#include "paMath.h"
#include "paWorkspace.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

namespace
{

// The settings and caches of the evaluator belong to the current frame
// (Pa_EvalState); every exported function binds them to these pointers.
struct Pa_EvalSettings
{
    bool physicalAreaGuard = false;
    bool clusterEvaluation = false;
    bool capacityRepair = false;
    bool wireTolerance = false;
    bool timingEvaluation = false;
    bool exactTiming = false;
};
static ABC_THREAD_LOCAL Pa_EvalSettings * s_pSettings = nullptr;

constexpr double kTimingWeight = 0.5;
// With wire tolerance, relative wire-arrival changes below this do not propagate.
constexpr double kWireChangeTolerance = 1.0e-6;
constexpr double kCompareTolerance = 1.0e-10;
constexpr int kRegionDivisions = 5;
constexpr double kMinimumRegionStep = 0.05;

struct Pa_Geometry
{
    double x = 0.0;
    double y = 0.0;
    double width = 0.0;
    double densityHalfX = 0.0;
    double densityHalfY = 0.0;
    double densityScale = 0.0;
};

// Candidate evaluation does not mutate placement. Cache live data by object
// ID until the next commit. No cache entry survives a pass/ID reassignment.
struct Pa_ReadCache
{
    struct Object
    {
        Pa_Geometry geometry;
        double hpwl = 0.0;
        unsigned geometryStamp = 0, hpwlStamp = 0;
        bool hasPoint = false;
    };
    struct Bin
    {
        double base = 0.0, delta = 0.0;
        unsigned baseStamp = 0, deltaStamp = 0;
    };
    std::vector<Object> objects;
    std::vector<Bin> bins;
    unsigned version = 1, candidate = 1;
    void Invalidate()
    {
        if ( ++version == 0 )
        {
            objects.clear();
            bins.clear();
            version = 1;
        }
    }
    void Start(Abc_Ntk_t * Network)
    {
        Invalidate();
        objects.resize(Abc_NtkObjNumMax(Network));
    }
    Object & Get(int Id)
    {
        if ( static_cast<size_t>(Id) >= objects.size() )
            objects.resize(std::max(static_cast<size_t>(Id + 1), objects.size() * 2));
        return objects[Id];
    }
    void BeginCandidate(int Count)
    {
        bins.resize(Count);
        if ( ++candidate == 0 )
        {
            for ( auto & B : bins )
                B.deltaStamp = 0;
            candidate = 1;
        }
    }
};
static ABC_THREAD_LOCAL Pa_ReadCache * s_pReadCache = nullptr;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the geometry of an object through the read cache.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_ReadObjectGeometry(Abc_Ntk_t * Network, Abc_Obj_t * Object, double * X, double * Y, double * Width,
                                 double * HalfX, double * HalfY, double * Scale)
{
    auto & C = s_pReadCache->Get(Object->Id);
    if ( C.geometryStamp != s_pReadCache->version )
    {
        auto & G = C.geometry;
        C.hasPoint = Pa_ManReadObjectGeometry(Network, Object, &G.x, &G.y, &G.width, &G.densityHalfX, &G.densityHalfY,
                                              &G.densityScale) != 0;
        C.geometryStamp = s_pReadCache->version;
    }
    if ( !C.hasPoint )
        return 0;
    const auto & G = C.geometry;
    if ( X )
        *X = G.x;
    if ( Y )
        *Y = G.y;
    if ( Width )
        *Width = G.width;
    if ( HalfX )
        *HalfX = G.densityHalfX;
    if ( HalfY )
        *HalfY = G.densityHalfY;
    if ( Scale )
        *Scale = G.densityScale;
    return 1;
}

struct Pa_Entity
{
    Abc_Obj_t * object = nullptr;
    int decIndex = -1;
    bool virtualNode = false;
    bool movable = false;
    bool hasPoint = false;
    Pa_Geometry geometry;
};

// A distinct position of the removed MFFC (cluster mode).
struct Pa_Cluster
{
    double x = 0.0;
    double y = 0.0;
    int count = 0;
};

struct Pa_SymbolicLit
{
    int entity = -1;
    bool complement = false;
};

struct Pa_LocalNet
{
    PaWorkspace::IntList pins;
    int fixedCount = 0;
    double fixedMinX = 0.0, fixedMaxX = 0.0;
    double fixedMinY = 0.0, fixedMaxY = 0.0;

    void AddFixed(double X, double Y)
    {
        if ( fixedCount++ == 0 )
        {
            fixedMinX = fixedMaxX = X;
            fixedMinY = fixedMaxY = Y;
        }
        else
        {
            fixedMinX = std::min(fixedMinX, X);
            fixedMaxX = std::max(fixedMaxX, X);
            fixedMinY = std::min(fixedMinY, Y);
            fixedMaxY = std::max(fixedMaxY, Y);
        }
    }
};

struct Pa_DirectFanout
{
    int id = -1;
    Abc_Obj_t * object = nullptr;
    Abc_Obj_t * otherFanin = nullptr;
    bool rootComplement = false;
};

struct Pa_Rectangle
{
    double lowX = 0.0;
    double highX = 0.0;
    double lowY = 0.0;
    double highY = 0.0;
    bool valid = false;
};

struct Pa_Arrival
{
    int logic = 0;
    double wire = 0.0;
};

// Candidate timing uses membership and memo lookups, never hash iteration.
// AIG object IDs let us reuse this scratch space without per-object allocation
// or an O(network size) clear for every candidate. Like the placement read
// cache, it belongs to the sequential evaluator; no candidate timing escapes
// its constructor or overlaps another candidate evaluation.
struct Pa_CandidateTimingScratch
{
    struct Object
    {
        Pa_Arrival memo;
        unsigned affected = 0, ancestor = 0, visiting = 0, memoStamp = 0;
    };
    std::vector<Object> objects;
    std::vector<Abc_Obj_t *> moved, backward, queue;
    unsigned generation = 0;
    void Start(int ObjectMax)
    {
        if ( static_cast<int>(objects.size()) < ObjectMax )
            objects.resize(ObjectMax);
        if ( ++generation == 0 )
        {
            std::fill(objects.begin(), objects.end(), Object{});
            generation = 1;
        }
        moved.clear();
        backward.clear();
        queue.clear();
    }
    bool Mark(unsigned & Stamp)
    {
        if ( Stamp == generation )
            return false;
        Stamp = generation;
        return true;
    }
};
static ABC_THREAD_LOCAL Pa_CandidateTimingScratch * s_pCandidateTiming = nullptr;

struct Pa_TimingNode
{
    Pa_Arrival arrival;
    int requiredLogic = ABC_INFINITY;
    double requiredWire = std::numeric_limits<double>::infinity();
    double x = 0.0;
    double y = 0.0;
};

/**Function*************************************************************

  Synopsis    [Returns the change of the slack potential.]

  Description [An unconstrained timing model contributes no score.
               Subtracting two infinite potentials would otherwise turn an
               otherwise valid score into NaN.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Pa_SlackPotentialDelta(double OldSlack, double NewSlack)
{
    if ( OldSlack == std::numeric_limits<double>::infinity() && OldSlack == NewSlack )
        return 0.0;
    if ( !std::isfinite(OldSlack) || !std::isfinite(NewSlack) )
        return std::numeric_limits<double>::quiet_NaN();
    auto Potential = [](double Slack) { return Slack > 0.0 ? std::log1p(Slack) : Slack; };
    return Potential(NewSlack) - Potential(OldSlack);
}

// Kept outside Abc_Obj_t so placement does not change ABC's object layout.
// A pass starts with one global build, then refreshes timing locally.
struct Pa_TimingCache
{
    Abc_Ntk_t * network = nullptr;
    std::vector<Pa_TimingNode> nodes;
    std::vector<int> topoRank;
    int maxLogic = 0;
    double maxWire = 0.0;
    double wireScale = 1.0;
    bool ready = false;
    unsigned updateStamp = 0;
    std::vector<unsigned> positionStamp;
    std::vector<unsigned> arrivalQueueStamp;
    std::vector<unsigned> arrivalAllowedStamp;
    std::vector<unsigned> refreshStamp;
    std::vector<int> workQueue;
    // Intrusive level buckets for unrestricted forward timing propagation.
    // Equal-level nodes have no edges between them; their order is immaterial.
    std::vector<int> arrivalLevelHead;
    std::vector<int> arrivalNext;
    std::vector<int> requiredQueue;
    std::vector<unsigned char> requiredDirty;
    std::vector<int> refreshOrder;
    unsigned refreshGeneration = 0;
    int lastRefreshRootId = -1;

    static double Distance(const Pa_TimingNode & From, const Pa_TimingNode & To)
    {
        return std::hypot(From.x - To.x, From.y - To.y);
    }

    static bool SameWireValue(double Left, double Right)
    {
        if ( std::isinf(Left) || std::isinf(Right) )
            return Left == Right;
        double Epsilon = kCompareTolerance * (1.0 + std::max(std::fabs(Left), std::fabs(Right)));
        return std::fabs(Left - Right) <= Epsilon;
    }

    bool Build(Abc_Ntk_t * pNtk)
    {
        ready = false;
        network = pNtk;
        if ( pNtk == nullptr || (!Pa_ManIsPassActive(pNtk) && !Pa_ManHasPlacement(pNtk)) )
            return false;
        nodes.assign(Abc_NtkObjNumMax(pNtk), Pa_TimingNode{});
        requiredQueue.clear();
        requiredDirty.assign(nodes.size(), 0);
        topoRank.assign(nodes.size(), 0);
        positionStamp.assign(nodes.size(), 0);
        arrivalQueueStamp.assign(nodes.size(), 0);
        arrivalNext.resize(nodes.size());
        arrivalLevelHead.clear();
        arrivalAllowedStamp.assign(nodes.size(), 0);
        refreshStamp.assign(nodes.size(), 0);
        updateStamp = 0;
        refreshGeneration = 0;
        lastRefreshRootId = -1;
        maxLogic = 0;
        maxWire = 0.0;
        Vec_Ptr_t * pOrder = Abc_NtkDfs(pNtk, 1);
        Abc_Obj_t * pObj;
        int i;
        bool Complete = true;
        Vec_PtrForEachEntry(Abc_Obj_t *, pOrder, pObj, i)
        {
            if ( !Abc_ObjIsNode(pObj) )
                continue;
            Pa_TimingNode & Timing = nodes[pObj->Id];
            if ( !Pa_ManReadObjectPosition(pNtk, pObj, &Timing.x, &Timing.y) )
            {
                Complete = false;
                break;
            }
            Abc_Obj_t * pFanin;
            int k;
            Abc_ObjForEachFanin(pObj, pFanin, k)
            {
                const Pa_TimingNode & Input = nodes[pFanin->Id];
                Timing.arrival.logic = std::max(Timing.arrival.logic, Input.arrival.logic + 1);
                double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, Timing);
                Timing.arrival.wire = std::max(Timing.arrival.wire, Input.arrival.wire + Wire);
            }
            // Logic depth is itself a valid topological rank.  Unlike object
            // IDs or a saved DFS index, it remains valid after local AIG
            // replacement creates late-ID nodes feeding older fanouts.
            topoRank[pObj->Id] = Timing.arrival.logic;
        }
        if ( Complete )
        {
            Abc_NtkForEachCo(pNtk, pObj, i)
            {
                const Pa_Arrival & Input = nodes[Abc_ObjFanin0(pObj)->Id].arrival;
                nodes[pObj->Id].arrival = Input;
                topoRank[pObj->Id] = Input.logic;
                maxLogic = std::max(maxLogic, Input.logic);
                maxWire = std::max(maxWire, Input.wire);
            }
            wireScale = maxLogic > 0 && maxWire > 1.0e-8 ? maxWire / maxLogic : 1.0;
            Abc_NtkForEachCo(pNtk, pObj, i)
            {
                Pa_TimingNode & Output = nodes[pObj->Id];
                Output.requiredLogic = maxLogic;
                Output.requiredWire = maxWire;
                Pa_TimingNode & Driver = nodes[Abc_ObjFanin0(pObj)->Id];
                Driver.requiredLogic = std::min(Driver.requiredLogic, maxLogic);
                Driver.requiredWire = std::min(Driver.requiredWire, maxWire);
            }
            Vec_PtrForEachEntryReverse(Abc_Obj_t *, pOrder, pObj, i)
            {
                if ( !Abc_ObjIsNode(pObj) )
                    continue;
                const Pa_TimingNode & Parent = nodes[pObj->Id];
                Abc_Obj_t * pFanin;
                int k;
                Abc_ObjForEachFanin(pObj, pFanin, k)
                {
                    Pa_TimingNode & Input = nodes[pFanin->Id];
                    if ( Parent.requiredLogic != ABC_INFINITY )
                        Input.requiredLogic = std::min(Input.requiredLogic, Parent.requiredLogic - 1);
                    if ( std::isfinite(Parent.requiredWire) )
                    {
                        double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, Parent);
                        Input.requiredWire = std::min(Input.requiredWire, Parent.requiredWire - Wire);
                    }
                }
            }
        }
        Vec_PtrFree(pOrder);
        ready = Complete;
        return ready;
    }

    bool UpdateAfterLocalEdit(Abc_Ntk_t * pNtk, const std::vector<int> & PositionIds,
                              const std::vector<int> & StructuralIds, int ProcessedRootId, bool LevelsCurrent)
    {
        if ( !ready || network != pNtk || pNtk == nullptr )
            return false;
        int ObjectMax = Abc_NtkObjNumMax(pNtk);
        if ( static_cast<int>(nodes.size()) < ObjectMax )
        {
            nodes.resize(ObjectMax);
            topoRank.resize(ObjectMax, 0);
            positionStamp.resize(ObjectMax, 0);
            arrivalQueueStamp.resize(ObjectMax, 0);
            arrivalNext.resize(ObjectMax);
            arrivalAllowedStamp.resize(ObjectMax, 0);
            refreshStamp.resize(ObjectMax, 0);
        }
        if ( ++updateStamp == 0 )
        {
            std::fill(positionStamp.begin(), positionStamp.end(), 0);
            std::fill(arrivalQueueStamp.begin(), arrivalQueueStamp.end(), 0);
            std::fill(arrivalAllowedStamp.begin(), arrivalAllowedStamp.end(), 0);
            updateStamp = 1;
        }
        lastRefreshRootId = -1;

        for ( int Id : PositionIds )
        {
            if ( Id < 0 || Id >= ObjectMax || positionStamp[Id] == updateStamp )
                continue;
            Abc_Obj_t * pObject = Abc_NtkObj(pNtk, Id);
            if ( pObject == nullptr || !Abc_ObjIsNode(pObject) )
                continue;
            double X, Y;
            if ( !Pa_ManReadObjectPosition(pNtk, pObject, &X, &Y) )
                return false;
            nodes[Id].x = X;
            nodes[Id].y = Y;
            positionStamp[Id] = updateStamp;
        }

        // Arrival is a forward data-flow problem.  Seed every changed object
        // and every fanout whose incident edge or fanin identity changed.
        // Propagate through all live old objects up to the processed root ID.
        // This restores the already-visited prefix after moving a reused
        // object; future roots repair their own cones lazily.  Explicitly
        // seeded high-ID new objects and direct fanouts are still updated.
        workQueue.clear();
        // With unrestricted rs propagation, a FIFO can revisit a reconvergent
        // cone once per path length. ABC has already updated structural levels
        // in Abc_AigReplace. Bucket by those levels (not old IDs/timing ranks)
        // so each node follows all affected fanins, without a heap operation
        // per node. Buckets drain completely and are reused at the next edit.
        // Otherwise the worklist is FIFO.
        bool Ordered = LevelsCurrent && ProcessedRootId == ABC_INFINITY;
        int MinArrivalLevel = ABC_INFINITY, MaxArrivalLevel = -1;
        auto EnqueueArrival = [&](int Id)
        {
            if ( Id < 0 || Id >= ObjectMax || arrivalQueueStamp[Id] == updateStamp || Abc_NtkObj(pNtk, Id) == nullptr )
                return;
            arrivalQueueStamp[Id] = updateStamp;
            arrivalAllowedStamp[Id] = updateStamp;
            if ( Ordered )
            {
                Abc_Obj_t * Object = Abc_NtkObj(pNtk, Id);
                int Rank = Abc_ObjIsCo(Object) ? Abc_ObjFanin0(Object)->Level + 1 : Object->Level;
                if ( Rank >= static_cast<int>(arrivalLevelHead.size()) )
                    arrivalLevelHead.resize(Rank + 1, -1);
                arrivalNext[Id] = arrivalLevelHead[Rank];
                arrivalLevelHead[Rank] = Id;
                MinArrivalLevel = std::min(MinArrivalLevel, Rank);
                MaxArrivalLevel = std::max(MaxArrivalLevel, Rank);
            }
            else
                workQueue.push_back(Id);
        };
        auto EnqueueObjectAndFanouts = [&](int Id)
        {
            if ( Id < 0 || Id >= ObjectMax )
                return;
            Abc_Obj_t * pObject = Abc_NtkObj(pNtk, Id);
            if ( pObject == nullptr )
                return;
            EnqueueArrival(Id);
            Abc_Obj_t * pFanout;
            int i;
            Abc_ObjForEachFanout(pObject, pFanout, i) EnqueueArrival(pFanout->Id);
        };
        for ( int Id : PositionIds )
            EnqueueObjectAndFanouts(Id);
        for ( int Id : StructuralIds )
            EnqueueObjectAndFanouts(Id);

        size_t Head = 0;
        while ( Ordered ? MinArrivalLevel <= MaxArrivalLevel : Head < workQueue.size() )
        {
            int Id;
            if ( Ordered )
            {
                while ( MinArrivalLevel <= MaxArrivalLevel && arrivalLevelHead[MinArrivalLevel] < 0 )
                    ++MinArrivalLevel;
                if ( MinArrivalLevel > MaxArrivalLevel )
                    break;
                Id = arrivalLevelHead[MinArrivalLevel];
                arrivalLevelHead[MinArrivalLevel] = arrivalNext[Id];
            }
            else
            {
                Id = workQueue[Head++];
                arrivalQueueStamp[Id] = 0;
            }
            Abc_Obj_t * pObject = Abc_NtkObj(pNtk, Id);
            if ( pObject == nullptr )
                continue;
            Pa_Arrival NewArrival;
            if ( Abc_ObjIsCo(pObject) )
                NewArrival = nodes[Abc_ObjFanin0(pObject)->Id].arrival;
            else if ( Abc_ObjIsNode(pObject) )
            {
                Abc_Obj_t * pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i)
                {
                    const Pa_TimingNode & Input = nodes[pFanin->Id];
                    NewArrival.logic = std::max(NewArrival.logic, Input.arrival.logic + 1);
                    double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, nodes[Id]);
                    NewArrival.wire = std::max(NewArrival.wire, Input.arrival.wire + Wire);
                }
            }
            const Pa_Arrival OldArrival = nodes[Id].arrival;
            bool Changed = OldArrival.logic != NewArrival.logic || !SameWireValue(OldArrival.wire, NewArrival.wire);
            if ( Changed && s_pSettings->wireTolerance && OldArrival.logic == NewArrival.logic )
            {
                const double rel = std::fabs(OldArrival.wire - NewArrival.wire) /
                                   std::max(1e-12, std::max(std::fabs(OldArrival.wire), std::fabs(NewArrival.wire)));
                if ( rel < kWireChangeTolerance )
                    Changed = false;
            }
            nodes[Id].arrival = NewArrival;
            topoRank[Id] = NewArrival.logic;
            if ( !Changed )
                continue;
            Abc_Obj_t * pFanout;
            int i;
            Abc_ObjForEachFanout(pObject, pFanout, i) if ( pFanout->Id <= ProcessedRootId ||
                                                           arrivalAllowedStamp[pFanout->Id] == updateStamp )
                EnqueueArrival(pFanout->Id);
        }
        return true;
    }

    void InvalidateRequired(Abc_Ntk_t * pNtk, const std::vector<int> & Seeds)
    {
        // Upstream propagation marks dependencies, without computing timing.
        // Already dirty cones are skipped. Values on visited nodes are never
        // rebuilt unless a later root actually consumes them after reuse.
        requiredQueue.clear();
        requiredDirty.resize(nodes.size(), 0);
        auto Mark = [&](int Id)
        {
            if ( Id >= 0 && Id < static_cast<int>(nodes.size()) && Abc_NtkObj(pNtk, Id) != nullptr &&
                 !requiredDirty[Id] )
            {
                requiredDirty[Id] = 1;
                requiredQueue.push_back(Id);
            }
        };
        for ( int Id : Seeds )
            Mark(Id);
        for ( size_t Head = 0; Head < requiredQueue.size(); ++Head )
        {
            Abc_Obj_t * pObject = Abc_NtkObj(pNtk, requiredQueue[Head]);
            Abc_Obj_t * pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) Mark(pFanin->Id);
        }
    }

    bool RefreshRequiredUses(Abc_Obj_t * pRoot)
    {
        auto Refresh = [&](auto && Self, Abc_Obj_t * Object) -> bool
        {
            int Id = Object->Id;
            if ( Id < 0 || Id >= static_cast<int>(requiredDirty.size()) )
                return false;
            if ( requiredDirty[Id] == 0 )
                return true;
            if ( requiredDirty[Id] == 2 )
                return false;
            requiredDirty[Id] = 2;
            int Logic = Abc_ObjIsCo(Object) ? maxLogic : ABC_INFINITY;
            double Wire = Abc_ObjIsCo(Object) ? maxWire : std::numeric_limits<double>::infinity();
            Abc_Obj_t * Fanout;
            int i;
            Abc_ObjForEachFanout(Object, Fanout, i)
            {
                if ( !Self(Self, Fanout) )
                    return false;
                const auto & Out = nodes[Fanout->Id];
                int Step = Abc_ObjIsCo(Fanout) ? 0 : 1;
                double Length = Abc_ObjIsCo(Fanout) || Abc_ObjIsCi(Object) ? 0.0 : Distance(nodes[Id], Out);
                if ( Out.requiredLogic != ABC_INFINITY )
                    Logic = std::min(Logic, Out.requiredLogic - Step);
                if ( std::isfinite(Out.requiredWire) )
                    Wire = std::min(Wire, Out.requiredWire - Length);
            }
            nodes[Id].requiredLogic = Logic;
            nodes[Id].requiredWire = Wire;
            requiredDirty[Id] = 0;
            return true;
        };
        Abc_Obj_t * Fanout;
        int i;
        Abc_ObjForEachFanout(pRoot, Fanout, i) if ( !Refresh(Refresh, Fanout) ) return false;
        return true;
    }

    bool RefreshMarkedCone(Abc_Obj_t * pRoot)
    {
        if ( !ready || pRoot == nullptr || pRoot->pNtk != network )
            return false;
        Abc_Ntk_t * pNtk = pRoot->pNtk;
        // Candidate evaluation is side-effect free.  The old root timing is
        // therefore independent of which cut is currently marked and only
        // needs one lazy refresh while all cuts of this root are tried.  An
        // accepted edit invalidates this key in UpdateAfterLocalEdit().
        if ( lastRefreshRootId == pRoot->Id )
            return true;
        // RW/RF keep the pass's required times; exact timing (RS, whose
        // divisors can lie outside the cone) refreshes them lazily.
        if ( s_pSettings->exactTiming && !RefreshRequiredUses(pRoot) )
            return false;
        int ObjectMax = Abc_NtkObjNumMax(pNtk);
        if ( static_cast<int>(nodes.size()) < ObjectMax )
        {
            nodes.resize(ObjectMax);
            topoRank.resize(ObjectMax, 0);
            positionStamp.resize(ObjectMax, 0);
            arrivalQueueStamp.resize(ObjectMax, 0);
            arrivalAllowedStamp.resize(ObjectMax, 0);
            refreshStamp.resize(ObjectMax, 0);
        }
        if ( ++refreshGeneration == 0 )
        {
            std::fill(refreshStamp.begin(), refreshStamp.end(), 0);
            refreshGeneration = 1;
        }

        refreshOrder.clear();
        auto Collect = [&](auto && Self, Abc_Obj_t * pObject) -> void
        {
            pObject = Abc_ObjRegular(pObject);
            if ( pObject == nullptr || pObject->Id < 0 || pObject->Id >= ObjectMax ||
                 refreshStamp[pObject->Id] == refreshGeneration )
                return;
            refreshStamp[pObject->Id] = refreshGeneration;
            if ( Abc_ObjIsNode(pObject) && Abc_NodeIsTravIdCurrent(pObject) )
            {
                Abc_Obj_t * pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i) Self(Self, pFanin);
            }
            refreshOrder.push_back(pObject->Id);
        };
        Collect(Collect, pRoot);

        for ( int Id : refreshOrder )
        {
            Abc_Obj_t * pObject = Abc_NtkObj(pNtk, Id);
            if ( pObject == nullptr )
                return false;
            Pa_Arrival NewArrival;
            if ( Abc_ObjIsCo(pObject) )
                NewArrival = nodes[Abc_ObjFanin0(pObject)->Id].arrival;
            else if ( Abc_ObjIsNode(pObject) )
            {
                Abc_Obj_t * pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i)
                {
                    const Pa_TimingNode & Input = nodes[pFanin->Id];
                    NewArrival.logic = std::max(NewArrival.logic, Input.arrival.logic + 1);
                    double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, nodes[Id]);
                    NewArrival.wire = std::max(NewArrival.wire, Input.arrival.wire + Wire);
                }
            }
            nodes[Id].arrival = NewArrival;
            topoRank[Id] = NewArrival.logic;
        }
        lastRefreshRootId = pRoot->Id;
        return true;
    }
};

static ABC_THREAD_LOCAL Pa_TimingCache * s_pTiming = nullptr;

/**Function*************************************************************

  Synopsis    [Clamps a value to [Low, High]; an empty interval gives its midpoint.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Pa_Clamp(double Value, double Low, double High)
{
    if ( Low > High )
        return 0.5 * (Low + High);
    return std::max(Low, std::min(High, Value));
}

/**Function*************************************************************

  Synopsis    [Compares two values with a relative tolerance.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static bool Pa_AlmostLess(double A, double B)
{
    double Epsilon = kCompareTolerance * (1.0 + std::max(std::fabs(A), std::fabs(B)));
    return A < B - Epsilon;
}

/**Function*************************************************************

  Synopsis    [Compares two values with a relative tolerance.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static bool Pa_AlmostEqual(double A, double B)
{
    double Epsilon = kCompareTolerance * (1.0 + std::max(std::fabs(A), std::fabs(B)));
    return std::fabs(A - B) <= Epsilon;
}

class Pa_DensityWorkspace
{
public:
    Pa_DensityWorkspace(Abc_Ntk_t * pNtk, double Width, double Height, int Bins, double BinSizeX, double BinSizeY)
        : pNtk_(pNtk), width_(Width), height_(Height), bins_(Bins), binSizeX_(BinSizeX), binSizeY_(BinSizeY)
    {
        s_pReadCache->BeginCandidate(Bins * Bins);
        valid_ = Pa_ManReadDensityBin(pNtk_, 0, 0, nullptr, &targetArea_) != 0;
    }

    bool IsValid() const
    {
        return valid_;
    }

    void Add(const Pa_Geometry & Geometry, double Sign)
    {
        exactAreaDelta_ += Sign * Geometry.width;
        auto & Contributions = scratch_;
        ContributionsAt(Geometry, Geometry.x, Geometry.y, Contributions);
        for ( const auto & Entry : Contributions )
        {
            auto & B = s_pReadCache->bins[Entry.first];
            if ( B.deltaStamp != s_pReadCache->candidate )
            {
                B.deltaStamp = s_pReadCache->candidate;
                B.delta = 0.0;
                touched_.push_back(Entry.first);
            }
            B.delta += Sign * Entry.second;
        }
    }

    struct AxisFootprint
    {
        double low = 0.0, high = 0.0;
        int first = 0, last = -1;
        std::array<double, 8> overlaps;
        bool cached = false;
    };

    AxisFootprint PrepareAxis(double Center, double Half, bool XAxis) const
    {
        double Limit = XAxis ? width_ : height_;
        double BinSize = XAxis ? binSizeX_ : binSizeY_;
        AxisFootprint Axis;
        Axis.low = std::max(0.0, Center - Half);
        Axis.high = std::min(Limit, Center + Half);
        if ( Axis.high <= Axis.low )
            return Axis;
        Axis.first = std::max(0, std::min(bins_ - 1, static_cast<int>(Axis.low / BinSize)));
        Axis.last =
            std::max(0, std::min(bins_ - 1, static_cast<int>(Pa_PreviousBoundary(Axis.high, Axis.low) / BinSize)));
        if ( Axis.last - Axis.first < 8 )
        {
            Axis.cached = true;
            for ( int b = Axis.first; b <= Axis.last; ++b )
                Axis.overlaps[b - Axis.first] =
                    std::max(0.0, std::min(Axis.high, (b + 1) * BinSize) - std::max(Axis.low, b * BinSize));
        }
        return Axis;
    }

    // The sample grid is a Cartesian product: bin ranges depend only on one
    // axis, so prepare each of them once.
    double EvaluateAddition(const Pa_Geometry & Geometry, const AxisFootprint & X, const AxisFootprint & Y)
    {
        double Cost = 0.0;
        for ( int Bx = X.first; Bx <= X.last; ++Bx )
        {
            double OverlapX =
                X.cached ? X.overlaps[Bx - X.first]
                         : std::max(0.0, std::min(X.high, (Bx + 1) * binSizeX_) - std::max(X.low, Bx * binSizeX_));
            for ( int By = Y.first; By <= Y.last; ++By )
            {
                double OverlapY =
                    Y.cached ? Y.overlaps[By - Y.first]
                             : std::max(0.0, std::min(Y.high, (By + 1) * binSizeY_) - std::max(Y.low, By * binSizeY_));
                double Area = OverlapX * OverlapY * Geometry.densityScale;
                if ( Area > 0.0 )
                    Cost += Current(Bx * bins_ + By) * Area / std::max(1.0e-12, targetArea_);
            }
        }
        return Cost;
    }

    double ExactAreaDelta() const
    {
        return exactAreaDelta_;
    }

    double OverflowDelta()
    {
        double Result = 0.0;
        for ( int Index : touched_ )
        {
            double Base = BaseDensity(Index);
            Result +=
                std::max(0.0, Base + s_pReadCache->bins[Index].delta - targetArea_) - std::max(0.0, Base - targetArea_);
        }
        return Result;
    }

private:
    int BinX(double X) const
    {
        return std::max(0, std::min(bins_ - 1, static_cast<int>(X / binSizeX_)));
    }

    int BinY(double Y) const
    {
        return std::max(0, std::min(bins_ - 1, static_cast<int>(Y / binSizeY_)));
    }

    void ContributionsAt(const Pa_Geometry & Geometry, double X, double Y,
                         std::vector<std::pair<int, double>> & Result) const
    {
        Result.clear();
        double X0 = std::max(0.0, X - Geometry.densityHalfX);
        double X1 = std::min(width_, X + Geometry.densityHalfX);
        double Y0 = std::max(0.0, Y - Geometry.densityHalfY);
        double Y1 = std::min(height_, Y + Geometry.densityHalfY);
        if ( X1 <= X0 || Y1 <= Y0 )
            return;
        int Bx0 = BinX(X0);
        int Bx1 = BinX(Pa_PreviousBoundary(X1, X0));
        int By0 = BinY(Y0);
        int By1 = BinY(Pa_PreviousBoundary(Y1, Y0));
        for ( int Bx = Bx0; Bx <= Bx1; ++Bx )
            for ( int By = By0; By <= By1; ++By )
            {
                double OverlapX = std::max(0.0, std::min(X1, (Bx + 1) * binSizeX_) - std::max(X0, Bx * binSizeX_));
                double OverlapY = std::max(0.0, std::min(Y1, (By + 1) * binSizeY_) - std::max(Y0, By * binSizeY_));
                double Area = OverlapX * OverlapY * Geometry.densityScale;
                if ( Area > 0.0 )
                    Result.emplace_back(Bx * bins_ + By, Area);
            }
    }

    double BaseDensity(int Index)
    {
        auto & B = s_pReadCache->bins[Index];
        if ( B.baseStamp != s_pReadCache->version )
        {
            if ( !Pa_ManReadDensityBin(pNtk_, Index / bins_, Index % bins_, &B.base, nullptr) )
                valid_ = false;
            B.baseStamp = s_pReadCache->version;
        }
        return B.base;
    }

    double Current(int Index)
    {
        const auto & B = s_pReadCache->bins[Index];
        return BaseDensity(Index) + (B.deltaStamp == s_pReadCache->candidate ? B.delta : 0.0);
    }

    Abc_Ntk_t * pNtk_ = nullptr;
    double width_ = 0.0;
    double height_ = 0.0;
    int bins_ = 0;
    double binSizeX_ = 0.0;
    double binSizeY_ = 0.0;
    double targetArea_ = 0.0;
    bool valid_ = false;
    double exactAreaDelta_ = 0.0;
    PaWorkspace::WorkspaceVector<int> touched_;
    // Reuse the footprint buffer for all samples of this candidate.
    PaWorkspace::WorkspaceVector<std::pair<int, double>> scratch_;
};

// One candidate is live at a time. Generation tags reuse an ID-indexed
// lookup without clearing the whole network or allocating hash nodes for
// each candidate entity. The full plan owns all geometry and placement.
class Pa_EntityIndex
{
    struct Entry
    {
        Abc_Obj_t * first = nullptr;
        int second = -1;
        unsigned stamp = 0;
    };
    static thread_local std::vector<Entry> entries_;
    static thread_local unsigned generation_;
    unsigned stamp_;

public:
    Pa_EntityIndex() : stamp_(++generation_)
    {
        if ( stamp_ == 0 )
        {
            entries_.clear();
            stamp_ = generation_ = 1;
        }
    }
    const Entry * end() const
    {
        return nullptr;
    }
    const Entry * find(Abc_Obj_t * Object) const
    {
        if ( !Object || static_cast<size_t>(Object->Id) >= entries_.size() )
            return nullptr;
        const auto & E = entries_[Object->Id];
        return E.stamp == stamp_ && E.first == Object ? &E : nullptr;
    }
    void emplace(Abc_Obj_t * Object, int Value)
    {
        if ( static_cast<size_t>(Object->Id) >= entries_.size() )
            entries_.resize(std::max(static_cast<size_t>(Object->Id + 1), entries_.size() * 2));
        entries_[Object->Id] = Entry{Object, Value, stamp_};
    }
};

thread_local std::vector<Pa_EntityIndex::Entry> Pa_EntityIndex::entries_;
thread_local unsigned Pa_EntityIndex::generation_ = 0;

// Small candidate MFFCs use sorted contiguous membership. No pointer-hash
// iteration or allocation per object; enumeration is stable by object ID.
class Pa_ObjectSet
{
    PaWorkspace::WorkspaceVector<Abc_Obj_t *> items_;
    auto lower(Abc_Obj_t * v) const
    {
        return std::lower_bound(items_.begin(), items_.end(), v,
                                [](Abc_Obj_t * a, Abc_Obj_t * b) { return a->Id < b->Id; });
    }

public:
    using iterator = std::vector<Abc_Obj_t *>::const_iterator;
    iterator begin() const
    {
        return items_.begin();
    }
    iterator end() const
    {
        return items_.end();
    }
    size_t size() const
    {
        return items_.size();
    }
    size_t count(Abc_Obj_t * v) const
    {
        if ( !v )
            return 0;
        auto it = lower(v);
        return it != end() && *it == v;
    }
    std::pair<iterator, bool> insert(Abc_Obj_t * v)
    {
        auto it = lower(v);
        if ( it != end() && *it == v )
            return {it, false};
        return {items_.insert(it, v), true};
    }
    void erase(Abc_Obj_t * v)
    {
        auto it = lower(v);
        if ( it != end() && *it == v )
            items_.erase(it);
    }
};

/**Function*************************************************************

  Synopsis    [Allocation-free structural screen of a small candidate.]

  Description [Allocation-free structural screen for small decomposition
               graphs. It uses the same live/virtual hashing,
               simplification and zero-fanout rules as the full plan. Only
               definitely invalid plans are rejected here; larger graphs
               and all retained-cone accounting still use the full
               evaluator.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static bool Pa_StructuralScreen(Abc_Obj_t * Root, Dec_Graph_t * Graph, int Saved, int LevelMax)
{
    constexpr int Limit = 64;
    if ( Graph->nSize > Limit || Dec_GraphIsConst(Graph) )
        return true;
    struct Entry
    {
        Abc_Obj_t * object;
        int refs, level, left, right;
    };
    Entry Entries[Limit + 1];
    int Literals[Limit], Count = 0, NewCount = 0;
    auto Actual = [&](Abc_Obj_t * Literal)
    {
        Abc_Obj_t * Object = Abc_ObjRegular(Literal);
        for ( int i = 0; i < Count; ++i )
            if ( Entries[i].object == Object )
                return 2 * i + Abc_ObjIsComplement(Literal);
        Entries[Count] = Entry{Object, Abc_ObjFanoutNum(Object), (int)Object->Level, -1, -1};
        return 2 * Count++ + Abc_ObjIsComplement(Literal);
    };
    Dec_Node_t * Node;
    int i;
    Dec_GraphForEachLeaf(Graph, Node, i)
    {
        Abc_Obj_t * Object = static_cast<Abc_Obj_t *>(Node->pFunc);
        if ( Object == nullptr || Abc_ObjRegular(Object) == Root )
            return false;
        Literals[i] = Actual(Object);
    }
    Dec_GraphForEachNode(Graph, Node, i)
    {
        if ( Node->eEdge0.Node >= (unsigned)i || Node->eEdge1.Node >= (unsigned)i )
            return false;
        int A = Literals[Node->eEdge0.Node] ^ Node->eEdge0.fCompl;
        int B = Literals[Node->eEdge1.Node] ^ Node->eEdge1.fCompl;
        int Result = -1;
        if ( A / 2 == B / 2 )
            Result = A == B ? A : (Actual(Abc_AigConst1(Root->pNtk)) ^ 1);
        else
        {
            int Const = Actual(Abc_AigConst1(Root->pNtk));
            if ( A / 2 == Const / 2 )
                Result = (A & 1) ? (Const ^ 1) : B;
            else if ( B / 2 == Const / 2 )
                Result = (B & 1) ? (Const ^ 1) : A;
            else
            {
                int Low = std::min(A, B), High = std::max(A, B);
                if ( Entries[A / 2].refs && Entries[B / 2].refs )
                {
                    for ( int k = Count - 1; k >= 0; --k )
                        if ( Entries[k].object == nullptr && Entries[k].left == Low && Entries[k].right == High )
                        {
                            Result = 2 * k;
                            break;
                        }
                    Abc_Obj_t * Left = Entries[A / 2].object;
                    Abc_Obj_t * Right = Entries[B / 2].object;
                    if ( Result < 0 && Left && Right )
                    {
                        bool LiftLeft = Abc_ObjFanoutNum(Left) == 0;
                        bool LiftRight = Abc_ObjFanoutNum(Right) == 0;
                        if ( LiftLeft )
                            ++Left->vFanouts.nSize;
                        if ( LiftRight )
                            ++Right->vFanouts.nSize;
                        Abc_Obj_t * Found = Abc_AigAndLookup(static_cast<Abc_Aig_t *>(Root->pNtk->pManFunc),
                                                             Abc_ObjNotCond(Left, A & 1), Abc_ObjNotCond(Right, B & 1));
                        if ( LiftRight )
                            --Right->vFanouts.nSize;
                        if ( LiftLeft )
                            --Left->vFanouts.nSize;
                        if ( Found )
                        {
                            if ( Abc_ObjRegular(Found) == Root )
                                return false;
                            Result = Actual(Found);
                        }
                    }
                }
                if ( Result < 0 )
                {
                    if ( ++NewCount > Saved + 0 )
                        return false;
                    int Level = 1 + std::max(Entries[A / 2].level, Entries[B / 2].level);
                    Entries[Count] = Entry{nullptr, 0, Level, Low, High};
                    Result = 2 * Count++;
                    ++Entries[A / 2].refs;
                    ++Entries[B / 2].refs;
                }
            }
        }
        if ( Entries[Result / 2].level > LevelMax )
            return false;
        Literals[i] = Result;
    }
    return Graph->eRoot.Node < (unsigned)Graph->nSize && Entries[Literals[Graph->eRoot.Node] / 2].object != Root;
}

// Only the labeled original MFFC is shared between candidates of one live
// cut. Retained nodes, placement, density and scores are rebuilt per candidate.
// A commit/pass change invalidates the placement version; a new cut changes
// the network traversal ID. Neither pointers nor marks cross those boundaries.
struct Pa_MffcCache
{
    Abc_Ntk_t * network = nullptr;
    Abc_Obj_t * root = nullptr;
    unsigned version = 0;
    int traversal = -1;
    Pa_ObjectSet removed;
    PaWorkspace::WorkspaceVector<int> ids;
};
static ABC_THREAD_LOCAL Pa_MffcCache * s_pMffcCache = nullptr;

class Pa_CandidatePlan
{
public:
    Pa_CandidatePlan(Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int nNodesSaved, int levelMax, int fRootComplement = 0)
        : pRoot_(pRoot), pNtk_(pRoot ? pRoot->pNtk : nullptr), pGraph_(pGraph), nNodesSaved_(nNodesSaved),
          levelMax_(levelMax), rootComplement_(fRootComplement != 0)
    {
        if ( pRoot_ == nullptr || pGraph_ == nullptr || pNtk_ == nullptr || !Pa_ManIsPassActive(pNtk_) ||
             !Pa_ManReadCanvas(pNtk_, &width_, &height_, &bins_, &binSizeX_, &binSizeY_) ||
             !Pa_ManReadMetrics(pNtk_, nullptr, nullptr, &hpwlScale_, nullptr) )
            return;
        {
            const size_t capacity = pGraph_->nSize + 8;
            entities_.reserve(capacity);
            addedFanouts_.reserve(capacity);
            virtualInputs_.reserve(capacity);
            timingInputs_.reserve(capacity);
            timingProduced_.reserve(capacity);
            timingBoundary_.reserve(capacity);
            entityLevels_.reserve(capacity);
            symbolicFanouts_.reserve(capacity);
            virtualEntities_.reserve(pGraph_->nSize);
            movableEntities_.reserve(pGraph_->nSize);
            nets_.reserve(capacity);
        }
        CollectRemoved();
        if ( static_cast<int>(removed_.size()) != nNodesSaved_ )
            return;
        // Clusters come from the original MFFC, before structural reuse can
        // shrink the set actually removed.
        if ( s_pSettings->clusterEvaluation && !BuildClusters() )
            return;
        BuildEntities();
        if ( !validBuild_ )
            return;
        ComputeRemovedAfterMaterialization();
        if ( !validBuild_ )
            return;
        if ( actualGain_ < 0 )
            return;
        // Cell widths depend on polarity, not candidate coordinates. Reject a
        // provable physical-area violation before constructing nets/placement.
        if ( s_pSettings->physicalAreaGuard && !(actualGain_ > 0) && AreaDeltaBeforePlacement() > 1e-9 )
            return;
        if ( HasDownstreamCascade() )
        {
            return;
        }
        density_.reset(new Pa_DensityWorkspace(pNtk_, width_, height_, bins_, binSizeX_, binSizeY_));
        if ( !density_->IsValid() )
            return;
        BuildMovables();
        // Fixed extrema retain exact HPWL and median regions; no count-based
        // candidate pruning is needed to use this representation.
        BuildNetsFast();

        InitializeDensity();
        if ( !validBuild_ )
            return;
        SeedFromPropagatedRegions();
        if ( !validBuild_ )
            return;
        if ( s_pSettings->clusterEvaluation )
            SnapVirtualNodesToClusters();
        // Repair, else reject, a candidate that raises the overflow above
        // max(0.099, current overflow).
        if ( s_pSettings->capacityRepair )
        {
            double currentArea = 0, currentOverflow = 0;
            Pa_ManReadMetrics(pNtk_, nullptr, &currentOverflow, nullptr, &currentArea);
            double next = (currentOverflow * currentArea + density_->OverflowDelta()) /
                          std::max(1e-9, currentArea + density_->ExactAreaDelta());
            if ( next > std::max(.099, currentOverflow) + 1e-9 )
            {
                RepairCapacity(currentArea, currentOverflow);
                next = (currentOverflow * currentArea + density_->OverflowDelta()) /
                       std::max(1e-9, currentArea + density_->ExactAreaDelta());
            }
            if ( next > std::max(.099, currentOverflow) + 1e-9 )
                return;
        }

        hpwlAdded_ = LocalHpwl();
        score_ = static_cast<double>(actualGain_) + 0.25 * (hpwlSaved_ - hpwlAdded_) / hpwlScale_;
        if ( s_pSettings->timingEvaluation && !EvaluateTiming() )
            return;
        valid_ = actualGain_ >= 0 && std::isfinite(score_) && std::isfinite(hpwlSaved_) && std::isfinite(hpwlAdded_) &&
                 density_->IsValid() &&
                 (!s_pSettings->physicalAreaGuard || density_->ExactAreaDelta() <= 1e-9 || actualGain_ > 0);
    }

    bool IsValid() const
    {
        return valid_;
    }

    int Gain() const
    {
        return actualGain_;
    }
    double Score() const
    {
        return score_;
    }
    double HpwlSaved() const
    {
        return hpwlSaved_;
    }
    double HpwlAdded() const
    {
        return hpwlAdded_;
    }

    double DensityDelta() const
    {
        return density_->OverflowDelta();
    }
    bool ResultIsVirtual() const
    {
        return resultEntity_ >= 0 && entities_[resultEntity_].virtualNode;
    }

    bool StageOldPlacement() const
    {
        for ( Abc_Obj_t * pRemoved : orderedRemoved_ )
            if ( !Pa_ManStageObjectRemoval(pNtk_, pRemoved) )
                return false;
        Abc_Obj_t * pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout,
                             i) if ( Abc_ObjIsNode(pFanout) && !Pa_ManStageObjectRefresh(pNtk_, pFanout) ) return false;
        return true;
    }

    bool ReversesRecentStructure() const
    {
        return false;
    }

    bool MaterializationMatchesPlan(Dec_Graph_t * pGraph, int FirstNewId, std::vector<int> & NewIds) const
    {
        std::unordered_set<Abc_Obj_t *> NewObjects;
        std::unordered_map<int, Abc_Obj_t *> Realized;
        Dec_Node_t * pDecNode;
        int i;
        Dec_GraphForEachNode(pGraph, pDecNode, i)
        {
            Abc_Obj_t * pLiteral = static_cast<Abc_Obj_t *>(pDecNode->pFunc);
            if ( pLiteral == nullptr || i >= static_cast<int>(decToEntity_.size()) )
                return false;
            int EntityId = decToEntity_[i];
            if ( EntityId < 0 )
                return false;
            Abc_Obj_t * pObject = Abc_ObjRegular(pLiteral);
            const Pa_Entity & Entity = entities_[EntityId];
            if ( (Abc_ObjIsComplement(pLiteral) != 0) != (decPhase_[i] != 0) )
                return false;
            if ( Entity.virtualNode )
            {
                if ( !Abc_ObjIsNode(pObject) || pObject->Id < FirstNewId )
                    return false;
                auto It = Realized.find(EntityId);
                if ( It != Realized.end() )
                {
                    if ( It->second != pObject )
                        return false;
                }
                else
                {
                    if ( !NewObjects.insert(pObject).second )
                        return false;
                    Realized.emplace(EntityId, pObject);
                    NewIds.push_back(pObject->Id);
                }
            }
            else if ( pObject != Entity.object )
                return false;
        }
        if ( NewObjects.size() != virtualEntities_.size() )
            return false;
        for ( int Id = FirstNewId; Id < Abc_NtkObjNumMax(pNtk_); ++Id )
        {
            Abc_Obj_t * pObject = Abc_NtkObj(pNtk_, Id);
            if ( pObject != nullptr && Abc_ObjIsNode(pObject) && !NewObjects.count(pObject) )
                return false;
        }
        return true;
    }

    bool BoundaryMatchesPlan(const std::vector<int> & NewIds, const std::vector<Pa_DirectFanout> & DirectFanouts,
                             Abc_Obj_t * pRootNew) const
    {
        for ( int Id : removedIds_ )
            if ( Abc_NtkObj(pNtk_, Id) != nullptr )
                return false;
        for ( int Id : NewIds )
            if ( Id >= Abc_NtkObjNumMax(pNtk_) || Abc_NtkObj(pNtk_, Id) == nullptr )
                return false;
        for ( const auto & Entry : DirectFanouts )
        {
            if ( Abc_NtkObj(pNtk_, Entry.id) != Entry.object || Abc_ObjFaninNum(Entry.object) != 2 )
                return false;
            Abc_Obj_t * pExpected = Abc_ObjNotCond(pRootNew, Entry.rootComplement);
            Abc_Obj_t * pActual0 = Abc_ObjChild0(Entry.object);
            Abc_Obj_t * pActual1 = Abc_ObjChild1(Entry.object);
            if ( !((pActual0 == pExpected && pActual1 == Entry.otherFanin) ||
                   (pActual1 == pExpected && pActual0 == Entry.otherFanin)) )
                return false;
        }
        return true;
    }

    std::vector<int> RequiredBoundaryIds() const
    {
        std::vector<int> Result;
        for ( Abc_Obj_t * pObject : orderedRemoved_ )
        {
            Abc_Obj_t * pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) if ( !removed_.count(pFanin) ) Result.push_back(pFanin->Id);
        }
        return Result;
    }

    std::vector<Pa_DirectFanout> DirectFanouts() const
    {
        std::vector<Pa_DirectFanout> Result;
        Abc_Obj_t * pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout, i) if ( Abc_ObjIsNode(pFanout) )
        {
            int RootIndex = Vec_IntFind(&pFanout->vFanins, pRoot_->Id);
            if ( RootIndex < 0 )
                continue;
            Result.push_back(Pa_DirectFanout{pFanout->Id, pFanout, Abc_ObjChild(pFanout, RootIndex ^ 1),
                                             Abc_ObjFaninC(pFanout, RootIndex) != 0});
        }
        return Result;
    }

    std::vector<int> TimingMovedObjectIds() const
    {
        std::vector<int> Result;
        for ( int EntityId : movableEntities_ )
        {
            const Pa_Entity & Entity = entities_[EntityId];
            if ( !Entity.virtualNode && Entity.object != nullptr && !removed_.count(Entity.object) )
                Result.push_back(Entity.object->Id);
        }
        SortUnique(Result);
        return Result;
    }

    bool WriteUpdatedPositions(Dec_Graph_t * pGraph, int FirstNewId) const
    {
        std::unordered_set<Abc_Obj_t *> Written;
        double RootX = 0.5 * width_, RootY = 0.5 * height_;
        Pa_ManReadObjectPosition(pNtk_, pRoot_, &RootX, &RootY);
        Dec_Node_t * pDecNode;
        int DecIndex;
        Dec_GraphForEachNode(pGraph, pDecNode, DecIndex)
        {
            if ( pDecNode->pFunc == nullptr )
                return false;
            Abc_Obj_t * pObject = Abc_ObjRegular(static_cast<Abc_Obj_t *>(pDecNode->pFunc));
            if ( !Abc_ObjIsNode(pObject) || pObject->Id < FirstNewId || !Written.insert(pObject).second )
                continue;
            int EntityId = decToEntity_[DecIndex];
            double X = RootX, Y = RootY;
            if ( EntityId >= 0 && entities_[EntityId].virtualNode )
            {
                X = entities_[EntityId].geometry.x;
                Y = entities_[EntityId].geometry.y;
            }
            if ( !Pa_ManWriteObjectPosition(pNtk_, pObject, X, Y) )
                return false;
        }
        for ( int EntityId : movableEntities_ )
        {
            const Pa_Entity & Entity = entities_[EntityId];
            if ( Entity.virtualNode || Entity.object == nullptr || !Written.insert(Entity.object).second )
                continue;
            if ( !Pa_ManWriteObjectPosition(pNtk_, Entity.object, Entity.geometry.x, Entity.geometry.y) )
                return false;
        }
        return true;
    }

private:
    bool TimingPosition(Abc_Obj_t * pObject, double * pX, double * pY) const
    {
        if ( pObject == pRoot_ )
        {
            if ( resultEntity_ < 0 )
                return false;
            const Pa_Geometry & G = entities_[resultEntity_].geometry;
            *pX = G.x;
            *pY = G.y;
            return true;
        }
        auto It = actualEntities_.find(pObject);
        if ( It != actualEntities_.end() && entities_[It->second].hasPoint )
        {
            const Pa_Geometry & G = entities_[It->second].geometry;
            *pX = G.x;
            *pY = G.y;
            return true;
        }
        if ( pObject->Id < 0 || pObject->Id >= static_cast<int>(s_pTiming->nodes.size()) )
            return false;
        *pX = s_pTiming->nodes[pObject->Id].x;
        *pY = s_pTiming->nodes[pObject->Id].y;
        return true;
    }

    bool TimingEntityPosition(int Entity, double * pX, double * pY) const
    {
        const Pa_Entity & E = entities_[Entity];
        if ( E.virtualNode )
        {
            *pX = E.geometry.x;
            *pY = E.geometry.y;
            return true;
        }
        return E.object != nullptr && TimingPosition(E.object, pX, pY);
    }

    bool TimingIsCi(Abc_Obj_t * pObject) const
    {
        if ( pObject == pRoot_ )
        {
            Abc_Obj_t * pReplacement = entities_[resultEntity_].object;
            return pReplacement != nullptr && Abc_ObjIsCi(pReplacement);
        }
        return Abc_ObjIsCi(pObject);
    }

    bool TimingForEntity(int Entity, Pa_Arrival * pResult)
    {
        const Pa_Entity & E = entities_[Entity];
        if ( !E.virtualNode )
            return E.object != nullptr && TimingForObject(E.object, pResult);
        if ( timingEntityState_[Entity] == 2 )
        {
            *pResult = timingEntityMemo_[Entity];
            return true;
        }
        if ( timingEntityState_[Entity] == 1 )
            return false;
        timingEntityState_[Entity] = 1;
        Pa_Arrival Arrival;
        const auto & Inputs = virtualInputs_[Entity];
        for ( int Child : {Inputs.first.entity, Inputs.second.entity} )
        {
            Pa_Arrival Input;
            double X, Y;
            if ( !TimingForEntity(Child, &Input) || !TimingEntityPosition(Child, &X, &Y) )
                return false;
            const Pa_Entity & Source = entities_[Child];
            double Wire = Source.object != nullptr && Abc_ObjIsCi(Source.object)
                              ? 0.0
                              : std::hypot(X - E.geometry.x, Y - E.geometry.y);
            Arrival.logic = std::max(Arrival.logic, Input.logic + 1);
            Arrival.wire = std::max(Arrival.wire, Input.wire + Wire);
        }
        timingEntityState_[Entity] = 2;
        timingEntityMemo_[Entity] = Arrival;
        *pResult = Arrival;
        return true;
    }

    bool TimingForEntityLocal(int Entity, Pa_Arrival * pResult)
    {
        if ( Entity < 0 || Entity >= static_cast<int>(entities_.size()) )
            return false;
        if ( timingEntityState_[Entity] == 2 )
        {
            *pResult = timingEntityMemo_[Entity];
            return true;
        }
        if ( timingEntityState_[Entity] == 1 )
            return false;
        const Pa_Entity & E = entities_[Entity];

        // An unchanged boundary object keeps its cached arrival.  Candidate
        // core objects are the virtual ANDs and structurally reused ANDs
        // produced by this graph; placement can also move a literal result,
        // in which case its two real fanins are a bounded local update.
        if ( !E.virtualNode && !E.movable && !timingProduced_[Entity] && !timingBoundary_[Entity] )
        {
            if ( E.object == nullptr || E.object->Id < 0 || E.object->Id >= static_cast<int>(s_pTiming->nodes.size()) )
                return false;
            *pResult = s_pTiming->nodes[E.object->Id].arrival;
            return true;
        }

        timingEntityState_[Entity] = 1;
        Pa_Arrival Arrival;
        double X, Y;
        if ( !TimingEntityPosition(Entity, &X, &Y) )
            return false;
        auto Accumulate = [&](int Child, Abc_Obj_t * pChildObject) -> bool
        {
            Pa_Arrival Input;
            double InputX, InputY;
            if ( Child >= 0 )
            {
                if ( !TimingForEntityLocal(Child, &Input) || !TimingEntityPosition(Child, &InputX, &InputY) )
                    return false;
                pChildObject = entities_[Child].object;
            }
            else
            {
                pChildObject = Abc_ObjRegular(pChildObject);
                if ( pChildObject == nullptr || pChildObject->Id < 0 ||
                     pChildObject->Id >= static_cast<int>(s_pTiming->nodes.size()) ||
                     !TimingPosition(pChildObject, &InputX, &InputY) )
                    return false;
                Input = s_pTiming->nodes[pChildObject->Id].arrival;
            }
            double Wire =
                pChildObject != nullptr && Abc_ObjIsCi(pChildObject) ? 0.0 : std::hypot(InputX - X, InputY - Y);
            Arrival.logic = std::max(Arrival.logic, Input.logic + 1);
            Arrival.wire = std::max(Arrival.wire, Input.wire + Wire);
            return true;
        };

        if ( timingProduced_[Entity] )
        {
            const auto & Inputs = timingInputs_[Entity];
            if ( !Accumulate(Inputs.first.entity, nullptr) || !Accumulate(Inputs.second.entity, nullptr) )
                return false;
        }
        else if ( E.object != nullptr && Abc_ObjIsNode(E.object) )
        {
            Abc_Obj_t * pFanin;
            int i;
            Abc_ObjForEachFanin(E.object, pFanin, i)
            {
                auto It = actualEntities_.find(Abc_ObjRegular(pFanin));
                int Child = It != actualEntities_.end() && (entities_[It->second].movable ||
                                                            timingProduced_[It->second] || timingBoundary_[It->second])
                                ? It->second
                                : -1;
                if ( !Accumulate(Child, pFanin) )
                    return false;
            }
        }
        timingEntityState_[Entity] = 2;
        timingEntityMemo_[Entity] = Arrival;
        *pResult = Arrival;
        return true;
    }

    bool TimingForObject(Abc_Obj_t * pObject, Pa_Arrival * pResult)
    {
        if ( pObject == pRoot_ )
            return TimingForEntity(resultEntity_, pResult);
        if ( pObject->Id < 0 || pObject->Id >= static_cast<int>(s_pTiming->nodes.size()) || removed_.count(pObject) )
            return false;
        auto & Timing = s_pCandidateTiming->objects[pObject->Id];
        unsigned Generation = s_pCandidateTiming->generation;
        if ( Timing.affected != Generation )
        {
            *pResult = s_pTiming->nodes[pObject->Id].arrival;
            return true;
        }
        if ( Timing.memoStamp == Generation )
        {
            *pResult = Timing.memo;
            return true;
        }
        if ( !s_pCandidateTiming->Mark(Timing.visiting) )
            return false;
        Pa_Arrival Arrival;
        if ( Abc_ObjIsCo(pObject) )
        {
            if ( !TimingForObject(Abc_ObjFanin0(pObject), &Arrival) )
                return false;
        }
        else if ( Abc_ObjIsNode(pObject) )
        {
            double X, Y;
            if ( !TimingPosition(pObject, &X, &Y) )
                return false;
            Abc_Obj_t * pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i)
            {
                Pa_Arrival Input;
                double InputX, InputY;
                if ( !TimingForObject(pFanin, &Input) || !TimingPosition(pFanin, &InputX, &InputY) )
                    return false;
                double Wire = TimingIsCi(pFanin) ? 0.0 : std::hypot(InputX - X, InputY - Y);
                Arrival.logic = std::max(Arrival.logic, Input.logic + 1);
                Arrival.wire = std::max(Arrival.wire, Input.wire + Wire);
            }
        }
        Timing.visiting = 0;
        Timing.memo = Arrival;
        Timing.memoStamp = Generation;
        *pResult = Arrival;
        return true;
    }

    void PrepareTimingSeeds()
    {

        // Only old nodes feeding the virtual result are relevant to its
        // arrival. A reused node may move, and its old fanout path may feed
        // another reused node, but following every fanout to the outputs is
        // prohibitively expensive on high-fanout designs. Intersect that
        // fanout path with the old fanin closure of the result's actual
        // anchors. The topological-rank bound prunes ancestors that cannot
        // depend on any moved node. The root's fanouts are evaluated after
        // the root.
        auto & Moved = s_pCandidateTiming->moved;
        int MinMovedRank = ABC_INFINITY;
        for ( int Entity : movableEntities_ )
        {
            Abc_Obj_t * pObject = entities_[Entity].object;
            if ( pObject == nullptr || pObject == pRoot_ || removed_.count(pObject) )
                continue;
            Moved.push_back(pObject);
            MinMovedRank = std::min(MinMovedRank, s_pTiming->topoRank[pObject->Id]);
        }
        if ( s_pSettings->exactTiming )
        {
            // Logical root substitution affects these nodes even if no old
            // reused object moved. Seed them together before fanout evaluation.
            Abc_Obj_t * fo;
            int i;
            Abc_ObjForEachFanout(pRoot_, fo, i) if ( Abc_ObjIsNode(fo) )
            {
                Moved.push_back(fo);
                MinMovedRank = std::min(MinMovedRank, s_pTiming->topoRank[fo->Id]);
            }
        }
        if ( Moved.empty() )
            return;

        auto & Backward = s_pCandidateTiming->backward;
        if ( !entities_[resultEntity_].virtualNode )
            Backward.push_back(entities_[resultEntity_].object);
        if ( s_pSettings->exactTiming )
        {
            Abc_Obj_t * pFanout;
            int k;
            Abc_ObjForEachFanout(pRoot_, pFanout, k) Backward.push_back(pFanout);
        }
        for ( int Entity : virtualEntities_ )
        {
            const auto & Inputs = virtualInputs_[Entity];
            for ( int Child : {Inputs.first.entity, Inputs.second.entity} )
                if ( Child >= 0 && entities_[Child].object != nullptr )
                    Backward.push_back(entities_[Child].object);
        }
        while ( !Backward.empty() )
        {
            Abc_Obj_t * pObject = Backward.back();
            Backward.pop_back();
            if ( pObject == nullptr || pObject == pRoot_ || removed_.count(pObject) ||
                 s_pTiming->topoRank[pObject->Id] < MinMovedRank ||
                 !s_pCandidateTiming->Mark(s_pCandidateTiming->objects[pObject->Id].ancestor) )
                continue;
            if ( Abc_ObjIsNode(pObject) )
            {
                Abc_Obj_t * pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i) Backward.push_back(pFanin);
            }
        }
        auto & Queue = s_pCandidateTiming->queue;
        for ( Abc_Obj_t * pObject : Moved )
            if ( s_pCandidateTiming->objects[pObject->Id].ancestor == s_pCandidateTiming->generation )
                Queue.push_back(pObject);
        for ( size_t Head = 0; Head < Queue.size(); ++Head )
        {
            Abc_Obj_t * pObject = Queue[Head];
            if ( !s_pCandidateTiming->Mark(s_pCandidateTiming->objects[pObject->Id].affected) )
                continue;
            Abc_Obj_t * pFanout;
            int i;
            Abc_ObjForEachFanout(pObject, pFanout, i) if ( s_pCandidateTiming->objects[pFanout->Id].ancestor ==
                                                           s_pCandidateTiming->generation ) Queue.push_back(pFanout);
        }
    }

    // Adds the slack change of the root and of its immediate fanout boundary
    // to the score: one continuous term each for logic depth and geometric
    // wire, weighted by the integral of the criticality 1/(1+max(0,s)) over
    // the slack change (no buckets or hard cutoffs).
    bool EvaluateTiming()
    {
        if ( !s_pTiming->ready || s_pTiming->network != pNtk_ ||
             pRoot_->Id >= static_cast<int>(s_pTiming->nodes.size()) )
            return false;
        s_pCandidateTiming->Start(Abc_NtkObjNumMax(pNtk_));
        timingEntityState_.assign(entities_.size(), 0);
        timingEntityMemo_.resize(entities_.size());
        Pa_Arrival NewRoot;
        if ( !s_pSettings->exactTiming )
        {
            // Evaluate graph leaves and candidate core objects only. Exact
            // timing (below) explores moved-node ancestors and fanouts.
            if ( !TimingForEntityLocal(resultEntity_, &NewRoot) )
                return false;
        }
        else
        {
            PrepareTimingSeeds();
            if ( !TimingForEntity(resultEntity_, &NewRoot) )
                return false;
        }
        const Pa_TimingNode & OldRoot = s_pTiming->nodes[pRoot_->Id];
        auto RootRequiredAt = [&](double RootX, double RootY, bool SourceIsCi, int * pLogic, double * pWire) -> bool
        {
            *pLogic = ABC_INFINITY;
            *pWire = std::numeric_limits<double>::infinity();
            Abc_Obj_t * pFanout;
            int i;
            Abc_ObjForEachFanout(pRoot_, pFanout, i)
            {
                if ( pFanout->Id < 0 || pFanout->Id >= static_cast<int>(s_pTiming->nodes.size()) )
                    return false;
                const Pa_TimingNode & Fanout = s_pTiming->nodes[pFanout->Id];
                int Logic = Abc_ObjIsCo(pFanout) ? 0 : 1;
                double Wire = 0.0;
                if ( Abc_ObjIsNode(pFanout) && !SourceIsCi )
                {
                    double X, Y;
                    if ( !TimingPosition(pFanout, &X, &Y) )
                        return false;
                    Wire = std::hypot(RootX - X, RootY - Y);
                }
                if ( Fanout.requiredLogic != ABC_INFINITY )
                    *pLogic = std::min(*pLogic, Fanout.requiredLogic - Logic);
                if ( std::isfinite(Fanout.requiredWire) )
                    *pWire = std::min(*pWire, Fanout.requiredWire - Wire);
            }
            return true;
        };
        int OldRequiredLogic;
        double OldRequiredWire;
        if ( !RootRequiredAt(OldRoot.x, OldRoot.y, false, &OldRequiredLogic, &OldRequiredWire) )
            return false;
        double OldSlack = std::min(static_cast<double>(OldRequiredLogic - OldRoot.arrival.logic),
                                   (OldRequiredWire - OldRoot.arrival.wire) / s_pTiming->wireScale);
        int NewRequiredLogic;
        double NewRequiredWire;
        double RootX, RootY;
        if ( !TimingEntityPosition(resultEntity_, &RootX, &RootY) )
            return false;
        if ( !RootRequiredAt(RootX, RootY, TimingIsCi(pRoot_), &NewRequiredLogic, &NewRequiredWire) )
            return false;
        double NewSlack = std::min(static_cast<double>(NewRequiredLogic - NewRoot.logic),
                                   (NewRequiredWire - NewRoot.wire) / s_pTiming->wireScale);
        if ( !std::isfinite(OldSlack) || !std::isfinite(NewSlack) )
            return false;
        double OldLogicSlack = OldRequiredLogic == ABC_INFINITY
                                   ? std::numeric_limits<double>::infinity()
                                   : static_cast<double>(OldRequiredLogic - OldRoot.arrival.logic);
        double NewLogicSlack = NewRequiredLogic == ABC_INFINITY ? std::numeric_limits<double>::infinity()
                                                                : static_cast<double>(NewRequiredLogic - NewRoot.logic);
        double OldWireSlack = (OldRequiredWire - OldRoot.arrival.wire) / s_pTiming->wireScale;
        double NewWireSlack = (NewRequiredWire - NewRoot.wire) / s_pTiming->wireScale;
        double OldFanoutSlack = std::numeric_limits<double>::infinity();
        double NewFanoutSlack = std::numeric_limits<double>::infinity();
        bool HasFanoutSlack = false;
        Abc_Obj_t * pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout, i)
        {
            if ( pFanout->Id < 0 || pFanout->Id >= static_cast<int>(s_pTiming->nodes.size()) )
                continue;
            const Pa_TimingNode & FanoutTiming = s_pTiming->nodes[pFanout->Id];
            if ( FanoutTiming.requiredLogic == ABC_INFINITY &&
                 FanoutTiming.requiredWire == std::numeric_limits<double>::infinity() )
                continue;
            Pa_Arrival NewFanout;
            if ( s_pSettings->exactTiming )
            {
                s_pCandidateTiming->objects[pFanout->Id].affected = s_pCandidateTiming->generation;
                if ( !TimingForObject(pFanout, &NewFanout) )
                    return false;
            }
            else if ( Abc_ObjIsCo(pFanout) )
                NewFanout = NewRoot;
            else if ( Abc_ObjIsNode(pFanout) )
            {
                double FanoutX, FanoutY;
                if ( !TimingPosition(pFanout, &FanoutX, &FanoutY) )
                    continue;
                Abc_Obj_t * pFanin;
                int k;
                bool Complete = true;
                Abc_ObjForEachFanin(pFanout, pFanin, k)
                {
                    Pa_Arrival Input;
                    double InputX, InputY;
                    bool SourceIsCi;
                    if ( pFanin == pRoot_ )
                    {
                        Input = NewRoot;
                        InputX = RootX;
                        InputY = RootY;
                        SourceIsCi = TimingIsCi(pRoot_);
                    }
                    else
                    {
                        auto It = actualEntities_.find(pFanin);
                        if ( It != actualEntities_.end() &&
                             (entities_[It->second].movable || timingProduced_[It->second] ||
                              timingBoundary_[It->second]) )
                        {
                            if ( !TimingForEntityLocal(It->second, &Input) ||
                                 !TimingEntityPosition(It->second, &InputX, &InputY) )
                            {
                                Complete = false;
                                break;
                            }
                        }
                        else
                        {
                            if ( pFanin->Id < 0 || pFanin->Id >= static_cast<int>(s_pTiming->nodes.size()) ||
                                 !TimingPosition(pFanin, &InputX, &InputY) )
                            {
                                Complete = false;
                                break;
                            }
                            Input = s_pTiming->nodes[pFanin->Id].arrival;
                        }
                        SourceIsCi = Abc_ObjIsCi(pFanin);
                    }
                    double Wire = SourceIsCi ? 0.0 : std::hypot(InputX - FanoutX, InputY - FanoutY);
                    NewFanout.logic = std::max(NewFanout.logic, Input.logic + 1);
                    NewFanout.wire = std::max(NewFanout.wire, Input.wire + Wire);
                }
                if ( !Complete )
                    continue;
            }
            else
                continue;

            double OldLocalSlack =
                std::min(static_cast<double>(FanoutTiming.requiredLogic - FanoutTiming.arrival.logic),
                         (FanoutTiming.requiredWire - FanoutTiming.arrival.wire) / s_pTiming->wireScale);
            double NewLocalSlack = std::min(static_cast<double>(FanoutTiming.requiredLogic - NewFanout.logic),
                                            (FanoutTiming.requiredWire - NewFanout.wire) / s_pTiming->wireScale);
            if ( !std::isfinite(OldLocalSlack) || !std::isfinite(NewLocalSlack) )
                continue;
            OldFanoutSlack = std::min(OldFanoutSlack, OldLocalSlack);
            NewFanoutSlack = std::min(NewFanoutSlack, NewLocalSlack);
            HasFanoutSlack = true;
        }
        score_ += kTimingWeight * (Pa_SlackPotentialDelta(OldLogicSlack, NewLogicSlack) +
                                   Pa_SlackPotentialDelta(OldWireSlack, NewWireSlack));
        if ( HasFanoutSlack )
            score_ += kTimingWeight * Pa_SlackPotentialDelta(OldFanoutSlack, NewFanoutSlack);
        return std::isfinite(score_);
    }

    bool BuildClusters()
    {
        std::vector<Abc_Obj_t *> Removed(removed_.begin(), removed_.end());
        std::sort(Removed.begin(), Removed.end(), [](Abc_Obj_t * A, Abc_Obj_t * B) { return A->Id < B->Id; });
        for ( Abc_Obj_t * pObject : Removed )
        {
            double X, Y;
            if ( !Pa_ManReadObjectPosition(pNtk_, pObject, &X, &Y) )
                return false;
            auto It = std::find_if(clusters_.begin(), clusters_.end(), [X, Y](const Pa_Cluster & Cluster)
                                   { return std::fabs(Cluster.x - X) < 0.001 && std::fabs(Cluster.y - Y) < 0.001; });
            if ( It == clusters_.end() )
                clusters_.push_back(Pa_Cluster{X, Y, 1});
            else
                ++It->count;
        }
        return !clusters_.empty();
    }

    // Moves every new node to the cluster with the largest attraction
    // count / (distance^2 + 0.001), after the HPWL-optimal tree placement.
    void SnapVirtualNodesToClusters()
    {
        for ( int EntityId : virtualEntities_ )
        {
            Pa_Geometry & Geometry = entities_[EntityId].geometry;
            if ( densityPresent_[EntityId] )
                density_->Add(Geometry, -1.0);
            double BestForce = -1.0;
            const Pa_Cluster * Best = nullptr;
            for ( const Pa_Cluster & Cluster : clusters_ )
            {
                double Dx = Geometry.x - Cluster.x;
                double Dy = Geometry.y - Cluster.y;
                double Force = Cluster.count / (Dx * Dx + Dy * Dy + 0.001);
                if ( Force > BestForce )
                {
                    BestForce = Force;
                    Best = &Cluster;
                }
            }
            if ( Best )
            {
                Geometry.x = Best->x;
                Geometry.y = Best->y;
            }
            density_->Add(Geometry, 1.0);
            densityPresent_[EntityId] = 1;
        }
    }

    void CollectRemoved()
    {
        if ( s_pMffcCache->network == pNtk_ && s_pMffcCache->root == pRoot_ &&
             s_pMffcCache->version == s_pReadCache->version && s_pMffcCache->traversal == pNtk_->nTravIds )
        {
            removed_ = s_pMffcCache->removed;
            removedIds_ = s_pMffcCache->ids;
            return;
        }
        PaWorkspace::WorkspaceVector<Abc_Obj_t *> Stack;
        Stack.push_back(pRoot_);
        while ( !Stack.empty() )
        {
            Abc_Obj_t * pObject = Stack.back();
            Stack.pop_back();
            if ( !Abc_ObjIsNode(pObject) || !Abc_NodeIsTravIdCurrent(pObject) || !removed_.insert(pObject).second )
                continue;
            removedIds_.push_back(pObject->Id);
            Abc_Obj_t * pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) if ( Abc_ObjIsNode(pFanin) && Abc_NodeIsTravIdCurrent(pFanin) )
                Stack.push_back(pFanin);
        }
        {
            s_pMffcCache->network = pNtk_;
            s_pMffcCache->root = pRoot_;
            s_pMffcCache->version = s_pReadCache->version;
            s_pMffcCache->traversal = pNtk_->nTravIds;
            s_pMffcCache->removed = removed_;
            s_pMffcCache->ids = removedIds_;
        }
    }

    int AddActual(Abc_Obj_t * pObject)
    {
        pObject = Abc_ObjRegular(pObject);
        auto It = actualEntities_.find(pObject);
        if ( It != actualEntities_.end() )
            return It->second;
        Pa_Entity Entity;
        Entity.object = pObject;
        Entity.hasPoint = Pa_ReadObjectGeometry(pNtk_, pObject, &Entity.geometry.x, &Entity.geometry.y,
                                                &Entity.geometry.width, &Entity.geometry.densityHalfX,
                                                &Entity.geometry.densityHalfY, &Entity.geometry.densityScale) != 0;
        int Index = static_cast<int>(entities_.size());
        entities_.push_back(Entity);
        addedFanouts_.emplace_back();
        virtualInputs_.emplace_back();
        timingInputs_.emplace_back();
        timingProduced_.push_back(0);
        timingBoundary_.push_back(0);
        entityLevels_.push_back(static_cast<int>(pObject->Level));
        symbolicFanouts_.push_back(Abc_ObjFanoutNum(pObject));
        actualEntities_.emplace(pObject, Index);
        return Index;
    }

    int AddVirtual(int DecIndex, Pa_SymbolicLit Left, Pa_SymbolicLit Right)
    {
        Pa_Entity Entity;
        Entity.decIndex = DecIndex;
        Entity.virtualNode = true;
        Entity.hasPoint = true;
        Entity.geometry.width = Left.complement && Right.complement ? 2.0 : 3.0;
        const double SqrtTwo = std::sqrt(2.0);
        Entity.geometry.densityHalfX = std::max(0.5 * Entity.geometry.width, 0.5 * SqrtTwo * binSizeX_);
        Entity.geometry.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
        Entity.geometry.densityScale =
            Entity.geometry.width / (4.0 * Entity.geometry.densityHalfX * Entity.geometry.densityHalfY);
        double RootX = 0.5 * width_, RootY = 0.5 * height_;
        Pa_ManReadObjectPosition(pNtk_, pRoot_, &RootX, &RootY);
        Entity.geometry.x = Pa_Clamp(RootX, Entity.geometry.densityHalfX, width_ - Entity.geometry.densityHalfX);
        Entity.geometry.y = Pa_Clamp(RootY, Entity.geometry.densityHalfY, height_ - Entity.geometry.densityHalfY);
        int Index = static_cast<int>(entities_.size());
        entities_.push_back(Entity);
        addedFanouts_.emplace_back();
        virtualInputs_.emplace_back(Left, Right);
        timingInputs_.emplace_back(Left, Right);
        timingProduced_.push_back(1);
        timingBoundary_.push_back(0);
        entityLevels_.push_back(1 + std::max(entityLevels_[Left.entity], entityLevels_[Right.entity]));
        symbolicFanouts_.push_back(0);
        ++symbolicFanouts_[Left.entity];
        ++symbolicFanouts_[Right.entity];
        virtualEntities_.push_back(Index);
        return Index;
    }

    Pa_SymbolicLit ActualLiteral(Abc_Obj_t * pLiteral)
    {
        return Pa_SymbolicLit{AddActual(Abc_ObjRegular(pLiteral)), Abc_ObjIsComplement(pLiteral) != 0};
    }

    Pa_SymbolicLit ConstantLiteral(bool Value)
    {
        return Pa_SymbolicLit{AddActual(Abc_AigConst1(pNtk_)), !Value};
    }

    Pa_SymbolicLit SymbolicAnd(int DecIndex, Pa_SymbolicLit Left, Pa_SymbolicLit Right)
    {
        if ( Left.entity == Right.entity )
            return Left.complement == Right.complement ? Left : ConstantLiteral(false);
        int Const = AddActual(Abc_AigConst1(pNtk_));
        if ( Left.entity == Const )
            return Left.complement ? ConstantLiteral(false) : Right;
        if ( Right.entity == Const )
            return Right.complement ? ConstantLiteral(false) : Left;

        int Lit0 = 2 * Left.entity + Left.complement;
        int Lit1 = 2 * Right.entity + Right.complement;
        if ( Lit0 > Lit1 )
            std::swap(Lit0, Lit1);
        auto Key = std::make_pair(Lit0, Lit1);
        // ABC bypasses its structural hash table when either input has no
        // fanouts.  Track fanouts created by earlier symbolic ANDs, including
        // new nodes.  The most recently created virtual node is at the head
        // of the real hash bin and takes precedence over an older match.
        if ( symbolicFanouts_[Left.entity] > 0 && symbolicFanouts_[Right.entity] > 0 )
        {
            auto It = virtualHash_.find(Key);
            if ( It != virtualHash_.end() )
                return Pa_SymbolicLit{It->second, false};
            Abc_Obj_t * pLeft = entities_[Left.entity].object;
            Abc_Obj_t * pRight = entities_[Right.entity].object;
            if ( pLeft != nullptr && pRight != nullptr )
            {
                // A pre-existing input can have zero live fanouts but gain
                // one earlier in this virtual build.  ABC's lookup tests the
                // live count, so temporarily expose the simulated nonzero
                // count while querying the unchanged hash table.
                bool LiftLeft = Abc_ObjFanoutNum(pLeft) == 0;
                bool LiftRight = Abc_ObjFanoutNum(pRight) == 0;
                if ( LiftLeft )
                    ++pLeft->vFanouts.nSize;
                if ( LiftRight )
                    ++pRight->vFanouts.nSize;
                Abc_Obj_t * pFound =
                    Abc_AigAndLookup(static_cast<Abc_Aig_t *>(pNtk_->pManFunc), Abc_ObjNotCond(pLeft, Left.complement),
                                     Abc_ObjNotCond(pRight, Right.complement));
                if ( LiftRight )
                    --pRight->vFanouts.nSize;
                if ( LiftLeft )
                    --pLeft->vFanouts.nSize;
                if ( pFound != nullptr )
                {
                    if ( Abc_ObjRegular(pFound) == pRoot_ )
                    {
                        validBuild_ = false;
                        return Pa_SymbolicLit{};
                    }
                    Pa_SymbolicLit Result = ActualLiteral(pFound);
                    // Temporarily update every reused core object in candidate
                    // order. Retain the symbolic inputs that
                    // produced this reused AND so root timing can do the same
                    // without walking its potentially huge old fanin cone.
                    timingInputs_[Result.entity] = std::make_pair(Left, Right);
                    timingProduced_[Result.entity] = 1;
                    return Result;
                }
            }
        }
        int Entity = AddVirtual(DecIndex, Left, Right);
        virtualHash_[Key] = Entity;
        return Pa_SymbolicLit{Entity, false};
    }

    void BuildEntities()
    {
        validBuild_ = true;
        decToEntity_.assign(pGraph_->nSize, -1);
        decPhase_.assign(pGraph_->nSize, 0);
        Dec_Node_t * pNode;
        int i;
        Dec_GraphForEachLeaf(pGraph_, pNode, i)
        {
            if ( pNode->pFunc == nullptr || Abc_ObjRegular(static_cast<Abc_Obj_t *>(pNode->pFunc)) == pRoot_ )
            {
                validBuild_ = false;
                return;
            }
            Pa_SymbolicLit Literal = ActualLiteral(static_cast<Abc_Obj_t *>(pNode->pFunc));
            timingBoundary_[Literal.entity] = 1;
            decToEntity_[i] = Literal.entity;
            decPhase_[i] = Literal.complement;
        }
        Dec_GraphForEachNode(pGraph_, pNode, i)
        {
            int Child0 = pNode->eEdge0.Node;
            int Child1 = pNode->eEdge1.Node;
            if ( Child0 >= i || Child1 >= i || decToEntity_[Child0] < 0 || decToEntity_[Child1] < 0 )
            {
                validBuild_ = false;
                return;
            }
            Pa_SymbolicLit Left{decToEntity_[Child0], (pNode->eEdge0.fCompl ^ decPhase_[Child0]) != 0};
            Pa_SymbolicLit Right{decToEntity_[Child1], (pNode->eEdge1.fCompl ^ decPhase_[Child1]) != 0};
            Pa_SymbolicLit Result = SymbolicAnd(i, Left, Right);
            if ( !validBuild_ || Result.entity < 0 || entityLevels_[Result.entity] > levelMax_ )
            {
                validBuild_ = false;
                return;
            }
            decToEntity_[i] = Result.entity;
            decPhase_[i] = Result.complement;
        }
        if ( Dec_GraphIsConst(pGraph_) )
            resultEntity_ = AddActual(Abc_AigConst1(pNtk_));
        else
        {
            // Dec_GraphToNetwork() returns its last AND, rather than indexing
            // eRoot, for a nontrivial graph.  Accept only graphs for which
            // those two descriptions are identical.
            if ( pGraph_->eRoot.Node >= static_cast<unsigned>(decToEntity_.size()) ||
                 (pGraph_->nSize > pGraph_->nLeaves &&
                  pGraph_->eRoot.Node != static_cast<unsigned>(pGraph_->nSize - 1)) )
            {
                validBuild_ = false;
                return;
            }
            resultEntity_ = decToEntity_[pGraph_->eRoot.Node];
        }
        if ( resultEntity_ < 0 || entities_[resultEntity_].object == pRoot_ )
        {
            validBuild_ = false;
            return;
        }
        int ResultPhase = Dec_GraphIsConst(pGraph_) ? 0 : decPhase_[pGraph_->eRoot.Node];
        resultComplement_ = (ResultPhase ^ Dec_GraphIsComplement(pGraph_) ^ static_cast<int>(rootComplement_)) != 0;

        for ( int Parent : virtualEntities_ )
        {
            const auto & Inputs = virtualInputs_[Parent];
            addedFanouts_[Inputs.first.entity].push_back(Parent);
            addedFanouts_[Inputs.second.entity].push_back(Parent);
        }

        if ( resultEntity_ >= 0 )
        {
            Abc_Obj_t * pFanout;
            int k;
            Abc_ObjForEachFanout(pRoot_, pFanout, k) if ( Abc_ObjIsNode(pFanout) )
            {
                int Fanout = AddActual(pFanout);
                if ( entities_[Fanout].hasPoint )
                    addedFanouts_[resultEntity_].push_back(Fanout);
            }
        }
    }

    void ComputeRemovedAfterMaterialization()
    {
        // New ANDs are created before ABC replaces the old root.  Every old
        // MFFC node used by a new AND, or used as the replacement result,
        // gains a surviving fanout.  Its old MFFC fanin cone survives too.
        Pa_ObjectSet Retained;
        std::vector<Abc_Obj_t *> Stack;
        for ( int NewEntity : virtualEntities_ )
        {
            const auto & Inputs = virtualInputs_[NewEntity];
            for ( int Child : {Inputs.first.entity, Inputs.second.entity} )
            {
                Abc_Obj_t * pChild = entities_[Child].object;
                if ( pChild != nullptr && removed_.count(pChild) )
                    Stack.push_back(pChild);
            }
        }
        Abc_Obj_t * pResult = entities_[resultEntity_].object;
        if ( pResult != nullptr && removed_.count(pResult) )
            Stack.push_back(pResult);
        while ( !Stack.empty() )
        {
            Abc_Obj_t * pObject = Stack.back();
            Stack.pop_back();
            if ( !Retained.insert(pObject).second )
                continue;
            Abc_Obj_t * pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) if ( removed_.count(Abc_ObjRegular(pFanin)) )
                Stack.push_back(Abc_ObjRegular(pFanin));
        }
        for ( Abc_Obj_t * pObject : Retained )
            removed_.erase(pObject);
        // Pointer-hash iteration changes with allocation/ASLR. Numeric sums,
        // density updates and placement staging must use stable object IDs.
        orderedRemoved_.assign(removed_.begin(), removed_.end());
        std::sort(orderedRemoved_.begin(), orderedRemoved_.end(),
                  [](Abc_Obj_t * a, Abc_Obj_t * b) { return a->Id < b->Id; });
        removedIds_.clear();
        for ( Abc_Obj_t * pObject : orderedRemoved_ )
            removedIds_.push_back(pObject->Id);
        actualGain_ = static_cast<int>(removed_.size()) - VirtualCount();
        if ( !removed_.count(pRoot_) || (actualGain_ < -0) )
            validBuild_ = false;
    }

    // Each fixed-pin bounding box is a lower bound on that net's HPWL,
    // independently of placement/density constraints. Frozen reused pins add
    // further fixed terminals for the estimator's anchored component.

    double AreaDeltaBeforePlacement() const
    {
        double delta = 0;
        for ( auto * v : orderedRemoved_ )
        {
            double width;
            if ( !Pa_ReadObjectGeometry(pNtk_, v, nullptr, nullptr, &width, nullptr, nullptr, nullptr) )
                return -INFINITY;
            delta -= width;
        }
        for ( int v : virtualEntities_ )
            delta += entities_[v].geometry.width;
        Abc_Obj_t * fanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, fanout, i)
        {
            if ( !Abc_ObjIsNode(fanout) )
                continue;
            double width;
            if ( !Pa_ReadObjectGeometry(pNtk_, fanout, nullptr, nullptr, &width, nullptr, nullptr, nullptr) )
                return -INFINITY;
            int index = Abc_ObjFanin0(fanout) == pRoot_ ? 0 : Abc_ObjFanin1(fanout) == pRoot_ ? 1 : -1;
            if ( index < 0 )
                return -INFINITY;
            bool c0 = Abc_ObjFaninC0(fanout), c1 = Abc_ObjFaninC1(fanout);
            if ( index == 0 )
                c0 ^= resultComplement_;
            else
                c1 ^= resultComplement_;
            delta += (c0 && c1 ? 2.0 : 3.0) - width;
        }
        return delta;
    }

    void BuildMovables()
    {
        std::vector<unsigned char> seenFlags((entities_.size()));
        auto first = [&](int id)
        {
            bool fresh = !seenFlags[id];
            seenFlags[id] = 1;
            return fresh;
        };
        for ( int i = pGraph_->nLeaves; i < pGraph_->nSize; i++ )
        {
            int Entity = decToEntity_[i];
            if ( Entity < 0 || !first(Entity) )
                continue;
            Abc_Obj_t * pObject = entities_[Entity].object;
            if ( entities_[Entity].hasPoint && (entities_[Entity].virtualNode || !removed_.count(pObject)) )
            {
                entities_[Entity].movable = true;
                movableEntities_.push_back(Entity);
            }
        }
        if ( resultEntity_ >= 0 && first(resultEntity_) && entities_[resultEntity_].hasPoint &&
             !removed_.count(entities_[resultEntity_].object) )
        {
            entities_[resultEntity_].movable = true;
            movableEntities_.push_back(resultEntity_);
        }
    }

    int VirtualCount() const
    {
        return static_cast<int>(virtualEntities_.size());
    }

    bool HasDownstreamCascade() const
    {
        // Abc_AigReplace updates each root fanout in place unless replacing
        // the root makes that fanout structurally hash to an existing node.
        // In the latter case, replacement propagates beyond the candidate
        // boundary and invalidates this plan's exact affected-net delta.
        // Reject such a candidate before it mutates the live AIG.
        if ( resultEntity_ < 0 || entities_[resultEntity_].virtualNode || entities_[resultEntity_].object == nullptr )
            return false;
        Abc_Obj_t * pReplacement = Abc_ObjNotCond(entities_[resultEntity_].object, resultComplement_);
        Abc_Aig_t * pAig = static_cast<Abc_Aig_t *>(pNtk_->pManFunc);
        std::set<std::pair<int, int>> UpdatedFanoutKeys;
        Abc_Obj_t * pFanout;
        int k;
        Abc_ObjForEachFanout(pRoot_, pFanout, k)
        {
            if ( !Abc_ObjIsNode(pFanout) )
                continue;
            int FaninIndex = Vec_IntFind(&pFanout->vFanins, pRoot_->Id);
            if ( FaninIndex < 0 )
                return true;
            Abc_Obj_t * pChangedFanin = Abc_ObjNotCond(pReplacement, Abc_ObjFaninC(pFanout, FaninIndex));
            Abc_Obj_t * pOtherFanin = Abc_ObjChild(pFanout, FaninIndex ^ 1);
            Abc_Obj_t * pExisting = Abc_AigAndLookup(pAig, pChangedFanin, pOtherFanin);
            if ( pExisting != nullptr && Abc_ObjRegular(pExisting) != pFanout )
                return true;
            int Key0 = 2 * Abc_ObjRegular(pChangedFanin)->Id + Abc_ObjIsComplement(pChangedFanin);
            int Key1 = 2 * Abc_ObjRegular(pOtherFanin)->Id + Abc_ObjIsComplement(pOtherFanin);
            if ( Key0 > Key1 )
                std::swap(Key0, Key1);
            if ( !UpdatedFanoutKeys.emplace(Key0, Key1).second )
                return true;
            auto First = actualEntities_.find(Abc_ObjRegular(pChangedFanin));
            auto Second = actualEntities_.find(Abc_ObjRegular(pOtherFanin));
            if ( First != actualEntities_.end() && Second != actualEntities_.end() )
            {
                int Lit0 = 2 * First->second + Abc_ObjIsComplement(pChangedFanin);
                int Lit1 = 2 * Second->second + Abc_ObjIsComplement(pOtherFanin);
                if ( Lit0 > Lit1 )
                    std::swap(Lit0, Lit1);
                if ( virtualHash_.count(std::make_pair(Lit0, Lit1)) )
                    return true;
            }
        }
        return false;
    }

    template <class V> static void SortUnique(V & Values)
    {
        std::sort(Values.begin(), Values.end());
        Values.erase(std::unique(Values.begin(), Values.end()), Values.end());
    }

    static bool IsModeledDriver(Abc_Obj_t * pObject)
    {
        return pObject != nullptr && (Abc_ObjIsNode(pObject) || Abc_ObjIsCi(pObject));
    }

    double CurrentNetHpwl(Abc_Obj_t * pDriver) const
    {
        // Acquire the entry again when storing: geometry reads can grow the
        // ID-indexed array while traversing a driver's newer fanouts.
        if ( s_pReadCache->Get(pDriver->Id).hpwlStamp == s_pReadCache->version )
            return s_pReadCache->Get(pDriver->Id).hpwl;
        double MinX = 0.0, MaxX = 0.0, MinY = 0.0, MaxY = 0.0;
        bool Found = false;
        auto Add = [&](Abc_Obj_t * Object)
        {
            double X, Y;
            if ( !Pa_ReadObjectGeometry(pNtk_, Object, &X, &Y, nullptr, nullptr, nullptr, nullptr) )
                return;
            if ( !Found )
            {
                MinX = MaxX = X;
                MinY = MaxY = Y;
                Found = true;
            }
            else
            {
                MinX = std::min(MinX, X);
                MaxX = std::max(MaxX, X);
                MinY = std::min(MinY, Y);
                MaxY = std::max(MaxY, Y);
            }
        };
        Add(pDriver);
        Abc_Obj_t * Fanout;
        int k;
        Abc_ObjForEachFanout(pDriver, Fanout, k) if ( Abc_ObjIsNode(Fanout) ) Add(Fanout);
        auto & C = s_pReadCache->Get(pDriver->Id);
        C.hpwl = Found ? MaxX - MinX + MaxY - MinY : 0.0;
        C.hpwlStamp = s_pReadCache->version;
        return C.hpwl;
    }

    void AddPin(Pa_LocalNet & Net, int Entity)
    {
        if ( Entity < 0 || Entity >= static_cast<int>(entities_.size()) || !entities_[Entity].hasPoint )
            return;
        if ( entities_[Entity].movable )
            Net.pins.push_back(Entity);
        else
            Net.AddFixed(entities_[Entity].geometry.x, entities_[Entity].geometry.y);
    }

    void AddNetFast(Pa_LocalNet Net)
    {
        SortUnique(Net.pins);
        if ( Net.pins.size() + Net.fixedCount >= 2 )
            nets_.push_back(std::move(Net));
    }

    void BuildNetsFast()
    {
        // A is a set of affected DRIVER NETS, not a set of removed nodes.
        // A surviving boundary driver's fanout pins can change even though
        // the driver itself is present before and after.  The post-edit A'
        // consists of these surviving drivers plus the virtual new drivers.
        // Commit-time identity and boundary checks ensure that every net
        // outside A/A' has identical pins and fixed coordinates.
        std::vector<Abc_Obj_t *> OrderedDrivers;
        OrderedDrivers.reserve(3 * orderedRemoved_.size() + 2 * virtualEntities_.size() + 3 * movableEntities_.size() +
                               1);
        for ( Abc_Obj_t * pRemoved : orderedRemoved_ )
        {
            OrderedDrivers.push_back(pRemoved);
            Abc_Obj_t * pFanin;
            int k;
            Abc_ObjForEachFanin(pRemoved, pFanin, k) OrderedDrivers.push_back(Abc_ObjRegular(pFanin));
        }
        for ( int Entity : virtualEntities_ )
        {
            const auto & Inputs = virtualInputs_[Entity];
            int Children[2] = {Inputs.first.entity, Inputs.second.entity};
            for ( int Child : Children )
                if ( Child >= 0 && entities_[Child].object )
                    OrderedDrivers.push_back(entities_[Child].object);
        }
        for ( int Entity : movableEntities_ )
        {
            Abc_Obj_t * pObject = entities_[Entity].object;
            if ( pObject == nullptr )
                continue;
            OrderedDrivers.push_back(pObject);
            Abc_Obj_t * pFanin;
            int k;
            Abc_ObjForEachFanin(pObject, pFanin, k) OrderedDrivers.push_back(Abc_ObjRegular(pFanin));
        }
        if ( resultEntity_ >= 0 && entities_[resultEntity_].object )
            OrderedDrivers.push_back(entities_[resultEntity_].object);

        std::sort(OrderedDrivers.begin(), OrderedDrivers.end(),
                  [](Abc_Obj_t * a, Abc_Obj_t * b) { return a->Id < b->Id; });
        OrderedDrivers.erase(std::unique(OrderedDrivers.begin(), OrderedDrivers.end()), OrderedDrivers.end());

        for ( Abc_Obj_t * pDriver : OrderedDrivers )
            if ( IsModeledDriver(pDriver) )
                hpwlSaved_ += CurrentNetHpwl(pDriver);

        for ( Abc_Obj_t * pDriver : OrderedDrivers )
        {
            if ( removed_.count(pDriver) || !IsModeledDriver(pDriver) )
                continue;
            int Driver = AddActual(pDriver);
            Pa_LocalNet Net;
            AddPin(Net, Driver);
            Abc_Obj_t * pFanout;
            int k;
            Abc_ObjForEachFanout(pDriver, pFanout, k)
            {
                if ( !Abc_ObjIsNode(pFanout) || removed_.count(pFanout) )
                    continue;
                auto It = actualEntities_.find(pFanout);
                if ( It != actualEntities_.end() )
                    AddPin(Net, It->second);
                else
                {
                    double X, Y;
                    if ( Pa_ReadObjectGeometry(pNtk_, pFanout, &X, &Y, nullptr, nullptr, nullptr, nullptr) )
                        Net.AddFixed(X, Y);
                }
            }
            for ( int Fanout : addedFanouts_[Driver] )
                AddPin(Net, Fanout);
            AddNetFast(std::move(Net));
        }

        for ( int Driver : virtualEntities_ )
        {
            Pa_LocalNet Net;
            AddPin(Net, Driver);
            for ( int Fanout : addedFanouts_[Driver] )
                AddPin(Net, Fanout);
            AddNetFast(std::move(Net));
        }

        incidentNets_.assign(entities_.size(), {});
        for ( int Net = 0; Net < static_cast<int>(nets_.size()); ++Net )
            for ( int Pin : nets_[Net].pins )
                if ( entities_[Pin].movable )
                    incidentNets_[Pin].push_back(Net);
    }

    void InitializeDensity()
    {
        densityPresent_.assign(entities_.size(), 0);
        for ( Abc_Obj_t * pRemoved : orderedRemoved_ )
        {
            Pa_Geometry Geometry;
            if ( Pa_ReadObjectGeometry(pNtk_, pRemoved, &Geometry.x, &Geometry.y, &Geometry.width,
                                       &Geometry.densityHalfX, &Geometry.densityHalfY, &Geometry.densityScale) )
            {
                density_->Add(Geometry, -1.0);
            }
            else
                validBuild_ = false;
        }
        for ( int Entity : movableEntities_ )
            if ( !entities_[Entity].virtualNode )
                density_->Add(entities_[Entity].geometry, -1.0);
        Abc_Obj_t * pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout, i)
        {
            if ( !Abc_ObjIsNode(pFanout) )
                continue;
            Pa_Geometry OldGeometry;
            if ( !Pa_ReadObjectGeometry(pNtk_, pFanout, &OldGeometry.x, &OldGeometry.y, &OldGeometry.width,
                                        &OldGeometry.densityHalfX, &OldGeometry.densityHalfY,
                                        &OldGeometry.densityScale) )
            {
                validBuild_ = false;
                continue;
            }
            int FaninIndex = Abc_ObjFanin0(pFanout) == pRoot_ ? 0 : Abc_ObjFanin1(pFanout) == pRoot_ ? 1 : -1;
            if ( FaninIndex < 0 )
            {
                validBuild_ = false;
                continue;
            }
            bool Compl0 = Abc_ObjFaninC0(pFanout);
            bool Compl1 = Abc_ObjFaninC1(pFanout);
            if ( FaninIndex == 0 )
                Compl0 ^= resultComplement_;
            else
                Compl1 ^= resultComplement_;
            double NewWidth = Compl0 && Compl1 ? 2.0 : 3.0;
            if ( Pa_AlmostEqual(NewWidth, OldGeometry.width) )
                continue;
            Pa_Geometry NewGeometry = OldGeometry;
            NewGeometry.width = NewWidth;
            const double SqrtTwo = std::sqrt(2.0);
            NewGeometry.densityHalfX = std::max(0.5 * NewWidth, 0.5 * SqrtTwo * binSizeX_);
            NewGeometry.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
            NewGeometry.densityScale = NewWidth / (4.0 * NewGeometry.densityHalfX * NewGeometry.densityHalfY);
            auto It = actualEntities_.find(pFanout);
            if ( It != actualEntities_.end() && entities_[It->second].movable )
                entities_[It->second].geometry = NewGeometry;
            else
            {
                density_->Add(OldGeometry, -1.0);
                density_->Add(NewGeometry, 1.0);
            }
        }
    }

    void ClampRectangle(int Entity, Pa_Rectangle * pRectangle) const
    {
        const Pa_Geometry & Geometry = entities_[Entity].geometry;
        pRectangle->lowX = Pa_Clamp(pRectangle->lowX, Geometry.densityHalfX, width_ - Geometry.densityHalfX);
        pRectangle->highX = Pa_Clamp(pRectangle->highX, Geometry.densityHalfX, width_ - Geometry.densityHalfX);
        pRectangle->lowY = Pa_Clamp(pRectangle->lowY, Geometry.densityHalfY, height_ - Geometry.densityHalfY);
        pRectangle->highY = Pa_Clamp(pRectangle->highY, Geometry.densityHalfY, height_ - Geometry.densityHalfY);
        if ( pRectangle->lowX > pRectangle->highX )
            std::swap(pRectangle->lowX, pRectangle->highX);
        if ( pRectangle->lowY > pRectangle->highY )
            std::swap(pRectangle->lowY, pRectangle->highY);
    }

    Pa_Rectangle PropagatedRectangle(int Entity, const std::vector<Pa_Rectangle> & Regions,
                                     const std::vector<unsigned char> * pAssigned) const
    {
        PaWorkspace::Scratch<double, 16> xs((2 * incidentNets_[Entity].size())), ys((2 * incidentNets_[Entity].size()));
        size_t used = 0;
        for ( int NetIndex : incidentNets_[Entity] )
        {
            const Pa_LocalNet & Net = nets_[NetIndex];
            bool Found = Net.fixedCount > 0;
            double MinX = Found ? Net.fixedMinX : std::numeric_limits<double>::max();
            double MaxX = Found ? Net.fixedMaxX : std::numeric_limits<double>::lowest();
            double MinY = Found ? Net.fixedMinY : std::numeric_limits<double>::max();
            double MaxY = Found ? Net.fixedMaxY : std::numeric_limits<double>::lowest();
            for ( int Pin : Net.pins )
            {
                if ( Pin == Entity )
                    continue;
                const Pa_Entity & Other = entities_[Pin];
                if ( !Other.movable || (pAssigned != nullptr && (*pAssigned)[Pin]) )
                {
                    MinX = std::min(MinX, Other.geometry.x);
                    MaxX = std::max(MaxX, Other.geometry.x);
                    MinY = std::min(MinY, Other.geometry.y);
                    MaxY = std::max(MaxY, Other.geometry.y);
                    Found = true;
                }
                else if ( Regions[Pin].valid )
                {
                    MinX = std::min(MinX, Regions[Pin].lowX);
                    MaxX = std::max(MaxX, Regions[Pin].highX);
                    MinY = std::min(MinY, Regions[Pin].lowY);
                    MaxY = std::max(MaxY, Regions[Pin].highY);
                    Found = true;
                }
            }
            if ( Found )
            {
                {
                    xs[used] = MinX;
                    ys[used++] = MinY;
                    xs[used] = MaxX;
                    ys[used++] = MaxY;
                }
            }
        }
        Pa_Rectangle Result;
        if ( used == 0 )
            return Result;
        std::pair<double, double> XRegion, YRegion;
        {
            std::sort(xs.data(), xs.data() + used);
            std::sort(ys.data(), ys.data() + used);
            XRegion = {xs[used / 2 - 1], xs[used / 2]};
            YRegion = {ys[used / 2 - 1], ys[used / 2]};
        }
        Result.lowX = XRegion.first;
        Result.highX = XRegion.second;
        Result.lowY = YRegion.first;
        Result.highY = YRegion.second;
        Result.valid = true;
        ClampRectangle(Entity, &Result);
        return Result;
    }

    struct RegionSamples
    {
        std::array<double, kRegionDivisions + 1> values;
        int count = 0;
    };

    static RegionSamples Samples(double Low, double High)
    {
        RegionSamples Result;
        if ( Pa_AlmostEqual(Low, High) )
        {
            Result.values[Result.count++] = Low;
            return Result;
        }
        double Step = (High - Low) / kRegionDivisions;
        int Count = kRegionDivisions;
        if ( Step < kMinimumRegionStep )
        {
            Step = kMinimumRegionStep;
            Count = static_cast<int>((High - Low) / kMinimumRegionStep);
        }
        for ( int i = 0; i <= Count; ++i )
            Result.values[Result.count++] = Low + i * Step;
        return Result;
    }

    double PlaceInRectangle(int Entity, const Pa_Rectangle & Rectangle)
    {
        Pa_Geometry & Geometry = entities_[Entity].geometry;
        double OldX = Geometry.x, OldY = Geometry.y;
        if ( densityPresent_[Entity] )
            density_->Add(Geometry, -1.0);
        RegionSamples XSamples = Samples(Rectangle.lowX, Rectangle.highX);
        RegionSamples YSamples = Samples(Rectangle.lowY, Rectangle.highY);
        std::array<Pa_DensityWorkspace::AxisFootprint, kRegionDivisions + 1> XFootprints, YFootprints;
        for ( int i = 0; i < XSamples.count; ++i )
            XFootprints[i] = density_->PrepareAxis(XSamples.values[i], Geometry.densityHalfX, true);
        for ( int i = 0; i < YSamples.count; ++i )
            YFootprints[i] = density_->PrepareAxis(YSamples.values[i], Geometry.densityHalfY, false);
        double CenterX = 0.5 * (Rectangle.lowX + Rectangle.highX);
        double CenterY = 0.5 * (Rectangle.lowY + Rectangle.highY);
        double BestX = CenterX, BestY = CenterY;
        double BestDensity = std::numeric_limits<double>::max();
        double BestCenterDistance = std::numeric_limits<double>::max();
        for ( int i = 0; i < XSamples.count; ++i )
            for ( int j = 0; j < YSamples.count; ++j )
            {
                double X = XSamples.values[i], Y = YSamples.values[j];
                double Density = (density_->EvaluateAddition(Geometry, XFootprints[i], YFootprints[j]));
                double CenterDistance = (X - CenterX) * (X - CenterX) + (Y - CenterY) * (Y - CenterY);
                bool Better =
                    Pa_AlmostLess(Density, BestDensity) ||
                    (Pa_AlmostEqual(Density, BestDensity) && Pa_AlmostLess(CenterDistance, BestCenterDistance));
                if ( Better )
                {
                    BestX = X;
                    BestY = Y;
                    BestDensity = Density;
                    BestCenterDistance = CenterDistance;
                }
            }
        Geometry.x = BestX;
        Geometry.y = BestY;
        density_->Add(Geometry, 1.0);
        densityPresent_[Entity] = 1;
        return std::fabs(OldX - BestX) + std::fabs(OldY - BestY);
    }

    void SeedFromPropagatedRegions()
    {
        // The forward pass propagates HPWL-optimal rectangles from candidate
        // leaves toward the root.  The reverse pass fixes one density-aware
        // point per rectangle while using already fixed fanouts as anchors.
        // This is exact for each tree elimination step.  Reconvergent DAGs
        // can expose more than one virtual pin on a net, so the seed is a
        // heuristic for those cases; LocalHpwl measures its actual cost.
        std::vector<Pa_Rectangle> Regions(entities_.size());
        for ( int Entity : movableEntities_ )
            Regions[Entity] = PropagatedRectangle(Entity, Regions, nullptr);

        std::vector<unsigned char> Assigned(entities_.size(), 0);
        for ( auto It = movableEntities_.rbegin(); It != movableEntities_.rend(); ++It )
        {
            int Entity = *It;
            Pa_Rectangle Region = PropagatedRectangle(Entity, Regions, &Assigned);
            if ( !Region.valid )
                Region = Regions[Entity];
            if ( !Region.valid )
            {
                const Pa_Geometry & Geometry = entities_[Entity].geometry;
                Region = Pa_Rectangle{Geometry.x, Geometry.x, Geometry.y, Geometry.y, true};
                ClampRectangle(Entity, &Region);
            }
            PlaceInRectangle(Entity, Region);
            Assigned[Entity] = 1;
        }
    }

    // Preserve freed physical capacity when a wire-optimal seed is too dense.
    // Candidate-private geometry only; there is no graph rollback or global solve.

    void RepairCapacity(double area, double overflow)
    {
        std::vector<Pa_Geometry> sites;
        for ( auto * v : orderedRemoved_ )
        {
            Pa_Geometry g;
            if ( Pa_ReadObjectGeometry(pNtk_, v, &g.x, &g.y, &g.width, &g.densityHalfX, &g.densityHalfY,
                                       &g.densityScale) )
                sites.push_back(g);
        }
        std::vector<std::pair<double, double>> desired(entities_.size());
        for ( int id : movableEntities_ )
        {
            auto & g = entities_[id].geometry;
            desired[id] = {g.x, g.y};
            if ( densityPresent_[id] )
                density_->Add(g, -1.);
            densityPresent_[id] = 0;
        }
        // Reused objects retain their original sites; new objects inherit the
        // closest sufficiently large removed site, with deterministic ties.
        for ( int id : movableEntities_ )
            if ( !entities_[id].virtualNode )
            {
                auto & e = entities_[id];
                Pa_ManReadObjectPosition(pNtk_, e.object, &e.geometry.x, &e.geometry.y);
                // A previous polarity change can widen a reused cell at
                // the canvas edge. Score the same clipped coordinates that
                // WriteObjectPosition will materialize, including density.
                e.geometry.x = Pa_Clamp(e.geometry.x, 0.5 * e.geometry.width, width_ - 0.5 * e.geometry.width);
                e.geometry.y = Pa_Clamp(e.geometry.y, 0.5, height_ - 0.5);
                density_->Add(e.geometry, 1.);
                densityPresent_[id] = 1;
            }
        std::vector<int> order(virtualEntities_.begin(), virtualEntities_.end());
        std::stable_sort(order.begin(), order.end(),
                         [&](int a, int b) { return entities_[a].geometry.width > entities_[b].geometry.width; });
        std::vector<unsigned char> used(sites.size());
        for ( int id : order )
        {
            auto & g = entities_[id].geometry;
            int best = -1;
            double bestCost = INFINITY;
            for ( size_t i = 0; i < sites.size(); ++i )
                if ( !used[i] )
                {
                    double cost = std::abs(sites[i].x - desired[id].first) + std::abs(sites[i].y - desired[id].second);
                    if ( sites[i].width + 1e-9 < g.width )
                        cost += 1000 * (width_ + height_);
                    if ( cost < bestCost )
                    {
                        best = int(i);
                        bestCost = cost;
                    }
                }
            if ( best >= 0 )
            {
                used[best] = 1;
                g.x = sites[best].x;
                g.y = sites[best].y;
            }
            g.x = Pa_Clamp(g.x, g.densityHalfX, width_ - g.densityHalfX);
            g.y = Pa_Clamp(g.y, g.densityHalfY, height_ - g.densityHalfY);
            density_->Add(g, 1.);
            densityPresent_[id] = 1;
        }

        const double limit = std::max(.099, overflow);
        auto excess = [&]()
        {
            return std::max(0.,
                            overflow * area + density_->OverflowDelta() - limit * (area + density_->ExactAreaDelta()));
        };
        // Coordinate search first restores feasibility, then minimizes actual
        // affected-net HPWL without spending more overflow than the limit.
        const int sweeps = std::max(1, std::min(4, 1));
        for ( int sweep = 0; sweep < sweeps; ++sweep )
            for ( auto it = movableEntities_.rbegin(); it != movableEntities_.rend(); ++it )
            {
                int id = *it;
                auto & g = entities_[id].geometry;
                double x = g.x, y = g.y, bx = x, by = y, be = excess(), bh = LocalHpwl();
                const double dx = binSizeX_ * .5, dy = binSizeY_ * .5;
                std::vector<std::pair<double, double>> trials{
                    {desired[id].first, desired[id].second},
                    {(x + desired[id].first) * .5, (y + desired[id].second) * .5},
                    {x - dx, y},
                    {x + dx, y},
                    {x, y - dy},
                    {x, y + dy}};
                for ( const auto & site : sites )
                    trials.emplace_back(site.x, site.y);
                density_->Add(g, -1.);
                for ( auto t : trials )
                {
                    g.x = Pa_Clamp(t.first, g.densityHalfX, width_ - g.densityHalfX);
                    g.y = Pa_Clamp(t.second, g.densityHalfY, height_ - g.densityHalfY);
                    density_->Add(g, 1.);
                    double e = excess(), h = LocalHpwl();
                    if ( e < be - 1e-9 || (e <= be + 1e-9 && h < bh - 1e-9) )
                    {
                        be = e;
                        bh = h;
                        bx = g.x;
                        by = g.y;
                    }
                    density_->Add(g, -1.);
                }
                g.x = bx;
                g.y = by;
                density_->Add(g, 1.);
            }
    }

    double LocalHpwl() const
    {
        double Result = 0.0;
        for ( const Pa_LocalNet & Net : nets_ )
        {
            double MinX = Net.fixedMinX, MaxX = Net.fixedMaxX;
            double MinY = Net.fixedMinY, MaxY = Net.fixedMaxY;
            bool Found = Net.fixedCount > 0;
            for ( int Pin : Net.pins )
            {
                const Pa_Geometry & Geometry = entities_[Pin].geometry;
                if ( !Found )
                {
                    MinX = MaxX = Geometry.x;
                    MinY = MaxY = Geometry.y;
                    Found = true;
                }
                else
                {
                    MinX = std::min(MinX, Geometry.x);
                    MaxX = std::max(MaxX, Geometry.x);
                    MinY = std::min(MinY, Geometry.y);
                    MaxY = std::max(MaxY, Geometry.y);
                }
            }
            if ( Found )
                Result += MaxX - MinX + MaxY - MinY;
        }
        return Result;
    }

    Abc_Obj_t * pRoot_ = nullptr;
    Abc_Ntk_t * pNtk_ = nullptr;
    Dec_Graph_t * pGraph_ = nullptr;
    int nNodesSaved_ = 0;
    int levelMax_ = ABC_INFINITY;
    int actualGain_ = 0;
    double width_ = 0.0;
    double height_ = 0.0;
    int bins_ = 0;
    double binSizeX_ = 0.0;
    double binSizeY_ = 0.0;
    double hpwlScale_ = 1.0;
    double hpwlSaved_ = 0.0;
    double hpwlAdded_ = 0.0;

    double score_ = -std::numeric_limits<double>::infinity();
    bool validBuild_ = false;
    bool valid_ = false;

    bool rootComplement_ = false;
    bool resultComplement_ = false;
    int resultEntity_ = -1;
    Pa_ObjectSet removed_;
    PaWorkspace::WorkspaceVector<Abc_Obj_t *> orderedRemoved_;
    PaWorkspace::WorkspaceVector<int> removedIds_;
    Pa_EntityIndex actualEntities_;
    PaWorkspace::WorkspaceVector<Pa_Entity> entities_;
    PaWorkspace::WorkspaceVector<int> decToEntity_;
    PaWorkspace::WorkspaceVector<unsigned char> decPhase_;
    PaWorkspace::WorkspaceVector<int> entityLevels_;
    PaWorkspace::WorkspaceVector<int> symbolicFanouts_;
    PaWorkspace::WorkspaceVector<std::pair<Pa_SymbolicLit, Pa_SymbolicLit>> virtualInputs_;
    PaWorkspace::WorkspaceVector<std::pair<Pa_SymbolicLit, Pa_SymbolicLit>> timingInputs_;
    PaWorkspace::WorkspaceVector<unsigned char> timingProduced_;
    PaWorkspace::WorkspaceVector<unsigned char> timingBoundary_;
    std::map<std::pair<int, int>, int> virtualHash_;
    PaWorkspace::WorkspaceVector<int> virtualEntities_;
    std::vector<Pa_Cluster> clusters_;
    PaWorkspace::WorkspaceVector<int> movableEntities_;
    PaWorkspace::WorkspaceVector<PaWorkspace::IntList> addedFanouts_;
    PaWorkspace::WorkspaceVector<Pa_LocalNet> nets_;
    PaWorkspace::WorkspaceVector<PaWorkspace::IntList> incidentNets_;
    PaWorkspace::WorkspaceVector<unsigned char> densityPresent_;
    std::unique_ptr<Pa_DensityWorkspace> density_;
    PaWorkspace::WorkspaceVector<unsigned char> timingEntityState_;
    PaWorkspace::WorkspaceVector<Pa_Arrival> timingEntityMemo_;
};

/**Function*************************************************************

  Synopsis    [Marks the MFFC of the root bounded by the leaves and returns its size.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pa_MarkMffc(Abc_Obj_t * pRoot, Vec_Ptr_t * vLeaves)
{
    Abc_Obj_t * pLeaf;
    int i;
    Vec_PtrForEachEntry(Abc_Obj_t *, vLeaves, pLeaf, i) Abc_ObjRegular(pLeaf)->vFanouts.nSize++;
    Abc_NtkIncrementTravId(pRoot->pNtk);
    int Saved = Abc_NodeMffcLabelAig(pRoot);
    Vec_PtrForEachEntry(Abc_Obj_t *, vLeaves, pLeaf, i) Abc_ObjRegular(pLeaf)->vFanouts.nSize--;
    return Saved;
}

struct Pa_EvalState
{
    Pa_EvalSettings settings;
    Pa_ReadCache readCache;
    Pa_CandidateTimingScratch candidateTiming;
    Pa_TimingCache timing;
    Pa_MffcCache mffcCache;
};
void * Pa_EvalStateAlloc()
{
    return new Pa_EvalState();
}
void Pa_EvalStateFree(void * p)
{
    delete static_cast<Pa_EvalState *>(p);
}

/**Function*************************************************************

  Synopsis    [Binds the evaluator state of the current frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_EvalBind()
{
    auto * State = static_cast<Pa_EvalState *>(Pa_FrameState(PA_STATE_EVAL, Pa_EvalStateAlloc, Pa_EvalStateFree));
    s_pSettings = &State->settings;
    s_pReadCache = &State->readCache;
    s_pCandidateTiming = &State->candidateTiming;
    s_pTiming = &State->timing;
    s_pMffcCache = &State->mffcCache;
}

} // namespace

/**Function*************************************************************

  Synopsis    [Does not propagate relative wire-arrival changes below 1e-6.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManSetWireTolerance(int Enable)
{
    Pa_EvalBind();
    s_pSettings->wireTolerance = Enable != 0;
}

/**Function*************************************************************

  Synopsis    [Repairs, else rejects, candidates that raise the overflow too much.]

  Description [A candidate may not raise the density overflow above
               max(0.099, current overflow).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManSetCapacityRepair(int Enable)
{
    Pa_EvalBind();
    s_pSettings->capacityRepair = Enable != 0;
}

/**Function*************************************************************

  Synopsis    [Snaps new nodes to the clusters inherited through pa_strash.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManSetClusterEvaluation(int Enable)
{
    Pa_EvalBind();
    s_pSettings->clusterEvaluation = Enable != 0;
}

/**Function*************************************************************

  Synopsis    [Keeps all arrival and required times exact during a pass.]

  Description [Needed by resubstitution, whose divisors may lie beyond the
               traversal frontier.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManSetExactTiming(int Enable)
{
    Pa_EvalBind();
    s_pSettings->exactTiming = Enable != 0;
}

/**Function*************************************************************

  Synopsis    [Adds the slack change to the candidate score.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManSetTimingEvaluation(int Enable)
{
    Pa_EvalBind();
    s_pSettings->timingEvaluation = Enable != 0;
    if ( !s_pSettings->timingEvaluation )
        (*s_pTiming) = Pa_TimingCache{};
}

/**Function*************************************************************

  Synopsis    [Rejects candidates that grow the physical area without a node gain.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pa_ManSetPhysicalAreaGuard(int Enable)
{
    Pa_EvalBind();
    s_pSettings->physicalAreaGuard = Enable != 0;
}

/**Function*************************************************************

  Synopsis    [Prepares the read cache and the timing of a pass.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManPrepareTimingPass(Abc_Ntk_t * pNtk)
{
    Pa_EvalBind();
    s_pReadCache->Start(pNtk);
    if ( !s_pSettings->timingEvaluation )
        return 1;
    return s_pTiming->Build(pNtk);
}

/**Function*************************************************************

  Synopsis    [Evaluates a candidate replacement of the root.]

  Description [The graph is evaluated against the MFFC marked by the
               current traversal ID. Internal ANDs are simulated with ABC's
               simplification and structural-hashing rules; no ABC objects
               are created. Returns 1 if the candidate is valid; the gain
               and the score are returned.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManEvaluateCandidate(Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, int nNodesSaved, int LevelMax, int fRootComplement,
                            int * pGain, double * pScore, double * pHpwlSaved, double * pHpwlAdded,
                            double * pDensityDelta)
{
    Pa_EvalBind();
    if ( pRoot == nullptr || pGraph == nullptr || nNodesSaved < 0 )
        return 0;
    if ( s_pSettings->timingEvaluation && !s_pTiming->RefreshMarkedCone(pRoot) )
        return 0;
    if ( !Pa_StructuralScreen(pRoot, pGraph, nNodesSaved, LevelMax) )
        return 0;
    Pa_CandidatePlan Plan(pRoot, pGraph, nNodesSaved, LevelMax, fRootComplement);
    if ( !Plan.IsValid() || Plan.ReversesRecentStructure() )
        return 0;
    if ( pGain )
        *pGain = Plan.Gain();
    if ( pScore )
        *pScore = Plan.Score();
    if ( pHpwlSaved )
        *pHpwlSaved = Plan.HpwlSaved();
    if ( pHpwlAdded )
        *pHpwlAdded = Plan.HpwlAdded();
    if ( pDensityDelta )
        *pDensityDelta = Plan.DensityDelta();
    return 1;
}

/**Function*************************************************************

  Synopsis    [Commits a candidate replacement together with its placement.]

  Description [Rebuilds the MFFC mark and the placement of the candidate,
               creates the graph once, and commits the graph and its
               placement together.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pa_ManCommitCandidate(Abc_Obj_t * pRoot, Dec_Graph_t * pGraph, Vec_Ptr_t * vLeaves, int fUpdateLevel, int nGain)
{
    Pa_EvalBind();
    if ( pRoot == nullptr || pGraph == nullptr || vLeaves == nullptr )
        return 0;
    Abc_Ntk_t * pNtk = pRoot->pNtk;
    int ProcessedRootId = pRoot->Id;
    int nNodesSaved = Pa_MarkMffc(pRoot, vLeaves);

    Pa_CandidatePlan Plan(pRoot, pGraph, nNodesSaved, ABC_INFINITY);
    if ( !Plan.IsValid() || !Pa_ManBeginEdit(pNtk) )
        return 0;

    int NodesBefore = Abc_NtkNodeNum(pNtk);
    int FirstNewId = Abc_NtkObjNumMax(pNtk);
    auto DirectFanouts = Plan.DirectFanouts();
    auto TimingMovedIds = Plan.TimingMovedObjectIds();
    auto RequiredSeeds =
        s_pSettings->timingEvaluation && s_pSettings->exactTiming ? Plan.RequiredBoundaryIds() : std::vector<int>{};
    double HpwlBefore = 0.0, HpwlScale = 1.0;
    Pa_ManReadMetrics(pNtk, &HpwlBefore, nullptr, &HpwlScale, nullptr);
    if ( !Plan.StageOldPlacement() )
    {
        Pa_ManClearPlacement();
        return 0;
    }
    Abc_Obj_t * pRootNew = Pa_GraphToNetwork(pNtk, pGraph);

    std::vector<int> NewIds;
    bool ExactMaterialization = Plan.MaterializationMatchesPlan(pGraph, FirstNewId, NewIds);
    if ( !Plan.WriteUpdatedPositions(pGraph, FirstNewId) ||
         !Pa_AigReplace(static_cast<Abc_Aig_t *>(pNtk->pManFunc), pRoot, pRootNew, fUpdateLevel) )
    {
        Pa_ManClearPlacement();
        return 0;
    }
    s_pReadCache->Invalidate();

    int ActualGain = NodesBefore - Abc_NtkNodeNum(pNtk);
    // A matching node count is not enough to justify a local HPWL delta.
    // Materialization must preserve every predicted reuse/new-node identity,
    // and replacement must delete exactly the old MFFC without a downstream
    // structural-hash cascade.  Otherwise rebuild the actual netlist.
    bool ExactBoundary = ExactMaterialization && ActualGain == nGain && nGain == Plan.Gain() &&
                         Plan.BoundaryMatchesPlan(NewIds, DirectFanouts, pRootNew);
    bool TimingRebuilt = false;
    if ( ExactBoundary )
    {
        if ( !Pa_ManFinishLocalEdit(pNtk, Plan.HpwlSaved() - Plan.HpwlAdded()) )
        {
            Pa_ManClearPlacement();
            return 0;
        }
    }
    else
    {
        if ( !Pa_ManFinishGlobalEdit(pNtk) )
        {
            Pa_ManClearPlacement();
            return 0;
        }
        double HpwlAfter = 0.0;
        Pa_ManReadMetrics(pNtk, &HpwlAfter, nullptr, nullptr, nullptr);
        double ActualScore = ActualGain + 0.25 * (HpwlBefore - HpwlAfter) / HpwlScale;
        if ( s_pSettings->timingEvaluation )
        {
            if ( !s_pTiming->Build(pNtk) )
            {
                Pa_ManClearPlacement();
                return 0;
            }
            TimingRebuilt = true;
        }
        // The replacement is functionally correct, and the placement and the
        // timing rebuilt above describe the actual netlist.  A replacement
        // that turned out worse than predicted is reported and kept, so that
        // one misprediction does not discard the whole pass.
        if ( ActualGain < 0 || ActualScore <= kCompareTolerance )
            Abc_Print(0,
                      "placement: a replacement with a %s result has nonpositive actual score %.9f "
                      "(predicted gain %d, actual gain %d, HPWL %.9f -> %.9f, predicted local "
                      "reduction %.9f); it is kept.\n",
                      Plan.ResultIsVirtual() ? "virtual" : "structurally reused",
                      ActualScore, nGain, ActualGain, HpwlBefore, HpwlAfter, Plan.HpwlSaved() - Plan.HpwlAdded());
    }
    if ( s_pSettings->timingEvaluation && !TimingRebuilt )
    {
        bool TimingUpdated = false;
        if ( ExactBoundary )
        {
            std::vector<int> PositionIds = TimingMovedIds;
            std::vector<int> StructuralIds;
            // Collect every live object created while realizing the exact
            // candidate.  New object IDs can be above the old traversal
            // cursor and therefore must be seeded explicitly.
            for ( int Id = FirstNewId; Id < Abc_NtkObjNumMax(pNtk); ++Id )
            {
                Abc_Obj_t * pObject = Abc_NtkObj(pNtk, Id);
                if ( pObject == nullptr || !Abc_ObjIsNode(pObject) )
                    continue;
                PositionIds.push_back(Id);
                StructuralIds.push_back(Id);
            }
            Abc_Obj_t * pRootRegular = Abc_ObjRegular(pRootNew);
            if ( pRootRegular != nullptr && pRootRegular->Id >= 0 && pRootRegular->Id < Abc_NtkObjNumMax(pNtk) &&
                 Abc_NtkObj(pNtk, pRootRegular->Id) == pRootRegular )
            {
                StructuralIds.push_back(pRootRegular->Id);
                if ( Abc_ObjIsNode(pRootRegular) )
                    PositionIds.push_back(pRootRegular->Id);
            }
            for ( const Pa_DirectFanout & Entry : DirectFanouts )
                StructuralIds.push_back(Entry.id);
            TimingUpdated = s_pTiming->UpdateAfterLocalEdit(pNtk, PositionIds, StructuralIds,
                                                            s_pSettings->exactTiming ? ABC_INFINITY : ProcessedRootId,
                                                            fUpdateLevel != 0);
            if ( TimingUpdated && s_pSettings->exactTiming )
            {
                RequiredSeeds.insert(RequiredSeeds.end(), PositionIds.begin(), PositionIds.end());
                s_pTiming->InvalidateRequired(pNtk, RequiredSeeds);
            }
        }
        // A failed local update falls back to a full rebuild.
        if ( !TimingUpdated && !s_pTiming->Build(pNtk) )
        {
            Pa_ManClearPlacement();
            return 0;
        }
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
