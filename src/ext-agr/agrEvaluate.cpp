#include "agrLog.h"
/**CFile****************************************************************

  FileName    [agrEvaluate.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Lightweight placement-aware optimization support.]

  Synopsis    [Side-effect-free HPWL and density evaluation of AIG rewrites.]

  Description [Builds a virtual replacement hypergraph, places its new nodes
               in median regions, and commits only the selected candidate.]

***********************************************************************/

#include "agrEvaluate.h"
#include "aig/gia/gia.h"
#include "map/mio/mio.h"
#include "misc/util/utilNam.h"
#include "map/scl/sclCon.h"
#include "agrAig.h"
#include "base/main/main.h"
#include "agrProfile.h"
#include "agrMath.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <limits>
#include <map>
#include <memory>
#include <queue>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <cstring>
#include <fstream>
#include <string>
#include <functional>
#include "agrSpeed.h"

#include "agrPlace.h"

ABC_NAMESPACE_IMPL_START

namespace
{

static bool s_PhysicalAreaGuard = false;

static double s_CompareHpwl = 0, s_CompareArea = 1;
static long s_CompareMaxGrowth = 0;
static long s_CompareNegativeSelected = 0, s_CompareMinusOneSelected = 0,
            s_CompareGrowthCommits = 0;
static long s_CompareCalls = 0, s_CompareScreens = 0, s_ComparePlans = 0, s_CompareCommits = 0,
            s_CompareFallbacks = 0;
static bool s_ClusterEvaluation = false;

static long s_CoRepairCalls = 0, s_CoRepairSuccess = 0, s_CoDensityReject = 0;

struct CoRootObservation
{
    int calls = 0, commits = 0, gain = 0, plans = 0;
    double wire = 0;
};

static int s_CoMinimumGain = 0;

static std::vector<CoRootObservation> s_CoRootObservations;

static double s_CandidateScoreFloor = -std::numeric_limits<double>::infinity();
static long s_BoundQueries = 0, s_BoundPruned = 0;

static int s_TimingEvaluation = 0;
static bool s_ExactTimingEvaluation = false;
static bool s_RequiredTimingEvaluation = false;
static bool s_BalancedRefactor = false;





constexpr double kTimingEndpointWeight = 1.0;
static double s_TimingWeight = 0.50;


static int s_ScoreMode = 0;
#ifdef ABC_AGR_ENABLE_AUDIT
static unsigned long long s_PlanAttempts = 0, s_PlanCascades = 0, s_PlanValid = 0;
static unsigned long long s_ScreenChecks = 0;
#endif
constexpr double kCompareTolerance = 1.0e-10;
constexpr int kRegionDivisions = 5;
constexpr double kMinimumRegionStep = 0.05;

struct AgrEval_Geometry
{
    double x = 0.0;
    double y = 0.0;
    double width = 0.0;
    double densityHalfX = 0.0;
    double densityHalfY = 0.0;
    double densityScale = 0.0;
};

/* Candidate evaluation does not mutate placement. Cache live data by object
   ID until the next commit. No cache entry survives a pass/ID reassignment. */
struct AgrEval_ReadCache
{
    struct Object
    {
        AgrEval_Geometry geometry;
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
        if (++version == 0)
        {
            objects.clear();
            bins.clear();
            version = 1;
        }
    }
    void Start(Abc_Ntk_t *Network)
    {
        Invalidate();
        objects.resize(Abc_NtkObjNumMax(Network));
    }
    Object &Get(int Id)
    {
        if (static_cast<size_t>(Id) >= objects.size())
            objects.resize(std::max(static_cast<size_t>(Id + 1), objects.size() * 2));
        return objects[Id];
    }
    void BeginCandidate(int Count)
    {
        bins.resize(Count);
        if (++candidate == 0)
        {
            for (auto &B : bins)
                B.deltaStamp = 0;
            candidate = 1;
        }
    }
};
static AgrEval_ReadCache s_ReadCache;

static int AgrEval_ReadObjectGeometry(Abc_Ntk_t *Network, Abc_Obj_t *Object, double *X, double *Y,
                                     double *Width, double *HalfX, double *HalfY, double *Scale)
{
    auto &C = s_ReadCache.Get(Object->Id);
    if (C.geometryStamp != s_ReadCache.version)
    {
        auto &G = C.geometry;
        C.hasPoint =
            Agr_ManReadObjectGeometry(Network, Object, &G.x, &G.y, &G.width, &G.densityHalfX,
                                     &G.densityHalfY, &G.densityScale) != 0;
        C.geometryStamp = s_ReadCache.version;
    }
    if (!C.hasPoint)
        return 0;
    const auto &G = C.geometry;
    if (X)
        *X = G.x;
    if (Y)
        *Y = G.y;
    if (Width)
        *Width = G.width;
    if (HalfX)
        *HalfX = G.densityHalfX;
    if (HalfY)
        *HalfY = G.densityHalfY;
    if (Scale)
        *Scale = G.densityScale;
    return 1;
}

struct AgrEval_Entity
{
    Abc_Obj_t *object = nullptr;
    int decIndex = -1;
    bool virtualNode = false;
    bool movable = false;
    bool hasPoint = false;
    AgrEval_Geometry geometry;
};

struct AgrEval_Cluster
{
    double x = 0.0;
    double y = 0.0;
    int count = 0;
};

struct AgrEval_SymbolicLit
{
    int entity = -1;
    bool complement = false;
};

struct AgrEval_LocalNet
{
    AgrSpeed::IntList pins;
    int fixedCount = 0;
    double fixedMinX = 0.0, fixedMaxX = 0.0;
    double fixedMinY = 0.0, fixedMaxY = 0.0;

    void AddFixed(double X, double Y)
    {
        if (fixedCount++ == 0)
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

struct AgrEval_DirectFanout
{
    int id = -1;
    Abc_Obj_t *object = nullptr;
    Abc_Obj_t *otherFanin = nullptr;
    bool rootComplement = false;
};

struct AgrEval_Rectangle
{
    double lowX = 0.0;
    double highX = 0.0;
    double lowY = 0.0;
    double highY = 0.0;
    bool valid = false;
};

struct AgrEval_Arrival
{
    int logic = 0;
    double wire = 0.0;
};

// Candidate timing uses membership and memo lookups, never hash iteration.
// AIG object IDs let us reuse this scratch space without per-object allocation
// or an O(network size) clear for every candidate. Like the placement read
// cache, it belongs to the sequential evaluator; no candidate timing escapes
// its constructor or overlaps another candidate evaluation.
struct AgrEval_CandidateTimingScratch
{
    struct Object
    {
        AgrEval_Arrival memo;
        unsigned affected = 0, ancestor = 0, visiting = 0, memoStamp = 0, scheduled = 0;
    };
    std::vector<Object> objects;
    std::vector<Abc_Obj_t *> moved, backward, queue;
    unsigned generation = 0;
    void Start(int ObjectMax)
    {
        if (static_cast<int>(objects.size()) < ObjectMax)
            objects.resize(ObjectMax);
        if (++generation == 0)
        {
            std::fill(objects.begin(), objects.end(), Object{});
            generation = 1;
        }
        moved.clear();
        backward.clear();
        queue.clear();
    }
    bool Mark(unsigned &Stamp)
    {
        if (Stamp == generation)
            return false;
        Stamp = generation;
        return true;
    }
};
static AgrEval_CandidateTimingScratch s_CandidateTiming;

struct AgrEval_TimingNode
{
    AgrEval_Arrival arrival;
    int requiredLogic = ABC_INFINITY;
    double requiredWire = std::numeric_limits<double>::infinity();
    double x = 0.0;
    double y = 0.0;
};

/* Kept outside Abc_Obj_t so placement does not change ABC's object layout.
   A pass starts with one global build, then refreshes timing locally. */
struct ArrivalCounters
{
    long long visits = 0, logic = 0, wire = 0, wireTiny = 0, pruned = 0;
    ~ArrivalCounters() {}
};
static ArrivalCounters &arrivalStats()
{
    static ArrivalCounters c;
    return c;
}
// An unconstrained timing model contributes no score. Subtracting two
// infinite potentials would otherwise turn an otherwise valid score into NaN.
static double AgrEval_SlackPotentialDelta(double OldSlack, double NewSlack)
{
    if (OldSlack == std::numeric_limits<double>::infinity() && OldSlack == NewSlack)
        return 0.0;
    if (!std::isfinite(OldSlack) || !std::isfinite(NewSlack))
        return std::numeric_limits<double>::quiet_NaN();
    auto Potential = [](double Slack) { return Slack > 0.0 ? std::log1p(Slack) : Slack; };
    return Potential(NewSlack) - Potential(OldSlack);
}
struct AgrEval_TimingCache
{
    Abc_Ntk_t *network = nullptr;
    std::vector<AgrEval_TimingNode> nodes;
    std::vector<int> topoRank;
    int maxLogic = 0;
    double maxWire = 0.0;
    double wireScale = 1.0;
    bool ready = false;
    unsigned updateStamp = 0;
    std::vector<unsigned> positionStamp;
    std::vector<unsigned> arrivalQueueStamp;
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
    int requiredUsesAudited = 0;
    int requiredUsesMismatched = 0;

    static double Distance(const AgrEval_TimingNode &From, const AgrEval_TimingNode &To)
    {
        return std::hypot(From.x - To.x, From.y - To.y);
    }

    static bool SameWireValue(double Left, double Right)
    {
        if (std::isinf(Left) || std::isinf(Right))
            return Left == Right;
        double Epsilon = kCompareTolerance * (1.0 + std::max(std::fabs(Left), std::fabs(Right)));
        return std::fabs(Left - Right) <= Epsilon;
    }

    bool Build(Abc_Ntk_t *pNtk)
    {
        AGR_PROFILE_SCOPE(Build);
        ready = false;
        network = pNtk;
        if (pNtk == nullptr || (!Agr_ManIsPassActive(pNtk) && !Agr_ManHasPlacement(pNtk)))
            return false;
        nodes.assign(Abc_NtkObjNumMax(pNtk), AgrEval_TimingNode{});
        requiredQueue.clear();
        requiredDirty.assign(nodes.size(), 0);
        topoRank.assign(nodes.size(), 0);
        positionStamp.assign(nodes.size(), 0);
        arrivalQueueStamp.assign(nodes.size(), 0);
        arrivalNext.resize(nodes.size());
        arrivalLevelHead.clear();
        refreshStamp.assign(nodes.size(), 0);
        updateStamp = 0;
        refreshGeneration = 0;
        lastRefreshRootId = -1;
        maxLogic = 0;
        maxWire = 0.0;
        Vec_Ptr_t *pOrder = Abc_NtkDfs(pNtk, 1);
        Abc_Obj_t *pObj;
        int i;
        bool Complete = true;
        Vec_PtrForEachEntry(Abc_Obj_t *, pOrder, pObj, i)
        {
            if (!Abc_ObjIsNode(pObj))
                continue;
            AgrEval_TimingNode &Timing = nodes[pObj->Id];
            if (!Agr_ManReadObjectPosition(pNtk, pObj, &Timing.x, &Timing.y))
            {
                Complete = false;
                break;
            }
            Abc_Obj_t *pFanin;
            int k;
            Abc_ObjForEachFanin(pObj, pFanin, k)
            {
                const AgrEval_TimingNode &Input = nodes[pFanin->Id];
                Timing.arrival.logic = std::max(Timing.arrival.logic, Input.arrival.logic + 1);
                double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, Timing);
                Timing.arrival.wire = std::max(Timing.arrival.wire, Input.arrival.wire + Wire);
            }
            /* Logic depth is itself a valid topological rank.  Unlike object
               IDs or a saved DFS index, it remains valid after local AIG
               replacement creates late-ID nodes feeding older fanouts. */
            topoRank[pObj->Id] = Timing.arrival.logic;
        }
        if (Complete)
        {
            Abc_NtkForEachCo(pNtk, pObj, i)
            {
                const AgrEval_Arrival &Input = nodes[Abc_ObjFanin0(pObj)->Id].arrival;
                nodes[pObj->Id].arrival = Input;
                topoRank[pObj->Id] = Input.logic;
                maxLogic = std::max(maxLogic, Input.logic);
                maxWire = std::max(maxWire, Input.wire);
            }
            wireScale = maxLogic > 0 && maxWire > 1.0e-8 ? maxWire / maxLogic : 1.0;
            Abc_NtkForEachCo(pNtk, pObj, i)
            {
                AgrEval_TimingNode &Output = nodes[pObj->Id];
                Output.requiredLogic = maxLogic;
                Output.requiredWire = maxWire;
                AgrEval_TimingNode &Driver = nodes[Abc_ObjFanin0(pObj)->Id];
                Driver.requiredLogic = std::min(Driver.requiredLogic, maxLogic);
                Driver.requiredWire = std::min(Driver.requiredWire, maxWire);
            }
            Vec_PtrForEachEntryReverse(Abc_Obj_t *, pOrder, pObj, i)
            {
                if (!Abc_ObjIsNode(pObj))
                    continue;
                const AgrEval_TimingNode &Parent = nodes[pObj->Id];
                Abc_Obj_t *pFanin;
                int k;
                Abc_ObjForEachFanin(pObj, pFanin, k)
                {
                    AgrEval_TimingNode &Input = nodes[pFanin->Id];
                    if (Parent.requiredLogic != ABC_INFINITY)
                        Input.requiredLogic =
                            std::min(Input.requiredLogic, Parent.requiredLogic - 1);
                    if (std::isfinite(Parent.requiredWire))
                    {
                        double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, Parent);
                        Input.requiredWire =
                            std::min(Input.requiredWire, Parent.requiredWire - Wire);
                    }
                }
            }
        }
        Vec_PtrFree(pOrder);
        ready = Complete;
        return ready;
    }

    bool UpdateAfterLocalEdit(Abc_Ntk_t *pNtk, const std::vector<int> &PositionIds,
                              const std::vector<int> &StructuralIds,
                              bool LevelsCurrent)
    {
        AGR_PROFILE_SCOPE(ArrivalPropagation);
        if (!ready || network != pNtk || pNtk == nullptr)
            return false;
        int ObjectMax = Abc_NtkObjNumMax(pNtk);
        if (static_cast<int>(nodes.size()) < ObjectMax)
        {
            nodes.resize(ObjectMax);
            topoRank.resize(ObjectMax, 0);
            positionStamp.resize(ObjectMax, 0);
            arrivalQueueStamp.resize(ObjectMax, 0);
            arrivalNext.resize(ObjectMax);
            refreshStamp.resize(ObjectMax, 0);
        }
        if (++updateStamp == 0)
        {
            std::fill(positionStamp.begin(), positionStamp.end(), 0);
            std::fill(arrivalQueueStamp.begin(), arrivalQueueStamp.end(), 0);
            updateStamp = 1;
        }
        lastRefreshRootId = -1;

        for (int Id : PositionIds)
        {
            if (Id < 0 || Id >= ObjectMax || positionStamp[Id] == updateStamp)
                continue;
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk, Id);
            if (pObject == nullptr || !Abc_ObjIsNode(pObject))
                continue;
            double X, Y;
            if (!Agr_ManReadObjectPosition(pNtk, pObject, &X, &Y))
                return false;
            nodes[Id].x = X;
            nodes[Id].y = Y;
            positionStamp[Id] = updateStamp;
        }

        /* Arrival is a forward data-flow problem.  Seed every changed object
           and every fanout whose incident edge or fanin identity changed.
           Propagate to every affected fanout. Object IDs are allocation order,
           not topological order: a newly allocated node can drive an older
           object, including a boundary of the next candidate's marked cone. */
        workQueue.clear();
        // With unrestricted rs propagation, a FIFO can revisit a reconvergent
        // cone once per path length. ABC has already updated structural levels
        // in Abc_AigReplace. Bucket by those levels (not old IDs/timing ranks)
        // so each node follows all affected fanins, without a heap operation
        // per node. Buckets drain completely and are reused at the next edit.
        // When structural levels are unavailable, the FIFO revisits nodes
        // after changed fanins and reaches the same forward fixed point.
        bool Ordered = LevelsCurrent;
        int MinArrivalLevel = ABC_INFINITY, MaxArrivalLevel = -1;
        auto EnqueueArrival = [&](int Id)
        {
            if (Id < 0 || Id >= ObjectMax || arrivalQueueStamp[Id] == updateStamp ||
                Abc_NtkObj(pNtk, Id) == nullptr)
                return;
            arrivalQueueStamp[Id] = updateStamp;
            if (Ordered)
            {
                Abc_Obj_t *Object = Abc_NtkObj(pNtk, Id);
                int Rank = Abc_ObjIsCo(Object) ? Abc_ObjFanin0(Object)->Level + 1 : Object->Level;
                if (Rank >= static_cast<int>(arrivalLevelHead.size()))
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
            if (Id < 0 || Id >= ObjectMax)
                return;
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk, Id);
            if (pObject == nullptr)
                return;
            EnqueueArrival(Id);
            Abc_Obj_t *pFanout;
            int i;
            Abc_ObjForEachFanout(pObject, pFanout, i) EnqueueArrival(pFanout->Id);
        };
        for (int Id : PositionIds)
            EnqueueObjectAndFanouts(Id);
        for (int Id : StructuralIds)
            EnqueueObjectAndFanouts(Id);

        size_t Head = 0;
        while (Ordered ? MinArrivalLevel <= MaxArrivalLevel : Head < workQueue.size())
        {
            int Id;
            if (Ordered)
            {
                while (MinArrivalLevel <= MaxArrivalLevel && arrivalLevelHead[MinArrivalLevel] < 0)
                    ++MinArrivalLevel;
                if (MinArrivalLevel > MaxArrivalLevel)
                    break;
                Id = arrivalLevelHead[MinArrivalLevel];
                arrivalLevelHead[MinArrivalLevel] = arrivalNext[Id];
            }
            else
            {
                Id = workQueue[Head++];
                arrivalQueueStamp[Id] = 0;
            }
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk, Id);
            if (pObject == nullptr)
                continue;
            AgrEval_Arrival NewArrival;
            if (Abc_ObjIsCo(pObject))
                NewArrival = nodes[Abc_ObjFanin0(pObject)->Id].arrival;
            else if (Abc_ObjIsNode(pObject))
            {
                Abc_Obj_t *pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i)
                {
                    const AgrEval_TimingNode &Input = nodes[pFanin->Id];
                    NewArrival.logic = std::max(NewArrival.logic, Input.arrival.logic + 1);
                    double Wire = Abc_ObjIsCi(pFanin) ? 0.0 : Distance(Input, nodes[Id]);
                    NewArrival.wire = std::max(NewArrival.wire, Input.arrival.wire + Wire);
                }
            }
            AGR_PROFILE_COUNT(ArrivalNodes, 1);
            const AgrEval_Arrival OldArrival = nodes[Id].arrival;
            bool Changed = OldArrival.logic != NewArrival.logic ||
                           OldArrival.wire != NewArrival.wire;
            arrivalStats().visits++;
            if (OldArrival.logic != NewArrival.logic)
                arrivalStats().logic++;
            else if (Changed)
            {
                arrivalStats().wire++;
                const double rel = std::fabs(OldArrival.wire - NewArrival.wire) /
                                   std::max(1e-12, std::max(std::fabs(OldArrival.wire),
                                                            std::fabs(NewArrival.wire)));
                if (rel < 1e-3)
                    arrivalStats().wireTiny++;
            }
            // Updating this arrival while suppressing a small change leaves
            // its fanouts stale. Propagate every stored change; a numerical
            // tolerance remains appropriate for audits, not dependency repair.
            nodes[Id].arrival = NewArrival;
            topoRank[Id] = NewArrival.logic;
            if (!Changed)
                continue;
            Abc_Obj_t *pFanout;
            int i;
            Abc_ObjForEachFanout(pObject, pFanout, i) EnqueueArrival(pFanout->Id);
        }
        return true;
    }

    void InvalidateRequired(Abc_Ntk_t *pNtk, const std::vector<int> &Seeds)
    {
        AGR_PROFILE_SCOPE(RequiredInvalidation);
        // Upstream propagation marks dependencies, without computing timing.
        // Already dirty cones are skipped. Values on visited nodes are never
        // rebuilt unless a later root actually consumes them after reuse.
        requiredQueue.clear();
        requiredDirty.resize(nodes.size(), 0);
        auto Mark = [&](int Id)
        {
            if (Id >= 0 && Id < static_cast<int>(nodes.size()) && Abc_NtkObj(pNtk, Id) != nullptr &&
                !requiredDirty[Id])
            {
                requiredDirty[Id] = 1;
                requiredQueue.push_back(Id);
            }
        };
        for (int Id : Seeds)
            Mark(Id);
        for (size_t Head = 0; Head < requiredQueue.size(); ++Head)
        {
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk, requiredQueue[Head]);
            Abc_Obj_t *pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) Mark(pFanin->Id);
        }
    }

    bool RefreshRequiredUses(Abc_Obj_t *pRoot)
    {
        AGR_PROFILE_SCOPE(RequiredRefresh);
        auto Refresh = [&](auto &&Self, Abc_Obj_t *Object) -> bool
        {
            int Id = Object->Id;
            if (Id < 0 || Id >= static_cast<int>(requiredDirty.size()))
                return false;
            if (requiredDirty[Id] == 0)
                return true;
            if (requiredDirty[Id] == 2)
                return false;
            requiredDirty[Id] = 2;
            AGR_PROFILE_COUNT(RequiredNodes, 1);
            int Logic = Abc_ObjIsCo(Object) ? maxLogic : ABC_INFINITY;
            double Wire = Abc_ObjIsCo(Object) ? maxWire : std::numeric_limits<double>::infinity();
            Abc_Obj_t *Fanout;
            int i;
            Abc_ObjForEachFanout(Object, Fanout, i)
            {
                if (!Self(Self, Fanout))
                    return false;
                const auto &Out = nodes[Fanout->Id];
                int Step = Abc_ObjIsCo(Fanout) ? 0 : 1;
                double Length =
                    Abc_ObjIsCo(Fanout) || Abc_ObjIsCi(Object) ? 0.0 : Distance(nodes[Id], Out);
                if (Out.requiredLogic != ABC_INFINITY)
                    Logic = std::min(Logic, Out.requiredLogic - Step);
                if (std::isfinite(Out.requiredWire))
                    Wire = std::min(Wire, Out.requiredWire - Length);
            }
            nodes[Id].requiredLogic = Logic;
            nodes[Id].requiredWire = Wire;
            requiredDirty[Id] = 0;
            return true;
        };
        Abc_Obj_t *Fanout;
        int i;
        Abc_ObjForEachFanout(pRoot, Fanout, i) if (!Refresh(Refresh, Fanout)) return false;
        return true;
    }

#ifdef ABC_AGR_ENABLE_AUDIT
    static Vec_Ptr_t *AuditOrder(Abc_Ntk_t *Network)
    {
        // Abc_NtkDfs changes ABC's traversal marks. The evaluator owns those
        // marks for its MFFC, so a diagnostic must use private visitation.
        Vec_Ptr_t *Order = Vec_PtrAlloc(Abc_NtkNodeNum(Network));
        std::vector<unsigned char> Seen(Abc_NtkObjNumMax(Network), 0);
        auto Visit = [&](auto &&Self, Abc_Obj_t *Object) -> void
        {
            if (!Abc_ObjIsNode(Object) || Seen[Object->Id])
                return;
            Seen[Object->Id] = 1;
            Abc_Obj_t *Input;
            int k;
            Abc_ObjForEachFanin(Object, Input, k) Self(Self, Input);
            Vec_PtrPush(Order, Object);
        };
        Abc_Obj_t *Object;
        int i;
        Abc_NtkForEachNode(Network, Object, i) Visit(Visit, Object);
        return Order;
    }

    bool Audit() const
    {
        // Independent full DAG traversal, only enabled in validation runs.
        std::vector<AgrEval_TimingNode> Exact(nodes.size());
        Vec_Ptr_t *Order = AuditOrder(network);
        Abc_Obj_t *Obj;
        int i;
        bool Ok = true;
        Vec_PtrForEachEntry(Abc_Obj_t *, Order, Obj, i)
        {
            if (!Abc_ObjIsNode(Obj))
                continue;
            AgrEval_TimingNode &T = Exact[Obj->Id];
            if (!Agr_ManReadObjectPosition(network, Obj, &T.x, &T.y))
                Ok = false;
            Abc_Obj_t *In;
            int k;
            Abc_ObjForEachFanin(Obj, In, k)
            {
                T.arrival.logic = std::max(T.arrival.logic, Exact[In->Id].arrival.logic + 1);
                double Wire = Abc_ObjIsCi(In) ? 0.0 : Distance(Exact[In->Id], T);
                T.arrival.wire = std::max(T.arrival.wire, Exact[In->Id].arrival.wire + Wire);
            }
        }
        Abc_NtkForEachCo(network, Obj, i)
        {
            Exact[Obj->Id].arrival = Exact[Abc_ObjFanin0(Obj)->Id].arrival;
            Exact[Obj->Id].requiredLogic = maxLogic;
            Exact[Obj->Id].requiredWire = maxWire;
            AgrEval_TimingNode &In = Exact[Abc_ObjFanin0(Obj)->Id];
            In.requiredLogic = std::min(In.requiredLogic, maxLogic);
            In.requiredWire = std::min(In.requiredWire, maxWire);
        }
        Vec_PtrForEachEntryReverse(Abc_Obj_t *, Order, Obj, i)
        {
            if (!Abc_ObjIsNode(Obj))
                continue;
            const AgrEval_TimingNode &Out = Exact[Obj->Id];
            Abc_Obj_t *In;
            int k;
            Abc_ObjForEachFanin(Obj, In, k)
            {
                auto &T = Exact[In->Id];
                double Wire = Abc_ObjIsCi(In) ? 0.0 : Distance(T, Out);
                if (Out.requiredLogic != ABC_INFINITY)
                    T.requiredLogic = std::min(T.requiredLogic, Out.requiredLogic - 1);
                if (std::isfinite(Out.requiredWire))
                    T.requiredWire = std::min(T.requiredWire, Out.requiredWire - Wire);
            }
        }
        Abc_NtkForEachObj(network, Obj, i)
        {
            if (!Abc_ObjIsNode(Obj) && !Abc_ObjIsCo(Obj) && !Abc_ObjIsCi(Obj))
                continue;
            const auto &A = nodes[Obj->Id];
            const auto &B = Exact[Obj->Id];
            if (A.arrival.logic != B.arrival.logic ||
                !SameWireValue(A.arrival.wire, B.arrival.wire) ||
                (!requiredDirty[Obj->Id] && (A.requiredLogic != B.requiredLogic ||
                                             !SameWireValue(A.requiredWire, B.requiredWire))))
            {
                Abc_Print(-1,
                          "PA timing audit failed at %d: arrival %d/%.9f vs %d/%.9f, required "
                          "%d/%.9f vs %d/%.9f.\n",
                          Obj->Id, A.arrival.logic, A.arrival.wire, B.arrival.logic, B.arrival.wire,
                          A.requiredLogic, A.requiredWire, B.requiredLogic, B.requiredWire);
                Ok = false;
                break;
            }
        }
        Vec_PtrFree(Order);
        return Ok;
    }

    void AuditRequiredUse(Abc_Obj_t *pRoot)
    {
        // Audit only the fanout required times consumed by the current root's
        // score. Stale values on already-visited nodes are irrelevant here.
        std::vector<AgrEval_TimingNode> Ref(Abc_NtkObjNumMax(network));
        Vec_Ptr_t *Order = AuditOrder(network);
        Abc_Obj_t *Obj;
        int i;
        Vec_PtrForEachEntry(Abc_Obj_t *, Order, Obj, i) if (Abc_ObjIsNode(Obj))
            Agr_ManReadObjectPosition(network, Obj, &Ref[Obj->Id].x, &Ref[Obj->Id].y);
        Abc_NtkForEachCo(network, Obj, i)
        {
            auto &T = Ref[Obj->Id];
            T.requiredLogic = maxLogic;
            T.requiredWire = maxWire;
            auto &In = Ref[Abc_ObjFanin0(Obj)->Id];
            In.requiredLogic = std::min(In.requiredLogic, maxLogic);
            In.requiredWire = std::min(In.requiredWire, maxWire);
        }
        Vec_PtrForEachEntryReverse(Abc_Obj_t *, Order, Obj, i)
        {
            if (!Abc_ObjIsNode(Obj))
                continue;
            const auto &Out = Ref[Obj->Id];
            Abc_Obj_t *In;
            int k;
            Abc_ObjForEachFanin(Obj, In, k)
            {
                auto &T = Ref[In->Id];
                double Length = Abc_ObjIsCi(In) ? 0.0 : Distance(T, Out);
                if (Out.requiredLogic != ABC_INFINITY)
                    T.requiredLogic = std::min(T.requiredLogic, Out.requiredLogic - 1);
                if (std::isfinite(Out.requiredWire))
                    T.requiredWire = std::min(T.requiredWire, Out.requiredWire - Length);
            }
        }
        ++requiredUsesAudited;
        bool Mismatch = false;
        Abc_ObjForEachFanout(pRoot, Obj, i)
        {
            const auto &A = nodes[Obj->Id];
            const auto &B = Ref[Obj->Id];
            if (A.requiredLogic == B.requiredLogic && SameWireValue(A.requiredWire, B.requiredWire))
                continue;
            if (!Mismatch && requiredUsesMismatched < 3)
                AGR_VERBOSE("PA required-use audit: root %d, fanout %d, cached %d/%.9f, reference "
                           "%d/%.9f.\n",
                           pRoot->Id, Obj->Id, A.requiredLogic, A.requiredWire, B.requiredLogic,
                           B.requiredWire);
            Mismatch = true;
        }
        if (Mismatch)
            ++requiredUsesMismatched;
        Vec_PtrFree(Order);
    }

#endif

    bool RefreshMarkedCone(Abc_Obj_t *pRoot)
    {
        AGR_PROFILE_SCOPE(RootRefresh);
        if (!ready || pRoot == nullptr || pRoot->pNtk != network)
            return false;
        Abc_Ntk_t *pNtk = pRoot->pNtk;
        /* Candidate evaluation is side-effect free.  The old root timing is
           therefore independent of which cut is currently marked and only
           needs one lazy refresh while all cuts of this root are tried.  An
           accepted edit invalidates this key in UpdateAfterLocalEdit(). */
        if (lastRefreshRootId == pRoot->Id)
            return true;
        // The fast rw/rf proxy freezes downstream budgets for this pass.
        // Effort 1/2 and outside-cone rs divisors use lazy required updates.
        if (s_RequiredTimingEvaluation && !RefreshRequiredUses(pRoot))
            return false;
#ifdef ABC_AGR_ENABLE_AUDIT
        if (s_RequiredTimingEvaluation && ((char *)0) != nullptr)
            AuditRequiredUse(pRoot);
#endif
        int ObjectMax = Abc_NtkObjNumMax(pNtk);
        if (static_cast<int>(nodes.size()) < ObjectMax)
        {
            nodes.resize(ObjectMax);
            topoRank.resize(ObjectMax, 0);
            positionStamp.resize(ObjectMax, 0);
            arrivalQueueStamp.resize(ObjectMax, 0);
            refreshStamp.resize(ObjectMax, 0);
        }
        if (++refreshGeneration == 0)
        {
            std::fill(refreshStamp.begin(), refreshStamp.end(), 0);
            refreshGeneration = 1;
        }

        refreshOrder.clear();
        auto Collect = [&](auto &&Self, Abc_Obj_t *pObject) -> void
        {
            pObject = Abc_ObjRegular(pObject);
            if (pObject == nullptr || pObject->Id < 0 || pObject->Id >= ObjectMax ||
                refreshStamp[pObject->Id] == refreshGeneration)
                return;
            refreshStamp[pObject->Id] = refreshGeneration;
            if (Abc_ObjIsNode(pObject) && Abc_NodeIsTravIdCurrent(pObject))
            {
                Abc_Obj_t *pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i) Self(Self, pFanin);
            }
            refreshOrder.push_back(pObject->Id);
        };
        Collect(Collect, pRoot);

        for (int Id : refreshOrder)
        {
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk, Id);
            if (pObject == nullptr)
                return false;
            AgrEval_Arrival NewArrival;
            if (Abc_ObjIsCo(pObject))
                NewArrival = nodes[Abc_ObjFanin0(pObject)->Id].arrival;
            else if (Abc_ObjIsNode(pObject))
            {
                Abc_Obj_t *pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i)
                {
                    const AgrEval_TimingNode &Input = nodes[pFanin->Id];
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

static AgrEval_TimingCache s_Timing;

static double AgrEval_Clamp(double Value, double Low, double High)
{
    if (Low > High)
        return 0.5 * (Low + High);
    return std::max(Low, std::min(High, Value));
}

static bool AgrEval_AlmostLess(double A, double B)
{
    double Epsilon = kCompareTolerance * (1.0 + std::max(std::fabs(A), std::fabs(B)));
    return A < B - Epsilon;
}

static bool AgrEval_AlmostEqual(double A, double B)
{
    double Epsilon = kCompareTolerance * (1.0 + std::max(std::fabs(A), std::fabs(B)));
    return std::fabs(A - B) <= Epsilon;
}

class AgrEval_DensityWorkspace
{
  public:
    AgrEval_DensityWorkspace(Abc_Ntk_t *pNtk, double Width, double Height, int Bins, double BinSizeX,
                            double BinSizeY)
        : pNtk_(pNtk), width_(Width), height_(Height), bins_(Bins), binSizeX_(BinSizeX),
          binSizeY_(BinSizeY)
    {
        s_ReadCache.BeginCandidate(Bins * Bins);
        valid_ = Agr_ManReadDensityBin(pNtk_, 0, 0, nullptr, &targetArea_) != 0;
    }

    bool IsValid() const
    {
        return valid_;
    }

    void Add(const AgrEval_Geometry &Geometry, double Sign)
    {
        exactAreaDelta_ += Sign * Geometry.width;
        auto &Contributions = scratch_;
        ContributionsAt(Geometry, Geometry.x, Geometry.y, Contributions);
        for (const auto &Entry : Contributions)
        {
            auto &B = s_ReadCache.bins[Entry.first];
            if (B.deltaStamp != s_ReadCache.candidate)
            {
                B.deltaStamp = s_ReadCache.candidate;
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
        if (Axis.high <= Axis.low)
            return Axis;
        Axis.first = std::max(0, std::min(bins_ - 1, static_cast<int>(Axis.low / BinSize)));
        Axis.last = std::max(
            0, std::min(bins_ - 1,
                        static_cast<int>(Agr_PreviousBoundary(Axis.high, Axis.low) / BinSize)));
        if (AgrSpeed::Evaluation() && Axis.last - Axis.first < 8)
        {
            Axis.cached = true;
            for (int b = Axis.first; b <= Axis.last; ++b)
                Axis.overlaps[b - Axis.first] = std::max(
                    0.0, std::min(Axis.high, (b + 1) * BinSize) - std::max(Axis.low, b * BinSize));
        }
        return Axis;
    }

    // The sample grid is a Cartesian product: bin ranges depend only on one
    // axis, so prepare each of them once. Accumulate the exact same footprint
    // areas in the same X/Y order without materializing a pair vector.
    double EvaluateAddition(const AgrEval_Geometry &Geometry, const AxisFootprint &X,
                            const AxisFootprint &Y)
    {
        double Cost = 0.0;
        for (int Bx = X.first; Bx <= X.last; ++Bx)
        {
            double OverlapX = X.cached ? X.overlaps[Bx - X.first]
                                       : std::max(0.0, std::min(X.high, (Bx + 1) * binSizeX_) -
                                                           std::max(X.low, Bx * binSizeX_));
            for (int By = Y.first; By <= Y.last; ++By)
            {
                double OverlapY = Y.cached ? Y.overlaps[By - Y.first]
                                           : std::max(0.0, std::min(Y.high, (By + 1) * binSizeY_) -
                                                               std::max(Y.low, By * binSizeY_));
                double Area = OverlapX * OverlapY * Geometry.densityScale;
                if (Area > 0.0)
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
        for (int Index : touched_)
        {
            double Base = BaseDensity(Index);
            Result += std::max(0.0, Base + s_ReadCache.bins[Index].delta - targetArea_) -
                      std::max(0.0, Base - targetArea_);
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

    void ContributionsAt(const AgrEval_Geometry &Geometry, double X, double Y,
                         std::vector<std::pair<int, double>> &Result) const
    {
        Result.clear();
        double X0 = std::max(0.0, X - Geometry.densityHalfX);
        double X1 = std::min(width_, X + Geometry.densityHalfX);
        double Y0 = std::max(0.0, Y - Geometry.densityHalfY);
        double Y1 = std::min(height_, Y + Geometry.densityHalfY);
        if (X1 <= X0 || Y1 <= Y0)
            return;
        int Bx0 = BinX(X0);
        int Bx1 = BinX(Agr_PreviousBoundary(X1, X0));
        int By0 = BinY(Y0);
        int By1 = BinY(Agr_PreviousBoundary(Y1, Y0));
        for (int Bx = Bx0; Bx <= Bx1; ++Bx)
            for (int By = By0; By <= By1; ++By)
            {
                double OverlapX = std::max(0.0, std::min(X1, (Bx + 1) * binSizeX_) -
                                                    std::max(X0, Bx * binSizeX_));
                double OverlapY = std::max(0.0, std::min(Y1, (By + 1) * binSizeY_) -
                                                    std::max(Y0, By * binSizeY_));
                double Area = OverlapX * OverlapY * Geometry.densityScale;
                if (Area > 0.0)
                    Result.emplace_back(Bx * bins_ + By, Area);
            }
    }

    double BaseDensity(int Index)
    {
        auto &B = s_ReadCache.bins[Index];
        if (B.baseStamp != s_ReadCache.version)
        {
            if (!Agr_ManReadDensityBin(pNtk_, Index / bins_, Index % bins_, &B.base, nullptr))
                valid_ = false;
            B.baseStamp = s_ReadCache.version;
        }
        return B.base;
    }

    double Current(int Index)
    {
        const auto &B = s_ReadCache.bins[Index];
        return BaseDensity(Index) + (B.deltaStamp == s_ReadCache.candidate ? B.delta : 0.0);
    }

    Abc_Ntk_t *pNtk_ = nullptr;
    double width_ = 0.0;
    double height_ = 0.0;
    int bins_ = 0;
    double binSizeX_ = 0.0;
    double binSizeY_ = 0.0;
    double targetArea_ = 0.0;
    bool valid_ = false;
    double exactAreaDelta_ = 0.0;
    AgrSpeed::WorkspaceVector<int> touched_;
    // Reuse the footprint buffer for all samples of this candidate.
    AgrSpeed::WorkspaceVector<std::pair<int, double>> scratch_;
};

/* One candidate is live at a time. Generation tags reuse an ID-indexed
   lookup without clearing the whole network or allocating hash nodes for
   each candidate entity. The full plan owns all geometry and placement. */
class AgrEval_EntityIndex
{
    struct Entry
    {
        Abc_Obj_t *first = nullptr;
        int second = -1;
        unsigned stamp = 0;
    };
    inline static std::vector<Entry> entries_;
    inline static unsigned generation_ = 0;
    unsigned stamp_;

  public:
    AgrEval_EntityIndex() : stamp_(++generation_)
    {
        if (stamp_ == 0)
        {
            entries_.clear();
            stamp_ = generation_ = 1;
        }
    }
    const Entry *end() const
    {
        return nullptr;
    }
    const Entry *find(Abc_Obj_t *Object) const
    {
        if (!Object || Object->Id >= entries_.size())
            return nullptr;
        const auto &E = entries_[Object->Id];
        return E.stamp == stamp_ && E.first == Object ? &E : nullptr;
    }
    void emplace(Abc_Obj_t *Object, int Value)
    {
        if (Object->Id >= entries_.size())
            entries_.resize(std::max(static_cast<size_t>(Object->Id + 1), entries_.size() * 2));
        entries_[Object->Id] = Entry{Object, Value, stamp_};
    }
};

/* Small candidate MFFCs use sorted contiguous membership. No pointer-hash
   iteration or allocation per object; enumeration is stable by object ID. */
class AgrEval_ObjectSet
{
    AgrSpeed::WorkspaceVector<Abc_Obj_t *> items_;
    auto lower(Abc_Obj_t *v) const
    {
        return std::lower_bound(items_.begin(), items_.end(), v,
                                [](Abc_Obj_t *a, Abc_Obj_t *b) { return a->Id < b->Id; });
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
    size_t count(Abc_Obj_t *v) const
    {
        if (!v)
            return 0;
        auto it = lower(v);
        return it != end() && *it == v;
    }
    std::pair<iterator, bool> insert(Abc_Obj_t *v)
    {
        auto it = lower(v);
        if (it != end() && *it == v)
            return {it, false};
        return {items_.insert(it, v), true};
    }
    void erase(Abc_Obj_t *v)
    {
        auto it = lower(v);
        if (it != end() && *it == v)
            items_.erase(it);
    }
};

/* Allocation-free structural screen for small decomposition graphs. It uses
   the same live/virtual hashing, simplification and zero-fanout rules as the
   full plan. Only definitely invalid plans are rejected here; larger graphs
   and all retained-cone accounting still use the full evaluator. */
static bool AgrEval_StructuralScreen(Abc_Obj_t *Root, Dec_Graph_t *Graph, int Saved, int LevelMax)
{
    constexpr int Limit = 64;
    if (Graph->nSize > Limit || Dec_GraphIsConst(Graph))
        return true;
    struct Entry
    {
        Abc_Obj_t *object;
        int refs, level, left, right;
    };
    Entry Entries[Limit + 1];
    int Literals[Limit], Count = 0, NewCount = 0;
    auto Actual = [&](Abc_Obj_t *Literal)
    {
        Abc_Obj_t *Object = Abc_ObjRegular(Literal);
        for (int i = 0; i < Count; ++i)
            if (Entries[i].object == Object)
                return 2 * i + Abc_ObjIsComplement(Literal);
        Entries[Count] = Entry{Object, Abc_ObjFanoutNum(Object), (int)Object->Level, -1, -1};
        return 2 * Count++ + Abc_ObjIsComplement(Literal);
    };
    Dec_Node_t *Node;
    int i;
    Dec_GraphForEachLeaf(Graph, Node, i)
    {
        Abc_Obj_t *Object = static_cast<Abc_Obj_t *>(Node->pFunc);
        if (Object == nullptr || Abc_ObjRegular(Object) == Root)
            return false;
        Literals[i] = Actual(Object);
    }
    Dec_GraphForEachNode(Graph, Node, i)
    {
        if (Node->eEdge0.Node >= (unsigned)i || Node->eEdge1.Node >= (unsigned)i)
            return false;
        int A = Literals[Node->eEdge0.Node] ^ Node->eEdge0.fCompl;
        int B = Literals[Node->eEdge1.Node] ^ Node->eEdge1.fCompl;
        int Result = -1;
        if (A / 2 == B / 2)
            Result = A == B ? A : (Actual(Abc_AigConst1(Root->pNtk)) ^ 1);
        else
        {
            int Const = Actual(Abc_AigConst1(Root->pNtk));
            if (A / 2 == Const / 2)
                Result = (A & 1) ? (Const ^ 1) : B;
            else if (B / 2 == Const / 2)
                Result = (B & 1) ? (Const ^ 1) : A;
            else
            {
                int Low = std::min(A, B), High = std::max(A, B);
                if (Entries[A / 2].refs && Entries[B / 2].refs)
                {
                    for (int k = Count - 1; k >= 0; --k)
                        if (Entries[k].object == nullptr && Entries[k].left == Low &&
                            Entries[k].right == High)
                        {
                            Result = 2 * k;
                            break;
                        }
                    Abc_Obj_t *Left = Entries[A / 2].object;
                    Abc_Obj_t *Right = Entries[B / 2].object;
                    if (Result < 0 && Left && Right)
                    {
                        bool LiftLeft = Abc_ObjFanoutNum(Left) == 0;
                        bool LiftRight = Abc_ObjFanoutNum(Right) == 0;
                        if (LiftLeft)
                            ++Left->vFanouts.nSize;
                        if (LiftRight)
                            ++Right->vFanouts.nSize;
                        Abc_Obj_t *Found = Abc_AigAndLookup(
                            static_cast<Abc_Aig_t *>(Root->pNtk->pManFunc),
                            Abc_ObjNotCond(Left, A & 1), Abc_ObjNotCond(Right, B & 1));
                        if (LiftRight)
                            --Right->vFanouts.nSize;
                        if (LiftLeft)
                            --Left->vFanouts.nSize;
                        if (Found)
                        {
                            if (Abc_ObjRegular(Found) == Root)
                                return false;
                            Result = Actual(Found);
                        }
                    }
                }
                if (Result < 0)
                {
                    if (++NewCount > Saved + 0)
                        return false;
                    int Level = 1 + std::max(Entries[A / 2].level, Entries[B / 2].level);
                    Entries[Count] = Entry{nullptr, 0, Level, Low, High};
                    Result = 2 * Count++;
                    ++Entries[A / 2].refs;
                    ++Entries[B / 2].refs;
                }
            }
        }
        if (Entries[Result / 2].level > LevelMax)
            return false;
        Literals[i] = Result;
    }
    return Graph->eRoot.Node < (unsigned)Graph->nSize &&
           Entries[Literals[Graph->eRoot.Node] / 2].object != Root;
}

// Only the labeled original MFFC is shared between candidates of one live
// cut. Retained nodes, placement, density and scores are rebuilt per candidate.
// A commit/pass change invalidates the placement version; a new cut changes
// the network traversal ID. Neither pointers nor marks cross those boundaries.
struct AgrEval_MffcCache
{
    Abc_Ntk_t *network = nullptr;
    Abc_Obj_t *root = nullptr;
    unsigned version = 0;
    int traversal = -1;
    AgrEval_ObjectSet removed;
    AgrSpeed::WorkspaceVector<int> ids;
};
static AgrEval_MffcCache s_MffcCache;

class AgrEval_CandidatePlan
{
  public:
    AgrEval_CandidatePlan(Abc_Obj_t *pRoot, Dec_Graph_t *pGraph, int nNodesSaved, int levelMax,
                         int fRootComplement = 0, bool allowScoreBound = false)
        : pRoot_(pRoot), pNtk_(pRoot ? pRoot->pNtk : nullptr), pGraph_(pGraph),
          nNodesSaved_(nNodesSaved), levelMax_(levelMax), rootComplement_(fRootComplement != 0)
    {
#ifdef ABC_AGR_ENABLE_AUDIT
        ++s_PlanAttempts;
#endif
        if (pRoot_ == nullptr || pGraph_ == nullptr || pNtk_ == nullptr ||
            !Agr_ManIsPassActive(pNtk_) ||
            !Agr_ManReadCanvas(pNtk_, &width_, &height_, &bins_, &binSizeX_, &binSizeY_) ||
            !Agr_ManReadMetrics(pNtk_, nullptr, nullptr, &hpwlScale_, nullptr))
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
        if (static_cast<int>(removed_.size()) != nNodesSaved_)
            return;
        /* Form clusters from the original MFFC before structural reuse can
           reduce the set actually deleted. */

        BuildEntities();
        if (!validBuild_)
            return;
        ComputeRemovedAfterMaterialization();
        if (!validBuild_)
            return;
        if (true && actualGain_ < s_CoMinimumGain)
            return;
        // Cell widths depend on polarity, not candidate coordinates. Reject a
        // provable physical-area violation before constructing nets/placement.
        if (AgrSpeed::Evaluation() && s_PhysicalAreaGuard && !(1 && actualGain_ > 0) &&
            AreaDeltaBeforePlacement() > 1e-9)
            return;
        if (HasDownstreamCascade())
        {
#ifdef ABC_AGR_ENABLE_AUDIT
            ++s_PlanCascades;
#endif
            return;
        }
        density_.reset(
            new AgrEval_DensityWorkspace(pNtk_, width_, height_, bins_, binSizeX_, binSizeY_));
        if (!density_->IsValid())
            return;
        BuildMovables();
        // Fixed extrema retain exact HPWL and median regions; no count-based
        // candidate pruning is needed to use this representation.
        BuildNetsFast();

        InitializeDensity();
        if (!validBuild_)
            return;
        SeedFromPropagatedRegions();
        if (!validBuild_)
            return;

        {
            double currentArea = 0, currentOverflow = 0;
            Agr_ManReadMetrics(pNtk_, nullptr, &currentOverflow, nullptr, &currentArea);
            double next = (currentOverflow * currentArea + density_->OverflowDelta()) /
                          std::max(1e-9, currentArea + density_->ExactAreaDelta());
            if (next > std::max(.099, currentOverflow) + 1e-9)
            {
                ++s_CoRepairCalls;
                RepairCapacity(currentArea, currentOverflow);
                next = (currentOverflow * currentArea + density_->OverflowDelta()) /
                       std::max(1e-9, currentArea + density_->ExactAreaDelta());
                if (next <= std::max(.099, currentOverflow) + 1e-9)
                    ++s_CoRepairSuccess;
            }
            if (next > std::max(.099, currentOverflow) + 1e-9)
            {
                ++s_CoDensityReject;
                return;
            }
        }

        hpwlAdded_ = LocalHpwl();

        double topologyGain = (hpwlSaved_ - hpwlAdded_);

        score_ = static_cast<double>(actualGain_) + 0.25 * topologyGain / hpwlScale_;

        if (s_TimingEvaluation)
        {

            if (!EvaluateTiming())
                return;

            // PA's timing term is dimensionless. Convert it to the raw HPWL
            // units of mode 2, preserving PA's timing-to-HPWL exchange rate.
        }
        // Bound the physical tie-breaker strictly below half a node so no
        // one-node advantage can be exchanged for a proxy improvement.
        if (s_ScoreMode == 1)
        {
            double Physical = score_ - static_cast<double>(actualGain_);
            score_ = actualGain_ + 0.49 * Physical / (1.0 + std::fabs(Physical));
        }
        valid_ =
            (actualGain_ >= -0) && std::isfinite(score_) && std::isfinite(hpwlSaved_) &&
            std::isfinite(hpwlAdded_) && density_->IsValid() &&
            (!s_PhysicalAreaGuard || density_->ExactAreaDelta() <= 1e-9 || (1 && actualGain_ > 0));

#ifdef ABC_AGR_ENABLE_AUDIT
        if (valid_)
            ++s_PlanValid;
#endif
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
        for (Abc_Obj_t *pRemoved : orderedRemoved_)
            if (!Agr_ManStageObjectRemoval(pNtk_, pRemoved))
                return false;
        Abc_Obj_t *pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout,
                             i) if (Abc_ObjIsNode(pFanout) &&
                                    !Agr_ManStageObjectRefresh(pNtk_, pFanout)) return false;
        return true;
    }

    bool ReversesRecentStructure() const
    {
        return false;
    }

    bool MaterializationMatchesPlan(Dec_Graph_t *pGraph, int FirstNewId,
                                    std::vector<int> &NewIds) const
    {
        std::unordered_set<Abc_Obj_t *> NewObjects;
        std::unordered_map<int, Abc_Obj_t *> Realized;
        Dec_Node_t *pDecNode;
        int i;
        Dec_GraphForEachNode(pGraph, pDecNode, i)
        {
            Abc_Obj_t *pLiteral = static_cast<Abc_Obj_t *>(pDecNode->pFunc);
            if (pLiteral == nullptr || i >= static_cast<int>(decToEntity_.size()))
                return false;
            int EntityId = decToEntity_[i];
            if (EntityId < 0)
                return false;
            Abc_Obj_t *pObject = Abc_ObjRegular(pLiteral);
            const AgrEval_Entity &Entity = entities_[EntityId];
            if ((Abc_ObjIsComplement(pLiteral) != 0) != (decPhase_[i] != 0))
                return false;
            if (Entity.virtualNode)
            {
                if (!Abc_ObjIsNode(pObject) || pObject->Id < FirstNewId)
                    return false;
                auto It = Realized.find(EntityId);
                if (It != Realized.end())
                {
                    if (It->second != pObject)
                        return false;
                }
                else
                {
                    if (!NewObjects.insert(pObject).second)
                        return false;
                    Realized.emplace(EntityId, pObject);
                    NewIds.push_back(pObject->Id);
                }
            }
            else if (pObject != Entity.object)
                return false;
        }
        if (NewObjects.size() != virtualEntities_.size())
            return false;
        for (int Id = FirstNewId; Id < Abc_NtkObjNumMax(pNtk_); ++Id)
        {
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk_, Id);
            if (pObject != nullptr && Abc_ObjIsNode(pObject) && !NewObjects.count(pObject))
                return false;
        }
        return true;
    }

    bool BoundaryMatchesPlan(const std::vector<int> &NewIds,
                             const std::vector<AgrEval_DirectFanout> &DirectFanouts,
                             Abc_Obj_t *pRootNew) const
    {
        for (int Id : removedIds_)
            if (Abc_NtkObj(pNtk_, Id) != nullptr)
                return false;
        for (int Id : NewIds)
            if (Id >= Abc_NtkObjNumMax(pNtk_) || Abc_NtkObj(pNtk_, Id) == nullptr)
                return false;
        for (const auto &Entry : DirectFanouts)
        {
            if (Abc_NtkObj(pNtk_, Entry.id) != Entry.object || Abc_ObjFaninNum(Entry.object) != 2)
                return false;
            Abc_Obj_t *pExpected = Abc_ObjNotCond(pRootNew, Entry.rootComplement);
            Abc_Obj_t *pActual0 = Abc_ObjChild0(Entry.object);
            Abc_Obj_t *pActual1 = Abc_ObjChild1(Entry.object);
            if (!((pActual0 == pExpected && pActual1 == Entry.otherFanin) ||
                  (pActual1 == pExpected && pActual0 == Entry.otherFanin)))
                return false;
        }
        return true;
    }

    std::vector<int> RequiredBoundaryIds() const
    {
        std::vector<int> Result;
        for (Abc_Obj_t *pObject : orderedRemoved_)
        {
            Abc_Obj_t *pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) if (!removed_.count(pFanin))
                Result.push_back(pFanin->Id);
        }
        return Result;
    }

    std::vector<AgrEval_DirectFanout> DirectFanouts() const
    {
        std::vector<AgrEval_DirectFanout> Result;
        Abc_Obj_t *pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout, i) if (Abc_ObjIsNode(pFanout))
        {
            int RootIndex = Vec_IntFind(&pFanout->vFanins, pRoot_->Id);
            if (RootIndex < 0)
                continue;
            Result.push_back(AgrEval_DirectFanout{pFanout->Id, pFanout,
                                                 Abc_ObjChild(pFanout, RootIndex ^ 1),
                                                 Abc_ObjFaninC(pFanout, RootIndex) != 0});
        }
        return Result;
    }

    std::vector<int> TimingMovedObjectIds() const
    {
        std::vector<int> Result;
        for (int EntityId : movableEntities_)
        {
            const AgrEval_Entity &Entity = entities_[EntityId];
            if (!Entity.virtualNode && Entity.object != nullptr && !removed_.count(Entity.object))
                Result.push_back(Entity.object->Id);
        }
        SortUnique(Result);
        return Result;
    }

    bool WriteUpdatedPositions(Dec_Graph_t *pGraph, int FirstNewId) const
    {
        std::unordered_set<Abc_Obj_t *> Written;
        double RootX = 0.5 * width_, RootY = 0.5 * height_;
        Agr_ManReadObjectPosition(pNtk_, pRoot_, &RootX, &RootY);
        Dec_Node_t *pDecNode;
        int DecIndex;
        Dec_GraphForEachNode(pGraph, pDecNode, DecIndex)
        {
            if (pDecNode->pFunc == nullptr)
                return false;
            Abc_Obj_t *pObject = Abc_ObjRegular(static_cast<Abc_Obj_t *>(pDecNode->pFunc));
            if (!Abc_ObjIsNode(pObject) || pObject->Id < FirstNewId ||
                !Written.insert(pObject).second)
                continue;
            int EntityId = decToEntity_[DecIndex];
            double X = RootX, Y = RootY;
            if (EntityId >= 0 && entities_[EntityId].virtualNode)
            {
                X = entities_[EntityId].geometry.x;
                Y = entities_[EntityId].geometry.y;
            }
            if (!Agr_ManWriteObjectPosition(pNtk_, pObject, X, Y))
                return false;
        }
        for (int EntityId : movableEntities_)
        {
            const AgrEval_Entity &Entity = entities_[EntityId];
            if (Entity.virtualNode || Entity.object == nullptr ||
                !Written.insert(Entity.object).second)
                continue;
            if (!Agr_ManWriteObjectPosition(pNtk_, Entity.object, Entity.geometry.x,
                                           Entity.geometry.y))
                return false;
        }
        return true;
    }

  private:
    static double TimingBucket(double Slack)
    {
        if (Slack < -0.25)
            return -2.0;
        if (Slack < 0.0)
            return -1.0;
        if (Slack < 0.5)
            return 0.0;
        if (Slack < 1.0)
            return 1.0;
        return 2.0;
    }

    bool TimingPosition(Abc_Obj_t *pObject, double *pX, double *pY) const
    {
        if (pObject == pRoot_)
        {
            if (resultEntity_ < 0)
                return false;
            const AgrEval_Geometry &G = entities_[resultEntity_].geometry;
            *pX = G.x;
            *pY = G.y;
            return true;
        }
        auto It = actualEntities_.find(pObject);
        if (It != actualEntities_.end() && entities_[It->second].hasPoint)
        {
            const AgrEval_Geometry &G = entities_[It->second].geometry;
            *pX = G.x;
            *pY = G.y;
            return true;
        }
        if (pObject->Id < 0 || pObject->Id >= static_cast<int>(s_Timing.nodes.size()))
            return false;
        *pX = s_Timing.nodes[pObject->Id].x;
        *pY = s_Timing.nodes[pObject->Id].y;
        return true;
    }

    bool TimingEntityPosition(int Entity, double *pX, double *pY) const
    {
        const AgrEval_Entity &E = entities_[Entity];
        if (E.virtualNode)
        {
            *pX = E.geometry.x;
            *pY = E.geometry.y;
            return true;
        }
        return E.object != nullptr && TimingPosition(E.object, pX, pY);
    }

    bool TimingIsCi(Abc_Obj_t *pObject) const
    {
        if (pObject == pRoot_)
        {
            Abc_Obj_t *pReplacement = entities_[resultEntity_].object;
            return pReplacement != nullptr && Abc_ObjIsCi(pReplacement);
        }
        return Abc_ObjIsCi(pObject);
    }

    bool TimingForEntity(int Entity, AgrEval_Arrival *pResult)
    {
        const AgrEval_Entity &E = entities_[Entity];
        if (!E.virtualNode)
            return E.object != nullptr && TimingForObject(E.object, pResult);
        if (timingEntityState_[Entity] == 2)
        {
            *pResult = timingEntityMemo_[Entity];
            return true;
        }
        if (timingEntityState_[Entity] == 1)
            return false;
        timingEntityState_[Entity] = 1;
        AgrEval_Arrival Arrival;
        const auto &Inputs = virtualInputs_[Entity];
        for (int Child : {Inputs.first.entity, Inputs.second.entity})
        {
            AgrEval_Arrival Input;
            double X, Y;
            if (!TimingForEntity(Child, &Input) || !TimingEntityPosition(Child, &X, &Y))
                return false;
            const AgrEval_Entity &Source = entities_[Child];
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

    bool TimingForEntityLocal(int Entity, AgrEval_Arrival *pResult)
    {
        if (Entity < 0 || Entity >= static_cast<int>(entities_.size()))
            return false;
        if (timingEntityState_[Entity] == 2)
        {
            *pResult = timingEntityMemo_[Entity];
            return true;
        }
        if (timingEntityState_[Entity] == 1)
            return false;
        const AgrEval_Entity &E = entities_[Entity];

        /* An unchanged boundary object keeps its cached arrival.  Candidate
           core objects are the virtual ANDs and structurally reused ANDs
           produced by this graph; placement can also move a literal result,
           in which case its two real fanins are a bounded local update. */
        if (!E.virtualNode && !E.movable && !timingProduced_[Entity] && !timingBoundary_[Entity])
        {
            if (E.object == nullptr || E.object->Id < 0 ||
                E.object->Id >= static_cast<int>(s_Timing.nodes.size()))
                return false;
            *pResult = s_Timing.nodes[E.object->Id].arrival;
            return true;
        }

        timingEntityState_[Entity] = 1;
        AgrEval_Arrival Arrival;
        double X, Y;
        if (!TimingEntityPosition(Entity, &X, &Y))
            return false;
        auto Accumulate = [&](int Child, Abc_Obj_t *pChildObject) -> bool
        {
            AgrEval_Arrival Input;
            double InputX, InputY;
            if (Child >= 0)
            {
                if (!TimingForEntityLocal(Child, &Input) ||
                    !TimingEntityPosition(Child, &InputX, &InputY))
                    return false;
                pChildObject = entities_[Child].object;
            }
            else
            {
                pChildObject = Abc_ObjRegular(pChildObject);
                if (pChildObject == nullptr || pChildObject->Id < 0 ||
                    pChildObject->Id >= static_cast<int>(s_Timing.nodes.size()) ||
                    !TimingPosition(pChildObject, &InputX, &InputY))
                    return false;
                Input = s_Timing.nodes[pChildObject->Id].arrival;
            }
            double Wire = pChildObject != nullptr && Abc_ObjIsCi(pChildObject)
                              ? 0.0
                              : std::hypot(InputX - X, InputY - Y);
            Arrival.logic = std::max(Arrival.logic, Input.logic + 1);
            Arrival.wire = std::max(Arrival.wire, Input.wire + Wire);
            return true;
        };

        if (timingProduced_[Entity])
        {
            const auto &Inputs = timingInputs_[Entity];
            if (!Accumulate(Inputs.first.entity, nullptr) ||
                !Accumulate(Inputs.second.entity, nullptr))
                return false;
        }
        else if (E.object != nullptr && Abc_ObjIsNode(E.object))
        {
            Abc_Obj_t *pFanin;
            int i;
            Abc_ObjForEachFanin(E.object, pFanin, i)
            {
                auto It = actualEntities_.find(Abc_ObjRegular(pFanin));
                int Child = It != actualEntities_.end() &&
                                    (entities_[It->second].movable || timingProduced_[It->second] ||
                                     timingBoundary_[It->second])
                                ? It->second
                                : -1;
                if (!Accumulate(Child, pFanin))
                    return false;
            }
        }
        timingEntityState_[Entity] = 2;
        timingEntityMemo_[Entity] = Arrival;
        *pResult = Arrival;
        return true;
    }

    bool TimingForObject(Abc_Obj_t *pObject, AgrEval_Arrival *pResult)
    {
        if (pObject == pRoot_)
            return TimingForEntity(resultEntity_, pResult);
        if (pObject->Id < 0 || pObject->Id >= static_cast<int>(s_Timing.nodes.size()) ||
            removed_.count(pObject))
            return false;
        auto &Timing = s_CandidateTiming.objects[pObject->Id];
        unsigned Generation = s_CandidateTiming.generation;
        if (Timing.affected != Generation)
        {
            *pResult = s_Timing.nodes[pObject->Id].arrival;
            return true;
        }
        if (Timing.memoStamp == Generation)
        {
            *pResult = Timing.memo;
            return true;
        }
        if (!s_CandidateTiming.Mark(Timing.visiting))
            return false;
        AgrEval_Arrival Arrival;
        if (Abc_ObjIsCo(pObject))
        {
            if (!TimingForObject(Abc_ObjFanin0(pObject), &Arrival))
                return false;
        }
        else if (Abc_ObjIsNode(pObject))
        {
            double X, Y;
            if (!TimingPosition(pObject, &X, &Y))
                return false;
            Abc_Obj_t *pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i)
            {
                AgrEval_Arrival Input;
                double InputX, InputY;
                if (!TimingForObject(pFanin, &Input) || !TimingPosition(pFanin, &InputX, &InputY))
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
        AGR_PROFILE_SCOPE(SeedPreparation);

        /* Only old nodes feeding the virtual result are relevant to its
           arrival. A reused node may move, and its old fanout path may feed
           another reused node, but following every fanout to the outputs is
           prohibitively expensive on high-fanout designs. Intersect that
           fanout path with the old fanin closure of the result's actual
           anchors. The topological-rank bound prunes ancestors that cannot
           depend on any moved node. Full-cone mode propagates other fanouts
           separately after evaluating the root. */
        auto &Moved = s_CandidateTiming.moved;
        int MinMovedRank = ABC_INFINITY;
        for (int Entity : movableEntities_)
        {
            Abc_Obj_t *pObject = entities_[Entity].object;
            if (pObject == nullptr || pObject == pRoot_ || removed_.count(pObject))
                continue;
            Moved.push_back(pObject);
            MinMovedRank = std::min(MinMovedRank, s_Timing.topoRank[pObject->Id]);
        }
        if ((0 == 1 || 1) && s_ExactTimingEvaluation)
        {
            // Logical root substitution affects these nodes even if no old
            // reused object moved. Seed them together before fanout evaluation.
            Abc_Obj_t *fo;
            int i;
            Abc_ObjForEachFanout(pRoot_, fo, i) if (Abc_ObjIsNode(fo))
            {
                Moved.push_back(fo);
                MinMovedRank = std::min(MinMovedRank, s_Timing.topoRank[fo->Id]);
            }
        }
        if (Moved.empty())
            return;

        auto &Backward = s_CandidateTiming.backward;
        if (!entities_[resultEntity_].virtualNode)
            Backward.push_back(entities_[resultEntity_].object);
        if (s_ExactTimingEvaluation)
        {
            Abc_Obj_t *pFanout;
            int k;
            Abc_ObjForEachFanout(pRoot_, pFanout, k) Backward.push_back(pFanout);
        }
        for (int Entity : virtualEntities_)
        {
            const auto &Inputs = virtualInputs_[Entity];
            for (int Child : {Inputs.first.entity, Inputs.second.entity})
                if (Child >= 0 && entities_[Child].object != nullptr)
                    Backward.push_back(entities_[Child].object);
        }
        while (!Backward.empty())
        {
            Abc_Obj_t *pObject = Backward.back();
            Backward.pop_back();
            if (pObject == nullptr || pObject == pRoot_ || removed_.count(pObject) ||
                s_Timing.topoRank[pObject->Id] < MinMovedRank ||
                !s_CandidateTiming.Mark(s_CandidateTiming.objects[pObject->Id].ancestor))
                continue;
            AGR_PROFILE_COUNT(SeedBackwardNodes, 1);
            if (Abc_ObjIsNode(pObject))
            {
                Abc_Obj_t *pFanin;
                int i;
                Abc_ObjForEachFanin(pObject, pFanin, i) Backward.push_back(pFanin);
            }
        }
        auto &Queue = s_CandidateTiming.queue;
        for (Abc_Obj_t *pObject : Moved)
            if (s_CandidateTiming.objects[pObject->Id].ancestor == s_CandidateTiming.generation)
                Queue.push_back(pObject);
        for (size_t Head = 0; Head < Queue.size(); ++Head)
        {
            Abc_Obj_t *pObject = Queue[Head];
            if (!s_CandidateTiming.Mark(s_CandidateTiming.objects[pObject->Id].affected))
                continue;
            AGR_PROFILE_COUNT(SeedForwardNodes, 1);
            Abc_Obj_t *pFanout;
            int i;
            Abc_ObjForEachFanout(pObject, pFanout,
                                 i) if (s_CandidateTiming.objects[pFanout->Id].ancestor ==
                                        s_CandidateTiming.generation) Queue.push_back(pFanout);
        }
    }

    bool PropagateTiming()
    {
        /* Only a changed arrival or moved coordinate can change a fanout.
           Process surviving nodes in old topological order so multiple
           changed fanins are present before their common fanout is scored. */
        using RankedId = std::pair<int, int>;
        std::priority_queue<RankedId, std::vector<RankedId>, std::greater<RankedId>> Queue;
        auto Schedule = [&](Abc_Obj_t *pObject)
        {
            if (pObject == nullptr || pObject == pRoot_ || removed_.count(pObject) ||
                !s_CandidateTiming.Mark(s_CandidateTiming.objects[pObject->Id].scheduled))
                return;
            Queue.emplace(s_Timing.topoRank[pObject->Id], pObject->Id);
        };
        for (int Entity : movableEntities_)
            if (entities_[Entity].object != nullptr)
                Schedule(entities_[Entity].object);
        Abc_Obj_t *pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout, i) Schedule(pFanout);
        while (!Queue.empty())
        {
            int Id = Queue.top().second;
            Queue.pop();
            Abc_Obj_t *pObject = Abc_NtkObj(pNtk_, Id);
            if (pObject == nullptr)
                return false;
            s_CandidateTiming.objects[Id].affected = s_CandidateTiming.generation;
            AgrEval_Arrival Arrival;
            if (!TimingForObject(pObject, &Arrival))
                return false;
            const AgrEval_TimingNode &Base = s_Timing.nodes[Id];
            bool Changed = Arrival.logic != Base.arrival.logic ||
                           !AgrEval_AlmostEqual(Arrival.wire, Base.arrival.wire);
            auto It = actualEntities_.find(pObject);
            if (It != actualEntities_.end() && entities_[It->second].movable)
            {
                const AgrEval_Geometry &Geometry = entities_[It->second].geometry;
                Changed |= !AgrEval_AlmostEqual(Geometry.x, Base.x) ||
                           !AgrEval_AlmostEqual(Geometry.y, Base.y);
            }
            if (!Changed)
                continue;
            Abc_Obj_t *pFanout;
            int k;
            Abc_ObjForEachFanout(pObject, pFanout, k) Schedule(pFanout);
        }
        return true;
    }

    bool EvaluateTiming()
    {
        AGR_PROFILE_SCOPE(CandidateTiming);
        if (!s_Timing.ready || s_Timing.network != pNtk_ ||
            pRoot_->Id >= static_cast<int>(s_Timing.nodes.size()))
            return false;
        s_CandidateTiming.Start(Abc_NtkObjNumMax(pNtk_));
        timingEntityState_.assign(entities_.size(), 0);
        timingEntityMemo_.resize(entities_.size());
        AgrEval_Arrival NewRoot;
        if (s_TimingEvaluation == 1 && !s_ExactTimingEvaluation)
        {
            /* Evaluate graph leaves and candidate core objects only. The
               full-cone mode below explores moved-node ancestors/fanouts. */
            if (!TimingForEntityLocal(resultEntity_, &NewRoot))
                return false;
        }
        else
        {
            PrepareTimingSeeds();
            if (!TimingForEntity(resultEntity_, &NewRoot))
                return false;
        }
        const AgrEval_TimingNode &OldRoot = s_Timing.nodes[pRoot_->Id];
        auto RootRequiredAt = [&](double RootX, double RootY, bool SourceIsCi, int *pLogic,
                                  double *pWire) -> bool
        {
            *pLogic = ABC_INFINITY;
            *pWire = std::numeric_limits<double>::infinity();
            Abc_Obj_t *pFanout;
            int i;
            Abc_ObjForEachFanout(pRoot_, pFanout, i)
            {
                if (pFanout->Id < 0 || pFanout->Id >= static_cast<int>(s_Timing.nodes.size()))
                    return false;
                const AgrEval_TimingNode &Fanout = s_Timing.nodes[pFanout->Id];
                int Logic = Abc_ObjIsCo(pFanout) ? 0 : 1;
                double Wire = 0.0;
                if (Abc_ObjIsNode(pFanout) && !SourceIsCi)
                {
                    double X, Y;
                    if (!TimingPosition(pFanout, &X, &Y))
                        return false;
                    Wire = std::hypot(RootX - X, RootY - Y);
                }
                if (Fanout.requiredLogic != ABC_INFINITY)
                    *pLogic = std::min(*pLogic, Fanout.requiredLogic - Logic);
                if (std::isfinite(Fanout.requiredWire))
                    *pWire = std::min(*pWire, Fanout.requiredWire - Wire);
            }
            return true;
        };
        int OldRequiredLogic;
        double OldRequiredWire;
        if (!RootRequiredAt(OldRoot.x, OldRoot.y, false, &OldRequiredLogic, &OldRequiredWire))
            return false;
        double OldSlack = std::min(static_cast<double>(OldRequiredLogic - OldRoot.arrival.logic),
                                   (OldRequiredWire - OldRoot.arrival.wire) / s_Timing.wireScale);
        int NewRequiredLogic;
        double NewRequiredWire;
        double RootX, RootY;
        if (!TimingEntityPosition(resultEntity_, &RootX, &RootY))
            return false;
        if (!RootRequiredAt(RootX, RootY, TimingIsCi(pRoot_), &NewRequiredLogic, &NewRequiredWire))
            return false;
        double NewSlack = std::min(static_cast<double>(NewRequiredLogic - NewRoot.logic),
                                   (NewRequiredWire - NewRoot.wire) / s_Timing.wireScale);
        if (!std::isfinite(OldSlack) || !std::isfinite(NewSlack))
            return false;
        if (s_TimingEvaluation == 1)
        {
            /* Use one continuous timing term for logic, geometric wire, and
               the immediate fanout boundary.  Separate criticalities keep an
               inactive model from inheriting weight from the active one.
               There is no timing bucket or hard slack cutoff: a candidate is
               accepted or rejected by the same node/HPWL/timing score. */
            double OldLogicSlack = OldRequiredLogic == ABC_INFINITY
                                       ? std::numeric_limits<double>::infinity()
                                       : static_cast<double>(OldRequiredLogic - OldRoot.arrival.logic);
            double NewLogicSlack = NewRequiredLogic == ABC_INFINITY
                                       ? std::numeric_limits<double>::infinity()
                                       : static_cast<double>(NewRequiredLogic - NewRoot.logic);
            double OldWireSlack = (OldRequiredWire - OldRoot.arrival.wire) / s_Timing.wireScale;
            double NewWireSlack = (NewRequiredWire - NewRoot.wire) / s_Timing.wireScale;
            double LogicCriticality = 1.0 / (1.0 + std::max(0.0, OldLogicSlack));
            double WireCriticality = 1.0 / (1.0 + std::max(0.0, OldWireSlack));
            auto Bounded = [](double Delta) { return std::max(-2.0, std::min(2.0, Delta)); };
            double OldFanoutSlack = std::numeric_limits<double>::infinity();
            double NewFanoutSlack = std::numeric_limits<double>::infinity();
            bool HasFanoutSlack = false;
            Abc_Obj_t *pFanout;
            int i;
            Abc_ObjForEachFanout(pRoot_, pFanout, i)
            {
                if (pFanout->Id < 0 || pFanout->Id >= static_cast<int>(s_Timing.nodes.size()))
                    continue;
                const AgrEval_TimingNode &FanoutTiming = s_Timing.nodes[pFanout->Id];
                if (FanoutTiming.requiredLogic == ABC_INFINITY &&
                    FanoutTiming.requiredWire == std::numeric_limits<double>::infinity())
                    continue;
                AgrEval_Arrival NewFanout;
                if (s_ExactTimingEvaluation)
                {
                    s_CandidateTiming.objects[pFanout->Id].affected = s_CandidateTiming.generation;
                    if (!TimingForObject(pFanout, &NewFanout))
                        return false;
                }
                else if (Abc_ObjIsCo(pFanout))
                    NewFanout = NewRoot;
                else if (Abc_ObjIsNode(pFanout))
                {
                    double FanoutX, FanoutY;
                    if (!TimingPosition(pFanout, &FanoutX, &FanoutY))
                        continue;
                    Abc_Obj_t *pFanin;
                    int k;
                    bool Complete = true;
                    Abc_ObjForEachFanin(pFanout, pFanin, k)
                    {
                        AgrEval_Arrival Input;
                        double InputX, InputY;
                        bool SourceIsCi;
                        if (pFanin == pRoot_)
                        {
                            Input = NewRoot;
                            InputX = RootX;
                            InputY = RootY;
                            SourceIsCi = TimingIsCi(pRoot_);
                        }
                        else
                        {
                            auto It = actualEntities_.find(pFanin);
                            if (It != actualEntities_.end() &&
                                (entities_[It->second].movable || timingProduced_[It->second] ||
                                 timingBoundary_[It->second]))
                            {
                                if (!TimingForEntityLocal(It->second, &Input) ||
                                    !TimingEntityPosition(It->second, &InputX, &InputY))
                                {
                                    Complete = false;
                                    break;
                                }
                            }
                            else
                            {
                                if (pFanin->Id < 0 ||
                                    pFanin->Id >= static_cast<int>(s_Timing.nodes.size()) ||
                                    !TimingPosition(pFanin, &InputX, &InputY))
                                {
                                    Complete = false;
                                    break;
                                }
                                Input = s_Timing.nodes[pFanin->Id].arrival;
                            }
                            SourceIsCi = Abc_ObjIsCi(pFanin);
                        }
                        double Wire =
                            SourceIsCi ? 0.0 : std::hypot(InputX - FanoutX, InputY - FanoutY);
                        NewFanout.logic = std::max(NewFanout.logic, Input.logic + 1);
                        NewFanout.wire = std::max(NewFanout.wire, Input.wire + Wire);
                    }
                    if (!Complete)
                        continue;
                }
                else
                    continue;

                double OldLocalSlack = std::min(
                    static_cast<double>(FanoutTiming.requiredLogic - FanoutTiming.arrival.logic),
                    (FanoutTiming.requiredWire - FanoutTiming.arrival.wire) / s_Timing.wireScale);
                double NewLocalSlack =
                    std::min(static_cast<double>(FanoutTiming.requiredLogic - NewFanout.logic),
                             (FanoutTiming.requiredWire - NewFanout.wire) / s_Timing.wireScale);
                if (!std::isfinite(OldLocalSlack) || !std::isfinite(NewLocalSlack))
                    continue;
                OldFanoutSlack = std::min(OldFanoutSlack, OldLocalSlack);
                NewFanoutSlack = std::min(NewFanoutSlack, NewLocalSlack);
                HasFanoutSlack = true;
            }
            if (s_ScoreMode == 2)
            {
                // The antiderivative of c(s)=1/(1+max(0,s)). Unlike
                // c(old)*clip(delta), this charges the entire transition
                // into negative slack and never saturates a timing loss.
                const double effectiveWeight = (s_TimingWeight);
                // Integrate criticality over the complete slack change.
                score_ += effectiveWeight * (AgrEval_SlackPotentialDelta(OldLogicSlack, NewLogicSlack) +
                                             AgrEval_SlackPotentialDelta(OldWireSlack, NewWireSlack));
                if (HasFanoutSlack)
                    score_ +=
                        effectiveWeight * AgrEval_SlackPotentialDelta(OldFanoutSlack, NewFanoutSlack);
                return std::isfinite(score_);
            }
            double FanoutTerm = 0.0;
            if (HasFanoutSlack)
            {
                double FanoutCriticality = 1.0 / (1.0 + std::max(0.0, OldFanoutSlack));
                FanoutTerm =
                    s_TimingWeight * FanoutCriticality * Bounded(NewFanoutSlack - OldFanoutSlack);
            }
            score_ += s_TimingWeight * LogicCriticality * Bounded(NewLogicSlack - OldLogicSlack) +
                      s_TimingWeight * WireCriticality * Bounded(NewWireSlack - OldWireSlack) +
                      FanoutTerm;
            return std::isfinite(score_);
        }
        if (!PropagateTiming())
            return false;

        int NewMaxLogic = 0;
        double NewMaxWire = 0.0;
        Abc_Obj_t *pFanout;
        int i;
        Abc_NtkForEachCo(pNtk_, pFanout, i)
        {
            AgrEval_Arrival Arrival;
            if (!TimingForObject(pFanout, &Arrival))
                return false;
            NewMaxLogic = std::max(NewMaxLogic, Arrival.logic);
            NewMaxWire = std::max(NewMaxWire, Arrival.wire);
        }
        double EndpointGain = static_cast<double>(s_Timing.maxLogic - NewMaxLogic) +
                              (s_Timing.maxWire - NewMaxWire) / s_Timing.wireScale;
        double Criticality = std::max(0.0, std::min(1.0, 1.0 - std::min(OldSlack, NewSlack)));
        /* The continuous term breaks ties near criticality; separate endpoint
           deltas reward improving either logic depth or placement-wire path. */
        score_ +=
            TimingBucket(NewSlack) - TimingBucket(OldSlack) +
            s_TimingWeight * Criticality * std::max(-2.0, std::min(2.0, NewSlack - OldSlack)) +
            kTimingEndpointWeight * EndpointGain;
        return std::isfinite(score_);
    }

    // Bounded coordinate descent over inherited cluster sites, starting from
    // the paper's attraction assignment. This is NOT globally optimal discrete
    // placement and does not certify that the final mapper uses these clusters.
    // Keep reused objects' tree placement, as in the paper. No extra candidates.

    void CollectRemoved()
    {
        AGR_SPEED_SCOPE(Other);
        if (AgrSpeed::Evaluation() && s_MffcCache.network == pNtk_ && s_MffcCache.root == pRoot_ &&
            s_MffcCache.version == s_ReadCache.version && s_MffcCache.traversal == pNtk_->nTravIds)
        {
            removed_ = s_MffcCache.removed;
            removedIds_ = s_MffcCache.ids;
            return;
        }
        AgrSpeed::WorkspaceVector<Abc_Obj_t *> Stack;
        Stack.push_back(pRoot_);
        while (!Stack.empty())
        {
            Abc_Obj_t *pObject = Stack.back();
            Stack.pop_back();
            if (!Abc_ObjIsNode(pObject) || !Abc_NodeIsTravIdCurrent(pObject) ||
                !removed_.insert(pObject).second)
                continue;
            removedIds_.push_back(pObject->Id);
            Abc_Obj_t *pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin,
                                i) if (Abc_ObjIsNode(pFanin) && Abc_NodeIsTravIdCurrent(pFanin))
                Stack.push_back(pFanin);
        }
        {
            s_MffcCache.network = pNtk_;
            s_MffcCache.root = pRoot_;
            s_MffcCache.version = s_ReadCache.version;
            s_MffcCache.traversal = pNtk_->nTravIds;
            s_MffcCache.removed = removed_;
            s_MffcCache.ids = removedIds_;
        }
    }

    int AddActual(Abc_Obj_t *pObject)
    {
        pObject = Abc_ObjRegular(pObject);
        auto It = actualEntities_.find(pObject);
        if (It != actualEntities_.end())
            return It->second;
        AgrEval_Entity Entity;
        Entity.object = pObject;
        Entity.hasPoint = AgrEval_ReadObjectGeometry(
                              pNtk_, pObject, &Entity.geometry.x, &Entity.geometry.y,
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

    int AddVirtual(int DecIndex, AgrEval_SymbolicLit Left, AgrEval_SymbolicLit Right)
    {
        AgrEval_Entity Entity;
        Entity.decIndex = DecIndex;
        Entity.virtualNode = true;
        Entity.hasPoint = true;
        Entity.geometry.width = Left.complement && Right.complement ? 2.0 : 3.0;
        const double SqrtTwo = std::sqrt(2.0);
        Entity.geometry.densityHalfX =
            std::max(0.5 * Entity.geometry.width, 0.5 * SqrtTwo * binSizeX_);
        Entity.geometry.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
        Entity.geometry.densityScale = Entity.geometry.width / (4.0 * Entity.geometry.densityHalfX *
                                                                Entity.geometry.densityHalfY);
        double RootX = 0.5 * width_, RootY = 0.5 * height_;
        Agr_ManReadObjectPosition(pNtk_, pRoot_, &RootX, &RootY);
        Entity.geometry.x = AgrEval_Clamp(RootX, Entity.geometry.densityHalfX,
                                         width_ - Entity.geometry.densityHalfX);
        Entity.geometry.y = AgrEval_Clamp(RootY, Entity.geometry.densityHalfY,
                                         height_ - Entity.geometry.densityHalfY);
        int Index = static_cast<int>(entities_.size());
        entities_.push_back(Entity);
        addedFanouts_.emplace_back();
        virtualInputs_.emplace_back(Left, Right);
        timingInputs_.emplace_back(Left, Right);
        timingProduced_.push_back(1);
        timingBoundary_.push_back(0);
        entityLevels_.push_back(1 +
                                std::max(entityLevels_[Left.entity], entityLevels_[Right.entity]));
        symbolicFanouts_.push_back(0);
        ++symbolicFanouts_[Left.entity];
        ++symbolicFanouts_[Right.entity];
        virtualEntities_.push_back(Index);
        return Index;
    }

    AgrEval_SymbolicLit ActualLiteral(Abc_Obj_t *pLiteral)
    {
        return AgrEval_SymbolicLit{AddActual(Abc_ObjRegular(pLiteral)),
                                  Abc_ObjIsComplement(pLiteral) != 0};
    }

    AgrEval_SymbolicLit ConstantLiteral(bool Value)
    {
        return AgrEval_SymbolicLit{AddActual(Abc_AigConst1(pNtk_)), !Value};
    }

    AgrEval_SymbolicLit SymbolicAnd(int DecIndex, AgrEval_SymbolicLit Left, AgrEval_SymbolicLit Right)
    {
        if (Left.entity == Right.entity)
            return Left.complement == Right.complement ? Left : ConstantLiteral(false);
        int Const = AddActual(Abc_AigConst1(pNtk_));
        if (Left.entity == Const)
            return Left.complement ? ConstantLiteral(false) : Right;
        if (Right.entity == Const)
            return Right.complement ? ConstantLiteral(false) : Left;

        int Lit0 = 2 * Left.entity + Left.complement;
        int Lit1 = 2 * Right.entity + Right.complement;
        if (Lit0 > Lit1)
            std::swap(Lit0, Lit1);
        auto Key = std::make_pair(Lit0, Lit1);
        /* ABC bypasses its structural hash table when either input has no
           fanouts.  Track fanouts created by earlier symbolic ANDs, including
           new nodes.  The most recently created virtual node is at the head
           of the real hash bin and takes precedence over an older match. */
        if (symbolicFanouts_[Left.entity] > 0 && symbolicFanouts_[Right.entity] > 0)
        {
            auto It = virtualHash_.find(Key);
            if (It != virtualHash_.end())
                return AgrEval_SymbolicLit{It->second, false};
            Abc_Obj_t *pLeft = entities_[Left.entity].object;
            Abc_Obj_t *pRight = entities_[Right.entity].object;
            if (pLeft != nullptr && pRight != nullptr)
            {
                /* A pre-existing input can have zero live fanouts but gain
                   one earlier in this virtual build.  ABC's lookup tests the
                   live count, so temporarily expose the simulated nonzero
                   count while querying the unchanged hash table. */
                bool LiftLeft = Abc_ObjFanoutNum(pLeft) == 0;
                bool LiftRight = Abc_ObjFanoutNum(pRight) == 0;
                if (LiftLeft)
                    ++pLeft->vFanouts.nSize;
                if (LiftRight)
                    ++pRight->vFanouts.nSize;
                Abc_Obj_t *pFound = Abc_AigAndLookup(static_cast<Abc_Aig_t *>(pNtk_->pManFunc),
                                                     Abc_ObjNotCond(pLeft, Left.complement),
                                                     Abc_ObjNotCond(pRight, Right.complement));
                if (LiftRight)
                    --pRight->vFanouts.nSize;
                if (LiftLeft)
                    --pLeft->vFanouts.nSize;
                if (pFound != nullptr)
                {
                    if (Abc_ObjRegular(pFound) == pRoot_)
                    {
                        validBuild_ = false;
                        return AgrEval_SymbolicLit{};
                    }
                    AgrEval_SymbolicLit Result = ActualLiteral(pFound);
                    /* Temporarily update every reused core object in candidate
                       order. Retain the symbolic inputs that
                       produced this reused AND so root timing can do the same
                       without walking its potentially huge old fanin cone. */
                    timingInputs_[Result.entity] = std::make_pair(Left, Right);
                    timingProduced_[Result.entity] = 1;
                    return Result;
                }
            }
        }
        int Entity = AddVirtual(DecIndex, Left, Right);
        virtualHash_[Key] = Entity;
        return AgrEval_SymbolicLit{Entity, false};
    }

    void BuildEntities()
    {
        AGR_SPEED_SCOPE(Entities);
        validBuild_ = true;
        decToEntity_.assign(pGraph_->nSize, -1);
        decPhase_.assign(pGraph_->nSize, 0);
        Dec_Node_t *pNode;
        int i;
        Dec_GraphForEachLeaf(pGraph_, pNode, i)
        {
            if (pNode->pFunc == nullptr ||
                Abc_ObjRegular(static_cast<Abc_Obj_t *>(pNode->pFunc)) == pRoot_)
            {
                validBuild_ = false;
                return;
            }
            AgrEval_SymbolicLit Literal = ActualLiteral(static_cast<Abc_Obj_t *>(pNode->pFunc));
            timingBoundary_[Literal.entity] = 1;
            decToEntity_[i] = Literal.entity;
            decPhase_[i] = Literal.complement;
        }
        Dec_GraphForEachNode(pGraph_, pNode, i)
        {
            int Child0 = pNode->eEdge0.Node;
            int Child1 = pNode->eEdge1.Node;
            if (Child0 >= i || Child1 >= i || decToEntity_[Child0] < 0 || decToEntity_[Child1] < 0)
            {
                validBuild_ = false;
                return;
            }
            AgrEval_SymbolicLit Left{decToEntity_[Child0],
                                    (pNode->eEdge0.fCompl ^ decPhase_[Child0]) != 0};
            AgrEval_SymbolicLit Right{decToEntity_[Child1],
                                     (pNode->eEdge1.fCompl ^ decPhase_[Child1]) != 0};
            AgrEval_SymbolicLit Result = SymbolicAnd(i, Left, Right);
            if (!validBuild_ || Result.entity < 0 || entityLevels_[Result.entity] > levelMax_)
            {
                validBuild_ = false;
                return;
            }
            decToEntity_[i] = Result.entity;
            decPhase_[i] = Result.complement;
        }
        if (Dec_GraphIsConst(pGraph_))
            resultEntity_ = AddActual(Abc_AigConst1(pNtk_));
        else
        {
            /* Dec_GraphToNetwork() returns its last AND, rather than indexing
               eRoot, for a nontrivial graph.  Accept only graphs for which
               those two descriptions are identical. */
            if (pGraph_->eRoot.Node >= static_cast<unsigned>(decToEntity_.size()) ||
                (pGraph_->nSize > pGraph_->nLeaves &&
                 pGraph_->eRoot.Node != static_cast<unsigned>(pGraph_->nSize - 1)))
            {
                validBuild_ = false;
                return;
            }
            resultEntity_ = decToEntity_[pGraph_->eRoot.Node];
        }
        if (resultEntity_ < 0 || entities_[resultEntity_].object == pRoot_)
        {
            validBuild_ = false;
            return;
        }
        int ResultPhase = Dec_GraphIsConst(pGraph_) ? 0 : decPhase_[pGraph_->eRoot.Node];
        resultComplement_ = ResultPhase ^ Dec_GraphIsComplement(pGraph_) ^ rootComplement_;

        for (int Parent : virtualEntities_)
        {
            const auto &Inputs = virtualInputs_[Parent];
            addedFanouts_[Inputs.first.entity].push_back(Parent);
            addedFanouts_[Inputs.second.entity].push_back(Parent);
        }

        if (resultEntity_ >= 0)
        {
            Abc_Obj_t *pFanout;
            int k;
            Abc_ObjForEachFanout(pRoot_, pFanout, k) if (Abc_ObjIsNode(pFanout))
            {
                int Fanout = AddActual(pFanout);
                if (entities_[Fanout].hasPoint)
                    addedFanouts_[resultEntity_].push_back(Fanout);
            }
        }
    }

    void ComputeRemovedAfterMaterialization()
    {
        AGR_SPEED_SCOPE(Materialization);
        /* New ANDs are created before ABC replaces the old root.  Every old
           MFFC node used by a new AND, or used as the replacement result,
           gains a surviving fanout.  Its old MFFC fanin cone survives too. */
        AgrEval_ObjectSet Retained;
        std::vector<Abc_Obj_t *> Stack;
        for (int NewEntity : virtualEntities_)
        {
            const auto &Inputs = virtualInputs_[NewEntity];
            for (int Child : {Inputs.first.entity, Inputs.second.entity})
            {
                Abc_Obj_t *pChild = entities_[Child].object;
                if (pChild != nullptr && removed_.count(pChild))
                    Stack.push_back(pChild);
            }
        }
        Abc_Obj_t *pResult = entities_[resultEntity_].object;
        if (pResult != nullptr && removed_.count(pResult))
            Stack.push_back(pResult);
        while (!Stack.empty())
        {
            Abc_Obj_t *pObject = Stack.back();
            Stack.pop_back();
            if (!Retained.insert(pObject).second)
                continue;
            Abc_Obj_t *pFanin;
            int i;
            Abc_ObjForEachFanin(pObject, pFanin, i) if (removed_.count(Abc_ObjRegular(pFanin)))
                Stack.push_back(Abc_ObjRegular(pFanin));
        }
        for (Abc_Obj_t *pObject : Retained)
            removed_.erase(pObject);
        // Pointer-hash iteration changes with allocation/ASLR. Numeric sums,
        // density updates and placement staging must use stable object IDs.
        orderedRemoved_.assign(removed_.begin(), removed_.end());
        std::sort(orderedRemoved_.begin(), orderedRemoved_.end(),
                  [](Abc_Obj_t *a, Abc_Obj_t *b) { return a->Id < b->Id; });
        removedIds_.clear();
        for (Abc_Obj_t *pObject : orderedRemoved_)
            removedIds_.push_back(pObject->Id);
        actualGain_ = static_cast<int>(removed_.size()) - VirtualCount();
        if (!removed_.count(pRoot_) || (actualGain_ < -0))
            validBuild_ = false;
    }

    // Each fixed-pin bounding box is a lower bound on that net's HPWL,
    // independently of placement/density constraints. Frozen reused pins add
    // further fixed terminals for the estimator's anchored component.

    double AreaDeltaBeforePlacement() const
    {
        double delta = 0;
        for (auto *v : orderedRemoved_)
        {
            double width;
            if (!AgrEval_ReadObjectGeometry(pNtk_, v, nullptr, nullptr, &width, nullptr, nullptr,
                                           nullptr))
                return -INFINITY;
            delta -= width;
        }
        for (int v : virtualEntities_)
            delta += entities_[v].geometry.width;
        Abc_Obj_t *fanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, fanout, i)
        {
            if (!Abc_ObjIsNode(fanout))
                continue;
            double width;
            if (!AgrEval_ReadObjectGeometry(pNtk_, fanout, nullptr, nullptr, &width, nullptr,
                                           nullptr, nullptr))
                return -INFINITY;
            int index = Abc_ObjFanin0(fanout) == pRoot_   ? 0
                        : Abc_ObjFanin1(fanout) == pRoot_ ? 1
                                                          : -1;
            if (index < 0)
                return -INFINITY;
            bool c0 = Abc_ObjFaninC0(fanout), c1 = Abc_ObjFaninC1(fanout);
            if (index == 0)
                c0 ^= resultComplement_;
            else
                c1 ^= resultComplement_;
            delta += (c0 && c1 ? 2.0 : 3.0) - width;
        }
        return delta;
    }

    void BuildMovables()
    {
        std::unordered_set<int> Seen;
        std::vector<unsigned char> seenFlags((entities_.size()));
        auto first = [&](int id)
        {
            bool fresh = !seenFlags[id];
            seenFlags[id] = 1;
            return fresh;
        };
        Dec_Node_t *pNode;
        int i;
        Dec_GraphForEachNode(pGraph_, pNode, i)
        {
            int Entity = decToEntity_[i];
            if (Entity < 0 || !first(Entity))
                continue;
            Abc_Obj_t *pObject = entities_[Entity].object;
            if (entities_[Entity].hasPoint &&
                (entities_[Entity].virtualNode || !removed_.count(pObject)))
            {
                entities_[Entity].movable = true;
                movableEntities_.push_back(Entity);
            }
        }
        if (resultEntity_ >= 0 && first(resultEntity_) && entities_[resultEntity_].hasPoint &&
            !removed_.count(entities_[resultEntity_].object))
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
        AGR_SPEED_SCOPE(Cascade);
        /* Abc_AigReplace updates each root fanout in place unless replacing
           the root makes that fanout structurally hash to an existing node.
           In the latter case, replacement propagates beyond the candidate
           boundary and invalidates this plan's exact affected-net delta.
           Reject such a candidate before it mutates the live AIG. */
        if (resultEntity_ < 0 || entities_[resultEntity_].virtualNode ||
            entities_[resultEntity_].object == nullptr)
            return false;
        Abc_Obj_t *pReplacement =
            Abc_ObjNotCond(entities_[resultEntity_].object, resultComplement_);
        Abc_Aig_t *pAig = static_cast<Abc_Aig_t *>(pNtk_->pManFunc);
        std::set<std::pair<int, int>> UpdatedFanoutKeys;
        Abc_Obj_t *pFanout;
        int k;
        Abc_ObjForEachFanout(pRoot_, pFanout, k)
        {
            if (!Abc_ObjIsNode(pFanout))
                continue;
            int FaninIndex = Vec_IntFind(&pFanout->vFanins, pRoot_->Id);
            if (FaninIndex < 0)
                return true;
            Abc_Obj_t *pChangedFanin =
                Abc_ObjNotCond(pReplacement, Abc_ObjFaninC(pFanout, FaninIndex));
            Abc_Obj_t *pOtherFanin = Abc_ObjChild(pFanout, FaninIndex ^ 1);
            Abc_Obj_t *pExisting = Abc_AigAndLookup(pAig, pChangedFanin, pOtherFanin);
            if (pExisting != nullptr && Abc_ObjRegular(pExisting) != pFanout)
                return true;
            int Key0 = 2 * Abc_ObjRegular(pChangedFanin)->Id + Abc_ObjIsComplement(pChangedFanin);
            int Key1 = 2 * Abc_ObjRegular(pOtherFanin)->Id + Abc_ObjIsComplement(pOtherFanin);
            if (Key0 > Key1)
                std::swap(Key0, Key1);
            if (!UpdatedFanoutKeys.emplace(Key0, Key1).second)
                return true;
            auto First = actualEntities_.find(Abc_ObjRegular(pChangedFanin));
            auto Second = actualEntities_.find(Abc_ObjRegular(pOtherFanin));
            if (First != actualEntities_.end() && Second != actualEntities_.end())
            {
                int Lit0 = 2 * First->second + Abc_ObjIsComplement(pChangedFanin);
                int Lit1 = 2 * Second->second + Abc_ObjIsComplement(pOtherFanin);
                if (Lit0 > Lit1)
                    std::swap(Lit0, Lit1);
                if (virtualHash_.count(std::make_pair(Lit0, Lit1)))
                    return true;
            }
        }
        return false;
    }

    template <class V> static void SortUnique(V &Values)
    {
        std::sort(Values.begin(), Values.end());
        Values.erase(std::unique(Values.begin(), Values.end()), Values.end());
    }

    static bool IsModeledDriver(Abc_Obj_t *pObject)
    {
        return pObject != nullptr && (Abc_ObjIsNode(pObject) || Abc_ObjIsCi(pObject));
    }

    double CurrentNetHpwl(Abc_Obj_t *pDriver) const
    {
        // Acquire the entry again when storing: geometry reads can grow the
        // ID-indexed array while traversing a driver's newer fanouts.
        if (s_ReadCache.Get(pDriver->Id).hpwlStamp == s_ReadCache.version)
            return s_ReadCache.Get(pDriver->Id).hpwl;
        double MinX = 0.0, MaxX = 0.0, MinY = 0.0, MaxY = 0.0;
        bool Found = false;
        auto Add = [&](Abc_Obj_t *Object)
        {
            double X, Y;
            if (!AgrEval_ReadObjectGeometry(pNtk_, Object, &X, &Y, nullptr, nullptr, nullptr,
                                           nullptr))
                return;
            if (!Found)
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
        Abc_Obj_t *Fanout;
        int k;
        Abc_ObjForEachFanout(pDriver, Fanout, k) if (Abc_ObjIsNode(Fanout)) Add(Fanout);
        auto &C = s_ReadCache.Get(pDriver->Id);
        C.hpwl = Found ? MaxX - MinX + MaxY - MinY : 0.0;
        C.hpwlStamp = s_ReadCache.version;
        return C.hpwl;
    }

    void AddPin(AgrEval_LocalNet &Net, int Entity)
    {
        if (Entity < 0 || Entity >= static_cast<int>(entities_.size()) ||
            !entities_[Entity].hasPoint)
            return;
        if (entities_[Entity].movable)
            Net.pins.push_back(Entity);
        else
            Net.AddFixed(entities_[Entity].geometry.x, entities_[Entity].geometry.y);
    }

    void AddNetFast(AgrEval_LocalNet Net)
    {
        SortUnique(Net.pins);
        if (Net.pins.size() + Net.fixedCount >= 2)
            nets_.push_back(std::move(Net));
    }

    void BuildNetsFast()
    {
        AGR_SPEED_SCOPE(Nets);
        /* A is a set of affected DRIVER NETS, not a set of removed nodes.
           A surviving boundary driver's fanout pins can change even though
           the driver itself is present before and after.  The post-edit A'
           consists of these surviving drivers plus the virtual new drivers.
           Commit-time identity and boundary checks ensure that every net
           outside A/A' has identical pins and fixed coordinates. */
        std::vector<Abc_Obj_t *> OrderedDrivers;
        OrderedDrivers.reserve(3 * orderedRemoved_.size() + 2 * virtualEntities_.size() +
                               3 * movableEntities_.size() + 1);
        for (Abc_Obj_t *pRemoved : orderedRemoved_)
        {
            OrderedDrivers.push_back(pRemoved);
            Abc_Obj_t *pFanin;
            int k;
            Abc_ObjForEachFanin(pRemoved, pFanin, k)
                OrderedDrivers.push_back(Abc_ObjRegular(pFanin));
        }
        for (int Entity : virtualEntities_)
        {
            const auto &Inputs = virtualInputs_[Entity];
            int Children[2] = {Inputs.first.entity, Inputs.second.entity};
            for (int Child : Children)
                if (Child >= 0 && entities_[Child].object)
                    OrderedDrivers.push_back(entities_[Child].object);
        }
        for (int Entity : movableEntities_)
        {
            Abc_Obj_t *pObject = entities_[Entity].object;
            if (pObject == nullptr)
                continue;
            OrderedDrivers.push_back(pObject);
            Abc_Obj_t *pFanin;
            int k;
            Abc_ObjForEachFanin(pObject, pFanin, k)
                OrderedDrivers.push_back(Abc_ObjRegular(pFanin));
        }
        if (resultEntity_ >= 0 && entities_[resultEntity_].object)
            OrderedDrivers.push_back(entities_[resultEntity_].object);

        std::sort(OrderedDrivers.begin(), OrderedDrivers.end(),
                  [](Abc_Obj_t *a, Abc_Obj_t *b) { return a->Id < b->Id; });
        OrderedDrivers.erase(std::unique(OrderedDrivers.begin(), OrderedDrivers.end()),
                             OrderedDrivers.end());

        for (Abc_Obj_t *pDriver : OrderedDrivers)
            if (IsModeledDriver(pDriver))
                hpwlSaved_ += CurrentNetHpwl(pDriver);

        for (Abc_Obj_t *pDriver : OrderedDrivers)
        {
            if (removed_.count(pDriver) || !IsModeledDriver(pDriver))
                continue;
            int Driver = AddActual(pDriver);
            AgrEval_LocalNet Net;
            AddPin(Net, Driver);
            Abc_Obj_t *pFanout;
            int k;
            Abc_ObjForEachFanout(pDriver, pFanout, k)
            {
                if (!Abc_ObjIsNode(pFanout) || removed_.count(pFanout))
                    continue;
                auto It = actualEntities_.find(pFanout);
                if (It != actualEntities_.end())
                    AddPin(Net, It->second);
                else
                {
                    double X, Y;
                    if (AgrEval_ReadObjectGeometry(pNtk_, pFanout, &X, &Y, nullptr, nullptr, nullptr,
                                                  nullptr))
                        Net.AddFixed(X, Y);
                }
            }
            for (int Fanout : addedFanouts_[Driver])
                AddPin(Net, Fanout);
            AddNetFast(std::move(Net));
        }

        for (int Driver : virtualEntities_)
        {
            AgrEval_LocalNet Net;
            AddPin(Net, Driver);
            for (int Fanout : addedFanouts_[Driver])
                AddPin(Net, Fanout);
            AddNetFast(std::move(Net));
        }

        incidentNets_.assign(entities_.size(), {});
        for (int Net = 0; Net < static_cast<int>(nets_.size()); ++Net)
            for (int Pin : nets_[Net].pins)
                if (entities_[Pin].movable)
                    incidentNets_[Pin].push_back(Net);
    }

    void InitializeDensity()
    {
        AGR_SPEED_SCOPE(Density);
        densityPresent_.assign(entities_.size(), 0);
        for (Abc_Obj_t *pRemoved : orderedRemoved_)
        {
            AgrEval_Geometry Geometry;
            if (AgrEval_ReadObjectGeometry(pNtk_, pRemoved, &Geometry.x, &Geometry.y,
                                          &Geometry.width, &Geometry.densityHalfX,
                                          &Geometry.densityHalfY, &Geometry.densityScale))
            {
                density_->Add(Geometry, -1.0);
            }
            else
                validBuild_ = false;
        }
        for (int Entity : movableEntities_)
            if (!entities_[Entity].virtualNode)
                density_->Add(entities_[Entity].geometry, -1.0);
        Abc_Obj_t *pFanout;
        int i;
        Abc_ObjForEachFanout(pRoot_, pFanout, i)
        {
            if (!Abc_ObjIsNode(pFanout))
                continue;
            AgrEval_Geometry OldGeometry;
            if (!AgrEval_ReadObjectGeometry(pNtk_, pFanout, &OldGeometry.x, &OldGeometry.y,
                                           &OldGeometry.width, &OldGeometry.densityHalfX,
                                           &OldGeometry.densityHalfY, &OldGeometry.densityScale))
            {
                validBuild_ = false;
                continue;
            }
            int FaninIndex = Abc_ObjFanin0(pFanout) == pRoot_   ? 0
                             : Abc_ObjFanin1(pFanout) == pRoot_ ? 1
                                                                : -1;
            if (FaninIndex < 0)
            {
                validBuild_ = false;
                continue;
            }
            bool Compl0 = Abc_ObjFaninC0(pFanout);
            bool Compl1 = Abc_ObjFaninC1(pFanout);
            if (FaninIndex == 0)
                Compl0 ^= resultComplement_;
            else
                Compl1 ^= resultComplement_;
            double NewWidth = Compl0 && Compl1 ? 2.0 : 3.0;
            if (AgrEval_AlmostEqual(NewWidth, OldGeometry.width))
                continue;
            AgrEval_Geometry NewGeometry = OldGeometry;
            NewGeometry.width = NewWidth;
            const double SqrtTwo = std::sqrt(2.0);
            NewGeometry.densityHalfX = std::max(0.5 * NewWidth, 0.5 * SqrtTwo * binSizeX_);
            NewGeometry.densityHalfY = std::max(0.5, 0.5 * SqrtTwo * binSizeY_);
            NewGeometry.densityScale =
                NewWidth / (4.0 * NewGeometry.densityHalfX * NewGeometry.densityHalfY);
            auto It = actualEntities_.find(pFanout);
            if (It != actualEntities_.end() && entities_[It->second].movable)
                entities_[It->second].geometry = NewGeometry;
            else
            {
                density_->Add(OldGeometry, -1.0);
                density_->Add(NewGeometry, 1.0);
            }
        }
    }

    void ClampRectangle(int Entity, AgrEval_Rectangle *pRectangle) const
    {
        const AgrEval_Geometry &Geometry = entities_[Entity].geometry;
        pRectangle->lowX =
            AgrEval_Clamp(pRectangle->lowX, Geometry.densityHalfX, width_ - Geometry.densityHalfX);
        pRectangle->highX =
            AgrEval_Clamp(pRectangle->highX, Geometry.densityHalfX, width_ - Geometry.densityHalfX);
        pRectangle->lowY =
            AgrEval_Clamp(pRectangle->lowY, Geometry.densityHalfY, height_ - Geometry.densityHalfY);
        pRectangle->highY =
            AgrEval_Clamp(pRectangle->highY, Geometry.densityHalfY, height_ - Geometry.densityHalfY);
        if (pRectangle->lowX > pRectangle->highX)
            std::swap(pRectangle->lowX, pRectangle->highX);
        if (pRectangle->lowY > pRectangle->highY)
            std::swap(pRectangle->lowY, pRectangle->highY);
    }

    AgrEval_Rectangle PropagatedRectangle(int Entity, const std::vector<AgrEval_Rectangle> &Regions,
                                         const std::vector<unsigned char> *pAssigned) const
    {
        AGR_SPEED_SCOPE(Median);
        std::vector<std::pair<double, double>> XIntervals;
        std::vector<std::pair<double, double>> YIntervals;
        AgrSpeed::Scratch<double, 16> xs((2 * incidentNets_[Entity].size())),
            ys((2 * incidentNets_[Entity].size()));
        size_t used = 0;
        for (int NetIndex : incidentNets_[Entity])
        {
            const AgrEval_LocalNet &Net = nets_[NetIndex];
            bool Found = Net.fixedCount > 0;
            double MinX = Found ? Net.fixedMinX : std::numeric_limits<double>::max();
            double MaxX = Found ? Net.fixedMaxX : std::numeric_limits<double>::lowest();
            double MinY = Found ? Net.fixedMinY : std::numeric_limits<double>::max();
            double MaxY = Found ? Net.fixedMaxY : std::numeric_limits<double>::lowest();
            for (int Pin : Net.pins)
            {
                if (Pin == Entity)
                    continue;
                const AgrEval_Entity &Other = entities_[Pin];
                if (!Other.movable || (pAssigned != nullptr && (*pAssigned)[Pin]))
                {
                    MinX = std::min(MinX, Other.geometry.x);
                    MaxX = std::max(MaxX, Other.geometry.x);
                    MinY = std::min(MinY, Other.geometry.y);
                    MaxY = std::max(MaxY, Other.geometry.y);
                    Found = true;
                }
                else if (Regions[Pin].valid)
                {
                    MinX = std::min(MinX, Regions[Pin].lowX);
                    MaxX = std::max(MaxX, Regions[Pin].highX);
                    MinY = std::min(MinY, Regions[Pin].lowY);
                    MaxY = std::max(MaxY, Regions[Pin].highY);
                    Found = true;
                }
            }
            if (Found)
            {
                {
                    xs[used] = MinX;
                    ys[used++] = MinY;
                    xs[used] = MaxX;
                    ys[used++] = MaxY;
                }
            }
        }
        AgrEval_Rectangle Result;
        if (used == 0)
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
        if (AgrEval_AlmostEqual(Low, High))
        {
            Result.values[Result.count++] = Low;
            return Result;
        }
        double Step = (High - Low) / kRegionDivisions;
        int Count = kRegionDivisions;
        if (Step < kMinimumRegionStep)
        {
            Step = kMinimumRegionStep;
            Count = static_cast<int>((High - Low) / kMinimumRegionStep);
        }
        for (int i = 0; i <= Count; ++i)
            Result.values[Result.count++] = Low + i * Step;
        return Result;
    }

    double PlaceInRectangle(int Entity, const AgrEval_Rectangle &Rectangle)
    {
        AGR_SPEED_SCOPE(DensitySamples);
        AgrEval_Geometry &Geometry = entities_[Entity].geometry;
        double OldX = Geometry.x, OldY = Geometry.y;
        if (densityPresent_[Entity])
            density_->Add(Geometry, -1.0);
        RegionSamples XSamples = Samples(Rectangle.lowX, Rectangle.highX);
        RegionSamples YSamples = Samples(Rectangle.lowY, Rectangle.highY);
        std::array<AgrEval_DensityWorkspace::AxisFootprint, kRegionDivisions + 1> XFootprints,
            YFootprints;
        for (int i = 0; i < XSamples.count; ++i)
            XFootprints[i] = density_->PrepareAxis(XSamples.values[i], Geometry.densityHalfX, true);
        for (int i = 0; i < YSamples.count; ++i)
            YFootprints[i] =
                density_->PrepareAxis(YSamples.values[i], Geometry.densityHalfY, false);
        double CenterX = 0.5 * (Rectangle.lowX + Rectangle.highX);
        double CenterY = 0.5 * (Rectangle.lowY + Rectangle.highY);
        double BestX = CenterX, BestY = CenterY;
        double BestDensity = std::numeric_limits<double>::max();
        double BestCenterDistance = std::numeric_limits<double>::max();
        for (int i = 0; i < XSamples.count; ++i)
            for (int j = 0; j < YSamples.count; ++j)
            {
                double X = XSamples.values[i], Y = YSamples.values[j];
                double Density =
                    (density_->EvaluateAddition(Geometry, XFootprints[i], YFootprints[j]));
                double CenterDistance =
                    (X - CenterX) * (X - CenterX) + (Y - CenterY) * (Y - CenterY);
                bool Better = AgrEval_AlmostLess(Density, BestDensity) ||
                              (AgrEval_AlmostEqual(Density, BestDensity) &&
                               AgrEval_AlmostLess(CenterDistance, BestCenterDistance));
                if (Better)
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
        AGR_SPEED_SCOPE(Placement);
        /* The forward pass propagates HPWL-optimal rectangles from candidate
           leaves toward the root.  The reverse pass fixes one density-aware
           point per rectangle while using already fixed fanouts as anchors.
           This is exact for each tree elimination step.  Reconvergent DAGs
           can expose more than one virtual pin on a net, so the seed is a
           heuristic for those cases; LocalHpwl measures its actual cost. */
        std::vector<AgrEval_Rectangle> Regions(entities_.size());
        for (int Entity : movableEntities_)
            Regions[Entity] = PropagatedRectangle(Entity, Regions, nullptr);

        std::vector<unsigned char> Assigned(entities_.size(), 0);
        for (auto It = movableEntities_.rbegin(); It != movableEntities_.rend(); ++It)
        {
            int Entity = *It;
            AgrEval_Rectangle Region = PropagatedRectangle(Entity, Regions, &Assigned);
            if (!Region.valid)
                Region = Regions[Entity];
            if (!Region.valid)
            {
                const AgrEval_Geometry &Geometry = entities_[Entity].geometry;
                Region = AgrEval_Rectangle{Geometry.x, Geometry.x, Geometry.y, Geometry.y, true};
            }
            PlaceInRectangle(Entity, Region);
            Assigned[Entity] = 1;
        }
        // Refine reconvergent/reused-node geometry using current neighbor points.
        // Every candidate and its commit execute the same deterministic sweeps.
        for (int pass = 0; pass < 0; ++pass)
        {
            for (size_t at = 0; at < movableEntities_.size(); ++at)
            {
                int entity = movableEntities_[pass % 2 ? movableEntities_.size() - 1 - at : at];
                AgrEval_Rectangle region = PropagatedRectangle(entity, Regions, &Assigned);
                if (region.valid)
                    PlaceInRectangle(entity, region);
            }
        }
        // Opt-in HPWL/density tradeoff outside the wire-optimal rectangle.
        // Choosing only the least dense point *inside* that rectangle cannot
        // prevent compression when the whole rectangle is already crowded.
        // All trials remain in this private plan; only the selected feasible
        // graph and its final positions can be committed by the caller.
    }

    // Preserve freed physical capacity when a wire-optimal seed is too dense.
    // Candidate-private geometry only; there is no graph rollback or global solve.

    void RepairCapacity(double area, double overflow)
    {
        std::vector<AgrEval_Geometry> sites;
        for (auto *v : orderedRemoved_)
        {
            AgrEval_Geometry g;
            if (AgrEval_ReadObjectGeometry(pNtk_, v, &g.x, &g.y, &g.width, &g.densityHalfX,
                                          &g.densityHalfY, &g.densityScale))
                sites.push_back(g);
        }
        std::vector<std::pair<double, double>> desired(entities_.size());
        for (int id : movableEntities_)
        {
            auto &g = entities_[id].geometry;
            desired[id] = {g.x, g.y};
            if (densityPresent_[id])
                density_->Add(g, -1.);
            densityPresent_[id] = 0;
        }
        // Reused objects retain their original sites; new objects inherit the
        // closest sufficiently large removed site, with deterministic ties.
        for (int id : movableEntities_)
            if (!entities_[id].virtualNode)
            {
                auto &e = entities_[id];
                Agr_ManReadObjectPosition(pNtk_, e.object, &e.geometry.x, &e.geometry.y);
                density_->Add(e.geometry, 1.);
                densityPresent_[id] = 1;
            }
        std::vector<int> order(virtualEntities_.begin(), virtualEntities_.end());
        std::stable_sort(order.begin(), order.end(), [&](int a, int b)
                         { return entities_[a].geometry.width > entities_[b].geometry.width; });
        std::vector<unsigned char> used(sites.size());
        for (int id : order)
        {
            auto &g = entities_[id].geometry;
            int best = -1;
            double bestCost = INFINITY;
            for (size_t i = 0; i < sites.size(); ++i)
                if (!used[i])
                {
                    double cost = std::abs(sites[i].x - desired[id].first) +
                                  std::abs(sites[i].y - desired[id].second);
                    if (sites[i].width + 1e-9 < g.width)
                        cost += 1000 * (width_ + height_);
                    if (cost < bestCost)
                    {
                        best = int(i);
                        bestCost = cost;
                    }
                }
            if (best >= 0)
            {
                used[best] = 1;
                g.x = sites[best].x;
                g.y = sites[best].y;
            }
            g.x = AgrEval_Clamp(g.x, g.densityHalfX, width_ - g.densityHalfX);
            g.y = AgrEval_Clamp(g.y, g.densityHalfY, height_ - g.densityHalfY);
            density_->Add(g, 1.);
            densityPresent_[id] = 1;
        }

        const double limit = std::max(.099, overflow);
        auto excess = [&]()
        {
            return std::max(0., overflow * area + density_->OverflowDelta() -
                                    limit * (area + density_->ExactAreaDelta()));
        };
        // Coordinate search first restores feasibility, then minimizes actual
        // affected-net HPWL without spending more overflow than the limit.
        const int sweeps = std::max(1, std::min(4, 1));
        for (int sweep = 0; sweep < sweeps; ++sweep)
            for (auto it = movableEntities_.rbegin(); it != movableEntities_.rend(); ++it)
            {
                int id = *it;
                auto &g = entities_[id].geometry;
                double x = g.x, y = g.y, bx = x, by = y, be = excess(), bh = LocalHpwl();
                const double dx = binSizeX_ * .5, dy = binSizeY_ * .5;
                std::vector<std::pair<double, double>> trials{
                    {desired[id].first, desired[id].second},
                    {(x + desired[id].first) * .5, (y + desired[id].second) * .5},
                    {x - dx, y},
                    {x + dx, y},
                    {x, y - dy},
                    {x, y + dy}};
                for (const auto &site : sites)
                    trials.emplace_back(site.x, site.y);
                density_->Add(g, -1.);
                for (auto t : trials)
                {
                    g.x = AgrEval_Clamp(t.first, g.densityHalfX, width_ - g.densityHalfX);
                    g.y = AgrEval_Clamp(t.second, g.densityHalfY, height_ - g.densityHalfY);
                    density_->Add(g, 1.);
                    double e = excess(), h = LocalHpwl();
                    if (e < be - 1e-9 || (e <= be + 1e-9 && h < bh - 1e-9))
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
        AGR_SPEED_SCOPE(Hpwl);
        double Result = 0.0;
        for (const AgrEval_LocalNet &Net : nets_)
        {
            double MinX = Net.fixedMinX, MaxX = Net.fixedMaxX;
            double MinY = Net.fixedMinY, MaxY = Net.fixedMaxY;
            bool Found = Net.fixedCount > 0;
            for (int Pin : Net.pins)
            {
                const AgrEval_Geometry &Geometry = entities_[Pin].geometry;
                if (!Found)
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
            if (Found)
                Result += MaxX - MinX + MaxY - MinY;
        }
        return Result;
    }

    Abc_Obj_t *pRoot_ = nullptr;
    Abc_Ntk_t *pNtk_ = nullptr;
    Dec_Graph_t *pGraph_ = nullptr;
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

    std::vector<Abc_Obj_t *> topologyDrivers_;
    double score_ = -std::numeric_limits<double>::infinity();
    bool validBuild_ = false;
    bool valid_ = false;

    bool rootComplement_ = false;
    bool resultComplement_ = false;
    int resultEntity_ = -1;
    AgrEval_ObjectSet removed_;
    AgrSpeed::WorkspaceVector<Abc_Obj_t *> orderedRemoved_;
    AgrSpeed::WorkspaceVector<int> removedIds_;
    AgrEval_EntityIndex actualEntities_;
    AgrSpeed::WorkspaceVector<AgrEval_Entity> entities_;
    AgrSpeed::WorkspaceVector<int> decToEntity_;
    AgrSpeed::WorkspaceVector<unsigned char> decPhase_;
    AgrSpeed::WorkspaceVector<int> entityLevels_;
    AgrSpeed::WorkspaceVector<int> symbolicFanouts_;
    AgrSpeed::WorkspaceVector<std::pair<AgrEval_SymbolicLit, AgrEval_SymbolicLit>> virtualInputs_;
    AgrSpeed::WorkspaceVector<std::pair<AgrEval_SymbolicLit, AgrEval_SymbolicLit>> timingInputs_;
    AgrSpeed::WorkspaceVector<unsigned char> timingProduced_;
    AgrSpeed::WorkspaceVector<unsigned char> timingBoundary_;
    std::map<std::pair<int, int>, int> virtualHash_;
    AgrSpeed::WorkspaceVector<int> virtualEntities_;
    AgrSpeed::WorkspaceVector<AgrEval_Cluster> clusters_;
    AgrSpeed::WorkspaceVector<int> movableEntities_;
    AgrSpeed::WorkspaceVector<AgrSpeed::IntList> addedFanouts_;
    AgrSpeed::WorkspaceVector<AgrEval_LocalNet> nets_;
    AgrSpeed::WorkspaceVector<AgrSpeed::IntList> incidentNets_;
    AgrSpeed::WorkspaceVector<unsigned char> densityPresent_;
    std::unique_ptr<AgrEval_DensityWorkspace> density_;
    AgrSpeed::WorkspaceVector<unsigned char> timingEntityState_;
    AgrSpeed::WorkspaceVector<AgrEval_Arrival> timingEntityMemo_;
};

static int AgrEval_MarkMffc(Abc_Obj_t *pRoot, Vec_Ptr_t *vLeaves)
{
    Abc_Obj_t *pLeaf;
    int i;
    Vec_PtrForEachEntry(Abc_Obj_t *, vLeaves, pLeaf, i) Abc_ObjRegular(pLeaf)->vFanouts.nSize++;
    Abc_NtkIncrementTravId(pRoot->pNtk);
    int Saved = Abc_NodeMffcLabelAig(pRoot);
    Vec_PtrForEachEntry(Abc_Obj_t *, vLeaves, pLeaf, i) Abc_ObjRegular(pLeaf)->vFanouts.nSize--;
    return Saved;
}

} // namespace

void AgrEval_ManSetBalancedRefactor(int Enable)
{
    s_BalancedRefactor = Enable != 0;
}

int AgrEval_ManBalancedRefactorEnabled()
{
    return 0;
}

Dec_Graph_t *AgrEval_ManBalanceGraph(Dec_Graph_t *pGraph)
{
    if (pGraph == nullptr || Dec_GraphIsConst(pGraph))
        return nullptr;
    Dec_Graph_t *Result = Dec_GraphCreate(pGraph->nLeaves);
    std::vector<int> Refs(pGraph->nSize, 0), Memo(pGraph->nSize, -1), Levels;
    Dec_Node_t *Node;
    int i;
    Dec_GraphForEachNode(pGraph, Node, i)
    {
        ++Refs[Node->eEdge0.Node];
        ++Refs[Node->eEdge1.Node];
    }
    Dec_GraphForEachLeaf(pGraph, Node, i)
    {
        Dec_GraphNode(Result, i)->pFunc = Node->pFunc;
        Memo[i] = i;
        auto *Object = Abc_ObjRegular(static_cast<Abc_Obj_t *>(Node->pFunc));
        Levels.push_back(Object ? static_cast<int>(Object->Level) : 0);
    }
    auto Build = [&](auto &&Self, int Index) -> int
    {
        if (Memo[Index] >= 0)
            return Memo[Index];
        using Item = std::pair<int, int>; // arrival level, complemented literal
        std::priority_queue<Item, std::vector<Item>, std::greater<Item>> Terms;
        auto Collect = [&](auto &&Gather, Dec_Edge_t Edge) -> void
        {
            int Child = Edge.Node;
            // Flatten only uncomplemented, singly used ANDs. An OR chain is
            // represented by the same AND association under De Morgan.
            if (Child >= pGraph->nLeaves && !Edge.fCompl && Refs[Child] == 1)
            {
                Gather(Gather, Dec_GraphNode(pGraph, Child)->eEdge0);
                Gather(Gather, Dec_GraphNode(pGraph, Child)->eEdge1);
            }
            else
            {
                int Built = Self(Self, Child);
                Terms.emplace(Levels[Built], 2 * Built + Edge.fCompl);
            }
        };
        Collect(Collect, Dec_GraphNode(pGraph, Index)->eEdge0);
        Collect(Collect, Dec_GraphNode(pGraph, Index)->eEdge1);
        while (Terms.size() > 1)
        {
            Item A = Terms.top();
            Terms.pop();
            Item B = Terms.top();
            Terms.pop();
            Dec_Edge_t Edge =
                Dec_GraphAddNodeAnd(Result, Dec_EdgeCreate(A.second / 2, A.second & 1),
                                    Dec_EdgeCreate(B.second / 2, B.second & 1));
            int Level = 1 + std::max(A.first, B.first);
            Levels.push_back(Level);
            Terms.emplace(Level, 2 * Edge.Node);
        }
        Memo[Index] = Terms.top().second / 2;
        return Memo[Index];
    };
    int Root = Build(Build, pGraph->eRoot.Node);
    Dec_GraphSetRoot(Result, Dec_EdgeCreate(Root, Dec_GraphIsComplement(pGraph)));
    bool Same = Result->nSize == pGraph->nSize && Result->eRoot.Node == pGraph->eRoot.Node;
    Dec_GraphForEachNode(pGraph, Node, i)
    {
        if (!Same)
            break;
        const Dec_Node_t *Other = Dec_GraphNode(Result, i);
        Same = Node->eEdge0.Node == Other->eEdge0.Node &&
               Node->eEdge0.fCompl == Other->eEdge0.fCompl &&
               Node->eEdge1.Node == Other->eEdge1.Node &&
               Node->eEdge1.fCompl == Other->eEdge1.fCompl;
    }
    if (Same)
    {
        Dec_GraphFree(Result);
        return nullptr;
    }
    return Result;
}

void AgrEval_ManSetScoreMode(int Mode)
{
    s_ScoreMode = std::max(0, std::min(2, Mode));
}

void AgrEval_ManSetTimingWeight(double Weight)
{
    s_TimingWeight = Weight;
}

void AgrEval_ManSetTimingEffort(int Mode)
{
    // Required times depend on graph/coordinates, not cached arrivals. They
    // can be maintained lazily even when candidate/arrival work is bounded.
    s_ExactTimingEvaluation = Mode >= 2;
    s_RequiredTimingEvaluation = Mode >= 1;
}

void AgrEval_ManSetExactTiming(int Enable)
{
    AgrEval_ManSetTimingEffort(Enable ? 2 : 0);
}

void AgrEval_ManSetClusterEvaluation(int Enable)
{
    s_ClusterEvaluation = Enable != 0;
}

void AgrEval_ManSetTimingEvaluation(int Enable)
{
    s_TimingEvaluation = std::max(0, std::min(2, Enable));
    if (!s_TimingEvaluation)
    {
#ifdef ABC_AGR_ENABLE_AUDIT
        if (s_PlanAttempts && ((char *)0) != nullptr)
            AGR_VERBOSE(
                "PA plan audit: %llu attempts, %llu valid, %llu rejected downstream cascades.\n",
                s_PlanAttempts, s_PlanValid, s_PlanCascades);
        s_PlanAttempts = s_PlanValid = s_PlanCascades = 0;
        if (s_ScreenChecks)
            AGR_VERBOSE(
                "PA structural-screen audit: %llu rejections checked, no false rejections.\n",
                s_ScreenChecks);
        s_ScreenChecks = 0;
        if (s_Timing.requiredUsesAudited)
            AGR_VERBOSE(
                "PA required-use audit: %d roots checked, %d used stale fanout requirements.\n",
                s_Timing.requiredUsesAudited, s_Timing.requiredUsesMismatched);
#endif
        AGR_PROFILE_FLUSH();
        s_Timing = AgrEval_TimingCache{};
    }
}

int AgrEval_ManPrepareTimingPass(Abc_Ntk_t *pNtk)
{
    s_ReadCache.Start(pNtk);
    if (!s_TimingEvaluation)
        return 1;
    return s_Timing.Build(pNtk);
}

int AgrEval_ManEvaluateCandidate(Abc_Obj_t *pRoot, Dec_Graph_t *pGraph, int nNodesSaved,
                                int LevelMax, int fRootComplement, int *pGain, double *pScore,
                                double *pHpwlSaved, double *pHpwlAdded, double *pDensityDelta)
{
    ++s_CompareCalls;
    if (pRoot == nullptr || pGraph == nullptr || nNodesSaved < 0)
        return 0;

    if (s_TimingEvaluation == 1 && !s_Timing.RefreshMarkedCone(pRoot))
        return 0;
    bool screen;
    {
        AGR_SPEED_SCOPE(Screen);
        screen = AgrEval_StructuralScreen(pRoot, pGraph, nNodesSaved, LevelMax);
    }
    if (!screen)
    {
        ++s_CompareScreens;
#ifdef ABC_AGR_ENABLE_AUDIT
        if (((char *)0) != nullptr)
        {
            ++s_ScreenChecks;
            AgrEval_CandidatePlan Reference(pRoot, pGraph, nNodesSaved, LevelMax, fRootComplement);
            if (Reference.IsValid())
            {
                Abc_Print(-1,
                          "PA structural-screen audit: rejected a valid candidate at root %d.\n",
                          pRoot->Id);
                std::abort();
            }
        }
#endif
        return 0;
    }
    ++s_ComparePlans;

    AgrEval_CandidatePlan Plan(pRoot, pGraph, nNodesSaved, LevelMax, fRootComplement, true);

    if (!Plan.IsValid())
        return 0;
    if (Plan.ReversesRecentStructure())
        return 0;
    if (pGain)
        *pGain = Plan.Gain();
    if (pScore)
        *pScore = Plan.Score();
    if (pHpwlSaved)
        *pHpwlSaved = Plan.HpwlSaved();
    if (pHpwlAdded)
        *pHpwlAdded = Plan.HpwlAdded();
    if (pDensityDelta)
    {
        *pDensityDelta = Plan.DensityDelta();
    }
    return 1;
}

// Independent full-plan check of the proxy's structural materialization count.
// Read-only reuse of the evaluator's structural screen, before RS beam ranking.

int AgrEval_ManCommitCandidate(Abc_Obj_t *pRoot, Dec_Graph_t *pGraph, Vec_Ptr_t *vLeaves,
                              int fUpdateLevel, int nGain)
{
    AGR_SPEED_COMMIT_DOMAIN();
    ++s_CompareCommits;
    s_CompareNegativeSelected += nGain < 0;
    s_CompareMinusOneSelected += nGain == -1;
    AGR_PROFILE_SCOPE(Commit);
    if (pRoot == nullptr || pGraph == nullptr || vLeaves == nullptr)
        return 0;
    Abc_Ntk_t *pNtk = pRoot->pNtk;
    int nNodesSaved = AgrEval_MarkMffc(pRoot, vLeaves);

    AgrEval_CandidatePlan Plan(pRoot, pGraph, nNodesSaved, ABC_INFINITY);
    if (!Plan.IsValid() || !Agr_ManBeginEdit(pNtk))
        return 0;

    int NodesBefore = Abc_NtkNodeNum(pNtk);
    int FirstNewId = Abc_NtkObjNumMax(pNtk);
    auto DirectFanouts = Plan.DirectFanouts();
    auto TimingMovedIds = Plan.TimingMovedObjectIds();
    auto RequiredSeeds = s_TimingEvaluation == 1 && s_RequiredTimingEvaluation
                             ? Plan.RequiredBoundaryIds()
                             : std::vector<int>{};
    double HpwlBefore = 0.0, HpwlScale = 1.0;
    Agr_ManReadMetrics(pNtk, &HpwlBefore, nullptr, &HpwlScale, nullptr);
    int OldMaxLogic = s_TimingEvaluation ? s_Timing.maxLogic : 0;
    double OldMaxWire = s_TimingEvaluation ? s_Timing.maxWire : 0.0;
    double OldWireScale = s_TimingEvaluation ? s_Timing.wireScale : 1.0;
    if (!Plan.StageOldPlacement())
    {
        Agr_ManClearPlacement();
        return 0;
    }
    Abc_Obj_t *pRootNew = Dec_GraphToNetwork(pNtk, pGraph);

    std::vector<int> NewIds;
    bool ExactMaterialization = Plan.MaterializationMatchesPlan(pGraph, FirstNewId, NewIds);
    if (!Plan.WriteUpdatedPositions(pGraph, FirstNewId) ||
        !Agr_AigReplace(static_cast<Abc_Aig_t *>(pNtk->pManFunc), pRoot, pRootNew, fUpdateLevel))
    {
        Agr_ManClearPlacement();
        return 0;
    }
    s_ReadCache.Invalidate();

    int ActualGain = NodesBefore - Abc_NtkNodeNum(pNtk);
    s_CompareGrowthCommits += ActualGain < 0;
    s_CompareMaxGrowth = std::max(s_CompareMaxGrowth, static_cast<long>(-ActualGain));
    /* A matching node count is not enough to justify a local HPWL delta.
       Materialization must preserve every predicted reuse/new-node identity,
       and replacement must delete exactly the old MFFC without a downstream
       structural-hash cascade.  Otherwise rebuild the actual netlist. */
    bool ExactBoundary = ExactMaterialization && ActualGain == nGain && nGain == Plan.Gain() &&
                         Plan.BoundaryMatchesPlan(NewIds, DirectFanouts, pRootNew);
    bool TimingRebuilt = false;
    if (ExactBoundary)
    {
        if (!Agr_ManFinishLocalEdit(pNtk, Plan.HpwlSaved() - Plan.HpwlAdded()))
        {
            Agr_ManClearPlacement();
            return 0;
        }
    }
    else
    {
        if (!Agr_ManFinishGlobalEdit(pNtk))
        {
            Agr_ManClearPlacement();
            return 0;
        }
        ++s_CompareFallbacks;
        double HpwlAfter = 0.0;
        Agr_ManReadMetrics(pNtk, &HpwlAfter, nullptr, nullptr, nullptr);
        double ActualScore = ActualGain + 0.25 * (HpwlBefore - HpwlAfter) / HpwlScale;
        if (s_TimingEvaluation)
        {
            if (!s_Timing.Build(pNtk))
            {
                Agr_ManClearPlacement();
                return 0;
            }
            TimingRebuilt = true;
            if (s_TimingEvaluation == 2)
            {
                double EndpointGain = static_cast<double>(OldMaxLogic - s_Timing.maxLogic) +
                                      (OldMaxWire - s_Timing.maxWire) / OldWireScale;
                ActualScore += kTimingEndpointWeight * EndpointGain;
            }
        }
        if ((ActualGain < -0) || ((ActualScore <= kCompareTolerance)))
        {
            Abc_Print(-1,
                      "placement error: materialized replacement has nonpositive actual score %.9f "
                      "(predicted gain %d, actual gain %d, HPWL %.9f -> %.9f, predicted local "
                      "reduction %.9f).\n",
                      ActualScore, nGain, ActualGain, HpwlBefore, HpwlAfter,
                      Plan.HpwlSaved() - Plan.HpwlAdded());
            Abc_Print(-1, "placement error: candidate result was %s.\n",
                      Plan.ResultIsVirtual() ? "virtual" : "structurally reused");
            Agr_ManClearPlacement();
            return 0;
        }
    }
    if (s_TimingEvaluation && !TimingRebuilt)
    {
        bool TimingUpdated = false;
        if (s_TimingEvaluation == 1 && ExactBoundary)
        {
            std::vector<int> PositionIds = TimingMovedIds;
            std::vector<int> StructuralIds;
            /* Collect every live object created while realizing the exact
               candidate.  New object IDs can be above the old traversal
               cursor and therefore must be seeded explicitly. */
            for (int Id = FirstNewId; Id < Abc_NtkObjNumMax(pNtk); ++Id)
            {
                Abc_Obj_t *pObject = Abc_NtkObj(pNtk, Id);
                if (pObject == nullptr || !Abc_ObjIsNode(pObject))
                    continue;
                PositionIds.push_back(Id);
                StructuralIds.push_back(Id);
            }
            Abc_Obj_t *pRootRegular = Abc_ObjRegular(pRootNew);
            if (pRootRegular != nullptr && pRootRegular->Id >= 0 &&
                pRootRegular->Id < Abc_NtkObjNumMax(pNtk) &&
                Abc_NtkObj(pNtk, pRootRegular->Id) == pRootRegular)
            {
                StructuralIds.push_back(pRootRegular->Id);
                if (Abc_ObjIsNode(pRootRegular))
                    PositionIds.push_back(pRootRegular->Id);
            }
            for (const AgrEval_DirectFanout &Entry : DirectFanouts)
                StructuralIds.push_back(Entry.id);
            TimingUpdated = s_Timing.UpdateAfterLocalEdit(
                pNtk, PositionIds, StructuralIds, fUpdateLevel != 0);
            if (TimingUpdated && s_RequiredTimingEvaluation)
            {
                RequiredSeeds.insert(RequiredSeeds.end(), PositionIds.begin(), PositionIds.end());
                s_Timing.InvalidateRequired(pNtk, RequiredSeeds);
            }
        }
        /* The full-cone ablation needs refreshed endpoint maxima.  A boundary
           mismatch also falls back to the global audit because its true edit
           cone is intentionally treated as unknown. */
        if (!TimingUpdated)
        {
            if (!s_Timing.Build(pNtk))
            {
                Agr_ManClearPlacement();
                return 0;
            }
        }
    }
#ifdef ABC_AGR_ENABLE_AUDIT
    if (s_ExactTimingEvaluation && s_TimingEvaluation && ((char *)0) != nullptr &&
        !s_Timing.Audit())
        return 0;
#endif
    (void)nGain;

    return 1;
}

ABC_NAMESPACE_IMPL_END

ABC_NAMESPACE_IMPL_START
void AgrEval_ManSetCandidateScoreFloor(double floor)
{
    s_CandidateScoreFloor = floor;
}

void AgrEval_ManConfigure(int mode, int growth, double hpwl, double area)
{
    s_CoMinimumGain = 0;
    s_CandidateScoreFloor = -std::numeric_limits<double>::infinity();
    s_BoundQueries = s_BoundPruned = 0;
    s_CoRepairCalls = s_CoRepairSuccess = s_CoDensityReject = 0;
    s_PhysicalAreaGuard = false;
    s_CoRootObservations.clear();
    s_CompareHpwl = hpwl;
    s_CompareArea = area;
    s_CompareMaxGrowth = 0;
    s_CompareNegativeSelected = s_CompareMinusOneSelected = s_CompareGrowthCommits = 0;
    s_CompareCalls = s_CompareScreens = s_ComparePlans = s_CompareCommits = s_CompareFallbacks = 0;
}

void AgrEval_ManPrintEffort()
{

    AGR_VERBOSE("AGR_CAPACITY attempted=%ld feasible=%ld rejected=%ld\n", s_CoRepairCalls,
               s_CoRepairSuccess, s_CoDensityReject);
    AGR_VERBOSE("AGR_SCORE_BOUND queries=%ld pruned=%ld\n", s_BoundQueries, s_BoundPruned);
    AGR_SPEED_FLUSH();

    AGR_VERBOSE("AGR_EVAL_EFFORT calls=%ld screened=%ld full_plans=%ld commits=%ld fallbacks=%ld "
               "negative_selected=%ld minus_one_selected=%ld growth_commits=%ld growth_max=%ld\n",
               s_CompareCalls, s_CompareScreens, s_ComparePlans, s_CompareCommits,
               s_CompareFallbacks, s_CompareNegativeSelected, s_CompareMinusOneSelected,
               s_CompareGrowthCommits, s_CompareMaxGrowth);
}
ABC_NAMESPACE_IMPL_END

ABC_NAMESPACE_IMPL_START

void AgrEval_ManSetPhysicalAreaGuard(int enabled)
{
    s_PhysicalAreaGuard = enabled != 0;
}
ABC_NAMESPACE_IMPL_END

ABC_NAMESPACE_IMPL_START
extern "C" int AgrEval_ManGrowthEnabled(void)
{
    return 0;
}
ABC_NAMESPACE_IMPL_END
