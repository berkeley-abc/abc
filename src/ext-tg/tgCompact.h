extern "C";
extern "C";
extern "C";
#include "tgTensionKernel.h"
/* Sparse complete TG rounds over tension-selected roots. Original PA storage
 * and placement are shared through the isolated TgEval_ evaluator. No timer,
 * intermediate global placement, identity subtraction, or quality rollback. */
// Exact topology-only shape cache for append-only IDs inside sparse RF.
// Compare every live node's fanin literals, then invalidate only the bounded
// forward neighborhood that can observe a changed three-edge cone.
struct SparseShapeCache
{
    std::vector<std::pair<int, int>> inputs;
    std::vector<unsigned> values;
    std::vector<signed char> dirty;
    std::vector<std::pair<int, int>> queue;
    long reused = 0, rebuilt = 0;
    void refresh(Abc_Ntk_t *n)
    {
        const size_t old = inputs.size(), size = Abc_NtkObjNumMax(n);
        if (size < old)
            std::abort();
        inputs.resize(size, {-1, -1});
        values.resize(size);
        dirty.assign(size, -1);
        queue.clear();
        Abc_Obj_t *v;
        int i;
        Abc_NtkForEachNode(n, v, i)
        {
            const auto now = std::make_pair(2 * Abc_ObjFaninId0(v) + Abc_ObjFaninC0(v),
                                            2 * Abc_ObjFaninId1(v) + Abc_ObjFaninC1(v));
            if (inputs[v->Id] == now)
                continue;
            inputs[v->Id] = now;
            dirty[v->Id] = 3;
            queue.emplace_back(v->Id, 3);
        }
        if (!old)
            return; // Every live node is already dirty on the first round.
        for (size_t at = 0; at < queue.size(); ++at)
        {
            const auto item = queue[at];
            if (item.second <= 0)
                continue;
            auto *node = Abc_NtkObj(n, item.first);
            Abc_Obj_t *fanout;
            int j;
            Abc_ObjForEachFanout(node, fanout, j)
            {
                if (!Abc_ObjIsNode(fanout) || dirty[fanout->Id] >= item.second - 1)
                    continue;
                dirty[fanout->Id] = item.second - 1;
                queue.emplace_back(fanout->Id, item.second - 1);
            }
        }
    }
};

struct SparseScan
{
    struct Net
    {
        Axis x, y;
        int count = 0;
    };
    struct Opportunity
    {
        double wire = 0, lifted = 0, score = 0;
        unsigned shape = 2166136261u;
        int internals = 0, repeats = 0, associative = 0;
    };
    std::vector<Opportunity> opportunity;
    std::vector<unsigned> shapes;
    unsigned shape(int id) const
    {
        return shapes.empty() ? opportunity[id].shape : shapes[id];
    }
    std::vector<XY> pos;
    std::vector<unsigned char> present;
    std::vector<Net> nets;
    std::vector<double> tension, basePriority, actionPriority;
    explicit SparseScan(Abc_Ntk_t *n, bool selectionGeometry = true, bool topologyOnly = false)
    {

        int size = Abc_NtkObjNumMax(n);
        pos.resize(size);
        present.resize(size);
        nets.resize(size);
        tension.resize(size);
        if (topologyOnly)
        {
            basePriority.resize(size);
            return;
        }
        Abc_Obj_t *o, *f;
        int i, j;
        Abc_NtkForEachNode(n, o, i) present[o->Id] =
            Tg_ManReadObjectPosition(n, o, &pos[o->Id].x, &pos[o->Id].y);
        // Full traversal needs positions for the identical candidate generator,
        // but no tension scan or structural ranking.
        if (!selectionGeometry)
        {
            basePriority = tension;
            return;
        }

        std::vector<int> seen(size, -1);
        Abc_NtkForEachObj(n, o, i)
        {
            if (!Abc_ObjIsNode(o) && !Abc_ObjIsCi(o))
                continue;
            auto &net = nets[o->Id];
            auto add = [&](int id)
            {
                if (!present[id] || seen[id] == o->Id)
                    return;
                seen[id] = o->Id;
                ++net.count;
                net.x.add(pos[id].x);
                net.y.add(pos[id].y);
            };
            add(o->Id);
            Abc_ObjForEachFanout(o, f, j) add(f->Id);
        }

        auto gather = [&]()
        {
            std::vector<TgTensionItem> items;
            items.reserve(Abc_NtkNodeNum(n));
            Abc_Obj_t *root;
            int index;
            Abc_NtkForEachNode(n, root, index)
            {
                TgTensionItem v;
                v.id = root->Id;
                int drivers[3] = {root->Id, Abc_ObjFaninId0(root), Abc_ObjFaninId1(root)};
                for (int k = 0; k < 3; ++k)
                {
                    bool duplicate = false;
                    for (int l = 0; l < k; ++l)
                        duplicate |= drivers[k] == drivers[l];
                    const auto &net = nets[drivers[k]];
                    if (duplicate || net.count < 2)
                        continue;
                    v.boxes[v.count++] = {net.x.without(pos[root->Id].x),
                                          net.y.without(pos[root->Id].y)};
                }
                items.push_back(v);
            }
            return items;
        };

        int mode = ((0));
        const char *const selectionBackend = "fast";
        bool fast = selectionBackend && std::string(selectionBackend) == "fast";
        if (fast)
        {
            // Fused serial gather: at most two roots live in the SIMD scratch.
            TgTensionItem pair[2];
            size_t filled = 0;
            Abc_NtkForEachNode(n, o, i)
            {
                auto &v = pair[filled];
                v = TgTensionItem{};
                v.id = o->Id;
                int ds[3] = {o->Id, Abc_ObjFaninId0(o), Abc_ObjFaninId1(o)};
                for (int k = 0; k < 3; ++k)
                {
                    bool duplicate = false;
                    for (int l = 0; l < k; ++l)
                        duplicate |= ds[k] == ds[l];
                    const auto &net = nets[ds[k]];
                    if (duplicate || net.count < 2)
                        continue;
                    v.boxes[v.count++] = {net.x.without(pos[v.id].x), net.y.without(pos[v.id].y)};
                }
                if (++filled == 2)
                {
                    TgTensionVector(pair, tension, 0, 2, true);
                    filled = 0;
                }
            }
            if (filled)
                TgTensionVector(pair, tension, 0, filled, true);
            mode = 6;
        }
        else if (mode)
        {
            auto items = gather();
            TgTensionRun(items, tension, mode);
        }
        else
        {
            Abc_NtkForEachNode(n, o, i)
            {
                std::array<Box, 3> boxes;
                int count = 0;
                int drivers[3] = {o->Id, Abc_ObjFaninId0(o), Abc_ObjFaninId1(o)};
                for (int k = 0; k < 3; ++k)
                {
                    bool duplicate = false;
                    for (int l = 0; l < k; ++l)
                        duplicate |= drivers[k] == drivers[l];
                    const auto &net = nets[drivers[k]];
                    if (duplicate || net.count < 2)
                        continue;
                    boxes[count++] = {net.x.without(pos[o->Id].x), net.y.without(pos[o->Id].y)};
                }
                for (int axis = 0; axis < 2; ++axis)
                {
                    std::array<double, 6> ends{};
                    for (int k = 0; k < count; ++k)
                    {
                        auto b = axis ? boxes[k].y : boxes[k].x;
                        ends[2 * k] = b.first;
                        ends[2 * k + 1] = b.second;
                    }
                    if (!count)
                        continue;
                    std::sort(ends.begin(), ends.begin() + 2 * count);
                    double center = ends[count - 1];
                    for (int k = 0; k < count; ++k)
                        tension[o->Id] += dist(center, axis ? boxes[k].y : boxes[k].x);
                }
            }
        }

        // Freeze selection features before any edits in this round. In
        // particular, diagnostics must not look up newly appended fanin IDs in
        // the earlier scan arrays after an upstream replacement.
        basePriority = tension;
        Abc_NtkForEachNode(n, o, i) for (int k = 0; k < 2; ++k)
        {
            auto *u = Abc_ObjFanin(o, k);
            if (Abc_ObjIsNode(u) && Abc_ObjFanoutNum(u) == 1)
                basePriority[o->Id] += .5 * tension[u->Id];
        }
        // Cheap anchored three-terminal reassociation opportunity. Only positive,
        // single-use AND edges can be flattened without changing the Boolean function.
    }
#include "tgScan.h"
    // Bounded structural lookahead, independent of truth factoring/evaluation.
    // Seven internal occurrences and eight terminal occurrences at most.
    void prepareOpportunities(Abc_Ntk_t *n, bool shapeOnly = false, bool fastFeatures = false,
                              SparseShapeCache *cache = nullptr)
    {
        if (!shapeOnly)
            cache = nullptr;
        if (cache)
            cache->refresh(n);
        if (shapeOnly)
            shapes.resize(Abc_NtkObjNumMax(n));
        else
            opportunity.resize(Abc_NtkObjNumMax(n));
        Abc_Obj_t *root;
        int ri;
        // All roots are visited directly on this thread; no pointer snapshot needed.
        auto prepare = [&](Abc_Obj_t *root)
        {
            if (cache && cache->dirty[root->Id] < 0 && !TgSpeed::CareAudit())
            {
                shapes[root->Id] = cache->values[root->Id];
                ++cache->reused;
                return;
            }
            Opportunity local;
            auto &f = shapeOnly ? local : opportunity[root->Id];
            Abc_Obj_t *queue[15];
            int depth[15], seen[15], count = 0;
            queue[0] = root;
            depth[0] = 0;
            int end = 1;
            double exposure = 0;
            for (int at = 0; at < end; ++at)
            {
                auto *v = queue[at];
                bool duplicate = false;
                int previous = -1;
                for (int j = 0; j < count; ++j)
                    if (seen[j] == v->Id)
                    {
                        duplicate = true;
                        previous = j;
                        break;
                    }
                unsigned code = duplicate
                                    ? 32u + unsigned(previous)
                                    : (Abc_ObjIsNode(v) && depth[at] < 3
                                           ? 1u + 2u * Abc_ObjFaninC0(v) + 4u * Abc_ObjFaninC1(v)
                                           : 0u);
                f.shape = (f.shape ^ code) * 16777619u;
                if (duplicate)
                {
                    ++f.repeats;
                    continue;
                }
                seen[count++] = v->Id;
                if (!Abc_ObjIsNode(v) || depth[at] >= 3)
                    continue;
                if (!shapeOnly)
                {
                    ++f.internals;
                    const auto &net = nets[v->Id];
                    if (net.count > 1)
                        f.wire += net.x.hi - net.x.lo + net.y.hi - net.y.lo;
                    f.lifted += tension[v->Id] / (1.0 + depth[at]);
                    exposure += std::max(0, Abc_ObjFanoutNum(v) - 1);
                }
                for (int k = 0; k < 2; ++k)
                {
                    auto *u = Abc_ObjFanin(v, k);
                    if (!shapeOnly && Abc_ObjIsNode(u) && !Abc_ObjFaninC(v, k) &&
                        Abc_ObjFanoutNum(u) == 1)
                        ++f.associative;
                    queue[end] = u;
                    depth[end++] = depth[at] + 1;
                }
            }
            // Favor measurable wire opportunity in transformable cones, discounted
            // for approximate cone size and external coupling. No fitted design IDs.
            if (shapeOnly)
                shapes[root->Id] = f.shape;
            if (cache)
            {
                if (cache->dirty[root->Id] < 0 && cache->values[root->Id] != f.shape)
                {
                    Abc_Print(-1, "TG_SHAPE_CACHE stale structural shape.\n");
                    std::abort();
                }
                cache->reused += cache->dirty[root->Id] < 0;
                cache->rebuilt += cache->dirty[root->Id] >= 0;
                cache->values[root->Id] = f.shape;
            }
            if (!shapeOnly)
                f.score = (f.lifted + .25 * f.wire) * (1 + f.repeats + .5 * f.associative) /
                          (1 + .25 * f.internals + .25 * exposure);
        };
        Abc_NtkForEachNode(n, root, ri) prepare(root);
    }
    double rootPriority(Abc_Ntk_t *, int id) const
    {
        return id >= 0 && id < int(basePriority.size()) ? basePriority[id] : 0;
    }

    std::vector<int>
    roots(Abc_Ntk_t *n, int percent, int maximum, bool tree, bool zero, bool shared, int logic,
          Abc_ManCut_t *manager, const std::string &ranking,
          const std::vector<unsigned char> *visited = nullptr,
          const std::vector<double> *utility = nullptr, bool referenceRanking = false,
          const std::unordered_map<unsigned, double> *classWeight = nullptr,
          const std::vector<unsigned> *selectionGroups = nullptr, bool softHistory = false) const
    {
        std::vector<int> out;
        auto selectionClass = [&](int id)
        { return selectionGroups ? (*selectionGroups)[id] : shape(id); };
        auto *cone = Vec_PtrAlloc(32);
        int cutScans = 0;
        const bool mappedActive = 0 != 0;
        Abc_Obj_t *o;
        int i;
        auto priority = [&](int id)
        {
            if (ranking == "opportunity")
                return (*utility)[id];
            if (ranking == "cone")
                return opportunity[id].score;
            if (ranking == "wire")
                return opportunity[id].wire;
            if (ranking == "lift")
                return opportunity[id].lifted;
            if (ranking == "uniform")
            { // Deterministic hash control, independent of placement.
                unsigned h = unsigned(id);
                h ^= h >> 16;
                h *= 0x7feb352du;
                h ^= h >> 15;
                h *= 0x846ca68bu;
                h ^= h >> 16;
                return double(h);
            }
            return rootPriority(n, id);
        };
        Abc_NtkForEachNode(n, o, i) if (Abc_ObjFanoutNum(o) > 0 && Abc_ObjFanoutNum(o) <= 1000 &&
                                        (!mappedActive || true) && !Abc_NodeIsPersistant(o) &&
                                        (zero || rootPriority(n, o->Id) > 1e-12))
        {
            if (tree && !((!Abc_ObjFaninC0(o) && Abc_ObjIsNode(Abc_ObjFanin0(o)) &&
                           (shared || Abc_ObjFanoutNum(Abc_ObjFanin0(o)) == 1)) ||
                          (!Abc_ObjFaninC1(o) && Abc_ObjIsNode(Abc_ObjFanin1(o)) &&
                           (shared || Abc_ObjFanoutNum(Abc_ObjFanin1(o)) == 1))))
                continue;
            // Exploration policy only: prefer roots never evaluated in this
            // command. Newly created roots remain eligible. This is not a claim
            // that previously visited cones cannot benefit from another edit.
            if (visited && o->Id < int(visited->size()) && ((*visited)[o->Id] & 2))
                continue;
            if (logic == 3 && Abc_ObjFanoutNum(o) == 1)
            {
                auto *parent = Abc_ObjFanout0(o);
                if (Abc_ObjIsNode(parent) && Abc_NodeIsMuxType(parent))
                    continue;
            }
            if (logic == 2)
            {
                auto *cut = Abc_NodeFindCut(manager, o, 0);
                ++cutScans;
                Abc_NodeConeCollect(&o, 1, cut, cone, 0);
                // A read-once binary tree has exactly leaves-1 internals.
                // Positive surplus detects reconvergence throughout this cut;
                // it is still only an opportunity signal, not a savings proof.
                if (Vec_PtrSize(cone) < Vec_PtrSize(cut))
                    continue;
            }
            if (logic == 1)
            {
                // Look for reconvergence within three edges of the root. This
                // is a cheap opportunity filter, not a proof of reducibility.
                int ids[2][7], count[2] = {0, 0};
                for (int side = 0; side < 2; ++side)
                {
                    Abc_Obj_t *queue[7];
                    queue[0] = Abc_ObjFanin(o, side);
                    int end = 1;
                    for (int at = 0; at < end; ++at)
                    {
                        auto *v = queue[at];
                        ids[side][count[side]++] = v->Id;
                        if (at < 3 && Abc_ObjIsNode(v) && Abc_ObjFaninNum(v) == 2)
                        {
                            queue[end++] = Abc_ObjFanin0(v);
                            queue[end++] = Abc_ObjFanin1(v);
                        }
                    }
                }
                bool overlap = false;
                for (int a = 0; a < count[0]; ++a)
                    for (int b = 0; b < count[1]; ++b)
                        overlap |= ids[0][a] != 0 && ids[0][a] == ids[1][b];
                if (!overlap)
                    continue;
            }
            out.push_back(o->Id);
        }
        size_t keep = (out.size() * size_t(percent) + 99) / 100;
        if (maximum)
            keep = std::min(keep, size_t(maximum));
        if (ranking == "topology")
        {
            TG_VERBOSE("TG_SPARSE_SELECTION logic=%d eligible=%d selected=%d cut_scans=%d\n", logic,
                       int(out.size()), int(out.size()), cutScans);
            Vec_PtrFree(cone);
            return out;
        }
        // Compute ranking once per eligible root, not on every heap comparison.
        const bool directPriority =
            (ranking == "diverse" || ranking == "tension") && ((char *)"fast");
        std::vector<double> storedPriorities(directPriority ? 0 : pos.size());
        if (!directPriority)
            for (int id : out)
                storedPriorities[id] = priority(id);
        const std::vector<double> mappedPriorities;
        std::vector<double> structuralPriorities;

        const auto &originalPriorities =
            ((directPriority ? (mappedPriorities.empty() ? basePriority : mappedPriorities)
                             : storedPriorities));
        std::vector<double> placementPriorities;

        const int trajectoryMode = 0;

        const bool trajectoryActive = trajectoryMode > 0 && trajectoryMode < 9;

        const bool continuousHistory = softHistory || (trajectoryActive && ((char *)"0") && 0);
        std::vector<double> trajectorySignal;

        const auto &priorities = (originalPriorities);
        // Temporal geometry must be able to change allocation across structural
        // classes, not only rank roots inside a preallocated class. Use a
        // dimensionless live merit and retain the existing diversity/work prior.
        // These are heuristic weights only; generation and acceptance are intact.

        std::vector<double> allocationMerit;

        auto allocationWeight = [&](double sum, double peak, size_t count) { return 1.; };
        auto better = [&](int a, int b)
        {
            // Preserve class quotas; history changes only the choice within a
            // class (and equal-ticket ties). First-round novelty is uniformly 1.
            if (!continuousHistory && ranking == "diverse" && utility &&
                (*utility)[a] != (*utility)[b])
                return (*utility)[a] > (*utility)[b];
            double x = priorities[a], y = priorities[b];
            // Optional selected-standard-flow experiment: history discounts
            // geometry continuously rather than taking precedence over every
            // geometric score. Class ticket quotas and their denominators stay
            // unchanged; compact TG retains its existing history policy.
            if (continuousHistory && ranking == "diverse" && utility)
            {
                x *= (*utility)[a];
                y *= (*utility)[b];
            }
            return x != y ? x > y : a < b;
        };
        const char *const selectionBackend = "fast";
        const bool fast =
            !referenceRanking && selectionBackend && std::string(selectionBackend) == "fast";
        auto prefixSort = [&](std::vector<int> &ids, size_t count, auto comparison)
        {
            if (fast)
            {
                if (count < ids.size())
                    std::nth_element(ids.begin(), ids.begin() + count, ids.end(), comparison);
                std::sort(ids.begin(), ids.begin() + count, comparison);
            }
            else
                std::partial_sort(ids.begin(), ids.begin() + count, ids.end(), comparison);
        };
        if (ranking == "diverse")
        {

            // exponents weight class population and its peak geometric priority.
            // By default every class gets its first root before a second.
            // Learned allocation instead assigns a positive first-ticket cost
            // and scales every ticket by that class's observed utility.
            // This is a scheduling heuristic, never a Boolean equivalence cache.
            auto classUtility = [&](unsigned shape)
            {
                if (!classWeight)
                    return 1.0;
                auto at = classWeight->find(shape);
                return at == classWeight->end() ? 1.0 : at->second;
            };
            std::vector<double> ticket(pos.size(), INFINITY);
            size_t groupCount = 0;
            if (fast)
            {
                // Dense key arrays replace per-node tree lookups and thousands
                // of tiny bucket allocations. The upper 32 bits are the exact
                // existing shape hash; the lower 32 bits retain the root ID.
                std::vector<uint64_t> keys;
                keys.reserve(out.size());
                for (int id : out)
                    keys.push_back((uint64_t(selectionClass(id)) << 32) | unsigned(id));
                if (keys.size() < 4096)
                    std::sort(keys.begin(), keys.end());
                else
                {
                    std::vector<uint64_t> scratch(keys.size());
                    for (int shift = 32; shift < 64; shift += 8)
                    {
                        size_t offsets[256] = {};
                        for (auto key : keys)
                            ++offsets[(key >> shift) & 255u];
                        size_t sum = 0;
                        for (auto &offset : offsets)
                        {
                            size_t count = offset;
                            offset = sum;
                            sum += count;
                        }
                        for (auto key : keys)
                            scratch[offsets[(key >> shift) & 255u]++] = key;
                        keys.swap(scratch);
                    }
                }
                auto idOf = [](uint64_t key) { return int(key & 0xffffffffu); };
                auto compare = [&](uint64_t a, uint64_t b) { return better(idOf(a), idOf(b)); };
                for (size_t begin = 0; begin < keys.size();)
                {
                    size_t end = begin + 1;
                    while (end < keys.size() && (keys[end] >> 32) == (keys[begin] >> 32))
                        ++end;
                    const size_t count = end - begin, prefix = std::min(keep, count);
                    ++groupCount;
                    double allocationSum = 0., allocationPeak = 0.;
                    // Keys enter each class in ascending ID order, including
                    // the stable radix path. Accumulate before partial sorting.

                    if (prefix < count)
                        std::nth_element(keys.begin() + begin, keys.begin() + begin + prefix,
                                         keys.begin() + end, compare);
                    std::sort(keys.begin() + begin, keys.begin() + begin + prefix, compare);

                    double denominator = (std::sqrt(double(count)));

                    denominator *= classUtility(unsigned(keys[begin] >> 32));
                    denominator *= allocationWeight(allocationSum, allocationPeak, count);
                    for (size_t rank = 0; rank < prefix; ++rank)
                        ticket[idOf(keys[begin + rank])] =
                            (double(rank) + (classWeight ? 1 : 0)) / denominator;
                    begin = end;
                }
            }
            else
            {
                std::map<unsigned, std::vector<int>> groups;
                for (int id : out)
                    groups[selectionClass(id)].push_back(id);
                groupCount = groups.size();
                for (auto &entry : groups)
                {
                    auto &ids = entry.second;
                    double allocationSum = 0., allocationPeak = 0.;

                    std::sort(ids.begin(), ids.end(), better);

                    double denominator = (std::sqrt(double(ids.size())));

                    denominator *= classUtility(entry.first);
                    denominator *= allocationWeight(allocationSum, allocationPeak, ids.size());
                    for (size_t rank = 0; rank < ids.size(); ++rank)
                        ticket[ids[rank]] = (double(rank) + (classWeight ? 1 : 0)) / denominator;
                }
            }
            prefixSort(out, keep, [&](int a, int b)
                       { return ticket[a] != ticket[b] ? ticket[a] < ticket[b] : better(a, b); });
            TG_VERBOSE("TG_REGION_DIVERSITY groups=%d\n", int(groupCount));
        }
        else
            prefixSort(out, keep, better);
        TG_VERBOSE("TG_SPARSE_SELECTION logic=%d eligible=%d selected=%d cut_scans=%d\n", logic,
                   int(out.size()), int(keep), cutScans);
        Vec_PtrFree(cone);

        if (!actionPriority.empty() && keep && keep < out.size())
        {
            const size_t reserve = (3 * keep + 3) / 4;
            const auto baseline = out;
            auto ranked = out;
            auto merit = [&](int id)
            { return actionPriority[id] * (utility ? (.25 + .75 * (*utility)[id]) : 1.); };
            auto cmp = [&](int a, int b)
            {
                double x = merit(a), y = merit(b);
                return x != y ? x > y : a < b;
            };
            prefixSort(ranked, reserve, cmp);
            std::vector<unsigned char> used(pos.size());
            std::vector<int> selected;
            selected.reserve(keep);
            for (size_t j = 0; j < reserve; ++j)
                if (merit(ranked[j]) > 1e-8)
                {
                    selected.push_back(ranked[j]);
                    used[ranked[j]] = 1;
                }
            const size_t actionCount = selected.size();
            for (int id : baseline)
                if (selected.size() < keep && !used[id])
                {
                    selected.push_back(id);
                    used[id] = 1;
                }
            if (selected.size() != keep)
                std::abort();
            out.swap(selected);
            if (!referenceRanking)
                TG_VERBOSE("TG_ACTION_SELECT selected=%d action=%d\n", int(keep), int(actionCount));
        }
        out.resize(keep);

        return out;
    }
};
#include "tgHistory.h"

// All selected operators see the same live graph/placement in a Co epoch.
// Refresh exact changed geometry/connectivity between operators, instead of
// keeping three old snapshots that each need a full refresh after placement.
struct CoSparseSharedState
{
    int epoch = -1;
    SparseShapeCache shapes;
    std::unique_ptr<SparseScan> scan;
};
static CoSparseSharedState &CoSparseShared()
{
    static CoSparseSharedState s;
    if (s.epoch != Tg_Epoch())
    {
        s = CoSparseSharedState{};
        s.epoch = Tg_Epoch();
    }
    return s;
}

Region sparseGreedyCut(Abc_Ntk_t *n, int root, const SparseScan &scan, int K, int bound)
{
    Region r;
    r.root = r.seed = root;
    r.closed = false;
    r.inside.insert(root);
    auto *v = Abc_NtkObj(n, root);
    r.leaves.insert(Abc_ObjFaninId0(v));
    r.leaves.insert(Abc_ObjFaninId1(v));
    while (int(r.inside.size()) < bound)
    {
        int best = -1;
        double bestScore = -1;
        for (int id : r.leaves)
        {
            auto *u = Abc_NtkObj(n, id);
            if (!Abc_ObjIsNode(u) || Abc_NodeIsPersistant(u))
                continue;
            int extra = 0;
            for (int k = 0; k < 2; ++k)
            {
                int f = Abc_ObjFanin(u, k)->Id;
                extra += !r.leaves.count(f) && !r.inside.count(f);
            }
            if (int(r.leaves.size()) - 1 + extra > K)
                continue;
            int outside = 0;
            Abc_Obj_t *f;
            int j;
            Abc_ObjForEachFanout(u, f, j) outside += !r.inside.count(f->Id);
            double t = !proposalMode() && id < int(scan.tension.size()) ? scan.tension[id] : 0;
            double score = (1 + t) * (3 - extra) / (1.0 + outside + extra * extra);
            if (score > bestScore)
            {
                bestScore = score;
                best = id;
            }
        }
        if (best < 0)
            break;
        r.leaves.erase(best);
        r.inside.insert(best);
        auto *u = Abc_NtkObj(n, best);
        for (int k = 0; k < 2; ++k)
        {
            int f = Abc_ObjFanin(u, k)->Id;
            if (!r.inside.count(f))
                r.leaves.insert(f);
        }
    }
    return r;
}

// A depth-feasible geometric grouping of an associative AND cone. The exact
// Boolean identity is checked below; candidate placement remains PA's solver.
Expr sparseGeometryTree(const Expr &id, const std::vector<XY> &xy, const std::vector<int> &levels,
                        int required, const std::vector<Box> &boundary = {}, XY anchor = {0, 0},
                        bool keepDepth = false)
{
    Expr out(id.k);
    std::vector<int> terms, slots;
    std::function<void(int, int)> flatten = [&](int l, int depth)
    {
        if (l < 0 || l / 2 < id.k || (l & 1))
        {
            terms.push_back(l);
            slots.push_back(depth);
            return;
        }
        auto p = id.a[l / 2 - id.k];
        flatten(p.first, depth + 1);
        flatten(p.second, depth + 1);
    };
    flatten(id.root, 0);
    for (int l : terms)
        if (l < 0 || l / 2 >= id.k)
            return id;
    std::vector<XY> pos = xy;
    std::vector<int> lev = levels;
    std::vector<Box> boxes = boundary;
    auto minDepth = [](std::vector<int> v)
    {
        while (v.size() > 1)
        {
            std::sort(v.begin(), v.end());
            int x = 1 + v[1];
            v.erase(v.begin(), v.begin() + 2);
            v.push_back(x);
        }
        return v.empty() ? 0 : v[0];
    };
    while (terms.size() > 1)
    {
        int deepest = *std::max_element(slots.begin(), slots.end());
        int bi = -1, bj = -1;
        double best = INFINITY;
        XY bestPos{0, 0};
        for (int i = 0; i < int(terms.size()); ++i)
            for (int j = i + 1; j < int(terms.size()); ++j)
            {
                if (keepDepth && (slots[i] != deepest || slots[j] != deepest))
                    continue;
                int x = terms[i] / 2, y = terms[j] / 2;
                int merged = 1 + std::max(lev[x], lev[y]);
                std::vector<int> remaining{merged};
                for (int k = 0; k < int(terms.size()); ++k)
                    if (k != i && k != j)
                        remaining.push_back(lev[terms[k] / 2]);
                if (!keepDepth && minDepth(remaining) > required)
                    continue;
                double cost = std::abs(pos[x].x - pos[y].x) + std::abs(pos[x].y - pos[y].y);
                XY mergedPos{(pos[x].x + pos[y].x) / 2, (pos[x].y + pos[y].y) / 2};
                if (!boxes.empty())
                {
                    cost = 0;
                    for (int axis = 0; axis < 2; ++axis)
                    {
                        auto a = axis ? boxes[x].y : boxes[x].x, b = axis ? boxes[y].y : boxes[y].x;
                        double ends[4] = {a.first, a.second, b.first, b.second};
                        std::sort(ends, ends + 4);
                        double p = std::max(ends[1], std::min(ends[2], axis ? anchor.y : anchor.x));
                        cost += dist(p, a) + dist(p, b);
                        if (axis)
                            mergedPos.y = p;
                        else
                            mergedPos.x = p;
                    }
                }
                if (cost < best)
                {
                    best = cost;
                    bi = i;
                    bj = j;
                    bestPos = mergedPos;
                }
            }
        if (bi < 0)
            return id;
        int x = terms[bi] / 2, y = terms[bj] / 2;
        int l = out.land(terms[bi], terms[bj]);
        if (l < 0)
            return id;
        if (l / 2 >= int(pos.size()))
        {
            pos.push_back(bestPos);
            if (!boxes.empty())
                boxes.push_back({{bestPos.x, bestPos.x}, {bestPos.y, bestPos.y}});
            lev.push_back(1 + std::max(lev[x], lev[y]));
        }
        terms[bi] = l;
        terms.erase(terms.begin() + bj);
        --slots[bi];
        slots.erase(slots.begin() + bj);
    }
    out.root = terms[0];
    if (keepDepth)
    {
        auto depths = [](const Expr &e)
        {
            std::vector<int> v(e.k, -1);
            std::function<void(int, int)> visit = [&](int lit, int d)
            {
                if (lit < 0)
                    return;
                if (lit / 2 < e.k)
                {
                    v[lit / 2] = std::max(v[lit / 2], d);
                    return;
                }
                auto p = e.a[lit / 2 - e.k];
                visit(p.first, d + 1);
                visit(p.second, d + 1);
            };
            visit(e.root, 0);
            return v;
        };
        if (depths(out) != depths(id))
            return id;
    }
    return out;
}
// Command-scoped stamped scratch avoids a per-cut tree map. Object IDs are
// rebound after every edit; no topology, truth or coordinate cache survives.
struct SparseExpressionReader
{
    std::vector<int> literals;
    std::vector<unsigned> stamp;
    unsigned epoch = 0;
    Expr read(Abc_Ntk_t *n, const Region &r, const std::vector<Abc_Obj_t *> &leaves,
              const std::vector<Abc_Obj_t *> *roots = nullptr, std::vector<int> *outputs = nullptr)
    {
        size_t size = Abc_NtkObjNumMax(n);
        literals.resize(size);
        stamp.resize(size);
        if (++epoch == 0)
        {
            std::fill(stamp.begin(), stamp.end(), 0);
            epoch = 1;
        }
        Expr e(leaves.size());
        for (size_t i = 0; i < leaves.size(); ++i)
        {
            stamp[leaves[i]->Id] = epoch;
            literals[leaves[i]->Id] = 2 * i;
        }
        auto visit = [&](auto &&self, Abc_Obj_t *o) -> int
        {
            if (stamp[o->Id] == epoch)
                return literals[o->Id];
            int value = -2;
            if (!Abc_AigNodeIsConst(o))
            {
                int a = self(self, Abc_ObjFanin0(o)) ^ Abc_ObjFaninC0(o);
                int b = self(self, Abc_ObjFanin1(o)) ^ Abc_ObjFaninC1(o);
                value = e.land(a, b);
            }
            stamp[o->Id] = epoch;
            return literals[o->Id] = value;
        };
        if (roots)
        {
            outputs->clear();
            outputs->reserve(roots->size());
            for (auto *v : *roots)
                outputs->push_back(visit(visit, v));
            if (!outputs->empty())
                e.root = outputs->back();
        }
        else
            e.root = visit(visit, Abc_NtkObj(n, r.root));
        return e;
    }
};
#include "tgDivisors.h"
#include "tgDsd.h"
std::vector<Candidate> sparseGenerate(const Expr &id, const Truth &truth, const std::vector<XY> &xy,
                                      const std::vector<int> &levels, const std::string &kind,
                                      int cap, int required, const std::vector<Box> &boundary = {},
                                      XY anchor = {0, 0}, SparseDivisors *divisors = nullptr,
                                      SparseDsd *dsd = nullptr,
                                      const std::string *originalKey = nullptr)
{
    TG_SPEED_SCOPE(Generate);
    const XY *rootAnchor = (nullptr);
    if (kind != "dsdlib" && kind != "dsd" && kind != "adaptive" && kind != "divisor" &&
        kind != "mixed" && kind != "compact" && kind != "tree" && kind != "treebox" &&
        kind != "treelevel")
        return generate(id, truth, xy, levels, kind, cap);
    std::vector<Candidate> out;
    std::set<std::string> seen;
    const std::string original = originalKey ? *originalKey : id.key(true);

    auto add = [&](Expr e, const char *label, const std::string *knownKey = nullptr,
                   bool factorVerified = false)
    {
        {
            auto same = [&](const Expr &other)
            { return e.k == other.k && e.root == other.root && e.a == other.a; };
            if (same(id) ||
                std::any_of(out.begin(), out.end(), [&](const Candidate &c) { return same(c.e); }))
                return;
        }
        auto key = knownKey ? *knownKey : e.key(true);
        bool fresh;
        fresh = key != original && std::none_of(out.begin(), out.end(),
                                                [&](const Candidate &c) { return c.key() == key; });
        // Structural equality is exact. Repeated candidates need no second
        // truth-table evaluation; all distinct proposals are still checked.
        if (!fresh && !TgSpeed::CareAudit())
            return;
        auto actualTruth =
            (factorVerified && tgEfficientGeneration && !TgSpeed::CareAudit()) ? truth : e.truth();
        if (actualTruth != truth)
        {
            Abc_Print(-1, "TG_SPARSE truth mismatch.\n");
            std::abort();
        }
        if (fresh)
            out.emplace_back(std::move(e), label, std::move(key), std::move(actualTruth));
    };
    if (kind == "tree" || kind == "treebox" || kind == "treelevel")
    {
        add(sparseGeometryTree(id, xy, levels, required, boundary, anchor, kind == "treelevel"),
            kind == "tree"        ? "geometry-tree"
            : kind == "treelevel" ? "geometry-leafdepth"
                                  : "geometry-netbox");
        if (cap > 1)
            add(spatial(id, xy, levels, 0, rootAnchor), "spatial-original");
        return out;
    }
    if (kind == "adaptive")
    {
        // A read-once cone uses every boundary variable exactly once and
        // contains k-1 AND nodes. It cannot reduce Boolean node count; spend
        // its effort on geometry. Other cones retain the compact generator.
        std::vector<int> references(id.k + id.a.size());
        for (auto pair : id.a)
        {
            if (pair.first >= 0)
                ++references[pair.first / 2];
            if (pair.second >= 0)
                ++references[pair.second / 2];
        }
        bool readOnce = int(id.a.size()) == id.k - 1;
        for (int i = 0; i < int(references.size()); ++i)
            if (i != id.root / 2)
                readOnce &= references[i] == 1;
        if (readOnce)
        {
            add(spatial(id, xy, levels, 0, rootAnchor), "readonce-spatial");
            return out;
        }
    }
    if ((kind == "dsd" || kind == "dsdlib") && cap == 1)
    {
        add(dsd->generate(truth, id.k, xy, levels),
            kind == "dsdlib" ? "dsd-library" : "dsd-geometry");
        return out;
    }
    std::vector<int> order(id.k);
    std::iota(order.begin(), order.end(), 0);
    Expr ordinary(id.k);
    std::string ordinaryKey;
    if (!factor(ordinary, truth, order, false, &ordinaryKey))
        return out;
    add(ordinary, "ordinary", &ordinaryKey, true);
    {
        (void)(kind == "compact" && 0);
    }
    if (kind == "dsdlib")
    {
        auto factory = std::move(dsd->primeFactory);
        dsd->primeFactory = {};
        add(dsd->generate(truth, id.k, xy, levels), "dsd-geometry");
        dsd->primeFactory = std::move(factory);
        if (cap > 2)
            add(dsd->generate(truth, id.k, xy, levels), "dsd-library");
        if (cap > 3)
            add(spatial(id, xy, levels, 0, rootAnchor), "spatial-original");
        if (cap > 4)
            add(dsd->generate(truth, id.k, xy, levels, true), "dsd-library-arrival");
        return out;
    }
    if (kind == "dsd")
    {
        add(dsd->generate(truth, id.k, xy, levels), "dsd-geometry");
        if (cap > 2)
            add(spatial(id, xy, levels, 0, rootAnchor), "spatial-original");
        if (cap > 3)
            add(dsd->generate(truth, id.k, xy, levels, true), "dsd-arrival");
        return out;
    }
    if (kind == "divisor" || kind == "mixed")
    {
        if (kind == "mixed" && cap > 1)
            add(spatial(id, xy, levels, 0, rootAnchor), "spatial-original");
        int remaining = cap - (kind == "mixed" ? 2 : 1);
        if (divisors && remaining > 0)
            for (auto &e : divisors->generate(truth, id.k, xy, 2 * remaining))
            {
                add(std::move(e), "geometry-divisor");
                if (int(out.size()) >= cap)
                    break;
            }
        return out;
    }
    if (cap > 1)
        add(spatial(id, xy, levels, 0, rootAnchor), "spatial-original");
    if (cap > 2)
        add(spatial(ordinary, xy, levels, 0, rootAnchor), "spatial-factor");
    if (cap > 3)
    {
        std::stable_sort(order.begin(), order.end(),
                         [&](int a, int b) { return xy[a].x + xy[a].y < xy[b].x + xy[b].y; });
        Expr e(id.k);
        if (factor(e, truth, order))
            add(std::move(e), "geometry-factor");
    }
    return out;
}

// Library-assisted Boolean candidates are imported from ABC's fixed 4-input
// forest. TG still chooses the regions; no native RW traversal is invoked.
#include "tgLibraryData.h"

struct SparseLibrary
{
    Rwr_Man_t *man = nullptr;
    struct Metadata
    {
        std::vector<std::string> keys;
        size_t minimum[2] = {1000, 1000};
    };
    struct Data
    {
        std::map<unsigned, std::vector<Expr>> cache;
        std::map<unsigned, Metadata> metadata;
    };
    static Data &SharedData()
    {
        static Data data;
        return data;
    }
    Data localData;
    std::map<unsigned, std::vector<Expr>> &cache;
    std::map<unsigned, Metadata> &metadata;
    SparseLibrary() : cache(((SharedData())).cache), metadata(((SharedData())).metadata) {}
    SparseLibrary(const SparseLibrary &) = delete;
    SparseLibrary &operator=(const SparseLibrary &) = delete;
    void BoundCache()
    {
        if (cache.size() >= 1024)
        {
            cache.clear();
            metadata.clear();
        }
    }
    long queries = 0, hits = 0, proposals = 0;
    ~SparseLibrary()
    {
        if (man)
            Rwr_ManStop(man);
    }

    const std::vector<Expr> &lookup(unsigned truth)
    {
        ++queries;
        auto hit = cache.find(truth);
        if (hit != cache.end())
        {
            ++hits;
            return hit->second;
        }
        auto *dec = (Dec_Man_t *)Abc_FrameReadManDec();
        int cl = dec->pMap[truth];
        const int *perm = tgLibraryPerms + 4 * (unsigned char)dec->pPerms[truth];
        unsigned phase = (unsigned char)dec->pPhases[truth];
        BoundCache();
        metadata.erase(truth); // A rebuilt library entry invalidates its derived keys.
        auto &out = cache[truth];
        std::set<std::string> seen;
        for (int index = tgLibraryClasses[cl]; index < tgLibraryClasses[cl + 1]; ++index)
        {
            const int *g = tgLibraryData + tgLibraryOffsets[index];
            Expr e(4);
            if (g[0])
                e.root = ((g[1] & 1) ? -1 : -2) ^ ((phase >> 4) & 1);
            else
            {
                std::vector<int> literals(4 + g[2]);
                for (int k = 0; k < 4; ++k)
                    literals[k] = 2 * perm[k] ^ ((phase >> k) & 1);
                for (int k = 0; k < g[2]; ++k)
                {
                    int x = g[3 + 2 * k], y = g[4 + 2 * k];
                    literals[4 + k] = e.land(literals[x / 2] ^ (x & 1), literals[y / 2] ^ (y & 1));
                }
                e.root = literals[g[1] / 2] ^ (g[1] & 1) ^ ((phase >> 4) & 1);
            }
            if ((e.truth()[0] & 65535) != truth)
            {
                Abc_Print(-1, "TG_SPARSE static library truth mismatch.\n");
                std::abort();
            }
            if (seen.insert(e.key()).second)
                out.push_back(std::move(e));
        }
        return out;
    }
    std::vector<Candidate> generate(const Expr &id, const Truth &truth, const std::vector<XY> &xy,
                                    const std::vector<int> &levels, int cap, int required,
                                    bool positiveRoot = false,
                                    const std::string *originalKey = nullptr,
                                    const std::vector<Abc_Obj_t *> *leafObjects = nullptr,
                                    Abc_Obj_t *rootObject = nullptr)
    {
        if (id.k != 4 || truth[0] == 0 || truth[0] == ~0u)
            return sparseGenerate(id, truth, xy, levels, "ordinary", cap, required);
        const auto &all = lookup(truth[0] & 65535);

        std::vector<std::pair<double, int>> ranks;
        auto &meta = metadata[truth[0] & 65535];
        if (meta.keys.size() != all.size())
        {
            meta = Metadata{};
            for (const auto &e : all)
            {
                meta.keys.push_back(e.key(true));
                meta.minimum[0] = std::min(meta.minimum[0], e.a.size());
                if (e.root < 0 || !(e.root & 1))
                    meta.minimum[1] = std::min(meta.minimum[1], e.a.size());
            }
        }
        std::string original = originalKey ? *originalKey : id.key(true);
        double scale = 0;
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < i; ++j)
                scale += std::abs(xy[i].x - xy[j].x) + std::abs(xy[i].y - xy[j].y);
        scale = std::max(1e-12, scale / 6);
        const size_t minimumSize = meta.minimum[positiveRoot ? 1 : 0];
        for (int index = 0; index < int(all.size()); ++index)
        {
            const auto &e = all[index];
            // Apply the same phase feasibility rule before truncating the
            // library shortlist; otherwise infeasible alternatives consume it.
            if (positiveRoot && e.root >= 0 && (e.root & 1))
                continue;
            if ((!false && e.a.size() > minimumSize + 1) || meta.keys[index] == original)
                continue;
            std::vector<Abc_Obj_t *> realized;

            TgSpeed::Scratch<XY, 64> pos(4 + e.a.size());
            TgSpeed::Scratch<int, 64> depth(4 + e.a.size());
            for (int i = 0; i < 4; ++i)
            {
                pos[i] = xy[i];
                depth[i] = levels[i];
            }
            size_t next = 4;
            double wire = 0;
            for (auto pair : e.a)
            {
                int x = pair.first / 2, y = pair.second / 2;
                wire += std::abs(pos[x].x - pos[y].x) + std::abs(pos[x].y - pos[y].y);
                pos[next] = {(pos[x].x + pos[y].x) / 2, (pos[x].y + pos[y].y) / 2};
                depth[next++] = 1 + std::max(depth[x], depth[y]);
            }
            if (e.root >= 0 && depth[e.root / 2] > required)
                continue;
            ranks.emplace_back(wire / scale + ((.25 * e.a.size())), index);
        }
        proposals += ranks.size();
        std::sort(ranks.begin(), ranks.end());
        if (ranks.size() > size_t(cap))
            ranks.resize(cap);
        std::vector<Candidate> out;
        for (auto rank : ranks)
            out.emplace_back(all[rank.second], "library-geometry", meta.keys[rank.second], truth);
        return out;
    }
};

// Enumerate a small family of exact, live four-leaf boundaries. Each step
// replaces a frontier node by its actual fanins, so every retained boundary
// still covers the root. A bounded breadth-first search avoids deep whole-cone
// traversal and does not use cached cuts after edits.

std::vector<std::vector<Abc_Obj_t *>> sparseFourCuts(Abc_Obj_t *root)
{

    struct Frontier
    {
        std::array<int, 5> ids{};
        int size = 0, depth = 0;
    };
    // At most 48 expanded frontiers, with <=4 successors each. The extra
    // fifth slot is used only while replacing one node by its two fanins.
    std::vector<Frontier> queue;
    queue.reserve(193);
    std::vector<std::vector<Abc_Obj_t *>> result;
    result.reserve(16);
    auto insert = [&](Frontier f)
    {
        std::sort(f.ids.begin(), f.ids.begin() + f.size);
        f.size = int(std::unique(f.ids.begin(), f.ids.begin() + f.size) - f.ids.begin());
        if (f.size > 4)
            return;
        for (const auto &v : queue)
            if (v.size == f.size &&
                std::equal(f.ids.begin(), f.ids.begin() + f.size, v.ids.begin()))
                return;
        queue.push_back(f);
    };
    Frontier first;
    first.size = 2;
    first.ids[0] = Abc_ObjFaninId0(root);
    first.ids[1] = Abc_ObjFaninId1(root);
    insert(first);
    for (size_t at = 0; at < queue.size() && at < 48 && result.size() < size_t(16); ++at)
    {
        const auto current = queue[at];
        if (current.size >= 3 && (1 || current.size == 4))
        {
            std::vector<Abc_Obj_t *> leaves;
            leaves.reserve(current.size);
            for (int i = 0; i < current.size; ++i)
                leaves.push_back(Abc_NtkObj(root->pNtk, current.ids[i]));
            result.push_back(std::move(leaves));
        }
        if (current.depth >= 6)
            continue;
        for (int i = 0; i < current.size; ++i)
        {
            auto *v = Abc_NtkObj(root->pNtk, current.ids[i]);
            if (!Abc_ObjIsNode(v) || Abc_AigNodeIsConst(v))
                continue;
            Frontier next;
            next.depth = current.depth + 1;
            for (int j = 0; j < current.size; ++j)
                if (i != j)
                    next.ids[next.size++] = current.ids[j];
            next.ids[next.size++] = Abc_ObjFaninId0(v);
            next.ids[next.size++] = Abc_ObjFaninId1(v);
            insert(next);
        }
    }

    return result;
}
// Expose nearby pre-existing divisors as additional cut inputs. Their relation
// to the original boundary is established by SparseCare, never assumed.
// The strict live level bound excludes root descendants and therefore cycles.

#include "tgCare.h"

#include "tgGeometryCut.h"

int compactRounds(Abc_Frame_t *frame, int maximum)
{
    const bool rsOnly = false, unified = true;
    const int operators = 3;
    constexpr int resubSteps = 0;
    const int timing = 1, timingScore = 2, rounds = 4, percent = 25, cutSize = 10, cap = 3,
              mode = 0, growth = 0, zero = 1, shared = 0, logic = 0, margin = 0, areaGuard = 1,
              phaseGuard = 2, novel = 0, paired = 0, reuseEmpty = 0, memory = 1, warm = 0;
    // The caller freezes the budget before the broad operator pass.
    const std::string frontier = "native", generator = "compact", order = "level",
                      ranking = "diverse";
    auto *n = Abc_FrameReadNtk(frame);
    if (!n || !Abc_NtkIsStrash(n) || Abc_NtkLatchNum(n) || Abc_NtkGetChoiceNum(n) || n->pExdc ||
        n->pExcare || n->pManTime || !Tg_ManHasPlacement(n))
        return 1;
    TG_VERBOSE("TG_POLICY mode=%d physical_evaluation=unchanged\n", proposalMode());

    const bool rsWindow = rsOnly && 0;

    const int odcDepth = (0);

    const int careDepth = (6);
    const int adapt = (3);
    const int cutLearn = (3);

    const bool rwEnabled = 1 || unified;

    TG_VERBOSE("TG_UNIFIED_POLICY operators=%d rs_steps=%d divisors=%d proposals=%d rs_cuts=%d "
               "rs_leaves=%d collect=%d macro=%d min_rs_gain=%d root_percent=%d root_cap=%d\n",
               operators, resubSteps, 32, 32, 2, 10, 0, 1, 1, percent, maximum);

    auto start = Clock::now();
    TG_VERBOSE(
        "TG_PARAMETERS area=%.9g anchor=%.9g crowd=%.9g alpha=%.9g priority=%.9g refine=%d "
        "generator=%d steiner=%d lookahead=%d cuts=%d care=%d library=%d advanced=%d reuse=%d\n",
        1, .5, .25, .5, 0, 0, 0, 0, 0, 2, 6, 1, 0, 0);
    TG_VERBOSE("TG_SEARCH_POLICY class_adapt=%d cut_learn=%d first_gain=%d incremental_scan=%d\n",
               adapt, cutLearn, 1, 1);
    double h0 = 0, areaInitial = 0;
    Tg_ManReadMetrics(n, &h0, nullptr, nullptr, &areaInitial);
    int nodes0 = Abc_NtkNodeNum(n), depth0 = Abc_NtkLevel(n);
    TgEval_ManConfigure(mode, growth, h0, areaInitial);
    TgEval_ManSetPhysicalAreaGuard(areaGuard);
    // Use the paper timing score with bounded RW/RF timing maintenance.
    // Every accepted edit refreshes the affected timing dependencies.
    struct TimingScope
    {
        bool enabled;
        ~TimingScope()
        {
            if (enabled)
            {
                TgEval_ManSetTimingEvaluation(0);
                TgEval_ManSetTimingEffort(0);
                TgEval_ManSetTimingWeight(0.50);
                TgEval_ManSetScoreMode(0);
            }
        }
    } timingScope{timing != 0};
    TgEval_ManSetTimingEvaluation(timing);
    TgEval_ManSetTimingEffort((((0))));
    TgEval_ManSetTimingWeight(0.50);
    TG_VERBOSE("TG_TIMING enabled=%d weight=0.5 effort=%d score_units=%s hpwl_only_bound=%d\n",
               timing, (((0))), ("pa_dimensionless"),
               int(1 && mode == 3 && !paired && !timing && 4 == 0));
    // Score mode 2 changes only timing. Keep the untimed path (including its
    // proven HPWL bound) unchanged when -t is absent.
    TgEval_ManSetScoreMode((timingScore));
    TG_VERBOSE("TG_TIMING_STYLE score=%d node_weight=%.3f\n", (timingScore), 4);
    TgEval_ManSetClusterEvaluation(0);
    TgEval_ManSetBalancedRefactor(0);
    TgGenerationSession session(true);
    SparseLibrary library;
    SparseDivisors divisors;
    SparseDsd dsd;

    SparseExpressionReader reader;
    SparseCare careManager;
    careManager.disableSemantic = odcDepth != 0;

    // Only candidate construction is cached. Exact expression storage, ordered
    // boundary identity, care, coordinates and levels define its full context.
    // Every returned candidate still receives fresh physical evaluation.
    std::unordered_map<std::string, std::vector<Candidate>> generationMemo;

    long generationMemoHits = 0;
    // Only cache the absence of candidates for an exact cut expression with no
    // associative spatial freedom. No placement, score, or rejection is cached.
    std::unordered_set<std::string> emptyRegions;
    long emptyHits = 0, emptyInserted = 0;
    Abc_NtkStartReverseLevels(n, 0);
    bool ok = Tg_ManBeginPass(n) && TgEval_ManPrepareTimingPass(n);
    auto *manager = (Abc_NtkManCutStart(cutSize, 16, 2, 1000));
    // Rebuild every alternative boundary from the live graph at this root.
    // Selection is still performed once per round; no cut survives a commit.
    std::vector<decltype(manager)> cutManagers{manager};
    for (int size : {4, 6, 8, 10})
        if (size < cutSize)
            cutManagers.push_back(Abc_NtkManCutStart(size, 16, 2, 1000));

    // Command-scoped empirical cut-family scheduling, never an equivalence cache.
    struct CutLearning
    {
        long attempts = 0, wins = 0;
    };
    std::array<CutLearning, 26> localCutLearning{};

    auto &cutLearning = (localCutLearning);

    long cutLearningSkipped = 0, earlyRoots = 0;
    long accepted = 0, evaluated = 0, stale = 0, candidateCount = 0, selected = 0;
    long bridgeAccepted = 0;
    // A rejection is reused only while NO edit has occurred anywhere in this
    // invocation. Thus graph, positions, density, levels and score references
    // are identical. Ordered boundary and cut position preserve generation.
    std::unordered_map<std::string, int> rejectedCuts;
    long rejectionVersion = -1, rejectionHits = 0, rejectionSaved = 0;
    double selection = 0, construct = 0, scoring = 0, commit = 0;
    long proofPhysicalChecks = 0, proofPhysicalViable = 0;
    double proofPhysicalSeconds = 0;
    // Observational coverage only: object IDs are append-only until the final reassignment.
    // Distinct root IDs do not imply disjoint Boolean cones.
    const int initialObjectLimit = Abc_NtkObjNumMax(n);
    std::vector<unsigned char> rootVisits(initialObjectLimit, 0);
    std::map<std::string, long> kinds;

    const bool metadataAudit = TgSpeed::CareAudit();
    std::map<std::string, std::array<double, 4>> cutStats;
    static int coCacheEpoch = -1;
    static TgOpportunityMemory coMemory;
    static SparseShapeCache coShapes;
    static std::unique_ptr<SparseScan> coScan;
    static std::vector<double> coLastPriority;
    if (Tg_InFlight() && coCacheEpoch != Tg_Epoch())
    {
        coMemory = TgOpportunityMemory{};
        coShapes = SparseShapeCache{};
        coScan.reset();
        coLastPriority.clear();
        coCacheEpoch = Tg_Epoch();
    }
    TgOpportunityMemory localMemory;
    auto &opportunityMemory = Tg_InFlight() ? coMemory : localMemory;
    opportunityMemory.enabled = memory;
    const bool trackHistory = false || (true && memory);
    SparseShapeCache localShapes;
    auto &shapeCache = (CoSparseShared().shapes);
    std::unique_ptr<SparseScan> localScan;
    auto &scanCache = (CoSparseShared().scan);
    // End a compact block when two complete rounds yield little node/HPWL
    // improvement. Unexplored roots may still improve; this is a work policy.

    const int yieldThreshold = 20;

    double blockHpwl = h0;
    int blockNodes = Abc_NtkNodeNum(n);
    long blockSelected = 0;
    int completedRounds = 0;
    // compact-round root filter. Each round's roots are split into
    // tension-priority tenths; statistics pool over the block's rounds; a tenth
    // is skipped once its smoothed acceptance < rho * overall smoothed acceptance.
    const double compactFilter = (0.5);
    int cfN[10] = {0}, cfK[10] = {0}, cfClosed[10] = {0}, cfAllN = 0, cfAllK = 0;
    long cfSkipped = 0;
    for (int round = 0; round < rounds && ok; ++round)
    {
        auto scanStart = Clock::now();
        const double sel0 = selection, gen0 = construct, score0 = scoring, commit0 = commit;
        const long candidates0 = candidateCount;
        const int roundNodes0 = Abc_NtkNodeNum(n);
        rootVisits.resize(Abc_NtkObjNumMax(n), 0);
        long firstSelected = 0, createdFirstSelected = 0;
        long firstEvaluated = 0, createdFirstEvaluated = 0;
        const bool trace = ((char *)0) != nullptr;

        std::unique_ptr<SparseScan> freshScan;
        {
            if (!scanCache)
            {
                scanCache.reset(new SparseScan(n, true));
                scanCache->captureInputs(n);
            }
            else
                scanCache->refreshGeometry(n);
        }
        auto &scan = (*scanCache);
        // Selection only: emphasize renewed geometric conflict and critical cones.
        // Structural/care validity still comes from fresh candidate checks.

        const bool fastSelection = true;
        const bool fastHistory = 1 && trackHistory && true && !trace;
        scan.prepareOpportunities(n,
                                  fastSelection && true && !trace && (!trackHistory || fastHistory),
                                  fastSelection, (&shapeCache));

        opportunityMemory.prepare(n, scan, false, fastHistory);

        // Allocate more slots to classes that produced useful local gain.
        // Hashes define heuristic classes only; candidates are always rebuilt
        // and checked against the live Boolean/physical context.
        std::unordered_map<unsigned, double> classWeights;
        {
            for (const auto &item : opportunityMemory.classes)
            {
                const auto &v = item.second;

                classWeights[item.first] = ((std::max(.05, (1 + v.gain) / (4 + v.attempts))));
            }
        }

        scan.actionPriority.clear();

        const int screenPercent = (percent);
        auto roots = (scan.roots(n, screenPercent, (maximum), false, zero, shared, logic, manager,
                                 ranking, (nullptr), ((&opportunityMemory.novelty)), false,
                                 classWeights.empty() ? nullptr : &classWeights));

        opportunityMemory.prepareSelected(n, scan, roots);
        {
            std::vector<uint64_t> keys;
            keys.reserve(roots.size());
            for (int id : roots)
                keys.push_back((uint64_t(Abc_NtkObj(n, id)->Level) << 32) | unsigned(id));
            std::sort(keys.begin(), keys.end());
            for (size_t i = 0; i < keys.size(); ++i)
                roots[i] = int(keys[i] & 0xffffffffu);
        }

        selection += std::chrono::duration<double>(Clock::now() - scanStart).count();
        selected += roots.size();
        long ev0 = evaluated, st0 = stale, ac0 = accepted;
        long actionCuts = 0, actionMissing = 0, actionIncluded = 0;
        std::unordered_map<int, int> cfGroup;
        int cfPrevGroup = -1;
        long cfPrevAcc = 0;
        {

            std::vector<std::pair<double, int>> ranked;
            for (int id : roots)
            {
                double key = scan.rootPriority(n, id);

                ranked.push_back({key, id});
            }
            std::sort(ranked.begin(), ranked.end(),
                      [](const std::pair<double, int> &x, const std::pair<double, int> &y)
                      { return x.first != y.first ? x.first > y.first : x.second < y.second; });
            for (size_t i = 0; i < ranked.size(); ++i)
                cfGroup[ranked[i].second] = int(i * 10 / std::max<size_t>(1, ranked.size()));
        }
        auto cfFinish = [&]()
        {
            if (cfPrevGroup < 0)
                return;
            const int g = cfPrevGroup;
            cfPrevGroup = -1;
            ++cfN[g];
            ++cfAllN;
            if (accepted > cfPrevAcc)
            {
                ++cfK[g];
                ++cfAllK;
            }
            if ((cfK[g] + 1.) / (cfN[g] + 2.) < compactFilter * (cfAllK + 1.) / (cfAllN + 2.))
                cfClosed[g] = 1;
        };
        for (int rootId : roots)
        {
            cfFinish();
            {
                const int g = cfGroup[rootId];
                if (cfClosed[g])
                {
                    ++cfSkipped;
                    continue;
                }
                cfPrevGroup = g;
                cfPrevAcc = accepted;
            }
            auto &visit = rootVisits[rootId];
            if (!(visit & 1))
            {
                ++firstSelected;
                createdFirstSelected += rootId >= initialObjectLimit;
                visit |= 1;
            }
            auto *root = Abc_NtkObj(n, rootId);
            if (!root || !Abc_ObjIsNode(root) || !Abc_ObjFanoutNum(root))
            {
                ++stale;
                continue;
            }
            ++evaluated;
            if (!(visit & 2))
            {
                ++firstEvaluated;
                createdFirstEvaluated += rootId >= initialObjectLimit;
                visit |= 2;
            }
            bool memoryAccepted = false;
            int memoryWork = 1;
            struct Observation
            {
                TgOpportunityMemory *m;
                int id;
                bool &a;
                int &w;
                Abc_Ntk_t *n;
                int before;
                ~Observation()
                {
                    if (m)
                        m->observe(id, a, w);
                    ((void)0);
                }
            } observation{(&opportunityMemory), rootId, memoryAccepted,
                          memoryWork,           n,      Abc_NtkNodeNum(n)};

            auto genStart = Clock::now();

            auto traceRoot = [&](int candidates, double gain, bool accepted) { return; };
            bool rootWinner = false, rootBridge = false;
            double rootBest = 1e-10;
            int rootGain = 0, rootCandidates = 0;
            Expr rootExpression(0);
            std::vector<Abc_Obj_t *> rootLeaves;
            std::string rootKind, rootCutFamily;
            std::set<std::vector<int>> seenCuts;
            std::array<std::array<int, 13>, 32> seenCutStorage;
            size_t seenCutCount = 0;

            std::vector<Abc_Obj_t *> actionLeaves;
            Expr actionExpression(4);
            const bool hasAction = false;
            actionCuts += hasAction;
            auto extraCuts = (sparseFourCuts(root));

            {
                for (int size : {6, 10})
                {
                    if (size > cutSize || (2 == 1 && size != cutSize))
                        continue;
                    auto region = sparseGreedyCut(n, rootId, scan, size, 32);
                    std::vector<Abc_Obj_t *> boundary;
                    for (int id : region.leaves)
                        boundary.push_back(Abc_NtkObj(n, id));
                    extraCuts.push_back(std::move(boundary));
                }
            }
            const int wideMode =
                (operators & 2) && Tg_InFlight() && !rsWindow && ((char *)"2") ? 2 : 0;
            if (wideMode < 0 || wideMode > 3)
                std::abort();

            std::vector<Abc_Obj_t *> wideLeaves;
            if (wideMode)
            {
                auto wide = geometryCut(n, root);
                if (wide.leaves.size() > 4)
                    for (int id : wide.leaves)
                        wideLeaves.push_back(Abc_NtkObj(n, id));
            }
            const bool hasWide = !wideLeaves.empty();
            construct += std::chrono::duration<double>(Clock::now() - genStart).count();
            for (size_t cutAt = 0; cutAt < cutManagers.size() + extraCuts.size() +
                                               size_t(hasAction) + size_t(hasWide);
                 ++cutAt)
            {
                const bool wideCut = hasWide && cutAt == 0;
                const bool actionCut = hasAction && cutAt == size_t(hasWide);
                const int regularAt = int(cutAt) - int(hasAction) - int(hasWide);
                auto *activeManager = !wideCut && !actionCut && regularAt < int(cutManagers.size())
                                          ? cutManagers[regularAt]
                                          : nullptr;

                genStart = Clock::now();
                Region r;
                TgSpeed::WorkspaceVector<Abc_Obj_t *> leaves;
                Expr id(0);
                {
                    TG_SPEED_SCOPE(Region);
                    if (wideCut)
                    {
                        leaves = wideLeaves;
                        r.root = rootId;
                    }
                    else
                    {
                        if (activeManager)
                        {
                            auto *cut = Abc_NodeFindCut(activeManager, root, 0);
                            Abc_Obj_t *v;
                            int j;
                            Vec_PtrForEachEntry(Abc_Obj_t *, cut, v, j) leaves.push_back(v);
                        }
                        else
                            leaves = extraCuts[regularAt - cutManagers.size()];
                        r.root = rootId;
                    }

                    if (leaves.size() < 2 || leaves.size() > size_t(((cutSize))))
                    {
                        construct += std::chrono::duration<double>(Clock::now() - genStart).count();
                        traceRoot(0, 0, false);
                        continue;
                    }
                    {
                        bool fresh = true;
                        {
                            std::array<int, 13> ids{};
                            ids[0] = int(leaves.size());
                            for (size_t i = 0; i < leaves.size(); ++i)
                                ids[i + 1] = leaves[i]->Id;
                            std::sort(ids.begin() + 1, ids.begin() + 1 + leaves.size());
                            for (size_t i = 0; i < seenCutCount; ++i)
                                if (ids == seenCutStorage[i])
                                {
                                    fresh = false;
                                    break;
                                }
                            if (fresh)
                            {
                                assert(seenCutCount < seenCutStorage.size());
                                seenCutStorage[seenCutCount++] = ids;
                            }
                        }
                        if (!fresh)
                        {
                            construct +=
                                std::chrono::duration<double>(Clock::now() - genStart).count();
                            continue;
                        }
                    }
                    id = reader.read(n, r, leaves);
                }
                if (id.a.size() < size_t((2)))
                {
                    construct += std::chrono::duration<double>(Clock::now() - genStart).count();
                    traceRoot(0, 0, false);
                    continue;
                }

                const int cutClass = (activeManager ? 0 : 13) + id.k;
                auto &cutEvidence = cutLearning[cutClass];
                // After 32 observations, retain periodic exploration for families
                // that have rarely supplied an improving incumbent. This changes
                // search coverage, not score/proof validity, and never rolls back.
                if (!actionCut && cutLearn && cutEvidence.attempts >= 32)
                {
                    int period = ((16));
                    const bool poor =
                        cutEvidence.wins == 0 ||
                        (cutLearn == 3 && cutEvidence.wins * 100 < cutEvidence.attempts);
                    if (!0 && poor && (evaluated + cutAt + round) % period)
                    {
                        ++cutLearningSkipped;
                        construct += std::chrono::duration<double>(Clock::now() - genStart).count();
                        continue;
                    }
                }
                ++cutEvidence.attempts;
                std::string rejectionKey;
                if (!actionCut && !((char *)0) && 1 && !resubSteps && !warm && !0 && true &&
                    !rootWinner)
                {
                    if (rejectionVersion != accepted)
                    {
                        rejectedCuts.clear();
                        rejectionVersion = accepted;
                    }
                    auto append = [&](int value)
                    { rejectionKey.append(reinterpret_cast<const char *>(&value), sizeof(value)); };
                    append(rootId);
                    append(int(cutAt));
                    for (auto *v : leaves)
                        append(v->Id);
                    auto found = rejectedCuts.find(rejectionKey);
                    if (found != rejectedCuts.end())
                    {
                        ++rejectionHits;
                        rejectionSaved += found->second;
                        int work = int(id.a.size()) + found->second;
                        if (cutAt == 0)
                            memoryWork = work;
                        else
                            memoryWork += work;
                        construct += std::chrono::duration<double>(Clock::now() - genStart).count();
                        continue;
                    }
                }
                std::string cutFamily;

                std::string emptyKey;

                auto truth = id.truth();
                const auto originalKey = id.key(true);
                TgSpeed::WorkspaceVector<XY> xy;
                TgSpeed::WorkspaceVector<int> levels;
                for (auto *v : leaves)
                {
                    XY p = scan.pos[rootId];
                    proposalPosition(n, v, &p.x, &p.y);
                    xy.push_back(p);
                    levels.push_back(v->Level);
                }
                std::vector<Box> boundary;
                XY anchor = scan.pos[rootId];
                proposalPosition(n, root, &anchor.x, &anchor.y);
                std::set<int> removed;

                Truth care(truth.size(), ~0u);
                care = careManager.reachable(n, leaves, careDepth);

                std::vector<Candidate> globalProofCandidates;
                double earlyPhysical = 0;

                std::string generationKey;

                auto memoAt = (generationMemo.end());
                const bool memoHit = memoAt != generationMemo.end();
                std::vector<Candidate> candidates;
                if (memoHit && !metadataAudit)
                {
                    candidates = memoAt->second;
                    ++generationMemoHits;
                }
                else
                {
                    candidates = (sparseGenerate(id, truth, xy, levels, generator, cap,
                                                 Abc_ObjRequiredLevel(root), boundary, anchor,
                                                 &divisors, &dsd, &originalKey));

                    if ((operators & 2) && rwEnabled && id.k == 4)
                    {
                        auto extra = library.generate(
                            id, truth, xy, levels, std::max(4, cap), Abc_ObjRequiredLevel(root),
                            !1 && 0 && phaseGuard &&
                                (phaseGuard == 1 || Abc_ObjFanoutNum(root) > 1),
                            &originalKey, &leaves, root);
                        for (auto &c : extra)
                        {
                            if (std::none_of(candidates.begin(), candidates.end(),
                                             [&](const Candidate &v)
                                             { return v.key() == c.key(); }))
                                candidates.push_back(std::move(c));
                        }
                    }
                    careManager.append(candidates, id, truth, care, xy, levels, &originalKey);
                    if (memoHit)
                    {
                        ++generationMemoHits;
                        const auto &expected = memoAt->second;
                        if (candidates.size() != expected.size())
                            std::abort();
                        for (size_t i = 0; i < candidates.size(); ++i)
                            if (candidates[i].key() != expected[i].key() ||
                                candidates[i].truth() != expected[i].truth())
                                std::abort();
                    }
                    else
                    {
                    }
                }

                for (auto &proposal : globalProofCandidates)
                    if (std::none_of(candidates.begin(), candidates.end(),
                                     [&](const Candidate &v) { return v.key() == proposal.key(); }))
                        candidates.push_back(std::move(proposal));

                {
                    (void)(Tg_InFlight() && 0 == 3 && (operators & 1));
                }

                if (cutAt == 0)
                    memoryWork = int(id.a.size() + candidates.size());
                else
                    memoryWork += int(id.a.size() + candidates.size());

                construct += std::chrono::duration<double>(Clock::now() - genStart).count();
                // Reclassify the early evaluator work rather than double-counting
                // it as both generation and scoring. Total process timing is intact.
                construct -= earlyPhysical;
                scoring += earlyPhysical;
                proofPhysicalSeconds += earlyPhysical;
                int winner = -1, winGain = 0;
                double best = rootBest;
                auto scoreStart = Clock::now();
                // Evaluation does not mutate traversal IDs or topology. Mark once
                // for this fixed root/cut; commit performs its own fresh marking.
                int saved = 0;
                if (!candidates.empty())
                {
                    for (auto *v : leaves)
                        ++v->vFanouts.nSize;
                    Abc_NtkIncrementTravId(n);
                    saved = Abc_NodeMffcLabelAig(root);
                    for (auto *v : leaves)
                        --v->vFanouts.nSize;
                }

                std::vector<std::pair<double, int>> ranked83;

                for (int j = 0; j < int(candidates.size()); ++j)
                {
                    ++candidateCount;
                    auto &c = candidates[j];

                    if (!SparseCare::equivalent(c.truth(), truth, care))
                    {
                        ok = false;
                        break;
                    }
                    // Preserve boundary polarity when requested. Complemented
                    // replacement roots change the stored phase of all fanout cuts.
                    const bool phaseRestricted = phaseGuard && c.e.root >= 0 && (c.e.root & 1) &&
                                                 (phaseGuard == 1 || Abc_ObjFanoutNum(root) > 1);

                    auto *g = c.e.graph(leaves);
                    int gain = 0;
                    double score = 0, oldHpwl = 0, newHpwl = 0;
                    TgEval_ManSetCandidateScoreFloor(best);
                    bool valid =
                        TgEval_ManEvaluateCandidate(root, g, saved, Abc_ObjRequiredLevel(root), 0,
                                                    &gain, &score, &oldHpwl, &newHpwl, nullptr);
                    Dec_GraphFree(g);

                    if (phaseRestricted && gain <= 0)
                        valid = false;

                    // Optional pre-commit robustness margin for area-neutral edits.
                    // No final placement, output selection, or rollback is involved.

                    // The incumbent may come from an earlier cut. Apply the
                    // same numerical tie rule across cuts as within a cut; a
                    // reset per-cut winner must not promote roundoff-only gains.
                    if (valid && score > best &&
                        ((!rootWinner && winner < 0) ||
                         score - best >
                             1e-10 * std::max(1.0, std::max(std::abs(score), std::abs(best)))))
                    {
                        best = score;
                        winner = j;
                        winGain = gain;
                    }
                }

                scoring += std::chrono::duration<double>(Clock::now() - scoreStart).count();
                rootCandidates += int(candidates.size());
                size_t cutCandidates = candidates.size();
                if (winner >= 0 && ok)
                {
                    ++cutEvidence.wins;
                    rootWinner = true;
                    rootBest = best;
                    rootGain = winGain;
                    rootExpression = std::move(candidates[winner].e);
                    rootLeaves = leaves;
                    rootKind = candidates[winner].kind;
                    rootCutFamily = cutFamily;
                }

                // RS proposals use their own live divisor boundary and compete
                // with the RW/RF incumbent before any mutation or early stopping.

                if (ok && !rootWinner && !rejectionKey.empty())
                {
                    if (rejectedCuts.size() >= 32768)
                        rejectedCuts.clear();
                    rejectedCuts.emplace(std::move(rejectionKey), int(cutCandidates));
                }
                if (!ok)
                    break;
                if (!0 && 1 && rootWinner && (1 == 3 || rootGain >= 1))
                {
                    ++earlyRoots;
                    break;
                }
            } // choose one replacement from the processed live cuts
            auto commitStart = Clock::now();
            Vec_Ptr_t *vl = nullptr;
            if (rootWinner && ok)
            {

                vl = Vec_PtrAlloc(rootLeaves.size());
                for (auto *v : rootLeaves)
                    Vec_PtrPush(vl, v);
                auto *g = rootExpression.graph(rootLeaves);
                ok = TgEval_ManCommitCandidate(root, g, vl, 1, rootGain);
                Dec_GraphFree(g);
                if (ok)
                {
                    ++accepted;
                    memoryAccepted = true;
                    bridgeAccepted += rootBridge;

                    opportunityMemory.classes[opportunityMemory.shapes[rootId]].gain +=
                        rootBest / std::max(1e-9, h0 / std::max(1, nodes0));
                    ++kinds[rootKind];
                }
            }
            commit += std::chrono::duration<double>(Clock::now() - commitStart).count();
            if (vl)
                Vec_PtrFree(vl);
            traceRoot(rootCandidates, rootWinner ? rootBest : 0, rootWinner && ok);
            if (!ok)
                break;
        }

        if (actionCuts)
            TG_VERBOSE("TG_SELECTED_ACTION round=%d cuts=%ld missing_proposals=%ld injected=%ld\n",
                       round, actionCuts, actionMissing, actionIncluded);
        TG_VERBOSE("TG_SPARSE_ROUND round=%d selected=%d evaluated=%ld stale=%ld accepted=%ld "
                   "first_selected=%ld revisited_selected=%ld created_first_selected=%ld "
                   "first_evaluated=%ld revisited_evaluated=%ld created_first_evaluated=%ld "
                   "candidates=%ld initial_nodes=%d nodes=%d selection=%.9f generation=%.9f "
                   "scoring=%.9f commit=%.9f seconds=%.9f\n",
                   round, int(roots.size()), evaluated - ev0, stale - st0, accepted - ac0,
                   firstSelected, long(roots.size()) - firstSelected, createdFirstSelected,
                   firstEvaluated, evaluated - ev0 - firstEvaluated, createdFirstEvaluated,
                   candidateCount - candidates0, roundNodes0, Abc_NtkNodeNum(n), selection - sel0,
                   construct - gen0, scoring - score0, commit - commit0,
                   std::chrono::duration<double>(Clock::now() - scanStart).count());
        cfFinish();
        ++completedRounds;
        TG_VERBOSE("TG_COMPACT_FILTER round=%d skipped_total=%ld closed=%d\n", round, cfSkipped,
                   cfClosed[0] + cfClosed[1] + cfClosed[2] + cfClosed[3] + cfClosed[4] +
                       cfClosed[5] + cfClosed[6] + cfClosed[7] + cfClosed[8] + cfClosed[9]);
        opportunityMemory.print(round);

        if (yieldThreshold && ok && completedRounds % 2 == 0 && completedRounds < rounds)
        {
            double nextHpwl = 0;
            Tg_ManReadMetrics(n, &nextHpwl, nullptr, nullptr, nullptr);
            const int nextNodes = Abc_NtkNodeNum(n);
            const long visited = selected - blockSelected;
            const double wireScale = std::max(1e-9, blockHpwl / std::max(1, blockNodes));
            const double benefit =
                (blockNodes - nextNodes) + .25 * (blockHpwl - nextHpwl) / wireScale;
            const double productivity = benefit / std::max(1L, visited);
            const bool more = std::isfinite(productivity) && visited > 0 &&
                              productivity >= yieldThreshold / 1000.;
            TG_VERBOSE(
                "TG_ROUND_YIELD completed=%d requested=%d visited=%ld nodes_saved=%d "
                "hpwl_gain=%.17g benefit=%.17g productivity=%.17g threshold=%.9f continue=%d\n",
                completedRounds, rounds, visited, blockNodes - nextNodes, blockHpwl - nextHpwl,
                benefit, productivity, yieldThreshold / 1000., int(more));
            if (!more)
                break;
            blockHpwl = nextHpwl;
            blockNodes = nextNodes;
            blockSelected = selected;
        }
        // A whole completed round with no edits leaves exactly the same
        // graph, geometry, density and deterministic selection/generation.
        // Stateful selection and warm placement cannot use this fixed point.

        {
            (void)(ok && Tg_InFlight() && round + 1 < rounds && accepted > ac0 && ((char *)0));
        }
    }
    if (ok)
    {
        ok = Tg_ManBeginEdit(n);
        if (ok)
        {
            if (!Tg_InFlight())
                Abc_NtkReassignIds(n);
            ok = Tg_ManFinishEdit(n);
        }
    }
    TG_VERBOSE("TG_REGION_REUSE enabled=%d hits=%ld inserted=%ld\n", reuseEmpty, emptyHits,
               emptyInserted);
    bool ended = Tg_ManEndPass(n);
    ok = ok && ended;
    Abc_NtkStopReverseLevels(n);
    for (auto *activeManager : cutManagers)
        Abc_NtkManCutStop(activeManager);

    TG_VERBOSE("TG_REJECT_CACHE hits=%ld avoided_candidates=%ld entries=%d\n", rejectionHits,
               rejectionSaved, int(rejectedCuts.size()));
    TG_VERBOSE("TG_FIRST_GAIN roots=%ld\n", earlyRoots);
    TG_VERBOSE("TG_CUT_LEARN skipped=%ld\n", cutLearningSkipped);

    TG_VERBOSE("TG_SHAPE_CACHE reused=%ld rebuilt=%ld\n", shapeCache.reused, shapeCache.rebuilt);

    TG_VERBOSE("TG_CARE queries=%ld hits=%ld restricted=%ld proposals=%ld factor_calls=%ld "
               "factor_hits=%ld semantic_hits=%ld\n",
               careManager.queries, careManager.hits, careManager.restricted, careManager.proposals,
               careManager.factorCalls, careManager.factorHits, careManager.semanticHits);
    if (proofPhysicalChecks)
        TG_VERBOSE("TG_PROOF_PHYSICAL evaluated=%ld viable=%ld seconds=%.9f\n", proofPhysicalChecks,
                   proofPhysicalViable, proofPhysicalSeconds);
    double hpwl = 0, overflow = 0, area = 0;
    Tg_ManReadMetrics(n, &hpwl, &overflow, nullptr, &area);

    int depth = Abc_NtkLevel(n);
    ok = ok && depth <= depth0 && Abc_NtkCheck(n);
    TG_VERBOSE(
        "TG_SPARSE_RESULT rounds=%d mode=%d growth=%d percent=%d cap=%d cut=%d selected=%ld "
        "evaluated=%ld stale=%ld candidates=%ld accepted=%ld initial_nodes=%d nodes=%d "
        "initial_depth=%d depth=%d initial_hpwl=%.9f hpwl=%.9f overflow=%.9f "
        "initial_area=%.9f area=%.9f selection=%.9f generation=%.9f scoring=%.9f commit=%.9f "
        "seconds=%.9f completed_rounds=%d initial_calls=0 resume_calls=0 rollback=0 status=%s\n",
        rounds, mode, growth, percent, cap, cutSize, selected, evaluated, stale, candidateCount,
        accepted, nodes0, Abc_NtkNodeNum(n), depth0, depth, h0, hpwl, overflow, areaInitial, area,
        selection, construct, scoring, commit,
        std::chrono::duration<double>(Clock::now() - start).count(), completedRounds,
        ok ? "ok" : "error");
    TG_VERBOSE("TG_SPARSE_LIBRARY queries=%ld hits=%ld proposals=%ld\n", library.queries,
               library.hits, library.proposals);
    TG_VERBOSE("TG_SPARSE_FACTOR calls=%ld hits=%ld\n", tgFactorCalls, tgFactorHits);

    for (const auto &k : kinds)
        TG_VERBOSE("TG_SPARSE_KIND kind=%s accepted=%ld\n", k.first.c_str(), k.second);
    TG_VERBOSE("TG_SPARSE_DIVISORS queries=%ld hits=%ld proposals=%ld products=%ld sums=%ld\n",
               divisors.queries, divisors.hits, divisors.proposals, divisors.products,
               divisors.sums);
    TG_VERBOSE("TG_SPARSE_DSD calls=%ld hits=%ld margin=%d area_guard=%d phase_guard=%d novel=%d "
               "paired=%d\n",
               dsd.calls, dsd.hits, margin, areaGuard, phaseGuard, novel, paired);
    TgEval_ManPrintEffort();
    return ok ? 0 : 1;
}

// A retained internal node reduces the actual deletion set below the marked
// MFFC. Evaluate an equivalent, deliberately redundant replacement without
// committing it: the cheap new-node screen admits b=2, but actual growth is 3.
