/**CFile****************************************************************

  FileName    [agrCompact.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [Tension scan and compact rounds (part of agrBlock.cpp).]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrCompact.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// The boxes of a root's (up to three) distinct incident nets, without the root.
struct TensionBoxes
{
    int count = 0;
    Box boxes[3];
};
/**Function*************************************************************

  Synopsis    [Returns the tension of a root.]

  Description [Tension: the L1 distance of the boxes from their median
               point, per axis.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double boxTension(const TensionBoxes & item)
{
    double result = 0;
    for ( int axis = 0; axis < 2; ++axis )
    {
        std::array<double, 6> ends{};
        for ( int k = 0; k < item.count; ++k )
        {
            auto b = axis ? item.boxes[k].y : item.boxes[k].x;
            ends[2 * k] = b.first;
            ends[2 * k + 1] = b.second;
        }
        if ( !item.count )
            continue;
        std::sort(ends.begin(), ends.begin() + 2 * item.count);
        double center = ends[item.count - 1];
        for ( int k = 0; k < item.count; ++k )
            result += dist(center, axis ? item.boxes[k].y : item.boxes[k].x);
    }
    return result;
}
// Compact AGR rounds over tension-selected roots. Candidates are scored and
// committed by the PA evaluator; accepted edits are never rolled back.
// Topology-only shape cache for the append-only object IDs of one command.
// Compare every live node's fanin literals, then invalidate only the bounded
// forward neighborhood that can observe a changed three-edge cone.
struct ShapeCache
{
    std::vector<std::pair<int, int>> inputs;
    std::vector<unsigned> values;
    std::vector<signed char> dirty;
    std::vector<std::pair<int, int>> queue;
    void refresh(Abc_Ntk_t * n)
    {
        const size_t old = inputs.size(), size = Abc_NtkObjNumMax(n);
        assert(size >= old);
        inputs.resize(size, {-1, -1});
        values.resize(size);
        dirty.assign(size, -1);
        queue.clear();
        Abc_Obj_t * v;
        int i;
        Abc_NtkForEachNode(n, v, i)
        {
            const auto now =
                std::make_pair(2 * Abc_ObjFaninId0(v) + Abc_ObjFaninC0(v), 2 * Abc_ObjFaninId1(v) + Abc_ObjFaninC1(v));
            if ( inputs[v->Id] == now )
                continue;
            inputs[v->Id] = now;
            dirty[v->Id] = 3;
            queue.emplace_back(v->Id, 3);
        }
        if ( !old )
            return; // Every live node is already dirty on the first round.
        for ( size_t at = 0; at < queue.size(); ++at )
        {
            const auto item = queue[at];
            if ( item.second <= 0 )
                continue;
            auto * node = Abc_NtkObj(n, item.first);
            Abc_Obj_t * fanout;
            int j;
            Abc_ObjForEachFanout(node, fanout, j)
            {
                if ( !Abc_ObjIsNode(fanout) || dirty[fanout->Id] >= item.second - 1 )
                    continue;
                dirty[fanout->Id] = item.second - 1;
                queue.emplace_back(fanout->Id, item.second - 1);
            }
        }
    }
};

struct TensionScan
{
    struct Net
    {
        Axis x, y;
        int count = 0;
    };
    std::vector<unsigned> shapes; // structural class of each root (depth-three cone hash)
    std::vector<XY> pos;
    std::vector<unsigned char> present;
    std::vector<Net> nets;
    std::vector<double> tension, basePriority;
    explicit TensionScan(Abc_Ntk_t * n)
    {
        int size = Abc_NtkObjNumMax(n);
        pos.resize(size);
        present.resize(size);
        nets.resize(size);
        tension.resize(size);
        Abc_Obj_t *o, *f;
        int i, j;
        Abc_NtkForEachNode(n, o, i) present[o->Id] = Pa_ManReadObjectPosition(n, o, &pos[o->Id].x, &pos[o->Id].y);
        std::vector<int> seen(size, -1);
        Abc_NtkForEachObj(n, o, i)
        {
            if ( !Abc_ObjIsNode(o) && !Abc_ObjIsCi(o) )
                continue;
            auto & net = nets[o->Id];
            auto add = [&](int id)
            {
                if ( !present[id] || seen[id] == o->Id )
                    return;
                seen[id] = o->Id;
                ++net.count;
                net.x.add(pos[id].x);
                net.y.add(pos[id].y);
            };
            add(o->Id);
            Abc_ObjForEachFanout(o, f, j) add(f->Id);
        }
        Abc_NtkForEachNode(n, o, i) tension[o->Id] = rootTension(o);
        // Freeze selection features before any edits in this round.
        basePriority = tension;
        Abc_NtkForEachNode(n, o, i) for ( int k = 0; k < 2; ++k )
        {
            auto * u = Abc_ObjFanin(o, k);
            if ( Abc_ObjIsNode(u) && Abc_ObjFanoutNum(u) == 1 )
                basePriority[o->Id] += .5 * tension[u->Id];
        }
    }
    // Incremental refresh within one command: every live or dead slot is
    // checked for changed fanins and coordinates; only the affected driver
    // boxes and root tensions are rebuilt.
    std::vector<std::array<int, 2>> previousInputs;
    std::vector<unsigned char> previousKinds;
    std::vector<unsigned> scanNetStamp, scanRootStamp, scanPinStamp;
    unsigned scanEpoch = 0, scanPinEpoch = 0;
    void captureInputs(Abc_Ntk_t * n)
    {
        const int size = Abc_NtkObjNumMax(n);
        previousInputs.assign(size, {-1, -1});
        previousKinds.assign(size, 0);
        Abc_Obj_t * v;
        int i;
        Abc_NtkForEachObj(n, v, i)
        {
            previousKinds[v->Id] = Abc_ObjIsNode(v) ? 1 : Abc_ObjIsCi(v) ? 2 : Abc_ObjIsCo(v) ? 3 : 0;
            if ( Abc_ObjIsNode(v) || Abc_ObjIsCo(v) )
                for ( int j = 0; j < Abc_ObjFaninNum(v) && j < 2; ++j )
                    previousInputs[v->Id][j] = 2 * Abc_ObjFanin(v, j)->Id + Abc_ObjFaninC(v, j);
        }
    }
    void refreshGeometry(Abc_Ntk_t * n)
    {
        const int size = Abc_NtkObjNumMax(n);
        assert(size >= int(previousInputs.size()));
        previousInputs.resize(size, {-1, -1});
        previousKinds.resize(size);
        pos.resize(size);
        present.resize(size);
        nets.resize(size);
        tension.resize(size);
        basePriority.resize(size);
        scanNetStamp.resize(size);
        scanRootStamp.resize(size);
        scanPinStamp.resize(size);
        if ( ++scanEpoch == 0 )
        {
            std::fill(scanNetStamp.begin(), scanNetStamp.end(), 0);
            std::fill(scanRootStamp.begin(), scanRootStamp.end(), 0);
            scanEpoch = 1;
        }
        std::vector<int> drivers;
        auto mark = [&](int id)
        {
            if ( id >= 0 && scanNetStamp[id] != scanEpoch )
            {
                scanNetStamp[id] = scanEpoch;
                drivers.push_back(id);
            }
        };
        for ( int id = 0; id < size; ++id )
        {
            auto * v = Abc_NtkObj(n, id);
            unsigned char kind = v ? (Abc_ObjIsNode(v) ? 1 : Abc_ObjIsCi(v) ? 2 : Abc_ObjIsCo(v) ? 3 : 0) : 0;
            std::array<int, 2> inputs{{-1, -1}};
            if ( kind == 1 || kind == 3 )
                for ( int j = 0; j < Abc_ObjFaninNum(v) && j < 2; ++j )
                    inputs[j] = 2 * Abc_ObjFanin(v, j)->Id + Abc_ObjFaninC(v, j);
            XY point;
            unsigned char has = kind == 1 ? Pa_ManReadObjectPosition(n, v, &point.x, &point.y) : 0;
            if ( kind != previousKinds[id] || inputs != previousInputs[id] || has != present[id] ||
                 point.x != pos[id].x || point.y != pos[id].y )
            {
                mark(id);
                for ( int input : previousInputs[id] )
                    if ( input >= 0 )
                        mark(input / 2);
                for ( int input : inputs )
                    if ( input >= 0 )
                        mark(input / 2);
            }
            previousInputs[id] = inputs;
            previousKinds[id] = kind;
            present[id] = has;
            pos[id] = point;
            if ( kind != 1 )
                tension[id] = 0;
        }
        std::vector<int> roots;
        auto root = [&](Abc_Obj_t * v)
        {
            if ( v && Abc_ObjIsNode(v) && scanRootStamp[v->Id] != scanEpoch )
            {
                scanRootStamp[v->Id] = scanEpoch;
                roots.push_back(v->Id);
            }
        };
        for ( int id : drivers )
        {
            nets[id] = Net{};
            auto * v = Abc_NtkObj(n, id);
            if ( !v || (!Abc_ObjIsNode(v) && !Abc_ObjIsCi(v)) )
                continue;
            if ( ++scanPinEpoch == 0 )
            {
                std::fill(scanPinStamp.begin(), scanPinStamp.end(), 0);
                scanPinEpoch = 1;
            }
            auto & net = nets[id];
            auto add = [&](int pin)
            {
                if ( !present[pin] || scanPinStamp[pin] == scanPinEpoch )
                    return;
                scanPinStamp[pin] = scanPinEpoch;
                ++net.count;
                net.x.add(pos[pin].x);
                net.y.add(pos[pin].y);
            };
            add(id);
            root(v);
            Abc_Obj_t * fo;
            int j;
            Abc_ObjForEachFanout(v, fo, j)
            {
                add(fo->Id);
                root(fo);
            }
        }
        for ( int id : roots )
            tension[id] = rootTension(Abc_NtkObj(n, id));
        basePriority = tension;
        Abc_Obj_t * v;
        int vi;
        Abc_NtkForEachNode(n, v, vi) for ( int k = 0; k < 2; ++k )
        {
            auto * u = Abc_ObjFanin(v, k);
            if ( Abc_ObjIsNode(u) && Abc_ObjFanoutNum(u) == 1 )
                basePriority[v->Id] += .5 * tension[u->Id];
        }
        shapes.clear();
    }
    // Structural class of each root: a hash of its fanin cone to depth three,
    // reused from the cache where no fanin within that depth changed.
    void prepareOpportunities(Abc_Ntk_t * n, ShapeCache * cache)
    {
        cache->refresh(n);
        shapes.resize(Abc_NtkObjNumMax(n));
        Abc_Obj_t * root;
        int ri;
        Abc_NtkForEachNode(n, root, ri)
        {
            if ( cache->dirty[root->Id] < 0 )
            {
                shapes[root->Id] = cache->values[root->Id];
                continue;
            }
            unsigned shape = 2166136261u;
            Abc_Obj_t * queue[15];
            int depth[15], seen[15], count = 0;
            queue[0] = root;
            depth[0] = 0;
            int end = 1;
            for ( int at = 0; at < end; ++at )
            {
                auto * v = queue[at];
                int previous = -1;
                for ( int j = 0; j < count; ++j )
                    if ( seen[j] == v->Id )
                    {
                        previous = j;
                        break;
                    }
                const unsigned code = previous >= 0 ? 32u + unsigned(previous)
                                      : Abc_ObjIsNode(v) && depth[at] < 3
                                          ? 1u + 2u * Abc_ObjFaninC0(v) + 4u * Abc_ObjFaninC1(v)
                                          : 0u;
                shape = (shape ^ code) * 16777619u;
                if ( previous >= 0 )
                    continue;
                seen[count++] = v->Id;
                if ( !Abc_ObjIsNode(v) || depth[at] >= 3 )
                    continue;
                for ( int k = 0; k < 2; ++k )
                {
                    queue[end] = Abc_ObjFanin(v, k);
                    depth[end++] = depth[at] + 1;
                }
            }
            shapes[root->Id] = shape;
            cache->values[root->Id] = shape;
        }
    }
    double rootTension(Abc_Obj_t * v) const
    {
        TensionBoxes item;
        int ds[3] = {v->Id, Abc_ObjFaninId0(v), Abc_ObjFaninId1(v)};
        for ( int k = 0; k < 3; ++k )
        {
            bool duplicate = false;
            for ( int l = 0; l < k; ++l )
                duplicate |= ds[k] == ds[l];
            const auto & net = nets[ds[k]];
            if ( duplicate || net.count < 2 )
                continue;
            item.boxes[item.count++] = {net.x.without(pos[v->Id].x), net.y.without(pos[v->Id].y)};
        }
        return boxTension(item);
    }

    double rootPriority(Abc_Ntk_t *, int id) const
    {
        return id >= 0 && id < int(basePriority.size()) ? basePriority[id] : 0;
    }

    // Roots of one pass: live nodes with 1..1000 fanouts. Every structural class
    // gets tickets rank / (sqrt(class size) * class weight), so each class gets
    // its first root before a second; within a class, novelty then geometric
    // priority decide. Classes are scheduling heuristics, never proofs.
    std::vector<int> roots(Abc_Ntk_t * n, int percent, int maximum, const std::vector<double> & novelty,
                           const std::unordered_map<unsigned, double> * classWeight) const
    {
        std::vector<int> out;
        Abc_Obj_t * o;
        int i;
        Abc_NtkForEachNode(n, o, i) if ( Abc_ObjFanoutNum(o) > 0 && Abc_ObjFanoutNum(o) <= 1000 &&
                                         !Abc_NodeIsPersistant(o) ) out.push_back(o->Id);
        size_t keep = (out.size() * size_t(percent) + 99) / 100;
        if ( maximum )
            keep = std::min(keep, size_t(maximum));
        auto better = [&](int a, int b)
        {
            if ( novelty[a] != novelty[b] )
                return novelty[a] > novelty[b];
            const double x = basePriority[a], y = basePriority[b];
            return x != y ? x > y : a < b;
        };
        auto classUtility = [&](unsigned shape)
        {
            if ( !classWeight )
                return 1.0;
            auto at = classWeight->find(shape);
            return at == classWeight->end() ? 1.0 : at->second;
        };
        std::vector<double> ticket(pos.size(), INFINITY);
        // Dense keys: the class hash in the upper 32 bits, the root ID below.
        std::vector<uint64_t> keys;
        keys.reserve(out.size());
        for ( int id : out )
            keys.push_back((uint64_t(shapes[id]) << 32) | unsigned(id));
        if ( keys.size() < 4096 )
            std::sort(keys.begin(), keys.end());
        else
        {
            std::vector<uint64_t> scratch(keys.size());
            for ( int shift = 32; shift < 64; shift += 8 )
            {
                size_t offsets[256] = {};
                for ( auto key : keys )
                    ++offsets[(key >> shift) & 255u];
                size_t sum = 0;
                for ( auto & offset : offsets )
                {
                    size_t count = offset;
                    offset = sum;
                    sum += count;
                }
                for ( auto key : keys )
                    scratch[offsets[(key >> shift) & 255u]++] = key;
                keys.swap(scratch);
            }
        }
        auto idOf = [](uint64_t key) { return int(key & 0xffffffffu); };
        auto compare = [&](uint64_t a, uint64_t b) { return better(idOf(a), idOf(b)); };
        for ( size_t begin = 0; begin < keys.size(); )
        {
            size_t end = begin + 1;
            while ( end < keys.size() && (keys[end] >> 32) == (keys[begin] >> 32) )
                ++end;
            const size_t count = end - begin, prefix = std::min(keep, count);
            if ( prefix < count )
                std::nth_element(keys.begin() + begin, keys.begin() + begin + prefix, keys.begin() + end, compare);
            std::sort(keys.begin() + begin, keys.begin() + begin + prefix, compare);
            double denominator = std::sqrt(double(count));
            denominator *= classUtility(unsigned(keys[begin] >> 32));
            for ( size_t rank = 0; rank < prefix; ++rank )
                ticket[idOf(keys[begin + rank])] = (double(rank) + (classWeight ? 1 : 0)) / denominator;
            begin = end;
        }
        auto byTicket = [&](int a, int b) { return ticket[a] != ticket[b] ? ticket[a] < ticket[b] : better(a, b); };
        if ( keep < out.size() )
            std::nth_element(out.begin(), out.begin() + keep, out.end(), byTicket);
        std::sort(out.begin(), out.begin() + keep, byTicket);
        out.resize(keep);
        return out;
    }
};
#include "agrHistory.h"

// All selected operators see the same live graph/placement in a Co epoch.
// Work allocation over root groups: a group closes once its Laplace-smoothed
// success rate falls below rho times the overall rate.
struct GroupFilter
{
    std::vector<int> n, k;
    std::vector<unsigned char> closed;
    int allN = 0, allK = 0;
    double rho;
    GroupFilter(int groups, double Rho) : n(groups), k(groups), closed(groups), rho(Rho)
    {
    }
    void record(int g, bool success)
    {
        ++n[g];
        ++allN;
        if ( success )
        {
            ++k[g];
            ++allK;
        }
        if ( (k[g] + 1.) / (n[g] + 2.) < rho * (allK + 1.) / (allN + 2.) )
            closed[g] = 1;
    }
};
/**Function*************************************************************

  Synopsis    [Returns the priority group of every root.]

  Description [Group of every root: its rank by priority, in `groups` equal
               parts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static std::vector<unsigned char> rankGroups(Abc_Ntk_t * n, const TensionScan & scan, const std::vector<int> & roots,
                                             int groups)
{
    std::vector<std::pair<double, int>> ranked;
    for ( int id : roots )
        ranked.push_back({scan.rootPriority(n, id), id});
    std::sort(ranked.begin(), ranked.end(), [](const std::pair<double, int> & x, const std::pair<double, int> & y)
              { return x.first != y.first ? x.first > y.first : x.second < y.second; });
    std::vector<unsigned char> group(Abc_NtkObjNumMax(n), 255);
    for ( size_t r = 0; r < ranked.size(); ++r )
        group[ranked[r].second] = (unsigned char)(r * groups / std::max<size_t>(1, ranked.size()));
    return group;
}

// History slots of the broad passes.
enum
{
    AGR_RW,
    AGR_RF,
    AGR_RS
};

// State of one agr command, shared by its broad and compact passes: the
// tension scan, refreshed between passes, and the root histories.
struct BlockState
{
    ShapeCache shapes;
    std::unique_ptr<TensionScan> scan;
    RootHistory broadHistory[3]; // indexed by AGR_RW, AGR_RF, AGR_RS
    RootHistory compactHistory;
};
static BlockState & blockState(); // per-frame, see AgrState

/**Function*************************************************************

  Synopsis    [Grows a cut of at most K leaves around the root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Region greedyCut(Abc_Ntk_t * n, int root, const TensionScan & scan, int K, int bound)
{
    Region r;
    r.root = r.seed = root;
    r.closed = false;
    r.inside.insert(root);
    auto * v = Abc_NtkObj(n, root);
    r.leaves.insert(Abc_ObjFaninId0(v));
    r.leaves.insert(Abc_ObjFaninId1(v));
    while ( int(r.inside.size()) < bound )
    {
        int best = -1;
        double bestScore = -1;
        for ( int id : r.leaves )
        {
            auto * u = Abc_NtkObj(n, id);
            if ( !Abc_ObjIsNode(u) || Abc_NodeIsPersistant(u) )
                continue;
            int extra = 0;
            for ( int k = 0; k < 2; ++k )
            {
                int f = Abc_ObjFanin(u, k)->Id;
                extra += !r.leaves.count(f) && !r.inside.count(f);
            }
            if ( int(r.leaves.size()) - 1 + extra > K )
                continue;
            int outside = 0;
            Abc_Obj_t * f;
            int j;
            Abc_ObjForEachFanout(u, f, j) outside += !r.inside.count(f->Id);
            double t = id < int(scan.tension.size()) ? scan.tension[id] : 0;
            double score = (1 + t) * (3 - extra) / (1.0 + outside + extra * extra);
            if ( score > bestScore )
            {
                bestScore = score;
                best = id;
            }
        }
        if ( best < 0 )
            break;
        r.leaves.erase(best);
        r.inside.insert(best);
        auto * u = Abc_NtkObj(n, best);
        for ( int k = 0; k < 2; ++k )
        {
            int f = Abc_ObjFanin(u, k)->Id;
            if ( !r.inside.count(f) )
                r.leaves.insert(f);
        }
    }
    return r;
}

// Command-scoped stamped scratch avoids a per-cut tree map. Object IDs are
// rebound after every edit; no topology, truth or coordinate cache survives.
struct ExpressionReader
{
    std::vector<int> literals;
    std::vector<unsigned> stamp;
    unsigned epoch = 0;
    Expr read(Abc_Ntk_t * n, const Region & r, const std::vector<Abc_Obj_t *> & leaves,
              const std::vector<Abc_Obj_t *> * roots = nullptr, std::vector<int> * outputs = nullptr)
    {
        size_t size = Abc_NtkObjNumMax(n);
        literals.resize(size);
        stamp.resize(size);
        if ( ++epoch == 0 )
        {
            std::fill(stamp.begin(), stamp.end(), 0);
            epoch = 1;
        }
        Expr e(leaves.size());
        for ( size_t i = 0; i < leaves.size(); ++i )
        {
            stamp[leaves[i]->Id] = epoch;
            literals[leaves[i]->Id] = 2 * i;
        }
        auto visit = [&](auto && self, Abc_Obj_t * o) -> int
        {
            if ( stamp[o->Id] == epoch )
                return literals[o->Id];
            int value = -2;
            if ( !Abc_AigNodeIsConst(o) )
            {
                int a = self(self, Abc_ObjFanin0(o)) ^ Abc_ObjFaninC0(o);
                int b = self(self, Abc_ObjFanin1(o)) ^ Abc_ObjFaninC1(o);
                value = e.land(a, b);
            }
            stamp[o->Id] = epoch;
            return literals[o->Id] = value;
        };
        if ( roots )
        {
            outputs->clear();
            outputs->reserve(roots->size());
            for ( auto * v : *roots )
                outputs->push_back(visit(visit, v));
            if ( !outputs->empty() )
                e.root = outputs->back();
        }
        else
            e.root = visit(visit, Abc_NtkObj(n, r.root));
        return e;
    }
};
/**Function*************************************************************

  Synopsis    [Returns the factored and regrouped candidates of a cut.]

  Description [Compact proposals for one cut: the ordinary factored form,
               the cut's own structure regrouped by geometry, and the
               factored form regrouped by geometry (at most `cap`). Repeats
               and the original structure are dropped.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
std::vector<Candidate> factoredCandidates(const Expr & id, const Truth & truth, const std::vector<XY> & xy, int cap,
                                          const std::string * originalKey = nullptr)
{
    std::vector<Candidate> out;
    const std::string original = originalKey ? *originalKey : id.key(true);
    auto add = [&](Expr e, const std::string * knownKey = nullptr, bool factorVerified = false)
    {
        auto same = [&](const Expr & other) { return e.k == other.k && e.root == other.root && e.a == other.a; };
        if ( same(id) || std::any_of(out.begin(), out.end(), [&](const Candidate & c) { return same(c.e); }) )
            return;
        auto key = knownKey ? *knownKey : e.key(true);
        if ( key == original ||
             std::any_of(out.begin(), out.end(), [&](const Candidate & c) { return c.key() == key; }) )
            return;
        // A factored form reproduces the truth it was factored from.
        assert(factorVerified || e.truth() == truth);
        out.emplace_back(std::move(e), std::move(key), truth);
    };
    std::vector<int> order(id.k);
    std::iota(order.begin(), order.end(), 0);
    Expr ordinary(id.k);
    std::string ordinaryKey;
    if ( !factor(ordinary, truth, order, &ordinaryKey) )
        return out;
    add(ordinary, &ordinaryKey, true);
    if ( cap > 1 )
        add(spatial(id, xy));
    if ( cap > 2 )
        add(spatial(ordinary, xy));
    return out;
}

// Library-assisted Boolean candidates are imported from ABC's fixed 4-input
// forest. AGR still chooses the regions; no native RW traversal is invoked.
#include "agrLibraryData.h"

struct StructureLibrary
{
    Rwr_Man_t * man = nullptr;
    struct Metadata
    {
        std::vector<std::string> keys;
        size_t minimum = 1000; // fewest ANDs of a structure of this class
    };
    struct Data
    {
        std::map<unsigned, std::vector<Expr>> cache;
        std::map<unsigned, Metadata> metadata;
    };
    static Data & SharedData(); // per-frame, see AgrState
    std::map<unsigned, std::vector<Expr>> & cache;
    std::map<unsigned, Metadata> & metadata;
    StructureLibrary() : cache(SharedData().cache), metadata(SharedData().metadata)
    {
    }
    StructureLibrary(const StructureLibrary &) = delete;
    StructureLibrary & operator=(const StructureLibrary &) = delete;
    void BoundCache()
    {
        if ( cache.size() >= 1024 )
        {
            cache.clear();
            metadata.clear();
        }
    }
    ~StructureLibrary()
    {
        if ( man )
            Rwr_ManStop(man);
    }

    const std::vector<Expr> & lookup(unsigned truth)
    {
        auto hit = cache.find(truth);
        if ( hit != cache.end() )
            return hit->second;
        auto * dec = (Dec_Man_t *)Abc_FrameReadManDec();
        int cl = dec->pMap[truth];
        const int * perm = libraryPerms + 4 * (unsigned char)dec->pPerms[truth];
        unsigned phase = (unsigned char)dec->pPhases[truth];
        BoundCache();
        metadata.erase(truth); // A rebuilt library entry invalidates its derived keys.
        auto & out = cache[truth];
        std::set<std::string> seen;
        for ( int index = libraryClasses[cl]; index < libraryClasses[cl + 1]; ++index )
        {
            const int * g = libraryData + libraryOffsets[index];
            Expr e(4);
            if ( g[0] )
                e.root = ((g[1] & 1) ? -1 : -2) ^ ((phase >> 4) & 1);
            else
            {
                std::vector<int> literals(4 + g[2]);
                for ( int k = 0; k < 4; ++k )
                    literals[k] = 2 * perm[k] ^ ((phase >> k) & 1);
                for ( int k = 0; k < g[2]; ++k )
                {
                    int x = g[3 + 2 * k], y = g[4 + 2 * k];
                    literals[4 + k] = e.land(literals[x / 2] ^ (x & 1), literals[y / 2] ^ (y & 1));
                }
                e.root = literals[g[1] / 2] ^ (g[1] & 1) ^ ((phase >> 4) & 1);
            }
            assert((e.truth()[0] & 65535) == truth);
            if ( seen.insert(e.key()).second )
                out.push_back(std::move(e));
        }
        return out;
    }
    // Up to `cap` library structures of the cut's 4-input class within one AND
    // of the smallest, ranked by internal wire plus 0.25 per AND; structures
    // deeper than `required` are skipped.
    std::vector<Candidate> generate(const Expr & id, const Truth & truth, const std::vector<XY> & xy,
                                    const std::vector<int> & levels, int cap, int required,
                                    const std::string * originalKey = nullptr)
    {
        if ( id.k != 4 || truth[0] == 0 || truth[0] == ~0u )
            return ordinaryCandidate(id, truth);
        const auto & all = lookup(truth[0] & 65535);

        std::vector<std::pair<double, int>> ranks;
        auto & meta = metadata[truth[0] & 65535];
        if ( meta.keys.size() != all.size() )
        {
            meta = Metadata{};
            for ( const auto & e : all )
            {
                meta.keys.push_back(e.key(true));
                meta.minimum = std::min(meta.minimum, e.a.size());
            }
        }
        std::string original = originalKey ? *originalKey : id.key(true);
        double scale = 0;
        for ( int i = 0; i < 4; ++i )
            for ( int j = 0; j < i; ++j )
                scale += std::abs(xy[i].x - xy[j].x) + std::abs(xy[i].y - xy[j].y);
        scale = std::max(1e-12, scale / 6);
        for ( int index = 0; index < int(all.size()); ++index )
        {
            const auto & e = all[index];
            if ( e.a.size() > meta.minimum + 1 || meta.keys[index] == original )
                continue;
            PaWorkspace::Scratch<XY, 64> pos(4 + e.a.size());
            PaWorkspace::Scratch<int, 64> depth(4 + e.a.size());
            for ( int i = 0; i < 4; ++i )
            {
                pos[i] = xy[i];
                depth[i] = levels[i];
            }
            size_t next = 4;
            double wire = 0;
            for ( auto pair : e.a )
            {
                int x = pair.first / 2, y = pair.second / 2;
                wire += std::abs(pos[x].x - pos[y].x) + std::abs(pos[x].y - pos[y].y);
                pos[next] = {(pos[x].x + pos[y].x) / 2, (pos[x].y + pos[y].y) / 2};
                depth[next++] = 1 + std::max(depth[x], depth[y]);
            }
            if ( e.root >= 0 && depth[e.root / 2] > required )
                continue;
            ranks.emplace_back(wire / scale + ((.25 * e.a.size())), index);
        }
        std::sort(ranks.begin(), ranks.end());
        if ( ranks.size() > size_t(cap) )
            ranks.resize(cap);
        std::vector<Candidate> out;
        for ( auto rank : ranks )
            out.emplace_back(all[rank.second], meta.keys[rank.second], truth);
        return out;
    }
};

// Enumerate a small family of exact, live four-leaf boundaries. Each step
// replaces a frontier node by its actual fanins, so every retained boundary
// still covers the root. A bounded breadth-first search avoids deep whole-cone
// traversal and does not use cached cuts after edits.

/**Function*************************************************************

  Synopsis    [Enumerates exact live four-input cuts of the root.]

  Description [Enumerate a small family of exact, live four-leaf
               boundaries. Each step replaces a frontier node by its actual
               fanins, so every retained boundary still covers the root. A
               bounded breadth-first search avoids deep whole-cone
               traversal and does not use cached cuts after edits.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
std::vector<std::vector<Abc_Obj_t *>> fourInputCuts(Abc_Obj_t * root)
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
        if ( f.size > 4 )
            return;
        for ( const auto & v : queue )
            if ( v.size == f.size && std::equal(f.ids.begin(), f.ids.begin() + f.size, v.ids.begin()) )
                return;
        queue.push_back(f);
    };
    Frontier first;
    first.size = 2;
    first.ids[0] = Abc_ObjFaninId0(root);
    first.ids[1] = Abc_ObjFaninId1(root);
    insert(first);
    for ( size_t at = 0; at < queue.size() && at < 48 && result.size() < size_t(16); ++at )
    {
        const auto current = queue[at];
        if ( current.size >= 3 )
        {
            std::vector<Abc_Obj_t *> leaves;
            leaves.reserve(current.size);
            for ( int i = 0; i < current.size; ++i )
                leaves.push_back(Abc_NtkObj(root->pNtk, current.ids[i]));
            result.push_back(std::move(leaves));
        }
        if ( current.depth >= 6 )
            continue;
        for ( int i = 0; i < current.size; ++i )
        {
            auto * v = Abc_NtkObj(root->pNtk, current.ids[i]);
            if ( !Abc_ObjIsNode(v) || Abc_AigNodeIsConst(v) )
                continue;
            Frontier next;
            next.depth = current.depth + 1;
            for ( int j = 0; j < current.size; ++j )
                if ( i != j )
                    next.ids[next.size++] = current.ids[j];
            next.ids[next.size++] = Abc_ObjFaninId0(v);
            next.ids[next.size++] = Abc_ObjFaninId1(v);
            insert(next);
        }
    }

    return result;
}
#include "agrCare.h"

#include "agrGeometryCut.h"

/**Function*************************************************************

  Synopsis    [Runs the compact rounds of one AGR block.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int compactRounds(Abc_Frame_t * frame, int maximum)
{
    // Fixed compact policy: up to four rounds over 25% of the live roots (at
    // most `maximum`), cuts of up to 10 leaves, three proposals per generator.
    const int rounds = 4, percent = 25, cutSize = 10, cap = 3;
    auto * n = Abc_FrameReadNtk(frame);
    if ( !n || !Abc_NtkIsStrash(n) || Abc_NtkLatchNum(n) || Abc_NtkGetChoiceNum(n) || n->pExdc || n->pExcare ||
         n->pManTime || !Pa_ManHasPlacement(n) )
        return 1;
    double h0 = 0;
    Pa_ManReadMetrics(n, &h0, nullptr, nullptr, nullptr);
    int nodes0 = Abc_NtkNodeNum(n), depth0 = Abc_NtkLevel(n);
    Pa_ManSetPhysicalAreaGuard(1);
    // Timing-aware scores with bounded RW/RF timing maintenance; every
    // accepted edit refreshes the affected dependencies.
    struct TimingScope
    {
        ~TimingScope()
        {
            Pa_ManSetTimingEvaluation(0);
        }
    } timingScope;
    Pa_ManSetTimingEvaluation(1);
    KitSession session;
    StructureLibrary library;
    ExpressionReader reader;
    CareSet careManager;
    Abc_NtkStartReverseLevels(n, 0);
    bool ok = Pa_ManBeginPass(n) && Pa_ManPrepareTimingPass(n);
    auto * manager = Abc_NtkManCutStart(cutSize, 16, 2, 1000);
    // Rebuild every alternative boundary from the live graph at this root.
    // Selection is still performed once per round; no cut survives a commit.
    std::vector<decltype(manager)> cutManagers{manager};
    for ( int size : {4, 6, 8, 10} )
        if ( size < cutSize )
            cutManagers.push_back(Abc_NtkManCutStart(size, 16, 2, 1000));

    // Command-scoped empirical cut-family scheduling, never an equivalence cache.
    struct CutLearning
    {
        long attempts = 0, wins = 0;
    };
    std::array<CutLearning, 26> cutLearning{};
    long accepted = 0, evaluated = 0, selected = 0;
    // A rejection is reused only while NO edit has occurred anywhere in this
    // invocation, so graph, positions, density, levels and score references
    // are unchanged.
    std::unordered_set<std::string> rejectedCuts;
    long rejectionVersion = -1;
    auto & opportunityMemory = blockState().compactHistory;
    auto & shapeCache = blockState().shapes;
    auto & scanCache = blockState().scan;
    // End a compact block when two complete rounds yield less than 0.02 node
    // equivalents (nodes + 0.25 HPWL in node units) per visited root.
    // Unexplored roots may still improve; this is a work policy.
    const double minimumYield = 20 / 1000.;
    double blockHpwl = h0;
    int blockNodes = Abc_NtkNodeNum(n);
    long blockSelected = 0;
    int completedRounds = 0;
    // Compact-round root filter. Each round's roots are split into
    // tension-priority tenths; statistics pool over the block's rounds; a tenth
    // is skipped once its smoothed acceptance < 0.5 * overall smoothed acceptance.
    GroupFilter groupFilter(10, 0.5);
    for ( int round = 0; round < rounds && ok; ++round )
    {
        if ( !scanCache )
        {
            scanCache.reset(new TensionScan(n));
            scanCache->captureInputs(n);
        }
        else
            scanCache->refreshGeometry(n);
        auto & scan = *scanCache;
        // Selection only: structural/care validity comes from fresh candidate checks.
        scan.prepareOpportunities(n, &shapeCache);
        opportunityMemory.prepare(n, scan);

        // Allocate more slots to classes that produced useful local gain.
        // Hashes define heuristic classes only; candidates are always rebuilt
        // and checked against the live Boolean/physical context.
        std::unordered_map<unsigned, double> classWeights;
        for ( const auto & item : opportunityMemory.classes )
            classWeights[item.first] = std::max(.05, (1 + item.second.gain) / (4 + item.second.attempts));
        auto roots =
            scan.roots(n, percent, maximum, opportunityMemory.novelty, classWeights.empty() ? nullptr : &classWeights);

        opportunityMemory.prepareSelected(n, scan, roots);
        {
            std::vector<uint64_t> keys;
            keys.reserve(roots.size());
            for ( int id : roots )
                keys.push_back((uint64_t(Abc_NtkObj(n, id)->Level) << 32) | unsigned(id));
            std::sort(keys.begin(), keys.end());
            for ( size_t i = 0; i < keys.size(); ++i )
                roots[i] = int(keys[i] & 0xffffffffu);
        }

        selected += roots.size();
        // A root's group records its success when the next root starts.
        const std::vector<unsigned char> group = rankGroups(n, scan, roots, 10);
        int pendingGroup = -1;
        long pendingAccepted = 0;
        auto finishRoot = [&]()
        {
            if ( pendingGroup >= 0 )
                groupFilter.record(pendingGroup, accepted > pendingAccepted);
            pendingGroup = -1;
        };
        for ( int rootId : roots )
        {
            finishRoot();
            if ( groupFilter.closed[group[rootId]] )
                continue;
            pendingGroup = group[rootId];
            pendingAccepted = accepted;
            auto * root = Abc_NtkObj(n, rootId);
            if ( !root || !Abc_ObjIsNode(root) || !Abc_ObjFanoutNum(root) )
                continue;
            ++evaluated;
            bool memoryAccepted = false;
            struct Observation
            {
                RootHistory * m;
                int id;
                bool & a;
                ~Observation()
                {
                    m->observe(id, a);
                }
            } observation{&opportunityMemory, rootId, memoryAccepted};

            bool rootWinner = false;
            double rootBest = 1e-10;
            int rootGain = 0;
            Expr rootExpression(0);
            std::vector<Abc_Obj_t *> rootLeaves;
            std::array<std::array<int, 13>, 32> seenCutStorage;
            size_t seenCutCount = 0;
            auto extraCuts = fourInputCuts(root);
            for ( int size : {6, 10} )
            {
                if ( size > cutSize )
                    continue;
                auto region = greedyCut(n, rootId, scan, size, 32);
                std::vector<Abc_Obj_t *> boundary;
                for ( int id : region.leaves )
                    boundary.push_back(Abc_NtkObj(n, id));
                extraCuts.push_back(std::move(boundary));
            }
            // A wide geometric cut.
            std::vector<Abc_Obj_t *> wideLeaves;
            {
                auto wide = geometryCut(n, root);
                if ( wide.leaves.size() > 4 )
                    for ( int id : wide.leaves )
                        wideLeaves.push_back(Abc_NtkObj(n, id));
            }
            const bool hasWide = !wideLeaves.empty();
            for ( size_t cutAt = 0; cutAt < cutManagers.size() + extraCuts.size() + size_t(hasWide); ++cutAt )
            {
                const bool wideCut = hasWide && cutAt == 0;
                const int regularAt = int(cutAt) - int(hasWide);
                auto * activeManager =
                    !wideCut && regularAt < int(cutManagers.size()) ? cutManagers[regularAt] : nullptr;

                Region r;
                PaWorkspace::WorkspaceVector<Abc_Obj_t *> leaves;
                Expr id(0);
                {
                    if ( wideCut )
                    {
                        leaves = wideLeaves;
                        r.root = rootId;
                    }
                    else
                    {
                        if ( activeManager )
                        {
                            auto * cut = Abc_NodeFindCut(activeManager, root, 0);
                            Abc_Obj_t * v;
                            int j;
                            Vec_PtrForEachEntry(Abc_Obj_t *, cut, v, j) leaves.push_back(v);
                        }
                        else
                            leaves = extraCuts[regularAt - cutManagers.size()];
                        r.root = rootId;
                    }

                    if ( leaves.size() < 2 || leaves.size() > size_t(cutSize) )
                        continue;
                    {
                        bool fresh = true;
                        {
                            std::array<int, 13> ids{};
                            ids[0] = int(leaves.size());
                            for ( size_t i = 0; i < leaves.size(); ++i )
                                ids[i + 1] = leaves[i]->Id;
                            std::sort(ids.begin() + 1, ids.begin() + 1 + leaves.size());
                            for ( size_t i = 0; i < seenCutCount; ++i )
                                if ( ids == seenCutStorage[i] )
                                {
                                    fresh = false;
                                    break;
                                }
                            if ( fresh )
                            {
                                assert(seenCutCount < seenCutStorage.size());
                                seenCutStorage[seenCutCount++] = ids;
                            }
                        }
                        if ( !fresh )
                            continue;
                    }
                    id = reader.read(n, r, leaves);
                }
                if ( id.a.size() < 2 )
                    continue;

                const int cutClass = (activeManager ? 0 : 13) + id.k;
                auto & cutEvidence = cutLearning[cutClass];
                // After 32 observations, retain periodic exploration for families
                // that have rarely supplied an improving incumbent. This changes
                // search coverage, not score/proof validity, and never rolls back.
                if ( cutEvidence.attempts >= 32 )
                {
                    const bool poor = cutEvidence.wins == 0 || cutEvidence.wins * 100 < cutEvidence.attempts;
                    if ( poor && (evaluated + cutAt + round) % 16 )
                        continue;
                }
                ++cutEvidence.attempts;
                std::string rejectionKey;
                if ( !rootWinner )
                {
                    if ( rejectionVersion != accepted )
                    {
                        rejectedCuts.clear();
                        rejectionVersion = accepted;
                    }
                    auto append = [&](int value)
                    { rejectionKey.append(reinterpret_cast<const char *>(&value), sizeof(value)); };
                    append(rootId);
                    append(int(cutAt));
                    for ( auto * v : leaves )
                        append(v->Id);
                    if ( rejectedCuts.count(rejectionKey) )
                        continue;
                }
                auto truth = id.truth();
                const auto originalKey = id.key(true);
                PaWorkspace::WorkspaceVector<XY> xy;
                PaWorkspace::WorkspaceVector<int> levels;
                for ( auto * v : leaves )
                {
                    XY p = scan.pos[rootId];
                    Pa_ManReadObjectPosition(n, v, &p.x, &p.y);
                    xy.push_back(p);
                    levels.push_back(v->Level);
                }
                const Truth care = careManager.reachable(n, leaves, 6);
                std::vector<Candidate> candidates = factoredCandidates(id, truth, xy, cap, &originalKey);
                if ( id.k == 4 )
                {
                    auto extra = library.generate(id, truth, xy, levels, std::max(4, cap), Abc_ObjRequiredLevel(root),
                                                  &originalKey);
                    for ( auto & c : extra )
                        if ( std::none_of(candidates.begin(), candidates.end(),
                                          [&](const Candidate & v) { return v.key() == c.key(); }) )
                            candidates.push_back(std::move(c));
                }
                careManager.append(candidates, id, truth, care, xy, &originalKey);

                int winner = -1, winGain = 0;
                double best = rootBest;
                // Evaluation does not mutate traversal IDs or topology. Mark once
                // for this fixed root/cut; commit performs its own fresh marking.
                int saved = 0;
                if ( !candidates.empty() )
                {
                    for ( auto * v : leaves )
                        ++v->vFanouts.nSize;
                    Abc_NtkIncrementTravId(n);
                    saved = Abc_NodeMffcLabelAig(root);
                    for ( auto * v : leaves )
                        --v->vFanouts.nSize;
                }

                for ( int j = 0; j < int(candidates.size()); ++j )
                {
                    auto & c = candidates[j];

                    if ( !CareSet::equivalent(c.truth(), truth, care) )
                    {
                        ok = false;
                        break;
                    }
                    // A complemented replacement root of a shared node changes the
                    // stored phase of all its fanout cuts; it must save a node.
                    const bool phaseRestricted = c.e.root >= 0 && (c.e.root & 1) && Abc_ObjFanoutNum(root) > 1;

                    auto * g = c.e.graph(leaves);
                    int gain = 0;
                    double score = 0, oldHpwl = 0, newHpwl = 0;
                    bool valid = Pa_ManEvaluateCandidate(root, g, saved, Abc_ObjRequiredLevel(root), 0, &gain, &score,
                                                         &oldHpwl, &newHpwl, nullptr);
                    Dec_GraphFree(g);

                    if ( phaseRestricted && gain <= 0 )
                        valid = false;

                    // The incumbent may come from an earlier cut. Apply the
                    // same numerical tie rule across cuts as within a cut; a
                    // reset per-cut winner must not promote roundoff-only gains.
                    if ( valid && score > best &&
                         ((!rootWinner && winner < 0) ||
                          score - best > 1e-10 * std::max(1.0, std::max(std::abs(score), std::abs(best)))) )
                    {
                        best = score;
                        winner = j;
                        winGain = gain;
                    }
                }

                if ( winner >= 0 && ok )
                {
                    ++cutEvidence.wins;
                    rootWinner = true;
                    rootBest = best;
                    rootGain = winGain;
                    rootExpression = std::move(candidates[winner].e);
                    rootLeaves = leaves;
                }

                if ( ok && !rootWinner && !rejectionKey.empty() )
                {
                    if ( rejectedCuts.size() >= 32768 )
                        rejectedCuts.clear();
                    rejectedCuts.insert(std::move(rejectionKey));
                }
                if ( !ok )
                    break;
                // First gain: stop at the first cut whose winner saves a node.
                if ( rootWinner && rootGain >= 1 )
                    break;
            } // choose one replacement from the processed live cuts
            Vec_Ptr_t * vl = nullptr;
            if ( rootWinner && ok )
            {

                vl = Vec_PtrAlloc(rootLeaves.size());
                for ( auto * v : rootLeaves )
                    Vec_PtrPush(vl, v);
                auto * g = rootExpression.graph(rootLeaves);
                ok = Pa_ManCommitCandidate(root, g, vl, 1, rootGain);
                Dec_GraphFree(g);
                if ( ok )
                {
                    ++accepted;
                    memoryAccepted = true;

                    opportunityMemory.classes[opportunityMemory.shapes[rootId]].gain +=
                        rootBest / std::max(1e-9, h0 / std::max(1, nodes0));
                }
            }
            if ( vl )
                Vec_PtrFree(vl);
            if ( !ok )
                break;
        }

        finishRoot();
        ++completedRounds;

        if ( ok && completedRounds % 2 == 0 && completedRounds < rounds )
        {
            double nextHpwl = 0;
            Pa_ManReadMetrics(n, &nextHpwl, nullptr, nullptr, nullptr);
            const int nextNodes = Abc_NtkNodeNum(n);
            const long visited = selected - blockSelected;
            const double wireScale = std::max(1e-9, blockHpwl / std::max(1, blockNodes));
            const double benefit = (blockNodes - nextNodes) + .25 * (blockHpwl - nextHpwl) / wireScale;
            const double productivity = benefit / std::max(1L, visited);
            if ( !(std::isfinite(productivity) && visited > 0 && productivity >= minimumYield) )
                break;
            blockHpwl = nextHpwl;
            blockNodes = nextNodes;
            blockSelected = selected;
        }
    }
    if ( ok )
    {
        ok = Pa_ManBeginEdit(n) && Pa_ManFinishEdit(n);
    }
    bool ended = Pa_ManEndPass(n);
    ok = ok && ended;
    Abc_NtkStopReverseLevels(n);
    for ( auto * activeManager : cutManagers )
        Abc_NtkManCutStop(activeManager);
    double hpwl = 0;
    Pa_ManReadMetrics(n, &hpwl, nullptr, nullptr, nullptr);
    ok = ok && Abc_NtkLevel(n) <= depth0 && Abc_NtkCheck(n);
    AGR_VERBOSE("agr: compact rounds = %d  accepted = %ld  nodes %d -> %d  hpwl %.3f -> %.3f\n", completedRounds,
                accepted, nodes0, Abc_NtkNodeNum(n), h0, hpwl);
    return ok ? 0 : 1;
}
