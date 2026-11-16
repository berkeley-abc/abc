#include "agrLog.h"
#include "aig/aig/aig.h"
#include "opt/dar/dar.h"

#include "agrEvaluate.h"

#include "base/main/mainInt.h"
#include "aig/gia/gia.h"
#include "misc/util/utilNam.h"
#include "map/scl/sclCon.h"
#include "map/mio/mio.h"
#include "map/if/if.h"
#include "misc/vec/vecMem.h"
#include "bool/kit/kit.h"
#include "opt/rwr/rwr.h"
#include "sat/bsat/satSolver.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <ctime>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cerrno>
#include <functional>
#include <fstream>
#include <limits>
#include <map>
#include <numeric>
#include <random>
#include <queue>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "agrSpeed.h"

#include "agrPlace.h"

ABC_NAMESPACE_IMPL_START

namespace
{
using Clock = std::chrono::steady_clock;
using Truth = std::vector<unsigned>;

// Generate proposals from the current AGR placement.
static constexpr int proposalMode()
{
    return 0;
}
static int proposalPosition(Abc_Ntk_t *n, Abc_Obj_t *v, double *x, double *y)
{
    return Agr_ManReadObjectPosition(n, v, x, y);
}

static bool agrEfficientGeneration = false;
static long agrFactorCalls = 0, agrFactorHits = 0;
struct XY
{
    double x = 0, y = 0;
};
struct Axis
{
    double lo = INFINITY, lo2 = INFINITY, hi = -INFINITY, hi2 = -INFINITY;
    int nl = 0, nh = 0;
    void add(double v)
    {
        if (v < lo)
        {
            lo2 = lo;
            lo = v;
            nl = 1;
        }
        else if (v == lo)
            ++nl;
        else
            lo2 = std::min(lo2, v);
        if (v > hi)
        {
            hi2 = hi;
            hi = v;
            nh = 1;
        }
        else if (v == hi)
            ++nh;
        else
            hi2 = std::max(hi2, v);
    }
    std::pair<double, double> without(double v) const
    {
        return {v == lo && nl == 1 ? lo2 : lo, v == hi && nh == 1 ? hi2 : hi};
    }
};
struct Box
{
    std::pair<double, double> x, y;
};
double dist(double p, std::pair<double, double> b)
{
    return std::max(0.0, b.first - p) + std::max(0.0, p - b.second);
}

struct Region
{
    int root = -1, seed = -1;
    std::set<int> inside, leaves;
    double priority = -1;
    bool closed = true; // false: truth cone may include retained shared logic
};

// Explore alternative cut expansions, retaining several frontiers at each size.
// Support bounds remain exact. Closed mode stops at shared logic; reconv mode
// may inspect it, while the backend only moves/removes the actual root MFFC.
// The soft freedom factor prioritizes cuts that admit different groupings.

// Keep a useful closed cut plus several distinct support sizes. Shared cuts
// complement closed cuts rather than replacing them. Reservations are deferred
// to live validation, so an unproductive cut cannot exclude its alternatives.

// A local structurally hashed expression DAG. Literals -2/-1 are true/false.
struct Expr
{
    int k, root = -2;
    AgrSpeed::WorkspaceVector<std::pair<int, int>> a;
    std::map<std::pair<int, int>, int> hash;
    bool smallLinear;
    explicit Expr(int K) : k(K), smallLinear(agrEfficientGeneration) {}
    static int neg(int l)
    {
        return l ^ 1;
    }
    int land(int x, int y)
    {
        if (x == -1 || y == -1)
            return -1;
        if (x == -2)
            return y;
        if (y == -2)
            return x;
        if (x == y)
            return x;
        if (x == neg(y))
            return -1;
        if (x > y)
            std::swap(x, y);
        auto p = std::make_pair(x, y);
        // Small local DAGs fit in contiguous storage. Avoid allocating a tree
        // map entry per AND while preserving exact structural hashing/order.
        if (smallLinear && a.size() < 32)
        {
            for (size_t i = 0; i < a.size(); ++i)
                if (a[i] == p)
                    return 2 * (k + i);
            int z = 2 * (k + a.size());
            a.push_back(p);
            return z;
        }
        if (smallLinear && hash.empty())
            for (size_t i = 0; i < a.size(); ++i)
                hash[a[i]] = 2 * (k + i);
        auto it = hash.find(p);
        if (it != hash.end())
            return it->second;
        int z = 2 * (k + a.size());
        a.push_back(p);
        hash[p] = z;
        return z;
    }
    int lor(int x, int y)
    {
        return neg(land(neg(x), neg(y)));
    }
    int mux(int c, int t, int e)
    {
        return lor(land(c, t), land(neg(c), e));
    }
    int import(const Dec_Graph_t *g, const std::vector<int> &perm)
    {
        if (g->fConst)
            return g->eRoot.fCompl ? -1 : -2;
        std::vector<int> v(g->nSize);
        for (int i = 0; i < g->nLeaves; ++i)
            v[i] = 2 * perm[i];
        for (int i = g->nLeaves; i < g->nSize; ++i)
        {
            auto &d = g->pNodes[i];
            v[i] = land(v[d.eEdge0.Node] ^ d.eEdge0.fCompl, v[d.eEdge1.Node] ^ d.eEdge1.fCompl);
        }
        return v[g->eRoot.Node] ^ g->eRoot.fCompl;
    }
    Dec_Graph_t *graph(const std::vector<Abc_Obj_t *> &leaves) const
    {
        AGR_SPEED_SCOPE(Graph);
        if (root < 0)
            return root == -1 ? Dec_GraphCreateConst0() : Dec_GraphCreateConst1();
        auto *g = Dec_GraphCreate(k);
        for (int i = 0; i < k; ++i)
            g->pNodes[i].pFunc = leaves[i];
        AgrSpeed::Scratch<Dec_Edge_t, 64> memo(a.size());
        AgrSpeed::Scratch<unsigned char, 64> present(a.size());
        std::fill(present.data(), present.data() + a.size(), 0);
        auto visit = [&](auto &&self, int lit) -> Dec_Edge_t
        {
            int id = lit / 2;
            Dec_Edge_t e;
            if (id < k)
                e = Dec_EdgeCreate(id, 0);
            else
            {
                if (present[id - k])
                    e = memo[id - k];
                else
                {
                    auto p = a[id - k];
                    auto x = self(self, p.first), y = self(self, p.second);
                    e = Dec_GraphAddNodeAnd(g, x, y);
                    memo[id - k] = e;
                    present[id - k] = 1;
                }
            }
            e.fCompl ^= lit & 1;
            return e;
        };
        auto e = visit(visit, root);
        Dec_GraphSetRoot(g, e);
        return g;
    }
    Truth truth() const
    {
        AGR_SPEED_SCOPE(Truth);
        int bits = std::max(32, 1 << k);
        Truth out(bits / 32);
        if (agrEfficientGeneration)
        {
            // Evaluate 32 assignments at once; preserve the repeated truth bits
            // used by Kit for cuts with fewer than five variables.
            const unsigned pattern[5] = {0xAAAAAAAAu, 0xCCCCCCCCu, 0xF0F0F0F0u, 0xFF00FF00u,
                                         0xFFFF0000u};
            AgrSpeed::Scratch<unsigned, 128> scratch((k + a.size()));
            std::vector<unsigned> storage((0));
            unsigned *values = (scratch.data());
            for (int w = 0; w < bits / 32; ++w)
            {
                for (int i = 0; i < k; ++i)
                    values[i] = i < 5 ? pattern[i] : ((w >> (i - 5)) & 1 ? ~0u : 0u);
                auto value = [&](int l)
                { return l < 0 ? (l == -2 ? ~0u : 0u) : values[l / 2] ^ ((l & 1) ? ~0u : 0u); };
                for (size_t i = 0; i < a.size(); ++i)
                    values[k + i] = value(a[i].first) & value(a[i].second);
                out[w] = value(root);
            }
            return out;
        }
        std::vector<unsigned char> v(k + a.size());
        auto val = [&](int l) { return l < 0 ? l == -2 : bool(v[l / 2] ^ (l & 1)); };
        for (int b = 0; b < bits; ++b)
        {
            for (int i = 0; i < k; ++i)
                v[i] = (b >> i) & 1;
            for (size_t i = 0; i < a.size(); ++i)
                v[k + i] = val(a[i].first) && val(a[i].second);
            if (val(root))
                out[b / 32] |= 1u << (b % 32);
        }
        return out;
    }
    std::string key(bool binary = false) const
    {
        AGR_SPEED_SCOPE(Key);
        // Serialize the reachable DAG, not its exponentially expanded tree.
        // Hashes only choose child traversal order. Equality compares the full
        // serialization, so a hash collision cannot merge different graphs.
        auto mix = [](uint64_t x)
        {
            x ^= x >> 30;
            x *= 0xbf58476d1ce4e5b9ULL;
            x ^= x >> 27;
            x *= 0x94d049bb133111ebULL;
            return x ^ (x >> 31);
        };
        AgrSpeed::Scratch<uint64_t, 128> hashScratch((k + a.size()));
        std::vector<uint64_t> hashStorage((0));
        auto *hash = (hashScratch.data());
        for (int i = 0; i < k; ++i)
            hash[i] = mix(i + 1);
        auto literalHash = [&](int l) -> uint64_t
        {
            if (l < 0)
                return mix(uint64_t(l));
            return hash[l / 2] ^ ((l & 1) ? 0x9e3779b97f4a7c15ULL : 0ULL);
        };
        for (size_t i = 0; i < a.size(); ++i)
        {
            auto x = literalHash(a[i].first), y = literalHash(a[i].second);
            if (x > y)
                std::swap(x, y);
            hash[k + i] = mix(x) ^ mix(y + 0x517cc1b727220a95ULL);
        }
        AgrSpeed::Scratch<int, 128> memoScratch((k + a.size()));
        std::vector<int> memoStorage((0));
        auto *memo = (memoScratch.data());
        std::fill(memo, memo + k + a.size(), -1);
        AgrSpeed::Scratch<std::pair<int, int>, 128> canonical(a.size());
        size_t canonicalSize = 0;
        auto visit = [&](auto &&self, int l) -> int
        {
            if (l < 0 || l / 2 < k)
                return l;
            int id = l / 2;
            if (memo[id] < 0)
            {
                auto p = a[id - k];
                if (std::make_pair(literalHash(p.first), p.first) >
                    std::make_pair(literalHash(p.second), p.second))
                    std::swap(p.first, p.second);
                int x = self(self, p.first), y = self(self, p.second);
                if (x > y)
                    std::swap(x, y);
                memo[id] = 2 * (k + canonicalSize);
                canonical[canonicalSize++] = {x, y};
            }
            return memo[id] ^ (l & 1);
        };
        int result = visit(visit, root);
        if (binary)
        {
            // Write the exact little-endian canonical key into one allocation.
            std::string out((2 + 2 * canonicalSize) * 4, '\0');
            char *at = out.data();
            auto append = [&](int value)
            {
                uint32_t v = uint32_t(value);
                for (int b = 0; b < 4; ++b)
                    at[b] = char((v >> (8 * b)) & 255);
                at += 4;
            };
            append(k);
            for (size_t i = 0; i < canonicalSize; ++i)
            {
                auto p = canonical[i];
                append(p.first);
                append(p.second);
            }
            append(result);
            return out;
        }
        std::string out = std::to_string(k) + ":";
        for (size_t i = 0; i < canonicalSize; ++i)
        {
            auto p = canonical[i];
            out += std::to_string(p.first) + "," + std::to_string(p.second) + ";";
        }
        return out + "r" + std::to_string(result);
    }
};

Truth permute(const Truth &t, int k, const std::vector<int> &p, bool inv)
{
    if (agrEfficientGeneration)
    {
        bool identity = true;
        for (int i = 0; i < k; ++i)
            identity &= p[i] == i;
        if (identity)
        {
            Truth u = t;
            if (inv)
                for (auto &word : u)
                    word = ~word;
            return u;
        }
    }
    if (agrEfficientGeneration && AgrSpeed::Generation())
    {
        // Move variables by word-parallel adjacent swaps instead of rebuilding
        // every assignment index bit by bit. Keep the full repeated truth word
        // convention for cuts with fewer than five variables.
        Truth u = t;
        AgrSpeed::Scratch<unsigned, 128> temporary(t.size());
        AgrSpeed::Scratch<int, 16> labels(k);
        for (int i = 0; i < k; ++i)
            labels[i] = i;
        unsigned *current = u.data(), *next = temporary.data();
        for (int i = 0; i < k; ++i)
        {
            int j = i;
            while (labels[j] != p[i])
                ++j;
            for (; j > i; --j)
            {
                Kit_TruthSwapAdjacentVars(next, current, k, j - 1);
                std::swap(current, next);
                std::swap(labels[j], labels[j - 1]);
            }
        }
        if (current != u.data())
            std::copy(current, current + t.size(), u.begin());
        if (inv)
            for (auto &word : u)
                word = ~word;

        return u;
    }
    Truth u(t.size());
    for (int b = 0; b < int(t.size() * 32); ++b)
    {
        int old = 0;
        for (int i = 0; i < k; ++i)
            old |= ((b >> i) & 1) << p[i];
        if (bool((t[old / 32] >> (old % 32)) & 1) ^ inv)
            u[b / 32] |= 1u << (b % 32);
    }
    return u;
}
// Cache pure Kit results by transformed truth and cut size, never by positions.
// Import each cached DAG into the caller's variable space and structural hash.
struct AgrFactorKeyHash
{
    size_t operator()(const std::pair<int, Truth> &key) const
    {
        uint64_t h = 1469598103934665603ULL ^ uint64_t(key.first);
        for (unsigned word : key.second)
            h = (h ^ word) * 1099511628211ULL;
        return size_t(h ^ (h >> 32));
    }
};
// Hashes index the cache only; full key equality validates every hit.
struct AgrFactorValue
{
    Expr expression;
    std::string canonical;
};
static std::unordered_map<std::pair<int, Truth>, AgrFactorValue, AgrFactorKeyHash> agrFactorCache;
static Vec_Int_t *agrFactorMemory = nullptr;
struct AgrGenerationSession
{
    explicit AgrGenerationSession(bool efficient)
    {
        agrEfficientGeneration = efficient;
        agrFactorCalls = agrFactorHits = 0;
        if (agrFactorMemory)
            Vec_IntFree(agrFactorMemory);
        agrFactorMemory = nullptr;
    }
    ~AgrGenerationSession()
    {
        agrEfficientGeneration = false;
        if (agrFactorMemory)
            Vec_IntFree(agrFactorMemory);
        agrFactorMemory = nullptr;
    }
};
bool factor(Expr &e, const Truth &t, const std::vector<int> &p, bool inv = false,
            std::string *canonical = nullptr)
{
    AGR_SPEED_SCOPE(Factor);
    auto u = permute(t, e.k, p, inv);
    ++agrFactorCalls;
    if (agrEfficientGeneration)
    {
        auto key = std::make_pair(e.k, u);
        auto found = agrFactorCache.find(key);
        if (found == agrFactorCache.end())
        {
            // Kit resets its scratch vector on each call; the graph owns its nodes.
            if (!agrFactorMemory)
                agrFactorMemory = Vec_IntAlloc(1 << 16);
            auto *g = (Dec_Graph_t *)Kit_TruthToGraph(u.data(), e.k, agrFactorMemory);
            if (!g)
                return false;
            Expr base(e.k);
            std::vector<int> natural(e.k);
            std::iota(natural.begin(), natural.end(), 0);
            base.root = base.import(g, natural);
            Dec_GraphFree(g);
            if (agrFactorCache.size() >= 8192)
                agrFactorCache.clear();
            if (base.truth() != u)
            {
                Abc_Print(-1, "AGR_FACTOR cached truth mismatch.\n");
                std::abort();
            }
            found = agrFactorCache.emplace(std::move(key), AgrFactorValue{std::move(base), {}}).first;
        }
        else
            ++agrFactorHits;
        const auto &base = found->second.expression;
        bool natural = e.a.empty();
        for (int i = 0; i < e.k; ++i)
            natural &= p[i] == i;
        if (natural)
        {
            e = base;
            e.root ^= int(inv);
            if (canonical)
            {
                if (inv)
                    *canonical = e.key(true);
                else
                {
                    if (found->second.canonical.empty())
                        found->second.canonical = base.key(true);
                    *canonical = found->second.canonical;
                }
            }
            return true;
        }
        std::vector<int> literals;
        for (int variable : p)
            literals.push_back(2 * variable);
        auto lit = [&](int l) { return l < 0 ? l : literals[l / 2] ^ (l & 1); };
        for (auto pair : base.a)
            literals.push_back(e.land(lit(pair.first), lit(pair.second)));
        e.root = lit(base.root) ^ int(inv);
        if (canonical)
            *canonical = e.key(true);
        return true;
    }
    auto *mem = Vec_IntAlloc(1 << 16);
    auto *g = (Dec_Graph_t *)Kit_TruthToGraph(u.data(), e.k, mem);
    if (!g)
    {
        Vec_IntFree(mem);
        return false;
    }
    e.root = e.import(g, p) ^ int(inv);
    if (canonical)
        *canonical = e.key(true);
    Dec_GraphFree(g);
    Vec_IntFree(mem);
    return true;
}
Expr spatial(const Expr &src, const std::vector<XY> &points, const std::vector<int> &levels,
             int variant, const XY *rootAnchor = nullptr)
{
    AGR_SPEED_SCOPE(Spatial);
    Expr dst(src.k);
    AgrSpeed::WorkspaceVector<int> memo(src.k + src.a.size(), std::numeric_limits<int>::min());
    AgrSpeed::WorkspaceVector<XY> pos = points;
    AgrSpeed::WorkspaceVector<int> lev = levels;
    std::vector<XY> anchors;

    AgrSpeed::WorkspaceVector<int> refs(src.k + src.a.size());
    for (auto p : src.a)
    {
        if (p.first >= 0)
            ++refs[p.first / 2];
        if (p.second >= 0)
            ++refs[p.second / 2];
    }
    {
        bool regroup = false;
        for (auto p : src.a)
            for (int lit : {p.first, p.second})
                regroup |= lit >= 2 * src.k && !(lit & 1) && refs[lit / 2] <= 1;
        // With no flattenable child, spatial's binary combines preserve the
        // reachable structure exactly (including phase). Avoid rebuilding it.
        // This shortcut is used only when the complete stored DAG is reachable.
        if (!regroup)
        {
            AgrSpeed::WorkspaceVector<unsigned char> seen(src.a.size());
            size_t count = 0;
            auto visit = [&](auto &&self, int lit) -> void
            {
                if (lit < 2 * src.k)
                    return;
                size_t i = lit / 2 - src.k;
                if (seen[i])
                    return;
                seen[i] = 1;
                ++count;
                self(self, src.a[i].first);
                self(self, src.a[i].second);
            };
            visit(visit, src.root);
            if (count == src.a.size())
                return src;
        }
    }

    auto add = [&](int a, int b)
    {
        int l = dst.land(a, b);
        if (l >= 0 && int(pos.size()) <= l / 2)
        {
            pos.resize(l / 2 + 1);
            lev.resize(l / 2 + 1);
            auto x = pos[a / 2], y = pos[b / 2];
            pos[l / 2] = {(x.x + y.x) / 2, (x.y + y.y) / 2};
            lev[l / 2] = 1 + std::max(lev[a / 2], lev[b / 2]);
        }
        return l;
    };
    auto convert = [&](auto &&self, int lit) -> int
    {
        if (lit < 0 || lit / 2 < src.k)
            return lit;
        int id = lit / 2;
        if (memo[id] != std::numeric_limits<int>::min())
            return memo[id] ^ (lit & 1);
        AgrSpeed::WorkspaceVector<int> terms;
        auto flatten = [&](auto &&flat, int l) -> void
        {
            if (l >= 0 && !(l & 1) && l / 2 >= src.k && refs[l / 2] <= 1)
            {
                auto p = src.a[l / 2 - src.k];
                flat(flat, p.first);
                flat(flat, p.second);
            }
            else
                terms.push_back(self(self, l));
        };
        auto pair = src.a[id - src.k];
        flatten(flatten, pair.first);
        flatten(flatten, pair.second);

        while (terms.size() > 1)
        {
            if (std::find(terms.begin(), terms.end(), -1) != terms.end())
            {
                terms = {-1};
                break;
            }
            terms.erase(std::remove(terms.begin(), terms.end(), -2), terms.end());
            if (terms.empty())
            {
                terms = {-2};
                break;
            }
            if (terms.size() == 1)
                break;
            size_t bi = 0, bj = 1;
            double best = INFINITY;
            for (size_t i = 0; (!AgrSpeed::Generation() || terms.size() > 2) && i < terms.size();
                 ++i)
                for (size_t j = i + 1; j < terms.size(); ++j)
                {
                    auto x = pos[terms[i] / 2], y = pos[terms[j] / 2];
                    double d =
                        std::abs(x.x - y.x) + std::abs(x.y - y.y) +
                        (variant ? 2.0 : 0.0) * std::max(lev[terms[i] / 2], lev[terms[j] / 2]);

                    if (d < best)
                    {
                        best = d;
                        bi = i;
                        bj = j;
                    }
                }
            int l = add(terms[bi], terms[bj]);
            terms.erase(terms.begin() + bj);
            terms[bi] = l;
        }
        memo[id] = terms[0];
        return terms[0] ^ (lit & 1);
    };
    dst.root = convert(convert, src.root);
    return dst;
}
struct Candidate
{
    Expr e;
    std::string kind;
    // Expression is immutable after construction until the candidate is consumed.
    // Keep the exact canonical serialization, never a digest-only identity.
    mutable std::string canonical;
    mutable Truth checkedTruth;
    Candidate(Expr E, std::string K, std::string key = {}, Truth truth = {})
        : e(std::move(E)), kind(std::move(K)), canonical(std::move(key)),
          checkedTruth(std::move(truth))
    {
    }
    const Truth &truth() const
    {
        if (checkedTruth.empty())
            checkedTruth = e.truth();
        return checkedTruth;
    }
    const std::string &key() const
    {
        if (canonical.empty())
            canonical = e.key(true);
        return canonical;
    }
};
std::vector<Candidate> generate(const Expr &id, const Truth &t, const std::vector<XY> &p,
                                const std::vector<int> &levels, const std::string &kind, int cap)
{
    int k = id.k;
    std::vector<int> order(k);
    std::iota(order.begin(), order.end(), 0);
    std::vector<Candidate> out;
    std::set<std::string> seen{id.key()};
    auto push = [&](Expr e, std::string label)
    {
        if (int(out.size()) >= cap)
            return;
        if (e.truth() != t)
        {
            Abc_Print(-1, "AGR fatal: generated candidate truth mismatch (%s).\n", label.c_str());
            std::abort();
        }
        if (seen.insert(e.key()).second)
            out.emplace_back(std::move(e), label);
    };
    if (kind == "spatial")
    {
        push(spatial(id, p, levels, 0), "spatial-original");
        push(spatial(id, p, levels, 1), "spatial-depth");
        return out;
    }
    Expr ordinary(k);
    if (!factor(ordinary, t, order))
        return out;
    push(ordinary, "ordinary");
    if (kind == "ordinary" || (agrEfficientGeneration && int(out.size()) >= cap))
        return out;
    push(spatial(id, p, levels, 0), "spatial-original");
    if (agrEfficientGeneration && int(out.size()) >= cap)
        return out;
    push(spatial(ordinary, p, levels, 0), "spatial-factor");
    if (agrEfficientGeneration && int(out.size()) >= cap)
        return out;
    push(spatial(id, p, levels, 1), "spatial-depth");
    if (agrEfficientGeneration && int(out.size()) >= cap)
        return out;
    for (int axis = 0; axis < 4; ++axis)
    {
        auto perm = order;
        std::stable_sort(perm.begin(), perm.end(),
                         [&](int a, int b)
                         {
                             double x = axis % 2 ? p[a].y : p[a].x, y = axis % 2 ? p[b].y : p[b].x;
                             return axis < 2 ? x < y : x > y;
                         });
        for (int inv = 0; inv < 2; ++inv)
        {
            if (agrEfficientGeneration && int(out.size()) >= cap)
                return out;
            Expr e(k);
            if (factor(e, t, perm, inv))
                push(std::move(e), "permuted-factor");
        }
    }
    // Geometry-conditioned cofactor choices are general Boolean alternatives.
    auto perm = order;
    std::stable_sort(perm.begin(), perm.end(),
                     [&](int a, int b) { return p[a].x + p[a].y < p[b].x + p[b].y; });
    for (int c : {perm.front(), perm.back()})
    {
        if (agrEfficientGeneration && int(out.size()) >= cap)
            return out;
        Expr e(k);
        Truth lo = t, hi = t;
        for (int b = 0; b < int(t.size() * 32); ++b)
        {
            int x = b & ~(1 << c), y = b | (1 << c);
            unsigned mask = 1u << (b % 32);
            lo[b / 32] = (lo[b / 32] & ~mask) | (((t[x / 32] >> (x % 32)) & 1) ? mask : 0);
            hi[b / 32] = (hi[b / 32] & ~mask) | (((t[y / 32] >> (y % 32)) & 1) ? mask : 0);
        }
        if (!factor(e, lo, order))
            continue;
        int a = e.root;
        if (!factor(e, hi, order))
            continue;
        e.root = e.mux(2 * c, e.root, a);
        push(std::move(e), "cofactor");
    }
    return out;
}

// ABC's general Abc_NtkDup walks IDs for AIGs. New nodes can precede older
// fanouts topologically after replacement, so checkpoints need an explicit DFS.

#include "agrOperators.h"

#include "agrCompact.h"

#include "agrBroad.h"

// Used to separate initial placement from the two original PA refactoring passes.

// Stop after a complete RS/RW/RF cycle; never choose a graph by its QoR.

// parser sets DelayTarget, while Nf reads MapDelayTarget. Keep the existing
// primary evaluator unchanged; use this separate command only for explicit
// common-target sensitivity studies. Target units are Nf's internal timing
// model, NOT stime picoseconds or the backend SDC clock period.

} // namespace

extern "C" int Agr_RunBlock(Abc_Frame_t *frame, int roots)
{
    if (broadRound(frame))
        return 1;
    return compactRounds(frame, roots);
}
extern "C" void Agr_Init(Abc_Frame_t *frame)
{
    Agr_RegisterPlacementCommands(frame);
}
extern "C" void Agr_End(Abc_Frame_t *)
{
    Agr_ManShutdown();
}

ABC_NAMESPACE_IMPL_END
