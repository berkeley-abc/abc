/**CFile****************************************************************

  FileName    [agrBlock.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [The AGR block: broad passes and compact cut resynthesis.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrBlock.cpp,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#include "agrInt.h"
#include "opt/pa/paWorkspace.h"
#include "bool/kit/kit.h"
#include "opt/rwr/rwr.h"

// ABC defines `inline` as a macro on MSVC; keep it out of the C++ library.
#if defined(_MSC_VER) && defined(inline)
#undef inline
#endif

#include <algorithm>
#include <array>
#include <climits>
#include <cmath>
#include <cstdint>
#include <limits>
#include <map>
#include <memory>
#include <numeric>
#include <set>
#include <string>
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
using Truth = std::vector<unsigned>;

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
        if ( v < lo )
        {
            lo2 = lo;
            lo = v;
            nl = 1;
        }
        else if ( v == lo )
            ++nl;
        else
            lo2 = std::min(lo2, v);
        if ( v > hi )
        {
            hi2 = hi;
            hi = v;
            nh = 1;
        }
        else if ( v == hi )
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
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the distance of a point to an interval.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
double dist(double p, std::pair<double, double> b)
{
    return std::max(0.0, b.first - p) + std::max(0.0, p - b.second);
}

struct Region
{
    int root = -1, seed = -1;
    std::set<int> inside, leaves;
    bool closed = true; // false: truth cone may include retained shared logic
};

// A local structurally hashed expression DAG. Literals -2/-1 are true/false.
struct Expr
{
    int k, root = -2;
    PaWorkspace::WorkspaceVector<std::pair<int, int>> a;
    std::map<std::pair<int, int>, int> hash;
    explicit Expr(int K) : k(K)
    {
    }
    static int neg(int l)
    {
        return l ^ 1;
    }
    int land(int x, int y)
    {
        if ( x == -1 || y == -1 )
            return -1;
        if ( x == -2 )
            return y;
        if ( y == -2 )
            return x;
        if ( x == y )
            return x;
        if ( x == neg(y) )
            return -1;
        if ( x > y )
            std::swap(x, y);
        auto p = std::make_pair(x, y);
        // Small local DAGs fit in contiguous storage. Avoid allocating a tree
        // map entry per AND while preserving exact structural hashing/order.
        if ( a.size() < 32 )
        {
            for ( size_t i = 0; i < a.size(); ++i )
                if ( a[i] == p )
                    return 2 * (k + i);
            int z = 2 * (k + a.size());
            a.push_back(p);
            return z;
        }
        if ( hash.empty() )
            for ( size_t i = 0; i < a.size(); ++i )
                hash[a[i]] = 2 * (k + i);
        auto it = hash.find(p);
        if ( it != hash.end() )
            return it->second;
        int z = 2 * (k + a.size());
        a.push_back(p);
        hash[p] = z;
        return z;
    }
    int import(const Dec_Graph_t * g, const std::vector<int> & perm)
    {
        if ( g->fConst )
            return g->eRoot.fCompl ? -1 : -2;
        std::vector<int> v(g->nSize);
        for ( int i = 0; i < g->nLeaves; ++i )
            v[i] = 2 * perm[i];
        for ( int i = g->nLeaves; i < g->nSize; ++i )
        {
            auto & d = g->pNodes[i];
            v[i] = land(v[d.eEdge0.Node] ^ d.eEdge0.fCompl, v[d.eEdge1.Node] ^ d.eEdge1.fCompl);
        }
        return v[g->eRoot.Node] ^ g->eRoot.fCompl;
    }
    Dec_Graph_t * graph(const std::vector<Abc_Obj_t *> & leaves) const
    {
        if ( root < 0 )
            return root == -1 ? Dec_GraphCreateConst0() : Dec_GraphCreateConst1();
        auto * g = Dec_GraphCreate(k);
        for ( int i = 0; i < k; ++i )
            g->pNodes[i].pFunc = leaves[i];
        PaWorkspace::Scratch<Dec_Edge_t, 64> memo(a.size());
        PaWorkspace::Scratch<unsigned char, 64> present(a.size());
        std::fill(present.data(), present.data() + a.size(), 0);
        auto visit = [&](auto && self, int lit) -> Dec_Edge_t
        {
            int id = lit / 2;
            Dec_Edge_t e;
            if ( id < k )
                e = Dec_EdgeCreate(id, 0);
            else
            {
                if ( present[id - k] )
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
        int bits = std::max(32, 1 << k);
        Truth out(bits / 32);
        // Evaluate 32 assignments at once; cuts with fewer than five variables
        // repeat their truth bits across the word, as Kit does.
        const unsigned pattern[5] = {0xAAAAAAAAu, 0xCCCCCCCCu, 0xF0F0F0F0u, 0xFF00FF00u, 0xFFFF0000u};
        PaWorkspace::Scratch<unsigned, 128> scratch((k + a.size()));
        unsigned * values = scratch.data();
        for ( int w = 0; w < bits / 32; ++w )
        {
            for ( int i = 0; i < k; ++i )
                values[i] = i < 5 ? pattern[i] : ((w >> (i - 5)) & 1 ? ~0u : 0u);
            auto value = [&](int l) { return l < 0 ? (l == -2 ? ~0u : 0u) : values[l / 2] ^ ((l & 1) ? ~0u : 0u); };
            for ( size_t i = 0; i < a.size(); ++i )
                values[k + i] = value(a[i].first) & value(a[i].second);
            out[w] = value(root);
        }
        return out;
    }
    std::string key(bool binary = false) const
    {
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
        PaWorkspace::Scratch<uint64_t, 128> hashScratch((k + a.size()));
        auto * hash = hashScratch.data();
        for ( int i = 0; i < k; ++i )
            hash[i] = mix(i + 1);
        auto literalHash = [&](int l) -> uint64_t
        {
            if ( l < 0 )
                return mix(uint64_t(l));
            return hash[l / 2] ^ ((l & 1) ? 0x9e3779b97f4a7c15ULL : 0ULL);
        };
        for ( size_t i = 0; i < a.size(); ++i )
        {
            auto x = literalHash(a[i].first), y = literalHash(a[i].second);
            if ( x > y )
                std::swap(x, y);
            hash[k + i] = mix(x) ^ mix(y + 0x517cc1b727220a95ULL);
        }
        PaWorkspace::Scratch<int, 128> memoScratch((k + a.size()));
        auto * memo = memoScratch.data();
        std::fill(memo, memo + k + a.size(), -1);
        PaWorkspace::Scratch<std::pair<int, int>, 128> canonical(a.size());
        size_t canonicalSize = 0;
        auto visit = [&](auto && self, int l) -> int
        {
            if ( l < 0 || l / 2 < k )
                return l;
            int id = l / 2;
            if ( memo[id] < 0 )
            {
                auto p = a[id - k];
                if ( std::make_pair(literalHash(p.first), p.first) > std::make_pair(literalHash(p.second), p.second) )
                    std::swap(p.first, p.second);
                int x = self(self, p.first), y = self(self, p.second);
                if ( x > y )
                    std::swap(x, y);
                memo[id] = 2 * (k + canonicalSize);
                canonical[canonicalSize++] = {x, y};
            }
            return memo[id] ^ (l & 1);
        };
        int result = visit(visit, root);
        if ( binary )
        {
            // Write the exact little-endian canonical key into one allocation.
            std::string out((2 + 2 * canonicalSize) * 4, '\0');
            char * at = out.data();
            auto append = [&](int value)
            {
                uint32_t v = uint32_t(value);
                for ( int b = 0; b < 4; ++b )
                    at[b] = char((v >> (8 * b)) & 255);
                at += 4;
            };
            append(k);
            for ( size_t i = 0; i < canonicalSize; ++i )
            {
                auto p = canonical[i];
                append(p.first);
                append(p.second);
            }
            append(result);
            return out;
        }
        std::string out = std::to_string(k) + ":";
        for ( size_t i = 0; i < canonicalSize; ++i )
        {
            auto p = canonical[i];
            out += std::to_string(p.first) + "," + std::to_string(p.second) + ";";
        }
        return out + "r" + std::to_string(result);
    }
};

/**Function*************************************************************

  Synopsis    [Returns the truth table with variable p[i] renamed to i.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Truth permute(const Truth & t, int k, const std::vector<int> & p)
{
    bool identity = true;
    for ( int i = 0; i < k; ++i )
        identity &= p[i] == i;
    if ( identity )
        return t;
    // Word-parallel adjacent swaps; cuts with fewer than five variables
    // keep the repeated truth-word convention.
    Truth u = t;
    PaWorkspace::Scratch<unsigned, 128> temporary(t.size());
    PaWorkspace::Scratch<int, 16> labels(k);
    for ( int i = 0; i < k; ++i )
        labels[i] = i;
    unsigned *current = u.data(), *next = temporary.data();
    for ( int i = 0; i < k; ++i )
    {
        int j = i;
        while ( labels[j] != p[i] )
            ++j;
        for ( ; j > i; --j )
        {
            Kit_TruthSwapAdjacentVars(next, current, k, j - 1);
            std::swap(current, next);
            std::swap(labels[j], labels[j - 1]);
        }
    }
    if ( current != u.data() )
        std::copy(current, current + t.size(), u.begin());
    return u;
}
// Cache pure Kit results by transformed truth and cut size, never by positions.
// Import each cached DAG into the caller's variable space and structural hash.
struct FactorKeyHash
{
    size_t operator()(const std::pair<int, Truth> & key) const
    {
        uint64_t h = 1469598103934665603ULL ^ uint64_t(key.first);
        for ( unsigned word : key.second )
            h = (h ^ word) * 1099511628211ULL;
        return size_t(h ^ (h >> 32));
    }
};
// Hashes index the cache only; full key equality validates every hit.
struct FactorValue
{
    Expr expression;
    std::string canonical;
};
using KitFactorCache = std::unordered_map<std::pair<int, Truth>, FactorValue, FactorKeyHash>;
// Per-frame state; see AgrState at the end of this file.
static KitFactorCache & factorCache();
static Vec_Int_t *& factorMemory();
// Owns Kit's scratch memory for one compact pass.
struct KitSession
{
    KitSession()
    {
        Release();
    }
    ~KitSession()
    {
        Release();
    }
    static void Release()
    {
        if ( factorMemory() )
            Vec_IntFree(factorMemory());
        factorMemory() = nullptr;
    }
};
/**Function*************************************************************

  Synopsis    [Factors a truth table over permuted variables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
bool factor(Expr & e, const Truth & t, const std::vector<int> & p, std::string * canonical = nullptr)
{
    auto u = permute(t, e.k, p);
    auto key = std::make_pair(e.k, u);
    auto found = factorCache().find(key);
    if ( found == factorCache().end() )
    {
        // Kit resets its scratch vector on each call; the graph owns its nodes.
        if ( !factorMemory() )
            factorMemory() = Vec_IntAlloc(1 << 16);
        auto * g = (Dec_Graph_t *)Kit_TruthToGraph(u.data(), e.k, factorMemory());
        if ( !g )
            return false;
        Expr base(e.k);
        std::vector<int> natural(e.k);
        std::iota(natural.begin(), natural.end(), 0);
        base.root = base.import(g, natural);
        Dec_GraphFree(g);
        if ( factorCache().size() >= 8192 )
            factorCache().clear();
        assert(base.truth() == u);
        found = factorCache().emplace(std::move(key), FactorValue{std::move(base), {}}).first;
    }
    const auto & base = found->second.expression;
    bool natural = e.a.empty();
    for ( int i = 0; i < e.k; ++i )
        natural &= p[i] == i;
    if ( natural )
    {
        e = base;
        if ( canonical )
        {
            if ( found->second.canonical.empty() )
                found->second.canonical = base.key(true);
            *canonical = found->second.canonical;
        }
        return true;
    }
    std::vector<int> literals;
    for ( int variable : p )
        literals.push_back(2 * variable);
    auto lit = [&](int l) { return l < 0 ? l : literals[l / 2] ^ (l & 1); };
    for ( auto pair : base.a )
        literals.push_back(e.land(lit(pair.first), lit(pair.second)));
    e.root = lit(base.root);
    if ( canonical )
        *canonical = e.key(true);
    return true;
}
/**Function*************************************************************

  Synopsis    [Regroups the AND trees of an expression by geometry.]

  Description [Regroups the cut function's AND trees by geometry: flattened
               single-use AND chains are recombined closest pair first.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Expr spatial(const Expr & src, const std::vector<XY> & points)
{
    Expr dst(src.k);
    PaWorkspace::WorkspaceVector<int> memo(src.k + src.a.size(), std::numeric_limits<int>::min());
    PaWorkspace::WorkspaceVector<XY> pos = points;

    PaWorkspace::WorkspaceVector<int> refs(src.k + src.a.size());
    for ( auto p : src.a )
    {
        if ( p.first >= 0 )
            ++refs[p.first / 2];
        if ( p.second >= 0 )
            ++refs[p.second / 2];
    }
    {
        bool regroup = false;
        for ( auto p : src.a )
            for ( int lit : {p.first, p.second} )
                regroup |= lit >= 2 * src.k && !(lit & 1) && refs[lit / 2] <= 1;
        // With no flattenable child, spatial's binary combines preserve the
        // reachable structure exactly (including phase). Avoid rebuilding it.
        // This shortcut is used only when the complete stored DAG is reachable.
        if ( !regroup )
        {
            PaWorkspace::WorkspaceVector<unsigned char> seen(src.a.size());
            size_t count = 0;
            auto visit = [&](auto && self, int lit) -> void
            {
                if ( lit < 2 * src.k )
                    return;
                size_t i = lit / 2 - src.k;
                if ( seen[i] )
                    return;
                seen[i] = 1;
                ++count;
                self(self, src.a[i].first);
                self(self, src.a[i].second);
            };
            visit(visit, src.root);
            if ( count == src.a.size() )
                return src;
        }
    }

    auto add = [&](int a, int b)
    {
        int l = dst.land(a, b);
        if ( l >= 0 && int(pos.size()) <= l / 2 )
        {
            pos.resize(l / 2 + 1);
            auto x = pos[a / 2], y = pos[b / 2];
            pos[l / 2] = {(x.x + y.x) / 2, (x.y + y.y) / 2};
        }
        return l;
    };
    auto convert = [&](auto && self, int lit) -> int
    {
        if ( lit < 0 || lit / 2 < src.k )
            return lit;
        int id = lit / 2;
        if ( memo[id] != std::numeric_limits<int>::min() )
            return memo[id] ^ (lit & 1);
        PaWorkspace::WorkspaceVector<int> terms;
        auto flatten = [&](auto && flat, int l) -> void
        {
            if ( l >= 0 && !(l & 1) && l / 2 >= src.k && refs[l / 2] <= 1 )
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

        while ( terms.size() > 1 )
        {
            if ( std::find(terms.begin(), terms.end(), -1) != terms.end() )
            {
                terms = {-1};
                break;
            }
            terms.erase(std::remove(terms.begin(), terms.end(), -2), terms.end());
            if ( terms.empty() )
            {
                terms = {-2};
                break;
            }
            if ( terms.size() == 1 )
                break;
            size_t bi = 0, bj = 1;
            double best = INFINITY;
            for ( size_t i = 0; terms.size() > 2 && i < terms.size(); ++i )
                for ( size_t j = i + 1; j < terms.size(); ++j )
                {
                    auto x = pos[terms[i] / 2], y = pos[terms[j] / 2];
                    double d = std::abs(x.x - y.x) + std::abs(x.y - y.y);
                    if ( d < best )
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
    // Expression is immutable after construction until the candidate is consumed.
    // Keep the exact canonical serialization, never a digest-only identity.
    mutable std::string canonical;
    mutable Truth checkedTruth;
    explicit Candidate(Expr E, std::string key = {}, Truth truth = {})
        : e(std::move(E)), canonical(std::move(key)), checkedTruth(std::move(truth))
    {
    }
    const Truth & truth() const
    {
        if ( checkedTruth.empty() )
            checkedTruth = e.truth();
        return checkedTruth;
    }
    const std::string & key() const
    {
        if ( canonical.empty() )
            canonical = e.key(true);
        return canonical;
    }
};

/**Function*************************************************************

  Synopsis    [Returns the factored form of a cut unless it repeats the cut.]

  Description [The ordinary factored form of t, unless it repeats the cut's
               structure.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
std::vector<Candidate> ordinaryCandidate(const Expr & id, const Truth & t)
{
    std::vector<Candidate> out;
    std::vector<int> order(id.k);
    std::iota(order.begin(), order.end(), 0);
    Expr ordinary(id.k);
    if ( !factor(ordinary, t, order) )
        return out;
    assert(ordinary.truth() == t);
    if ( ordinary.key() != id.key() )
        out.emplace_back(std::move(ordinary));
    return out;
}

#include "agrCompact.h"

#include "agrBroad.h"

// The mutable state of AGR in the current frame: the state of one command,
// and caches of factored forms that persist between commands.
struct AgrState
{
    int verbose = 0;
    BlockState block;
    KitFactorCache factorCache;
    Vec_Int_t * factorMemory = nullptr;
    CareSet::CareCache care;
    CareSet::FactorCache careFactors;
    StructureLibrary::Data library;
    ~AgrState()
    {
        if ( factorMemory )
            Vec_IntFree(factorMemory);
    }
};
static ABC_THREAD_LOCAL AgrState * s_pAgr = nullptr;
/**Function*************************************************************

  Synopsis    [Allocates the AGR state of a frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void * AgrStateAlloc()
{
    return new AgrState();
}
/**Function*************************************************************

  Synopsis    [Frees the AGR state of a frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void AgrStateFree(void * p)
{
    delete static_cast<AgrState *>(p);
}
/**Function*************************************************************

  Synopsis    [Binds the AGR state of the current frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void AgrBind()
{
    s_pAgr = static_cast<AgrState *>(Pa_FrameState(PA_STATE_AGR, AgrStateAlloc, AgrStateFree));
}
/**Function*************************************************************

  Synopsis    [Returns the cache of factored forms.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static KitFactorCache & factorCache()
{
    return s_pAgr->factorCache;
}
/**Function*************************************************************

  Synopsis    [Returns the scratch memory of the factoring.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t *& factorMemory()
{
    return s_pAgr->factorMemory;
}
/**Function*************************************************************

  Synopsis    [Returns the cache of don't-care factored forms.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
CareSet::CareCache & CareSet::SharedCare()
{
    return s_pAgr->care;
}
/**Function*************************************************************

  Synopsis    [Returns the cache of don't-care candidates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
CareSet::FactorCache & CareSet::SharedFactors()
{
    return s_pAgr->careFactors;
}
/**Function*************************************************************

  Synopsis    [Returns the cache of library structures.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
StructureLibrary::Data & StructureLibrary::SharedData()
{
    return s_pAgr->library;
}
/**Function*************************************************************

  Synopsis    [Returns the state of the current agr command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static BlockState & blockState()
{
    return s_pAgr->block;
}

} // namespace

/**Function*************************************************************

  Synopsis    [Sets the verbosity of the current agr command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Agr_SetVerbose(int fVerbose)
{
    AgrBind();
    s_pAgr->verbose = fVerbose;
}

/**Function*************************************************************

  Synopsis    [Returns the verbosity of the current agr command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Agr_IsVerbose(void)
{
    AgrBind();
    return s_pAgr->verbose;
}

/**Function*************************************************************

  Synopsis    [Frees the state kept between the blocks of one agr command.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Agr_ResetBlock(void)
{
    AgrBind();
    s_pAgr->block = BlockState{};
}

/**Function*************************************************************

  Synopsis    [Runs one AGR block on the placed current network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Agr_RunBlock(Abc_Frame_t * pAbc, int nRoots)
{
    AgrBind();
    if ( broadRound(pAbc) )
        return 1;
    return compactRounds(pAbc, nRoots);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
