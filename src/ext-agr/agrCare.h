/* Exact reachable cut-input patterns over a bounded upstream window.
 * Window terminals are independent: their enumeration over-approximates all
 * real assignments. Only patterns absent from this over-approximation are DCs.
 * No sampling, external assumptions, or downstream observability is used.
 */
#include "agrGlobalCare.h"
struct SparseCare
{
    SparseGlobalCare global;
    SparseExpressionReader reader;
    using CareCache = std::unordered_map<std::string, Truth>;
    using FactorCache = std::unordered_map<std::string, Candidate>;
    static CareCache &SharedCare()
    {
        static CareCache values;
        return values;
    }
    static FactorCache &SharedFactors()
    {
        static FactorCache values;
        return values;
    }
    CareCache localCare;
    FactorCache localFactors;
    CareCache &cache;
    FactorCache &factors;
    SparseCare() : cache((SharedCare())), factors((SharedFactors())) {}
    SparseCare(const SparseCare &) = delete;
    SparseCare &operator=(const SparseCare &) = delete;
    // Only full Boolean expressions/tables cross command boundaries. Semantic
    // node-ID masks below remain private to this invocation and are destroyed
    // before the caller reassigns network IDs.
    // Scoped to a single sparseRounds invocation. IDs are append-only until
    // its final reassignment. Each accepted local edit preserves the Boolean
    // function of every surviving node, including its stored polarity. Thus a
    // conservative care mask for these ordered leaf IDs stays conservative
    // after later equivalent edits, even if a freshly expanded window differs.
    // Never cache coordinates, scores, cuts, or cross-command node identities.
    std::unordered_map<std::string, Truth> semantic;
    size_t semanticBytes = 0;
    std::unordered_map<std::string, Truth> witnessed;
    long optimisticCandidates = 0, provenCandidates = 0;
    long semanticHits = 0;
    bool disableSemantic = false;
    long queries = 0, hits = 0, restricted = 0, proposals = 0, factorCalls = 0, factorHits = 0;
    Truth reachable(Abc_Ntk_t *n, const std::vector<Abc_Obj_t *> &leaves, int depth)
    {
        ++queries;
        std::string semanticKey;
        const bool useSemantic = 1 && !disableSemantic;
        if (useSemantic)
        {
            semanticKey.reserve(4 * leaves.size());
            for (auto *v : leaves)
                for (int b = 0; b < 4; ++b)
                    semanticKey.push_back(char((unsigned(v->Id) >> (8 * b)) & 255));
            auto found = semantic.find(semanticKey);
            if (found != semantic.end())
            {
                ++semanticHits;
                return found->second;
            }
        }
        auto remember = [&](const Truth &value)
        {
            if (!useSemantic)
                return;
            const size_t bytes = semanticKey.size() + sizeof(unsigned) * value.size() + 96;
            if (semantic.size() >= 131072 || semanticBytes + bytes > 32u * 1024 * 1024)
            {
                semantic.clear();
                semanticBytes = 0;
            }
            semantic.emplace(std::move(semanticKey), value);
            semanticBytes += bytes;
        };
        auto finish = [&](Truth value)
        {
            // Like semantic masks, immutable CNF definitions are sound only
            // while every surviving node preserves its global Boolean function.
            // Observability-changing experiments explicitly disable this path.

            remember(value);
            return value;
        };
        // At most twelve ordinary window terminals: contiguous, ID-sorted
        // storage preserves the reference map's expansion and tie order.
        AgrSpeed::WorkspaceVector<std::pair<int, int>> frontier;
        frontier.reserve(12);
        auto locate = [&](int id)
        {
            return std::lower_bound(frontier.begin(), frontier.end(), id,
                                    [](const std::pair<int, int> &v, int key)
                                    { return v.first < key; });
        };
        auto insert = [&](int id, int depth)
        {
            auto at = locate(id);
            if (at == frontier.end() || at->first != id)
                frontier.insert(at, {id, depth});
            else
                at->second = std::min(at->second, depth);
        };
        for (auto *v : leaves)
            insert(v->Id, 0);
        for (int step = 0; step < 32; ++step)
        {
            int chosen = -1, cost = INT_MAX, level = -1;
            for (auto entry : frontier)
            {
                auto *v = Abc_NtkObj(n, entry.first);
                if (!Abc_ObjIsNode(v) || Abc_AigNodeIsConst(v) || entry.second >= depth)
                    continue;
                int additional = 0;
                for (int side = 0; side < 2; ++side)
                {
                    auto *f = Abc_ObjFanin(v, side);
                    auto at = locate(f->Id);
                    additional +=
                        !Abc_AigNodeIsConst(f) && (at == frontier.end() || at->first != f->Id);
                }
                if (int(frontier.size()) - 1 + additional > 12)
                    continue;
                if (additional < cost || (additional == cost && int(v->Level) > level))
                {
                    chosen = v->Id;
                    cost = additional;
                    level = v->Level;
                }
            }
            if (chosen < 0)
                break;
            auto at = locate(chosen);
            int nextDepth = at->second + 1;
            frontier.erase(at);
            auto *v = Abc_NtkObj(n, chosen);
            for (int side = 0; side < 2; ++side)
            {
                auto *f = Abc_ObjFanin(v, side);
                if (Abc_AigNodeIsConst(f))
                    continue;
                insert(f->Id, nextDepth);
            }
        }
        AgrSpeed::WorkspaceVector<Abc_Obj_t *> boundary;
        boundary.reserve(frontier.size());
        for (auto entry : frontier)
            boundary.push_back(Abc_NtkObj(n, entry.first));
        std::string key;
        auto append = [&](unsigned v)
        {
            char bytes[4];
            for (int b = 0; b < 4; ++b)
                bytes[b] = char((v >> (8 * b)) & 255);
            key.append(bytes, 4);
        };
        append(boundary.size());
        append(leaves.size());
        const int words = std::max(1, (1 << boundary.size()) / 32);
        AgrSpeed::WorkspaceVector<unsigned> values;
        {
            // Read the entire upstream window once. Shared internal functions
            // are evaluated once per truth word, with all cut-leaf functions
            // retained as outputs. The cache compares the complete DAG key.
            Region region;
            AgrSpeed::WorkspaceVector<int> outputs;
            Expr joint = reader.read(n, region, boundary, &leaves, &outputs);
            append(~0u);
            append(joint.a.size());
            for (auto pair : joint.a)
            {
                append(unsigned(pair.first));
                append(unsigned(pair.second));
            }
            for (int literal : outputs)
                append(unsigned(literal));
            auto found = cache.find(key);
            if (found != cache.end())
            {
                ++hits;
                return finish(found->second);
            }
            values.resize(outputs.size() * words);
            const unsigned pattern[5] = {0xAAAAAAAAu, 0xCCCCCCCCu, 0xF0F0F0F0u, 0xFF00FF00u,
                                         0xFFFF0000u};
            AgrSpeed::Scratch<unsigned, 128> storage(joint.k + joint.a.size());
            auto literal = [&](int l)
            { return l < 0 ? (l == -2 ? ~0u : 0u) : storage[l / 2] ^ ((l & 1) ? ~0u : 0u); };
            for (int w = 0; w < words; ++w)
            {
                for (int i = 0; i < joint.k; ++i)
                    storage[i] = i < 5 ? pattern[i] : ((w >> (i - 5)) & 1 ? ~0u : 0u);
                for (size_t i = 0; i < joint.a.size(); ++i)
                    storage[joint.k + i] = literal(joint.a[i].first) & literal(joint.a[i].second);
                for (size_t i = 0; i < outputs.size(); ++i)
                    values[i * words + w] = literal(outputs[i]);
            }
        }
        Truth care(std::max(1, (1 << leaves.size()) / 32), 0);

        {
            // Transpose eight assignment bits from eight leaf bitplanes at a
            // time. Each resulting byte is an exact cut-input pattern. Two
            // groups cover every supported cut, without recursive splitting.
            auto transpose = [](uint64_t x)
            {
                uint64_t t = (x ^ (x >> 7)) & 0x00AA00AA00AA00AAULL;
                x ^= t ^ (t << 7);
                t = (x ^ (x >> 14)) & 0x0000CCCC0000CCCCULL;
                x ^= t ^ (t << 14);
                t = (x ^ (x >> 28)) & 0x00000000F0F0F0F0ULL;
                return x ^ t ^ (t << 28);
            };
            unsigned missing = 1u << leaves.size();
            for (size_t word = 0; word < size_t(words) && missing; ++word)
            {
                for (unsigned shift = 0; shift < 32 && missing; shift += 8)
                {
                    uint64_t low = 0, high = 0;
                    for (size_t i = 0; i < std::min(size_t(8), leaves.size()); ++i)
                        low |= uint64_t((values[i * words + word] >> shift) & 255u) << (8 * i);
                    for (size_t i = 8; i < leaves.size(); ++i)
                        high |= uint64_t((values[i * words + word] >> shift) & 255u)
                                << (8 * (i - 8));
                    low = transpose(low);
                    high = transpose(high);
                    for (unsigned i = 0; i < 8; ++i)
                    {
                        unsigned pattern = unsigned((low >> (8 * i)) & 255u) |
                                           (unsigned((high >> (8 * i)) & 255u) << 8);
                        unsigned bit = 1u << (pattern % 32);
                        if (!(care[pattern / 32] & bit))
                        {
                            care[pattern / 32] |= bit;
                            --missing;
                        }
                    }
                }
            }
        }
        // ABC truth words repeat their support below five variables.
        if (leaves.size() < 5)
            for (unsigned bit = 1u << leaves.size(); bit < 32; ++bit)
                if (care[0] & (1u << (bit & ((1u << leaves.size()) - 1))))
                    care[0] |= 1u << bit;
        if (cache.size() >= 4096)
            cache.clear();
        cache.emplace(std::move(key), care);
        return finish(std::move(care));
    }
    static bool equivalent(const Truth &a, const Truth &b, const Truth &care)
    {
        if (a.size() != b.size() || a.size() != care.size())
            return false;
        for (size_t i = 0; i < a.size(); ++i)
            if ((a[i] ^ b[i]) & care[i])
                return false;
        return true;
    }

    void append(std::vector<Candidate> &out, const Expr &id, const Truth &truth, const Truth &care,
                const std::vector<XY> &xy, const std::vector<int> &levels,
                const std::string *originalKey = nullptr)
    {
        if (std::all_of(care.begin(), care.end(), [](unsigned w) { return w == ~0u; }))
            return;
        ++restricted;
        const auto original = originalKey ? *originalKey : id.key(true);
        std::vector<std::vector<int>> orders;
        for (int which = 0; which <= 2; ++which)
        {
            std::vector<int> order(id.k);
            std::iota(order.begin(), order.end(), 0);
            if (which)
            {
                auto coordinate = [&](int i) -> double
                {
                    return which == 1   ? xy[i].x
                           : which == 2 ? xy[i].y
                           : which == 3 ? double(levels[i])
                           : which == 4 ? xy[i].x + xy[i].y
                           : which == 5 ? xy[i].x - xy[i].y
                                        : -double(i);
                };
                std::stable_sort(order.begin(), order.end(),
                                 [&](int a, int b) { return coordinate(a) < coordinate(b); });
            }
            if (std::find(orders.begin(), orders.end(), order) != orders.end())
                continue;
            orders.push_back(order);
            auto orderedTruth = permute(truth, id.k, order, false),
                 orderedCare = permute(care, id.k, order, false);
            for (int phase = 0; phase < 2; ++phase)
            {
                Truth on(truth.size()), off(truth.size());
                for (size_t i = 0; i < truth.size(); ++i)
                {
                    unsigned f = phase ? ~orderedTruth[i] : orderedTruth[i];
                    on[i] = f & orderedCare[i];
                    off[i] = ~f & orderedCare[i];
                }
                // Cache only the pure Boolean factorization. Variable order,
                // polarity and both complete on/off tables are part of the key;
                // spatial regrouping and physical evaluation remain live below.
                ++factorCalls;
                std::string factorKey;
                factorKey.reserve(8 + 8 * truth.size());
                auto appendWord = [&](unsigned word)
                {
                    char bytes[4];
                    for (int b = 0; b < 4; ++b)
                        bytes[b] = char((word >> (8 * b)) & 255);
                    factorKey.append(bytes, 4);
                };
                appendWord(id.k);
                appendWord(phase);
                for (unsigned word : on)
                    appendWord(word);
                for (unsigned word : off)
                    appendWord(word);
                if (which)
                {
                    appendWord(~0u);
                    for (int variable : order)
                        appendWord(variable);
                }
                const bool useCache = 1;
                auto found = factors.find(factorKey);
                const bool hit = useCache && found != factors.end();
                Expr e(id.k);
                if (hit)
                {
                    e = found->second.e;
                    ++factorHits;
                }
                if (!hit || AgrSpeed::CareAudit())
                {
                    if (!agrFactorMemory)
                        agrFactorMemory = Vec_IntAlloc(1 << 16);
                    auto *g = (Dec_Graph_t *)Kit_TruthToGraph2(off.data(), on.data(), id.k,
                                                               agrFactorMemory);
                    if (!g)
                    {
                        if (hit)
                        {
                            Abc_Print(-1, "AGR_CARE cached factor failed recomputation.\n");
                            std::abort();
                        }
                        continue;
                    }
                    Expr fresh(id.k);
                    fresh.root = fresh.import(g, order) ^ phase;
                    Dec_GraphFree(g);
                    if (hit)
                    {
                        if (e.key(true) != fresh.key(true))
                        {
                            Abc_Print(-1, "AGR_CARE factor cache mismatch.\n");
                            std::abort();
                        }
                    }
                    else
                    {
                        e = std::move(fresh);
                        {
                            if (factors.size() >= 8192)
                                factors.clear();
                            found =
                                factors
                                    .emplace(std::move(factorKey),
                                             Candidate(e, "care-factor", e.key(true), e.truth()))
                                    .first;
                        }
                    }
                }
                for (int variant = 0; variant < 2; ++variant)
                {
                    Expr proposal = variant ? spatial(e, xy, levels, 0) : e;
                    if (variant && !AgrSpeed::CareAudit() && proposal.root == e.root &&
                        proposal.a == e.a)
                        continue;
                    auto key = (!variant && useCache) ? found->second.key() : proposal.key(true);
                    const bool duplicate =
                        key == original ||
                        std::any_of(out.begin(), out.end(),
                                    [&](const Candidate &c) { return c.key() == key; });
                    if (duplicate && !AgrSpeed::CareAudit())
                        continue;
                    auto actualTruth =
                        (!variant && useCache) ? found->second.truth() : proposal.truth();
                    if (!equivalent(actualTruth, truth, care))
                    {
                        Abc_Print(-1, "AGR_CARE truth mismatch.\n");
                        std::abort();
                    }
                    if (duplicate)
                        continue;
                    out.emplace_back(std::move(proposal),
                                     which ? (variant ? "care-permuted-spatial" : "care-permuted")
                                           : (variant ? "care-spatial" : "care-factor"),
                                     std::move(key), std::move(actualTruth));
                    ++proposals;
                }
            }
        }
    }
};
