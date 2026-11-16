/* Geometry-ranked algebraic divisors of a bounded ISOP cover. This changes
 * Boolean factor selection rather than merely reordering an existing tree.
 * Every output is truth-checked by the caller and evaluated by the same Pc
 * physical evaluator as the ordinary candidate. No approximate score commits. */
struct SparseDivisors
{
    struct Cover
    {
        std::vector<unsigned> cubes;
        bool complement = false, valid = false;
    };
    struct Divisor
    {
        int a, b;
        bool sum;
        int benefit;
        std::vector<unsigned> quotient, remainder;
    };
    std::map<std::pair<int, Truth>, Cover> cache;
    long queries = 0, hits = 0, proposals = 0, products = 0, sums = 0;
    const Cover &cover(const Truth &truth, int k)
    {
        ++queries;
        auto key = std::make_pair(k, truth);
        auto it = cache.find(key);
        if (it != cache.end())
        {
            ++hits;
            return it->second;
        }
        Cover result;
        Truth copy = truth;
        if (!tgFactorMemory)
            tgFactorMemory = Vec_IntAlloc(1 << 16);
        int phase = Kit_TruthIsop(copy.data(), k, tgFactorMemory, 1);
        if (phase >= 0 && Vec_IntSize(tgFactorMemory) <= 64)
        {
            unsigned *data = reinterpret_cast<unsigned *>(Vec_IntArray(tgFactorMemory));
            result.cubes.assign(data, data + Vec_IntSize(tgFactorMemory));
            int literals = 0;
            for (unsigned cube : result.cubes)
                literals += __builtin_popcount(cube);
            result.valid = literals <= 256;
            result.complement = phase;
        }
        if (cache.size() >= 1024)
            cache.clear();
        return cache.emplace(std::move(key), std::move(result)).first->second;
    }
    static Truth truthOf(const std::vector<unsigned> &cubes, int k)
    {
        const unsigned pattern[5] = {0xAAAAAAAAu, 0xCCCCCCCCu, 0xF0F0F0F0u, 0xFF00FF00u,
                                     0xFFFF0000u};
        Truth result(std::max(1, (1 << k) / 32));
        for (size_t w = 0; w < result.size(); ++w)
            for (unsigned cube : cubes)
            {
                unsigned value = ~0u;
                while (cube)
                {
                    int lit = __builtin_ctz(cube), v = lit / 2;
                    unsigned bits = v < 5 ? pattern[v] : ((w >> (v - 5)) & 1 ? ~0u : 0u);
                    value &= lit & 1 ? bits : ~bits;
                    cube &= cube - 1;
                }
                result[w] |= value;
            }
        return result;
    }
    std::vector<Divisor> divisors(const Cover &c, int k) const
    {
        // Product occurrence counts and residual buckets avoid testing all
        // cube pairs. Literal indices use Kit's negative-even encoding.
        std::map<std::pair<int, int>, int> productCounts, sumCounts;
        std::map<unsigned, std::vector<int>> residuals;
        for (unsigned cube : c.cubes)
        {
            for (int a = 0; a < 2 * k; ++a)
                if (cube & (1u << a))
                {
                    residuals[cube ^ (1u << a)].push_back(a);
                    for (int b = a + 1; b < 2 * k; ++b)
                        if (cube & (1u << b))
                            ++productCounts[{a, b}];
                }
        }
        for (const auto &entry : residuals)
        {
            const auto &lits = entry.second;
            for (size_t i = 0; i < lits.size(); ++i)
                for (size_t j = i + 1; j < lits.size(); ++j)
                {
                    int a = lits[i], b = lits[j];
                    if (a > b)
                        std::swap(a, b);
                    if (a / 2 != b / 2)
                        ++sumCounts[{a, b}];
                }
        }
        std::vector<Divisor> result;
        for (const auto &entry : productCounts)
        {
            if (entry.second < 2)
                continue;
            int a = entry.first.first, b = entry.first.second;
            unsigned mask = (1u << a) | (1u << b);
            Divisor d{a, b, false, entry.second - 1, {}, {}};
            for (unsigned cube : c.cubes)
                if ((cube & mask) == mask)
                    d.quotient.push_back(cube ^ mask);
                else
                    d.remainder.push_back(cube);
            result.push_back(std::move(d));
        }
        std::set<unsigned> all(c.cubes.begin(), c.cubes.end());
        for (const auto &entry : sumCounts)
        {
            int a = entry.first.first, b = entry.first.second;
            unsigned ba = 1u << a, bb = 1u << b;
            Divisor d{a, b, true, entry.second - 1, {}, {}};
            std::set<unsigned> used;
            for (unsigned cube : c.cubes)
                if ((cube & ba) && !(cube & bb))
                {
                    unsigned residual = cube ^ ba;
                    if (all.count(residual | bb))
                    {
                        d.quotient.push_back(residual);
                        used.insert(cube);
                        used.insert(residual | bb);
                        d.benefit += __builtin_popcount(residual);
                    }
                }
            if (d.quotient.empty() || d.benefit <= 0)
                continue;
            for (unsigned cube : c.cubes)
                if (!used.count(cube))
                    d.remainder.push_back(cube);
            result.push_back(std::move(d));
        }
        return result;
    }
    std::vector<Expr> generate(const Truth &truth, int k, const std::vector<XY> &xy, int attempts)
    {
        const auto &c = cover(truth, k);
        if (!c.valid || c.cubes.size() < 2 || attempts <= 0)
            return {};
        auto choices = divisors(c, k);
        double span = 0;
        for (int i = 0; i < k; ++i)
            for (int j = i + 1; j < k; ++j)
                span = std::max(span, std::abs(xy[i].x - xy[j].x) + std::abs(xy[i].y - xy[j].y));
        auto rank = [&](const Divisor &d)
        {
            auto a = xy[d.a / 2], b = xy[d.b / 2];
            return d.benefit /
                   (1.0 + (std::abs(a.x - b.x) + std::abs(a.y - b.y)) / std::max(span, 1e-12));
        };
        std::stable_sort(choices.begin(), choices.end(),
                         [&](const Divisor &a, const Divisor &b) { return rank(a) > rank(b); });
        std::vector<int> order(k);
        std::iota(order.begin(), order.end(), 0);
        std::vector<Expr> result;
        for (int i = 0; i < std::min(attempts, int(choices.size())); ++i)
        {
            const auto &d = choices[i];
            Expr e(k);
            if (!factor(e, truthOf(d.quotient, k), order))
                continue;
            int quotient = e.root;
            if (!factor(e, truthOf(d.remainder, k), order))
                continue;
            int divisor = d.sum ? e.lor(d.a ^ 1, d.b ^ 1) : e.land(d.a ^ 1, d.b ^ 1);
            e.root = e.lor(e.land(divisor, quotient), e.root) ^ int(c.complement);
            ++proposals;
            d.sum ? ++sums : ++products;
            result.push_back(std::move(e));
        }
        return result;
    }
};
