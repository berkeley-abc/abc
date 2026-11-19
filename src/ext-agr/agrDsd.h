/* Geometry-guided disjoint-support factoring. Boolean decomposition is cached;
 * spatial decisions are rebuilt from current boundary positions on every use.
 * This proposes candidates only: the PA-derived evaluator remains authoritative.
 */
struct SparseDsd
{
    std::map<std::pair<int, Truth>, Kit_DsdNtk_t *> cache;
    long calls = 0, hits = 0;
    std::function<Expr(const Truth &, const Expr &, const std::vector<XY> &,
                       const std::vector<int> &)>
        primeFactory;
    ~SparseDsd()
    {
        for (auto &v : cache)
            Kit_DsdNtkFree(v.second);
    }
    Expr generate(const Truth &truth, int k, const std::vector<XY> &xy,
                  const std::vector<int> &levels, bool balanced = false, const XY *anchor = nullptr,
                  const std::vector<XY> *future = nullptr, const XY *futureAnchor = nullptr,
                  int cellArity = 2)
    {
        ++calls;
        auto key = std::make_pair(k, truth);
        auto found = cache.find(key);
        Kit_DsdNtk_t *ntk;
        if (found != cache.end())
        {
            ++hits;
            ntk = found->second;
        }
        else
        {
            if (cache.size() >= 8192)
            {
                for (auto &v : cache)
                    Kit_DsdNtkFree(v.second);
                cache.clear();
            }
            Truth copy = truth;
            ntk = Kit_DsdDecomposeExpand(copy.data(), k);
            cache.emplace(std::move(key), ntk);
        }
        Expr e(k);
        struct Term
        {
            int lit;
            XY pos;
            int level;
            XY future{0, 0};
        };
        std::vector<Term> memo(Kit_DsdNtkObjNum(ntk));
        std::vector<char> seen(memo.size());
        for (int i = 0; i < k; ++i)
        {
            memo[i] = {2 * i, xy[i], levels[i], future ? future->at(i) : xy[i]};
            seen[i] = 1;
        }
        std::function<Term(int)> visit = [&](int literal) -> Term
        {
            int id = literal / 2;
            if (!seen[id])
            {
                auto *o = Kit_DsdNtkObj(ntk, id);
                std::vector<Term> terms;
                for (int i = 0; i < int(o->nFans); ++i)
                    terms.push_back(visit(o->pFans[i]));
                Term value{-2, {0, 0}, 0};
                if (o->Type == KIT_DSD_VAR)
                    value = terms.at(0);
                else if (o->Type == KIT_DSD_AND || o->Type == KIT_DSD_XOR)
                {
                    while (terms.size() > 1)
                    {
                        // Group the inputs of a prospective multi-input AND
                        // cell, rather than optimizing wires that disappear
                        // inside that cell. Exact truth and live evaluation
                        // remain mandatory after this proposal heuristic.
                        if (cellArity > 2 && o->Type == KIT_DSD_AND && terms.size() > 2)
                        {
                            const int count = std::min(cellArity, int(terms.size()));
                            std::vector<int> group, bestGroup;
                            double best = INFINITY;
                            XY bestPos{}, bestFuture{};
                            auto geometry =
                                [&](const std::vector<int> &ids, bool forecast, XY &center)
                            {
                                XY r = forecast && futureAnchor ? *futureAnchor
                                       : anchor                 ? *anchor
                                                                : terms.back().pos;
                                std::vector<double> xs{r.x}, ys{r.y};
                                for (int id : ids)
                                {
                                    XY p = forecast ? terms[id].future : terms[id].pos;
                                    xs.push_back(p.x);
                                    ys.push_back(p.y);
                                }
                                std::sort(xs.begin(), xs.end());
                                std::sort(ys.begin(), ys.end());
                                center = {xs[xs.size() / 2], ys[ys.size() / 2]};
                                auto distance = [](XY a, XY b)
                                { return std::abs(a.x - b.x) + std::abs(a.y - b.y); };
                                double cost = distance(center, r);
                                for (int id : ids)
                                {
                                    XY p = forecast ? terms[id].future : terms[id].pos;
                                    cost += distance(p, center) - distance(p, r);
                                }
                                return cost;
                            };
                            auto choose = [&](auto &&self, int start) -> void
                            {
                                if (int(group.size()) == count)
                                {
                                    XY p, q;
                                    double cost = geometry(group, false, p);
                                    const double projected = geometry(group, true, q);
                                    if (future && futureAnchor)
                                        cost = std::max(cost, projected);
                                    if (cost < best)
                                    {
                                        best = cost;
                                        bestGroup = group;
                                        bestPos = p;
                                        bestFuture = q;
                                    }
                                    return;
                                }
                                for (int i = start;
                                     i <= int(terms.size()) - (count - int(group.size())); ++i)
                                {
                                    group.push_back(i);
                                    self(self, i + 1);
                                    group.pop_back();
                                }
                            };
                            choose(choose, 0);
                            std::vector<Term> cluster;
                            for (int i : bestGroup)
                                cluster.push_back(terms[i]);
                            while (cluster.size() > 1)
                            {
                                std::stable_sort(cluster.begin(), cluster.end(),
                                                 [](const Term &a, const Term &b)
                                                 { return a.level < b.level; });
                                auto a = cluster[0], b = cluster[1];
                                Term joined{e.land(a.lit, b.lit), bestPos,
                                            1 + std::max(a.level, b.level), bestFuture};
                                cluster.erase(cluster.begin(), cluster.begin() + 2);
                                cluster.push_back(joined);
                            }
                            for (auto i = bestGroup.rbegin(); i != bestGroup.rend(); ++i)
                                terms.erase(terms.begin() + *i);
                            terms.push_back(cluster[0]);
                            continue;
                        }
                        size_t ia = 0, ib = 1;
                        double best = INFINITY;
                        int bestHigh = INT_MAX, bestLow = INT_MAX;
                        for (size_t a = 0; a < terms.size(); ++a)
                            for (size_t b = a + 1; b < terms.size(); ++b)
                            {
                                double distance = std::abs(terms[a].pos.x - terms[b].pos.x) +
                                                  std::abs(terms[a].pos.y - terms[b].pos.y);
                                if (anchor)
                                {
                                    auto saving = [](XY a, XY b, XY r)
                                    {
                                        return std::max({a.x, b.x, r.x}) -
                                               std::min({a.x, b.x, r.x}) +
                                               std::max({a.y, b.y, r.y}) -
                                               std::min({a.y, b.y, r.y}) - std::abs(a.x - r.x) -
                                               std::abs(a.y - r.y) - std::abs(b.x - r.x) -
                                               std::abs(b.y - r.y);
                                    };
                                    distance = saving(terms[a].pos, terms[b].pos, *anchor);
                                    if (future && futureAnchor)
                                        distance = std::max(distance,
                                                            saving(terms[a].future, terms[b].future,
                                                                   *futureAnchor));
                                }
                                int high = std::max(terms[a].level, terms[b].level);
                                int low = std::min(terms[a].level, terms[b].level);
                                bool better = !balanced
                                                  ? distance < best
                                                  : high < bestHigh ||
                                                        (high == bestHigh &&
                                                         (low < bestLow ||
                                                          (low == bestLow && distance < best)));
                                if (better)
                                {
                                    best = distance;
                                    bestHigh = high;
                                    bestLow = low;
                                    ia = a;
                                    ib = b;
                                }
                            }
                        auto a = terms[ia], b = terms[ib];
                        int lit = o->Type == KIT_DSD_AND ? e.land(a.lit, b.lit)
                                                         : e.mux(a.lit, b.lit ^ 1, b.lit);
                        value = {lit,
                                 {(a.pos.x + b.pos.x) / 2, (a.pos.y + b.pos.y) / 2},
                                 std::max(a.level, b.level) + (o->Type == KIT_DSD_XOR ? 2 : 1),
                                 {(a.future.x + b.future.x) / 2, (a.future.y + b.future.y) / 2}};
                        if (anchor)
                        {
                            auto median = [](double a, double b, double c)
                            { return std::max(std::min(a, b), std::min(std::max(a, b), c)); };
                            value.pos = {median(a.pos.x, b.pos.x, anchor->x),
                                         median(a.pos.y, b.pos.y, anchor->y)};
                            const XY r = futureAnchor ? *futureAnchor : *anchor;
                            value.future = {median(a.future.x, b.future.x, r.x),
                                            median(a.future.y, b.future.y, r.y)};
                        }
                        terms.erase(terms.begin() + ib);
                        terms.erase(terms.begin() + ia);
                        terms.push_back(value);
                    }
                    value = terms.at(0);
                }
                else if (o->Type == KIT_DSD_PRIME)
                {
                    int count = o->nFans;
                    auto *tt = Kit_DsdObjTruth(o);
                    Truth t(tt, tt + Kit_TruthWordNum(count));
                    std::vector<int> order(count);
                    std::iota(order.begin(), order.end(), 0);
                    Expr prime(count);
                    if (!factor(prime, t, order))
                        std::abort();
                    if (primeFactory && count <= 4)
                    {
                        std::vector<XY> px;
                        std::vector<int> pl;
                        for (const auto &v : terms)
                        {
                            px.push_back(v.pos);
                            pl.push_back(v.level);
                        }
                        prime = primeFactory(t, prime, px, pl);
                    }
                    auto literalTerm = [&](int l)
                    {
                        if (l < 0)
                            return Term{l, {0, 0}, 0};
                        Term t = terms.at(l / 2);
                        t.lit ^= l & 1;
                        return t;
                    };
                    for (auto pair : prime.a)
                    {
                        auto a = literalTerm(pair.first), b = literalTerm(pair.second);
                        terms.push_back(
                            {e.land(a.lit, b.lit),
                             {(a.pos.x + b.pos.x) / 2, (a.pos.y + b.pos.y) / 2},
                             1 + std::max(a.level, b.level),
                             {(a.future.x + b.future.x) / 2, (a.future.y + b.future.y) / 2}});
                    }
                    value = literalTerm(prime.root);
                }
                else if (o->Type != KIT_DSD_CONST1)
                    std::abort();
                memo[id] = value;
                seen[id] = 1;
            }
            Term result = memo[id];
            result.lit ^= literal & 1;
            return result;
        };
        e.root = visit(ntk->Root).lit;
        return e;
    }
};
