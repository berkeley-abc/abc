/* Ranking memory only. No cached candidate validity, scores, or Boolean proofs.
 * Stable object-generation identities survive ABC ID reassignment. Context hash collisions affect
 * priority, never correctness. Quantized geometry reactivates changed neighborhoods. */
struct AgrOpportunityMemory
{
    struct Entry
    {
        uint64_t context = 0, structure = 0, pairs = 0;
        int attempts = 0, accepted = 0;
        std::array<double, 21> geometry{};
    };
    struct Class
    {
        double attempts = 0, accepted = 0, work = 0, gain = 0;
    };
    struct Identity
    {
        int id;
        uint64_t uid;
    };
    std::unordered_map<Abc_Obj_t *, Identity> identities;
    uint64_t nextUid = 1;
    void rebind(Abc_Ntk_t *n, bool afterRenumber)
    {
        Abc_Obj_t *o;
        int i;
        if (afterRenumber)
        {
            Abc_NtkForEachObj(n, o, i)
            {
                auto it = identities.find(o);
                if (it == identities.end())
                    std::abort();
                it->second.id = o->Id;
            }
            return;
        }
        // A recycled ABC object address has a newly appended ID before
        // reassignment. Drop dead addresses before IDs are compacted/reused.
        std::unordered_map<Abc_Obj_t *, Identity> live;
        live.reserve(Abc_NtkObjNum(n));
        Abc_NtkForEachObj(n, o, i)
        {
            auto it = identities.find(o);
            live.emplace(o, it != identities.end() && it->second.id == o->Id
                                ? it->second
                                : Identity{o->Id, nextUid++});
        }
        identities.swap(live);
    }
    std::unordered_map<uint64_t, Entry> history;
    std::unordered_map<unsigned, Class> classes;
    std::vector<uint64_t> keys, contexts;
    std::vector<unsigned> shapes;
    std::vector<unsigned char> seen, same;
    std::vector<double> utility, novelty;
    // Optional coupled-placement history. Keep topology and continuous relative
    // geometry separate: a rigid translation must not erase failed-search history.
    static constexpr int geometryHistory = 0;
    static constexpr int geometryEvent = 0;
    std::vector<uint64_t> pairMasks;
    long pairEvents = 0;
    std::vector<uint64_t> structures;
    std::vector<std::array<double, 21>> geometries;
    long geometryStable = 0, geometryPartial = 0, geometryReset = 0, structureReset = 0;
    bool enabled = false;
    std::vector<double> cachedPressure;
    double cachedBx = 0, cachedBy = 0;
    int cachedBins = 0;
    long attempts = 0, fresh = 0, changed = 0, repeated = 0, successes = 0;
    static uint64_t mix(uint64_t a, uint64_t b)
    {
        b += 0x9e3779b97f4a7c15ULL;
        b = (b ^ (b >> 30)) * 0xbf58476d1ce4e5b9ULL;
        b = (b ^ (b >> 27)) * 0x94d049bb133111ebULL;
        return (a ^ ((b ^ (b >> 31)) + (a << 6) + (a >> 2))) * 0x9e3779b97f4a7c15ULL;
    }

    uint64_t contextFor(Abc_Obj_t *o, const SparseScan &scan, const std::vector<double> &pressure,
                        double bx, double by, int bins) const
    {

        const int id = o->Id;
        auto quant = [](double x, double step)
        { return uint64_t(int64_t(std::llround(x / std::max(1e-6, step)))); };
        uint64_t context = mix(Abc_ObjFanoutNum(o), o->Level);
        // Bounded local topology; upstream edits outside this region do
        // not erase history merely because a distant cone hash changed.
        Abc_Obj_t *queue[15];
        int depth[15];
        queue[0] = o;
        depth[0] = 0;
        int end = 1;
        for (int at = 0; at < end; ++at)
        {
            auto *v = queue[at];
            context = mix(context, keys[v->Id]);
            if (!Abc_ObjIsNode(v) || depth[at] >= 3)
                continue;
            context = mix(context, Abc_ObjFanoutNum(v));
            context = mix(context, Abc_ObjFaninC0(v) + 2 * Abc_ObjFaninC1(v));
            for (int k = 0; k < 2; ++k)
            {
                queue[end] = Abc_ObjFanin(v, k);
                depth[end++] = depth[at] + 1;
            }
        }
        uint64_t fanouts = 0;
        Abc_Obj_t *fo;
        int fi;
        Abc_ObjForEachFanout(o, fo, fi) fanouts += mix(91, keys[fo->Id]);
        context = mix(context, fanouts);
        for (int netId : {id, Abc_ObjFaninId0(o), Abc_ObjFaninId1(o)})
        {
            const auto &net = scan.nets[netId];
            context = mix(context, net.count);
            if (net.count)
                for (auto value : {quant(net.x.lo, bx / 8), quant(net.x.hi, bx / 8),
                                   quant(net.y.lo, by / 8), quant(net.y.hi, by / 8)})
                    context = mix(context, value);
        }
        context = mix(context, quant(scan.pos[id].x, bx / 8));
        context = mix(context, quant(scan.pos[id].y, by / 8));
        int cx = std::max(0, std::min(bins - 1, int(scan.pos[id].x / bx)));
        int cy = std::max(0, std::min(bins - 1, int(scan.pos[id].y / by)));
        for (int dx = -1; dx <= 1; ++dx)
            for (int dy = -1; dy <= 1; ++dy)
            {
                int x = std::max(0, std::min(bins - 1, cx + dx)),
                    y = std::max(0, std::min(bins - 1, cy + dy));
                context = mix(context, quant(pressure[x * bins + y], 1.0 / 16));
            }
        return context;
    }
    void prepareSelected(Abc_Ntk_t *n, const SparseScan &scan, const std::vector<int> &roots)
    {
        for (int id : roots)
            if (!seen[id])
            {
                contexts[id] = contextFor(Abc_NtkObj(n, id), scan, cachedPressure, cachedBx,
                                          cachedBy, cachedBins);
                shapes[id] = scan.shape(id);
            }
    }
    void prepare(Abc_Ntk_t *n, const SparseScan &scan, bool rw, bool diverseOnly = false)
    {
        int size = Abc_NtkObjNumMax(n);
        const size_t oldSize = keys.size();
        if (diverseOnly)
            keys.resize(size, 0);
        else
            keys.assign(size, 0);
        contexts.resize(size);
        shapes.resize(size);
        seen.assign(size, 0);
        same.assign(size, 0);
        utility.assign(size, 0);
        novelty.assign(size, 1);

        Abc_Obj_t *o;
        int i;
        if (diverseOnly)
        {
            // Sparse RF never reassigns object IDs inside a command. New IDs
            // append; assign exactly the UIDs that the generic live map would
            // assign, without rebuilding that map for every existing node.
            if (size_t(size) < oldSize)
                std::abort();
            for (size_t id = oldSize; id < size_t(size); ++id)
                if (Abc_NtkObj(n, int(id)))
                    keys[id] = nextUid++;
        }
        else
        {
            rebind(n, false);
            Abc_NtkForEachObj(n, o, i) keys[o->Id] = identities.at(o).uid;
        }
        double width, height, bx, by;
        int bins;
        if (!Agr_ManReadCanvas(n, &width, &height, &bins, &bx, &by))
            std::abort();
        // Read the authoritative PA density grid under a temporary read-only
        // pass when RW is between passes, avoiding repeated full fingerprints.
        bool own = !Agr_ManIsPassActive(n);
        if (own && !Agr_ManBeginPass(n))
            std::abort();
        std::vector<double> pressure(bins * bins);
        for (int x = 0; x < bins; ++x)
            for (int y = 0; y < bins; ++y)
            {
                double cells = 0, target = 0;
                if (!Agr_ManReadDensityBin(n, x, y, &cells, &target))
                    std::abort();
                pressure[x * bins + y] = cells / std::max(1e-9, target);
            }
        if (own && !Agr_ManEndPass(n))
            std::abort();
        if (diverseOnly)
        {
            cachedPressure = pressure;
            cachedBx = bx;
            cachedBy = by;
            cachedBins = bins;
        }
        double mean = 0;
        int count = 0;
        if (!diverseOnly)
        {
            Abc_NtkForEachNode(n, o, i)
            {
                mean += scan.basePriority[o->Id];
                ++count;
            }
        }
        mean /= std::max(1, count);
        Abc_NtkForEachNode(n, o, i)
        {
            int id = o->Id;
            if (diverseOnly && history.find(keys[id]) == history.end())
                continue;
            SparseScan::Opportunity unused;
            const auto &f = diverseOnly ? unused : scan.opportunity[id];
            shapes[id] = scan.shape(id);
            const uint64_t context = contextFor(o, scan, pressure, bx, by, bins);
            contexts[id] = context;
            auto it = history.find(keys[id]);
            seen[id] = it != history.end();
            same[id] = seen[id] && it->second.context == context;

            if (diverseOnly)
            {
                novelty[id] = enabled && same[id] ? (it->second.accepted ? .25 : .05) : 1;
                continue;
            }
            // Cheap operator-specific prior, followed by observed class success
            // and deterministic work counts. Wall-clock timing never affects rank.
            double potential = rw ? 1 + std::min(3, f.repeats) + .25 * std::max(0, f.internals - 2)
                                  : 1 + .5 * f.repeats + .5 * f.associative;
            double geometry = 1 + std::min(4.0, scan.basePriority[id] / std::max(1e-9, mean));
            double success = .5, cost = 1;
            auto ci = classes.find(f.shape);
            if (enabled && ci != classes.end())
            {
                success = (2 + ci->second.accepted) / (4 + ci->second.attempts);
                cost = 1 + .1 * ci->second.work / (4 + ci->second.attempts);
            }
            double noveltyWeight = enabled && same[id] ? (it->second.accepted ? .25 : .05) : 1;
            novelty[id] = noveltyWeight;
            utility[id] = potential * geometry * success * noveltyWeight / cost;
        }
    }
    // Logical-only preparation: no canvas, density, coordinate or HPWL reads.

    void observe(int id, bool accepted, int work)
    {
        if (id < 0 || id >= int(keys.size()))
            return;
        ++attempts;
        successes += accepted;
        if (!seen[id])
            ++fresh;
        else if (!same[id])
            ++changed;
        else
            ++repeated;
        // Retain observations in the disabled control too; only ranking uses enabled.
        auto &e = history[keys[id]];
        e.context = contexts[id];
        ++e.attempts;
        e.accepted = int(accepted);

        auto &c = classes[shapes[id]];
        ++c.attempts;
        c.accepted += accepted;
        c.work += std::max(1, work);
    }
    void print(int round) const
    {
        AGR_VERBOSE("AGR_OPPORTUNITY round=%d memory=%d attempts=%ld fresh=%ld changed=%ld "
                   "repeated=%ld accepted=%ld entries=%d classes=%d\n",
                   round, int(enabled), attempts, fresh, changed, repeated, successes,
                   int(history.size()), int(classes.size()));
        printGeometry();
    }
    void printGeometry() const {}
};
