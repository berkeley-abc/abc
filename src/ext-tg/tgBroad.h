static const int *coVisitIds = nullptr;
static int coVisitSize = -1, coEmptyVisit = 0;
extern "C" const int *Tg_ReadVisitOrder(int *count)
{
    *count = coVisitSize;
    return coVisitSize < 0 ? nullptr : coVisitSize ? coVisitIds : &coEmptyVisit;
}
extern "C" void Tg_SetVisitOrder(const int *order, int count)
{
    coVisitIds = order;
    coVisitSize = count;
}
extern "C" int Tg_NtkNativeRegionResubstitute(Abc_Ntk_t *, int, int, int, const unsigned char *,
                                              int);
static int coStandardPassDepth = 0;
struct CoStandardPassScope
{
    CoStandardPassScope()
    {
        ++coStandardPassDepth;
    }
    ~CoStandardPassScope()
    {
        --coStandardPassDepth;
    }
};
extern "C" void Tg_RwSetMask(const unsigned char *, int);
extern "C";
extern "C";
extern "C" void Tg_RwSetBuckets(const unsigned char *, int, int, double, unsigned char *);
extern "C" int Tg_RwBucketStats(int *);
extern "C";
extern "C";
extern "C" void Tg_RfSetMask(const unsigned char *, int);
// Run the broad RS/RW/RF passes. Root masks preserve ABC visitation order;
// the RW filter allocates work using tension-ranked productivity buckets.
int broadRound(Abc_Frame_t *frame)
{
    auto *n = Abc_FrameReadNtk(frame);
    if (!n || !Tg_InFlight() || !Tg_ManHasPlacement(n))
        return 1;
    static int epoch = -1;
    static TgOpportunityMemory memory[3];
    if (epoch != Tg_Epoch())
    {
        for (auto &m : memory)
            m = TgOpportunityMemory{};
        epoch = Tg_Epoch();
    }
    for (int op : {4, 1, 2})
    {
        const auto start = Abc_Clock();
        const int initialNodes = Abc_NtkNodeNum(n), slot = op == 4 ? 2 : op - 1;
        auto &storage = CoSparseShared().scan;
        if (!storage)
        {
            storage.reset(new SparseScan(n));
            storage->captureInputs(n);
        }
        else
            storage->refreshGeometry(n);
        auto &scan = *storage;
        scan.prepareOpportunities(n, true, true, &CoSparseShared().shapes);
        auto &mem = memory[slot];
        mem.enabled = true;
        mem.prepare(n, scan, op == 1, true);
        scan.actionPriority.clear();
        auto roots = scan.roots(n, 100, initialNodes, false, true, false, 0, nullptr, "diverse",
                                nullptr, &mem.novelty, false, nullptr, nullptr, false);
        mem.prepareSelected(n, scan, roots);
        std::vector<std::array<int, 2>> before;
        for (int id : roots)
        {
            auto *v = Abc_NtkObj(n, id);
            before.push_back({2 * Abc_ObjFaninId0(v) + Abc_ObjFaninC0(v),
                              2 * Abc_ObjFaninId1(v) + Abc_ObjFaninC1(v)});
        }
        std::vector<unsigned char> mask(Abc_NtkObjNumMax(n));
        for (int id : roots)
            mask[id] = 1;
        double hpwl = 0, area = 0;
        Tg_ManReadMetrics(n, &hpwl, nullptr, nullptr, &area);
        CoStandardPassScope standardPassScope;
        TgEval_ManConfigure(0, 0, hpwl, area);
        TgEval_ManSetTimingEvaluation(1);
        TgEval_ManSetClusterEvaluation(0);
        TgEval_ManSetBalancedRefactor(0);
        TgEval_ManSetTimingEffort(0);
        TgEval_ManSetScoreMode(2);
        TgEval_ManSetTimingWeight(.5);
        std::vector<unsigned char> bucket, attempted;
        constexpr int buckets = 10;
        if (op == 1)
        {
            std::vector<std::pair<double, int>> ranked;
            for (int id : roots)
                ranked.push_back({scan.rootPriority(n, id), id});
            std::sort(ranked.begin(), ranked.end(), [](const auto &a, const auto &b)
                      { return a.first != b.first ? a.first > b.first : a.second < b.second; });
            bucket.assign(Abc_NtkObjNumMax(n), 255);
            attempted.assign(Abc_NtkObjNumMax(n), 0);
            for (size_t r = 0; r < ranked.size(); ++r)
                bucket[ranked[r].second] = (unsigned char)std::min<size_t>(
                    buckets - 1, r * buckets / std::max<size_t>(1, ranked.size()));
            Tg_RwSetBuckets(bucket.data(), int(bucket.size()), buckets, .25, attempted.data());
            Tg_RwSetMask(mask.data(), int(mask.size()));
        }
        else if (op == 2)
            Tg_RfSetMask(mask.data(), int(mask.size()));
        int ok = op == 1 ? TgEval_NtkRewrite(n, 1, 0, 0, 0, 1)
                 : op == 2
                     ? TgEval_NtkRefactorPhysical(n, 10, 0, 16, 1, 0, 0, 0)
                     : Tg_NtkNativeRegionResubstitute(n, 8, 2, 0, mask.data(), int(mask.size()));
        Tg_SetVisitOrder(nullptr, -1);
        if (!bucket.empty())
        {
            int closed = 0;
            const int skipped = Tg_RwBucketStats(&closed);
            TG_VERBOSE("TG_RW_FILTER roots=%d skipped=%d closed_buckets=%d buckets=%d\n",
                       int(roots.size()), skipped, closed, buckets);
            std::vector<int> keptRoots;
            std::vector<std::array<int, 2>> keptBefore;
            for (size_t i = 0; i < roots.size(); ++i)
                if (roots[i] < int(attempted.size()) && attempted[roots[i]])
                {
                    keptRoots.push_back(roots[i]);
                    keptBefore.push_back(before[i]);
                }
            roots.swap(keptRoots);
            before.swap(keptBefore);
            Tg_RwSetBuckets(nullptr, 0, 0, 0, nullptr);
        }
        Tg_RwSetMask(nullptr, 0);
        Tg_RfSetMask(nullptr, 0);
        TgEval_ManPrintEffort();
        TgEval_ManSetTimingEvaluation(0);
        TgEval_ManSetTimingEffort(0);
        TgEval_ManSetScoreMode(0);
        if (ok <= 0)
            return 1;
        for (size_t i = 0; i < roots.size(); ++i)
        {
            auto *v = Abc_NtkObj(n, roots[i]);
            bool changed = !v || 2 * Abc_ObjFaninId0(v) + Abc_ObjFaninC0(v) != before[i][0] ||
                           2 * Abc_ObjFaninId1(v) + Abc_ObjFaninC1(v) != before[i][1];
            mem.observe(roots[i], changed, 1);
        }
        TG_VERBOSE("TG_BROAD operator=%d selected=%d initial_nodes=%d nodes=%d cpu_seconds=%.9f\n",
                   op, int(roots.size()), initialNodes, Abc_NtkNodeNum(n),
                   double(Abc_Clock() - start) / CLOCKS_PER_SEC);
    }
    return 0;
}
