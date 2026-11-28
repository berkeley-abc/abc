/**CFile****************************************************************

  FileName    [agrHistory.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [Root priority from earlier attempts (part of agrBlock.cpp).]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrHistory.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// Ranking memory only. No cached candidate validity, scores, or Boolean proofs.
// Stable object-generation identities survive ABC ID reassignment. Context hash collisions affect
// priority, never correctness. Quantized geometry reactivates changed neighborhoods.
struct RootHistory
{
    struct Entry
    {
        uint64_t context = 0;
        int accepted = 0; // the last attempt was accepted
    };
    struct Class
    {
        double attempts = 0, gain = 0;
    };
    uint64_t nextUid = 1;
    std::unordered_map<uint64_t, Entry> history;
    std::unordered_map<unsigned, Class> classes;
    std::vector<uint64_t> keys, contexts;
    std::vector<unsigned> shapes;
    std::vector<unsigned char> seen;
    std::vector<double> novelty;
    std::vector<double> cachedPressure;
    double cachedBx = 0, cachedBy = 0;
    int cachedBins = 0;
    static uint64_t mix(uint64_t a, uint64_t b)
    {
        b += 0x9e3779b97f4a7c15ULL;
        b = (b ^ (b >> 30)) * 0xbf58476d1ce4e5b9ULL;
        b = (b ^ (b >> 27)) * 0x94d049bb133111ebULL;
        return (a ^ ((b ^ (b >> 31)) + (a << 6) + (a >> 2))) * 0x9e3779b97f4a7c15ULL;
    }

    uint64_t contextFor(Abc_Obj_t * o, const TensionScan & scan, const std::vector<double> & pressure, double bx,
                        double by, int bins) const
    {

        const int id = o->Id;
        auto quant = [](double x, double step) { return uint64_t(int64_t(std::llround(x / std::max(1e-6, step)))); };
        uint64_t context = mix(Abc_ObjFanoutNum(o), o->Level);
        // Bounded local topology; upstream edits outside this region do
        // not erase history merely because a distant cone hash changed.
        Abc_Obj_t * queue[15];
        int depth[15];
        queue[0] = o;
        depth[0] = 0;
        int end = 1;
        for ( int at = 0; at < end; ++at )
        {
            auto * v = queue[at];
            context = mix(context, keys[v->Id]);
            if ( !Abc_ObjIsNode(v) || depth[at] >= 3 )
                continue;
            context = mix(context, Abc_ObjFanoutNum(v));
            context = mix(context, Abc_ObjFaninC0(v) + 2 * Abc_ObjFaninC1(v));
            for ( int k = 0; k < 2; ++k )
            {
                queue[end] = Abc_ObjFanin(v, k);
                depth[end++] = depth[at] + 1;
            }
        }
        uint64_t fanouts = 0;
        Abc_Obj_t * fo;
        int fi;
        Abc_ObjForEachFanout(o, fo, fi) fanouts += mix(91, keys[fo->Id]);
        context = mix(context, fanouts);
        for ( int netId : {id, Abc_ObjFaninId0(o), Abc_ObjFaninId1(o)} )
        {
            const auto & net = scan.nets[netId];
            context = mix(context, net.count);
            if ( net.count )
                for ( auto value : {quant(net.x.lo, bx / 8), quant(net.x.hi, bx / 8), quant(net.y.lo, by / 8),
                                    quant(net.y.hi, by / 8)} )
                    context = mix(context, value);
        }
        context = mix(context, quant(scan.pos[id].x, bx / 8));
        context = mix(context, quant(scan.pos[id].y, by / 8));
        int cx = std::max(0, std::min(bins - 1, int(scan.pos[id].x / bx)));
        int cy = std::max(0, std::min(bins - 1, int(scan.pos[id].y / by)));
        for ( int dx = -1; dx <= 1; ++dx )
            for ( int dy = -1; dy <= 1; ++dy )
            {
                int x = std::max(0, std::min(bins - 1, cx + dx)), y = std::max(0, std::min(bins - 1, cy + dy));
                context = mix(context, quant(pressure[x * bins + y], 1.0 / 16));
            }
        return context;
    }
    void prepareSelected(Abc_Ntk_t * n, const TensionScan & scan, const std::vector<int> & roots)
    {
        for ( int id : roots )
            if ( !seen[id] )
            {
                contexts[id] = contextFor(Abc_NtkObj(n, id), scan, cachedPressure, cachedBx, cachedBy, cachedBins);
                shapes[id] = scan.shapes[id];
            }
    }
    // Object IDs only append inside a command: new objects get new identities.
    // A root whose history entry saw the same local context is deprioritized.
    void prepare(Abc_Ntk_t * n, const TensionScan & scan)
    {
        int size = Abc_NtkObjNumMax(n);
        const size_t oldSize = keys.size();
        assert(size_t(size) >= oldSize);
        keys.resize(size, 0);
        contexts.resize(size);
        shapes.resize(size);
        seen.assign(size, 0);
        novelty.assign(size, 1);
        for ( size_t id = oldSize; id < size_t(size); ++id )
            if ( Abc_NtkObj(n, int(id)) )
                keys[id] = nextUid++;
        double width, height, bx, by;
        int bins;
        if ( !Pa_ManReadCanvas(n, &width, &height, &bins, &bx, &by) )
            assert(!"no placement canvas");
        // Read the authoritative density grid under a temporary read-only
        // pass when RW is between passes, avoiding repeated full fingerprints.
        bool own = !Pa_ManIsPassActive(n);
        if ( own && !Pa_ManBeginPass(n) )
            assert(!"placement pass rejected");
        std::vector<double> pressure(bins * bins);
        for ( int x = 0; x < bins; ++x )
            for ( int y = 0; y < bins; ++y )
            {
                double cells = 0, target = 0;
                if ( !Pa_ManReadDensityBin(n, x, y, &cells, &target) )
                    assert(!"no density bin");
                pressure[x * bins + y] = cells / std::max(1e-9, target);
            }
        if ( own && !Pa_ManEndPass(n) )
            assert(!"placement pass rejected");
        cachedPressure = pressure;
        cachedBx = bx;
        cachedBy = by;
        cachedBins = bins;
        Abc_Obj_t * o;
        int i;
        Abc_NtkForEachNode(n, o, i)
        {
            int id = o->Id;
            auto it = history.find(keys[id]);
            if ( it == history.end() )
                continue;
            shapes[id] = scan.shapes[id];
            const uint64_t context = contextFor(o, scan, pressure, bx, by, bins);
            contexts[id] = context;
            seen[id] = 1;
            novelty[id] = it->second.context == context ? (it->second.accepted ? .25 : .05) : 1;
        }
    }

    void observe(int id, bool accepted)
    {
        if ( id < 0 || id >= int(keys.size()) )
            return;
        auto & e = history[keys[id]];
        e.context = contexts[id];
        e.accepted = int(accepted);
        ++classes[shapes[id]].attempts;
    }
};
