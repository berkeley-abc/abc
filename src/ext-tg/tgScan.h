// Included inside SparseScan. Exact reuse is scoped to one command, before
// object-ID reassignment. Inspect every live/dead slot for changed fanins and
// coordinates, then rebuild only affected driver boxes and node tensions.
std::vector<std::array<int, 2>> previousInputs;
std::vector<unsigned char> previousKinds;
std::vector<unsigned> scanNetStamp, scanRootStamp, scanPinStamp;
unsigned scanEpoch = 0, scanPinEpoch = 0;
void captureInputs(Abc_Ntk_t *n)
{
    const int size = Abc_NtkObjNumMax(n);
    previousInputs.assign(size, {-1, -1});
    previousKinds.assign(size, 0);
    Abc_Obj_t *v;
    int i;
    Abc_NtkForEachObj(n, v, i)
    {
        previousKinds[v->Id] = Abc_ObjIsNode(v) ? 1 : Abc_ObjIsCi(v) ? 2 : Abc_ObjIsCo(v) ? 3 : 0;
        if (Abc_ObjIsNode(v) || Abc_ObjIsCo(v))
            for (int j = 0; j < Abc_ObjFaninNum(v) && j < 2; ++j)
                previousInputs[v->Id][j] = 2 * Abc_ObjFanin(v, j)->Id + Abc_ObjFaninC(v, j);
    }
}
void refreshGeometry(Abc_Ntk_t *n)
{
    const int size = Abc_NtkObjNumMax(n);
    if (size < int(previousInputs.size()) || 0)
        std::abort();
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
    if (++scanEpoch == 0)
    {
        std::fill(scanNetStamp.begin(), scanNetStamp.end(), 0);
        std::fill(scanRootStamp.begin(), scanRootStamp.end(), 0);
        scanEpoch = 1;
    }
    std::vector<int> drivers;
    auto mark = [&](int id)
    {
        if (id >= 0 && scanNetStamp[id] != scanEpoch)
        {
            scanNetStamp[id] = scanEpoch;
            drivers.push_back(id);
        }
    };
    for (int id = 0; id < size; ++id)
    {
        auto *v = Abc_NtkObj(n, id);
        unsigned char kind = v ? (Abc_ObjIsNode(v) ? 1
                                  : Abc_ObjIsCi(v) ? 2
                                  : Abc_ObjIsCo(v) ? 3
                                                   : 0)
                               : 0;
        std::array<int, 2> inputs{{-1, -1}};
        if (kind == 1 || kind == 3)
            for (int j = 0; j < Abc_ObjFaninNum(v) && j < 2; ++j)
                inputs[j] = 2 * Abc_ObjFanin(v, j)->Id + Abc_ObjFaninC(v, j);
        XY point;
        unsigned char has = kind == 1 ? Tg_ManReadObjectPosition(n, v, &point.x, &point.y) : 0;
        if (kind != previousKinds[id] || inputs != previousInputs[id] || has != present[id] ||
            point.x != pos[id].x || point.y != pos[id].y)
        {
            mark(id);
            for (int input : previousInputs[id])
                if (input >= 0)
                    mark(input / 2);
            for (int input : inputs)
                if (input >= 0)
                    mark(input / 2);
        }
        previousInputs[id] = inputs;
        previousKinds[id] = kind;
        present[id] = has;
        pos[id] = point;
        if (kind != 1)
            tension[id] = 0;
    }
    std::vector<int> roots;
    auto root = [&](Abc_Obj_t *v)
    {
        if (v && Abc_ObjIsNode(v) && scanRootStamp[v->Id] != scanEpoch)
        {
            scanRootStamp[v->Id] = scanEpoch;
            roots.push_back(v->Id);
        }
    };
    for (int id : drivers)
    {
        nets[id] = Net{};
        auto *v = Abc_NtkObj(n, id);
        if (!v || (!Abc_ObjIsNode(v) && !Abc_ObjIsCi(v)))
            continue;
        if (++scanPinEpoch == 0)
        {
            std::fill(scanPinStamp.begin(), scanPinStamp.end(), 0);
            scanPinEpoch = 1;
        }
        auto &net = nets[id];
        auto add = [&](int pin)
        {
            if (!present[pin] || scanPinStamp[pin] == scanPinEpoch)
                return;
            scanPinStamp[pin] = scanPinEpoch;
            ++net.count;
            net.x.add(pos[pin].x);
            net.y.add(pos[pin].y);
        };
        add(id);
        root(v);
        Abc_Obj_t *fo;
        int j;
        Abc_ObjForEachFanout(v, fo, j)
        {
            add(fo->Id);
            root(fo);
        }
    }
    TgTensionItem pair[2];
    size_t filled = 0;
    for (int id : roots)
    {
        auto *v = Abc_NtkObj(n, id);
        auto &item = pair[filled];
        item = TgTensionItem{};
        item.id = id;
        int ds[3] = {id, Abc_ObjFaninId0(v), Abc_ObjFaninId1(v)};
        for (int k = 0; k < 3; ++k)
        {
            bool duplicate = false;
            for (int j = 0; j < k; ++j)
                duplicate |= ds[k] == ds[j];
            const auto &net = nets[ds[k]];
            if (duplicate || net.count < 2)
                continue;
            item.boxes[item.count++] = {net.x.without(pos[id].x), net.y.without(pos[id].y)};
        }
        if (++filled == 2)
        {
            TgTensionVector(pair, tension, 0, 2, true);
            filled = 0;
        }
    }
    if (filled)
        TgTensionVector(pair, tension, 0, filled, true);
    basePriority = tension;
    Abc_Obj_t *v;
    int vi;
    Abc_NtkForEachNode(n, v, vi) for (int k = 0; k < 2; ++k)
    {
        auto *u = Abc_ObjFanin(v, k);
        if (Abc_ObjIsNode(u) && Abc_ObjFanoutNum(u) == 1)
            basePriority[v->Id] += .5 * tension[u->Id];
    }
    opportunity.clear();
    shapes.clear();
}
