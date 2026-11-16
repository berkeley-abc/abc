struct TgTensionItem
{
    int id = 0, count = 0;
    Box boxes[3];
};
static double TgTensionReference(const TgTensionItem &item)
{
    double result = 0;
    for (int axis = 0; axis < 2; ++axis)
    {
        std::array<double, 6> ends{};
        for (int k = 0; k < item.count; ++k)
        {
            auto b = axis ? item.boxes[k].y : item.boxes[k].x;
            ends[2 * k] = b.first;
            ends[2 * k + 1] = b.second;
        }
        if (!item.count)
            continue;
        std::sort(ends.begin(), ends.begin() + 2 * item.count);
        double center = ends[item.count - 1];
        for (int k = 0; k < item.count; ++k)
            result += dist(center, axis ? item.boxes[k].y : item.boxes[k].x);
    }
    return result;
}
static double TgTensionClosed(const TgTensionItem &item)
{
    double result = 0;
    for (int axis = 0; axis < 2; ++axis)
    {
        double lo = -INFINITY, hi = INFINITY;
        for (int k = 0; k < item.count; ++k)
        {
            auto b = axis ? item.boxes[k].y : item.boxes[k].x;
            lo = std::max(lo, b.first);
            hi = std::min(hi, b.second);
        }
        result += std::max(0.0, lo - hi);
    }
    return result;
}
#if defined(__clang__) || defined(__GNUC__)
using TgVec2 = double __attribute__((vector_size(16)));
static TgVec2 TgVMin(TgVec2 a, TgVec2 b)
{
    return a < b ? a : b;
}
static TgVec2 TgVMax(TgVec2 a, TgVec2 b)
{
    return a > b ? a : b;
}
static TgVec2 TgVPositive(TgVec2 a)
{
    return a > 0 ? a : TgVec2{0, 0};
}
static void TgTensionVector(const TgTensionItem *items, std::vector<double> &out, size_t begin,
                            size_t end, bool exact)
{
    size_t i = begin;
    for (; i + 1 < end; i += 2)
    {
        const auto &a = items[i];
        const auto &b = items[i + 1];
        TgVec2 result{0, 0};
        for (int axis = 0; axis < 2; ++axis)
        {
            TgVec2 lo[3], hi[3];
            for (int k = 0; k < 3; ++k)
            {
                auto x = k < a.count ? (axis ? a.boxes[k].y : a.boxes[k].x)
                                     : std::pair<double, double>{-INFINITY, INFINITY};
                auto y = k < b.count ? (axis ? b.boxes[k].y : b.boxes[k].x)
                                     : std::pair<double, double>{-INFINITY, INFINITY};
                lo[k] = TgVec2{x.first, y.first};
                hi[k] = TgVec2{x.second, y.second};
            }
            if (!exact)
            {
                result += TgVPositive(TgVMax(TgVMax(lo[0], lo[1]), lo[2]) -
                                      TgVMin(TgVMin(hi[0], hi[1]), hi[2]));
                continue;
            }
            TgVec2 e[6] = {lo[0], hi[0], lo[1], hi[1], lo[2], hi[2]};
            // Sort six endpoints. Missing intervals [-inf,+inf] move the legacy
            // (count-1)-th endpoint to index 2 without contributing distance.
            for (int phase = 0; phase < 6; ++phase)
                for (int k = phase % 2; k + 1 < 6; k += 2)
                {
                    TgVec2 x = e[k], y = e[k + 1];
                    e[k] = TgVMin(x, y);
                    e[k + 1] = TgVMax(x, y);
                }
            TgVec2 center = e[2];
            if (!a.count)
                center[0] = 0;
            if (!b.count)
                center[1] = 0;
            // Same per-node order as legacy: x0,x1,x2,y0,y1,y2. No fast-math.
            for (int k = 0; k < 3; ++k)
                result += TgVPositive(lo[k] - center) + TgVPositive(center - hi[k]);
        }
        out[a.id] = result[0];
        out[b.id] = result[1];
    }
    if (i < end)
        out[items[i].id] = exact ? TgTensionReference(items[i]) : TgTensionClosed(items[i]);
}
#else
static void TgTensionVector(const TgTensionItem *items, std::vector<double> &out, size_t begin,
                            size_t end, bool exact)
{
    for (size_t i = begin; i < end; ++i)
        out[items[i].id] = exact ? TgTensionReference(items[i]) : TgTensionClosed(items[i]);
}
#endif
static void TgTensionRun(const std::vector<TgTensionItem> &items, std::vector<double> &out,
                         int mode)
{
    if (mode < 2)
    {
        for (const auto &v : items)
            out[v.id] = mode == 0 ? TgTensionReference(v) : TgTensionClosed(v);
        return;
    }
    bool exact = mode == 2 || mode == 4;
    if (mode < 4 || items.size() < 32768)
    {
        TgTensionVector(items.data(), out, 0, items.size(), exact);
        return;
    }
    TgTensionVector(items.data(), out, 0, items.size(), exact);
}
