struct AgrTensionItem
{
    int id = 0, count = 0;
    Box boxes[3];
};
static double AgrTensionReference(const AgrTensionItem &item)
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
static double AgrTensionClosed(const AgrTensionItem &item)
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
using AgrVec2 = double __attribute__((vector_size(16)));
static AgrVec2 AgrVMin(AgrVec2 a, AgrVec2 b)
{
    return a < b ? a : b;
}
static AgrVec2 AgrVMax(AgrVec2 a, AgrVec2 b)
{
    return a > b ? a : b;
}
static AgrVec2 AgrVPositive(AgrVec2 a)
{
    return a > 0 ? a : AgrVec2{0, 0};
}
static void AgrTensionVector(const AgrTensionItem *items, std::vector<double> &out, size_t begin,
                            size_t end, bool exact)
{
    size_t i = begin;
    for (; i + 1 < end; i += 2)
    {
        const auto &a = items[i];
        const auto &b = items[i + 1];
        AgrVec2 result{0, 0};
        for (int axis = 0; axis < 2; ++axis)
        {
            AgrVec2 lo[3], hi[3];
            for (int k = 0; k < 3; ++k)
            {
                auto x = k < a.count ? (axis ? a.boxes[k].y : a.boxes[k].x)
                                     : std::pair<double, double>{-INFINITY, INFINITY};
                auto y = k < b.count ? (axis ? b.boxes[k].y : b.boxes[k].x)
                                     : std::pair<double, double>{-INFINITY, INFINITY};
                lo[k] = AgrVec2{x.first, y.first};
                hi[k] = AgrVec2{x.second, y.second};
            }
            if (!exact)
            {
                result += AgrVPositive(AgrVMax(AgrVMax(lo[0], lo[1]), lo[2]) -
                                      AgrVMin(AgrVMin(hi[0], hi[1]), hi[2]));
                continue;
            }
            AgrVec2 e[6] = {lo[0], hi[0], lo[1], hi[1], lo[2], hi[2]};
            // Sort six endpoints. Missing intervals [-inf,+inf] move the legacy
            // (count-1)-th endpoint to index 2 without contributing distance.
            for (int phase = 0; phase < 6; ++phase)
                for (int k = phase % 2; k + 1 < 6; k += 2)
                {
                    AgrVec2 x = e[k], y = e[k + 1];
                    e[k] = AgrVMin(x, y);
                    e[k + 1] = AgrVMax(x, y);
                }
            AgrVec2 center = e[2];
            if (!a.count)
                center[0] = 0;
            if (!b.count)
                center[1] = 0;
            // Same per-node order as legacy: x0,x1,x2,y0,y1,y2. No fast-math.
            for (int k = 0; k < 3; ++k)
                result += AgrVPositive(lo[k] - center) + AgrVPositive(center - hi[k]);
        }
        out[a.id] = result[0];
        out[b.id] = result[1];
    }
    if (i < end)
        out[items[i].id] = exact ? AgrTensionReference(items[i]) : AgrTensionClosed(items[i]);
}
#else
static void AgrTensionVector(const AgrTensionItem *items, std::vector<double> &out, size_t begin,
                            size_t end, bool exact)
{
    for (size_t i = begin; i < end; ++i)
        out[items[i].id] = exact ? AgrTensionReference(items[i]) : AgrTensionClosed(items[i]);
}
#endif
static void AgrTensionRun(const std::vector<AgrTensionItem> &items, std::vector<double> &out,
                         int mode)
{
    if (mode < 2)
    {
        for (const auto &v : items)
            out[v.id] = mode == 0 ? AgrTensionReference(v) : AgrTensionClosed(v);
        return;
    }
    bool exact = mode == 2 || mode == 4;
    if (mode < 4 || items.size() < 32768)
    {
        AgrTensionVector(items.data(), out, 0, items.size(), exact);
        return;
    }
    AgrTensionVector(items.data(), out, 0, items.size(), exact);
}
