// Construct an eight-input cut by internalizing long removable connections.
struct GeometryCut
{
    std::vector<int> leaves, inside;
};
static GeometryCut geometryCut(Abc_Ntk_t *n, Abc_Obj_t *root)
{
    constexpr int mode = 1, limit = 8;
    GeometryCut cut;
    cut.inside.push_back(root->Id);
    std::map<int, int> frontier{{Abc_ObjFaninId0(root), 1}, {Abc_ObjFaninId1(root), 1}};
    for (int step = 0; step < (((23))); ++step)
    {
        int winner = -1;
        double best = -1;
        std::map<int, int> chosen;
        for (auto item : frontier)
        {
            auto *v = Abc_NtkObj(n, item.first);
            if (!Abc_ObjIsNode(v) || Abc_AigNodeIsConst(v) || item.second >= (((6))))
                continue;
            bool removable = true;
            Abc_Obj_t *fo;
            int j;
            Abc_ObjForEachFanout(v, fo, j) if (std::find(cut.inside.begin(), cut.inside.end(),
                                                         fo->Id) == cut.inside.end())
            {
                removable = false;
                break;
            }
            if (!removable)
                continue;
            auto next = frontier;
            next.erase(v->Id);
            for (int k = 0; k < 2; ++k)
            {
                const int id = Abc_ObjFanin(v, k)->Id;
                if (std::find(cut.inside.begin(), cut.inside.end(), id) != cut.inside.end())
                    continue;
                auto it = next.find(id);
                if (it == next.end())
                    next[id] = item.second + 1;
                else
                    it->second = std::min(it->second, item.second + 1);
            }
            if (next.size() > size_t(limit))
                continue;
            double x = 0, y = 0, span = 0;
            const bool placed = mode && Tg_ManReadObjectPosition(n, v, &x, &y);

            if (placed)
                Abc_ObjForEachFanout(v, fo, j)
                {
                    double fx = 0, fy = 0;
                    if (!Tg_ManReadObjectPosition(n, fo, &fx, &fy))
                        continue;
                    double wire = std::abs(fx - x) + std::abs(fy - y);

                    span += wire;
                }
            // Prefer internalizing long connections per newly consumed input.
            const double score =
                (span / (1. + std::max(0, int(next.size()) - int(frontier.size()))));
            if (score > best)
            {
                best = score;
                winner = v->Id;
                chosen = std::move(next);
            }
        }
        if (winner < 0)
            break;
        cut.inside.push_back(winner);
        frontier = std::move(chosen);
    }
    for (auto item : frontier)
        cut.leaves.push_back(item.first);
    return cut;
}
