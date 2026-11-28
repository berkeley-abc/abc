/**CFile****************************************************************

  FileName    [agrGeometryCut.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [Geometry-shaped cuts (part of agrBlock.cpp).]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrGeometryCut.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// An eight-input cut that internalizes long removable connections; it grows
// by at most 23 nodes within depth 6 of the root.
struct GeometryCut
{
    std::vector<int> leaves, inside;
};
/**Function*************************************************************

  Synopsis    [Builds an eight-input cut that internalizes long connections.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static GeometryCut geometryCut(Abc_Ntk_t * n, Abc_Obj_t * root)
{
    constexpr int limit = 8, steps = 23, depth = 6;
    GeometryCut cut;
    cut.inside.push_back(root->Id);
    std::map<int, int> frontier{{Abc_ObjFaninId0(root), 1}, {Abc_ObjFaninId1(root), 1}};
    for ( int step = 0; step < steps; ++step )
    {
        int winner = -1;
        double best = -1;
        std::map<int, int> chosen;
        for ( auto item : frontier )
        {
            auto * v = Abc_NtkObj(n, item.first);
            if ( !Abc_ObjIsNode(v) || Abc_AigNodeIsConst(v) || item.second >= depth )
                continue;
            bool removable = true;
            Abc_Obj_t * fo;
            int j;
            Abc_ObjForEachFanout(v, fo,
                                 j) if ( std::find(cut.inside.begin(), cut.inside.end(), fo->Id) == cut.inside.end() )
            {
                removable = false;
                break;
            }
            if ( !removable )
                continue;
            auto next = frontier;
            next.erase(v->Id);
            for ( int k = 0; k < 2; ++k )
            {
                const int id = Abc_ObjFanin(v, k)->Id;
                if ( std::find(cut.inside.begin(), cut.inside.end(), id) != cut.inside.end() )
                    continue;
                auto it = next.find(id);
                if ( it == next.end() )
                    next[id] = item.second + 1;
                else
                    it->second = std::min(it->second, item.second + 1);
            }
            if ( next.size() > size_t(limit) )
                continue;
            double x = 0, y = 0, span = 0;
            const bool placed = Pa_ManReadObjectPosition(n, v, &x, &y);
            if ( placed )
                Abc_ObjForEachFanout(v, fo, j)
                {
                    double fx = 0, fy = 0;
                    if ( !Pa_ManReadObjectPosition(n, fo, &fx, &fy) )
                        continue;
                    span += std::abs(fx - x) + std::abs(fy - y);
                }
            // Prefer internalizing long connections per newly consumed input.
            const double score = (span / (1. + std::max(0, int(next.size()) - int(frontier.size()))));
            if ( score > best )
            {
                best = score;
                winner = v->Id;
                chosen = std::move(next);
            }
        }
        if ( winner < 0 )
            break;
        cut.inside.push_back(winner);
        frontier = std::move(chosen);
    }
    for ( auto item : frontier )
        cut.leaves.push_back(item.first);
    return cut;
}
