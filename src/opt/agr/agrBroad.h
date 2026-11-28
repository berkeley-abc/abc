/**CFile****************************************************************

  FileName    [agrBroad.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Adaptive geometric restructuring.]

  Synopsis    [Broad RS, RW and RF passes (part of agrBlock.cpp).]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: agrBroad.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

// RW allocates its work over ten priority groups of roots.

// Root filter of one broad pass: the selected roots and, for RW, the groups.
struct BroadFilter
{
    const std::vector<unsigned char> & selected;
    const std::vector<unsigned char> * group = nullptr;
    GroupFilter * groups = nullptr;
    std::vector<unsigned char> * attempted = nullptr;

    static int visit(void * pData, Abc_Obj_t * pRoot)
    {
        auto * f = static_cast<BroadFilter *>(pData);
        const int id = pRoot->Id;
        if ( id >= int(f->selected.size()) || !f->selected[id] )
            return 0;
        if ( f->groups && id < int(f->group->size()) )
        {
            const int g = (*f->group)[id];
            if ( g >= int(f->groups->closed.size()) || f->groups->closed[g] )
                return 0;
            (*f->attempted)[id] = 1;
        }
        return 1;
    }
    static void done(void * pData, Abc_Obj_t * pRoot, int fFound)
    {
        auto * f = static_cast<BroadFilter *>(pData);
        if ( f->groups && pRoot->Id < int(f->group->size()) )
            f->groups->record((*f->group)[pRoot->Id], fFound != 0);
    }
};

/**Function*************************************************************

  Synopsis    [Runs the broad RS, RW and RF passes over tension-selected roots.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int broadRound(Abc_Frame_t * frame)
{
    auto * n = Abc_FrameReadNtk(frame);
    if ( !n || !Pa_ManHasPlacement(n) )
        return 1;
    for ( int op : {AGR_RS, AGR_RW, AGR_RF} )
    {
        const int initialNodes = Abc_NtkNodeNum(n);
        auto & storage = blockState().scan;
        if ( !storage )
        {
            storage.reset(new TensionScan(n));
            storage->captureInputs(n);
        }
        else
            storage->refreshGeometry(n);
        auto & scan = *storage;
        scan.prepareOpportunities(n, &blockState().shapes);
        auto & history = blockState().broadHistory[op];
        history.prepare(n, scan);
        auto roots = scan.roots(n, 100, initialNodes, history.novelty, nullptr);
        history.prepareSelected(n, scan, roots);
        std::vector<std::array<int, 2>> before;
        for ( int id : roots )
        {
            auto * v = Abc_NtkObj(n, id);
            before.push_back({2 * Abc_ObjFaninId0(v) + Abc_ObjFaninC0(v), 2 * Abc_ObjFaninId1(v) + Abc_ObjFaninC1(v)});
        }
        std::vector<unsigned char> selected(Abc_NtkObjNumMax(n));
        for ( int id : roots )
            selected[id] = 1;
        BroadFilter filter{selected};
        std::vector<unsigned char> group, attempted;
        GroupFilter groups(10, .25);
        if ( op == AGR_RW )
        {
            group = rankGroups(n, scan, roots, 10);
            attempted.assign(Abc_NtkObjNumMax(n), 0);
            filter.group = &group;
            filter.groups = &groups;
            filter.attempted = &attempted;
        }
        Pa_Filter_t paFilter = {BroadFilter::visit, BroadFilter::done, &filter};
        Pa_ManSetPhysicalAreaGuard(0);
        Pa_ManSetTimingEvaluation(1);
        int ok = op == AGR_RW   ? Pa_NtkRewrite(n, &paFilter, 0)
                 : op == AGR_RF ? Pa_NtkRefactor(n, &paFilter, 0)
                                : Pa_NtkResubstitute(n, &paFilter, 0, 1);
        Pa_ManSetTimingEvaluation(0);
        if ( ok <= 0 )
            return 1;
        // RW observes only the roots it attempted.
        if ( op == AGR_RW )
        {
            std::vector<int> keptRoots;
            std::vector<std::array<int, 2>> keptBefore;
            for ( size_t i = 0; i < roots.size(); ++i )
                if ( attempted[roots[i]] )
                {
                    keptRoots.push_back(roots[i]);
                    keptBefore.push_back(before[i]);
                }
            roots.swap(keptRoots);
            before.swap(keptBefore);
        }
        for ( size_t i = 0; i < roots.size(); ++i )
        {
            auto * v = Abc_NtkObj(n, roots[i]);
            bool changed = !v || 2 * Abc_ObjFaninId0(v) + Abc_ObjFaninC0(v) != before[i][0] ||
                           2 * Abc_ObjFaninId1(v) + Abc_ObjFaninC1(v) != before[i][1];
            history.observe(roots[i], changed);
        }
        AGR_VERBOSE("agr: broad %s  roots = %d  nodes %d -> %d\n",
                    op == AGR_RS   ? "RS"
                    : op == AGR_RW ? "RW"
                                   : "RF",
                    int(roots.size()), initialNodes, Abc_NtkNodeNum(n));
    }
    return 0;
}
