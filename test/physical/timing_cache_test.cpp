// Compile this translation unit against libabc.a. Including the implementation
// exercises its private timing cache without adding a production test command.
#define Agr_ManReadObjectPosition TimingTest_ReadPosition
#define Agr_ManHasPlacement TimingTest_HasPlacement
#define Agr_ManIsPassActive TimingTest_IsPassActive
#ifndef AGR_EVALUATOR_SOURCE
#define AGR_EVALUATOR_SOURCE "../../src/ext-agr/agrEvaluate.cpp"
#endif
#include AGR_EVALUATOR_SOURCE
#undef Agr_ManReadObjectPosition
#undef Agr_ManHasPlacement
#undef Agr_ManIsPassActive

#include <cstdio>

static std::map<Abc_Obj_t *, std::pair<double, double>> positions;

extern "C" int TimingTest_ReadPosition(Abc_Ntk_t *, Abc_Obj_t *object, double *x, double *y)
{
    auto found = positions.find(object);
    if (found == positions.end())
        return 0;
    *x = found->second.first;
    *y = found->second.second;
    return 1;
}
extern "C" int TimingTest_HasPlacement(Abc_Ntk_t *network) { return network != nullptr; }
extern "C" int TimingTest_IsPassActive(Abc_Ntk_t *network) { return network != nullptr; }

static bool Update(AgrEval_TimingCache &cache, Abc_Ntk_t *network,
                   const std::vector<int> &moved, int originalCursor)
{
#ifdef AGR_TEST_ORIGINAL
    return cache.UpdateAfterLocalEdit(network, moved, {}, originalCursor, false);
#else
    (void)originalCursor;
    return cache.UpdateAfterLocalEdit(network, moved, {}, false);
#endif
}

static Abc_Ntk_t *Fixture(std::vector<Abc_Obj_t *> &nodes, bool reverseIds)
{
    positions.clear();
    Abc_Ntk_t *network = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    std::vector<Abc_Obj_t *> inputs;
    for (int i = 0; i < 8; ++i)
        inputs.push_back(Abc_NtkCreatePi(network));
    auto manager = static_cast<Abc_Aig_t *>(network->pManFunc);
    nodes.push_back(Abc_AigAnd(manager, inputs[0], inputs[1]));
    for (int i = 1; i < 6; ++i)
        nodes.push_back(Abc_AigAnd(manager, nodes.back(), inputs[i + 1]));
    const double xs[] = {0, 10, 5, 15, 0, 10};
    for (int i = 0; i < 6; ++i)
        positions[nodes[i]] = {xs[i], 0};
    if (reverseIds)
    {
        // The late object drives an older object, as happens after AIG edits.
        Abc_Obj_t *late = Abc_AigAnd(manager, nodes[0], inputs[7]);
        positions[late] = {3, 0};
        Abc_ObjPatchFanin(nodes[2], nodes[1], late);
        nodes.push_back(late);
    }
    Abc_ObjAddFanin(Abc_NtkCreatePo(network), nodes[5]);
    return network;
}

static bool SameArrivals(const AgrEval_TimingCache &cache, Abc_Ntk_t *network)
{
    AgrEval_TimingCache exact;
    if (!exact.Build(network))
        return false;
    Abc_Obj_t *object;
    int i;
    Abc_NtkForEachObj(network, object, i)
    {
        const auto &a = cache.nodes[object->Id].arrival;
        const auto &b = exact.nodes[object->Id].arrival;
        if (a.logic != b.logic || std::fabs(a.wire - b.wire) > 1e-12)
            return false;
    }
    return true;
}

static bool TinyArrivalChange()
{
    std::vector<Abc_Obj_t *> nodes;
    Abc_Ntk_t *network = Fixture(nodes, false);
    AgrEval_TimingCache cache;
    bool ok = cache.Build(network);
    positions[nodes[1]].first += 1e-6;
    ok = ok && Update(cache, network, {nodes[1]->Id}, ABC_INFINITY);
    ok = ok && SameArrivals(cache, network);
    Abc_NtkDelete(network);
    return ok;
}

static bool AllocationOrderIsNotTopology()
{
    std::vector<Abc_Obj_t *> nodes;
    Abc_Ntk_t *network = Fixture(nodes, true);
    AgrEval_TimingCache cache;
    bool ok = nodes[6]->Id > nodes[2]->Id && cache.Build(network);
    positions[nodes[0]].first += 1;
    ok = ok && Update(cache, network, {nodes[0]->Id}, nodes[0]->Id);
    ok = ok && SameArrivals(cache, network);
    Abc_NtkDelete(network);
    return ok;
}

static bool UnconstrainedScore()
{
    double inf = std::numeric_limits<double>::infinity();
#ifdef AGR_TEST_ORIGINAL
    auto Potential = [](double slack) { return slack > 0 ? std::log1p(slack) : slack; };
    return std::isfinite(Potential(inf) - Potential(inf));
#else
    return AgrEval_SlackPotentialDelta(inf, inf) == 0 &&
           AgrEval_SlackPotentialDelta(-1, -2) == -1 &&
           std::fabs(AgrEval_SlackPotentialDelta(0, 1) - std::log(2.0)) < 1e-15 &&
           std::isnan(AgrEval_SlackPotentialDelta(inf, 0)) &&
           std::isnan(AgrEval_SlackPotentialDelta(std::numeric_limits<double>::quiet_NaN(), 0));
#endif
}

int main()
{
    Abc_Start();
    int failed = 0;
    for (auto check : {std::make_pair("unconstrained_score", UnconstrainedScore),
                       std::make_pair("small_arrival_fanout", TinyArrivalChange),
                       std::make_pair("allocation_order", AllocationOrderIsNotTopology)})
    {
        bool ok = check.second();
        std::printf("%s: %s\n", check.first, ok ? "passed" : "FAILED");
        failed += !ok;
    }
    Abc_Stop();
    return failed != 0;
}
