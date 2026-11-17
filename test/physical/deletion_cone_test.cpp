// Exercise the planner's deletion boundary against ABC's actual replacement.
// No placement objective or benchmark-specific decision enters this test.
#ifndef AGR_EVALUATOR_SOURCE
#define AGR_EVALUATOR_SOURCE "../../src/ext-agr/agrEvaluate.cpp"
#endif
#include AGR_EVALUATOR_SOURCE

static bool Check(int mode)
{
    Abc_Ntk_t *network = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    auto *manager = static_cast<Abc_Aig_t *>(network->pManFunc);
    Abc_Obj_t *a = Abc_NtkCreatePi(network), *b = Abc_NtkCreatePi(network);
    Abc_Obj_t *c = Abc_NtkCreatePi(network);
    Abc_Obj_t *ab = Abc_AigAnd(manager, a, b);
    Abc_Obj_t *abc = Abc_AigAnd(manager, ab, c);
    // This root is constant zero; a cut at abc must not stop its deletion.
    Abc_Obj_t *root = mode < 2 ? Abc_AigAnd(manager, abc, Abc_ObjNot(a)) : abc;
    Abc_ObjAddFanin(Abc_NtkCreatePo(network), root);
    if (mode == 1) Abc_ObjAddFanin(Abc_NtkCreatePo(network), ab);
    std::vector<int> oldIds;
    Abc_Obj_t *object; int i;
    Abc_NtkForEachNode(network, object, i) oldIds.push_back(object->Id);
    std::unordered_map<Abc_Obj_t *, int> added;
    // The reassociation in mode 2 creates references only to PIs; mode 3
    // keeps ab alive as a new gate's input. Both replace an internal root.
    if (mode == 3) added[ab] = 1;
    if (mode == 4) added[ab] = Abc_ObjFanoutNum(root);
    auto predicted = AgrEval_DeletionCone(root, added);
    std::set<int> removed;
    for (auto *node : predicted) removed.insert(node->Id);
    const size_t expected[] = {3, 2, 2, 1, 1};
    bool ok = removed.size() == expected[mode];
    Abc_Obj_t *replacement = Abc_ObjNot(Abc_AigConst1(network));
    if (mode == 2) replacement = Abc_AigAnd(manager, a, Abc_AigAnd(manager, b, c));
    // The fourth case tests the mutator's reference accounting only.
    if (mode == 3) replacement = Abc_AigAnd(manager, ab, Abc_ObjNot(c));
    if (mode == 4) replacement = ab;
    ok = Abc_AigReplace(manager, root, replacement, 0) && ok;
    for (int id : oldIds)
        ok = (bool(removed.count(id)) == (Abc_NtkObj(network, id) == nullptr)) && ok;
    Abc_NtkDelete(network);
    return ok;
}

int main()
{
    Abc_Start();
    int failed = 0;
    const char *names[] = {"unused_cut_leaf", "shared_boundary", "reassociated_cone", "new_reference", "reused_result"};
    for (int i = 0; i < 5; ++i)
    {
        bool ok = Check(i);
        std::printf("%s: %s\n", names[i], ok ? "passed" : "FAILED");
        failed += !ok;
    }
    Abc_Stop();
    return failed != 0;
}
