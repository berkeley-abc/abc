// Retain whole-pass alternatives from one AGR invocation, merge them as
// structural choices, then select by the cost of the common plain-AIG mapper.
// All graphs are private. The user's &-space and fraig_store are untouched.
#ifndef ABC__ext_agr__agrChoices_h
#define ABC__ext_agr__agrChoices_h

#include "aig/aig/aig.h"
#include "aig/gia/gia.h"
#include "map/scl/sclLib.h"
#include "map/scl/sclSize.h"
#include "map/if/if.h"
#include "misc/util/utilNam.h"
#include "opt/dau/dau.h"
#include "opt/sfm/sfm.h"
#include "proof/fraig/fraig.h"
#include "proof/dch/dch.h"
#include <ctime>

ABC_NAMESPACE_IMPL_START

extern "C" {
Abc_Ntk_t *Abc_NtkFraigPartitioned(Vec_Ptr_t *, void *);
Aig_Man_t *Abc_NtkToDarChoices(Abc_Ntk_t *);
Gia_Man_t *Gia_ManFromAig(Aig_Man_t *);
Gia_Man_t *Gia_ManFromAigChoices(Aig_Man_t *);
Aig_Man_t *Gia_ManToAig(Gia_Man_t *, int);
Abc_Ntk_t *Abc_NtkFromAigPhase(Aig_Man_t *);
Gia_Man_t *Gia_ManLutBalance(Gia_Man_t *, int, int, int, int, int);
Gia_Man_t *Gia_ManPerformMfs(Gia_Man_t *, Sfm_Par_t *);
void Nf_ManSetDefaultPars(Jf_Par_t *);
Gia_Man_t *Nf_ManPerformMappingWithLib(Gia_Man_t *, Jf_Par_t *, Mio_Library_t *);
Abc_Ntk_t *Abc_NtkFromCellMappedGia(Gia_Man_t *, int);
int Abc_NtkResubstitute(Abc_Ntk_t *, int, int, int, int, int, int, int, int, int);
Aig_Man_t *Gia_ManToAigSkip(Gia_Man_t *, int);
Vec_Ptr_t *Gia_ManOrderPios(Aig_Man_t *, Gia_Man_t *);
}

namespace {

struct AgrChoiceNtkDelete { void operator()(Abc_Ntk_t *p) const { if (p) Abc_NtkDelete(p); } };
struct AgrChoiceGiaDelete { void operator()(Gia_Man_t *p) const { if (p) Gia_ManStop(p); } };
struct AgrChoiceAigDelete { void operator()(Aig_Man_t *p) const { if (p) Aig_ManStop(p); } };
using AgrChoiceNtk = std::unique_ptr<Abc_Ntk_t, AgrChoiceNtkDelete>;
using AgrChoiceGia = std::unique_ptr<Gia_Man_t, AgrChoiceGiaDelete>;
using AgrChoiceAig = std::unique_ptr<Aig_Man_t, AgrChoiceAigDelete>;

struct AgrChoiceCost
{
    double area = INFINITY, delay = INFINITY;
    bool Valid() const { return std::isfinite(area) && std::isfinite(delay) && area >= 0 && delay >= 0; }
};

static AgrChoiceGia AgrChoiceToGia(Abc_Ntk_t *network)
{
    const bool choices = Abc_NtkGetChoiceNum(network) != 0;
    auto *aig = choices ? Abc_NtkToDarChoices(network) : Abc_NtkToDar(network, 0, 1);
    if (!aig) return {};
    AgrChoiceGia gia(choices ? Gia_ManFromAigChoices(aig) : Gia_ManFromAig(aig));
    Aig_ManStop(aig);
    return gia;
}

struct AgrChoiceMapping
{
    AgrChoiceGia gia;
    AgrChoiceNtk network;
    AgrChoiceCost cost;
};

// Equivalent to &nf -R <relax>; &put; stime. Never updates the global frame.
static AgrChoiceMapping AgrChoiceMap(Gia_Man_t *input, int relax)
{
    AgrChoiceMapping result;
    auto *library = static_cast<Mio_Library_t *>(Abc_FrameReadLibGen());
    auto *scl = static_cast<SC_Lib *>(Abc_FrameReadLibScl());
    if (!input || !library || !scl) return result;
    AgrChoiceGia copy(Gia_ManDupWithAttributes(input));
    Jf_Par_t parameters;
    Nf_ManSetDefaultPars(&parameters);
    parameters.nRelaxRatio = relax;
    auto *mapped = Nf_ManPerformMappingWithLib(copy.get(), &parameters, library);
    if (!mapped) return result;
    if (mapped == copy.get()) copy.release();
    result.gia.reset(mapped);
    if (!Gia_ManHasCellMapping(mapped)) return result;
    result.network.reset(Abc_NtkFromCellMappedGia(mapped, 0));
    if (!result.network) return result;
    auto *timing = Abc_SclManStart(scl, result.network.get(), 0, 1, 0, 0);
    if (timing)
    {
        result.cost = {timing->SumArea0, timing->MaxDelay0};
        Abc_SclManFree(timing);
    }
    return result;
}

class AgrChoiceSession
{
    std::vector<AgrChoiceNtk> snapshots;
    std::vector<std::string> labels;
    bool enabled;
    bool failed = false;

    // The standard compress2rs sequence on a private network. The -l
    // switches disable level preservation, matching the public ABC script.
    // No command interpreter, current network or user-owned store is used.
    static AgrChoiceNtk Compress(Abc_Ntk_t *source)
    {
        AgrChoiceNtk network(Abc_NtkDup(source));
        if (!network) return {};
        auto balance = [&]()
        {
            auto *next = Abc_NtkBalance(network.get(), 0, 0, 0);
            if (!next) return false;
            network.reset(next);
            return true;
        };
        auto resub = [&](int cut, int nodes)
        { return Abc_NtkResubstitute(network.get(), cut, nodes, 1, 0, 0, 0, 0, 0, 0) > 0; };
        auto rewrite = [&](int zeros)
        { return Abc_NtkRewrite(network.get(), 0, zeros, 0, 0, 0) > 0; };
        auto refactor = [&](int zeros)
        { return Abc_NtkRefactor(network.get(), 10, zeros ? 0 : 1, 16, 0, zeros, 0, 0) > 0; };
        if (!balance() || !resub(6, 1) || !rewrite(0) || !resub(6, 2) ||
            !refactor(0) || !resub(8, 1) || !balance() || !resub(8, 2) ||
            !rewrite(0) || !resub(10, 1) || !rewrite(1) || !resub(10, 2) ||
            !balance() || !resub(12, 1) || !refactor(1) || !resub(12, 2) ||
            !rewrite(1) || !balance()) return {};
        return network;
    }

    void AddCompression()
    {
        auto *anchor = snapshots.front().get();
        for (int round = 1; round <= 2; ++round)
        {
            auto compressed = Compress(anchor);
            if (!compressed) break;
            anchor = compressed.get();
            snapshots.push_back(std::move(compressed));
            labels.push_back("input_compress2rs_" + std::to_string(round));
        }
        const size_t count = snapshots.size();
        for (size_t i = 0; i < count; ++i)
            if (labels[i] == "input_mfs_fx" || labels[i] == "agr_mfs_fx")
            {
                auto compressed = Compress(snapshots[i].get());
                if (!compressed) continue;
                snapshots.push_back(std::move(compressed));
                labels.push_back(labels[i] + "_compress2rs");
            }
    }

    static void CopyNames(Abc_Ntk_t *source, Abc_Ntk_t *target)
    {
        Nm_ManFree(target->pManName);
        target->pManName = Nm_ManCreate(Abc_NtkCiNum(target) + Abc_NtkCoNum(target));
        Abc_Obj_t *object; int i;
        Abc_NtkForEachCi(target, object, i)
            Abc_ObjAssignName(object, Abc_ObjName(Abc_NtkCi(source, i)), nullptr);
        Abc_NtkForEachCo(target, object, i)
            Abc_ObjAssignName(object, Abc_ObjName(Abc_NtkCo(source, i)), nullptr);
        ABC_FREE(target->pName); target->pName = Abc_UtilStrsav(source->pName);
        ABC_FREE(target->pSpec); target->pSpec = Abc_UtilStrsav(source->pSpec);
    }

    void Diversify(Abc_Ntk_t *source, const std::string &prefix, bool verbose)
    {
        // Fixed, design-independent family; each transform starts from the
        // same anchor. LUT don't-care resynthesis is bounded by window size
        // and SAT conflicts. The final selector may reject every alternative.
        for (int method = 0; method < 5; ++method)
        {
            const std::clock_t start = std::clock();
            if (verbose)
            {
                Abc_Print(1, "AGR_CHOICE_STAGE anchor=%s method=%d status=started\n", prefix.c_str(), method);
                fflush(stdout);
            }
            auto input = AgrChoiceToGia(source);
            if (!input) continue;
            AgrChoiceGia variant;
            const char *name = nullptr;
            if (method == 0)
            {
                variant.reset(Gia_ManAreaBalance(input.get(), 0, ABC_INFINITY, 0, 0));
                name = "balance";
            }
            else if (method == 1)
            {
                variant.reset(Gia_ManLutBalance(input.get(), 6, 1, 1, 1, 0));
                name = "lut_balance";
            }
            else if (method == 2)
            {
                variant.reset(Gia_ManPerformDsdBalance(input.get(), 6, 8, 0, 0));
                name = "dsd_balance";
            }
            else if (method == 3)
            {
                variant.reset(Gia_ManPerformSopBalance(input.get(), 16, 0, 0));
                name = "sop_balance";
            }
            else
            {
                If_Par_t lutParameters;
                Gia_ManSetIfParsDefault(&lutParameters);
                lutParameters.nLutSize = 6;
                lutParameters.pLutLib = nullptr;
                lutParameters.pCellLib = nullptr;
                AgrChoiceGia mapped(Gia_ManPerformMapping(input.get(), &lutParameters));
                if (!mapped || !Gia_ManHasMapping(mapped.get())) continue;
                Sfm_Par_t parameters;
                Sfm_ParSetDefault(&parameters);
                parameters.nTfoLevMax = 4;
                parameters.nDepthMax = 100;
                parameters.nWinSizeMax = 1000;
                parameters.nBTLimit = 20000;
                parameters.nGrowthLevel = 1;
                parameters.fMoreEffort = 1;
                AgrChoiceGia optimized(Gia_ManPerformMfs(mapped.get(), &parameters));
                if (!optimized || !Gia_ManHasMapping(optimized.get())) continue;
                AgrChoiceGia factored(Gia_ManPerformFx(optimized.get(), 1000000, 0, 0, 0, 0));
                if (!factored) continue;
                // &fx returns a plain AIG, not another LUT-mapped graph.
                // Match &st's unmapped branch rather than dropping it.
                variant.reset(Gia_ManRehash(factored.get(), 0));
                name = "mfs_fx";
            }
            if (!variant) continue;
            if (variant.get() == input.get()) input.release();
            auto *aig = Gia_ManToAig(variant.get(), 0);
            if (!aig) continue;
            AgrChoiceNtk network(Abc_NtkFromAigPhase(aig));
            Aig_ManStop(aig);
            if (!network || Abc_NtkCiNum(network.get()) != Abc_NtkCiNum(source) ||
                Abc_NtkCoNum(network.get()) != Abc_NtkCoNum(source)) continue;
            CopyNames(source, network.get());
            snapshots.push_back(std::move(network));
            labels.push_back(prefix + name);
            if (verbose)
            {
                Abc_Print(1, "AGR_CHOICE_STAGE anchor=%s method=%d status=complete cpu_seconds=%.6f\n",
                          prefix.c_str(), method, double(std::clock() - start) / CLOCKS_PER_SEC);
                fflush(stdout);
            }
        }
    }

    // Mapping every raw alternative remains useful, but a costly choice merge
    // need not include a graph that is worse in both measured objectives.
    // Keep the input and plain AGR as anchors, and spread at most six other
    // contributors across the area/delay frontier. This bound is independent
    // of the benchmark identity and uses no placement or routed metrics.
    std::vector<size_t> Contributors(const std::vector<AgrChoiceCost> &costs, bool filter) const
    {
        std::vector<size_t> selected, frontier;
        for (size_t i = 0; i < snapshots.size(); ++i)
        {
            if (!filter) { selected.push_back(i); continue; }
            if (!costs[i].Valid()) continue;
            bool dominated = false;
            for (size_t j = 0; j < snapshots.size(); ++j)
                if (i != j && costs[j].Valid() && costs[j].area <= costs[i].area &&
                    costs[j].delay <= costs[i].delay &&
                    (costs[j].area < costs[i].area || costs[j].delay < costs[i].delay || j < i))
                { dominated = true; break; }
            if (!dominated && i != 0 && i + 1 != snapshots.size()) frontier.push_back(i);
        }
        if (!filter) return selected;
        selected = {0, snapshots.size() - 1};
        std::sort(frontier.begin(), frontier.end(), [&](size_t a, size_t b)
        {
            if (costs[a].delay != costs[b].delay) return costs[a].delay < costs[b].delay;
            if (costs[a].area != costs[b].area) return costs[a].area < costs[b].area;
            return a < b;
        });
        if (frontier.size() <= 6) selected.insert(selected.end(), frontier.begin(), frontier.end());
        else for (size_t i = 0; i < 6; ++i) selected.push_back(frontier[i * (frontier.size() - 1) / 5]);
        std::sort(selected.begin(), selected.end());
        selected.erase(std::unique(selected.begin(), selected.end()), selected.end());
        return selected;
    }

    AgrChoiceGia MergeDch(int conflicts, const std::vector<size_t> &contributors)
    {
        // Same construction as Gia_ManCreateChoicesArray, with explicit
        // conflict limits and ownership of every temporary AIG/GIA.
        std::vector<AgrChoiceGia> graphs;
        graphs.push_back(AgrChoiceToGia(snapshots.back().get()));
        for (size_t i : contributors)
            if (i + 1 < snapshots.size()) graphs.push_back(AgrChoiceToGia(snapshots[i].get()));
        for (const auto &graph : graphs) if (!graph) return {};
        auto *array = Vec_PtrAlloc(int(graphs.size()));
        for (const auto &graph : graphs) Vec_PtrPush(array, graph.get());
        AgrChoiceGia miter(Gia_ManChoiceMiter(array));
        Vec_PtrFree(array);
        if (!miter) return {};
        AgrChoiceAig aig(Gia_ManToAigSkip(miter.get(), int(graphs.size())));
        if (!aig) return {};
        Dch_Pars_t parameters;
        Dch_ManSetDefaultParams(&parameters);
        parameters.fSynthesis = 0;
        parameters.nBTLimit = conflicts;
        AgrChoiceAig choices(Dch_ComputeChoices(aig.get(), &parameters));
        if (!choices) return {};
        auto *order = Gia_ManOrderPios(choices.get(), graphs.front().get());
        if (!order) return {};
        AgrChoiceAig ordered(Aig_ManDupDfsGuided(choices.get(), order));
        Vec_PtrFree(order);
        if (!ordered) return {};
        return AgrChoiceGia(Gia_ManFromAigChoices(ordered.get()));
    }

    AgrChoiceNtk Merge(int conflicts, const std::vector<size_t> &contributors)
    {
        auto *store = Vec_PtrAlloc(int(contributors.size()));
        // Match fraig_restore's preference for the final synthesis endpoint.
        Vec_PtrPush(store, snapshots.back().get());
        for (size_t i : contributors)
            if (i && i + 1 < snapshots.size()) Vec_PtrPush(store, snapshots[i].get());
        if (snapshots.size() > 1) Vec_PtrPush(store, snapshots.front().get());
        Fraig_Params_t parameters;
        Fraig_ParamsSetDefault(&parameters);
        const int objects = Abc_NtkNodeNum(snapshots.back().get()) + Abc_NtkCiNum(snapshots.back().get());
        parameters.nPatsRand = parameters.nPatsDyna = std::max(1, std::min(32, (1 << 27) / std::max(1, objects))) * 32;
        parameters.nBTLimit = conflicts;
        parameters.fFuncRed = parameters.fFeedBack = parameters.fDist1Pats = 1;
        parameters.fDoSparse = parameters.fChoicing = parameters.fInternal = 1;
        parameters.fTryProve = parameters.fVerbose = 0;
        // The partitioner changes only the progressbar flag in the frame.
        auto *frame = Abc_FrameGetGlobalFrame();
        const char *flag = Cmd_FlagReadByName(frame, const_cast<char *>("progressbar"));
        const bool hadFlag = flag != nullptr;
        const std::string oldFlag = flag ? flag : "";
        AgrChoiceNtk merged(Abc_NtkFraigPartitioned(store, &parameters));
        if (hadFlag)
            Cmd_FlagUpdateValue(frame, const_cast<char *>("progressbar"), const_cast<char *>(oldFlag.c_str()));
        else
            Cmd_FlagDeleteByName(frame, const_cast<char *>("progressbar"));
        Vec_PtrFree(store);
        return merged;
    }

public:
    explicit AgrChoiceSession(bool active) : enabled(active) {}

    void Capture(Abc_Ntk_t *network)
    {
        if (!enabled || failed) return;
        AgrChoiceNtk copy(Abc_NtkStrash(network, 0, 1, 0));
        if (!copy) { failed = true; return; }
        labels.push_back("checkpoint_" + std::to_string(snapshots.size()));
        snapshots.push_back(std::move(copy));
    }

    Abc_Ntk_t *Finish(Abc_Ntk_t *baseline, double delayGain, bool diverse, bool compress, int conflicts, bool filter, bool modern, double delayWeight, bool verbose)
    {
        if (!enabled || failed || snapshots.empty()) return nullptr;
        const std::clock_t start = std::clock();
        auto initialGia = AgrChoiceToGia(baseline);
        auto initial = AgrChoiceMap(initialGia.get(), 0);
        if (!initial.cost.Valid()) return nullptr;
        if (diverse)
        {
            Diversify(snapshots.front().get(), "input_", verbose);
            Diversify(baseline, "agr_", verbose);
            Capture(baseline); // Keep plain AGR as the preferred primary AIG.
        }
        const double target = initial.cost.delay * (1.0 - delayGain / 100.0);
        AgrChoiceCost bestCost = initial.cost;
        AgrChoiceNtk best(Abc_NtkStrash(baseline, 0, 1, 0));
        std::string bestLabel = "plain_agr";
        int candidates = 1;
        auto consider = [&](AgrChoiceNtk candidate, AgrChoiceCost cost, const std::string &label)
        {
            if (!candidate || !cost.Valid()) return;
            ++candidates;
            // A positive weight trades a small area difference for a useful
            // delay reduction. At the default zero delay-gain target, both
            // metrics are guarded against the plain AGR endpoint.
            auto feasibleCost = [&](AgrChoiceCost c)
            { return c.delay <= target && (delayWeight == 0 || delayGain > 0 || c.area <= initial.cost.area); };
            auto objective = [&](AgrChoiceCost c)
            { return std::log(std::max(c.area, 1e-20)) + delayWeight * std::log(std::max(c.delay, 1e-20)); };
            const bool feasible = feasibleCost(cost);
            const bool bestFeasible = feasibleCost(bestCost);
            const double score = objective(cost), bestScore = objective(bestCost);
            const bool areaBetter = cost.area < bestCost.area || (cost.area == bestCost.area && cost.delay < bestCost.delay);
            const bool better = feasible != bestFeasible ? feasible :
                feasible ? (delayWeight == 0 ? areaBetter : (score < bestScore || (score == bestScore && areaBetter))) :
                           (cost.delay < bestCost.delay || (cost.delay == bestCost.delay && cost.area < bestCost.area));
            if (verbose)
                Abc_Print(1, "AGR_CHOICE_CANDIDATE name=%s area=%.9g delay=%.9g feasible=%d\n",
                          label.c_str(), cost.area, cost.delay, int(feasible));
            if (better) { best = std::move(candidate); bestCost = cost; bestLabel = label; }
        };
        int choiceNodes = 0;
        std::vector<AgrChoiceCost> costs;
        for (int bank = 0; bank < (compress ? 2 : 1); ++bank)
        {
            const size_t previousCount = bank ? snapshots.size() : 0;
            if (bank)
            {
                AddCompression();
                Capture(baseline);
            }
            costs.resize(snapshots.size());
            for (size_t i = previousCount; i < snapshots.size(); ++i)
            {
                auto gia = AgrChoiceToGia(snapshots[i].get());
                auto mapped = AgrChoiceMap(gia.get(), 0);
                costs[i] = mapped.cost;
                consider(AgrChoiceNtk(Abc_NtkStrash(snapshots[i].get(), 0, 1, 0)), mapped.cost,
                         labels[i]);
            }
            auto contributors = Contributors(costs, filter);
            if (verbose)
            {
                Abc_Print(1, "AGR_CHOICE_STAGE bank=%d merge=started snapshots=%d contributors=%d\n",
                          bank, int(snapshots.size()), int(contributors.size()));
                fflush(stdout);
            }
            AgrChoiceGia choices;
            if (modern) choices = MergeDch(conflicts, contributors);
            else
            {
                auto merged = Merge(conflicts, contributors);
                if (merged) choices = AgrChoiceToGia(merged.get());
            }
            if (!choices) continue;
            choiceNodes = std::max(choiceNodes, Gia_ManChoiceNum(choices.get()));
            if (verbose)
            {
                Abc_Print(1, "AGR_CHOICE_STAGE bank=%d merge=complete choice_nodes=%d\n", bank, Gia_ManChoiceNum(choices.get()));
                fflush(stdout);
            }
            for (int independent = 0; independent < 2; ++independent)
            {
                AgrChoiceGia current(Gia_ManDupWithAttributes(choices.get()));
                for (int relax : {0, 5, 10, 20, 40, 100})
                {
                    auto shaped = AgrChoiceMap(independent ? choices.get() : current.get(), relax);
                    if (!shaped.network) break;
                    AgrChoiceNtk endpoint(Abc_NtkStrash(shaped.network.get(), 0, 1, 0));
                    if (!endpoint) break;
                    auto gia = AgrChoiceToGia(endpoint.get());
                    auto remapped = AgrChoiceMap(gia.get(), 0);
                    if (!remapped.cost.Valid()) break;
                    consider(std::move(endpoint), remapped.cost,
                             std::string(bank ? "compressed_" : "") +
                             (independent ? "independent_R" : "sequential_R") + std::to_string(relax));
                    current = std::move(remapped.gia);
                }
            }
        }
        if (!best) return nullptr;
        // Mapping creates generic terminal names; restore the caller's names
        // by position, preserving the combinational PI/PO ordering contract.
        CopyNames(baseline, best.get());
        Abc_Print(1, "AGR_CHOICES snapshots=%d choice_nodes=%d candidates=%d selected=%s "
                     "base_area=%.9g base_delay=%.9g area=%.9g delay=%.9g target=%.9g cpu_seconds=%.6f sat_conflicts=%d engine=%s delay_weight=%.6g\n",
                  int(snapshots.size()), choiceNodes, candidates, bestLabel.c_str(), initial.cost.area,
                  initial.cost.delay, bestCost.area, bestCost.delay, target,
                  double(std::clock() - start) / CLOCKS_PER_SEC, conflicts, modern ? "dch" : "fraig", delayWeight);
        return best.release();
    }
};

static AgrChoiceSession *s_ChoiceSession = nullptr;

} // namespace

extern "C" void Agr_ChoiceCheckpoint(Abc_Ntk_t *network)
{
    if (s_ChoiceSession) s_ChoiceSession->Capture(network);
}

ABC_NAMESPACE_IMPL_END

#endif
