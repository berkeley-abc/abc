#include "psfmImpl.hpp"
#include <algorithm>

extern "C" {
    Sfm_Ntk_t* Abc_NtkExtractMfs(Abc_Ntk_t* pNtk, int nFirstFixed);
    Sfm_Ntk_t* Abc_NtkExtractMfs2(Abc_Ntk_t* pNtk, int pivot);
    Sfm_Ntk_t* Gia_ManExtractMfs(Gia_Man_t* p);
} // extern "C"

namespace EfxAbc::Sfm::Impl {

    Network::Network(const Abc_Ntk_t &abc_network, Parameters &params) {
        _impl = Abc_NtkExtractMfs(const_cast<Abc_Ntk_t*>(&abc_network), params->nFirstFixed);
        _impl->pPars = &params.GetImpl();
        Sfm_NtkPrepare(_impl, &params.GetImpl());
    }

    Network::Network(const Abc_Ntk_t &abc_network, Parameters &params, int pivot) {
        _impl = Abc_NtkExtractMfs2(const_cast<Abc_Ntk_t*>(&abc_network), pivot);
        _impl->pPars = &params.GetImpl();
        Sfm_NtkPrepare(_impl, &params.GetImpl());
    }

    Network::Network(const Gia_Man_t &gia_network, Parameters &params) {
        _impl = Gia_ManExtractMfs(const_cast<Gia_Man_t*>(&gia_network));
        _impl->pPars = &params.GetImpl();
        Sfm_NtkPrepare(_impl, &params.GetImpl());
    }

    Network::~Network() {
        Sfm_NtkFree(_impl);
    }

    namespace {

        // Useful for debugging purposes
        bool DumpSfmNetwork(Sfm_Ntk_t* ntk, const char* filename) {
            if (FILE* fp = fopen(filename, "w")) {
                int node_idx = 0;

                Sfm_NtkForEachNode(ntk, node_idx) {
                    fprintf(fp, "Node %d:\n", node_idx);

                    {
                        int fanin_node_idx = 0;
                        int fanin_i = 0;
                        Sfm_ObjForEachFanin(ntk, node_idx, fanin_node_idx, fanin_i) {
                            fprintf(fp, "\tFanin  #%d: %d\n", fanin_i, fanin_node_idx);
                        }
                    }

                    {
                        int fanout_node_idx = 0;
                        int fanout_i = 0;
                        Sfm_ObjForEachFanout(ntk, node_idx, fanout_node_idx, fanout_i) {
                            fprintf(fp, "\tFanout #%d: %d\n", fanout_i, fanout_node_idx);
                        }
                    }

                    fprintf(fp, "\n");
                }

                return fclose(fp) == 0;
            }

            return false;
        }

    } // <anonymous> namespace

    bool Network::Dump(const std::string &filename) const {
        return DumpSfmNetwork(_impl, filename.c_str());
    }

    namespace {

        void RemoveFanin(Network &network, Obj obj, Obj fanin) {
            EFX_DBG_HARD_ASSERT(&obj.GetNetwork() == &network);
            EFX_DBG_HARD_ASSERT(obj.IsNode());
            EFX_DBG_HARD_ASSERT(!obj.IsPrimaryInput());

            auto &network_impl = network.GetImpl();
            const auto node_idx = obj.Index();
            const auto fanin_idx = fanin.Index();

            Vec_IntRemove(Sfm_ObjFiArray(&network_impl, node_idx), fanin_idx);
            Vec_IntRemove(Sfm_ObjFoArray(&network_impl, fanin_idx), node_idx);
        }

        void AddFanin(Network &network, Obj obj, Obj fanin) {
            EFX_DBG_HARD_ASSERT(obj.IsNode());
            EFX_DBG_HARD_ASSERT(!fanin.IsPrimaryOutput());

            auto &network_impl = network.GetImpl();
            const auto node_idx = obj.Index();
            const auto fanin_idx = fanin.Index();

            EFX_DBG_HARD_ASSERT(std::ranges::count(obj.Fanins(), fanin) == 0);
            EFX_DBG_HARD_ASSERT(std::ranges::count(fanin.Fanouts(), obj) == 0);

            Vec_IntPush(Sfm_ObjFiArray(&network_impl, node_idx), fanin_idx);
            Vec_IntPush(Sfm_ObjFoArray(&network_impl, fanin_idx), node_idx);
        }

        void DeleteObj(Network &network, Obj obj, boost::unordered_flat_set<Obj::IndexType> &deleted) {
            if (obj.NumFanouts() > 0 || obj.IsPrimaryInput() || obj.IsFixed()) {
                return;
            }
            EFX_HARD_ASSERT(obj.IsNode());

            auto &network_impl = network.GetImpl();
            bool should_delete = deleted.emplace(obj.Index()).second;
            if (!should_delete) return;

            for (Obj fanin : obj.Fanins()) {
                Vec_IntRemove(Sfm_ObjFoArray(&network_impl, fanin.Index()), obj.Index());
                DeleteObj(network, fanin, deleted);
            }

            Vec_IntClear(Sfm_ObjFiArray(&network_impl, obj.Index()));
            Vec_WrdWriteEntry(network_impl.vTruths, obj.Index(), (word)0);
        }

    } // <anonymous> namespace

    NetworkEditor::~NetworkEditor() {
        if (std::uncaught_exceptions() == 0) {
            EFX_HARD_ASSERT(_pending_deletion.empty());
            EFX_HARD_ASSERT(_pending_truth_update.empty());
            EFX_HARD_ASSERT(_pending_level_update.empty());
            EFX_HARD_ASSERT(_pending_rev_level_update.empty());
        }
    }

    bool NetworkEditor::UpdateResubSolve(ResubSolveResult &&result) {
        bool reduced_num_fanins = false;

        auto &network_impl = _network.GetImpl();
        const auto num_words = Abc_Truth6WordNum(result.pivot.NumFanins() - 
                                   int(result.new_fanin.has_value()));

        EFX_DBG_HARD_ASSERT(result.pivot.IsNode());
        EFX_DBG_HARD_ASSERT(!result.new_fanin || result.curr_fanin.Index() != result.new_fanin->Index());
        EFX_DBG_HARD_ASSERT(result.pivot.NumFanins() <= SFM_FANIN_MAX);

        if (Abc_TtIsConst0(result.pTruth.data(), num_words) || 
            Abc_TtIsConst1(result.pTruth.data(), num_words))
        {
            reduced_num_fanins = result.pivot.NumFanins() > 0;

            for (Obj fanin : result.pivot.Fanins()) {
                Vec_IntRemove(Sfm_ObjFoArray(&network_impl, fanin.Index()), result.pivot.Index());
                _pending_deletion.emplace(fanin.Index());
            }
            Vec_IntClear(Sfm_ObjFiArray(&network_impl, result.pivot.Index()));
        }
        else {
            RemoveFanin(_network, result.pivot, result.curr_fanin);
            reduced_num_fanins = !result.new_fanin.has_value();

            if (auto new_fanin = result.new_fanin) {
                // replace old fanin by new fanin
                AddFanin(_network, result.pivot, *new_fanin);
            }

            // recursively remove MFFC
            _pending_deletion.emplace(result.curr_fanin.Index());
        }

        // update logic levels
        _pending_level_update.emplace(result.pivot.Index());
        if (auto new_fanin = result.new_fanin) {
            _pending_rev_level_update.emplace(new_fanin->Index());
        }
        // Unnecessary/incorrect condition? --> if (result.curr_fanin.Numfanouts() > 0)
        _pending_rev_level_update.emplace(result.curr_fanin.Index());

        // update truth table
        auto [iter, is_new] = _pending_truth_update.try_emplace(result.pivot.Index());
        EFX_HARD_ASSERT(is_new);

        auto &entry = iter->second;
        entry.utruth = result.truth;
        entry.num_words = num_words;
        entry.truth_arr.emplace(std::move(result.pTruth));

        return reduced_num_fanins;
    }

    void NetworkEditor::UpdateResubOne(const ResubOneResult &result) {
        // update truth table
        auto [iter, is_new] = _pending_truth_update.try_emplace(result.pivot.Index());
        EFX_HARD_ASSERT(is_new);

        iter->second.utruth = result.truth;
    }

    bool NetworkEditor::Update(ResubResult &&result) {
        if (auto* resubsolve = std::get_if<ResubSolveResult>(&result)) {
            return UpdateResubSolve(std::move(*resubsolve));
        }
        else {
            const auto* resubone = std::get_if<ResubOneResult>(&result);
            EFX_HARD_ASSERT(resubone != nullptr);
            UpdateResubOne(*resubone);
            return false;
        }
    }

    std::size_t NetworkEditor::Finalise() {
        // Recursively delete 0 fanout nodes
        boost::unordered_flat_set<Obj::IndexType> actually_deleted_objs;
        for (auto node_idx : _pending_deletion) {
            DeleteObj(_network, Obj{ _network, node_idx }, actually_deleted_objs);
        }
        _pending_deletion.clear();

        // Recursively update levels & reverse levels
        auto &network_impl = _network.GetImpl();
        for (auto node_idx : _pending_level_update) {
            Sfm_NtkUpdateLevel_rec(&network_impl, node_idx);
        }
        _pending_level_update.clear();
        for (auto node_idx : _pending_rev_level_update) {
            Sfm_NtkUpdateLevelR_rec(&network_impl, node_idx);
        }
        _pending_rev_level_update.clear();

        // Update truth tables and CNFs
        for (auto &[node_idx, info] : _pending_truth_update) {
            Obj node{ _network, node_idx };
            const auto num_fanins = node.NumFanins();

            if (actually_deleted_objs.contains(node_idx)) {
                // Node has been deleted.
                // The computed truth table is no longer valid, nor relevant
                //
                // We have already cleared its vTruths entry (see DeleteObj).
                // Need to also update the CNF entry (this step is missing in the original ABC implemetation?)
                Sfm_TruthToCnf(0, nullptr, 0, nullptr,
                               (Vec_Str_t*)_network.Cnf(node_idx));
                continue;
            }
            else {
                if (info.truth_arr) { // Resubsolve update
                    Vec_WrdWriteEntry(network_impl.vTruths, node_idx, info.utruth);
                    if (network_impl.vTruths2 && Vec_WrdSize(network_impl.vTruths2)) {
                        Abc_TtCopy(Vec_WrdEntryP(network_impl.vTruths2, Vec_IntEntry(network_impl.vStarts, node_idx)),
                                   info.truth_arr->data(), *info.num_words, 0);
                    }
                    AbcIntVec tmp_vec;
                    Sfm_TruthToCnf(info.utruth, info.truth_arr->data(), num_fanins, tmp_vec.Get(),
                                   (Vec_Str_t*)_network.Cnf(node_idx));
                }
                else { // ResubOne update
                    EFX_HARD_ASSERT(num_fanins <= 6);

                    Vec_WrdWriteEntry(network_impl.vTruths, node_idx, info.utruth);
                    Sfm_TruthToCnf(info.utruth, nullptr, num_fanins, nullptr,
                                    (Vec_Str_t*)_network.Cnf(node_idx));
                }
            }           
        }
        _pending_truth_update.clear();

        return actually_deleted_objs.size();
    }

} // namespace EfxAbc::Sfm::Impl