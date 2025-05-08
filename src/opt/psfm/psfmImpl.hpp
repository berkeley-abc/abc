#pragma once

#include "opt/sfm/sfmInt.h"
#include "psfm.hpp"

#include <array>
#include <cstdint>
#include <memory>
#include <optional>
#include <variant>
#include <vector>
#include <boost/unordered/unordered_flat_set.hpp>
#include <boost/unordered/unordered_flat_map.hpp>

namespace EfxAbc::Sfm::Impl {

    class PrimaryInput;

    class ScopedAbcNetwork {
        Abc_Ntk_t* _network;

    public:
        ScopedAbcNetwork(Abc_Ntk_t* ntk) noexcept
        :_network{ ntk }
        {}

        ~ScopedAbcNetwork() {
            if (_network) {
                Abc_NtkDelete(_network);
            }
        }

        ScopedAbcNetwork(const ScopedAbcNetwork&) = delete;
        ScopedAbcNetwork &operator=(const ScopedAbcNetwork&) = delete;

        auto Get() const noexcept { return _network; }
        auto &operator*() const noexcept { return *_network; };
    };

    class Network {
        Sfm_Ntk_t* _impl;
    
    public:
        Network(const Abc_Ntk_t &abc_network, Parameters &params);
        Network(const Abc_Ntk_t &abc_network, Parameters &params, int pivot);
        Network(const Gia_Man_t &gia_network, Parameters &params);
        ~Network();

        Network(const Network&) = delete;
        Network &operator=(const Network&) = delete;

        auto Nodes() const;
        std::size_t NumNodes() const noexcept { return static_cast<std::size_t>(Sfm_NtkNodeNum(_impl)); }

        std::size_t MaxLevel() const noexcept { return static_cast<std::size_t>(_impl->nLevelMax); }

        auto* Cnf(std::size_t idx) noexcept { return Vec_WecEntry(_impl->vCnfs, idx); }
        
        word Truth(std::size_t idx) const noexcept { return Vec_WrdEntry(_impl->vTruths, idx); }
        auto ElementaryTruth(std::size_t idx) const noexcept {  return static_cast<const word*>(_impl->pTtElems[idx]); }

        Sfm_Ntk_t &GetImpl() noexcept { return *_impl; }
        const Sfm_Ntk_t &GetImpl() const noexcept { return *_impl; }

        bool Dump(const std::string &filename) const;
    };

    class Obj {
        friend class Network;
        using IdxType = int;

        const Network* _network;
        IdxType _idx;

        auto NonConstNetworkPtr() const noexcept { return const_cast<Network*>(_network); }
        auto NonConstNetworkImplPtr() const noexcept { return &NonConstNetworkPtr()->GetImpl(); }

    public:
        using IndexType = IdxType;

        Obj(const Network &network, IdxType idx)
        :_network{ &network },
         _idx{ idx }
        {}

        inline bool operator==(const Obj &other) const noexcept {
            EFX_DBG_HARD_ASSERT(_network == other._network);
            return _idx == other._idx;
        }

        bool IsFixed() const noexcept { return Sfm_ObjIsFixed(NonConstNetworkImplPtr(), _idx); }
        bool IsNode() const noexcept { return Sfm_ObjIsNode(NonConstNetworkImplPtr(), _idx); }
        bool IsPrimaryInput() const noexcept { return Sfm_ObjIsPi(NonConstNetworkImplPtr(), _idx); }
        bool IsPrimaryOutput() const noexcept { return Sfm_ObjIsPo(NonConstNetworkImplPtr(), _idx); }
        bool IsUseful() const noexcept { return Sfm_ObjIsUseful(NonConstNetworkImplPtr(), _idx); }
        bool IsRoot(const Parameters &params, int max_level) const noexcept {
            return Sfm_NtkCheckRoot(NonConstNetworkImplPtr(), &params.GetImpl(), _idx, max_level);
        }

        std::size_t Level() const noexcept { return Sfm_ObjLevel(NonConstNetworkImplPtr(), _idx); }
        std::size_t ReverseLevel() const noexcept { return Sfm_ObjLevelR(NonConstNetworkImplPtr(), _idx); }

        std::size_t NumFanins() const noexcept { return static_cast<std::size_t>(Sfm_ObjFaninNum(NonConstNetworkImplPtr(), _idx)); }
        auto Fanins() const {
            std::ranges::iota_view indices{ std::size_t(0), NumFanins() };
            auto ntk_ptr = NonConstNetworkPtr();
            auto this_idx = Index();

            return indices
                   | std::views::transform([ntk_ptr, this_idx](auto fanin_idx){ return Sfm_ObjFanin(&ntk_ptr->GetImpl(), this_idx, fanin_idx); })
                   | std::views::transform([ntk_ptr](auto node_idx){ return Obj{ *ntk_ptr, node_idx }; });
        }

        std::size_t NumFanouts() const noexcept { return static_cast<std::size_t>(Sfm_ObjFanoutNum(NonConstNetworkImplPtr(), _idx)); }
        auto Fanouts() const {
            std::ranges::iota_view indices{ std::size_t(0), NumFanouts() };
            auto ntk_ptr = NonConstNetworkPtr();
            auto this_idx = Index();

            return indices
                   | std::views::transform([ntk_ptr, this_idx](auto fanout_idx){ return Sfm_ObjFanout(&ntk_ptr->GetImpl(), this_idx, fanout_idx); })
                   | std::views::transform([ntk_ptr](auto node_idx){ return Obj{ *ntk_ptr, node_idx }; });
        }

        IndexType Index() const noexcept { return _idx; }
        const Network &GetNetwork() const noexcept { return *_network; }
    };

    inline auto Network::Nodes() const {
        std::ranges::iota_view indices{ _impl->nPis, _impl->nObjs - _impl->nPos };

        return indices 
               | std::views::transform([this](auto idx){ return Obj{ *this, idx }; });
    }

    using VectorOfObjIndices = std::vector<Obj::IndexType>;

    struct ResubSolverInitData {
        VectorOfObjIndices roots;
        VectorOfObjIndices tfos;
        VectorOfObjIndices order;
    };

    class ObjIdxToObj {
        const Network* _network;
    
    public:
        ObjIdxToObj(const Network &network)
        :_network{ &network }
        {}

        auto operator()(Obj::IndexType idx) const {
            return Obj{ *_network, idx };
        }
    };

    class ResubstitutionWindow {
        const Parameters* _params;
        Obj _pivot;

        VectorOfObjIndices _divisors;
        
        ResubstitutionWindow(const Parameters &params, Obj obj)
        :_params{ &params },
         _pivot{ obj }
        {}

        bool Init(ResubSolverInitData &solver_init_data);
    
    public:
        static std::optional<ResubstitutionWindow> Make(const Parameters &params, Obj obj,
                                                        ResubSolverInitData &solver_init_data);

        Obj Pivot() const noexcept { return _pivot; }
        const Network &GetNetwork() const noexcept { return _pivot.GetNetwork(); }
        const Parameters &GetParameters() const noexcept { return *_params; }

        inline auto NumDivisors() const noexcept { return _divisors.size(); }
        Obj Divisor(std::size_t idx) const { return ObjIdxToObj(GetNetwork())(_divisors[idx]); }
        auto Divisors() const { return _divisors | std::views::transform(ObjIdxToObj{ GetNetwork() }); }
    };

    using TruthArr = std::array<word, SFM_WORDS_MAX>;
    
    struct ResubSolveDataset {
        std::vector<Obj::IndexType> divisor_indices;
        TruthArr pTruth;
    };

    struct ResubSolveResult {
        Obj pivot;
        Obj curr_fanin;
        std::optional<Obj> new_fanin;
        TruthArr pTruth;
        word truth;

        ResubSolveResult(Obj p, Obj curr_f, std::optional<Obj> new_f,
                         const TruthArr &pT, word t)
        :pivot{ p },
         curr_fanin{ curr_f },
         new_fanin{ new_f },
         pTruth{ pT },
         truth{ t }
        {}
    };

    struct ResubOneResult {
        Obj pivot;
        word truth;

        ResubOneResult(Obj p, word t)
        :pivot{ p },
         truth{ t }
        {}
    };

    using ResubResult = std::variant<std::monostate, ResubSolveResult, ResubOneResult>;

    class ResubstitutionSolver {
        using SatVarIdx = std::int32_t;

        const ResubstitutionWindow* _window;
        sat_solver* _sat;

        boost::unordered_flat_map<Obj::IndexType, SatVarIdx> _node_to_sat_var;

        std::vector<SatVarIdx> _divisor_sat_var;
        std::vector<word> _divisor_counter_examples_buffer;
        std::size_t _num_counter_examples = 0;

        ResubstitutionSolver(const ResubstitutionWindow &window, sat_solver &sat)
        :_window{ &window },
         _sat{ &sat }
        {}

        void RecordVarMapping(const VectorOfObjIndices &order, std::size_t &sat_var_counter);
        void UpdateVarMapping(Obj::IndexType node_idx, std::size_t &sat_var_counter);

        SatVarIdx NodeToSatVar(Obj::IndexType node_idx) const {
            auto iter = _node_to_sat_var.find(node_idx);
            EFX_HARD_ASSERT(iter != _node_to_sat_var.end());
            return iter->second;
        }
    
    public:
        ResubstitutionSolver(const ResubstitutionSolver&) = delete;
        ResubstitutionSolver &operator=(const ResubstitutionSolver&) = delete;

        static std::unique_ptr<ResubstitutionSolver> Make(const ResubstitutionWindow &window,
                                                          sat_solver &sat,
                                                          const ResubSolverInitData &init_data);

        std::optional<ResubSolveResult> TryNodeResubstitutionSolve(Obj fanin, bool remove_only);
        std::optional<ResubOneResult> TryNodeResubstitutionOne();

        word ComputeInterpolant(ResubSolveDataset &dataset);
        word ComputeInterpolant2();
    };

    class NetworkEditor {
        struct NewTruthInfo {
            word utruth;
            std::optional<int> num_words;
            std::optional<TruthArr> truth_arr;
        };

        Network &_network;

        boost::unordered_flat_set<Obj::IndexType> _pending_deletion;
        boost::unordered_flat_map<Obj::IndexType, NewTruthInfo> _pending_truth_update;
        boost::unordered_flat_set<Obj::IndexType> _pending_level_update;
        boost::unordered_flat_set<Obj::IndexType> _pending_rev_level_update;
    
        // Returns true if a fanin has been directly deleted
        bool UpdateResubSolve(ResubSolveResult &&result);

        void UpdateResubOne(const ResubOneResult &result);

    public:
        NetworkEditor(Network &network)
        :_network{ network }
        {}

        ~NetworkEditor();

        NetworkEditor(const NetworkEditor&) = delete;
        NetworkEditor &operator=(const NetworkEditor&) = delete;

        // Returns true if a fanin has been directly deleted
        bool Update(ResubResult &&result);

        // Returns the number of deleted nodes
        std::size_t Finalise();
    };

    struct Report {
        std::size_t num_deleted_fanins = 0;
        std::size_t num_deleted_nodes = 0;
        std::size_t num_changed_nodes = 0;
    };
    Report ExecuteImpl(Network &network, const Parameters &params);

} // namespace EfxAbc::Sfm::Impl