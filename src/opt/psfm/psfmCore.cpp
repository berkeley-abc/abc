#include "psfmImpl.hpp"

#include "tbb/blocked_range.h"
#include "tbb/parallel_for.h"
#include <random>
#include <thread>

#include "efxProf.h"

namespace EfxAbc::Sfm::Impl {

    namespace {

        bool ShouldConsiderNode(const Parameters &params, Obj node) {
            if (node.IsFixed()) {
                return false;
            }
            if (params->nDepthMax && node.Level() > params->nDepthMax) {
                return false;
            }
            if (node.NumFanins() > SFM_SUPP_MAX) {
                return false;
            }
            return true;
        }

        ResubResult TryNodeResubstitution(const Parameters &params, sat_solver &sat, Obj obj) {
            auto solver_init_data = std::make_unique<ResubSolverInitData>();

            auto window = ResubstitutionWindow::Make(params, obj, *solver_init_data);
            if (!window) {
                return {};
            }

            auto solver = ResubstitutionSolver::Make(*window, sat, *solver_init_data);
            if (!solver) {
                return {};
            }
            solver_init_data.reset();

            // try replacing area critical fanins
            for (Obj fanin : obj.Fanins()) {
                if (fanin.IsNode() && fanin.NumFanouts() == 1) {
                    if (auto opt = solver->TryNodeResubstitutionSolve(fanin, false)) {
                        return *opt;
                    }
                } 
            }

            // try removing redundant edges
            if (!params->fArea) {
                for (Obj fanin : obj.Fanins()) {
                    if (!fanin.IsNode() || fanin.NumFanouts() != 1) {
                        if (auto opt = solver->TryNodeResubstitutionSolve(fanin, true)) {
                            return *opt;
                        }
                    } 
                }
            }

            // try simplifying local functions
            if (params->fUseDcs && obj.NumFanins() <= 6) {
                if (auto opt = solver->TryNodeResubstitutionOne()) {
                    return *opt;
                }
            }

            return {};
        }

        class ScopedSatSolver {
            sat_solver* _solver = nullptr;
        
        public:
            ScopedSatSolver() {
                _solver = sat_solver_new();
            }

            ScopedSatSolver(const ScopedSatSolver&) = delete;
            ScopedSatSolver &operator=(const ScopedSatSolver&) = delete;

            ~ScopedSatSolver() {
                sat_solver_delete(_solver);
            }

            operator sat_solver&() noexcept {
                return *_solver;
            }
        };

        struct CandidateNode {
            Obj node;
            bool in_consideration = false;

            CandidateNode(Obj n) noexcept
            :node{ n }
            {}
        };

    } // <anonymous> namespace

    Report ExecuteImpl(Network &network, const Parameters &params) {
        const auto starting_num_nodes = network.NumNodes();
        if (starting_num_nodes == 0) return {};

        DIAG_GBL_POST_DEBUG("EfxAbc::Sfm is considering network with {} nodes", starting_num_nodes);
        EfxProf &prof = EfxProf::get();

        std::vector<CandidateNode> candidate_nodes;
        for (Obj node : network.Nodes()) {
            candidate_nodes.emplace_back(node);
        }

        if (!params.StrictCompliance()) {
            static const auto prune_group_id = prof.RegisterGroup("EfxAbc::Sfm::Prune");
            EfxScopedProf scoped_sweep_prof(prof, prune_group_id);

            // Using simple partitioner to work around sat_solver_restart()'s incomplete
            // cleaning, which would manifest as non-determinism if not mitigated.
            tbb::parallel_for(
                tbb::blocked_range<std::size_t>(0, candidate_nodes.size(), 256),
                [&params, &candidate_nodes](const auto &subrange) {
                    ScopedSatSolver sat;

                    for (auto i = subrange.begin(); i != subrange.end(); ++i) {
                        auto &candidate = candidate_nodes[i];

                        auto solution = TryNodeResubstitution(params, sat, candidate.node);
                        if (!std::holds_alternative<std::monostate>(solution)) {
                            candidate.in_consideration = true;
                        }
                    }
                },
                tbb::simple_partitioner{}
            );

            const auto num_eliminated = std::ranges::count_if(candidate_nodes,
                                                              [](const auto &c){ return !c.in_consideration; });
            DIAG_GBL_POST_DEBUG("EfxAbc::Sfm ruled out {} ({:.2f}%) nodes",
                                num_eliminated, static_cast<float>(num_eliminated) / starting_num_nodes * 100.0f);
        }
        else {
            DIAG_GBL_POST_DEBUG("EfxAbc::Sfm strict compliance mode enabled");

            for (auto &candidate : candidate_nodes) {
                candidate.in_consideration = true;
            }
        }

        std::size_t num_changed_nodes = 0;
        std::size_t total_deleted_fanins = 0;
        std::size_t total_deleted_nodes = 0;

        {
            static const auto main_group_id = prof.RegisterGroup("EfxAbc::Sfm::MainBody");
            EfxScopedProf scoped_sweep_prof(prof, main_group_id);

            ScopedSatSolver sat;
            for (const auto &candidate : candidate_nodes
                                         | std::views::filter([](const auto &c){ return c.in_consideration; })
                                         | std::views::filter([&params](const auto &c){ return ShouldConsiderNode(params, c.node); }))
            {
                bool changed_node = false;
                auto solution = TryNodeResubstitution(params, sat, candidate.node);

                while (!std::holds_alternative<std::monostate>(solution)) {
                    changed_node = true;

                    {
                        NetworkEditor editor{ network };
                        total_deleted_fanins += std::size_t(editor.Update(std::move(solution)));
                        total_deleted_nodes += editor.Finalise();
                    }

                    solution = TryNodeResubstitution(params, sat, candidate.node);
                }

                num_changed_nodes += std::size_t(changed_node);
                if (params->nNodesMax && num_changed_nodes >= params->nNodesMax) {
                    break;
                }
            }
        }

        Report rpt;
        rpt.num_deleted_fanins = total_deleted_fanins;
        rpt.num_deleted_nodes = total_deleted_nodes;
        rpt.num_changed_nodes = num_changed_nodes;
        return rpt;
    }

} // namespace EfxAbc::Sfm::Impl {