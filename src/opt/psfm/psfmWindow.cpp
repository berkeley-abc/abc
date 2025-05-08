#include "psfmImpl.hpp"
#include <algorithm>

namespace EfxAbc::Sfm::Impl {

    namespace {

        class VisitedNodeTracker {
            boost::unordered_flat_set<Obj::IndexType> _visited;
        
        public:
            // Returns true if inserted
            bool Intern(Obj obj) {
                return _visited.emplace(obj.Index()).second;
            }

            bool Contains(Obj obj) const {
                return _visited.contains(obj.Index());
            }
        };

        class TransitiveFaninsCollector {
            VectorOfObjIndices &_fanin_indices;
            VisitedNodeTracker &_visited;
            std::size_t _max_count = std::numeric_limits<std::size_t>::max();

            bool VisitRecursive(Obj obj) {
                bool node_not_visited = _visited.Intern(obj);
                if (!node_not_visited) {
                    return true;
                }

                for (Obj fanin : obj.Fanins()) {
                    if (!VisitRecursive(fanin)) {
                        return false;
                    }
                }

                _fanin_indices.push_back(obj.Index());
                return _fanin_indices.size() <= _max_count;
            }

            TransitiveFaninsCollector(VectorOfObjIndices &vec, VisitedNodeTracker &tracker)
            :_fanin_indices{ vec },
             _visited{ tracker }
            {}
        
        public:
            static bool WorkUnbounded(const ResubstitutionWindow &window,
                                      Obj obj,
                                      VectorOfObjIndices &result,
                                      VisitedNodeTracker &tracker)
            {
                TransitiveFaninsCollector collector{ result, tracker };
                return collector.VisitRecursive(obj);
            }

            static bool Work(const ResubstitutionWindow &window,
                             Obj obj,
                             VectorOfObjIndices &result,
                             VisitedNodeTracker &tracker)
            {
                TransitiveFaninsCollector collector{ result, tracker };
                if (auto max_win_size = window.GetParameters()->nWinSizeMax;
                    max_win_size > 0)
                {
                    collector._max_count = static_cast<std::size_t>(max_win_size);
                }

                return collector.VisitRecursive(obj);
            }
        };

        class DivisorCollector {
            const VisitedNodeTracker &_fanin_tracker;
            std::size_t _max_fanouts = std::numeric_limits<std::size_t>::max();

            VisitedNodeTracker _divisor_tracker;
            boost::unordered_flat_map<Obj::IndexType, int> _fanin_count;
            VectorOfObjIndices &_result;
            
        public:
            DivisorCollector(const Parameters &params,
                             const VisitedNodeTracker &fanin_tracker,
                             VectorOfObjIndices &result)
            :_fanin_tracker{ fanin_tracker },
             _result{ result }
            {
                if (auto max_fanouts = params->nFanoutMax;
                    max_fanouts > 0)
                {
                    _max_fanouts = static_cast<std::size_t>(max_fanouts);
                }
            }

            void operator()(Obj obj, std::size_t max_level) {
                std::size_t fanout_count = 0;

                for (Obj fanout : obj.Fanouts()) {
                    // skip some of the fanouts if the number is large
                    if (fanout_count > _max_fanouts) {
                        return;
                    }
                    ++fanout_count;

                    // skip TFI nodes, PO nodes, or nodes with high logic level
                    if (_fanin_tracker.Contains(fanout) ||
                        fanout.IsPrimaryOutput() ||
                        fanout.Level() > max_level)
                    {
                        continue;
                    }

                    const auto num_fanins = fanout.NumFanins();

                    // handle single-input nodes
                    
                    if (num_fanins == 1) {
                        _result.push_back(fanout.Index());
                    }
                    // visit node for the first time
                    else if (_divisor_tracker.Intern(fanout)) {
                        EFX_DBG_HARD_ASSERT(num_fanins > 1);
                        _fanin_count[fanout.Index()] = num_fanins - 1;
                    }
                    else if ((--_fanin_count[fanout.Index()]) == 0) {
                        _result.push_back(fanout.Index());
                    }
                }
            }
        };

        class RootsCollector {
            const Parameters &_params;
            Obj::IndexType _pivot_idx;
            std::size_t _max_level;
            VectorOfObjIndices &_roots;
            VectorOfObjIndices &_tfos;
            VisitedNodeTracker _tracker;

            RootsCollector(const Parameters &params,
                           Obj pivot,
                           std::size_t max_level,
                           VectorOfObjIndices &roots,
                           VectorOfObjIndices &tfos)
            :_params{ params },
             _pivot_idx{ pivot.Index() },
             _max_level{ max_level },
             _roots{ roots },
             _tfos{ tfos }
            {}

            void CollectRecursive(Obj obj) {
                if (!_tracker.Intern(obj)) {
                    return;
                }

                if (obj.Index() != _pivot_idx) {
                    _tfos.push_back(obj.Index());
                }

                // check if the node should be the root
                if (obj.IsRoot(_params, _max_level)) {
                    _roots.push_back(obj.Index());
                }
                // if not, explore its fanouts
                else {
                    for (Obj fanout : obj.Fanouts()) {
                        CollectRecursive(fanout);
                    }
                }
            }
        
        public:
            static void Work(const Parameters &params,
                             Obj pivot, 
                             std::size_t max_level,
                             VectorOfObjIndices &roots, 
                             VectorOfObjIndices &tfos)
            {
                RootsCollector collector{ params, pivot, max_level, roots, tfos };
                collector.CollectRecursive(pivot);
            }
        };

    } // <anonymous> namespace

    std::optional<ResubstitutionWindow> ResubstitutionWindow::Make(const Parameters &params, Obj obj,
                                                                   ResubSolverInitData &solver_init_data)
    {
        ResubstitutionWindow result{ params, obj };

        if (!result.Init(solver_init_data)) {
            return std::nullopt;
        }
        return result;
    }

    bool ResubstitutionWindow::Init(ResubSolverInitData &solver_init_data) {
        {
            VisitedNodeTracker fanin_tracker;

            // collect transitive fanin
            {
                VectorOfObjIndices nodes;
                if (!TransitiveFaninsCollector::Work(*this, _pivot, nodes, fanin_tracker)) {
                    return false;
                }

                _divisors = std::move(nodes);
            }

            // create divisors
            EFX_HARD_ASSERT(!_divisors.empty());
            _divisors.pop_back();

            auto max_num_divisors = std::numeric_limits<std::size_t>::max();
            if (const auto max_win_size = GetParameters()->nWinSizeMax;
                max_win_size > 0)
            {
                max_num_divisors = static_cast<std::size_t>(max_win_size);
            }

            // add non-topological divisors
            //
            // In practice this doesn't really contribute much to QoR.
            // Disabling when strict compliance is not requested
            if (GetParameters().StrictCompliance()) {
                DivisorCollector div_collector{ GetParameters(), fanin_tracker, _divisors };

                const auto max_level = GetNetwork().MaxLevel();
                EFX_HARD_ASSERT(max_level >= _pivot.ReverseLevel());
                const auto relative_max_level = max_level - _pivot.ReverseLevel();

                for (std::size_t i = 0; i < _divisors.size(); ++i) {
                    // Note: We are appending to _divisors while iterating over it
                    // hence the use of classic for loop.
                    auto div_node_idx = _divisors[i];

                    if (_divisors.size() >= max_num_divisors) {
                        break;
                    }

                    div_collector(Obj{ GetNetwork(), div_node_idx }, relative_max_level);
                }
            }

            if (_divisors.size() > max_num_divisors) {
                _divisors.resize(max_num_divisors);
            }
        }

        // remove node/fanins from divisors
        // compact divisors
        {
            boost::unordered_flat_set<Obj::IndexType> immediate_nodes;

            immediate_nodes.insert(_pivot.Index());
            for (Obj fanin : _pivot.Fanins()) {
                immediate_nodes.insert(fanin.Index());
            }

            auto removed_range = std::ranges::remove_if(_divisors, [&](auto idx){
                return immediate_nodes.contains(idx) ||
                       !Obj{ GetNetwork(), idx }.IsUseful();
            });
            _divisors.erase(removed_range.begin(), removed_range.end());
        }

        // collect TFO and window root
        if (const auto max_tfo_level = GetParameters()->nTfoLevMax;
            max_tfo_level > 0 && !_pivot.IsRoot(GetParameters(), _pivot.Level() + max_tfo_level))
        {
            // explore transitive fanout
            {
                RootsCollector::Work(GetParameters(), _pivot, _pivot.Level() + max_tfo_level,
                                     solver_init_data.roots, solver_init_data.tfos);
                EFX_HARD_ASSERT(!solver_init_data.roots.empty());
                EFX_HARD_ASSERT(!solver_init_data.tfos.empty());
            }

            VisitedNodeTracker tracker;

            auto collect_tfi = [&](const auto &nodes) {
                for (auto node_idx : nodes) {
                    if (!TransitiveFaninsCollector::Work(*this, Obj{ GetNetwork(), node_idx },
                                                         solver_init_data.order, tracker))
                    {
                        solver_init_data.roots.clear();
                        solver_init_data.tfos.clear();
                        solver_init_data.order.clear();
                        return;
                    }
                }
            };

            // compute new leaves and nodes
            collect_tfi(solver_init_data.roots);
            if (!solver_init_data.roots.empty()) {
                collect_tfi(solver_init_data.tfos);
            }
            if (!solver_init_data.roots.empty()) {
                collect_tfi(_divisors);
            }
        }

        if (solver_init_data.order.empty()) {
            VisitedNodeTracker tracker;

            TransitiveFaninsCollector::WorkUnbounded(*this, _pivot, solver_init_data.order, tracker);
            for (auto div_node_idx : _divisors) {
                TransitiveFaninsCollector::WorkUnbounded(*this, Obj{ GetNetwork(), div_node_idx }, solver_init_data.order, tracker);
            }
        }

        return true;
    }

} // namespace EfxAbc::Sfm::Impl