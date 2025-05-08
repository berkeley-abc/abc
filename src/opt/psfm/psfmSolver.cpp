#include "psfmImpl.hpp"
#include "bool/kit/kit.h"

namespace EfxAbc::Sfm::Impl {

    void ResubstitutionSolver::RecordVarMapping(const VectorOfObjIndices &order, std::size_t &sat_var_counter) {
        _node_to_sat_var.reserve(order.size());

        for (auto obj_idx : order) {
            _node_to_sat_var[obj_idx] = sat_var_counter;
            ++sat_var_counter;
        }
    }

    void ResubstitutionSolver::UpdateVarMapping(Obj::IndexType node_idx, std::size_t &sat_var_counter) {
        _node_to_sat_var[node_idx] = sat_var_counter;
        ++sat_var_counter;
    }

    std::unique_ptr<ResubstitutionSolver> ResubstitutionSolver::Make(const ResubstitutionWindow &window,
                                                                     sat_solver &sat,
                                                                     const ResubSolverInitData &solver_init_data)
    {
        std::unique_ptr<ResubstitutionSolver> result{ new ResubstitutionSolver{ window, sat } };

        // solver_init_data.order contains all variables in the window in a good order
        // window.Divisors() is a subset of nodes in solver_init_data.order used as divisor candidates
        // solver_init_data.tfos contains TFO of the node (does not include node)
        // solver_init_data.roots contains roots of the TFO of the node (may include node)
        sat_solver_restart(result->_sat);
        sat_solver_setnvars(result->_sat,
                            1 + solver_init_data.order.size() + solver_init_data.tfos.size() + solver_init_data.roots.size() + 10);

        // create SAT variables
        std::size_t sat_var_counter = 1;
        result->RecordVarMapping(solver_init_data.order, sat_var_counter);

        // collect divisor variables
        for (Obj div_node : window.Divisors()) {
            result->_divisor_sat_var.push_back(result->NodeToSatVar((div_node.Index())));
        }

        // add CNF clauses for the TFI
        {
            AbcIntVec fanin_mapping;
            AbcWecVec clauses;

            for (Obj order_node : solver_init_data.order
                                  | std::views::transform(ObjIdxToObj{ window.GetNetwork() })) 
            {
                if (order_node.IsPrimaryInput()) continue;

                // collect fanin variables
                fanin_mapping.clear();
                for (Obj fanin : order_node.Fanins()) {
                    fanin_mapping.push_back(result->NodeToSatVar(fanin.Index()));
                }
                fanin_mapping.push_back(result->NodeToSatVar(order_node.Index()));

                // generate CNF 
                clauses.clear();
                Sfm_TranslateCnf(clauses.Get(),
                                 (Vec_Str_t *)const_cast<Network&>(window.GetNetwork()).Cnf(order_node.Index()),
                                 fanin_mapping.Get(), -1);
                
                // add clauses
                for (auto clause : clauses.Range()) {
                    if (clause.empty()) break;

                    bool add_clause_success = sat_solver_addclause(result->_sat, clause.data(), clause.data() + clause.size());
                    if (!add_clause_success) {
                        return {};
                    }
                }
            }
        }

        if (solver_init_data.tfos.size() > 0) {
            EFX_HARD_ASSERT(window.GetParameters()->nTfoLevMax > 0);
            EFX_HARD_ASSERT(!solver_init_data.roots.empty());
            
            // collect variables of root nodes
            std::vector<SatVarIdx> literals;
            for (auto obj_idx : solver_init_data.roots) {
                literals.push_back(result->NodeToSatVar(obj_idx));
            }
            // assign new variables to the TFO nodes
            for (auto obj_idx : solver_init_data.tfos) {
                result->UpdateVarMapping(obj_idx, sat_var_counter);
            }

            // add CNF clauses for the TFO
            AbcIntVec fanin_mapping;
            AbcWecVec clauses;

            for (Obj obj : solver_init_data.tfos
                           | std::views::transform(ObjIdxToObj{ window.GetNetwork() })) 
            {
                // collect fanin variables
                fanin_mapping.clear();
                for (Obj fanin : obj.Fanins()) {
                    fanin_mapping.push_back(result->NodeToSatVar(fanin.Index()));
                }
                fanin_mapping.push_back(result->NodeToSatVar(obj.Index()));

                // generate CNF 
                clauses.clear();
                Sfm_TranslateCnf(clauses.Get(),
                                 (Vec_Str_t*)const_cast<Network&>(window.GetNetwork()).Cnf(obj.Index()),
                                 fanin_mapping.Get(),
                                 result->NodeToSatVar(window.Pivot().Index()));
                
                // add clauses
                for (auto clause : clauses.Range()) {
                    if (clause.empty()) break;

                    bool add_clause_success = sat_solver_addclause(result->_sat, clause.data(), clause.data() + clause.size());
                    if (!add_clause_success) {
                        return {};
                    }
                }
            }

            // create XOR clauses for the roots
            std::size_t i = 0;
            for (auto obj_idx : solver_init_data.roots) {
                sat_solver_add_xor(result->_sat, literals[i], result->NodeToSatVar(obj_idx), sat_var_counter, 0 );
                literals[i] = Abc_Var2Lit(sat_var_counter, 0);

                ++sat_var_counter;
                ++i;
            }

            // make OR clause for the last nRoots variables
            bool add_clause_success = sat_solver_addclause(result->_sat, literals.data(), literals.data() + literals.size());
            if (!add_clause_success) {
                return {};
            }
        }

        // finalize
        if (sat_solver_simplify(result->_sat)) {
            return result;
        }
        return {};
    }

    std::optional<ResubSolveResult> ResubstitutionSolver::TryNodeResubstitutionSolve(Obj fanin, bool remove_only) {
        // clean simulation info
        _num_counter_examples = 0;
        _divisor_counter_examples_buffer.clear();
        _divisor_counter_examples_buffer.resize(_window->NumDivisors(), 0);

        ResubSolveDataset dataset;

        // collect fanins
        for (Obj curr_fanin : _window->Pivot().Fanins()) {
            if (curr_fanin.Index() != fanin.Index()) {
                dataset.divisor_indices.push_back(NodeToSatVar(curr_fanin.Index()));
            }
        }

        // Find fanin to skip
        Obj::IndexType fanin_index_to_skip = -1;
        if (fanin.IsFixed() && fanin.NumFanins() == 1) {
            fanin_index_to_skip  = (*fanin.Fanins().begin()).Index();
        }

        std::optional<Obj> new_fanin;

        auto truth = ComputeInterpolant(dataset);
        if (truth == SFM_SAT_UNDEC) {
            return std::nullopt;
        }
        else if (truth == SFM_SAT_SAT) {
            if (remove_only || _window->GetParameters()->fRrOnly || _window->NumDivisors() == 0) {
                return std::nullopt;
            }

            while (true) {
                // find the next divisor to try
                word mask = (~(word)0) >> (std::size_t(64) - _num_counter_examples);

                std::size_t i = 0;
                for (i = 0; i < _divisor_counter_examples_buffer.size(); ++i) {
                    const auto sign = _divisor_counter_examples_buffer[i];
                    if (sign == mask && _window->Divisor(i).Index() != fanin_index_to_skip) {
                        break;
                    }
                }
                if (i == _divisor_counter_examples_buffer.size()) {
                    return std::nullopt;
                }

                // try replacing the critical fanin
                const auto curr_candidate_var = NodeToSatVar(_window->Divisor(i).Index());
                dataset.divisor_indices.push_back(curr_candidate_var);
                truth = ComputeInterpolant(dataset);

                // analyze outcomes
                if (truth == SFM_SAT_UNDEC) {
                    return std::nullopt;
                }
                else if (truth != SFM_SAT_SAT) {
                    new_fanin = _window->Divisor(i);
                    break;
                }
                else if (_num_counter_examples == 64) {
                    return std::nullopt;
                }
                // remove the last variable
                dataset.divisor_indices.pop_back();
            }
        }

        return ResubSolveResult{ _window->Pivot(),
                                 fanin,
                                 new_fanin,
                                 dataset.pTruth,
                                 truth };
    }

    std::optional<ResubOneResult> ResubstitutionSolver::TryNodeResubstitutionOne() {
        auto truth = ComputeInterpolant2();
        
        if (truth == SFM_SAT_UNDEC) {
            return std::nullopt;
        }
        EFX_HARD_ASSERT(truth != SFM_SAT_SAT);
        
        const auto pivot = _window->Pivot();
        const auto truth0 = _window->GetNetwork().Truth(pivot.Index());
        if (truth == truth0) {
            return std::nullopt;
        }

        AbcIntVec tmp_vec;

        auto old_val = Kit_TruthLitNum((unsigned*)&truth0, pivot.NumFanins(), tmp_vec.Get());
        auto new_val = Kit_TruthLitNum((unsigned*)&truth, pivot.NumFanins(), tmp_vec.Get());
        if (new_val > old_val) {
            return std::nullopt;
        }

        return ResubOneResult{ _window->Pivot(), truth };
    }

    word ResubstitutionSolver::ComputeInterpolant(ResubSolveDataset &dataset) {
        const auto num_vars = sat_solver_nvars(_sat);
        const auto num_words = Abc_Truth6WordNum(dataset.divisor_indices.size());
        sat_solver_setnvars(_sat, num_vars + 1);

        int literals[2];
        literals[0] = Abc_Var2Lit(NodeToSatVar(_window->Pivot().Index()), 0);
        literals[1] = Abc_Var2Lit(num_vars, 0);
        Abc_TtClear(dataset.pTruth.data(), num_words);

        std::vector<int> var_values;

        while (true) {
            // Find onset minterm
            auto status = sat_solver_solve(_sat, literals, literals + 2, _window->GetParameters()->nBTLimit, 0, 0, 0);
            if (status == l_Undef) {
                return SFM_SAT_UNDEC;
            }
            else if (status == l_False) {
                return dataset.pTruth[0];
            }
            EFX_HARD_ASSERT(status == l_True);

            // remember variable values
            var_values.clear();
            for (auto var_idx : _divisor_sat_var) {
                var_values.push_back(sat_solver_var_value(_sat, var_idx));
            }

            // collect divisor literals
            std::vector<int> divisor_literals;
            divisor_literals.push_back(Abc_LitNot(literals[0]));
            for (auto div_idx : dataset.divisor_indices) {
                divisor_literals.push_back(sat_solver_var_literal(_sat, div_idx));
            }

            // check against offset
            status = sat_solver_solve(_sat, divisor_literals.data(), divisor_literals.data() + divisor_literals.size(),
                                      _window->GetParameters()->nBTLimit, 0, 0, 0);
            if (status == l_Undef) {
                return SFM_SAT_UNDEC;
            }
            else if (status == l_True) {
                break;
            }
            EFX_HARD_ASSERT(status == l_False);

            // compute cube and add clause
            int* final = nullptr;
            const auto final_count = sat_solver_final(_sat, &final);

            word cube[SFM_WORDS_MAX];
            Abc_TtFill(cube, num_words);
            divisor_literals.clear();
            divisor_literals.push_back(Abc_LitNot(literals[1]));
            for (int i = 0; i < final_count; ++i) {
                if (final[i] == literals[0]) {
                    continue;
                }
                divisor_literals.push_back(final[i]);

                auto var_iter = std::ranges::find(dataset.divisor_indices, Abc_Lit2Var(final[i]));
                EFX_HARD_ASSERT(var_iter != dataset.divisor_indices.end());
                auto div_idx = std::distance(dataset.divisor_indices.begin(), var_iter);

                Abc_TtAndSharp(cube, cube,
                               const_cast<word*>(_window->GetNetwork().ElementaryTruth(div_idx)),
                               num_words, !Abc_LitIsCompl(final[i]));
            }

            Abc_TtOr(dataset.pTruth.data(), dataset.pTruth.data(), cube, num_words);
            status = sat_solver_addclause(_sat, divisor_literals.data(), divisor_literals.data() + divisor_literals.size());
        }
        
        // Store the counter example
        for (std::size_t i = 0; i < _divisor_sat_var.size(); ++i) {
            if (var_values[i] ^ sat_solver_var_value(_sat, _divisor_sat_var[i])) {
                auto &sign = _divisor_counter_examples_buffer[i];
                Abc_InfoXorBit((unsigned *)&sign, _num_counter_examples);
            }
        }
        ++_num_counter_examples;
        return SFM_SAT_SAT;
    }

    word ResubstitutionSolver::ComputeInterpolant2() {
        auto helper = [&](auto &divisor_indices, word truth[2]) {
            // collect fanins
            for (Obj fanin : _window->Pivot().Fanins()) {
                divisor_indices.push_back(NodeToSatVar(fanin.Index()));
            }

            truth[0] = 0;
            truth[1] = 0;
            const auto num_vars = sat_solver_nvars(_sat);
            const auto pivot_var_idx = NodeToSatVar(_window->Pivot().Index());

            sat_solver_setnvars(_sat, num_vars + 1);
            auto new_lit = Abc_Var2Lit(num_vars, 0);

            std::vector<int> var_values;
            var_values.resize((1 << divisor_indices.size()) * _divisor_sat_var.size(), -1);

            int mint = 0;

            while (true) {
                // find care minterm
                auto status = sat_solver_solve(_sat, &new_lit, &new_lit + 1, _window->GetParameters()->nBTLimit, 0, 0, 0);
                if (status == l_Undef) {
                    return l_Undef;
                }
                else if (status == l_False) {
                    return l_False;
                }

                // collect values
                mint = 0;
                int on_set = sat_solver_var_value(_sat, pivot_var_idx);

                std::vector<int> divisor_literals;
                divisor_literals.push_back(Abc_LitNot(new_lit));
                divisor_literals.push_back(Abc_LitNot(sat_solver_var_literal(_sat, pivot_var_idx)));

                for (std::size_t i = 0; i < divisor_indices.size(); ++i) {
                    auto div_idx = divisor_indices[i];
                    divisor_literals.push_back(Abc_LitNot(sat_solver_var_literal(_sat, div_idx)));

                    if (sat_solver_var_value(_sat, div_idx)) {
                        mint |= 1 << i;
                    }
                }

                if (truth[!on_set] & ((word)1 << mint)) {
                    break;
                }
                truth[on_set] |= ((word)1 << mint);

                // remember variable values
                for (std::size_t i = 0; i < _divisor_sat_var.size(); ++i) {
                    var_values[mint * _divisor_sat_var.size() + i] = sat_solver_var_value(_sat, _divisor_sat_var[i]);
                }

                status = sat_solver_addclause(_sat, divisor_literals.data(), divisor_literals.data() + divisor_literals.size());
                if (status == 0) {
                    return l_False;
                }
            }
            
            // store the counter example
            for (std::size_t i = 0; i < _divisor_sat_var.size(); ++i) {
                int value = var_values[mint * _divisor_sat_var.size() + i];

                if (value ^ sat_solver_var_value(_sat, _divisor_sat_var[i])) {
                    auto &sign = _divisor_counter_examples_buffer[i];
                    Abc_InfoXorBit((unsigned *)&sign, _num_counter_examples);
                }
            }
            ++_num_counter_examples;
            return l_True;
        };

        std::vector<Obj::IndexType> divisor_indices;
        word truth[2];

        const auto result = helper(divisor_indices, truth);
        if (result == l_Undef) {
            return SFM_SAT_UNDEC;
        }
        else if (result == l_True) {
            return SFM_SAT_SAT;
        }

        truth[0] = Abc_Tt6Stretch(truth[0], divisor_indices.size());
        truth[1] = Abc_Tt6Stretch(truth[1], divisor_indices.size());

        int num_pos_cubes = 0;
        int num_neg_cubes = 0;
        auto res_pos = Abc_Tt6Isop(truth[1], ~truth[0], divisor_indices.size(), &num_pos_cubes);
        auto res_neg = Abc_Tt6Isop(truth[0], ~truth[1], divisor_indices.size(), &num_neg_cubes);

        return num_pos_cubes <= num_neg_cubes ? res_pos : ~res_neg;
    }

} // namespace EfxAbc::Sfm::Impl