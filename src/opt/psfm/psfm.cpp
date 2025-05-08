#include "psfmImpl.hpp"
#include "base/abc/abc.h"
#include "base/io/ioAbc.h"

extern "C" {
    void Abc_NtkInsertMfs(Abc_Ntk_t*, Sfm_Ntk_t*);
    Abc_Ntk_t* Abc_NtkUnrollAndDrop(Abc_Ntk_t*, int, int, Vec_Int_t*, int*);
    void Abc_NtkReinsertNodes(Abc_Ntk_t*, Abc_Ntk_t*, int);
    Gia_Man_t* Gia_ManInsertMfs(Gia_Man_t*, Sfm_Ntk_t*, int);
} // extern "C"

namespace EfxAbc::Sfm {

    Parameters::Parameters(int) {
        Sfm_ParSetDefault(&_impl);
        _very_verbose = false;
    }

    Parameters::Parameters() {
        operator=(DefaultSettings());
    }

    Parameters &Parameters::DefaultSettings() {
        static Parameters global_inst{ 0 };
        return global_inst;
    }

    bool ExecuteWithAbcNetwork(Abc_Ntk_t &abc_network, Parameters &params) {
        EFX_HARD_ASSERT(Abc_NtkIsLogic(&abc_network));
        Abc_NtkSweep(&abc_network, 0);

        const auto max_fanins = Abc_NtkGetFaninMax(&abc_network);
        if (max_fanins > 15) {
            Abc_Print(1, "Currently \"mfs\" cannot process the network containing nodes with more than 15 fanins.\n");
            return true;
        }
        if (!Abc_NtkHasSop(&abc_network)) {
            if (!Abc_NtkToSop(&abc_network, -1, ABC_INFINITY)) {
                printf("Conversion to SOP has failed due to low resource limit.\n");
                return false;
            }
        }

        Impl::Network sfm_network{ abc_network, params };
        
        const auto report = Impl::ExecuteImpl(sfm_network, params);
        DIAG_GBL_POST_DEBUG("EfxAbc::Sfm removed {} fanin(s), removed {} node(s), changed {} node(s)",
                            report.num_deleted_fanins, report.num_deleted_nodes, report.num_changed_nodes);

        if (report.num_changed_nodes > 0) {
            Abc_NtkInsertMfs(&abc_network, &sfm_network.GetImpl());
        }
        return true;
    }
    
    bool ExecuteWithAbcNetworkAfterICheck(Abc_Ntk_t &abc_network, Parameters &params, int num_frames,
                                          int num_added_frames, Vec_Int_t* vFlops)
    {
        EFX_HARD_ASSERT(Abc_NtkIsLogic(&abc_network));
        
        const auto max_fanins = Abc_NtkGetFaninMax(&abc_network);
        if (max_fanins > 15) {
            Abc_Print(1, "Currently \"mfs\" cannot process the network containing nodes with more than 15 fanins.\n");
            return false;
        }
        if (!Abc_NtkHasSop(&abc_network)) {
            if (!Abc_NtkToSop(&abc_network, -1, ABC_INFINITY)) {
                printf("Conversion to SOP has failed due to low resource limit.\n");
                return false;
            }
        }

        // derive unfolded network
        {
            int pivot = 0;
            Impl::ScopedAbcNetwork unrolled_abc_network = Abc_NtkUnrollAndDrop(&abc_network, num_frames, num_added_frames, vFlops, &pivot);
            Io_WriteBlifLogic(unrolled_abc_network.Get(), "unroll_dump.blif", 0);

            {
                Impl::Network sfm_network{ *unrolled_abc_network, params, pivot };
            
                const auto report = Impl::ExecuteImpl(sfm_network, params);
                DIAG_GBL_POST_DEBUG("EfxAbc::Sfm removed {} fanin(s), removed {} node(s), changed {} node(s)",
                                    report.num_deleted_fanins, report.num_deleted_nodes, report.num_changed_nodes);

                if (report.num_changed_nodes > 0) {
                    Abc_NtkInsertMfs(unrolled_abc_network.Get(), &sfm_network.GetImpl());
                    Abc_NtkReinsertNodes(&abc_network, unrolled_abc_network.Get(), pivot);
                }
            }
        }

        // perform final sweep
        Abc_NtkSweep(&abc_network, 0);
        if (!Abc_NtkHasSop(&abc_network)) {
            Abc_NtkToSop(&abc_network, -1, ABC_INFINITY);
        }

        return true;
    }

    Gia_Man_t* ExecuteWithGiaNetwork(Gia_Man_t &gia_network, Parameters &params) {
        EFX_HARD_ASSERT(Gia_ManRegNum(&gia_network) == 0);
        EFX_HARD_ASSERT(gia_network.vMapping != nullptr);

        if (gia_network.pManTime != nullptr && gia_network.pAigExtra != nullptr) {
            Abc_Print(1, "Timing manager is given but there is no GIA of boxes.\n");
            return nullptr;
        }
        if (gia_network.pManTime != nullptr && gia_network.pAigExtra != nullptr && Gia_ManCiNum(gia_network.pAigExtra) > 15) {
            Abc_Print(1, "Currently \"&pmfs\" cannot process the network containing white-boxes with more than 15 inputs.\n");
            return nullptr;
        }

        // count fanouts
        const auto nFaninMax = Gia_ManLutSizeMax(&gia_network);
        if (nFaninMax > 15) {
            Abc_Print(1, "Currently \"&pmfs\" cannot process the network containing nodes with more than 15 fanins.\n");
            return NULL;
        }

        // collect information
        Impl::Network sfm_network{ gia_network, params };

        // perform optimization
        const auto report = Impl::ExecuteImpl(sfm_network, params);
        DIAG_GBL_POST_DEBUG("EfxAbc::Sfm removed {} fanin(s), removed {} node(s), changed {} node(s)",
                            report.num_deleted_fanins, report.num_deleted_nodes, report.num_changed_nodes);

        if (report.num_changed_nodes == 0) {
            auto new_gia_network = Gia_ManDup(&gia_network);
            new_gia_network->vMapping = Vec_IntDup(gia_network.vMapping);
            Gia_ManTransferTiming(new_gia_network, &gia_network);

            return new_gia_network;
        }
        else {
            return Gia_ManInsertMfs(&gia_network, &sfm_network.GetImpl(), params->fAllBoxes);
        }
    }

} // namespace EfxAbc::Sfm