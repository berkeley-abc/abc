#pragma once

#include "EfxAbcSfm.hpp"
#include "EfxAbcContainers.hpp"
#include "opt/sfm/sfm.h"
#include "base/main/abcapis.h"
#include "base/cmd/cmd.h"
#include <type_traits>

namespace EfxAbc::Sfm {

    static_assert(std::is_same_v<CommandFuncType, Cmd_CommandFuncType>);

    class Parameters {
        Sfm_Par_t _impl;
        bool _strict_compliance = false;
        bool _very_verbose = false;

        Parameters(int);

    public:
        Parameters();
        static Parameters &DefaultSettings();

        Sfm_Par_t* operator->() noexcept { return &_impl; }
        const Sfm_Par_t* operator->() const noexcept { return &_impl; }

        bool StrictCompliance() const noexcept { return _strict_compliance; }
        void StrictCompliance(bool b) noexcept { _strict_compliance = b; }

        bool VeryVerbose() const noexcept { return _very_verbose; }
        void VeryVerbose(bool b) noexcept { _very_verbose = b; }

        Sfm_Par_t &GetImpl() noexcept { return _impl; }
        const Sfm_Par_t &GetImpl() const noexcept { return _impl; }
    };

    bool ExecuteWithAbcNetwork(Abc_Ntk_t &network, Parameters &params);

    bool ExecuteWithAbcNetworkAfterICheck(Abc_Ntk_t &network, Parameters &params, int num_frames,
                                          int num_added_frames, Vec_Int_t* vFlops);

    Gia_Man_t* ExecuteWithGiaNetwork(Gia_Man_t &network, Parameters &params);

} // namespace EfxAbc::Sfm