#include "psfmImpl.hpp"
#include "base/main/mainInt.h"

#include "efxProf.h"
#include <charconv>

namespace EfxAbc::Sfm {

    namespace {

        std::optional<std::size_t> StrToSize(std::string_view str) {
            std::size_t result;
            const auto begin = str.data();
            const auto end = begin + str.size();

            auto [p, ec] = std::from_chars(begin, end, result);

            if (ec == std::errc() && p == end) {
                return result;
            }
            return std::nullopt;
        }
        
        int Mfs2Command(Abc_Frame_t* pAbc, int argc, char** argv) {
            EfxProf &prof = EfxProf::get();
            static const auto group_id = prof.RegisterGroup("EfxAbc::Sfm");
            EfxScopedProf scoped_sweep_prof(prof, group_id);

            int fIndDCs = 0;
            int fUseAllFfs = 0;
            int nFramesAdd = 0;

            auto PrintUsage = [&]() {
                const auto &default_params = Parameters::DefaultSettings();

                Abc_Print(-2, "usage: pmfs [-GWFDMLCZNI <num>] [-daeijlvwh]\n");
                Abc_Print(-2, "\t           performs don't-care-based optimization of logic networks\n");
                Abc_Print(-2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n",             default_params->nTfoLevMax);
                Abc_Print(-2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n",                default_params->nFanoutMax);
                Abc_Print(-2, "\t-D <num> : the max depth nodes to try (0 = no limit) [default = %d]\n",                   default_params->nDepthMax);
                Abc_Print(-2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n",    default_params->nWinSizeMax);
                Abc_Print(-2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", default_params->nGrowthLevel);
                Abc_Print(-2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n",   default_params->nBTLimit);
                Abc_Print(-2, "\t-Z <num> : treat the first <num> logic nodes as fixed (0 = none) [default = %d]\n",       default_params->nFirstFixed);
                Abc_Print(-2, "\t-N <num> : the max number of nodes to try (0 = all) [default = %d]\n",                    default_params->nNodesMax);
                Abc_Print(-2, "\t-d       : toggle performing redundancy removal [default = %s]\n",                        default_params->fRrOnly? "yes": "no");
                Abc_Print(-2, "\t-a       : toggle minimizing area or area+edges [default = %s]\n",                        default_params->fArea? "area": "area+edges");
                Abc_Print(-2, "\t-e       : toggle high-effort resubstitution [default = %s]\n",                           default_params->fMoreEffort? "yes": "no");
                Abc_Print(-2, "\t-i       : toggle using inductive don't-cares [default = %s]\n",                          fIndDCs? "yes": "no");
                Abc_Print(-2, "\t-j       : toggle using all flops when \"-i\" is enabled [default = %s]\n",               fUseAllFfs? "yes": "no");
                Abc_Print(-2, "\t-I       : the number of additional frames inserted [default = %d]\n",                    nFramesAdd);
                Abc_Print(-2, "\t-l       : toggle deriving don't-cares [default = %s]\n",                                 default_params->fUseDcs? "yes": "no");
                Abc_Print(-2, "\t-v       : toggle printing optimization summary [default = %s]\n",                        default_params->fVerbose? "yes": "no");
                Abc_Print(-2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n",                default_params->fVeryVerbose? "yes": "no");
                Abc_Print(-2, "\t-h       : print the command usage\n");
            };

            // set defaults
            Parameters params;
            Extra_UtilGetoptReset();

            int c = 0;
            while ((c = Extra_UtilGetopt(argc, argv, "GWFDMLCZNIdaeijlvwh")) != EOF) {
                switch (c) {
                case 'W':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-W\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nTfoLevMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nTfoLevMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'F':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-F\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nFanoutMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nFanoutMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'D':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-D\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nDepthMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nDepthMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'M':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-M\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nWinSizeMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nWinSizeMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'L':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-L\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nGrowthLevel = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nGrowthLevel < -ABC_INFINITY || params->nGrowthLevel > ABC_INFINITY) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'C':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-C\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nBTLimit = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nBTLimit < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'Z':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-Z\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nFirstFixed = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nFirstFixed < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'N':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-N\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nNodesMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nNodesMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'I':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-I\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    nFramesAdd = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (nFramesAdd < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'd':
                    params->fRrOnly ^= 1;
                    break;
                case 'a':
                    params->fArea ^= 1;
                    break;
                case 'e':
                    params->fMoreEffort ^= 1;
                    break;
                case 'i':
                    fIndDCs ^= 1;
                    break;
                case 'j':
                    fUseAllFfs ^= 1;
                    break;
                case 'l':
                    params->fUseDcs ^= 1;
                    break;
                case 'v':
                    params->fVerbose ^= 1;
                    break;
                case 'w':
                    params->fVeryVerbose ^= 1;
                    break;
                case 'h':
                    [[fallthrough]];
                default:
                    PrintUsage();
                    return 1;
                }
            }

            Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

            if (pNtk == nullptr) {
                Abc_Print(-1, "Empty network.\n");
                return 1;
            }
            if (!Abc_NtkIsLogic(pNtk)) {
                Abc_Print(-1, "This command can only be applied to a logic network.\n");
                return 1;
            }

            if (fIndDCs) {
                if (fUseAllFfs) {
                    pAbc->nIndFrames = 1;
                    Vec_IntFreeP(&pAbc->vIndFlops);
                    pAbc->vIndFlops = Vec_IntAlloc(Abc_NtkLatchNum(pNtk));
                    Vec_IntFill(pAbc->vIndFlops, Abc_NtkLatchNum(pNtk), 1);
                }
                if (pAbc->nIndFrames <= 0) {
                    Abc_Print(-1, "The number of k-inductive frames is not specified.\n");
                    return 0;
                }
                if (pAbc->vIndFlops == nullptr) {
                    Abc_Print(-1, "The set of k-inductive flops is not specified.\n");
                    return 0;
                }

                if (Vec_IntSize(pAbc->vIndFlops) != Abc_NtkLatchNum(pNtk)) {
                    Abc_Print(-1, "The saved flop count (%d) does not match that of the current network (%d).\n",
                              Vec_IntSize(pAbc->vIndFlops), Abc_NtkLatchNum(pNtk));
                    return 0;
                }

                // modify the current network
                if (!ExecuteWithAbcNetworkAfterICheck(*pNtk, params, pAbc->nIndFrames, nFramesAdd, pAbc->vIndFlops)) {
                    Abc_Print(-1, "Resynthesis has failed.\n");
                    return 1;
                }

                if (fUseAllFfs) {
                    pAbc->nIndFrames = 0;
                    Vec_IntFreeP(&pAbc->vIndFlops);
                }
            }
            else {
                // modify the current network
                if (!ExecuteWithAbcNetwork(*pNtk, params)) {
                    Abc_Print(-1, "Resynthesis has failed.\n");
                    return 1;
                }
            }
            return 0;
        }

        int AmpersandMfsCommand(Abc_Frame_t* pAbc, int argc, char** argv) {
            EfxProf &prof = EfxProf::get();
            static const auto group_id = prof.RegisterGroup("EfxAbc::Sfm");
            EfxScopedProf scoped_sweep_prof(prof, group_id);

            auto PrintUsage = [&]() {
                const auto &default_params = Parameters::DefaultSettings();

                Abc_Print(-2, "usage: &pmfs [-GWFDMLCN <num>] [-daeblvwh]\n");
                Abc_Print(-2, "\t           performs don't-care-based optimization of logic networks\n");
                Abc_Print(-2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n",             default_params->nTfoLevMax);
                Abc_Print(-2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n",                default_params->nFanoutMax);
                Abc_Print(-2, "\t-D <num> : the max depth nodes to try (0 = no limit) [default = %d]\n",                   default_params->nDepthMax);
                Abc_Print(-2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n",    default_params->nWinSizeMax);
                Abc_Print(-2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", default_params->nGrowthLevel);
                Abc_Print(-2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n",   default_params->nBTLimit);
                Abc_Print(-2, "\t-N <num> : the max number of nodes to try (0 = all) [default = %d]\n",                    default_params->nNodesMax);
                Abc_Print(-2, "\t-d       : toggle performing redundancy removal [default = %s]\n",                        default_params->fRrOnly? "yes": "no");
                Abc_Print(-2, "\t-a       : toggle minimizing area or area+edges [default = %s]\n",                        default_params->fArea? "area": "area+edges");
                Abc_Print(-2, "\t-e       : toggle high-effort resubstitution [default = %s]\n",                           default_params->fMoreEffort? "yes": "no");
                Abc_Print(-2, "\t-b       : toggle preserving all white boxes [default = %s]\n",                           default_params->fAllBoxes? "yes": "no");
                Abc_Print(-2, "\t-l       : toggle deriving don't-cares [default = %s]\n",                                 default_params->fUseDcs? "yes": "no");
                Abc_Print(-2, "\t-v       : toggle printing optimization summary [default = %s]\n",                        default_params->fVerbose? "yes": "no");
                Abc_Print(-2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n",                default_params->fVeryVerbose? "yes": "no");
                Abc_Print(-2, "\t-h       : print the command usage\n");
            };

            // set defaults
            Parameters params;
            params->nTfoLevMax  =    5;
            params->nDepthMax   =  100;
            params->nWinSizeMax = 2000;
            Extra_UtilGetoptReset();

            int c = 0;
            while ((c = Extra_UtilGetopt(argc, argv, "GWFDMLCNdaeblvwh")) != EOF) {
                switch (c) {
                case 'W':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-W\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nTfoLevMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nTfoLevMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'F':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-F\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nFanoutMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nFanoutMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'D':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-D\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nDepthMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nDepthMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'M':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-M\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nWinSizeMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nWinSizeMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'L':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-L\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nGrowthLevel = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nGrowthLevel < 0 || params->nGrowthLevel > ABC_INFINITY) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'C':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-C\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nBTLimit = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nBTLimit < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'N':
                    if (globalUtilOptind >= argc) {
                        Abc_Print(-1, "Command line switch \"-N\" should be followed by an integer.\n");
                        PrintUsage();
                        return 1;
                    }
                    params->nNodesMax = atoi(argv[globalUtilOptind]);
                    globalUtilOptind++;
                    if (params->nNodesMax < 0) {
                        PrintUsage();
                        return 1;
                    }
                    break;
                case 'd':
                    params->fRrOnly ^= 1;
                    break;
                case 'a':
                    params->fArea ^= 1;
                    break;
                case 'e':
                    params->fMoreEffort ^= 1;
                    break;
                case 'b':
                    params->fAllBoxes ^= 1;
                    break;
                case 'l':
                    params->fUseDcs ^= 1;
                    break;
                case 'v':
                    params->fVerbose ^= 1;
                    break;
                case 'w':
                    params->fVeryVerbose ^= 1;
                    break;
                case 'h':
                    [[fallthrough]];
                default:
                    PrintUsage();
                    return 1;
                }
            }

            if (pAbc->pGia == nullptr) {
                Abc_Print(-1, "&pmfs: There is no AIG.\n");
                return 0;
            }
            if (Gia_ManBufNum(pAbc->pGia)) {
                Abc_Print(-1, "&pmfs: This command does not work with barrier buffers.\n");
                return 1;
            }
            if (!Gia_ManHasMapping(pAbc->pGia)) {
                Abc_Print(-1, "&pmfs: The current AIG has no mapping.\n");
                return 0;
            }
            if (Gia_ManLutSizeMax(pAbc->pGia) > 15) {
                Abc_Print(-1, "&pmfs: The current mapping has nodes with more than 15 inputs. Cannot use \"mfs\".\n");
                return 0;
            }

            Gia_Man_t* pTemp = nullptr;
            if (Gia_ManRegNum(pAbc->pGia) == 0) {
                pTemp = ExecuteWithGiaNetwork(*pAbc->pGia, params);
            }
            else {
                int nRegs = Gia_ManRegNum(pAbc->pGia);
                pAbc->pGia->nRegs = 0;
                pTemp = ExecuteWithGiaNetwork(*pAbc->pGia, params);
                Gia_ManSetRegNum(pAbc->pGia, nRegs);
                Gia_ManSetRegNum(pTemp, nRegs);
            }

            EFX_HARD_ASSERT(pTemp != nullptr);
            Abc_FrameUpdateGia(pAbc, pTemp);

            return 0;
        }

    } // <anonymous> namespace

    void RegisterMfs2Command(RegisterCommandFunc regfunc) {
        regfunc(Mfs2Command, true);
    }

    void RegisterAmpersandMfsCommand(RegisterCommandFunc regfunc) {
        regfunc(AmpersandMfsCommand, false);
    }

    void SetStrictCompliance(bool b) {
        Parameters::DefaultSettings().StrictCompliance(b);
    }

} // namespace EfxAbc::Sfm