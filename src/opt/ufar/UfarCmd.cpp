/*
 * UifCmd.cpp
 *
 *  Created on: Aug 25, 2015
 *      Author: Yen-Sheng Ho
 */

#include <iostream>
#include <iomanip>
#include <climits>
#include <regex>

#include "base/wlc/wlc.h"
#include "opt/ufar/UfarCmd.h"
#include "opt/ufar/UfarMgr.h"
#include "opt/untk/NtkNtk.h"
#include "opt/util/util.h"

ABC_NAMESPACE_IMPL_START

using namespace std;

static UFAR::UfarManager ufar_manager;

static int Abc_CommandTest( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAnalyzeCex( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCreateAbstraction( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCreateMiter( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandProveUsingUif( Abc_Frame_t * pAbc, int argc, char ** argv );

static inline Wlc_Ntk_t * Wlc_AbcGetNtk( Abc_Frame_t * pAbc )                       { return (Wlc_Ntk_t *)pAbc->pAbcWlc;                      }
static inline void        Wlc_AbcFreeNtk( Abc_Frame_t * pAbc )                      { if ( pAbc->pAbcWlc ) Wlc_NtkFree(Wlc_AbcGetNtk(pAbc));  }
static inline void        Wlc_AbcUpdateNtk( Abc_Frame_t * pAbc, Wlc_Ntk_t * pNtk )  { Wlc_AbcFreeNtk(pAbc); pAbc->pAbcWlc = pNtk;             }


void Ufar_Init(Abc_Frame_t *pAbc)
{
    //Cmd_CommandAdd( pAbc, "Word level Prove", "%%test",           Abc_CommandTest,              0 );
    //Cmd_CommandAdd( pAbc, "Word level Prove", "%%cex",            Abc_CommandAnalyzeCex,        0 );
    //Cmd_CommandAdd( pAbc, "Word level Prove", "%%abs",            Abc_CommandCreateAbstraction, 0 );
    Cmd_CommandAdd( pAbc, "Word level", "%ufar",          Abc_CommandProveUsingUif,     0 );
    //Cmd_CommandAdd( pAbc, "Word level Prove", "%%miter",          Abc_CommandCreateMiter,     0 );
}

static int Abc_CommandCreateMiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Wlc_Ntk_t * pNew = UFAR::CreateMiter(Wlc_AbcGetNtk(pAbc), 0);
    Wlc_AbcUpdateNtk(pAbc, pNew);
    return 0;
}

static int Abc_CommandCreateAbstraction( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Wlc_Ntk_t * pNew = ufar_manager.BuildCurrentAbstraction();
    Wlc_AbcUpdateNtk(pAbc, pNew);
    return 0;
}

static int Abc_CommandAnalyzeCex( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    if ( pAbc->pCex == NULL )
        {
        cout << "There is no CEX.\n";
        return 0;
    }

    // ufar_manager.GetOperatorsInCex(pAbc->pCex);
    ufar_manager.FindUifPairsUsingCex(pAbc->pCex);

    return 0;
}

static int Abc_CommandProveUsingUif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    if (Wlc_AbcGetNtk(pAbc) == NULL) {
        cout << "There is no current design.\n";
        return 0;
    }

    OptMgr opt_mgr(argv[0]);
    opt_mgr.AddOpt("--norm", ufar_manager.params.fNorm ? "yes" : "no", "", "toggle using data type normalization");
    opt_mgr.AddOpt("--adder", "no", "", "toggle including adders");
    opt_mgr.AddOpt("--cexmin", ufar_manager.params.fCexMin ? "yes" : "no", "", "toggle using CEX minimization");
    opt_mgr.AddOpt("--sim", "none", "str", "use simulation and specify its setting");
    opt_mgr.AddOpt("-v", to_string(ufar_manager.params.iVerbosity), "num", "specify verbosity level");
    opt_mgr.AddOpt("--seq", to_string(ufar_manager.params.nSeqLookBack), "num", "specify the number of look-back frames (0 = no sequential UIF)");
    opt_mgr.AddOpt("--profile", "no", "", "dump time distribution");
    opt_mgr.AddOpt("--pba_uif", ufar_manager.params.fPbaUif ? "yes" : "no", "", "toggle using proof-based refinement for UIF pairs");
    opt_mgr.AddOpt("--lazysim", ufar_manager.params.fLazySim ? "yes" : "no", "", "toggle applying UIF pairs based on simulation");
    opt_mgr.AddOpt("--pbasim", ufar_manager.params.fPbaSim ? "yes" : "no", "", "toggle combining pba and sim");
    opt_mgr.AddOpt("--pbacex", ufar_manager.params.fPbaCex ? "yes" : "no", "", "toggle combining pba and cex");
    opt_mgr.AddOpt("--satmin", ufar_manager.params.fSatMin ? "yes" : "no", "", "toggle using sat-min in pba");
    opt_mgr.AddOpt("--cbawb", ufar_manager.params.fCbaWb ? "yes" : "no", "", "toggle using cex-based refinement for white boxing");
    opt_mgr.AddOpt("--grey", ufar_manager.params.fGrey ? "yes" : "no", "", "toggle using grey-box constraints");
    opt_mgr.AddOpt("--grey2", to_string(ufar_manager.params.nGrey), "float", "specify the greyness threshold");
    opt_mgr.AddOpt("--dump", "none", "str", "specify file name");
    opt_mgr.AddOpt("--dump-abs", "none", "str", "specify file name");
    opt_mgr.AddOpt("--par", "none", "str", "use parallel solvers");
    opt_mgr.AddOpt("--dump_states", "none", "str", "specify the name for the states file");
    opt_mgr.AddOpt("--read_states", "none", "str", "specify the name for the states file");
    opt_mgr.AddOpt("--sp", ufar_manager.params.fSuper_prove ? "yes" : "no", "", "toggle using super_prove");
    opt_mgr.AddOpt("--simp", ufar_manager.params.fSimple ? "yes" : "no", "", "toggle using simple (prove)");
    opt_mgr.AddOpt("--syn", ufar_manager.params.fSyn ? "yes" : "no", "", "toggle using simple synthesis");
    opt_mgr.AddOpt("--pth", ufar_manager.params.fPthread ? "yes" : "no", "", "toggle using pthreads");
    opt_mgr.AddOpt("--onewb", to_string(ufar_manager.params.iOneWb), "int", "specify the mode for one-white-boxing");
    opt_mgr.AddOpt("--timeout", to_string(ufar_manager.params.nTimeout), "num", "specify the timeout (sec)");
    opt_mgr.AddOpt("--exp", to_string(ufar_manager.params.iExp), "int", "specify the exp mode");
    opt_mgr.AddOpt("--miter", "yes", "", "toggle mitering the problem");
    opt_mgr.AddOpt("--under", "-1", "num", "try under-approximation with the given size");
    if(!opt_mgr.Parse(argc, argv)) {
        opt_mgr.PrintUsage();
        cout << "\n       This command was developed by Yen-Sheng Ho at UC Berkeley in 2015.\n";
        cout << "       https://people.eecs.berkeley.edu/~alanmi/publications/2016/fmcad16_uif.pdf \n"; 
        return 0;
    }

    if(opt_mgr["--norm"])
        ufar_manager.params.fNorm ^= 1;
    if(opt_mgr["--cexmin"])
        ufar_manager.params.fCexMin ^= 1;
    if(opt_mgr["--pba_uif"])
        ufar_manager.params.fPbaUif ^= 1;
    if(opt_mgr["--pbasim"])
        ufar_manager.params.fPbaSim ^= 1;
    if(opt_mgr["--pbacex"])
        ufar_manager.params.fPbaCex ^= 1;
    if(opt_mgr["--satmin"])
        ufar_manager.params.fSatMin ^= 1;
    if(opt_mgr["--cbawb"])
        ufar_manager.params.fCbaWb ^= 1;
    if(opt_mgr["--grey"])
        ufar_manager.params.fGrey ^= 1;
    if(opt_mgr["--grey2"])
        ufar_manager.params.nGrey = stof(opt_mgr.GetOptVal("--grey2"));
    if(opt_mgr["--sp"])
        ufar_manager.params.fSuper_prove ^= 1;
    if(opt_mgr["--simp"])
        ufar_manager.params.fSimple ^= 1;
    if(opt_mgr["--syn"])
        ufar_manager.params.fSyn ^= 1;
    if(opt_mgr["--pth"])
        ufar_manager.params.fPthread ^= 1;
    if(opt_mgr["--onewb"])
        ufar_manager.params.iOneWb = stoi(opt_mgr.GetOptVal("--onewb"));
    if(opt_mgr["--exp"])
        ufar_manager.params.iExp = stoi(opt_mgr.GetOptVal("--exp"));
    if(opt_mgr["--par"])
        ufar_manager.params.parSetting = opt_mgr.GetOptVal("--par");
    if(opt_mgr["--sim"])
        ufar_manager.params.simSetting = opt_mgr.GetOptVal("--sim");
    if(opt_mgr["--dump_states"]) {
        smatch sub_match;
        string option = opt_mgr.GetOptVal("--dump_states");
        if(regex_search(option, sub_match, regex(R"(/?(\w+\.v)$)")))
            ufar_manager.params.fileStatesOut = sub_match[1].str();
        else
            ufar_manager.params.fileStatesOut = opt_mgr.GetOptVal("--dump_states");
    }
    if(opt_mgr["--read_states"])
        ufar_manager.params.fileStatesIn = opt_mgr.GetOptVal("--read_states");
    if(opt_mgr["--lazysim"])
        ufar_manager.params.fLazySim ^= 1;
    if(opt_mgr["-v"])
        ufar_manager.params.iVerbosity = stoi(opt_mgr.GetOptVal("-v"));
    if(opt_mgr["--timeout"])
        ufar_manager.params.nTimeout = stoi(opt_mgr.GetOptVal("--timeout"));
    if(opt_mgr["--seq"])
        ufar_manager.params.nSeqLookBack = stoi(opt_mgr.GetOptVal("--seq"));
    if(opt_mgr["--dump-abs"]) {
        smatch sub_match;
        string option = opt_mgr.GetOptVal("--dump-abs");
        if(regex_search(option, sub_match, regex(R"(/?(\w+)\.v$)")))
            ufar_manager.params.fileAbs = sub_match[1].str();
        else
            ufar_manager.params.fileAbs = opt_mgr.GetOptVal("--dump");
    }
    if(opt_mgr["--dump"]) {
        smatch sub_match;
        string option = opt_mgr.GetOptVal("--dump");
        if(regex_search(option, sub_match, regex(R"(/?(\w+\.v)$)")))
            ufar_manager.params.fileName = sub_match[1].str();
        else
            ufar_manager.params.fileName = opt_mgr.GetOptVal("--dump");
    }

    // ufar_manager.DumpParams();
    LogT::prefix = "UIF_PROVE";

    set<unsigned> set_op_types;
    set_op_types.insert(WLC_OBJ_ARI_MULTI);
    if (opt_mgr["--adder"])
        set_op_types.insert(WLC_OBJ_ARI_ADD);
    if (!UFAR::HasOperator(Wlc_AbcGetNtk(pAbc), set_op_types)) {
        cout << "There is no operator for UIF.\n";
        return 0;
    }

    Wlc_Ntk_t * pNew = NULL;
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    if (!opt_mgr["--miter"]) {
        if (Wlc_NtkPoNum(Wlc_AbcGetNtk(pAbc)) != 2) {
            cout << "The current design doesn't have dual outputs.\n";
            return 0;
        }
        pNew = UFAR::CreateMiter(Wlc_AbcGetNtk(pAbc), 0);
        Wlc_AbcUpdateNtk(pAbc, pNew);
    }

    if (ufar_manager.params.fNorm) {
        pNew = UFAR::NormalizeDataTypes(Wlc_AbcGetNtk(pAbc), set_op_types, true);
        Wlc_AbcUpdateNtk(pAbc, pNew);
    }

    if (opt_mgr["--under"]) {
        pNew = UFAR::MakeUnderApprox(Wlc_AbcGetNtk(pAbc), stoi(opt_mgr.GetOptVal("--under")));
        Wlc_AbcUpdateNtk(pAbc, pNew);
        pNew = UFAR::MakeUnderApprox2(Wlc_AbcGetNtk(pAbc), set_op_types, stoi(opt_mgr.GetOptVal("--under")));
        Wlc_AbcUpdateNtk(pAbc, pNew);
        Wlc_WriteVer(Wlc_AbcGetNtk(pAbc), "UND.v", 0, 0);
    }

    Gia_Man_t * pGia = UFAR::BitBlast(Wlc_AbcGetNtk(pAbc));
    Gia_ManPrintStats( pGia, NULL );
    Gia_ManStop( pGia );

    ufar_manager.Initialize(Wlc_AbcGetNtk(pAbc), set_op_types);

    int ret = ufar_manager.PerformUIFProve(t1);
    if (ret == 1) {
        LOG(0) << "Proved by UIF (UNSAT).";
    } else if (ret == 0) {
        LOG(0) << "Falsified by UIF (SAT).";
    } else {
        LOG(0) << "Undecided by UIF.";
    }

    gettimeofday(&t2, NULL);
    unsigned tTotal = elapsed_time_usec(t1, t2);
    if(opt_mgr["--profile"]) {
        auto log_profile = [&](const string& str, abctime t) {
          LOG(1) << str << " time = " << fixed << setprecision(4) << setw(8) << (double)t/1000000 << " sec [" << setw(7) << (double)t/tTotal*100 << "%]";
        };
        log_profile("BLSolver  ", ufar_manager.profile.tBLSolver);
        log_profile("UifRefine ", ufar_manager.profile.tUifRefine);
        log_profile("WbRefine  ", ufar_manager.profile.tWbRefine);
        log_profile("UifSim    ", ufar_manager.profile.tUifSim);
        log_profile("GbRefine  ", ufar_manager.profile.tGbRefine);
    }

    LOG(0) << "Time = " << setprecision(5) << ((double) (tTotal) / 1000000) << " sec";

    return 0;
}

static int Abc_CommandTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    LogT::prefix = "TEST::";
    OptMgr opt_mgr(argv[0]);
    opt_mgr.AddOpt("--ntk", "none", "str", "specify the file name (*.aig) for the input network");
    opt_mgr.AddOpt("--adder", "no", "", "toggle including adders");
    if(!opt_mgr.Parse(argc, argv)) {
        opt_mgr.PrintUsage();
        return 0;
    }
    set<unsigned> set_op_types;
    set_op_types.insert(WLC_OBJ_ARI_MULTI);
    if(opt_mgr["--adder"]) {
        set_op_types.insert(WLC_OBJ_ARI_ADD);
    }
    Wlc_Ntk_t * pNew = UFAR::AddConstFlops(Wlc_AbcGetNtk(pAbc), set_op_types);
    Wlc_AbcUpdateNtk(pAbc, pNew);
    return 0;

#if 0
    opt_mgr.AddOpt("--ntk", "none", "str", "specify the file name (*.aig) for the input network");
    opt_mgr.AddOpt("--inv", "none", "str", "specify the file name (*.pla) for the invariant");
    if(!opt_mgr.Parse(argc, argv)) {
        opt_mgr.PrintUsage();
        return 0;
    }

    string nameNtk = opt_mgr.GetOptVal("--ntk");
    string nameInv = opt_mgr.GetOptVal("--inv");
    UFAR::TestInvariant(nameNtk, nameInv);
#endif
#if 0
    set<unsigned> set_op_types;
    set_op_types.insert(WLC_OBJ_ARI_MULTI);

    OptMgr opt_mgr(argv[0]);
    opt_mgr.AddOpt("--cube", "no", "", "toggle using cubes for interpolants");
    if(!opt_mgr.Parse(argc, argv)) {
        opt_mgr.PrintUsage();
        return 0;
    }

    UFAR::TestITP(Wlc_AbcGetNtk(pAbc), set_op_types, opt_mgr["--cube"]);
#endif
#if 0
     if (  Wlc_AbcGetNtk(pAbc) == NULL ) {
         cout << "There is no current design.\n";
         return 0;
     }

     if (Wlc_NtkPoNum(Wlc_AbcGetNtk(pAbc)) != 2) {
         cout << "The current design doesn't have dual outputs.\n";
         return 0;
     }

     set<unsigned> set_op_types;
     set_op_types.insert(WLC_OBJ_ARI_MULTI);
     if (!UFAR::HasOperator(Wlc_AbcGetNtk(pAbc), set_op_types)) {
         cout << "There is no operator for UIF.\n";
         return 0;
     }

     Wlc_Ntk_t * pNew = NULL;

     pNew = UFAR::CreateMiter(Wlc_AbcGetNtk(pAbc), 0);
     Wlc_AbcUpdateNtk(pAbc, pNew);

     pNew = UFAR::NormalizeDataTypes(Wlc_AbcGetNtk(pAbc), set_op_types, true);
     Wlc_AbcUpdateNtk(pAbc, pNew);

     ufar_manager.Initialize(Wlc_AbcGetNtk(pAbc), set_op_types);
     ufar_manager.DumpMgrInfo();

     pNew = ufar_manager.BuildCurrentAbstraction();
     Wlc_AbcUpdateNtk(pAbc, pNew);


    return 0;
#endif
}

ABC_NAMESPACE_IMPL_END
