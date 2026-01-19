/*
 * UifMgr.h
 *
 *  Created on: Aug 25, 2015
 *      Author: Yen-Sheng Ho
 */

#ifndef SRC_EXT2_UIF_UIFMGR_H_
#define SRC_EXT2_UIF_UIFMGR_H_

#include <set>
#include <string>
#include <vector>
#include <unordered_map>
#include <sstream>
#include <iostream>
#include <memory>
#ifdef _WIN32
// Define timeval before windows.h to prevent winsock.h forward declaration conflicts
#ifndef _TIMEVAL_DEFINED
#define _TIMEVAL_DEFINED
struct timeval {
    long tv_sec;
    long tv_usec;
};
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <sys/time.h>
#endif

#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_CXX_HEADER_START

typedef struct Wlc_Ntk_t_ Wlc_Ntk_t;
typedef struct Abc_Cex_t_ Abc_Cex_t;
typedef struct Gia_Man_t_ Gia_Man_t;

namespace UFAR {

using VecVecInt = std::vector<std::vector<int> >;
using VecVecStr = std::vector<std::vector<std::string> >;
using VecChar = std::vector<char>;
using VecStr = std::vector<std::string>;
using IntPair = std::pair<int, int>;

struct OperatorID;
struct UifPair;
class Greyness;
using  UIF_PAIR = UifPair;

class SimUifPairFinder;
class CexUifPairFinder;

class UfarManager {
    public:
        struct Params {
            Params();
            bool     fCexMin;
            bool     fPbaUif;
            bool     fLazySim;
            bool     fPbaSim;
            bool     fPbaCex;
            bool     fSatMin;
            bool     fCbaWb;
            bool     fGrey;
            float    nGrey;
            bool     fNorm;
            bool     fSuper_prove;
            bool     fSimple;
            bool     fSyn;
            bool     fPthread;
            int      iOneWb;
            int      iExp;
            unsigned nConstraintLimit;
            unsigned iVerbosity;
            unsigned nSeqLookBack;
            unsigned nTimeout;
            std::string simSetting;
            std::string parSetting;
            std::string fileName;
            std::string fileAbs;
            std::string fileStatesOut;
            std::string fileStatesIn;
        };
        struct Profile {
            Profile() : tBLSolver(0), tUifRefine(0), tWbRefine(0), tUifSim(0), tGbRefine(0) {}
            unsigned tBLSolver;
            unsigned tUifRefine;
            unsigned tWbRefine;
            unsigned tUifSim;
            unsigned tGbRefine;
        };

        UfarManager();
        ~UfarManager();

        void Initialize(Wlc_Ntk_t * pNtk, const std::set<unsigned>& types);

        Wlc_Ntk_t * BuildCurrentAbstraction();
        Wlc_Ntk_t * ApplyUifConstraints(Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids);
        void        FindUifPairsUsingCex(Abc_Cex_t * pCex, Abc_Cex_t ** ppCex = NULL);
        void        FindUifPairsUsingSim();
        void        DetermineWhiteBoxes(Abc_Cex_t * pCex);
        void        DetermineGreyness(Abc_Cex_t * pCex);

        int         VerifyCurrentAbstraction(Abc_Cex_t ** ppCex);
        int         PerformUIFProve(const timeval& timer);

        void        DumpMgrInfo() const;
        void        DumpParams() const;
        void        GetOperatorsInCex(Abc_Cex_t *pCex, VecVecStr* pRes);

        Params      params;
        Profile     profile;

    private:
        Wlc_Ntk_t * _abstract_operators(Wlc_Ntk_t * pNtk, const std::vector<int>& vec_ids) const;

        Wlc_Ntk_t * _introduce_choices(std::vector<unsigned>& vec_choice2idx, bool fBlack);
        Wlc_Ntk_t * _introduce_bitwise_choices(std::vector<IntPair>& vec_choice2idx);
        Wlc_Ntk_t * _set_up_constraints(std::vector<int>& vec_ids);
        void        _compute_core_choices(Wlc_Ntk_t * pChoice, Abc_Cex_t * pCex, std::vector<unsigned>& vec_cores, int num_sel_pis);
        void        _simulate();
        void        _perform_proof_based_white_boxing(Abc_Cex_t * pCex);
        void        _perform_proof_based_grey_boxing(Abc_Cex_t * pCex);
        void        _perform_cex_based_white_boxing();
        std::string _get_profile_uf_wb();
        void        _massage_state_b();
        void        _dump_states(const std::string& file);
        void        _read_states(const std::string& file);

        void        _shrink_final_abstraction();

        Wlc_Ntk_t *              _pOrigNtk;
        std::vector<std::string> _vec_orig_names;

        std::vector<int>                _vec_op_ids;
        std::vector<bool>               _vec_op_blackbox_marks;
        std::vector<std::vector<int> >  _vec_vec_op_ffs;
        std::vector<Greyness>           _vec_op_greyness;

        std::set<UIF_PAIR>       _set_uif_pairs;
        std::set<UIF_PAIR>       _set_uif_sim_pairs;
        std::set<OperatorID>     _set_prev_ops;

        Wlc_Ntk_t *              _pAbsWithAuxPos;

        std::unique_ptr<SimUifPairFinder>  _p_sim_mgr;
        std::unique_ptr<CexUifPairFinder>  _p_cex_mgr;

        std::ostringstream       _oss;

        struct timespec          _timeout;
};

}

ABC_NAMESPACE_CXX_HEADER_END

#endif /* SRC_EXT2_UIF_UIFMGR_H_ */
