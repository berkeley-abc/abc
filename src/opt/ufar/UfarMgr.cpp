/*
 * UifMgr.cpp
 *
 *  Created on: Aug 25, 2015
 *      Author: Yen-Sheng Ho
 */

#include <cstdio>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <map>
#include <algorithm>
#include <array>
#include <regex>

#include <sys/wait.h>

#include <base/wlc/wlc.h>
#include <sat/cnf/cnf.h>
#include <aig/gia/giaAig.h>
#include "opt/untk/NtkNtk.h"
#include "opt/util/util.h"
#include "UfarMgr.h"

ABC_NAMESPACE_IMPL_START

using namespace std;

namespace UFAR {

static inline unsigned log_level() {
    return LogT::loglevel;
}

static void split(const string &s, char delim, vector<string>& elems) {
    stringstream ss(s);
    string item;
    elems.clear();
    while (getline(ss, item, delim)) {
        elems.push_back(std::move(item));
    }
}

static void set_state_b(vector<bool>& vec_b_state, const string& str_state) {
    if (vec_b_state.size() != str_state.size()) {
        cerr << "Invalid initial states for B.\n" ;
        return;
    }

    for(size_t i = 0; i < str_state.size(); ++i) {
        char state = str_state[i];
        if (state == '0') {
            vec_b_state[i] = false;
        } else if (state == '1') {
            vec_b_state[i] = true;
        } else if (state != '1') {
            assert(false);
        }
    }
}

static void set_state_p(set<UIF_PAIR>& set_p_state, const string& str_pair) {
    vector<string> tokens;
    split(str_pair, ',', tokens);
    assert(tokens.size() == 5);
    set_p_state.insert(UIF_PAIR(OperatorID(stoi(tokens[0]), stoi(tokens[1])), OperatorID(stoi(tokens[2]), stoi(tokens[3])), tokens[4]=="1"));
}

static void readCexFromVec(Gia_Man_t * pGia, const vector<int>& vec_cex, Abc_Cex_t ** ppCex) {
    int nBits = vec_cex.size();
    int nRegs = Gia_ManRegNum(pGia);
    int nPis  = Gia_ManPiNum(pGia);

    int iFrame = (nBits - nRegs) / nPis - 1;
    assert(nBits == (nRegs + (iFrame + 1)*nPis));

    *ppCex = Abc_CexAlloc(nRegs, nPis, iFrame + 1);
    (*ppCex)->iFrame = iFrame;
    (*ppCex)->iPo = 0;
    for(size_t i = 0; i < vec_cex.size(); ++i) {
        if (vec_cex[i] == 1 || vec_cex[i] == 0) {
            if (vec_cex[i] == 1)
                Abc_InfoSetBit((*ppCex)->pData, i);
        }
    }
}

static Vec_Int_t * collect_boxes(const vector<int>& vec_ids, const vector<bool>& vec_marks, bool fCollectBlack) {
    Vec_Int_t * vec_ops = Vec_IntAlloc(10);
    for(unsigned i = 0; i < vec_ids.size(); i++) {
        int op_id = vec_ids[i];
        bool is_black = vec_marks[i];
        if((is_black && fCollectBlack) || (!is_black && !fCollectBlack))
            Vec_IntPush(vec_ops, op_id);
    }
    return vec_ops;
}

static bool verify_cex_direct(Wlc_Ntk_t * pNtk, Abc_Cex_t * pCex) {
    Gia_Man_t * pGia = BitBlast(pNtk);
    int i;

    Gia_ManConst0(pGia)->Value = 0;
    Gia_Obj_t * pObj, * pObjRi;
    Gia_ManForEachRi( pGia, pObj, i )
        pObj->Value = 0;
    for ( int f = 0; f <= pCex->iFrame; f++ ) {
        for( i = 0; i < Gia_ManPiNum(pGia); i++ ) {
            Gia_ManPi(pGia, i)->Value = Abc_InfoHasBit(pCex->pData, pCex->nRegs+pCex->nPis*f + i);
        }
        Gia_ManForEachRiRo( pGia, pObjRi, pObj, i )
            pObj->Value = pObjRi->Value;
        Gia_ManForEachAnd( pGia, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj) & Gia_ObjFanin1Copy(pObj);
        Gia_ManForEachCo( pGia, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        Gia_ManForEachPo( pGia, pObj, i ) {
            if (pObj->Value==1) {
                LOG(3) << "CEX is valid.";
                Gia_ManStop(pGia);
                return true;
            }
        }
    }

    LOG(3) << "CEX is invalid.";
    Gia_ManStop(pGia);
    return false;
}

static bool verify_cex_on_original(Wlc_Ntk_t * pOrig, Abc_Cex_t * pCex) {
    Gia_Man_t * pGiaOrig = BitBlast(pOrig);

    unsigned nbits_orig_pis = compute_bit_level_pi_num(pOrig);
    int nbits_ppis = pCex->nPis - Gia_ManPiNum(pGiaOrig);
    LOG(3) << "VerifyCEX: #ppis = " << nbits_ppis;

    int i;

    Gia_ManConst0(pGiaOrig)->Value = 0;
    Gia_Obj_t * pObj, * pObjRi;
    Gia_ManForEachRi( pGiaOrig, pObj, i )
        pObj->Value = 0;
    for ( int f = 0; f <= pCex->iFrame; f++ ) {
        for( i = 0; i < Gia_ManPiNum(pGiaOrig); i++ ) {
            if ( i < nbits_orig_pis ) {
                Gia_ManPi(pGiaOrig, i)->Value = Abc_InfoHasBit(pCex->pData, pCex->nRegs+pCex->nPis*f + i);
            } else { // undc PIs
                Gia_ManPi(pGiaOrig, i)->Value = Abc_InfoHasBit(pCex->pData, pCex->nRegs+pCex->nPis*f + i + nbits_ppis);
            }
        }
        Gia_ManForEachRiRo( pGiaOrig, pObjRi, pObj, i )
            pObj->Value = pObjRi->Value;
        Gia_ManForEachAnd( pGiaOrig, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj) & Gia_ObjFanin1Copy(pObj);
        Gia_ManForEachCo( pGiaOrig, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        Gia_ManForEachPo( pGiaOrig, pObj, i ) {
            if (pObj->Value==1) {
                LOG(3) << "CEX is real.";
                return true;
            }
        }
    }

    Gia_ManStop(pGiaOrig);
    LOG(3) << "CEX is spurious.";
    return false;
}

static bool bitstr_not_equal(const string& str1, const string& str2) {
    if (str1.size()!=str2.size()) return true;

    for(unsigned i = 0; i < str1.size(); i++) {
        if (str1[i]=='1' && str2[i]=='0')
            return true;
        if (str1[i]=='0' && str2[i]=='1')
            return true;

        if (str1[i]=='u' && str2[i]=='s')
            return true;
        if (str1[i]=='s' && str2[i]=='u')
            return true;
    }

    return false;
}

static bool bitstr_all_x(const string& str) {
    for(auto& x : str) {
        if(x!='x') return false;
    }
    return true;
}

static void print_blackboxes(const vector<bool>& vec_bb) {
    ostringstream oss;
    for(const auto& x : vec_bb) {
        oss << (x ? "1" : "0");
    }
    LOG(3) << oss.str();
}

static void print_pairs(const set<UifPair>& set_pairs) {
    for(auto& x : set_pairs) {
        LOG(3) << "(" << x.first << ", " << x.second << ")" << (x.fMark ? " [r]" : "");
    }
}

/*
static int super_prove(Wlc_Ntk_t * pNtk, Abc_Cex_t ** ppCex, bool fSimp, const string* pFileName = NULL) {
    if(*ppCex) {
        Abc_CexFree(*ppCex);
        *ppCex = NULL;
    }

    Gia_Man_t * pGia = BitBlast(pNtk);

    if (pFileName && !pFileName->empty())
        Gia_AigerWriteSimple(pGia, &((*pFileName + ".aig")[0u]));

    string tmpName = tmpnam(nullptr);
    string tmpFileName = tmpName + ".aig";
    Gia_AigerWrite( pGia, &tmpFileName[0u], 0, 0 );

    //string cmd = "super_prove -r /dev/stderr " + tmpFileName;
    string cmd;
    if (fSimp)
        cmd = "simple " + tmpFileName;
    else
        cmd = "super_prove " + tmpFileName;

    vector<int> vec_cex;
    int result = call_python("run_sp", "verify", cmd.c_str(), vec_cex);
    if(result == 1)
        readCexFromVec(pGia, vec_cex, ppCex);
    remove(tmpFileName.c_str());
    Gia_ManStop(pGia);

    if (result == 0) {
        return 1;
    } else if (result == 1) {
        return 0;
    } else {
        return -1;
    }
}
*/

static void get_operator_pair(Wlc_Ntk_t * p, const UIF_PAIR& uif_pair, array<int, 3>& wires1, array<int, 3>& wires2, const vector<int>& vec_ids, const VecVecInt& vv_op_ffs) {
    const UIF_PAIR& x = uif_pair;
    assert(x.second.timediff == 0);
    wires2[2] = vec_ids[x.second.idx];
    wires2[0] = x.fMark ? Wlc_ObjFaninId1(Wlc_NtkObj(p, vec_ids[x.second.idx])) : Wlc_ObjFaninId0(Wlc_NtkObj(p, vec_ids[x.second.idx]));
    wires2[1] = x.fMark ? Wlc_ObjFaninId0(Wlc_NtkObj(p, vec_ids[x.second.idx])) : Wlc_ObjFaninId1(Wlc_NtkObj(p, vec_ids[x.second.idx]));

    if (x.first.timediff == 0) {
        wires1[2] = vec_ids[x.first.idx];
        wires1[0] = Wlc_ObjFaninId0(Wlc_NtkObj(p, vec_ids[x.first.idx]));
        wires1[1] = Wlc_ObjFaninId1(Wlc_NtkObj(p, vec_ids[x.first.idx]));
    } else {
        int ci_idx = vv_op_ffs[x.first.idx][0 - x.first.timediff - 1];
        wires1[2] = Wlc_ObjId(p, Wlc_NtkCi(p, ci_idx));
        wires1[1] = Wlc_ObjId(p, Wlc_NtkCi(p, ci_idx - 1));
        wires1[0] = Wlc_ObjId(p, Wlc_NtkCi(p, ci_idx - 2));
    }
}

static Gia_Man_t * unroll_with_cex(Wlc_Ntk_t * pChoice, Abc_Cex_t * pCex, int nbits_old_pis, int num_sel_pis, int * p_num_ppis, bool sel_pi_first) {
    Gia_Man_t * pGiaChoice = BitBlast( pChoice );

    int nbits_new_pis = compute_bit_level_pi_num(pChoice);
    int num_ppis = nbits_new_pis - nbits_old_pis - num_sel_pis;
    *p_num_ppis = num_ppis;
    int num_undc_pis = Gia_ManPiNum(pGiaChoice) - nbits_new_pis;
    LOG(3) << "#orig_pis = " << nbits_old_pis << ", #ppis = " << num_ppis << ", #sel_pis = " << num_sel_pis << ", #undc_pis = " << num_undc_pis;
    assert(Gia_ManPiNum(pGiaChoice)==nbits_old_pis+num_ppis+num_sel_pis+num_undc_pis);
    assert(Gia_ManPiNum(pGiaChoice)==pCex->nPis+num_sel_pis);

    Gia_Man_t * pFrames = NULL;

    Gia_Obj_t * pObj, * pObjRi;
    int f, i;
    pFrames = Gia_ManStart( 10000 );
    pFrames->pName = Abc_UtilStrsav( pGiaChoice->pName );
    Gia_ManHashAlloc( pFrames );
    Gia_ManConst0(pGiaChoice)->Value = 0;
    Gia_ManForEachRi( pGiaChoice, pObj, i )
        pObj->Value = 0;

    auto is_sel_pi = [=](int iPi) {
        return (sel_pi_first ? iPi < nbits_old_pis + num_sel_pis : iPi >= nbits_old_pis + num_ppis);
    };

    for ( f = 0; f <= pCex->iFrame; f++ ) {
        for( i = 0; i < Gia_ManPiNum(pGiaChoice); i++ ) {
            if ( i >= nbits_old_pis && i < nbits_old_pis + num_ppis + num_sel_pis ) {
                if(f == 0 || !is_sel_pi(i))
                    Gia_ManPi(pGiaChoice, i)->Value = Gia_ManAppendCi(pFrames);
            } else if (i < nbits_old_pis) {
                Gia_ManPi(pGiaChoice, i)->Value = Abc_InfoHasBit(pCex->pData, pCex->nRegs+pCex->nPis*f + i);
            } else if (i >= nbits_old_pis + num_ppis + num_sel_pis) {
                Gia_ManPi(pGiaChoice, i)->Value = Abc_InfoHasBit(pCex->pData, pCex->nRegs+pCex->nPis*f + i - num_sel_pis);
            }
        }
        Gia_ManForEachRiRo( pGiaChoice, pObjRi, pObj, i )
            pObj->Value = pObjRi->Value;
        Gia_ManForEachAnd( pGiaChoice, pObj, i )
            pObj->Value = Gia_ManHashAnd(pFrames, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
        Gia_ManForEachCo( pGiaChoice, pObj, i )
            pObj->Value = Gia_ObjFanin0Copy(pObj);
        Gia_ManForEachPo( pGiaChoice, pObj, i )
            Gia_ManAppendCo(pFrames, pObj->Value);
    }
    Gia_ManHashStop (pFrames);
    Gia_ManSetRegNum(pFrames, 0);
    Gia_Man_t * pGia;
    pFrames = Gia_ManCleanup(pGia = pFrames);
    Gia_ManStop(pGia);
    Gia_ManStop(pGiaChoice);

    return pFrames;
}

static void compute_core_using_sat(Gia_Man_t * pFrames, vector<unsigned>& vec_cores, int nFrames, int num_sel_pis, int num_other_pis, bool sel_pi_first, VecVecInt* ppi_model = NULL, bool fSatMin = false, int nConfLimit = 0) {
    Aig_Man_t * pAigFrames = Gia_ManToAigSimple( pFrames );
    Cnf_Dat_t * pCnf = Cnf_Derive(pAigFrames, Aig_ManCoNum(pAigFrames));
    sat_solver * pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnf->nVars);
    for (unsigned i = 0; i < pCnf->nClauses; i++) {
        if (!sat_solver_addclause(pSat, pCnf->pClauses[i], pCnf->pClauses[i + 1]))
            assert(false);
    }
    {
        Vec_Int_t* vLits = Vec_IntAlloc(100);
        Aig_Obj_t* pObj;
        int i;
        Aig_ManForEachCo( pAigFrames, pObj, i )
        {
            assert(pCnf->pVarNums[pObj->Id] >= 0);
            Vec_IntPush(vLits, toLitCond(pCnf->pVarNums[pObj->Id], 0));
        }
        int ret = sat_solver_addclause(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits));
        if (!ret) {
            LOG(0) << "UNSAT after adding PO clause.";
        }

        Vec_IntFree(vLits);
    }
    {
        Vec_Int_t* vLits = Vec_IntAlloc(100);
        map<int, int> varMap;
        int first_sel_pi = sel_pi_first ? 0 : num_other_pis;
        for (int i = 0; i < num_sel_pis; i++) {
        //for (int i = num_sel_pis - 1; i >= 0; --i) {
            int cur_pi = first_sel_pi + i;
            int var = pCnf->pVarNums[Aig_ManCi(pAigFrames, cur_pi)->Id];
            assert(var >= 0);
            varMap[var] = i;
            Vec_IntPush(vLits, toLitCond(var, 0));
        }
        if(log_level() >= 3) {
            int i, Entry;
            ostringstream oss;
            oss << "#vLits = " << Vec_IntSize(vLits) << "; vLits = ";
            Vec_IntForEachEntry(vLits, Entry, i)
                oss << Entry << " ";
            LOG(3) << oss.str();
        }
        int status = sat_solver_solve(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)(nConfLimit), (ABC_INT64_T)(0), (ABC_INT64_T)(0), (ABC_INT64_T)(0));
        if (status == l_False) {
            LOG(3) << "UNSAT.";
            int nCoreLits, *pCoreLits;
            nCoreLits = sat_solver_final(pSat, &pCoreLits);

            vector<bool> vec_cores_marks (Vec_IntSize(vLits),false);
            for (int i = 0; i < nCoreLits; i++) {
                vec_cores_marks[varMap[lit_var(pCoreLits[i])]] = true;
            }

            // SAT-min
            if (fSatMin && nCoreLits > 1) {
                for (int i = 0; i < vec_cores_marks.size(); i++) {
                    if (!vec_cores_marks[i])
                        Vec_IntWriteEntry(vLits, i, lit_neg(Vec_IntEntry(vLits, i)));
                }

                for (int i = 0; i < vec_cores_marks.size(); i++) {
                    if (!vec_cores_marks[i])
                        continue;

                    Vec_IntWriteEntry(vLits, i, lit_neg(Vec_IntEntry(vLits, i)));
                    int status = sat_solver_solve(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T) (5000), (ABC_INT64_T) (0), (ABC_INT64_T) (0), (ABC_INT64_T) (0));

                    if (status == l_False) {
                        LOG(4) << "Loop[" << i << "] : Drop 1 literal = " << Vec_IntEntry(vLits, i);
                        vec_cores_marks[i] = false;
                    } else {
                        if (status == l_True)
                            LOG(4) << "Loop[" << i << "] : SAT";
                        else
                            LOG(4) << "Loop[" << i << "] : Unknown";
                        Vec_IntWriteEntry(vLits, i, lit_neg(Vec_IntEntry(vLits, i)));
                    }
                }
                LOG(2) << "SAT-MIN : " << nCoreLits << " ==> " << count(vec_cores_marks.begin(), vec_cores_marks.end(), true);
            }

            for (int i = 0; i < vec_cores_marks.size(); i++) {
                if(vec_cores_marks[i])
                    vec_cores.push_back(i);
            }
        } else if (status == l_True) {
            LOG(3) << "SAT.";

            if (ppi_model && sel_pi_first) {
                ppi_model->clear();
                for (int f = 0; f < nFrames; f++) {
                    ppi_model->push_back(vector<int>());
                    for (int i = 0; i < num_other_pis; i++) {
                        int cur_pi = num_sel_pis + f * num_other_pis + i;
                        int var = pCnf->pVarNums[Aig_ManCi(pAigFrames, cur_pi)->Id];
                        ppi_model->back().push_back(sat_solver_var_value(pSat, var));
                    }
                }
            }
        } else {
            LOG(3) << "UNKNOWN.";
        }

        Vec_IntFree(vLits);
    }
    Cnf_ManFree();
    sat_solver_delete(pSat);
    Aig_ManStop(pAigFrames);
}

std::ostream& operator<<(ostream& os, const OperatorID& obj) {
    os << obj.idx << " @ " << obj.timediff;
    return os;
}

class SimUifPairFinder {
    public:
        SimUifPairFinder(Wlc_Ntk_t * pOrig, const vector<int>* p_vec_ids) :
            nWords(1),
            nFrames(1),
            nThreshold(0),
            _pOrigNtk(pOrig),
            _p_vec_op_ids(p_vec_ids)
        {}

        void Simulate() {
            _compute_max_bw();
            _simulate_and_count();
        }
        void ComputeUifPairs() {
            _insert_sim_pairs();
        }
        void SetParams(const string& setting);

        bool HasResults() const {return !_mat_pairwise_matches.empty();}
        int  GetCount(const UIF_PAIR& x) const;
        bool IsGood(const UIF_PAIR& x) const {return (GetCount(x) >= nThreshold);}
        void AddPair(const UIF_PAIR& x);

        const set<UIF_PAIR>* GetSimPairsPtr() { return &_set_sim_pairs; }

        int nWords;
        int nFrames;
        int nThreshold;
    private:
        void _compute_max_bw() { ComputeMaxBW(_pOrigNtk, *_p_vec_op_ids, _max_input_bw, _max_output_bw); }
        void _simulate_and_count();
        void _insert_sim_pairs();
        void _count_matches(Vec_Ptr_t * vRes, int range);
        Vec_Int_t * _collect_sim_nodes(Wlc_Ntk_t * pNtk);

        Wlc_Ntk_t *          _pOrigNtk;
        const vector<int>*   _p_vec_op_ids;

        set<UIF_PAIR>     _set_sim_pairs;

        int               _max_input_bw {-1};
        int               _max_output_bw {-1};

        VecVecInt         _mat_pairwise_matches;
};

void SimUifPairFinder::AddPair(const UIF_PAIR& x) {
    assert(x.first.timediff == 0 && x.second.timediff == 0);
    assert(x.first.idx < x.second.idx);

    if(x.fMark)
        _mat_pairwise_matches[x.second.idx][x.first.idx] += nThreshold;
    else 
        _mat_pairwise_matches[x.first.idx][x.second.idx] += nThreshold;
}
int  SimUifPairFinder::GetCount(const UIF_PAIR& x) const {
    assert(x.first.timediff == 0 && x.second.timediff == 0);
    assert(x.first.idx < x.second.idx);

    return (x.fMark ? _mat_pairwise_matches[x.second.idx][x.first.idx] : _mat_pairwise_matches[x.first.idx][x.second.idx]);
}

void SimUifPairFinder::SetParams(const string& setting) {
    int temp = 0;
    smatch sub_match;

    if(regex_search(setting, sub_match, regex(R"(w:(\d+))")))
        nWords = stoi(sub_match[1].str());

    if(regex_search(setting, sub_match, regex(R"(f:(\d+))")))
        nFrames = stoi(sub_match[1].str());

    if(regex_search(setting, sub_match, regex(R"(t:(\d+))")))
        temp = stoi(sub_match[1].str());

    nThreshold = temp * nWords * nFrames * 64 / 100;
}

Vec_Int_t * SimUifPairFinder::_collect_sim_nodes(Wlc_Ntk_t * pNtk) {
    Vec_Int_t * vNodes = Vec_IntAlloc( _p_vec_op_ids->size() * 2 );
    int i;
    Wlc_Obj_t * pPo;
    int range = Wlc_ObjRange(Wlc_NtkPo(pNtk, 1));
    (void)range;
    Wlc_NtkForEachPo(pNtk, pPo, i) {
       if ((i%3)==0) continue;
       assert(range == Wlc_ObjRange(pPo));
       Vec_IntPush(vNodes, Wlc_ObjId(pNtk, pPo));
    }
    assert(Vec_IntSize(vNodes) == _p_vec_op_ids->size() * 2);

    return vNodes;
}

static unsigned bit_count (word value) {
    unsigned count = 0;
    while (value > 0) {           // until all bits are zero
        if ((value & 1) == 1)     // check lower bit
            count++;
        value >>= 1;              // shift bits, removing lower bit
    }
    return count;
}

static void bit_print (word value) {
    int n_bits = 0;
    while(n_bits < 64) {
        if ((value & 1) == 1)
            cout << "1";
        else
            cout << "0";
        value >>= 1;
        n_bits++;
    }
    cout << endl;
}

void SimUifPairFinder::_count_matches(Vec_Ptr_t * vRes, int range) {
    VecVecInt& mat = _mat_pairwise_matches;
    int num_ops = _p_vec_op_ids->size();
    mat = VecVecInt(num_ops, vector<int>(num_ops, 0));
    array<int, 2> op1, op2;

    for(int i = 0; i < num_ops; i++) {
        for(int j = 0; j < num_ops; j++) {
            if (i == j) continue;

            for(int f = 0; f < nFrames; f++) {
                vector<word> merges(nWords, ~0);

                op1[0] = (i < j) ? (i << 1) : (i << 1) + 1;
                op1[1] = (i < j) ? (i << 1) + 1 : (i << 1);
                op2[0] = (j << 1);
                op2[1] = (j << 1) + 1;

                for (int k = 0; k < range; k++) {
                    for (int w = 0; w < nWords; w++) {
                        word w1, w2;
                        w1 = ((word*) Vec_VecEntryEntry((Vec_Vec_t *) vRes, op1[0], k))[f * nWords + w];
                        w2 = ((word*) Vec_VecEntryEntry((Vec_Vec_t *) vRes, op2[0], k))[f * nWords + w];
                        merges[w] = merges[w] & (~(w1 ^ w2));

                        w1 = ((word*) Vec_VecEntryEntry((Vec_Vec_t *) vRes, op1[1], k))[f * nWords + w];
                        w2 = ((word*) Vec_VecEntryEntry((Vec_Vec_t *) vRes, op2[1], k))[f * nWords + w];
                        merges[w] = merges[w] & (~(w1 ^ w2));
                    }
                }

                for (int w = 0; w < nWords; w++) {
                    mat[i][j] += bit_count(merges[w]);
                }
            }
        }
    }

    /*
    for(int i = 0; i < num_ops; ++i) {
        for(int j = 0; j < num_ops; ++j) {
            if(i == j) continue;
            if(mat[i][j] == 0) continue;
            cout << "[" << i << "][" << j << "] = " << mat[i][j] << endl;
        }
    }
    */
}

void SimUifPairFinder::_simulate_and_count() {
    vector<int> vec_ids = *_p_vec_op_ids;
    Wlc_Ntk_t * pSimNtk = AddAuxPOsForOperators(_pOrigNtk, vec_ids, _max_input_bw, _max_output_bw);
    Vec_Int_t * vNodes = _collect_sim_nodes(pSimNtk);
    Vec_Ptr_t * vRes;
    vRes = Wlc_NtkSimulate( pSimNtk, vNodes, nWords, nFrames );
    // Wlc_NtkSimulatePrint(pSimNtk, vNodes, vRes, nWords, nFrames);
    _count_matches(vRes, Wlc_ObjRange(Wlc_NtkObj(pSimNtk, Vec_IntEntry(vNodes, 0))));

    Wlc_NtkFree(pSimNtk);
    Vec_IntFree(vNodes);
    Wlc_NtkDeleteSim(vRes);
}

void SimUifPairFinder::_insert_sim_pairs() {
    VecVecInt& mat = _mat_pairwise_matches;
    _set_sim_pairs.clear();

    int num_ops = mat.size();

    for(int i = 0; i < num_ops; ++i) {
        for(int j = 0; j < num_ops; ++j) {
            if(i == j) continue;
            if(mat[i][j] < nThreshold) continue;

            if (i < j)
                _set_sim_pairs.insert(UIF_PAIR(OperatorID(i), OperatorID(j), 0));
            else
                _set_sim_pairs.insert(UIF_PAIR(OperatorID(j), OperatorID(i), 1));
        }
    }
}

class CexUifPairFinder {
    public:
        CexUifPairFinder(Wlc_Ntk_t * pOrigNtk, const vector<int>* p_vec_op_ids) :
            _pOrigNtk(pOrigNtk),
            _p_vec_op_ids(p_vec_op_ids)
        {}

        void SetStates(Abc_Cex_t * pCex, const vector<bool>* p_vec_op_marks, const set<UIF_PAIR>* p_set_uif_pairs, set<OperatorID>* p_set_prev_ops, const UfarManager::Params* p_params) {
            _pCex = pCex;
            _p_vec_op_blackbox_marks = p_vec_op_marks;
            _p_set_uif_pairs = p_set_uif_pairs;
            _p_set_prev_ops = p_set_prev_ops;
            _p_params = p_params;
        }
        void FindUifPairs(const VecVecChar& cex_po_values, unsigned nLookBack, set<UIF_PAIR>& set_new_pairs);
        void FindUifPairsBasic(const VecVecChar& cex_po_values, unsigned nLookBack, set<UIF_PAIR>& set_new_pairs);
        void ComputeCoreUifPairs(const set<UIF_PAIR>& set_candidates, set<UIF_PAIR>& set_core, Abc_Cex_t ** ppCex);
        const VecVecStr* GetOutputs() const {return &_outputs;}
    private:
        void _compute_max_bw();
        string _get_bitstr(Wlc_Obj_t * pObj, const VecChar& cur_pos, unsigned& pos, bool isOutput);

        Wlc_Ntk_t * _introduce_choices(const set<UIF_PAIR>& set_candidates, vector<UIF_PAIR>& vec_choice2pair);
        Wlc_Ntk_t * _apply_uif_pairs_with_choices(Wlc_Ntk_t * pNtk, const VecVecInt& vv_op_ffs, vector<int>& vec_ids, const set<UIF_PAIR>& set_candidates, vector<UIF_PAIR>& vec_choice2pair);

        Wlc_Ntk_t *         _pOrigNtk;
        const vector<int>*  _p_vec_op_ids;

        Abc_Cex_t *               _pCex                    {NULL};
        const vector<bool>*       _p_vec_op_blackbox_marks {NULL};
        const set<UIF_PAIR>*      _p_set_uif_pairs         {NULL};
        set<OperatorID>*          _p_set_prev_ops          {NULL};
        const UfarManager::Params* _p_params                {NULL};

        int            _max_input_bw {-1};
        int            _max_output_bw {-1};

        VecVecStr      _outputs;
        VecVecStr      _inputs;
};

void CexUifPairFinder::_compute_max_bw() {
     // compute max bit-width
    ComputeMaxBW(_pOrigNtk, *_p_vec_op_ids, _max_input_bw, _max_output_bw);
    LOG(3) << "maxIn = " << _max_input_bw << "; maxOut = " << _max_output_bw;
}

string CexUifPairFinder::_get_bitstr(Wlc_Obj_t * pObj, const VecChar& cur_pos, unsigned& pos, bool isOutput) {
    int range = Wlc_ObjRange(pObj);
    int max_bw = isOutput ? _max_output_bw : _max_input_bw;
    string bitstr = string(cur_pos.begin() + pos, cur_pos.begin() + pos + range).append(max_bw - range, *(cur_pos.begin() + pos + range - 1));
    pos += range;

    return bitstr;
}

Wlc_Ntk_t * CexUifPairFinder::_apply_uif_pairs_with_choices(Wlc_Ntk_t * pNtk, const VecVecInt& vv_op_ffs, vector<int>& vec_ids, const set<UIF_PAIR>& set_candidates, vector<UIF_PAIR>& vec_choice2pair) {
    array<int, 3> wires1;
    array<int, 3> wires2;

    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);
    Vec_Int_t * vUifConstrs = Vec_IntAlloc( 100 );
    Vec_Int_t * vFanins = Vec_IntAlloc( 2 );

    for(auto& x : *_p_set_uif_pairs) {
        get_operator_pair(p, x, wires1, wires2, vec_ids, vv_op_ffs);
        int iObj = AddOneUifImplication(p, wires1, wires2);
        Vec_IntPush(vUifConstrs, iObj);
    }

    for(auto& x : set_candidates) {
        vec_choice2pair.push_back(x);
        get_operator_pair(p, x, wires1, wires2, vec_ids, vv_op_ffs);
        int iObj = AddOneUifImplication(p, wires1, wires2);
        int iSelPi = Wlc_ObjAlloc( p, WLC_OBJ_PI, 0, 0, 0);
        Vec_IntFill(vFanins, 1, iSelPi);
        int iSelPiNeg = Wlc_ObjCreate( p, WLC_OBJ_LOGIC_NOT, 0, 0, 0, vFanins);
        Vec_IntFillTwo(vFanins, 2, iObj, iSelPiNeg);
        int iObjNew = Wlc_ObjCreate( p, WLC_OBJ_LOGIC_OR, 0, 0, 0, vFanins);
        Vec_IntPush(vUifConstrs, iObjNew);
    }

    if (Wlc_NtkFfNum(_pOrigNtk) == 0)
        FoldCombConstraints(p, vUifConstrs);
    else
        FoldSeqConstraints(p, vUifConstrs);

    Wlc_Ntk_t * pNew = DupNtkAndUpdateIDs(p, vec_ids);

    Wlc_NtkFree(p);
    Vec_IntFree(vUifConstrs);
    Vec_IntFree(vFanins);

    return pNew;
}

Wlc_Ntk_t * CexUifPairFinder::_introduce_choices(const set<UIF_PAIR>& set_candidates, vector<UIF_PAIR>& vec_choice2pair) {
    vector<int> vec_ids = *_p_vec_op_ids;
    VecVecInt vv_op_ffs;
    Wlc_Ntk_t * pNew, * pTemp;

    if(!_p_set_prev_ops->empty())
        pNew = IntroducePrevOperators(_pOrigNtk, vec_ids, *_p_set_prev_ops, vv_op_ffs);
    else
        pNew = DupNtkAndUpdateIDs(_pOrigNtk, vec_ids);

    if(_p_params->fGrey) {
        pNew = ApplyGreyConstraints(pTemp = pNew, vec_ids, Wlc_NtkFfNum(_pOrigNtk) > 0);
        Wlc_NtkFree(pTemp);
    }

    pNew = _apply_uif_pairs_with_choices(pTemp = pNew, vv_op_ffs, vec_ids, set_candidates, vec_choice2pair);
    Wlc_NtkFree(pTemp);

    Vec_Int_t * vec_ops = collect_boxes(vec_ids, *_p_vec_op_blackbox_marks, true /*black*/);
    assert(Vec_IntSize(vec_ops) > 0);
    pNew = AbstractNodes(pTemp = pNew, vec_ops);
    Wlc_NtkFree(pTemp);

    return pNew;
}


static Abc_Cex_t * get_new_cex_with_ppi(Abc_Cex_t * pOrigCex, const VecVecInt& ppi_model, int num_orig_pis, int num_ppis, bool one_more_flop) {
    Abc_Cex_t * pCex = Abc_CexAlloc( one_more_flop ? pOrigCex->nRegs + 1 : pOrigCex->nRegs, pOrigCex->nPis, pOrigCex->iFrame + 1);
    pCex->iFrame = pOrigCex->iFrame;
    pCex->iPo = 0;

    for(int f = 0; f < pOrigCex->iFrame + 1; f++) {
        for(int i = 0; i < pOrigCex->nPis; i++) {
            int iOrigBit = pOrigCex->nRegs+pOrigCex->nPis*f + i;
            int iBit = one_more_flop ? iOrigBit + 1 : iOrigBit;
            if ( i >= num_orig_pis && i < num_orig_pis + num_ppis ) {
                if(ppi_model[f][i-num_orig_pis]) {
                    Abc_InfoSetBit(pCex->pData, iBit);
                }
            } else { // i < num_orig_pis || i >= num_orig_pis + num_ppis
                if(Abc_InfoHasBit(pOrigCex->pData, iOrigBit)) {
                    Abc_InfoSetBit(pCex->pData, iBit);
                }
            }
        }
    }

    return pCex;
}

void CexUifPairFinder::ComputeCoreUifPairs(const set<UIF_PAIR>& set_candidates, set<UIF_PAIR>& set_core, Abc_Cex_t ** ppCex) {
    vector<UIF_PAIR> vec_choice2pair;
    Wlc_Ntk_t * pChoice = _introduce_choices(set_candidates, vec_choice2pair);
    assert(set_candidates.size() == vec_choice2pair.size());

    int num_ppis;
    int num_orig_pis = compute_bit_level_pi_num(_pOrigNtk);
    Gia_Man_t * pGiaFrames = unroll_with_cex(pChoice, _pCex, num_orig_pis, vec_choice2pair.size(), &num_ppis, true);

    vector<unsigned> vec_cores;
    VecVecInt ppi_model;
    compute_core_using_sat(pGiaFrames, vec_cores, _pCex->iFrame+1, vec_choice2pair.size(), num_ppis, true, &ppi_model, false, 5000);
    if(ppCex && !ppi_model.empty()) {
        if(*ppCex) Abc_CexFree(*ppCex);
        *ppCex = get_new_cex_with_ppi(_pCex, ppi_model, num_orig_pis, num_ppis, _p_set_uif_pairs->empty() && Wlc_NtkFfNum(_pOrigNtk));
    }
    // Abc_CexPrintStats(_pCex);
    // Abc_CexPrintStats(*ppCex);

    set_core.clear();
    for(auto& x : vec_cores) {
        set_core.insert(vec_choice2pair[x]);
    }

    Gia_ManStop(pGiaFrames);
    Wlc_NtkFree(pChoice);
}

void CexUifPairFinder::FindUifPairsBasic(const VecVecChar& cex_po_values, unsigned nLookBack, set<UIF_PAIR>& set_new_pairs) {
    assert(Wlc_NtkPoNum(_pOrigNtk) == 1);
    assert(Wlc_ObjRange(Wlc_NtkPo(_pOrigNtk, 0)) == 1);

    _inputs.clear();
    _outputs.clear();

    for (unsigned f = 0; f < cex_po_values.size(); f++) {
        _inputs.push_back(vector<string>());
        _outputs.push_back(vector<string>());

        const vector<char>& cur_po_values = cex_po_values[f];
        unsigned pos = 1;

        for (unsigned i = 0; i < _p_vec_op_ids->size(); i++) {
            int op_id = _p_vec_op_ids->at(i);
            Wlc_Obj_t * pObj = Wlc_NtkObj(_pOrigNtk, op_id);

            Wlc_Obj_t * pObjInput = NULL;

            pObjInput = Wlc_ObjFanin0(_pOrigNtk, pObj);
            _max_input_bw = Wlc_ObjRange(pObjInput);
            string bits_input0 = _get_bitstr(pObjInput, cur_po_values, pos, false);
            bits_input0 += (Wlc_ObjIsSigned(pObjInput) ? 's' : 'u');

            pObjInput = Wlc_ObjFanin1(_pOrigNtk, pObj);
            _max_input_bw = Wlc_ObjRange(pObjInput);
            string bits_input1 = _get_bitstr(pObjInput, cur_po_values, pos, false);
            bits_input1 += (Wlc_ObjIsSigned(pObjInput) ? 's' : 'u');

            _max_output_bw = Wlc_ObjRange(pObj);
            string bits_output = _get_bitstr(pObj, cur_po_values, pos, true);
            bits_output += (Wlc_ObjIsSigned(pObj) ? 's' : 'u');
            _outputs.back().push_back(bits_output);

            vector<string> keys;
            keys.push_back(bits_input0 + ':' + bits_input1);
            keys.push_back(bits_input1 + ':' + bits_input0);
            _inputs.back().push_back(keys[0]);


            for (unsigned reversed = 0; reversed < keys.size(); reversed++) {
                const string& key = keys[reversed];
                for (int g = f; g >= 0 && g >= (int)f - (int)nLookBack; g--) {
                    for (int j = 0; j < _inputs[g].size(); j++) {
                        if (!bitstr_not_equal(key, _inputs[g][j]) && bitstr_not_equal(_outputs[f][i], _outputs[g][j])) {
                            UIF_PAIR pair_int(OperatorID(j, g-f), OperatorID(i), reversed);
                            if (_p_set_uif_pairs->count(pair_int) == 0)
                                set_new_pairs.insert(pair_int);
                            if(g < f)
                                _p_set_prev_ops->insert(OperatorID(j, g-f));
                        }
                    }
                }
            }
            LOG(4) << "[" << f << "][" << i << "] : " << "key = " << keys[0] << " output = " << _outputs[f][i] ;
        }
    }
}

void CexUifPairFinder::FindUifPairs(const VecVecChar& cex_po_values, unsigned nLookBack, set<UIF_PAIR>& set_new_pairs) {
    assert(Wlc_NtkPoNum(_pOrigNtk) == 1);
    assert(Wlc_ObjRange(Wlc_NtkPo(_pOrigNtk, 0)) == 1);

    _compute_max_bw();

    _inputs.clear();
    _outputs.clear();

    for (unsigned f = 0; f < cex_po_values.size(); f++) {

        _inputs.push_back(vector<string>());
        _outputs.push_back(vector<string>());

        const vector<char>& cur_po_values = cex_po_values[f];
        unsigned pos = 1;

        for (unsigned i = 0; i < _p_vec_op_ids->size(); i++) {
            int op_id = _p_vec_op_ids->at(i);
            Wlc_Obj_t * pObj = Wlc_NtkObj(_pOrigNtk, op_id);

            string bits_input0 = _get_bitstr(Wlc_ObjFanin0(_pOrigNtk, pObj), cur_po_values, pos, false);
            string bits_input1 = _get_bitstr(Wlc_ObjFanin1(_pOrigNtk, pObj), cur_po_values, pos, false);
            assert(bits_input0.size() == bits_input1.size());

            string bits_output = _get_bitstr(pObj, cur_po_values, pos, true);
            _outputs.back().push_back(bits_output);

            vector<string> keys;
            keys.push_back(bits_input0 + ':' + bits_input1);
            keys.push_back(bits_input1 + ':' + bits_input0);
            _inputs.back().push_back(keys[0]);

            for (unsigned reversed = 0; reversed < keys.size(); reversed++) {
                const string& key = keys[reversed];
                for (int g = f; g >= 0 && g >= (int)f - (int)nLookBack; g--) {
                    for (int j = 0; j < _inputs[g].size(); j++) {
                        if (!bitstr_not_equal(key, _inputs[g][j]) && bitstr_not_equal(_outputs[f][i], _outputs[g][j])) {
                            UIF_PAIR pair_int(OperatorID(j, g-f), OperatorID(i), reversed);
                            if (_p_set_uif_pairs->count(pair_int) == 0)
                                set_new_pairs.insert(pair_int);
                            if(g < f)
                                _p_set_prev_ops->insert(OperatorID(j, g-f));
                        }
                    }
                }
            }
            LOG(4) << "[" << f << "][" << i << "] : " << "key = " << keys[0] << " output = " << _outputs[f][i] ;
        }
    }

}

UfarManager::Params::Params() :
                fCexMin(true),
                fPbaUif(false),
                fLazySim(true),
                fPbaSim(false),
                fPbaCex(false),
                fSatMin(false),
                fCbaWb(false),
                fGrey(false),
                nGrey(0),
                fNorm(true),
                fSuper_prove(false),
                fSimple(false),
                fSyn(false),
                fPthread(false),
                iOneWb(-1),
                iExp(-1),
                nConstraintLimit(65536),
                iVerbosity(0),
                nSeqLookBack(0),
                nTimeout(65536)
            {}
UfarManager::UfarManager() : _pOrigNtk(NULL), _pAbsWithAuxPos(NULL) {}

UfarManager::~UfarManager() {
    if (_pOrigNtk) Wlc_NtkFree(_pOrigNtk);
}

void UfarManager::Initialize(Wlc_Ntk_t * pNtk, const set<unsigned>& types) {
    if (_pOrigNtk) Wlc_NtkFree(_pOrigNtk);
    _vec_orig_names.clear();
    _vec_op_ids.clear();
    _vec_op_blackbox_marks.clear();
    _vec_op_greyness.clear();
    _set_uif_pairs.clear();
    _set_uif_sim_pairs.clear();

    _vec_vec_op_ffs.clear();
    _set_prev_ops.clear();

    profile = Profile();

    _pOrigNtk = Wlc_NtkDupDfsSimple(pNtk);

    Wlc_Obj_t * pObj;
    int i;
    _vec_orig_names.resize(Wlc_NtkObjNumMax(pNtk));
    Wlc_NtkForEachObj(pNtk, pObj, i) {
        _vec_orig_names[i] = (Wlc_ObjName(pNtk, i));

        if(types.count(pObj->Type) > 0) {
            _vec_op_ids.push_back(i);
            if(params.nGrey) {
                _vec_op_greyness.push_back(Greyness(pNtk, pObj));
            }
        }
    }

    _vec_op_blackbox_marks.resize(_vec_op_ids.size(), true);

    _p_sim_mgr.reset(new SimUifPairFinder(_pOrigNtk, &_vec_op_ids));
    _p_cex_mgr.reset(new CexUifPairFinder(_pOrigNtk, &_vec_op_ids));

    LogT::loglevel = params.iVerbosity;

    struct timeval now;
    gettimeofday(&now, NULL);
    _timeout.tv_sec = now.tv_sec + params.nTimeout;
    _timeout.tv_nsec = now.tv_usec * 1000;
}

Wlc_Ntk_t * UfarManager::ApplyUifConstraints(Wlc_Ntk_t * pNtk, vector<int>& vec_ids) {
    array<int, 3> wires1;
    array<int, 3> wires2;

    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);
    Vec_Int_t * vUifConstrs = Vec_IntAlloc( 100 );

    for(auto& x : _set_uif_pairs) {
        get_operator_pair(p, x, wires1, wires2, vec_ids, _vec_vec_op_ffs);
        int iObj = AddOneUifImplication(p, wires1, wires2);
        Vec_IntPush(vUifConstrs, iObj);
    }

    if (Wlc_NtkFfNum(_pOrigNtk) == 0)
        FoldCombConstraints(p, vUifConstrs);
    else
        FoldSeqConstraints(p, vUifConstrs);

    Wlc_Ntk_t * pNew = DupNtkAndUpdateIDs(p, vec_ids);

    Wlc_NtkFree(p);
    Vec_IntFree(vUifConstrs);

    return pNew;
}

Wlc_Ntk_t * UfarManager::_set_up_constraints(vector<int>& vec_ids) {
    Wlc_Ntk_t * pNew, * pTemp;

    if(!_set_prev_ops.empty())
        pNew = IntroducePrevOperators(_pOrigNtk, vec_ids, _set_prev_ops, _vec_vec_op_ffs);
    else
        pNew = DupNtkAndUpdateIDs(_pOrigNtk, vec_ids);

    if(params.fGrey) {
        pNew = ApplyGreyConstraints(pTemp = pNew, vec_ids, Wlc_NtkFfNum(_pOrigNtk) > 0);
        Wlc_NtkFree(pTemp);
    }

    if(!_set_uif_pairs.empty()) {
        pNew = ApplyUifConstraints(pTemp = pNew, vec_ids);
        Wlc_NtkFree(pTemp);
    }

    if(params.nGrey) {
        pNew = ApplyGreynessConstraints(pTemp = pNew, _vec_op_greyness, vec_ids);
        Wlc_NtkFree(pTemp);
    }

    return pNew;
}


Wlc_Ntk_t * UfarManager::BuildCurrentAbstraction() {
    vector<int> vec_ids = _vec_op_ids;
    Wlc_Ntk_t * pNew, * pTemp;

    pNew = _set_up_constraints(vec_ids);

    pNew = AddAuxPOsForOperators(pTemp = pNew, vec_ids);
    Wlc_NtkFree(pTemp);
    // for(auto x : vec_ids) cout << "ID = " << x << " Type = " << Wlc_NtkObj(pNew, x)->Type << endl;

    if (count(_vec_op_blackbox_marks.begin(), _vec_op_blackbox_marks.end(), true) > 0) {
        pNew = _abstract_operators(pTemp = pNew, vec_ids);
        Wlc_NtkFree(pTemp);
    }

    if(_pAbsWithAuxPos) Wlc_NtkFree(_pAbsWithAuxPos);
    _pAbsWithAuxPos = Wlc_NtkDupDfsSimple(pNew);

    pNew = RemoveAuxPOs(pTemp = pNew, Wlc_NtkPoNum(_pOrigNtk));
    Wlc_NtkFree(pTemp);

    // Wlc_WriteVer(pNew, "Abs.v", 0, 0);

    return pNew;
}

void UfarManager::_simulate() {
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    _p_sim_mgr->SetParams(params.simSetting);
    _p_sim_mgr->Simulate();

    gettimeofday(&t2, NULL);
    profile.tUifSim += elapsed_time_usec(t1, t2);
}

void UfarManager::FindUifPairsUsingSim() {
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    _p_sim_mgr->ComputeUifPairs();
    _set_uif_sim_pairs = *_p_sim_mgr->GetSimPairsPtr();

    set<UIF_PAIR> set_new_pairs;
    for(auto& x:_set_uif_sim_pairs) {
        auto res = _set_uif_pairs.insert(x);
        if(res.second)
            set_new_pairs.insert(x);
    }
    if(log_level() >= 3)
        print_pairs(set_new_pairs);

    gettimeofday(&t2, NULL);
    profile.tUifSim += elapsed_time_usec(t1, t2);
}

void UfarManager::FindUifPairsUsingCex(Abc_Cex_t * pCex, Abc_Cex_t ** ppCex) {
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    VecVecChar cex_po_values;
    Gia_Man_t * pGia = BitBlast(_pAbsWithAuxPos);
    CollectPoValuesInCex(pGia, pCex, cex_po_values, params.fCexMin);
    Gia_ManStop(pGia);

    _p_cex_mgr->SetStates(pCex, &_vec_op_blackbox_marks, &_set_uif_pairs, &_set_prev_ops, &params);
    set<UIF_PAIR> set_found_pairs, set_temp;
    if (params.fNorm) {
        _p_cex_mgr->FindUifPairs(cex_po_values, params.nSeqLookBack, set_found_pairs);
    } else {
        _p_cex_mgr->FindUifPairsBasic(cex_po_values, params.nSeqLookBack, set_found_pairs);
    }
    if(log_level() >= 3) print_pairs(set_found_pairs);

    if(params.fPbaUif && !set_found_pairs.empty()) {
        _p_cex_mgr->ComputeCoreUifPairs(set_temp = set_found_pairs, set_found_pairs, ppCex);
        if(set_found_pairs.empty()) {
            LOG(2) << "Proof-based refinement failed (SAT)";
            // set_found_pairs = set_temp;
            if(params.fPbaCex) {
                set_found_pairs = set_temp;
            }
            if(params.fPbaSim && _p_sim_mgr->HasResults()) {
                for(auto& x : set_temp) {
                    if(_p_sim_mgr->GetCount(x) > 0)
                        set_found_pairs.insert(x);
                }
                if(set_found_pairs.empty()) {
                    LOG(2) << "No pair found with PBA and SIM";
                }
            }
        }
    }

    for(auto& x : set_found_pairs) _set_uif_pairs.insert(x);

    gettimeofday(&t2, NULL);
    profile.tUifRefine += elapsed_time_usec(t1, t2);
}

Wlc_Ntk_t * UfarManager::_introduce_bitwise_choices(vector<IntPair>& vec_choice2idx) {
    vector<int> vec_ids = _vec_op_ids;
    Wlc_Ntk_t * pNew, * pTemp;

    pNew = _set_up_constraints(vec_ids);

    pNew = IntroduceBitwiseChoices(pTemp = pNew, vec_ids, _vec_op_greyness, vec_choice2idx);
    Wlc_NtkFree(pTemp);

    return pNew;
}

Wlc_Ntk_t * UfarManager::_introduce_choices(vector<unsigned>& vec_choice2idx, bool fBlack) {
    vector<int> vec_ids = _vec_op_ids;
    Wlc_Ntk_t * pNew, * pTemp;

    pNew = _set_up_constraints(vec_ids);

    Vec_Int_t * vec_ops = collect_boxes(vec_ids, _vec_op_blackbox_marks, fBlack);
    assert(Vec_IntSize(vec_ops) > 0);
    map<int, int> map_temp;
    for(unsigned i = 0; i < vec_ids.size(); i++)
        map_temp[vec_ids[i]] = i;
    Vec_IntSort(vec_ops, 0);
    for(int i = 0; i < Vec_IntSize(vec_ops); i++)
        vec_choice2idx.push_back(map_temp[Vec_IntEntry(vec_ops, i)]);

    pNew = IntroduceChoices(pTemp = pNew, vec_ops);
    Wlc_NtkFree(pTemp);
    Vec_IntFree(vec_ops);

    return pNew;
}

void UfarManager::_compute_core_choices(Wlc_Ntk_t * pChoice, Abc_Cex_t * pCex, vector<unsigned>& vec_cores, int num_sel_pis) {
    int num_ppis = -1;
    Gia_Man_t * pGiaFrames = unroll_with_cex(pChoice, pCex, compute_bit_level_pi_num(_pOrigNtk), num_sel_pis, &num_ppis, false);

    compute_core_using_sat(pGiaFrames, vec_cores, pCex->iFrame+1, num_sel_pis, num_ppis, false, NULL, params.fSatMin);

    Gia_ManStop(pGiaFrames);
}

void UfarManager::_perform_cex_based_white_boxing() {
    const VecVecStr* cex_outputs = _p_cex_mgr->GetOutputs();

    unsigned nFrames = cex_outputs->size();
    assert(nFrames);
    unsigned nOperators = (*cex_outputs)[0].size();
    assert(nOperators == _vec_op_ids.size());

    vector<bool> vec_op_refine(nOperators, false);
    for(unsigned i = 0; i < nOperators; i++) {
        for(unsigned f = 0; f < nFrames; f++) {
            if(!bitstr_all_x((*cex_outputs)[f][i])) {
                vec_op_refine[i] = true;
                break;
            }
        }
    }

    if(log_level() >= 2) {
        _oss.str("");
        _oss << "#vWBs = " << count(vec_op_refine.begin(), vec_op_refine.end(), true) << "(" << nOperators << ")" << "; vWBs = ";
        for(unsigned i = 0; i < nOperators; i++) {
            if(vec_op_refine[i])
                _oss << i << " ";
        }
        LOG(2) << _oss.str();
    }

    for(unsigned i = 0; i < nOperators; i++) {
        if(vec_op_refine[i])
            _vec_op_blackbox_marks[i] = false;
    }
}

void UfarManager::_shrink_final_abstraction() {
    vector<unsigned> vec_choice2idx;
    Wlc_Ntk_t * pNtkWithChoices = _introduce_choices(vec_choice2idx, false /*white*/);

    int num_sel_pis = vec_choice2idx.size();
    int num_other_pis = compute_bit_level_pi_num(pNtkWithChoices) - num_sel_pis;

    Gia_Man_t * pMiter = GetInvMiter(pNtkWithChoices, "inv.pla");
    printf("Miter stat: pi = %d, ff = %d, and = %d, po = %d\n", Gia_ManPiNum(pMiter), Gia_ManRegNum(pMiter), Gia_ManAndNum(pMiter), Gia_ManPoNum(pMiter));

    vector<unsigned> vec_core_choices;
    compute_core_using_sat(pMiter, vec_core_choices, 1, num_sel_pis, num_other_pis, false, NULL, params.fSatMin);

    Wlc_NtkFree(pNtkWithChoices);
    Gia_ManStop(pMiter);

    LOG(2) << "Shrink from " << vec_choice2idx.size() << " to " << vec_core_choices.size();
    if(log_level() >= 3) {
        _oss.str("");
        _oss << "remaining white boxes = ";
        for (auto x : vec_core_choices) {
            _oss << x << " ";
        }
        LOG(3) << _oss.str();
    }

    _vec_op_blackbox_marks = vector<bool>(_vec_op_ids.size(), true);
    for (auto x : vec_core_choices)
        _vec_op_blackbox_marks[vec_choice2idx[x]] = false;
}

void UfarManager::_perform_proof_based_grey_boxing(Abc_Cex_t * pCex) {
    vector<IntPair> vec_choice2idx;
    Wlc_Ntk_t * pNtkWithChoices = _introduce_bitwise_choices(vec_choice2idx);

    vector<unsigned> vec_core_choices;
    _compute_core_choices(pNtkWithChoices, pCex, vec_core_choices, vec_choice2idx.size());
    assert(!vec_core_choices.empty());
    Wlc_NtkFree(pNtkWithChoices);

    if(log_level() >= 4) {
        for (auto x : vec_core_choices) {
            LOG(4) << "WBit : operator[" << vec_choice2idx[x].first << "] at " << vec_choice2idx[x].second << "/" << _vec_op_greyness[vec_choice2idx[x].first].Size() ;
        }
    }

    vector<bool> vec_change_marks(_vec_op_greyness.size(), false);
    for (auto x : vec_core_choices) {
        _vec_op_greyness[vec_choice2idx[x].first].Set(vec_choice2idx[x].second, false);
        vec_change_marks[vec_choice2idx[x].first] = true;
    }

    for (size_t i = 0; i < _vec_op_greyness.size(); ++i) {
        Greyness& grey = _vec_op_greyness[i];
        if(vec_change_marks[i])
            grey.UpdateCost();

        if(grey.IsTooWhite(params.nGrey)) {
            LOG(2) << "Grey: SetWhite: [" << i << "] = " << float(grey.CurrentCost())/float(grey.TotalCost()) << " (" << grey.CurrentCost() << " / " << grey.TotalCost() << ") " << grey.to_string();
            grey.SetWhite();
            _vec_op_blackbox_marks[i] = false;
        }
    }
}

void UfarManager::_perform_proof_based_white_boxing(Abc_Cex_t * pCex) {
    vector<unsigned> vec_choice2idx;
    Wlc_Ntk_t * pNtkWithChoices = _introduce_choices(vec_choice2idx, true /*black*/);

    // for(unsigned i = 0; i < vec_choice2idx.size(); i++) cout << "i = " << i << " idx = " << vec_choice2idx[i] << endl;

    vector<unsigned> vec_core_choices;
    _compute_core_choices(pNtkWithChoices, pCex, vec_core_choices, vec_choice2idx.size());
    assert(!vec_core_choices.empty());
    Wlc_NtkFree(pNtkWithChoices);

    if(log_level() >= 2) {
        _oss.str("");
        _oss << "#vCores = " << vec_core_choices.size() << "; vCores = ";
        for (unsigned i = 0; i < vec_core_choices.size(); i++) {
            _oss << vec_choice2idx[vec_core_choices[i]] << " ";
        }
        LOG(2) << _oss.str();
    }

    if (params.iOneWb == -1) {
        for (unsigned i = 0; i < vec_core_choices.size(); i++)
            _vec_op_blackbox_marks[vec_choice2idx[vec_core_choices[i]]] = false;
    } else if (params.iOneWb == 0) {
        unsigned idx = 0;
        for (auto x : vec_core_choices) {
            if (vec_choice2idx[x] > idx)
                idx = vec_choice2idx[x];
        }
        _vec_op_blackbox_marks[idx] = false;
        LOG(2) << "White boxing ID(" << idx << ")";
    }
}

void UfarManager::DetermineGreyness(Abc_Cex_t *pCex) {
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    _perform_proof_based_grey_boxing(pCex);

    gettimeofday(&t2, NULL);
    profile.tGbRefine += elapsed_time_usec(t1, t2);
}

void UfarManager::DetermineWhiteBoxes(Abc_Cex_t * pCex) {
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    if(params.fCbaWb) {
        _perform_cex_based_white_boxing();
    } else {
        _perform_proof_based_white_boxing(pCex);
    }

    gettimeofday(&t2, NULL);
    profile.tWbRefine += elapsed_time_usec(t1, t2);
}

int UfarManager::VerifyCurrentAbstraction(Abc_Cex_t ** ppCex) {
    timeval t1, t2;
    gettimeofday(&t1, NULL);

    Wlc_Ntk_t * pCurrent = BuildCurrentAbstraction();
    if(!params.fileAbs.empty())
        Wlc_WriteVer(pCurrent, &((params.fileAbs + "_abs.v")[0u]), 0, 0);

    int ret = -1;
    /*
    if(params.fSuper_prove || params.fSimple) {
        ret = super_prove(pCurrent, ppCex, params.fSimple, &params.fileName);
    } else {
        if ( params.fPthread ) {
            ret = verify_model(pCurrent, ppCex, &params.fileName, &params.parSetting, params.fSyn, &_timeout);
        } else {
            ret = bit_level_solve(pCurrent, ppCex, &params.fileName, &params.parSetting, params.fSyn);
        }
    }
    */
    ret = verify_model(pCurrent, ppCex, &params.fileName, &params.parSetting, params.fSyn, &_timeout);
    Wlc_NtkFree(pCurrent);

    gettimeofday(&t2, NULL);
    profile.tBLSolver += elapsed_time_usec(t1, t2);

    return ret;
}

int UfarManager::PerformUIFProve(const timeval& timer) {
    struct Mem {
            Mem() : pCex(NULL), pCex2(NULL) {}
            ~Mem() {
                if (pCex)  Abc_CexFree(pCex);
                if (pCex2) Abc_CexFree(pCex2);
            }
            Abc_Cex_t * pCex;
            Abc_Cex_t * pCex2;
    };

    Mem mem;
    char buffer [256];
    int ret;
    unsigned n_iter_wb = 0;
    unsigned n_iter_uif = 0;
    timeval curTime;
    float elapsedTime;

    auto dump_grey_stat = [&]() {
        if(!params.nGrey || log_level()<2 ) return;
        float stat = 0;
        for(size_t i = 0; i < _vec_op_greyness.size(); ++i) {
            if (_vec_op_greyness[i].IsGrey()) {
                unsigned current_cost = _vec_op_greyness[i].CurrentCost();
                unsigned total_cost = _vec_op_greyness[i].TotalCost();
                float cur_stat = float(current_cost) / float(total_cost);
                stat += cur_stat;
                LOG(2) << "Grey: [" << i << "] = " << setprecision(2) << cur_stat << "\t (" << current_cost << " / "
                       << total_cost << ") \t" << _vec_op_greyness[i].to_string();
            }
        }
        LOG(1) << "Grey: [Total] = " << setprecision(4) << stat << " (" << _vec_op_greyness.size() << ")";
    };
    auto print_stat = [&]() {
        gettimeofday(&curTime, NULL);
        elapsedTime = elapsed_time_usec(timer, curTime)/1000000.0;
        snprintf(buffer, sizeof(buffer), "Iteration[%2u][%3u]: %4lu White boxes\t%4lu UIF constraints (time = %.4f)", n_iter_wb, n_iter_uif, count(_vec_op_blackbox_marks.begin(), _vec_op_blackbox_marks.end(), false), _set_uif_pairs.size(), elapsedTime);
        LOG(1) << buffer << _get_profile_uf_wb();
        dump_grey_stat();
        if(!params.fileStatesOut.empty()) _dump_states(params.fileStatesOut);
    };

    if (!params.fileStatesIn.empty()) {
        _read_states(params.fileStatesIn);
        if (params.iExp != -1) _massage_state_b();
        print_stat();
    }

    if (!params.fLazySim && !params.simSetting.empty()) {
        unsigned origSize = _set_uif_pairs.size();
        LOG(1) << "Try using simulation to find UIF pairs";
        _simulate();
        FindUifPairsUsingSim();
        params.simSetting.clear();
        if (origSize == _set_uif_pairs.size()) {
            LOG(1) << "No new UIF pair is found using simulation";
        } else {
            ++n_iter_uif;
            print_stat();
        }
    }

    while(true) {
        while(true) {
            if (params.fPbaCex && mem.pCex2) {
                if(mem.pCex) Abc_CexFree(mem.pCex);
                mem.pCex = mem.pCex2;
                mem.pCex2 = NULL;
                Wlc_Ntk_t * pCurrent = BuildCurrentAbstraction();
                Wlc_NtkFree(pCurrent);
                ret = 0;
            } else {
                ret = VerifyCurrentAbstraction(&mem.pCex);
            }

            if (ret ==  0) { // SAT
                // GetOperatorsInCex(mem.pCex);
                if (verify_cex_on_original(_pOrigNtk, mem.pCex)) {
                    PrintWordCEX(_pOrigNtk, mem.pCex, &_vec_orig_names);
                    return 0;
                }
                unsigned n_before = _set_uif_pairs.size();

                FindUifPairsUsingCex(mem.pCex, &mem.pCex2);

                if (n_before == _set_uif_pairs.size()) {
                    LOG(1) << "No new UIF pair is found in CEX";

                    if(!params.simSetting.empty()) {
                        LOG(1) << "Try using simulation to find UIF pairs";
                        _simulate();
                        FindUifPairsUsingSim();
                        params.simSetting.clear();
                        if (n_before == _set_uif_pairs.size()) {
                            LOG(1) << "No new UIF pair is found using simulation";
                        }
                    }

                    if (params.nGrey) {
                        DetermineGreyness(mem.pCex);
                    }

                    if (n_before == _set_uif_pairs.size() && !params.nGrey) {
                        break; // entering white-boxing refinement
                    }
                }

                ++n_iter_uif;
                print_stat();

                if(_set_uif_pairs.size() > params.nConstraintLimit)
                    return -1;
            } else if (ret == 1) { // UNSAT
                //_shrink_final_abstraction();
                //print_stat();
                return 1;

            } else {
                return -1;

            }
        }

        DetermineWhiteBoxes(mem.pCex);

        ++n_iter_wb;
        print_stat();
    }
    return -1;
}

void UfarManager::_massage_state_b() {
    for(const auto& x : _set_uif_pairs ) {
        bool first_black = _vec_op_blackbox_marks[x.first.idx];
        bool second_black = _vec_op_blackbox_marks[x.second.idx];
        if (!first_black && !second_black) {
            int to_black_idx = (params.iExp == 0 ? x.second.idx : x.first.idx);
            _vec_op_blackbox_marks[to_black_idx] = true;
            LOG(2) << "Blackbox (" << to_black_idx << ") for UF (" << x.first.idx << ", " << x.second.idx << ")";
        }
    }
}


string UfarManager::_get_profile_uf_wb() {
    if (log_level() <= 4) return "";
    unsigned num_full_white = 0;
    unsigned num_full_black = 0;
    unsigned num_grey = 0;
    for(const auto& x : _set_uif_pairs ) {
        bool first_black = _vec_op_blackbox_marks[x.first.idx];
        bool second_black = _vec_op_blackbox_marks[x.second.idx];
        if(first_black && second_black) {
            ++num_full_black;
        } else if (!first_black && !second_black) {
            ++num_full_white;
            LOG(3) << "ww : (" << x.first.idx << ", " << x.second.idx << ")";
        } else {
            ++num_grey;
        }
    }
    ostringstream oss;
    oss << "; ww = " << num_full_white << "; bb = " << num_full_black << "; gr = " << num_grey <<";";
    return oss.str();
}

void UfarManager::GetOperatorsInCex(Abc_Cex_t *pCex, VecVecStr* pRes) {
    VecVecChar cex_po_values;

    Gia_Man_t * pGia = BitBlast(_pAbsWithAuxPos);
    CollectPoValuesInCex(pGia, pCex, cex_po_values, params.fCexMin);
    Gia_ManStop(pGia);

    unsigned pos;
    for(unsigned f = 0; f < cex_po_values.size(); f++) {
        if (pRes) pRes->push_back(VecStr());
        vector<char>& cur_po_vals = cex_po_values[f];
        pos = 1;
        for(unsigned i = 1; i < Wlc_NtkPoNum(_pAbsWithAuxPos); i++) {
            int range = Wlc_ObjRange(Wlc_NtkPo(_pAbsWithAuxPos, i));
            string bit_str = string(cur_po_vals.begin() + pos, cur_po_vals.begin() + pos + range);
            if (!pRes) {
                cout << "PO[" << i << "]@" << f << " = " << string(bit_str.rbegin(), bit_str.rend()) << endl;
            } else {
                pRes->back().push_back(bit_str);
            }
            pos += range;
        }
    }

}

void UfarManager::DumpParams() const {
    unsigned n_setw = 15;
    cout << "Parameters : " << endl;
    cout << "     " << setw(n_setw) << left << "cexmin" << " : " << (params.fCexMin ? "yes" : "no") << endl;
    cout << "     " << setw(n_setw) << left << "iLogLevel" << " : " << params.iVerbosity << endl;
}

void UfarManager::DumpMgrInfo() const {
    cout << "Operators : " << endl;
    for(unsigned i = 0; i < _vec_op_ids.size(); i++, printf("\n")) {
        cout << "OP_ID = " << i << " : ";
        cout << _vec_orig_names[_vec_op_ids[i]] << " = ";
        cout << _vec_orig_names[Wlc_ObjFaninId0(Wlc_NtkObj(_pOrigNtk, _vec_op_ids[i]))] << " * ";
        cout << _vec_orig_names[Wlc_ObjFaninId1(Wlc_NtkObj(_pOrigNtk, _vec_op_ids[i]))] ;
        cout << (_vec_op_blackbox_marks[i] ? " (black)" : "") ;
    }
}


void UfarManager::_dump_states(const std::string& file) {
    fstream fs;
    fs.open((file + "_s").c_str(), fstream::out);

    if(!fs.is_open()) {
        cerr << "Cannot open the file for dumping states.\n";
        return;
    }

    fs << "B\n";
    for (int i = 0; i < _vec_op_blackbox_marks.size(); ++i) {
        fs << (_vec_op_blackbox_marks[i] == true ? "1" : "0");
    }
    fs << "\nP\n";
    for (const auto& x : _set_uif_pairs) {
        fs << x.first.idx << "," << x.first.timediff << ",";
        fs << x.second.idx << "," << x.second.timediff << ",";
        fs << (x.fMark == true ? "1" : "0") << "\n";
    }

    fs.close();
}

void UfarManager::_read_states(const std::string &file) {
    fstream fs;
    fs.open(file.c_str(), fstream::in);

    if(!fs.is_open()) {
        cerr << "Cannot open the file for reading states.\n";
        return;
    }

    string line;
    getline(fs, line);
    assert(line == "B");
    getline(fs, line);
    set_state_b(_vec_op_blackbox_marks, line);
    getline(fs, line);
    assert(line == "P");
    while(getline(fs, line)) {
        set_state_p(_set_uif_pairs, line);
    }

    if(log_level() >= 3) print_blackboxes(_vec_op_blackbox_marks);
    if(log_level() >= 3) print_pairs(_set_uif_pairs);

    fs.close();
}

 Wlc_Ntk_t * UfarManager::_abstract_operators(Wlc_Ntk_t * pNtk, const vector<int>& vec_ids) const {
    Vec_Int_t * vec_ops = collect_boxes(vec_ids, _vec_op_blackbox_marks, true /*black*/);
    assert(Vec_IntSize(vec_ops) > 0);

    Wlc_Ntk_t * pNew = NULL;
    pNew = AbstractNodes(pNtk, vec_ops);

    Vec_IntFree(vec_ops);

    return pNew;
}

}

ABC_NAMESPACE_IMPL_END
