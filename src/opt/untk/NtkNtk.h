/*
 * NtkNtk.h
 *
 *  Created on: Aug 25, 2015
 *      Author: Yen-Sheng Ho
 */

#ifndef SRC_EXT2_NTK_NTKNTK_H_
#define SRC_EXT2_NTK_NTKNTK_H_

#include <set>
#include <vector>
#include <string>
#include <array>
#include <sstream>
#include <algorithm>

#include <base/wlc/wlc.h>
#include "Netlist.h"

ABC_NAMESPACE_CXX_HEADER_START

typedef struct Wlc_Ntk_t_ Wlc_Ntk_t;
typedef struct Abc_Cex_t_ Abc_Cex_t;
typedef struct Vec_Int_t_ Vec_Int_t;
typedef struct Gia_Man_t_ Gia_Man_t;

namespace UFAR {

using VecVecChar = std::vector<std::vector<char> >;
using VecVecInt  = std::vector<std::vector<int> >;
using IntPair = std::pair<int, int>;

struct OperatorID {
        OperatorID() : idx(-1), timediff(0) {}
        OperatorID(int i) : idx(i), timediff(0) {}
        OperatorID(int i, int t) : idx(i), timediff(t) {}
        bool operator< (const OperatorID& rhs) const {
            if (timediff != rhs.timediff) return (timediff < rhs.timediff);
            return (idx < rhs.idx);
        }
        bool operator!= (const OperatorID& rhs) const {
            return ((idx != rhs.idx) || (timediff != rhs.timediff));
        }
        int idx;
        int timediff;
};

std::ostream& operator<<(std::ostream& os, const OperatorID& obj);

struct UifPair {
        UifPair(const OperatorID& first_, const OperatorID& second_) : first(first_), second(second_), fMark(false) {}
        UifPair(const OperatorID& first_, const OperatorID& second_, bool fMark_) : first(first_), second(second_), fMark(fMark_) {}
        bool operator< (const UifPair& rhs) const {
            if(first  != rhs.first)  return (first < rhs.first);
            if(second != rhs.second) return (second < rhs.second);
            return (!fMark && rhs.fMark);
        }
        OperatorID first;
        OperatorID second;
        bool fMark;
};

class Greyness {
public:
    Greyness(Wlc_Ntk_t * pNtk, Wlc_Obj_t * pObj);

    std::string to_string() const {
        std::ostringstream oss;
        for (size_t i = 0; i < _vec_black_bits.size(); ++i)
            oss << ( _vec_black_bits[i] ? '0' : '1' );
        return oss.str();
    }

    bool IsGrey() const {
        return (!IsBlack() && !IsWhite());
    }
    bool IsWhite() const {
        return (std::find(_vec_black_bits.begin(), _vec_black_bits.end(), true) == _vec_black_bits.end());
    }
    bool IsBlack() const {
        return (std::find(_vec_black_bits.begin(), _vec_black_bits.end(), false) == _vec_black_bits.end());
    }
    unsigned TotalCost() const { return _total_cost; }
    unsigned CurrentCost() const { return _current_cost; }
    void UpdateCost();

    size_t Size() const { return _vec_black_bits.size(); }
    bool Get(size_t pos) const { return _vec_black_bits[pos]; }
    void Set(size_t pos, bool val) { _vec_black_bits[pos] = val; }

    void SetWhite() {
        _vec_black_bits = std::vector<bool>(_vec_black_bits.size(), false);
        _current_cost = _total_cost;
    }
    bool IsTooWhite(float threshold) const {
        float ratio = float(_current_cost) / float(_total_cost);
        if ((ratio > threshold) || (_current_cost == _total_cost))
            return true;
        if (ratio > 0.5 && _total_cost < 1000)
            return true;
        return false;
    }

private:
    std::vector<bool> _vec_black_bits;
    unsigned          _total_cost;
    unsigned          _current_cost;
    unsigned          _orig_size;
    WNetlist          _N_white;
    int               _iOpId;
};

Wlc_Ntk_t * AbstractNodes( Wlc_Ntk_t * p, Vec_Int_t * vNodesInit );
Wlc_Ntk_t * AddConstFlops( Wlc_Ntk_t * p, const std::set<unsigned>& types );
Wlc_Ntk_t * IntroduceChoices( Wlc_Ntk_t * p, Vec_Int_t * vNodes );
Wlc_Ntk_t * IntroduceBitwiseChoices( Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids, const std::vector<Greyness>& vec_greys, std::vector<IntPair>& vec_choice2idx );
Wlc_Ntk_t * CreateMiter(Wlc_Ntk_t *pNtk, bool fXor);
Wlc_Ntk_t * NormalizeDataTypes(Wlc_Ntk_t * p, const std::set<unsigned>& types, bool fUnify);
Wlc_Ntk_t * AddAuxPOsForOperators(Wlc_Ntk_t * p, std::vector<int>& vec_ids, int max_input_bw = -1, int max_output_bw = -1);
Wlc_Ntk_t * RemoveAuxPOs(Wlc_Ntk_t * p, int iStart);
Wlc_Ntk_t * DupNtkAndUpdateIDs(Wlc_Ntk_t * p, std::vector<int>& vec_ids);
Wlc_Ntk_t * ApplyGreynessConstraints(Wlc_Ntk_t * pNtk, const std::vector<Greyness>& vec_grey, std::vector<int>& vec_ids);
Wlc_Ntk_t * IntroducePrevOperators(Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids, const std::set<OperatorID>& set_prev_ops, VecVecInt& vv_op_ffs);
Wlc_Ntk_t * ApplyGreyConstraints(Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids, bool fSeq);
int         AddOneFanoutFF(Wlc_Ntk_t * pNtk, int obj_id, unsigned& count_bits);
int         AddOneUifImplication(Wlc_Ntk_t * pNtk, const std::array<int, 3>& wires1, const std::array<int, 3>& wires2);
void        FoldCombConstraints(Wlc_Ntk_t *pNtk, Vec_Int_t *vConstrs);
void        FoldSeqConstraints(Wlc_Ntk_t *pNtk, Vec_Int_t *vConstrs);
void        CollectPoValuesInCex(Gia_Man_t * pGia, Abc_Cex_t * pCex, VecVecChar& po_values, bool fCexMin);
bool        HasOperator(const Wlc_Ntk_t * p, const std::set<unsigned>& types);

void        ComputeMaxBW(Wlc_Ntk_t * p, const std::vector<int>& vec_ids, int& max_input_bw, int& max_output_bw );

void        PrintWordCEX(Wlc_Ntk_t * pNtk, Abc_Cex_t * pCex, const std::vector<std::string>* names = nullptr);

unsigned    compute_bit_level_pi_num(Wlc_Ntk_t * pNtk);

int         verify_model(Wlc_Ntk_t * pNtk, Abc_Cex_t ** ppCex, const std::string* pFileName = NULL, const std::string* pParSetting = NULL, bool fSyn = false, struct timespec * timeout = NULL);
int         bit_level_solve(Wlc_Ntk_t * pNtk, Abc_Cex_t ** ppCex, const std::string* pFileName = NULL, const std::string* pParSetting = NULL, bool fSyn = false);

Gia_Man_t * BitBlast(Wlc_Ntk_t * pNtk);

Gia_Man_t * GetInvMiter(Wlc_Ntk_t * pNtk, char * nameInv);
void        TestInvariant(std::string& nameNtk, std::string& nameInv);

Wlc_Ntk_t * MakeUnderApprox(Wlc_Ntk_t * pNtk, int num_bits);
Wlc_Ntk_t * MakeUnderApprox2(Wlc_Ntk_t * pNtk, const std::set<unsigned>& types, int num_bits);


}

ABC_NAMESPACE_CXX_HEADER_END

#endif /* SRC_EXT2_NTK_NTKNTK_H_ */
