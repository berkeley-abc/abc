/*
 * NtkNtk.cpp
 *
 *  Created on: Aug 25, 2015
 *      Author: Yen-Sheng Ho
 */

#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif
#include <fstream>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <algorithm>
#include <cctype>

#include <base/wlc/wlc.h>
#include <sat/bmc/bmc.h>
#include <sat/bsat/satSolver.h>
#include <proof/pdr2/pdr2.h>
#include <aig/saig/saig.h>
#include <proof/fraig/fraig.h>
#include <aig/gia/giaAig.h>
#include <base/io/ioAbc.h>

#include "opt/util/util.h"
#include "NtkNtk.h"
#include "Netlist.h"

ABC_NAMESPACE_HEADER_START
    //int Wlc_ObjDup( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, int iObj, Vec_Int_t * vFanins );
    void Wlc_NtkDupDfs_rec( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, int iObj, Vec_Int_t * vFanins );
    //void Wlc_ObjSetCo( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int fFlopInput );
    Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    Gia_Man_t * Gia_ManDupInvMiter( Gia_Man_t * p, Gia_Man_t * pInv );
    Gia_Man_t * Wlc_NtkBitBlast2( Wlc_Ntk_t * p, Vec_Int_t * vBoxIds );
    //void Gia_ManPrintStats( Gia_Man_t * p, Gps_Par_t * pPars );
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

using namespace std;

namespace UFAR {

static inline int create_buffer(Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Int_t * vFanins, int max_bw) {
    return Wlc_ObjCreate(p, WLC_OBJ_BUF, Wlc_ObjIsSigned(pObj), (max_bw == -1 ? Wlc_ObjRange(pObj) - 1 : max_bw - 1), 0, vFanins);
}

Gia_Man_t * BitBlast(Wlc_Ntk_t * pNtk) {
    Wlc_BstPar_t Par, * pPar = &Par;
    Wlc_BstParDefault( pPar );
    Gia_Man_t * pGia = Wlc_NtkBitBlast(pNtk, pPar);
    if ( pGia == NULL )
        return NULL;
    if ( pGia->pName == NULL )
        pGia->pName = Abc_UtilStrsav( pNtk->pName ? pNtk->pName : pNtk->pSpec );
    if ( pGia->pSpec == NULL )
        pGia->pSpec = Abc_UtilStrsav( pNtk->pName ? pNtk->pName : pNtk->pSpec );
    return pGia;
}

template<typename Functor>
void ModifyMarkedNodes(Wlc_Ntk_t * pNtk, int nOrigObjNum, Functor get_modified_node) {
    Wlc_Obj_t * pObj;
    int i, k, iFanin, iObj;
    // iterate through the nodes in the DFS order
    Wlc_NtkForEachObj( pNtk, pObj, i ) {
        if (i == nOrigObjNum) {
            // cout << "break at " << i << endl;
            break;
        }
        if (pObj->Mark) {
            pObj->Mark = 0;
            iObj = get_modified_node(pObj);
        } else {
            // update fanins
            Wlc_ObjForEachFanin( pObj, iFanin, k )
                Wlc_ObjFanins(pObj)[k] = Wlc_ObjCopy(pNtk, iFanin);
            // node to remain
            iObj = i;
        }
        Wlc_ObjSetCopy( pNtk, i, iObj );
    }

    Wlc_NtkForEachCo( pNtk, pObj, i )
    {
        iObj = Wlc_ObjId(pNtk, pObj);
        if (iObj != Wlc_ObjCopy(pNtk, iObj)) {
            assert(pObj->fIsFi);
            Wlc_NtkObj(pNtk, Wlc_ObjCopy(pNtk, iObj))->fIsFi = 1;
            Vec_IntWriteEntry(&pNtk->vCos, i, Wlc_ObjCopy(pNtk, iObj));
        }
    }
}


Greyness::Greyness(Wlc_Ntk_t * pNtk, Wlc_Obj_t * pOpObj) {
    auto compute_cone_size = [&](Wlc_Ntk_t * pOrig, const vector<int>& ids, Vec_Int_t * vFanins) {
        int i;
        Wlc_Obj_t * pObj;
        WNetlist N;
        Wlc_Ntk_t * pNew = N.GetNtk();
        Wlc_NtkForEachCi( pOrig, pObj, i ) {
            int iNewPi = Wlc_ObjAlloc(pNew, WLC_OBJ_PI, Wlc_ObjIsSigned(pObj), Wlc_ObjRange(pObj) - 1, 0);
            Wlc_ObjSetCopy(pOrig, Wlc_ObjId(pOrig, pObj), iNewPi);
        }

        for(auto x : ids)
            Wlc_NtkDupDfs_rec( pNew, pOrig, x, vFanins );
        for(auto x : ids)
            Wlc_ObjSetCo( pNew, Wlc_NtkObj(pNew, Wlc_ObjCopy(pOrig, x)), 0 );

        Gia_Man_t * pGia = BitBlast(pNew);
        int cone_size = Gia_ManAndNum(pGia);
        Gia_ManStop(pGia);

        return cone_size;
    };

    _current_cost = 0;

    _vec_black_bits.resize(Wlc_ObjRange(pOpObj), true);
    
    int iOpId = Wlc_ObjId(pNtk, pOpObj);

    _N_white = pNtk;
    Wlc_Ntk_t * pOrig = _N_white.GetNtk();

    iOpId = Wlc_ObjCopy(pNtk, iOpId);
    pOpObj = Wlc_NtkObj(pOrig, iOpId);
    _iOpId = iOpId;
    int iFin0 = Wlc_ObjFaninId0(pOpObj);
    int iFin1 = Wlc_ObjFaninId1(pOpObj);

    Vec_Int_t * vFanins = Vec_IntAlloc(100);

    Wlc_NtkCleanCopy( pOrig );
    int out_size = compute_cone_size(pOrig, vector<int>{iOpId}, vFanins);
    Wlc_NtkCleanCopy( pOrig );
    int in_size = compute_cone_size(pOrig, vector<int>{iFin0, iFin1}, vFanins);

    assert(out_size >= in_size);
    _total_cost = unsigned(out_size - in_size);

    Gia_Man_t * pGia = BitBlast(pOrig);
    _orig_size = unsigned(Gia_ManAndNum(pGia));
    Gia_ManStop(pGia);

    Vec_IntFree(vFanins);
}

void Greyness::UpdateCost() {
    Wlc_Ntk_t * pOrig = _N_white.GetNtk();
    Wlc_Obj_t * pOpObj = Wlc_NtkObj(pOrig, _iOpId);
    int         iOpObj = _iOpId;
    int offset = pOpObj->Beg;
    int range = Wlc_ObjRange(pOpObj);
    int is_signed = Wlc_ObjIsSigned(pOpObj);

    Wlc_NtkCleanCopy( pOrig );
    WNetlist N_Grey( pOrig );
    Wlc_Ntk_t * pGrey = N_Grey.GetNtk();
    Wlc_NtkCleanCopy( pGrey );
    int nOrigObjNum = Wlc_NtkObjNumMax( pGrey );
    iOpObj = Wlc_ObjCopy(pOrig, iOpObj);
    Wlc_NtkObj(pGrey, iOpObj)->Mark = 1;
    int iPPI = Wlc_ObjAlloc(pGrey, WLC_OBJ_PI, is_signed, range - 1, 0);

    auto create_grey_output = [&](Wlc_Obj_t * pObj){
        Vec_Int_t * vFanins = Vec_IntAlloc(3);
        Vec_Int_t * vFanins2 = Vec_IntAlloc(3);

        for (size_t i = 0; i < _vec_black_bits.size(); ++i) {
            Vec_IntClear(vFanins2);
            if (_vec_black_bits[i])
                Vec_IntPush(vFanins2, iPPI);
            else
                Vec_IntPush(vFanins2, iOpObj);
            Vec_IntPushTwo(vFanins2, i + offset, i + offset);
            Vec_IntPush(vFanins, Wlc_ObjCreate(pGrey, WLC_OBJ_BIT_SELECT, 0, 0, 0, vFanins2));
        }
        Vec_IntReverseOrder(vFanins);
        int iObj = Wlc_ObjCreate(pGrey, WLC_OBJ_BIT_CONCAT, is_signed, range - 1, 0, vFanins);

        Vec_IntFree(vFanins);
        Vec_IntFree(vFanins2);

        return iObj;
    };

    ModifyMarkedNodes(pGrey, nOrigObjNum, create_grey_output);

    WNetlist N_result(pGrey);

    Gia_Man_t * pGia = BitBlast(N_result.GetNtk());
    unsigned grey_size = unsigned(Gia_ManAndNum(pGia));
    Gia_ManStop(pGia);

    assert(_orig_size >= grey_size);
    _current_cost = _total_cost - (_orig_size - grey_size);
}

unsigned compute_bit_level_pi_num(Wlc_Ntk_t * pNtk) {
    unsigned num = 0;
    int i;
    Wlc_Obj_t * pObj;
    Wlc_NtkForEachPi(pNtk, pObj, i) {
        num += Wlc_ObjRange(pObj);
    }
    return num;
}

void DumpWlcNtk(Wlc_Ntk_t * pNtk) {
    int i, k, iFanin;
    Wlc_Obj_t * pObj;
    Wlc_NtkForEachObj(pNtk, pObj, i) {
        cout << i << " <-- ";
        Wlc_ObjForEachFanin( pObj, iFanin, k ) {
            cout << iFanin << " ";
        }
        cout << endl;
    }
}

Wlc_Ntk_t * DupNtkAndUpdateIDs(Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids) {
    Wlc_Ntk_t * p = Wlc_NtkDupDfsSimple(pNtk);
    for(unsigned i = 0; i < vec_ids.size(); i++) {
        vec_ids[i] = Wlc_ObjCopy(pNtk, vec_ids[i]);
    }
    return p;
}

int AddOneFanoutFF(Wlc_Ntk_t * pNtk, int obj_id, unsigned& count_bits) {
     Vec_Int_t * vFanins = Vec_IntAlloc( 1 );

     int range = Wlc_ObjRange(Wlc_NtkObj(pNtk, obj_id));

     // create flop
     int fo = Wlc_ObjCreate( pNtk, WLC_OBJ_FO, Wlc_ObjIsSigned(Wlc_NtkObj(pNtk, obj_id)), range-1, 0, vFanins );
     (void)fo;

     // set up FI
     Wlc_NtkObj(pNtk, obj_id)->fIsFi = 1;

     // push FI
     Vec_IntPush(&pNtk->vCos, obj_id);

     // push vInits
     if ( pNtk->vInits == NULL ) {
         pNtk->vInits = Vec_IntAlloc( 100 );
     }
     Vec_IntPush( pNtk->vInits, -range );

     count_bits += range;

     Vec_IntFree( vFanins );

     assert(Wlc_NtkCi(pNtk, Wlc_NtkCiNum(pNtk)-1) == Wlc_NtkObj(pNtk, fo));
     return Wlc_NtkCiNum(pNtk) - 1;
}

Wlc_Ntk_t * IntroducePrevOperators(Wlc_Ntk_t * pNtk, vector<int>& vec_ids, const set<OperatorID>& set_prev_ops, VecVecInt& vv_op_ffs) {
    array<int, 3> wires;
    unsigned count_bits = 0;

    vv_op_ffs = vector<vector<int> >(vec_ids.size(), vector<int>());
    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);

    for(auto it = set_prev_ops.begin(); it != set_prev_ops.end(); it++) {
        int idx = it->idx;
        int prev_idx = 0 - it->timediff - 1;
        assert(idx < vv_op_ffs.size());
        assert(prev_idx >= 0);

        for(int i = 0; i <= prev_idx; i++) {
            if(i < vv_op_ffs[idx].size()) continue;
            assert(i == vv_op_ffs[idx].size());

            if(i == 0) {
                wires[2] = vec_ids[idx];
                wires[0] = Wlc_ObjFaninId0(Wlc_NtkObj(p, vec_ids[idx]));
                wires[1] = Wlc_ObjFaninId1(Wlc_NtkObj(p, vec_ids[idx]));
            } else {
                wires[2] = Wlc_ObjId(p, Wlc_NtkCi(p, vv_op_ffs[idx][i-1]));
                wires[1] = Wlc_ObjId(p, Wlc_NtkCi(p, vv_op_ffs[idx][i-1]) - 1);
                wires[0] = Wlc_ObjId(p, Wlc_NtkCi(p, vv_op_ffs[idx][i-1]) - 2);
            }

            AddOneFanoutFF(p, wires[0], count_bits);
            AddOneFanoutFF(p, wires[1], count_bits);
            vv_op_ffs[idx].push_back(AddOneFanoutFF(p, wires[2], count_bits));
        }
    }

    if (p->pInits) {
        char * pStr = strcpy(
                ABC_ALLOC(char, strlen(p->pInits) + count_bits + 1),
                p->pInits);
        for (unsigned i = 0; i < count_bits; ++i) {
            pStr[strlen(p->pInits) + i] = '0';
        }
        pStr[strlen(p->pInits) + count_bits] = '\0';
        ABC_FREE(p->pInits);
        p->pInits = pStr;
    }

    Wlc_Ntk_t * pNew = DupNtkAndUpdateIDs(p, vec_ids);
    Wlc_NtkFree(p);
    return pNew;
}

int AddZeroImplication(Wlc_Ntk_t * pNtk, const array<int, 3>& wires)
{
    int iFaninNew;
    int iObjNew, iObjNew2;
    int iObjConst0;

    Vec_Int_t * vFanins = Vec_IntAlloc( 2 );
    Vec_Int_t * vCompares = Vec_IntAlloc( 2 );

    Vec_IntFill(vFanins, 1, 0);
    iObjConst0 = Wlc_ObjCreate(pNtk, WLC_OBJ_CONST, 0, 0, 0, vFanins);

    Vec_IntFillTwo( vFanins, 2, wires[0], iObjConst0);
    iFaninNew = Wlc_ObjCreate( pNtk, WLC_OBJ_COMP_NOTEQU, 0, 0, 0, vFanins );
    Vec_IntPush( vCompares, iFaninNew );

    Vec_IntFillTwo( vFanins, 2, wires[1], iObjConst0);
    iFaninNew = Wlc_ObjCreate( pNtk, WLC_OBJ_COMP_NOTEQU, 0, 0, 0, vFanins );
    Vec_IntPush( vCompares, iFaninNew );

    // concatenate fanin comparators
    iObjNew = Wlc_ObjCreate( pNtk, WLC_OBJ_BIT_CONCAT, 0, Vec_IntSize(vCompares) - 1, 0, vCompares );
    // create reduction-AND node
    Vec_IntFill( vFanins, 1, iObjNew );
    iObjNew = Wlc_ObjCreate( pNtk, WLC_OBJ_REDUCT_AND, 0, 0, 0, vFanins );

    // create output comparator node
    Vec_IntFillTwo( vFanins, 2, wires[2], iObjConst0 );
    iObjNew2 = Wlc_ObjCreate( pNtk, WLC_OBJ_COMP_EQU, 0, 0, 0, vFanins );
    // create implication node (iObjNew is already complemented above)
    Vec_IntFillTwo( vFanins, 2, iObjNew, iObjNew2 );
    iObjNew = Wlc_ObjCreate( pNtk, WLC_OBJ_LOGIC_OR, 0, 0, 0, vFanins );

    Vec_IntFree( vCompares );
    Vec_IntFree( vFanins );

    return iObjNew;
}

int AddOneUifImplication(Wlc_Ntk_t * pNtk, const array<int, 3>& wires1, const array<int, 3>& wires2)
{
    int iFaninNew;
    int iObjNew, iObjNew2;

    Vec_Int_t * vFanins = Vec_IntAlloc( 2 );
    Vec_Int_t * vCompares = Vec_IntAlloc( 2 );

    Vec_IntFillTwo( vFanins, 2, wires1[0], wires2[0]);
    iFaninNew = Wlc_ObjCreate( pNtk, WLC_OBJ_COMP_NOTEQU, 0, 0, 0, vFanins );
    Vec_IntPush( vCompares, iFaninNew );

    Vec_IntFillTwo( vFanins, 2, wires1[1], wires2[1]);
    iFaninNew = Wlc_ObjCreate( pNtk, WLC_OBJ_COMP_NOTEQU, 0, 0, 0, vFanins );
    Vec_IntPush( vCompares, iFaninNew );

    // concatenate fanin comparators
    iObjNew = Wlc_ObjCreate( pNtk, WLC_OBJ_BIT_CONCAT, 0, Vec_IntSize(vCompares) - 1, 0, vCompares );
    // create reduction-OR node
    Vec_IntFill( vFanins, 1, iObjNew );
    iObjNew = Wlc_ObjCreate( pNtk, WLC_OBJ_REDUCT_OR, 0, 0, 0, vFanins );
    // create output comparator node
    Vec_IntFillTwo( vFanins, 2, wires1[2], wires2[2] );
    iObjNew2 = Wlc_ObjCreate( pNtk, WLC_OBJ_COMP_EQU, 0, 0, 0, vFanins );
    // create implication node (iObjNew is already complemented above)
    Vec_IntFillTwo( vFanins, 2, iObjNew, iObjNew2 );
    iObjNew = Wlc_ObjCreate( pNtk, WLC_OBJ_LOGIC_OR, 0, 0, 0, vFanins );

    Vec_IntFree( vCompares );
    Vec_IntFree( vFanins );

    return iObjNew;
}

int AddOneGrey(Wlc_Ntk_t * pNtk, const array<int, 3>& wires, const Greyness& greyness) {
    Vec_Int_t * vFanins = Vec_IntAlloc( 3 );
    Vec_Int_t * vEquals = Vec_IntAlloc( 32 );

    Vec_IntFillTwo(vFanins, 2, wires[0], wires[1]);
    Wlc_Obj_t * pOrigOut = Wlc_NtkObj(pNtk, wires[2]);
    int iShadowOut = Wlc_ObjCreate(pNtk, pOrigOut->Type, Wlc_ObjIsSigned(pOrigOut), pOrigOut->End, pOrigOut->Beg, vFanins);
    int offset = pOrigOut->Beg;

    for (size_t pos = 0; pos < greyness.Size(); ++pos) {
        // black bit : do nothing
        if (greyness.Get(pos)) continue;

        // white bit
        Vec_IntClear(vFanins);
        Vec_IntPush(vFanins, wires[2]);
        Vec_IntPushTwo(vFanins, pos + offset, pos + offset);
        int iOrigBit = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_SELECT, 0, 0, 0, vFanins);
        Vec_IntClear(vFanins);
        Vec_IntPush(vFanins, iShadowOut);
        Vec_IntPushTwo(vFanins, pos + offset, pos + offset);
        int iShadowBit = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_SELECT, 0, 0, 0, vFanins);

        Vec_IntFillTwo(vFanins, 2, iOrigBit, iShadowBit);
        Vec_IntPush(vEquals, Wlc_ObjCreate(pNtk, WLC_OBJ_COMP_EQU, 0, 0, 0, vFanins));
    }

    int iConcat = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_CONCAT, 0, Vec_IntSize(vEquals)-1, 0, vEquals);
    Vec_IntFill(vFanins, 1, iConcat);
    int iRes = Wlc_ObjCreate(pNtk, WLC_OBJ_REDUCT_AND, 0, 0, 0, vFanins);

    Vec_IntFree( vFanins );
    Vec_IntFree( vEquals );

    return iRes;
}

Wlc_Ntk_t * ApplyGreynessConstraints(Wlc_Ntk_t * pNtk, const vector<Greyness>& vec_grey, vector<int>& vec_ids) {
    array<int, 3> wires;

    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);
    Vec_Int_t * vGreyConstrs = Vec_IntAlloc( vec_ids.size() );

    for (size_t i = 0; i < vec_ids.size(); ++i) {
        if(!vec_grey[i].IsGrey()) continue;

        int iOut = vec_ids[i];
        wires[2] = iOut;
        wires[0] = Wlc_ObjFaninId0(Wlc_NtkObj(p, iOut));
        wires[1] = Wlc_ObjFaninId1(Wlc_NtkObj(p, iOut));
        Vec_IntPush(vGreyConstrs, AddOneGrey(p, wires, vec_grey[i]));
    }

    if (Wlc_NtkFfNum(p) == 0)
        FoldCombConstraints(p, vGreyConstrs);
    else
        FoldSeqConstraints(p, vGreyConstrs);

    Wlc_Ntk_t * pNew = DupNtkAndUpdateIDs(p, vec_ids);

    Wlc_NtkFree(p);
    Vec_IntFree(vGreyConstrs);

    return pNew;
}

Wlc_Ntk_t * ApplyGreyConstraints(Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids, bool fSeq) {
    array<int, 3> wires;

    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);
    Vec_Int_t * vGreyConstrs = Vec_IntAlloc( vec_ids.size() );

    for(auto& x : vec_ids) {
        wires[2] = x;
        wires[0] = Wlc_ObjFaninId0(Wlc_NtkObj(p, x));
        wires[1] = Wlc_ObjFaninId1(Wlc_NtkObj(p, x));
        int iObj = AddZeroImplication(p, wires);
        Vec_IntPush(vGreyConstrs, iObj);
    }

    if (!fSeq)
        FoldCombConstraints(p, vGreyConstrs);
    else
        FoldSeqConstraints(p, vGreyConstrs);

    Wlc_Ntk_t * pNew = DupNtkAndUpdateIDs(p, vec_ids);

    Wlc_NtkFree(p);
    Vec_IntFree(vGreyConstrs);

    return pNew;
}

void FoldSeqConstraints(Wlc_Ntk_t *pNtk, Vec_Int_t *vConstrs)
{
     if (Vec_IntSize(vConstrs) == 0) return;

     int iObjNew;
     Vec_Int_t * vFanins = Vec_IntAlloc( 100 );

     // derive the AND of the UIF constraints
     assert(Vec_IntSize(vConstrs) > 0);
     if (Vec_IntSize(vConstrs) == 1)
         iObjNew = Vec_IntEntry(vConstrs, 0);
     else {
         // concatenate
         iObjNew = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_CONCAT, 0,
                 Vec_IntSize(vConstrs) - 1, 0, vConstrs);
         // create reduction-AND node
         Vec_IntFill(vFanins, 1, iObjNew);
         iObjNew = Wlc_ObjCreate(pNtk, WLC_OBJ_REDUCT_AND, 0, 0, 0, vFanins);
     }

     // create flop
     int iObjFO = 0;
     int iObjFI = 0;
     int iObjNegAllConstraints = 0;
     Vec_IntClear(vFanins);
     iObjFO = Wlc_ObjCreate(pNtk, WLC_OBJ_FO, 0, 0, 0, vFanins);
     Vec_IntFill(vFanins, 1, iObjNew);
     iObjNegAllConstraints = Wlc_ObjCreate(pNtk, WLC_OBJ_LOGIC_NOT, 0, 0, 0, vFanins);
     Vec_IntFillTwo(vFanins, 2, iObjNegAllConstraints, iObjFO);
     iObjFI = Wlc_ObjCreate(pNtk, WLC_OBJ_LOGIC_OR, 0, 0, 0, vFanins);
     Wlc_NtkObj(pNtk, iObjFI)->fIsFi = 1;

     if (pNtk->pInits) {
         char * pStr = strcpy(ABC_ALLOC(char, strlen(pNtk->pInits) + 2), pNtk->pInits);
         pStr[strlen(pNtk->pInits)] = '0';
         pStr[strlen(pNtk->pInits) + 1] = '\0';
         ABC_FREE(pNtk->pInits);
         pNtk->pInits = pStr;
         // push vInits
         Vec_IntPush( pNtk->vInits, -1 );
     }

     //Vec_IntPush(&p->vCis, iObjFO);
     Vec_IntPush(&pNtk->vCos, iObjFI);

     // update PO
     Vec_IntFill(vFanins, 1, iObjFI);
     int iObjNegFI = Wlc_ObjCreate(pNtk, WLC_OBJ_LOGIC_NOT, 0, 0, 0, vFanins);
     int iObjPO = Wlc_ObjId(pNtk, Wlc_NtkPo(pNtk, 0));
     Vec_IntFillTwo(vFanins, 2, iObjNegFI, iObjPO);
     int iObjNewPO = Wlc_ObjCreate(pNtk, WLC_OBJ_LOGIC_AND, 0, 0, 0, vFanins);

     Vec_IntWriteEntry(&pNtk->vPos, 0, iObjNewPO);
     Vec_IntWriteEntry(&pNtk->vCos, 0, iObjNewPO);

     Wlc_NtkObj(pNtk, iObjNewPO)->fIsPo = 1;
     Wlc_NtkObj(pNtk, iObjPO)->fIsPo = 0;

     Vec_IntFree( vFanins );
}

void FoldCombConstraints(Wlc_Ntk_t *pNtk, Vec_Int_t *vConstrs)
{
     if (Vec_IntSize(vConstrs) == 0) return;

     int iObjNew;
     Vec_Int_t * vFanins = Vec_IntAlloc( 100 );

     // derive the AND of the UIF constraints
     assert(Vec_IntSize(vConstrs) > 0);
     if (Vec_IntSize(vConstrs) == 1)
         iObjNew = Vec_IntEntry(vConstrs, 0);
     else {
         // concatenate
         iObjNew = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_CONCAT, 0,
                 Vec_IntSize(vConstrs) - 1, 0, vConstrs);
         // create reduction-AND node
         Vec_IntFill(vFanins, 1, iObjNew);
         iObjNew = Wlc_ObjCreate(pNtk, WLC_OBJ_REDUCT_AND, 0, 0, 0, vFanins);
     }

     // update PO
     int iObjPO = Wlc_ObjId(pNtk, Wlc_NtkPo(pNtk, 0));
     Vec_IntFillTwo(vFanins, 2, iObjNew, iObjPO);
     int iObjNewPO = Wlc_ObjCreate(pNtk, WLC_OBJ_LOGIC_AND, 0, 0, 0, vFanins);

     Vec_IntWriteEntry(&pNtk->vPos, 0, iObjNewPO);
     Vec_IntWriteEntry(&pNtk->vCos, 0, iObjNewPO);

     Wlc_NtkObj(pNtk, iObjNewPO)->fIsPo = 1;
     Wlc_NtkObj(pNtk, iObjPO)->fIsPo = 0;

     Vec_IntFree( vFanins );
}

static bool isPIAndDontCare(Gia_Man_t * pGia, Gia_Obj_t * pObj, Abc_Cex_t * pCare, int f) {
    if(!Gia_ObjIsPi(pGia, pObj)) return false;
    if(!pCare) return false;

    if(!Abc_InfoHasBit(pCare->pData, pCare->nRegs + pCare->nPis * f + pObj->Value))
        return true;

    return false;
}

void CollectPoValuesInCex(Gia_Man_t * pGia, Abc_Cex_t * pCex, VecVecChar& po_values, bool fCexMin)
{
    assert(po_values.empty());

    int k, iBit;
    Gia_Obj_t * pObj, * pObjRi, *pObjRo;

    Abc_Cex_t * pCare = NULL;
    if (fCexMin) {
        pCare = Bmc_CexCareMinimizeAig(pGia, Gia_ManPiNum(pGia), pCex, 1, 0, 0);
        assert(pCare != NULL);

        Gia_ManCleanValue(pGia);
        Gia_ManForEachPi( pGia, pObj, k )
            pObj->Value = k;
    }

    Gia_ManCleanMark0(pGia);

    iBit = pCex->nRegs;

    for ( int f = 0; f <= pCex->iFrame; f++ ) {
        po_values.push_back(vector<char>());
        Gia_ManForEachPi( pGia, pObj, k )
            pObj->fMark0 = Abc_InfoHasBit(pCex->pData, iBit++);
        Gia_ManForEachAnd( pGia, pObj, k )
            pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj)) &
                           (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj));
        Gia_ManForEachCo( pGia, pObj, k ) {
            pObj->fMark0 = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj);
            if (Gia_ObjIsPo(pGia, pObj)) {
                if(isPIAndDontCare(pGia, Gia_ObjFanin0(pObj), pCare, f)) {
                    po_values.back().push_back('x');
                } else {
                    po_values.back().push_back(pObj->fMark0 + '0');
                }
            }
        }
        Gia_ManForEachRiRo( pGia, pObjRi, pObjRo, k )
            pObjRo->fMark0 = pObjRi->fMark0;
    }
    assert( iBit == pCex->nBits );
    Abc_CexFreeP( &pCare );
}

Wlc_Ntk_t * AddAuxPOsForOperators(Wlc_Ntk_t * pNtk, std::vector<int>& vec_ids, int max_input_bw, int max_output_bw)
{
    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);

    Wlc_Obj_t * pObj;
    int iFin0, iFin1;
    int iNew, iFin0New, iFin1New;
    Vec_Int_t * vFanins = Vec_IntAlloc( 1 );

    for(unsigned i = 0; i < vec_ids.size(); i++) {
        pObj = Wlc_NtkObj(p, vec_ids[i]);
        iFin0 = Wlc_ObjFaninId0(pObj);
        iFin1 = Wlc_ObjFaninId1(pObj);

        Vec_IntFill(vFanins, 1, iFin0);
        iFin0New = create_buffer(p, Wlc_NtkObj(p, iFin0), vFanins, max_input_bw);
        Vec_IntFill(vFanins, 1, iFin1);
        iFin1New = create_buffer(p, Wlc_NtkObj(p, iFin1), vFanins, max_input_bw);
        Vec_IntFill(vFanins, 1, vec_ids[i]);
        iNew = create_buffer(p, Wlc_NtkObj(p, vec_ids[i]), vFanins, max_output_bw);

        Wlc_NtkObj(p, iFin0New)->fIsPo = 1;
        Wlc_NtkObj(p, iFin1New)->fIsPo = 1;
        Wlc_NtkObj(p, iNew)->fIsPo = 1;

        Vec_IntInsert(&p->vCos, Wlc_NtkPoNum(p), iFin0New);
        Vec_IntPush(&p->vPos, iFin0New);
        Vec_IntInsert(&p->vCos, Wlc_NtkPoNum(p), iFin1New);
        Vec_IntPush(&p->vPos, iFin1New);
        Vec_IntInsert(&p->vCos, Wlc_NtkPoNum(p), iNew);
        Vec_IntPush(&p->vPos, iNew);
    }

    Wlc_Ntk_t * pNew = DupNtkAndUpdateIDs(p, vec_ids);

    Vec_IntFree(vFanins);
    Wlc_NtkFree(p);
    return pNew;
}

Wlc_Ntk_t * RemoveAuxPOs(Wlc_Ntk_t * p, int iStart)
{
    int iObj;
    while (Wlc_NtkPoNum(p) > iStart) {
        iObj = Vec_IntEntry(&p->vPos, iStart);
        Wlc_NtkObj(p, iObj)->fIsPo = 0;
        Vec_IntDrop(&p->vPos, iStart);
        Vec_IntDrop(&p->vCos, iStart);
    }

    Wlc_Ntk_t * pNew = Wlc_NtkDupDfsSimple(p);
    return pNew;
}

Wlc_Ntk_t * MakeUnderApprox(Wlc_Ntk_t * pNtk, int num_bits) {
    int nOrigObjNum = Wlc_NtkObjNumMax(pNtk);
    Wlc_NtkCleanCopy( pNtk );

    Wlc_Obj_t * pObj;
    int i;

    Wlc_NtkForEachPi(pNtk, pObj, i) {
        pObj->Mark = 1;
    }

    auto create_under_pi = [&pNtk, &num_bits] (Wlc_Obj_t * pObj) {
        int i = Wlc_ObjId(pNtk, pObj);
        int range = Wlc_ObjRange(pObj);
        if (range <= num_bits)
            return i;

        Vec_Int_t * vFanins = Vec_IntAlloc( 1 );
        int isSigned = Wlc_ObjIsSigned(pObj);

        Vec_IntFill(vFanins, 1, i);
        int iShrink = Wlc_ObjCreate(pNtk, WLC_OBJ_BUF, isSigned, num_bits - 1, 0, vFanins);
        Vec_IntFill(vFanins, 1, iShrink);
        int iObj = Wlc_ObjCreate(pNtk, WLC_OBJ_BUF, isSigned, range - 1, 0, vFanins);

        Vec_IntFree(vFanins);

        return iObj;
    };

    ModifyMarkedNodes(pNtk, nOrigObjNum, create_under_pi);

    Wlc_Ntk_t * pNew = Wlc_NtkDupDfsSimple(pNtk);

    return pNew;
}

Wlc_Ntk_t * IntroduceBitwiseChoices( Wlc_Ntk_t * pNtk, vector<int>& vec_ids, const vector<Greyness>& vec_greys, vector<IntPair>& vec_choice2idx )
{
    Wlc_Ntk_t * p = DupNtkAndUpdateIDs(pNtk, vec_ids);
    int nOrigObjNum = Wlc_NtkObjNumMax(p);
    Wlc_NtkCleanCopy( p );

    Wlc_Obj_t * pObj;
    int iObj;

    map<int, int> map_node2pi;
    map<int, int> map_node2idx;
    map<int, const Greyness*> map_node2grey;

    for (size_t i = 0; i < vec_greys.size(); ++i) {
        const Greyness& grey = vec_greys[i];
        if(grey.IsWhite()) continue;

        iObj = vec_ids[i];
        pObj = Wlc_NtkObj(p, iObj);
        pObj->Mark = 1;
        map_node2pi[iObj] = Wlc_ObjAlloc( p, WLC_OBJ_PI, Wlc_ObjIsSigned(pObj), Wlc_ObjRange(pObj) - 1, 0 );
        map_node2grey[iObj] = &grey;
        map_node2idx[iObj] = int(i);
    }

    auto create_output_with_bitwise_mux = [&vec_choice2idx, &map_node2grey, &map_node2idx, &map_node2pi, &p](Wlc_Obj_t * pObj) {
        Vec_Int_t * vFanins = Vec_IntAlloc( 100 );
        Vec_Int_t * vFanins2 = Vec_IntAlloc( 3 );

        int i = Wlc_ObjId(p, pObj);
        bool isSigned = bool(Wlc_ObjIsSigned(pObj));
        int range = Wlc_ObjRange(pObj);
        int offset = pObj->Beg;
        
        Vec_IntClear(vFanins);
        for (int pos = 0; pos < range; ++pos) {
            Vec_IntClear(vFanins2);
            Vec_IntPush(vFanins2, i);
            Vec_IntPushTwo(vFanins2, pos + offset, pos + offset);
            int iWhiteBit = Wlc_ObjCreate(p, WLC_OBJ_BIT_SELECT, 0, 0, 0, vFanins2);

            if(map_node2grey[i]->Get(pos)) { // add choice/sel
                Vec_IntClear(vFanins2);
                Vec_IntPush(vFanins2, map_node2pi[i]);
                Vec_IntPushTwo(vFanins2, pos, pos);
                int iBlackBit = Wlc_ObjCreate(p, WLC_OBJ_BIT_SELECT, 0, 0, 0, vFanins2);

                int iSel = Wlc_ObjAlloc( p, WLC_OBJ_PI, 0, 0, 0);
                Vec_IntClear(vFanins2);
                Vec_IntPush(vFanins2, iSel);
                Vec_IntPush(vFanins2, iBlackBit);
                Vec_IntPush(vFanins2, iWhiteBit);
                Vec_IntPush(vFanins, Wlc_ObjCreate(p, WLC_OBJ_MUX, 0, 0, 0, vFanins2));

                vec_choice2idx.push_back(IntPair(map_node2idx[i], pos));
            } else {
                Vec_IntPush(vFanins, iWhiteBit);
            }
        }
        Vec_IntReverseOrder(vFanins);

        int iObj = Wlc_ObjCreate(p, WLC_OBJ_BIT_CONCAT, isSigned, range - 1, 0, vFanins);

        Vec_IntFree(vFanins);
        Vec_IntFree(vFanins2);

        return iObj;
    };

    ModifyMarkedNodes(p, nOrigObjNum, create_output_with_bitwise_mux);

    Wlc_Ntk_t * pNew = Wlc_NtkDupDfsSimple(p);
    Wlc_NtkFree( p );

    return pNew;
}

Wlc_Ntk_t * AddConstFlops( Wlc_Ntk_t * pNtk, const set<unsigned>& types )
{
    Wlc_Ntk_t * p = Wlc_NtkDupDfsSimple(pNtk);
    Wlc_NtkCleanCopy( p );
    int nOrigObjNum = Wlc_NtkObjNumMax(p);
    if ( !Wlc_NtkHasNameId(p) && Wlc_NtkHasNameId(pNtk) )
        Wlc_NtkTransferNames( p, pNtk );

    Wlc_Obj_t * pObj;
    int i, iObjConst0;

    {
        Vec_Int_t * vFanins = Vec_IntAlloc( 2 );

        Vec_IntFill(vFanins, 1, 0);
        iObjConst0 = Wlc_ObjCreate(p, WLC_OBJ_CONST, 0, 0, 0, vFanins);
        Wlc_NtkObj(p, iObjConst0)->fIsFi = 1;
        nOrigObjNum++;

        Vec_IntFree( vFanins );
    }

    Wlc_NtkForEachObj( p, pObj, i ) {
        if (types.count(pObj->Type)) {
            pObj->Mark = 1;
        }
    }

    auto create_ff_and_mux = [p, iObjConst0](Wlc_Obj_t  * pObj) {
        Vec_Int_t * vFanins = Vec_IntAlloc( 3 );

        int i = Wlc_ObjId(p, pObj);
        int isSigned = Wlc_ObjIsSigned(pObj);
        int range = Wlc_ObjRange(pObj);
        
        int iPPI = Wlc_ObjAlloc( p, WLC_OBJ_PI, isSigned, range - 1, 0 );
        int iObjFo = Wlc_ObjCreate( p, WLC_OBJ_FO, 0, 0, 0, vFanins );

        Vec_IntPush(&p->vCos, iObjConst0);

        if (p->pInits == NULL) {
            char * pStr = ABC_ALLOC(char, 2);
            pStr[0] = '0';
            pStr[1] = '\0';
            p->pInits = pStr;
        } else {
            char * pStr = strcpy(ABC_ALLOC(char, strlen(p->pInits) + 2), p->pInits);
            pStr[strlen(p->pInits)] = '0';
            pStr[strlen(p->pInits) + 1] = '\0';
            ABC_FREE(p->pInits);
            p->pInits = pStr;
        }
        if ( p->vInits == NULL ) {
            p->vInits = Vec_IntAlloc( 100 );
        }
        // push vInits
        Vec_IntPush( p->vInits, -1 );

        int iSelID = iObjFo;
        Vec_IntClear(vFanins);
        Vec_IntPush(vFanins, iSelID);
        Vec_IntPush(vFanins, i);
        Vec_IntPush(vFanins, iPPI);
        int iObj = Wlc_ObjCreate(p, WLC_OBJ_MUX, isSigned, range - 1, 0, vFanins);

        Vec_IntFree( vFanins );

        return iObj;
    };
 
    ModifyMarkedNodes(p, nOrigObjNum, create_ff_and_mux);

    Wlc_Ntk_t * pNew = Wlc_NtkDupDfsSimple( p );
    if ( !Wlc_NtkHasNameId(pNew) && Wlc_NtkHasNameId(p) )
        Wlc_NtkTransferNames( pNew, p );

    Wlc_NtkFree( p );

    return pNew;
}

Wlc_Ntk_t * IntroduceChoices( Wlc_Ntk_t * pNtk, Vec_Int_t * vNodes )
{
    if ( vNodes == NULL ) return NULL;

    Wlc_Ntk_t * pNew;
    Wlc_Obj_t * pObj;
    int i, iObj;
    Vec_Int_t * vFanins = Vec_IntAlloc( 3 );
    map<int, int> map_node2pi;

    Wlc_Ntk_t * p = Wlc_NtkDupDfsSimple(pNtk);
    int nOrigObjNum = Wlc_NtkObjNumMax(p);
    Wlc_NtkForEachObjVec( vNodes, pNtk, pObj, i ) {
        Vec_IntWriteEntry(vNodes, i, Wlc_ObjCopy(pNtk, Wlc_ObjId(pNtk, pObj)));
    }

    // Vec_IntPrint(vNodes);
    Wlc_NtkCleanCopy( p );

    // mark nodes
    Wlc_NtkForEachObjVec( vNodes, p, pObj, i ) {
        iObj = Wlc_ObjId(p, pObj);
        pObj->Mark = 1;
        // add fresh PI with the same number of bits
        map_node2pi[iObj] = Wlc_ObjAlloc( p, WLC_OBJ_PI, Wlc_ObjIsSigned(pObj), Wlc_ObjRange(pObj) - 1, 0 );
    }

    auto create_output_mux = [&p, &map_node2pi](Wlc_Obj_t * pObj) {
        Vec_Int_t * vFanins = Vec_IntAlloc( 3 );

        int i = Wlc_ObjId(p, pObj);
        int isSigned = Wlc_ObjIsSigned(pObj);
        int range = Wlc_ObjRange(pObj);
        int iSelID = Wlc_ObjAlloc( p, WLC_OBJ_PI, 0, 0, 0);
        Vec_IntClear(vFanins);
        Vec_IntPush(vFanins, iSelID);
        Vec_IntPush(vFanins, map_node2pi.at(i));
        Vec_IntPush(vFanins, i);
        int iObj = Wlc_ObjCreate(p, WLC_OBJ_MUX, isSigned, range - 1, 0, vFanins);

        Vec_IntFree(vFanins);

        return iObj;
    };

    ModifyMarkedNodes(p, nOrigObjNum, create_output_mux);

    // DumpWlcNtk(p);
    pNew = Wlc_NtkDupDfsSimple( p );

    Vec_IntFree(vFanins);
    Wlc_NtkFree( p );

    return pNew;
}

Wlc_Ntk_t * AbstractNodes( Wlc_Ntk_t * pNtk, Vec_Int_t * vNodesInit )
{
    Vec_Int_t * vNodes = vNodesInit;
    Wlc_Ntk_t * pNew;
    Wlc_Obj_t * pObj;
    int i, iObj;
    map<int, int> map_node2pi;

    if ( vNodes == NULL )
        return NULL;

    Wlc_Ntk_t * p = NULL;
    p = Wlc_NtkDupDfsSimple(pNtk);
    Wlc_NtkForEachObjVec( vNodes, pNtk, pObj, i ) {
        Vec_IntWriteEntry(vNodes, i, Wlc_ObjCopy(pNtk, Wlc_ObjId(pNtk, pObj)));
    }

    int nOrigObjNum = Wlc_NtkObjNumMax( p );
    // mark nodes
    Wlc_NtkForEachObjVec( vNodes, p, pObj, i ) {
        iObj = Wlc_ObjId(p, pObj);
        pObj->Mark = 1;
        // add fresh PI with the same number of bits
        map_node2pi[iObj] = Wlc_ObjAlloc( p, WLC_OBJ_PI, Wlc_ObjIsSigned(pObj), Wlc_ObjRange(pObj) - 1, 0 );
    }

    auto create_black_output = [&p, &map_node2pi](Wlc_Obj_t * pObj) {
        return map_node2pi[Wlc_ObjId(p, pObj)];
    };

    Wlc_NtkCleanCopy( p );
    ModifyMarkedNodes(p, nOrigObjNum, create_black_output);

    if ( vNodes != vNodesInit )
        Vec_IntFree( vNodes );
    // reconstruct topological order
    pNew = Wlc_NtkDupDfsSimple( p );
    //Wlc_NtkTransferNames( pNew, p );
    Wlc_NtkFree( p );
    return pNew;
}

Wlc_Ntk_t * MakeUnderApprox2(Wlc_Ntk_t * pNtk, const set<unsigned>& types, int num_bits) {
    Wlc_Obj_t *pObj;
    int i, iFanin0, iFanin1;
    int iNew, iFanin0New, iFanin1New;

    Vec_Int_t *vFanins = Vec_IntAlloc(2);
    Wlc_NtkForEachObj(pNtk, pObj, i) {
        if (types.count(pObj->Type)) {
            // Already normalized
            if (pObj->Mark) continue;

            iFanin0 = Wlc_ObjFaninId0(pObj);
            iFanin1 = Wlc_ObjFaninId1(pObj);

            assert(Wlc_ObjIsSigned(Wlc_NtkObj(pNtk, iFanin0)));
            assert(Wlc_ObjIsSigned(Wlc_NtkObj(pNtk, iFanin1)));
            assert(Wlc_ObjIsSigned(pObj));

            int range0 = Wlc_ObjRange(Wlc_NtkObj(pNtk, iFanin0));
            int range1 = Wlc_ObjRange(Wlc_NtkObj(pNtk, iFanin1));

            unsigned op_type = pObj->Type;

            Vec_IntFill(vFanins, 1, iFanin0);
            iFanin0New = Wlc_ObjCreate(pNtk, WLC_OBJ_BUF, 1, (range0 > num_bits ? num_bits : range0) - 1, 0, vFanins);

            Vec_IntFill(vFanins, 1, iFanin1);
            iFanin1New = Wlc_ObjCreate(pNtk, WLC_OBJ_BUF, 1, (range1 > num_bits ? num_bits : range1) - 1, 0, vFanins);

            int lossless_range =
                    Wlc_ObjRange(Wlc_NtkObj(pNtk, iFanin0New)) + Wlc_ObjRange(Wlc_NtkObj(pNtk, iFanin1New));

            Vec_IntFillTwo(vFanins, 2, iFanin0New, iFanin1New);
            iNew = Wlc_ObjCreate(pNtk, op_type, 1, lossless_range - 1, 0, vFanins);

            Wlc_NtkObj(pNtk, iNew)->Mark = 1;

            Wlc_NtkObj(pNtk, i)->Type = WLC_OBJ_BUF;
            Wlc_NtkObj(pNtk, i)->nFanins = 1;
            Wlc_ObjFanins(Wlc_NtkObj(pNtk, i))[0] = iNew;
        }
    }

    Wlc_Ntk_t * p = Wlc_NtkDupDfsSimple(pNtk);
    Vec_Int_t * vConstrs = Vec_IntAlloc(100);

    Wlc_NtkForEachObj(p, pObj, i) {
        if (types.count(pObj->Type)) {
            iFanin0 = Wlc_ObjFaninId0(pObj);
            iFanin1 = Wlc_ObjFaninId1(pObj);

            int iFanin0Fanin0 = Wlc_ObjFaninId0(Wlc_NtkObj(p, iFanin0));
            int iFanin1Fanin0 = Wlc_ObjFaninId0(Wlc_NtkObj(p, iFanin1));

            Vec_IntFillTwo(vFanins, 2, iFanin0, iFanin0Fanin0);
            Vec_IntPush(vConstrs, Wlc_ObjCreate(p, WLC_OBJ_COMP_EQU, 0, 0, 0, vFanins));

            Vec_IntFillTwo(vFanins, 2, iFanin1, iFanin1Fanin0);
            Vec_IntPush(vConstrs, Wlc_ObjCreate(p, WLC_OBJ_COMP_EQU, 0, 0, 0, vFanins));
        }
    }

    if (Wlc_NtkFfNum(p) == 0)
        FoldCombConstraints(p, vConstrs);
    else
        FoldSeqConstraints(p, vConstrs);

    Wlc_Ntk_t * pNew = Wlc_NtkDupDfsSimple(p);

    Wlc_NtkFree(p);
    Vec_IntFree(vFanins);
    Vec_IntFree(vConstrs);

    return pNew;
}

Wlc_Ntk_t * NormalizeDataTypes(Wlc_Ntk_t * p, const set<unsigned>& types, bool fUnify)
{
    Wlc_Ntk_t *pNtk, *pNew;

    pNtk = Wlc_NtkDupDfsSimple(p);
    if ( !Wlc_NtkHasNameId(pNtk) && Wlc_NtkHasNameId(p) )
        Wlc_NtkTransferNames( pNtk, p );

    Wlc_Obj_t *pObj;
    int i, iFanin0, iFanin1;
    int iNew, iFanin0New, iFanin1New;
    int lossless_range;
    Vec_Int_t * vFanins = Vec_IntAlloc( 2 );
    vector<int> signs;

    Wlc_NtkForEachObj( pNtk, pObj, i ) {
        if ( types.count(pObj->Type) ) {
            // Already normalized
            if (pObj->Mark) continue;

            iFanin0 = Wlc_ObjFaninId0(pObj);
            iFanin1 = Wlc_ObjFaninId1(pObj);

            signs.clear();
            signs.push_back(Wlc_ObjIsSigned(Wlc_NtkObj(pNtk, iFanin0)));
            signs.push_back(Wlc_ObjIsSigned(Wlc_NtkObj(pNtk, iFanin1)));
            signs.push_back(Wlc_ObjIsSigned(pObj));

            int op_is_signed = signs[0] && signs[1];
            unsigned op_type = pObj->Type;

            Vec_IntFill(vFanins, 1, iFanin0);
            if (op_is_signed)
                iFanin0New = iFanin0;
            else if (fUnify)
                iFanin0New = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_ZEROPAD, 1, Wlc_NtkObj(pNtk, iFanin0)->End + 1, Wlc_NtkObj(pNtk, iFanin0)->Beg, vFanins);
            else
                iFanin0New = Wlc_ObjCreate(pNtk, WLC_OBJ_BUF, op_is_signed, Wlc_NtkObj(pNtk, iFanin0)->End, Wlc_NtkObj(pNtk, iFanin0)->Beg, vFanins);

            Vec_IntFill(vFanins, 1, iFanin1);
            if (op_is_signed)
                iFanin1New = iFanin1;
            else if (fUnify)
                iFanin1New = Wlc_ObjCreate(pNtk, WLC_OBJ_BIT_ZEROPAD, 1, Wlc_NtkObj(pNtk, iFanin1)->End + 1, Wlc_NtkObj(pNtk, iFanin1)->Beg, vFanins);
            else
                iFanin1New = Wlc_ObjCreate(pNtk, WLC_OBJ_BUF, op_is_signed, Wlc_NtkObj(pNtk, iFanin1)->End, Wlc_NtkObj(pNtk, iFanin1)->Beg, vFanins);

            lossless_range = Wlc_ObjRange(Wlc_NtkObj(pNtk, iFanin0New)) + Wlc_ObjRange(Wlc_NtkObj(pNtk, iFanin1New));

            Vec_IntFillTwo(vFanins, 2, iFanin0New, iFanin1New);
            if (fUnify)
                iNew = Wlc_ObjCreate(pNtk, op_type, 1, lossless_range - 1, 0, vFanins);
            else
                iNew = Wlc_ObjCreate(pNtk, op_type, op_is_signed, lossless_range - 1, 0, vFanins);

            Wlc_NtkObj(pNtk, iNew)->Mark = 1;

            Wlc_NtkObj(pNtk, i)->Type = WLC_OBJ_BUF;
            Wlc_NtkObj(pNtk, i)->nFanins = 1;
            Wlc_ObjFanins(Wlc_NtkObj(pNtk, i))[0] = iNew;
        }
    }
    Vec_IntFree(vFanins);

    pNew = Wlc_NtkDupDfsSimple(pNtk);
    if ( !Wlc_NtkHasNameId(pNew) && Wlc_NtkHasNameId(pNtk) )
        Wlc_NtkTransferNames( pNew, pNtk );
    Wlc_NtkFree(pNtk);

    return pNew;
}

Wlc_Ntk_t * CreateMiter(Wlc_Ntk_t *pNtk, bool fXor)
{
    assert(Wlc_NtkPoNum(pNtk) == 2);

    Wlc_Ntk_t *pNew = Wlc_NtkDupDfsSimple(pNtk);
    if ( !Wlc_NtkHasNameId(pNew) && Wlc_NtkHasNameId(pNtk) )
        Wlc_NtkTransferNames( pNew, pNtk );

    Wlc_Obj_t *pOldPo0 = Wlc_NtkPo(pNew, 0);
    Wlc_Obj_t *pOldPo1 = Wlc_NtkPo(pNew, 1);
    //assert(Wlc_ObjRange(pOldPo0) == Wlc_ObjRange(pOldPo1));

    int iOldPo0 = Wlc_ObjId(pNew, pOldPo0);
    int iOldPo1 = Wlc_ObjId(pNew, pOldPo1);

    Vec_Int_t *vFanins = Vec_IntAlloc( 2 );
    Vec_IntFillTwo( vFanins, 2, iOldPo0, iOldPo1 );
    int iNewPo;
    if (!fXor) iNewPo = Wlc_ObjCreate( pNew, WLC_OBJ_COMP_NOTEQU, 0, 0, 0, vFanins );
    else       iNewPo = Wlc_ObjCreate( pNew, WLC_OBJ_BIT_XOR, 0, Wlc_ObjRange(pOldPo0)-1, 0, vFanins );
    Vec_IntFree( vFanins );

    Vec_IntWriteEntry( &pNew->vPos, 0, iNewPo );
    Vec_IntDrop( &pNew->vPos, 1 );
    Vec_IntWriteEntry( &pNew->vCos, 0, iNewPo );
    Vec_IntDrop( &pNew->vCos, 1 );

    Wlc_NtkObj(pNew, iNewPo)->fIsPo = 1;
    Wlc_NtkObj(pNew, iOldPo0)->fIsPo = 0;
    Wlc_NtkObj(pNew, iOldPo1)->fIsPo = 0;

    Wlc_Ntk_t *pNewNew = Wlc_NtkDupDfsSimple(pNew);
    if ( !Wlc_NtkHasNameId(pNewNew) && Wlc_NtkHasNameId(pNew) )
        Wlc_NtkTransferNames( pNewNew, pNew );
    Wlc_NtkFree(pNew);
    return pNewNew;
}

void PrintWordCEX(Wlc_Ntk_t * pNtk, Abc_Cex_t * pCex, const vector<string>* names)
{
    // PIs at each frame
    for (int f = 0; f <= pCex->iFrame; ++f) {
        int pos = 0;
        for (int i = 0; i < Wlc_NtkPiNum(pNtk); ++i) {
            cout << "CEX:";
            for (int k = 0; k < Wlc_ObjRange(Wlc_NtkPi(pNtk, i)); ++k ) {
                cout << Abc_InfoHasBit(pCex->pData, pCex->nRegs+pCex->nPis*f + (Wlc_ObjRange(Wlc_NtkPi(pNtk, i))-k-1)+pos);
            }
            pos += Wlc_ObjRange(Wlc_NtkPi(pNtk, i));
            cout << ":" ;
            if (names)
                cout << (*names)[Wlc_ObjId(pNtk, Wlc_NtkPi(pNtk, i))];
            else
                cout << Wlc_ObjName(pNtk, Wlc_ObjId(pNtk, Wlc_NtkPi(pNtk, i)));
            cout << "@" << f;
            cout << endl;
        }
    }
}

bool HasOperator(const Wlc_Ntk_t * p, const set<unsigned>& types)
{
    bool ret = false;
    for (set<unsigned>::const_iterator it = types.begin(); it != types.end(); it++) {
        if (p->nObjs[*it] > 0) {
            ret = true;
            break;
        }
    }
    return ret;
}

void ComputeMaxBW(Wlc_Ntk_t * p, const vector<int>& vec_ids, int& max_input_bw, int& max_output_bw ) {
    max_input_bw = max_output_bw = 0;
    for (unsigned i = 0; i < vec_ids.size(); i++) {
        int op_id = vec_ids[i];
        Wlc_Obj_t * pObj = Wlc_NtkObj(p, op_id);
        int range = Wlc_ObjRange(pObj);
        int range0 = Wlc_ObjRange(Wlc_ObjFanin0(p, pObj));
        int range1 = Wlc_ObjRange(Wlc_ObjFanin1(p, pObj));
        if (range0 > max_input_bw)
            max_input_bw = range0;
        if (range1 > max_input_bw)
            max_input_bw = range1;
        if (range > max_output_bw)
            max_output_bw = range;
    }
}

// Solves a bit-blasted abstraction using PDR2.
// The backend is fixed. The caller owns the returned trace, whose inputs and initial registers
// follow the original abstraction.
// Replaces the caller's counterexample and honors cancellation.
// See also: BitBlast
int SolveAbstractModel( Wlc_Ntk_t * pNtk, Abc_Cex_t ** ppCex, const string * pFileName,
    bool fSyn, int nTimeOut, int (*pFuncStop)(int), int RunId )
{
    Gia_Man_t * pGia, * pSolve;
    Aig_Man_t * pAig;
    Pdr2_Par_t Pars;
    int Result;
    if ( !pNtk || !ppCex ) return -1;
    Abc_CexFreeP( ppCex );
    if ( pFuncStop && pFuncStop(RunId) ) return -1;
    pGia = BitBlast( pNtk );
    if ( !pGia ) return -1;
    pSolve = fSyn ? Gia_ManSeqStructSweep(pGia, 1, 1, 0) : pGia;
    if ( !pSolve || (pFuncStop && pFuncStop(RunId)) )
    {
        if ( pSolve != pGia ) Gia_ManStopP( &pSolve );
        Gia_ManStop( pGia );
        return -1;
    }
    if ( pFileName && !pFileName->empty() )
    {
        string File = *pFileName + ".aig";
        Gia_AigerWriteSimple( pSolve, &File[0] );
    }
    pAig = Gia_ManToAig( pSolve, 0 );
    if ( pAig->pName == NULL )
        pAig->pName = Abc_UtilStrsav( pSolve->pName ? pSolve->pName : pSolve->pSpec );
    if ( pAig->pSpec == NULL )
        pAig->pSpec = Abc_UtilStrsav( pSolve->pName ? pSolve->pName : pSolve->pSpec );
    Pdr2_ManSetDefaultParams( &Pars );
    Pars.nTimeOut = Abc_MaxInt( 0, nTimeOut );
    Pars.fVerifyComplete = 1;
    Pars.RunId = RunId;
    Pars.pFuncStop = pFuncStop;
    Result = Pdr2_ManSolve( pAig, &Pars );
    if ( pFuncStop && pFuncStop(RunId) ) Result = -1;
    if ( Result == 0 )
    {
        if ( pAig->pSeqModel && Saig_ManVerifyCex(pAig, pAig->pSeqModel) )
            *ppCex = Abc_CexDup( pAig->pSeqModel, Gia_ManRegNum(pGia) );
        if ( !*ppCex || !Gia_ManVerifyCex(pGia, *ppCex, 0) )
        {
            Abc_Print( 1, "Warning: UFAR rejected a counterexample from PDR2.\n" );
            Abc_CexFreeP( ppCex );
            Result = -1;
        }
    }
    Aig_ManStop( pAig );
    if ( pSolve != pGia ) Gia_ManStop( pSolve );
    Gia_ManStop( pGia );
    return Result;
}


Gia_Man_t * GetInvMiter(Wlc_Ntk_t * pNtk, char * nameInv) {
    auto check_pla = [](char * name) {
        string line;
        ifstream ifs (name, std::ifstream::in);
        if(ifs) {
            while(getline(ifs, line)) {
                if (line == ".p 0") {
                    return false;
                }
            }
            ifs.close();
        }
        return true;
    };

    Gia_Man_t * pMiter = NULL;
    Gia_Man_t * pGia = BitBlast(pNtk);
    printf("Gia stat: pi = %d, ff = %d, and = %d, po = %d\n", Gia_ManPiNum(pGia), Gia_ManRegNum(pGia), Gia_ManAndNum(pGia), Gia_ManPoNum(pGia));

    if (!check_pla(nameInv)) {
        LOG(2) << "Empty invariant. Changed to combinational SAT.";
        pMiter = Gia_ManDupInvMiter(pGia, NULL);
    } else {
        Abc_Ntk_t *pAbcNtk = Io_Read(nameInv, Io_ReadFileType(nameInv), 1, 0);
        Abc_Ntk_t *pStrash = Abc_NtkStrash(pAbcNtk, 0, 1, 0);
        Aig_Man_t *pAig = Abc_NtkToDar(pStrash, 0, 0);
        Gia_Man_t *pInv = Gia_ManFromAig(pAig);
        printf("Inv stat: pi = %d, ff = %d, and = %d, po = %d\n", Gia_ManPiNum(pInv), Gia_ManRegNum(pInv),
               Gia_ManAndNum(pInv), Gia_ManPoNum(pInv));
        pMiter = Gia_ManDupInvMiter(pGia, pInv);

        Abc_NtkDelete(pAbcNtk);
        Abc_NtkDelete(pStrash);
        Aig_ManStop(pAig);
        Gia_ManStop(pInv);
    }

    Gia_ManStop(pGia);

    return pMiter;
}

void TestInvariant(string& nameNtk, string& nameInv) {
    Gia_Man_t * pGia = Gia_AigerRead( &nameNtk[0u], 0, 0, 0 );
    printf("Gia stat: pi = %d, ff = %d, and = %d, po = %d\n", Gia_ManPiNum(pGia), Gia_ManRegNum(pGia), Gia_ManAndNum(pGia), Gia_ManPoNum(pGia));

    Abc_Ntk_t * pAbcNtk = Io_Read( &nameInv[0u], Io_ReadFileType(&nameInv[0u]), 1, 0 );
    Abc_Ntk_t * pStrash = Abc_NtkStrash( pAbcNtk, 0, 1, 0 );
    Aig_Man_t * pAig = Abc_NtkToDar( pStrash, 0, 0 );
    Gia_Man_t * pInv = Gia_ManFromAig( pAig );
    printf("Inv stat: pi = %d, ff = %d, and = %d, po = %d\n", Gia_ManPiNum(pInv), Gia_ManRegNum(pInv), Gia_ManAndNum(pInv), Gia_ManPoNum(pInv));

    Gia_Man_t * pMiter = Gia_ManDupInvMiter(pGia, pInv);
    Gia_AigerWrite(pMiter, "miter.aig", 0, 0, 0);


    // TODO : flip Node1, Abc_LitNot(Node2)
    // Gia_Man_t * Gia_ManDupInvMiter( Gia_Man_t * p, Gia_Man_t * pInv )

    // TODO : flip fUseSupp
    // void Pdr_ManDumpClauses( Pdr_Man_t * p, char * pFileName, int fProved )

    Abc_NtkDelete(pAbcNtk);
    Abc_NtkDelete(pStrash);
    Aig_ManStop(pAig);
    Gia_ManStop(pInv);
    Gia_ManStop(pGia);
    Gia_ManStop(pMiter);
}


}

ABC_NAMESPACE_IMPL_END
