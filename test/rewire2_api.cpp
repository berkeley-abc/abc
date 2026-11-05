/**CFile****************************************************************

  FileName    [rewire2_api.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring tests.]

  Synopsis    [Standalone regression of rewiring interfaces and rejected inputs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 7, 2026.]

  Revision    []

***********************************************************************/

// Build as a standalone executable linked with libabc, not as part of abc.
// For example, from the repository root with GCC or Clang:
// g++ -std=c++17 -DLIN64 -Isrc -fno-access-control test/rewire2_api.cpp
//     libabc.a -lreadline -lpthread -ldl -lm -o rewire2_test
// Private-method checks in the API/pair tests need -fno-access-control.
// With a namespace library, also pass its matching -DABC_NAMESPACE=<name>.
// Keep checks active even when the library is built with NDEBUG.
#ifdef NDEBUG
#undef NDEBUG
#endif

#include "base/main/main.h"
#include "opt/rar/rewire2Rar.h"
#include "opt/rar/rewire2Miaig.h"
#include <vector>
#include <limits>
ABC_NAMESPACE_USING_NAMESPACE

static Mini_Aig_t * RunMini( Mini_Aig_t * p, Gia_Man_t * care = NULL, float ratio = 0 )
{
    return MiniAig_ManRewire2(p, care, 4, 8, ratio, 128, 4, -1, 8, 0, 0, 0, 0, 1, 0, 1, 1, 0);
}
static Gia_Man_t * RunGia( Gia_Man_t * p, Gia_Man_t * care = NULL, float ratio = 0 )
{
    return Gia_ManRewire2(p, care, 4, 8, ratio, 128, 4, -1, 8, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0);
}
static std::vector<int> Evaluate( Mini_Aig_t * p, int pattern )
{
    std::vector<int> values(Mini_AigNodeNum(p), 0), outputs;
    int index = 0;
    for ( int i = 1; i < Mini_AigNodeNum(p); i++ )
    {
        if ( Mini_AigNodeIsPi(p, i) ) values[i] = (pattern >> index++) & 1;
        else
        {
            int a = Mini_AigNodeFanin0(p, i);
            int value = values[a >> 1] ^ (a & 1);
            if ( Mini_AigNodeIsPo(p, i) ) outputs.push_back(value);
            else
            {
                int b = Mini_AigNodeFanin1(p, i);
                values[i] = value & (values[b >> 1] ^ (b & 1));
            }
        }
    }
    return outputs;
}
int main()
{
    Abc_Start();
    Mini_Aig_t * p = Mini_AigStart();
    int a = Mini_AigCreatePi(p), q = Mini_AigCreatePi(p);
    int d = Mini_AigAnd(p, a, q);
    Mini_AigCreatePo(p, q ^ 1);
    Mini_AigCreatePo(p, d);
    Mini_AigSetRegNum(p, 1);
    Mini_Aig_t * out = RunMini(p);
    assert(out && Mini_AigRegNum(out) == 1);
    assert(Mini_AigPiNum(out) == 2 && Mini_AigPoNum(out) == 2);
    for ( int i = 0; i < 4; i++ ) assert(Evaluate(p, i) == Evaluate(out, i));
    Mini_AigStop(out);
    assert(!RunMini(p, NULL, 1.0e30f));
    assert(!RunMini(p, NULL, std::numeric_limits<float>::quiet_NaN()));
    Gia_Man_t * care = Gia_ManStart(16);
    Gia_ManAppendCo(care, Gia_ManAppendCi(care));
    assert(!RunMini(p, care));
    Gia_ManStop(care);
    Mini_AigStop(p);

    p = Mini_AigStart();
    for ( int i = 0; i < 25; i++ ) Mini_AigCreatePi(p);
    Mini_AigCreatePo(p, 2);
    assert(!RunMini(p));
    Mini_AigStop(p);
    Gia_Man_t * g = Gia_ManStart(64);
    for ( int i = 0; i < 25; i++ ) Gia_ManAppendCi(g);
    Gia_ManAppendCo(g, 2);
    assert(!RunGia(g));
    Gia_ManStop(g);
    Abc_Ntk_t * n = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    Abc_Obj_t * first = NULL;
    for ( int i = 0; i < 25; i++ ) { Abc_Obj_t * pi = Abc_NtkCreatePi(n); if (!i) first = pi; }
    Abc_ObjAddFanin(Abc_NtkCreatePo(n), first);
    assert(!Abc_ManRewire2(n, NULL, 4, 8, 0, 128, 4, -1, 8, 0, 0, 0, 0, 1, 0, 1, 1, 0));
    Abc_NtkDelete(n);
    // Internal boundary paths must return before reading absent rows or allocating huge tables.
    {
        Rewire2::Miaig empty(0, 0, 1);
        word result = 0x12345678;
        empty.truthSimNode(0, &result);
        assert(result == 0x12345678);
        assert(empty.findShared(ABC_INT_MAX) == 0);
        assert(empty.findShared(40000) == 0);
        assert(empty.nObjs() == 1);
    }
    // Compact GIA representations are not two-input ANDs, either as the target or care.
    for ( int kind = 0; kind < 3; ++kind )
    {
        Gia_Man_t * extended = Gia_ManStart(16);
        if (kind == 1) extended->pMuxes = ABC_CALLOC(unsigned, extended->nObjsAlloc);
        int a = Gia_ManAppendCi(extended), b = Gia_ManAppendCi(extended), c = Gia_ManAppendCi(extended);
        int root = kind == 0 ? Gia_ManAppendXorReal(extended, a, b) :
                   kind == 1 ? Gia_ManAppendMuxReal(extended, c, a, b) : Gia_ManAppendBuf(extended, a);
        Gia_ManAppendCo(extended, root);
        assert(!RunGia(extended));
        Gia_Man_t * plain = Gia_ManStart(16);
        a = Gia_ManAppendCi(plain); b = Gia_ManAppendCi(plain); Gia_ManAppendCi(plain);
        Gia_ManAppendCo(plain, Gia_ManAppendAnd(plain, a, b));
        assert(!RunGia(plain, extended));
        assert(!Gia_ManRewire2(plain, NULL, 4, 8, 0, 128, 0, -1, 8, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0));
        assert(!Gia_ManRewire2(plain, NULL, 4, 8, 0, 128, ABC_INT_MAX, -1, 8, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0));
        assert(!Gia_ManRewire2(plain, NULL, 4, 8, 0, 128, 4, ABC_INT_MAX, 8, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0));
        assert(!Gia_ManRewire2(plain, NULL, 4, 8, 0, 128, 4, -1, 8, 0, 1, 2, 0, 1, 1, 1, 1, 0, 0));
        Gia_ManStop(plain);
        Gia_ManStop(extended);
    }
    // Sequential choices must fail before a combinational snapshot is added.
    g = Gia_ManStart(16);
    int pi = Gia_ManAppendCi(g), ro = Gia_ManAppendCi(g);
    int product = Gia_ManAppendAnd(g, pi, ro);
    Gia_ManAppendCo(g, ro ^ 1); Gia_ManAppendCo(g, product);
    Gia_ManSetRegNum(g, 1);
    assert(!Gia_ManRewire2(g, NULL, 4, 8, 0, 128, 4, -1, 8, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0));
    assert(Gia_ManRegNum(g) == 1);
    Gia_ManStop(g);
    // No outputs means a vacuous level bound, not an invalid ratio.
    g = Gia_ManStart(16); Gia_ManAppendCi(g);
    Gia_Man_t *emptyOut = RunGia(g, NULL, 1);
    assert(emptyOut && Gia_ManCiNum(emptyOut) == 1 && Gia_ManCoNum(emptyOut) == 0);
    Gia_ManStop(emptyOut); Gia_ManStop(g);
    Abc_Stop();
    puts("PASS: extended GIA guards, zero-fanin simulation, oversized pair tables, invalid search options; public API bounds, bad care, finite level limits, sequential MiniAIG ports and exhaustive truth check");
    return 0;
}
