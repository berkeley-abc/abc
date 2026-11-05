/**CFile****************************************************************

  FileName    [rewire2_pairs.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring tests.]

  Synopsis    [Standalone regression of dense and sparse fanin-pair extraction.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 7, 2026.]

  Revision    []

***********************************************************************/

// Build as a standalone executable linked with libabc, not as part of abc.
// For example, from the repository root with GCC or Clang:
// g++ -std=c++17 -DLIN64 -Isrc -fno-access-control test/rewire2_pairs.cpp
//     libabc.a -lreadline -lpthread -ldl -lm -o rewire2_test
// Private-method checks in the API/pair tests need -fno-access-control.
// With a namespace library, also pass its matching -DABC_NAMESPACE=<name>.
// Keep checks active even when the library is built with NDEBUG.
#ifdef NDEBUG
#undef NDEBUG
#endif

#include "base/main/main.h"
#include "opt/rar/rewire2Miaig.h"
#include <random>
ABC_NAMESPACE_USING_NAMESPACE
static Rewire2::Miaig Build(int nodes, int capacity, unsigned seed) {
    Rewire2::Miaig n(6,1,capacity); std::mt19937 rng(seed);
    for(int i=0;i<nodes;i++) {
        int obj=n.appendObj();
        std::vector<int> fans;
        for(int k=0;k<2+(int)(rng()%5);k++) fans.push_back(2*(1+rng()%6)+(rng()%2));
        std::sort(fans.begin(),fans.end()); fans.erase(std::unique(fans.begin(),fans.end()),fans.end());
        for(int f:fans) n.appendFanin(obj,f);
    }
    int last=n.nObjs()-1, out=n.appendObj(); n.appendFanin(out,2*last);
    return n;
}
static Mini_Aig_t * Extract(Rewire2::Miaig &n,int limit) {
    int added=n.findShared(limit); n.nObjs()-=added;
    Rewire2::Miaig clean=n.dupDfs(); n.nObjs()+=added;
    return clean.toMiniAig();
}
int main() {
    Abc_Start();
    for(unsigned seed=1;seed<=300;seed++) {
        Rewire2::Miaig n=Build(30+(seed%100),150,seed);
        int words=(2*n.nObjsAlloc()+63)/64;
        std::vector<word> bits((size_t)words*2*n.nObjsAlloc());
        rw2_vi *a=n.findPairs(bits.data(),words), *b=n.findPairs(NULL,0);
        assert(a->size==b->size);
        assert(!memcmp(a->ptr,b->ptr,sizeof(int)*a->size));
        Rw2_Vi_Free(a); Rw2_Vi_Free(b);
        if(seed<=60) {
            Rewire2::Miaig small=Build(50,70,seed), large=Build(50,24000,seed);
            Mini_Aig_t *x=Extract(small,8), *y=Extract(large,8);
            assert(x->nSize==y->nSize);
            assert(!memcmp(x->pArray,y->pArray,sizeof(int)*x->nSize));
            Mini_AigStop(x);Mini_AigStop(y);
        }
    }
    // More than 11,600 objects previously skipped sharing; now extract real pairs.
    Rewire2::Miaig large=Build(12000,12008,99);
    int added=large.findShared(12000); assert(added>0);
    printf("PASS: 300 dense/sparse pair sequences, 60 full extraction identities, large case extracted %d pairs\n",added);
    Abc_Stop();
}
