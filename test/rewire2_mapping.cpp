/**CFile****************************************************************

  FileName    [rewire2_mapping.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring tests.]

  Synopsis    [Standalone regression of rewiring mapping ownership and equivalence.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 7, 2026.]

  Revision    []

***********************************************************************/

// Build as a standalone executable linked with libabc, not as part of abc.
// For example, from the repository root with GCC or Clang:
// g++ -std=c++17 -DLIN64 -Isrc -fno-access-control test/rewire2_mapping.cpp
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
ABC_NAMESPACE_HEADER_START
void Mio_IntallSimpleLibrary();
ABC_NAMESPACE_HEADER_END
ABC_NAMESPACE_USING_NAMESPACE
// Build the mapper's second library in memory without a checkout-specific file.
static void PrepareLibrary() {
    Mio_IntallSimpleLibrary();
    FILE *file = tmpfile();
    assert(file);
    Mio_WriteLibrary(file, (Mio_Library_t *)Abc_FrameReadLibGen(), 0, 0, 0);
    assert(!fflush(file));
    long length = ftell(file);
    assert(length > 0);
    rewind(file);
    std::vector<char> buffer((size_t)length + 1, 0);
    assert(fread(buffer.data(), 1, (size_t)length, file) == (size_t)length);
    assert(!fclose(file));
    char name[] = "rewire2_test.genlib";
    Vec_Str_t *first = Vec_StrAllocArrayCopy(buffer.data(), (int)buffer.size());
    Vec_Str_t *second = Vec_StrDup(first);
    Vec_StrPop(second);
    Vec_StrAppend(second, ".end\n");
    Vec_StrPush(second, '\0');
    int installed = Mio_UpdateGenlib2(first, second, name, 0);
    Vec_StrFree(first);
    Vec_StrFree(second);
    assert(installed);
}

static unsigned Truth(Gia_Man_t *p) {
    unsigned value = 0;
    for (int pat = 0; pat < 16; ++pat) {
        std::vector<int> bits(Gia_ManObjNum(p));
        Gia_Obj_t *obj; int i;
        Gia_ManForEachCi(p, obj, i) bits[Gia_ObjId(p,obj)] = (pat >> i) & 1;
        Gia_ManForEachAnd(p,obj,i) bits[i] = (bits[Gia_ObjFaninId0(obj,i)] ^ obj->fCompl0) & (bits[Gia_ObjFaninId1(obj,i)] ^ obj->fCompl1);
        obj = Gia_ManCo(p,0); i=Gia_ObjId(p,obj);
        value |= (bits[Gia_ObjFaninId0(obj,i)] ^ obj->fCompl0) << pat;
    }
    return value;
}
int main(int argc, char **argv) {
    Abc_Start(); setvbuf(stdout, NULL, _IONBF, 0); PrepareLibrary();
    if (argc > 2 || (argc == 2 && (argv[1][0] < '0' || argv[1][0] > '2' || argv[1][1]))) {
        fprintf(stderr, "usage: rewire2_mapping [0|1|2]\n");
        Abc_Stop();
        return 1;
    }
    int mapper = argc == 2 ? argv[1][0] - '0' : 0;
    Gia_Man_t *p=Gia_ManStart(64);
    int a=Gia_ManAppendCi(p), b=Gia_ManAppendCi(p), c=Gia_ManAppendCi(p), d=Gia_ManAppendCi(p);
    int x=Gia_ManAppendAnd(p,a,b), y=Gia_ManAppendAnd(p,c,d);
    int z=Gia_ManAppendAnd(p,x^1,y^1);
    Gia_ManAppendCo(p,z^1); p->pName=Abc_UtilStrsav((char *)"mapping_test");
    unsigned expected = Truth(p);
    {
        Rewire2::Miaig n(p);
        float area1=n.countMappedArea(1,mapper,1), area2=n.countMappedArea(1,mapper,1);
        printf("mapper=%d areas=%g,%g\n", mapper, area1, area2); assert(area1 > 0 && area1 < ABC_INFINITY && area1==area2);
        if (mapper != 2) {
            assert(n.countMappedDelay(1,mapper,1)>0);
            assert(n.countMappedDelay(1,mapper,1)>0);
        }
    }
    Gia_Man_t *r=Gia_ManRewire2(p,NULL,3,0,0,16,2,2,4,0,1,mapper,0,1,0,1,1,0,0);
    assert(r && Truth(r)==expected);
    Gia_ManStop(r); Gia_ManStop(p);
    Abc_Stop();
    puts("PASS: repeated mapped objectives and exhaustive equivalence");
}
