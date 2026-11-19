#ifndef ABC__ext_agr__agrAig_h
#define ABC__ext_agr__agrAig_h
#include "base/abc/abc.h"
ABC_NAMESPACE_HEADER_START
#ifdef __cplusplus
extern "C"
{
#endif
    int Agr_AigReplace(Abc_Aig_t *pMan, Abc_Obj_t *pOld, Abc_Obj_t *pNew, int fUpdateLevel);
#ifdef __cplusplus
}
#endif
ABC_NAMESPACE_HEADER_END
#endif
