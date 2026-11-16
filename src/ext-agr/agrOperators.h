#ifndef ABC__ext_agr__agrOperators_h
#define ABC__ext_agr__agrOperators_h

#include "base/abc/abc.h"

ABC_NAMESPACE_HEADER_START
#ifdef __cplusplus
extern "C" {
#endif

int AgrEval_NtkRefactorPhysical(Abc_Ntk_t *, int, int, int, int, int, int, int);
int AgrEval_NtkRewrite(Abc_Ntk_t *, int, int, int, int, int);
int Agr_NtkNativeRegionResubstitute(Abc_Ntk_t *, int, int, int, const unsigned char *, int);
void Agr_RwSetMask(const unsigned char *, int);
void Agr_RfSetMask(const unsigned char *, int);
void Agr_RwSetBuckets(const unsigned char *, int, int, double, unsigned char *);
int Agr_RwBucketStats(int *);
void Agr_ClearRewriteCache(void);

#ifdef __cplusplus
}
#endif
ABC_NAMESPACE_HEADER_END

#endif
