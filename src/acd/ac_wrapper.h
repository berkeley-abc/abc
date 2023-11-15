// #pragma once
#ifndef __ACD_WRAPPER_H_
#define __ACD_WRAPPER_H_

// #include "base/main/main.h"
#include "misc/util/abc_global.h"

// ABC_NAMESPACE_HEADER_START

#ifdef __cplusplus
extern "C" {
#endif

int acd_evaluate( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned *cost );
int acd_decompose( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned char *decomposition );

#ifdef __cplusplus
}
#endif

// ABC_NAMESPACE_HEADER_END

#endif