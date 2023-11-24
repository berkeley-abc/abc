#pragma once
#ifndef __ACD_WRAPPER_H_
#define __ACD_WRAPPER_H_

#include "misc/util/abc_global.h"
#include "map/if/if.h"

#ifdef __cplusplus
extern "C" {
#endif

int acd_evaluate( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned *cost, int try_no_late_arrival );
int acd_decompose( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned char *decomposition );

#ifdef __cplusplus
}
#endif

#endif