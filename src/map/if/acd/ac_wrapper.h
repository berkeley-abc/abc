/**C++File**************************************************************

  FileName    [ac_wrapper.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Ashenhurst-Curtis decomposition.]

  Synopsis    [Interface with the FPGA mapping package.]

  Author      [Alessandro Tempia Calvino]
  
  Affiliation [EPFL]

  Date        [Ver. 1.0. Started - November 20, 2023.]

***********************************************************************/

#pragma once
#ifndef __ACD_WRAPPER_H_
#define __ACD_WRAPPER_H_

#include "misc/util/abc_global.h"
#include "map/if/if.h"

ABC_NAMESPACE_HEADER_START

int acd_evaluate( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned *cost, int try_no_late_arrival );
int acd_decompose( word * pTruth, unsigned nVars, int lutSize, unsigned *pdelay, unsigned char *decomposition );

ABC_NAMESPACE_HEADER_END

#endif