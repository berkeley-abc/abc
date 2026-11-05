/**CFile****************************************************************

  FileName    [rewire2Map.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Map.h,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef REWIRE2_MAP_H
#define REWIRE2_MAP_H

#include "base/abc/abc.h"
#include "aig/gia/giaAig.h"
#include "map/amap/amap.h"
#include "proof/dch/dch.h"
#include "map/mio/mio.h"
#include "aig/miniaig/miniaig.h"

ABC_NAMESPACE_HEADER_START

Abc_Ntk_t *Gia_ManRewire2Put(Gia_Man_t *pGia);
Abc_Ntk_t *Abc_ManRewire2Dch(Abc_Ntk_t *pNtk);
Gia_Man_t *Gia_ManRewire2Dch(Gia_Man_t *pGia);
Abc_Ntk_t *Abc_ManRewire2MapAmap(Abc_Ntk_t *pNtk);
Abc_Ntk_t *Gia_ManRewire2MapNf(Gia_Man_t *pGia);
Abc_Ntk_t *Gia_ManRewire2MapSimap(Gia_Man_t *pGia, int nBound, int nBTLimit, int nTimeout);
Vec_Int_t *Abc_ManRewire2NtkWriteMiniMapping(Abc_Ntk_t *pNtk);
Abc_Ntk_t *Abc_ManRewire2NtkFromMiniMapping(int *vMapping);
Mini_Aig_t *Abc_ManRewire2MiniAigFromNtk(Abc_Ntk_t *pNtk);

ABC_NAMESPACE_HEADER_END

#endif // REWIRE2_MAP_H
