#ifndef REWIRE_MAP_H
#define REWIRE_MAP_H

#include "base/abc/abc.h"
#include "aig/gia/giaAig.h"
#include "map/amap/amap.h"
#include "map/mio/mio.h"
#include "aig/miniaig/miniaig.h"

ABC_NAMESPACE_HEADER_START

Abc_Ntk_t *Gia_ManRewirePut(Gia_Man_t *pGia);
Abc_Ntk_t *Abc_ManRewireMap(Abc_Ntk_t *pNtk);
Vec_Int_t *Abc_ManRewireNtkWriteMiniMapping(Abc_Ntk_t *pNtk);
Abc_Ntk_t *Abc_ManRewireNtkFromMiniMapping(int *vMapping);
Mini_Aig_t *Abc_ManRewireMiniAigFromNtk(Abc_Ntk_t *pNtk);

ABC_NAMESPACE_HEADER_END

#endif // REWIRE_MAP_H