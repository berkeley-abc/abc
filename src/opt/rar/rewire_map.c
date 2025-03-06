/**CFile****************************************************************

  FileName    [rewire_map.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Re-wiring.]

  Synopsis    []

  Author      [Jiun-Hao Chen]
  
  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rewire_map.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rewire_map.h"

ABC_NAMESPACE_IMPL_START

extern Abc_Ntk_t *Abc_NtkFromAigPhase(Aig_Man_t *pMan);
extern Abc_Ntk_t *Abc_NtkDarAmap(Abc_Ntk_t *pNtk, Amap_Par_t *pPars);
extern void *Abc_FrameReadLibGen2();
extern Vec_Int_t * Abc_NtkWriteMiniMapping( Abc_Ntk_t * pNtk );
extern void Abc_NtkPrintMiniMapping( int * pArray );
extern Abc_Ntk_t * Abc_NtkFromMiniMapping( int *vMapping );
extern Mini_Aig_t * Abc_MiniAigFromNtk ( Abc_Ntk_t *pNtk );

Abc_Ntk_t *Gia_ManRewirePut(Gia_Man_t *pGia) {
    Aig_Man_t *pMan = Gia_ManToAig(pGia, 0);
    Abc_Ntk_t *pNtk = Abc_NtkFromAigPhase(pMan);
    Aig_ManStop(pMan);
    return pNtk;
}

Abc_Ntk_t *Abc_ManRewireMap(Abc_Ntk_t *pNtk) {
    Amap_Par_t Pars, *pPars = &Pars;
    Amap_ManSetDefaultParams(pPars);
    Abc_Ntk_t *pNtkMapped = Abc_NtkDarAmap(pNtk, pPars);
    if (pNtkMapped == NULL) {
        Abc_NtkDelete(pNtk);
        Abc_Print(-1, "Mapping has failed.\n");
        return NULL;
    }

    return pNtkMapped;
}

Vec_Int_t *Abc_ManRewireNtkWriteMiniMapping(Abc_Ntk_t *pNtk) {
    return Abc_NtkWriteMiniMapping(pNtk);
}

Abc_Ntk_t *Abc_ManRewireNtkFromMiniMapping(int *vMapping) {
    return Abc_NtkFromMiniMapping(vMapping);
}

Mini_Aig_t *Abc_ManRewireMiniAigFromNtk(Abc_Ntk_t *pNtk) {
    return Abc_MiniAigFromNtk(pNtk);
}

ABC_NAMESPACE_IMPL_END