/**CFile****************************************************************

  FileName    [rewire_rar.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Re-wiring.]

  Synopsis    []

  Author      [Jiun-Hao Chen]
  
  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rewire_rar.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rewire_rar.h"

ABC_NAMESPACE_IMPL_START

Gia_Man_t *Gia_ManRewire(Gia_Man_t *pGia, Gia_Man_t *pExc, int nIters, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int nSeed, int fCheck, int fChoices, int fVerbose) {
    return Gia_ManRewireInt(pGia, pExc, nIters, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, nSeed, fCheck, fChoices, fVerbose);
}

Abc_Ntk_t *Abc_ManRewire(Abc_Ntk_t *pNtk, Gia_Man_t *pExc, int nIters, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int nSeed, int fCheck, int fVerbose) {
    return Abc_ManRewireInt(pNtk, pExc, nIters, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, nSeed, fCheck, fVerbose);
}

Mini_Aig_t *MiniAig_ManRewire(Mini_Aig_t *pAig, Gia_Man_t *pExc, int nIters, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int nSeed, int fCheck, int fVerbose) {
    return MiniAig_ManRewireInt(pAig, pExc, nIters, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, nSeed, fCheck, fVerbose);
}

ABC_NAMESPACE_IMPL_END