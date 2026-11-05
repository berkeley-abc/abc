/**CFile****************************************************************

  FileName    [rewire2Rar.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Rar.c,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rewire2Rar.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Runs independent rewiring with the requested search limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t *Gia_ManRewire2(Gia_Man_t *pGia, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fChoices, int fVerbose) {
    return Gia_ManRewire2Int(pGia, pExc, nIters, nStall, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, nSeed, fCheck, fChoices, fVerbose);
}

/**Function*************************************************************

  Synopsis    [Runs independent rewiring with the requested search limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t *Abc_ManRewire2(Abc_Ntk_t *pNtk, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose) {
    return Abc_ManRewire2Int(pNtk, pExc, nIters, nStall, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, nSeed, fCheck, fVerbose);
}

/**Function*************************************************************

  Synopsis    [Runs independent rewiring with the requested search limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Mini_Aig_t *MiniAig_ManRewire2(Mini_Aig_t *pAig, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose) {
    return MiniAig_ManRewire2Int(pAig, pExc, nIters, nStall, levelGrowRatio, nExpands, nGrowth, nDivs, nFaninMax, nTimeOut, nMode, nMappedMode, nDist, fDch, fTiming, nSeed, fCheck, fVerbose);
}

ABC_NAMESPACE_IMPL_END
