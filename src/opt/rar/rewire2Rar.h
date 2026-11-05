/**CFile****************************************************************

  FileName    [rewire2Rar.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Improved re-wiring.]

  Synopsis    [Independent rewiring implementation derived from rewire.]

  Author      [Jiun-Hao Chen]

  Affiliation [National Taiwan University]

  Date        [Ver. 1.0. Started - November 4, 2026.]

  Revision    [$Id: rewire2Rar.h,v 1.00 2026/11/04 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef RAR2_H
#define RAR2_H

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "base/abc/abc.h"
#include "aig/gia/gia.h"
#include "aig/miniaig/miniaig.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

Gia_Man_t *Gia_ManRewire2(Gia_Man_t *pGia, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fChoices, int fVerbose);
Gia_Man_t *Gia_ManRewire2Int(Gia_Man_t *pGia, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fChoices, int fVerbose);
Abc_Ntk_t *Abc_ManRewire2(Abc_Ntk_t *pNtk, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose);
Abc_Ntk_t *Abc_ManRewire2Int(Abc_Ntk_t *pNtk, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose);
Mini_Aig_t *MiniAig_ManRewire2(Mini_Aig_t *pAig, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose);
Mini_Aig_t *MiniAig_ManRewire2Int(Mini_Aig_t *pAig, Gia_Man_t *pExc, int nIters, int nStall, float levelGrowRatio, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nMappedMode, int nDist, int fDch, int fTiming, int nSeed, int fCheck, int fVerbose);

ABC_NAMESPACE_HEADER_END

#endif // RAR2_H
