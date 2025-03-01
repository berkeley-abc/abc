#ifndef RAR_H
#define RAR_H

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

Gia_Man_t *Gia_ManRewire(Gia_Man_t *pGia, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nDist, int nSeed, int fVerbose);
Gia_Man_t *Gia_ManRewireInt(Gia_Man_t *pGia, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nDist, int nSeed, int fVerbose);
Abc_Ntk_t *Abc_ManRewire(Abc_Ntk_t *pNtk, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nDist, int nSeed, int fVerbose);
Abc_Ntk_t *Abc_ManRewireInt(Abc_Ntk_t *pNtk, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nDist, int nSeed, int fVerbose);
Mini_Aig_t *MiniAig_ManRewire(Mini_Aig_t *pAig, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nDist, int nSeed, int fVerbose);
Mini_Aig_t *MiniAig_ManRewireInt(Mini_Aig_t *pAig, int nIters, int nExpands, int nGrowth, int nDivs, int nFaninMax, int nTimeOut, int nMode, int nDist, int nSeed, int fVerbose);

ABC_NAMESPACE_HEADER_END

#endif // RAR_H