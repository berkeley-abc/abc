/**CFile****************************************************************

  FileName    [giaTranStoch2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Experimental single-threaded transduction optimization.]

  Author      [Yukio Miyasaka and ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 30, 2026.]

  Description [Based on the original transduction implementation of May 2023.]

***********************************************************************/

#include "base/abc/abc.h"
#include "aig/aig/aig.h"
#include "opt/dar/dar.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "map/mio/mio.h"
#include "opt/sfm/sfm.h"
#include "opt/fxu/fxu.h"

ABC_NAMESPACE_HEADER_START

extern Gia_Man_t * Gia_ManTransduction2BddPolicy(Gia_Man_t *pGia, int nType, int fMspf, unsigned nRandom, int nSortType, int nPiShuffle, int nParameter, int fLevel, Gia_Man_t *pExdc, int fNewLine, int nVerbose, int nCandidates, int nMspfRestarts, int fHybrid, int fLocal, abctime deadline);
extern Gia_Man_t * Gia_ManTransduction2TtPolicy(Gia_Man_t *pGia, int nType, int fMspf, unsigned nRandom, int nSortType, int nPiShuffle, int nParameter, int fLevel, Gia_Man_t *pExdc, int fNewLine, int nVerbose, int nCandidates, int nMspfRestarts, int fHybrid, int fLocal, abctime deadline);

ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
extern int Abc_NtkPerformMfs( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars );
extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern int Abc_NtkFxPerform( Abc_Ntk_t * pNtk, int nNewNodesMax, int nLitCountMax, int fCanonDivs, int fVerbose, int fVeryVerbose );

/**Function*************************************************************

  Synopsis    [Converts a GIA to an ABC network.]

***********************************************************************/
static Abc_Ntk_t * Gia_ManTranStoch2Put( Gia_Man_t * pGia ) {
  Abc_Ntk_t * pNtk;
  Aig_Man_t * pMan = Gia_ManToAig( pGia, 0 );
  pNtk = Abc_NtkFromAigPhase( pMan );
  Aig_ManStop( pMan );
  return pNtk;
}
/**Function*************************************************************

  Synopsis    [Maps the current network to LUTs.]

***********************************************************************/
static Abc_Ntk_t * Gia_ManTranStoch2If( Abc_Ntk_t * pNtk ) {
  If_Par_t Pars, * pPars = &Pars;
  If_ManSetDefaultPars( pPars );
  pPars->pLutLib = (If_LibLut_t *)Abc_FrameReadLibLut();
  pPars->nLutSize = pPars->pLutLib->LutMax;
  return Abc_NtkIf( pNtk, pPars );
}
/**Function*************************************************************

  Synopsis    [Resubstitutes in the mapped network.]

***********************************************************************/
static void Gia_ManTranStoch2Mfs2( Abc_Ntk_t * pNtk ) {
  Sfm_Par_t Pars, * pPars = &Pars;
  Sfm_ParSetDefault( pPars );
  Abc_NtkPerformMfs( pNtk, pPars );
}
/**Function*************************************************************

  Synopsis    [Converts the network back to a GIA.]

***********************************************************************/
static Gia_Man_t * Gia_ManTranStoch2Get( Abc_Ntk_t * pNtk ) {
  Gia_Man_t * pGia;
  Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
  pGia = Gia_ManFromAig( pAig );
  Aig_ManStop( pAig );
  return pGia;
}
/**Function*************************************************************

  Synopsis    [Extracts shared SOP divisors.]

***********************************************************************/
static void Gia_ManTranStoch2Fx( Abc_Ntk_t * pNtk ) {
  Fxu_Data_t Params, * p = &Params;
  Abc_NtkSetDefaultFxParams( p );
  Abc_NtkFxPerform( pNtk, p->nNodesExt, p->LitCountMax, p->fCanonDivs, p->fVerbose, p->fVeryVerbose );
  Abc_NtkFxuFreeInfo( p );
}
/**Function*************************************************************

  Synopsis    [Performs zero-cost refactoring.]

***********************************************************************/
static Gia_Man_t * Gia_ManTranStoch2Refactor( Gia_Man_t * pGia ) {
  Gia_Man_t * pNew;
  Aig_Man_t * pAig, * pTemp;
  Dar_RefPar_t Pars, * pPars = &Pars;
  Dar_ManDefaultRefParams( pPars );
  pPars->fUseZeros = 1;
  pAig = Gia_ManToAig( pGia, 0 );
  Dar_ManRefactor( pAig, pPars );
  pAig = Aig_ManDupDfs( pTemp = pAig );
  Aig_ManStop( pTemp );
  pNew = Gia_ManFromAig( pAig );
  Aig_ManStop( pAig );
  return pNew;
}

struct Gia_ManTranStoch2Param {
  Gia_Man_t * pStart;
  Gia_Man_t * pBestSeen;
  unsigned nSeed;
  int nHops;
  int nRestarts;
  int nSeedBase;
  int fMspf;
  int fMerge;
  int fResetHop;
  int fZeroCostHop;
  int fRefactor;
  int fTruth;
  int fNewLine;
  Gia_Man_t * pExdc;
  int nVerbose;
  int nCandidates;
  int nMspfRestarts;
  int fHybrid;
  int fLocal;
  abctime Deadline;

};

typedef struct Gia_ManTranStoch2Param Gia_ManTranStoch2Param;

/**Function*************************************************************

  Synopsis    [Checks the soft time budget between search steps.]

***********************************************************************/
static int Gia_ManTranStoch2Stopped( Gia_ManTranStoch2Param * p ) {
  return p->Deadline && Abc_Clock() >= p->Deadline;
}

/**Function*************************************************************

  Synopsis    [Retains intermediate improvements when a search policy is enabled.]

***********************************************************************/
static void Gia_ManTranStoch2Remember( Gia_ManTranStoch2Param * p, Gia_Man_t * pGia ) {
  if ( p->pBestSeen && Gia_ManAndNum(pGia) < Gia_ManAndNum(p->pBestSeen) ) {
    Gia_ManStop( p->pBestSeen );
    p->pBestSeen = Gia_ManDup( pGia );
  }
}

/**Function*************************************************************

  Synopsis    [Alternates transduction and cleanup until size stops improving.]

***********************************************************************/
static Gia_Man_t * Gia_ManTranStoch2Opt1( Gia_ManTranStoch2Param * p, Gia_Man_t * pOld ) {
  Gia_Man_t * pGia, * pNew;
  int i = 0, n;
  pGia = Gia_ManDup( pOld );
  do {
    if ( Gia_ManTranStoch2Stopped(p) )
      break;
    n = Gia_ManAndNum( pGia );
    if ( p->fTruth )
      pNew = Gia_ManTransduction2TtPolicy( pGia, (p->fMerge? 8: 7), p->fMspf, p->nSeed++, 0, 0, 0, 0, p->pExdc, p->fNewLine, p->nVerbose > 0? p->nVerbose - 1: 0, p->nCandidates, p->nMspfRestarts, p->fHybrid, p->fLocal, p->Deadline );
    else
      pNew = Gia_ManTransduction2BddPolicy( pGia, (p->fMerge? 8: 7), p->fMspf, p->nSeed++, 0, 0, 0, 0, p->pExdc, p->fNewLine, p->nVerbose > 0? p->nVerbose - 1: 0, p->nCandidates, p->nMspfRestarts, p->fHybrid, p->fLocal, p->Deadline );
    Gia_ManStop( pGia );
    pGia = pNew;
    Gia_ManTranStoch2Remember( p, pGia );
    if ( p->fRefactor ) {
      pNew = Gia_ManTranStoch2Refactor( pGia );
      Gia_ManStop( pGia );
      pGia = pNew;
      Gia_ManTranStoch2Remember( p, pGia );
    } else {
      pNew = Gia_ManCompress2( pGia, 1, 0 );
      Gia_ManStop( pGia );
      pGia = pNew;
      Gia_ManTranStoch2Remember( p, pGia );
    }
    if ( p->nVerbose )
      printf( "*                ite %d : #nodes = %5d\n", i, Gia_ManAndNum( pGia ) );
    i++;
  } while ( n > Gia_ManAndNum( pGia ) );
  return pGia;
}

/**Function*************************************************************

  Synopsis    [Explores mapping hops from one starting point.]

***********************************************************************/
static Gia_Man_t * Gia_ManTranStoch2Opt2( Gia_ManTranStoch2Param * p ) {
  int i, n = Gia_ManAndNum( p->pStart );
  Gia_Man_t * pGia, * pBest, * pNew;
  Abc_Ntk_t * pNtk, * pNtkRes;
  pGia = Gia_ManDup( p->pStart );
  pBest = Gia_ManDup( pGia );
  for ( i = 0; !Gia_ManTranStoch2Stopped(p); i++ ) {
    pNew = Gia_ManTranStoch2Opt1( p, pGia );
    Gia_ManStop( pGia );
    pGia = pNew;
    if ( n > Gia_ManAndNum( pGia ) ) {
      n = Gia_ManAndNum( pGia );
      Gia_ManStop( pBest );
      pBest = Gia_ManDup( pGia );
      if ( p->fResetHop )
        i = 0;
    }
    if ( i == p->nHops || Gia_ManTranStoch2Stopped(p) )
      break;
    if ( p->fZeroCostHop ) {
      pNew = Gia_ManTranStoch2Refactor( pGia );
      Gia_ManStop( pGia );
      pGia = pNew;
    } else {
      pNtk = Gia_ManTranStoch2Put( pGia );
      Gia_ManStop( pGia );
      pNtkRes = Gia_ManTranStoch2If( pNtk );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      Gia_ManTranStoch2Mfs2( pNtk );
      pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pGia = Gia_ManTranStoch2Get( pNtk );
      Abc_NtkDelete( pNtk );
    }
    Gia_ManTranStoch2Remember( p, pGia );
    if ( p->nVerbose )
      printf( "*         hop %d        : #nodes = %5d\n", i, Gia_ManAndNum( pGia ) );
  }
  Gia_ManStop( pGia );
  return pBest;
}

/**Function*************************************************************

  Synopsis    [Repeats the search with different seeds.]

***********************************************************************/
static Gia_Man_t * Gia_ManTranStoch2Opt3( Gia_ManTranStoch2Param * p ) {
  int i, n = Gia_ManAndNum( p->pStart );
  Gia_Man_t * pBest, * pNew;
  pBest = Gia_ManDup( p->pStart );
  for ( i = 0; i <= p->nRestarts && !Gia_ManTranStoch2Stopped(p); i++ ) {
    p->nSeed = 1234u * ((unsigned)i + (unsigned)p->nSeedBase);
    pNew = Gia_ManTranStoch2Opt2( p );
    if ( p->nRestarts && p->nVerbose )
      printf( "*  res %2d              : #nodes = %5d\n", i, Gia_ManAndNum( pNew ) );
    if ( n > Gia_ManAndNum( pNew ) ) {
      n = Gia_ManAndNum( pNew );
      Gia_ManStop( pBest );
      pBest = pNew;
    } else {
      Gia_ManStop( pNew );
    }
  }
  return pBest;
}


/**Function*************************************************************

  Synopsis    [Runs independent stochastic transduction with one worker.]

***********************************************************************/
Gia_Man_t * Gia_ManTranStoch2( Gia_Man_t * pGia, int nRestarts, int nHops, int nSeedBase, int fMspf, int fMerge, int fResetHop, int fZeroCostHop, int fRefactor, int fTruth, int fSingle, int fOriginalOnly, int fNewLine, Gia_Man_t * pExdc, int nVerbose, int nCandidates, int nMspfRestarts, int fHybrid, int fLocal, int nTime ) {
  int i, j = 0;
  Gia_Man_t * pNew, * pBest, * pStart;
  Abc_Ntk_t * pNtk, * pNtkRes; Vec_Ptr_t * vpStarts;
  Gia_ManTranStoch2Param Par, *p = &Par;
  if ( Gia_ManAndNum(pGia) == 0 )
    return Gia_ManDup(pGia);
  p->nRestarts = nRestarts;
  p->nHops = nHops;
  p->nSeedBase = nSeedBase;
  p->fMspf = fMspf;
  p->fMerge = fMerge;
  p->fResetHop = fResetHop;
  p->fZeroCostHop = fZeroCostHop;
  p->fRefactor = fRefactor;
  p->fTruth = fTruth == 1 || (fTruth == 2 && Gia_ManCiNum(pGia) <= 12);
  p->fNewLine = fNewLine;
  p->pExdc = pExdc;
  p->nVerbose = nVerbose;
  p->nCandidates = nCandidates;
  p->nMspfRestarts = nMspfRestarts;
  p->fHybrid = fHybrid;
  p->fLocal = fLocal;
  p->Deadline = nTime ? Abc_Clock() + (abctime)nTime * CLOCKS_PER_SEC : 0;
  p->pBestSeen = (nCandidates || nMspfRestarts || fHybrid || fLocal || nTime) ? Gia_ManDup(pGia) : NULL;
  // Build alternative starting points only when their BDD package is available.
#ifndef ABC_USE_CUDD
  fOriginalOnly = 1;
#endif
  // setup start points
  vpStarts = Vec_PtrAlloc( 4 );
  Vec_PtrPush( vpStarts, Gia_ManDup( pGia ) );
  if ( !fOriginalOnly && Gia_ManCiNum(pGia) <= 16 ) {
    if ( !Gia_ManTranStoch2Stopped(p) ) { // &put; collapse; st; &get;
      pNtk = Gia_ManTranStoch2Put( pGia );
      pNtkRes = Abc_NtkCollapse( pNtk, ABC_INFINITY, 0, 1, 0, 0, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pNew = Gia_ManTranStoch2Get( pNtk );
      Abc_NtkDelete( pNtk );
      Vec_PtrPush( vpStarts, pNew );
    }
    if ( !Gia_ManTranStoch2Stopped(p) ) { // &ttopt;
      pNew = Gia_ManTtopt( pGia, Gia_ManCiNum( pGia ), Gia_ManCoNum( pGia ), 100 );
      Vec_PtrPush( vpStarts, pNew );
    }
    if ( !Gia_ManTranStoch2Stopped(p) ) { // &put; collapse; sop; fx;
      pNtk = Gia_ManTranStoch2Put( pGia );
      pNtkRes = Abc_NtkCollapse( pNtk, ABC_INFINITY, 0, 1, 0, 0, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
      Gia_ManTranStoch2Fx( pNtk );
      pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pNew = Gia_ManTranStoch2Get( pNtk );
      Abc_NtkDelete( pNtk );
      Vec_PtrPush( vpStarts, pNew );
    }
  }
  if ( fSingle ) {
    pBest = (Gia_Man_t *)Vec_PtrEntry( vpStarts, 0 );
    for ( i = 1; i < Vec_PtrSize( vpStarts ); i++ ) {
      pStart = (Gia_Man_t *)Vec_PtrEntry( vpStarts, i );
      if ( Gia_ManAndNum( pStart ) < Gia_ManAndNum( pBest ) ) {
        Gia_ManStop( pBest );
        pBest = pStart;
        j = i;
      } else {
        Gia_ManStop( pStart );
      }
    }
    Vec_PtrClear( vpStarts );
    Vec_PtrPush( vpStarts, pBest );
  }
  // optimize
  pBest = Gia_ManDup( pGia );
  {
    Vec_PtrForEachEntry( Gia_Man_t *, vpStarts, pStart, i ) {
      if ( p->nVerbose )
        printf( "*begin starting point %d: #nodes = %5d\n", i + j, Gia_ManAndNum( pStart ) );
      p->pStart = pStart;
      Gia_ManTranStoch2Remember( p, pStart );
      pNew = Gia_ManTranStoch2Opt3( p );
      if ( p->nVerbose )
        printf( "*end   starting point %d: #nodes = %5d\n", i + j, Gia_ManAndNum( pNew ) );
      if ( Gia_ManAndNum( pBest ) > Gia_ManAndNum( pNew ) ) {
        Gia_ManStop( pBest );
        pBest = pNew;
      } else {
        Gia_ManStop( pNew );
      }
      Gia_ManStop( pStart );
    }
  }
  if ( p->pBestSeen ) {
    if ( Gia_ManAndNum(p->pBestSeen) < Gia_ManAndNum(pBest) ) {
      Gia_ManStop( pBest );
      pBest = p->pBestSeen;
    } else
      Gia_ManStop( p->pBestSeen );
  }
  if ( nVerbose )
    printf( "best: %d\n", Gia_ManAndNum( pBest ) );
  Vec_PtrFree( vpStarts );
  ABC_FREE( pBest->pName );
  ABC_FREE( pBest->pSpec );
  pBest->pName = Abc_UtilStrsav( pGia->pName );
  pBest->pSpec = Abc_UtilStrsav( pGia->pSpec );
  return pBest;
}

ABC_NAMESPACE_IMPL_END
