/**CFile****************************************************************

  FileName    [giaTranStoch.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Implementation of transduction method.]

  Author      [Yukio Miyasaka]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 2023.]

  Revision    [$Id: giaTranStoch.c,v 1.00 2023/05/10 00:00:00 Exp $]

***********************************************************************/

#include <base/abc/abc.h>
#include <aig/aig/aig.h>
#include <opt/dar/dar.h>
#include <aig/gia/gia.h>
#include <aig/gia/giaAig.h>
#include <base/main/main.h>
#include <base/main/mainInt.h>
#include <map/mio/mio.h>
#include <opt/sfm/sfm.h>
#include <opt/fxu/fxu.h>

ABC_NAMESPACE_IMPL_START

extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
extern int Abc_NtkPerformMfs( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars );
extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern int Abc_NtkFxPerform( Abc_Ntk_t * pNtk, int nNewNodesMax, int nLitCountMax, int fCanonDivs, int fVerbose, int fVeryVerbose );

Abc_Ntk_t * Gia_ManTranStochPut( Gia_Man_t * pGia ) {
  Abc_Ntk_t * pNtk;
  Aig_Man_t * pMan = Gia_ManToAig( pGia, 0 );
  pNtk = Abc_NtkFromAigPhase( pMan );
  Aig_ManStop( pMan );
  return pNtk;
}
Abc_Ntk_t * Gia_ManTranStochIf( Abc_Ntk_t * pNtk ) {
  If_Par_t Pars, * pPars = &Pars;
  If_ManSetDefaultPars( pPars );
  pPars->pLutLib = (If_LibLut_t *)Abc_FrameReadLibLut();
  pPars->nLutSize = pPars->pLutLib->LutMax;
  return Abc_NtkIf( pNtk, pPars );
}
void Gia_ManTranStochMfs2( Abc_Ntk_t * pNtk ) {
  Sfm_Par_t Pars, * pPars = &Pars;
  Sfm_ParSetDefault( pPars );
  Abc_NtkPerformMfs( pNtk, pPars );
}
Gia_Man_t * Gia_ManTranStochGet( Abc_Ntk_t * pNtk ) {
  Gia_Man_t * pGia;
  Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
  pGia = Gia_ManFromAig( pAig );
  Aig_ManStop( pAig );
  return pGia;
}
void Gia_ManTranStochFx( Abc_Ntk_t * pNtk ) {
  Fxu_Data_t Params, * p = &Params;
  Abc_NtkSetDefaultFxParams( p );
  Abc_NtkFxPerform( pNtk, p->nNodesExt, p->LitCountMax, p->fCanonDivs, p->fVerbose, p->fVeryVerbose );
  Abc_NtkFxuFreeInfo( p );
}

struct Gia_ManTranStochParam {
  int nSeed;
  int nHops;
  int nRestarts;
  int nSeedBase;
  int fCspf;
  int fMerge;
  int fResetHop;
  int fTruth;
  int fNewLine;
  Gia_Man_t * pExdc;
  int nVerbose;
};

typedef struct Gia_ManTranStochParam Gia_ManTranStochParam;
  
Gia_Man_t * Gia_ManTranStochOpt1( Gia_ManTranStochParam * p, Gia_Man_t * pOld ) {
  Gia_Man_t * pGia, * pNew;
  int i = 0, n;
  pGia = Gia_ManDup( pOld );
  do {
    n = Gia_ManAndNum( pGia );
    if ( p->fTruth )
      pNew = Gia_ManTransductionTt( pGia, (p->fMerge? 8: 7), !p->fCspf, p->nSeed++, 0, 0, 0, 0, p->pExdc, p->fNewLine, p->nVerbose > 0? p->nVerbose - 1: 0 );
    else
      pNew = Gia_ManTransductionBdd( pGia, (p->fMerge? 8: 7), !p->fCspf, p->nSeed++, 0, 0, 0, 0, p->pExdc, p->fNewLine, p->nVerbose > 0? p->nVerbose - 1: 0 );
    Gia_ManStop( pGia );
    pGia = pNew;    
    pNew = Gia_ManCompress2( pGia, 1, 0 );
    Gia_ManStop( pGia );
    pGia = pNew;
    if ( p->nVerbose )
      printf( "*                ite %d : #nodes = %5d\n", i, Gia_ManAndNum( pGia ) );
    i++;
  } while ( n > Gia_ManAndNum( pGia ) );
  return pGia;
}

Gia_Man_t * Gia_ManTranStochOpt2( Gia_ManTranStochParam * p, Gia_Man_t * pOld ) {
  int i, n = Gia_ManAndNum( pOld );
  Gia_Man_t * pGia, * pBest, * pNew;
  Abc_Ntk_t * pNtk, * pNtkRes;
  pGia = Gia_ManDup( pOld );
  pBest = Gia_ManDup( pGia );
  for ( i = 0; 1; i++ ) {
    pNew = Gia_ManTranStochOpt1( p, pGia );
    Gia_ManStop( pGia );
    pGia = pNew;
    if ( n > Gia_ManAndNum( pGia ) ) {
      n = Gia_ManAndNum( pGia );
      Gia_ManStop( pBest );
      pBest = Gia_ManDup( pGia );
      if ( p->fResetHop )
        i = 0;
    }
    if ( i == p->nHops )
      break;
    pNtk = Gia_ManTranStochPut( pGia );
    Gia_ManStop( pGia );
    pNtkRes = Gia_ManTranStochIf( pNtk );
    Abc_NtkDelete( pNtk );
    pNtk = pNtkRes;
    Gia_ManTranStochMfs2( pNtk );
    pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
    Abc_NtkDelete( pNtk );
    pNtk = pNtkRes;
    pGia = Gia_ManTranStochGet( pNtk );
    Abc_NtkDelete( pNtk );
    if ( p->nVerbose )
      printf( "*         hop %d        : #nodes = %5d\n", i, Gia_ManAndNum( pGia ) );
  }
  Gia_ManStop( pGia );
  return pBest;
}

Gia_Man_t * Gia_ManTranStochOpt3( Gia_ManTranStochParam * p, Gia_Man_t * pOld ) {
  int i, n = Gia_ManAndNum( pOld );
  Gia_Man_t * pBest, * pNew;
  pBest = Gia_ManDup( pOld );
  for ( i = 0; i <= p->nRestarts; i++ ) {
    p->nSeed = 1234 * (i + p->nSeedBase);
    pNew = Gia_ManTranStochOpt2( p, pOld );
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

Gia_Man_t * Gia_ManTranStoch( Gia_Man_t * pGia, int nRestarts, int nHops, int nSeedBase, int fCspf, int fMerge, int fResetHop, int fTruth, int fSingle, int fOriginalOnly, int fNewLine, Gia_Man_t * pExdc, int nVerbose ) {
  int i, j = 0;
  Gia_Man_t * pNew, * pBest, * pStart;
  Abc_Ntk_t * pNtk, * pNtkRes; Vec_Ptr_t * vpStarts;
  Gia_ManTranStochParam Par, *p = &Par;
  p->nRestarts = nRestarts;
  p->nHops = nHops;
  p->nSeedBase = nSeedBase;
  p->fCspf = fCspf;
  p->fMerge = fMerge;
  p->fResetHop = fResetHop;
  p->fTruth = fTruth;
  p->fNewLine = fNewLine;
  p->pExdc = pExdc;
  p->nVerbose = nVerbose;
  // setup start points
  vpStarts = Vec_PtrAlloc( 4 );
  Vec_PtrPush( vpStarts, Gia_ManDup( pGia ) );
  if ( !fOriginalOnly ) {
    { // &put; collapse; st; &get;
      pNtk = Gia_ManTranStochPut( pGia );
      pNtkRes = Abc_NtkCollapse( pNtk, ABC_INFINITY, 0, 1, 0, 0, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pNew = Gia_ManTranStochGet( pNtk );
      Abc_NtkDelete( pNtk );
      Vec_PtrPush( vpStarts, pNew );
    }
    { // &ttopt;
      pNew = Gia_ManTtopt( pGia, Gia_ManCiNum( pGia ), Gia_ManCoNum( pGia ), 100 );
      Vec_PtrPush( vpStarts, pNew );
    }
    { // &put; collapse; sop; fx; 
      pNtk = Gia_ManTranStochPut( pGia );
      pNtkRes = Abc_NtkCollapse( pNtk, ABC_INFINITY, 0, 1, 0, 0, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
      Gia_ManTranStochFx( pNtk );
      pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
      Abc_NtkDelete( pNtk );
      pNtk = pNtkRes;
      pNew = Gia_ManTranStochGet( pNtk );
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
  Vec_PtrForEachEntry( Gia_Man_t *, vpStarts, pStart, i ) {
    if ( p->nVerbose )
      printf( "*begin starting point %d: #nodes = %5d\n", i + j, Gia_ManAndNum( pStart ) );
    pNew = Gia_ManTranStochOpt3( p, pStart );
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
  if ( p->nVerbose )
    printf( "best: %d\n", Gia_ManAndNum( pBest ) );
  Vec_PtrFree( vpStarts );
  return pBest;
}

ABC_NAMESPACE_IMPL_END
