/**CFile****************************************************************

  FileName    [imc.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [External declarations.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imc.h,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__proof__imc__imc_h
#define ABC__proof__imc__imc_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Imc_Par_t_ Imc_Par_t;
struct Imc_Par_t_
{
    int nTimeOut;           // total runtime limit in seconds (0 = unlimited)
    int nFrameMax;          // maximum suffix depth (0 = unlimited)
    int nConfLimit;         // conflict limit for image/induction/check queries
    int nBddMax;            // interpolant BDD node limit (0 = disabled)
    int fPortfolio;        // automatic phase schedule; disable for a selected mode
    int fUseMiniSat;        // use ABC's resolution proof solver instead of CaDiCaL
    int fBackward;         // overapproximate predecessors of the bad states
    int fDual;             // negate the interpolant of the reversed partitions
    int fInductive;        // use transition-based union induction
    int fPudlak;           // Pudlak interpolation for LRAT proofs
    int fUseDelta;         // compute images only outside the previous union
    int fGrowFrames;       // grow the suffix using the completed image depth
    int fSweep;            // bounded SAT sweeping of interpolants
    int fAutoItp;          // 0: fixed, 1: all labelings, 2: both polarities
    int fCompose;          // simplify the composed backward image before CNF
    int fPreprocess;       // enable CaDiCaL preprocessing and search defaults
    int fIncremental;      // retain CaDiCaL and its LIDRUP proof between images
    int fSimulate;         // bounded concrete simulation before interpolation
    int fResetPrefix;      // encode a bounded reachable set using optional resets
    int fSeqSweep;         // bounded sequential equivalence preprocessing
    int fMinimize;         // re-solve the proof core before interpolant extraction
    int fWeaken;           // relax interpolant formulas using an UNSAT core
    int fPredicates;       // expose state predicates at the interpolation boundary
    int fAbstract;         // try interpolation over compound predicates first
    int fCheck;            // independently check interpolants and the invariant
    int fVerbose;          // print progress and timing information
    int iFrame;            // output: maximum counterexample frame checked
};

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// McMillan, Interpolation and SAT-based Model Checking, CAV 2003.
// The separate frontier and incremental induction check follow the design
// used by Niklas Een's IMC implementation in ZZ/Bip.
extern void Imc_ManSetDefaultParams( Imc_Par_t * p );
extern int  Imc_ManCheckParams( Imc_Par_t * p );
extern int  Imc_ManPerform( Gia_Man_t * pGia, Imc_Par_t * pPars );
extern int  Imc_ManPerformWithStop( Gia_Man_t * pGia, Imc_Par_t * pPars,
    int (*pFuncStop)(void *), void * pStopData );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
