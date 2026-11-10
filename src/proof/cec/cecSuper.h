/**CFile****************************************************************

  FileName    [cecSuper.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential verification orchestration.]

  Synopsis    [Native super_prove interface.]

  Author      [OpenAI Codex, with Alan Mishchenko]

  Affiliation [ABC project]

  Date        [Ver. 1.0. Started - November 9, 2026.]

  Revision    [$Id: cecSuper.h,v 1.00 2026/11/09 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__proof__cec__cecSuper_h
#define ABC__proof__cec__cecSuper_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Cec_ParSuper_t_
{
    int nProcs;             // maximum simultaneously active solver workers
    int nTimeOut;           // total time limit in seconds
    int iEngine;            // 0 = automatic; otherwise a selected experiment
    int fRewrite;           // use balance-free drwsat before races and after correspondence
    int fVerbose;           // report worker starts, reductions, and finishes
    int fSilent;            // suppress the final result line
    int nStarted;           // output: number of engine invocations
    int nReduced;           // output: number of accepted smaller models
    const char * pWinner;   // output: winning engine, or NULL
} Cec_ParSuper_t;

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

extern void         Cec_ManSuperSetDefaultParams( Cec_ParSuper_t * pPars );
extern const char * Cec_ManSuperEngineName( int iEngine );
extern int          Cec_ManSuperEngineId( const char * pName );
// Zero-initialized, unconstrained safety properties. Returns 1 (proved),
// 0 (original CEX checked), -1 (undecided), -2 (unsupported input or parameters),
// or -3 (worker synchronization initialization failed).
// Retains the original graph and stores a checked trace in pGia->pCexSeq.
extern int          Cec_GiaSuperProve( Gia_Man_t * pGia, Cec_ParSuper_t * pPars );

ABC_NAMESPACE_HEADER_END
#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
