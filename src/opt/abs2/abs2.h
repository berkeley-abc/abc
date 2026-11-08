/**CHeader****************************************************************

  FileName    [abs2.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Incremental flop abstraction.]

  Synopsis    [Interfaces for incremental flop abstraction and verification.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 21, 2026.]

  Revision    [$Id: abs2.h,v 1.00 2026/10/21 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__opt__abs2__abs2_h
#define ABC__opt__abs2__abs2_h

#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START

typedef struct Abs2_Par_t_
{
    int nFramesMax;        // Last BMC depth, inclusive; -1 means unlimited.
    int nTimeOut;          // Wall-clock seconds; zero means unlimited.
    int nConfLimit;        // Conflicts per query; zero means unlimited; exhaustion ends the session.
    int nStableMin;        // Stable depths required after nFramesMax.
    int nSatMode;          // 0 default; 1 focused; 2 plain; 3 no elim; 4 phase0;
                          // 5/6 plain+ILB; 7 stable/plain; 8 alternating/plain.
    int fUseCuts;          // Lazy mux and multi-input AND clausification.
    int fMuxProp;          // Complete mux unit propagation with consensus clauses.
    int nCutMax;           // General truth-table cuts: 0 off, or 3..6 leaves.
    int nCnfMode;          // Directional CNF: 0 full, 1 gates, 2 gates and flop links.
    int nResolveMode;      // 0 off, 1 unshared, 2 shared, 3/4 cover minimization, 5 bottom-up memoized.
    int fCompactVars;      // Allocate SAT variables only for encoded nodes.
    int nCompactDepth;     // Switch to compact numbering at this depth; 0 disables switching.
    int nSimplifyEvery;    // Periodic one-round simplification, with retired guards molten; 0 off.
    int fClauseQuery;      // Guard the disjunction of bads with a fresh literal.
    int fNativeQuery;      // Use CaDiCaL's single-query constraint clause.
    int nProofMode;        // Cache proved prefixes: 0 off, 1 flat clauses, 2 shared guard.
    int nActMode;          // Inactive flop guards: 0 free, 1 prefer false, 2 assume false.
    int nAssumeOrder;      // Flop assumptions: 0 register order, 1 reverse, 2/3 old/new guard first.
    int nCbaOrder;         // Generalization order: 0 natural, 1 reverse, 2 depth, 3 area flow.
    int fUsePba;           // Prune concrete flops using failed assumptions.
    int fUseStart;         // Start with the input graph's abstraction map.
    int fStopFull;         // Stop bounded abstraction after reaching a full map.
    int fVerbose;
    int (*pFuncStop)(void *); // Optional cooperative termination callback.
    int (*pFuncYield)(void *); // Yield between queries or during SAT; Run can resume.
    int (*pFuncRefine)(void *); // Before CBA; nonzero stops. Must preserve SAT model.
    void * pStopData;
    int fYielded;           // Last Run yielded; clear the callback condition to resume.
    int iFrame;            // Last completely proved BMC depth, initially -1.
    int nCalls, nCexes, nAdded, nRemoved;
    int nTruthCuts;
    int nResolveCalls, nResolveCuts, nResolvedNodes;
    int nMinimizedCuts, nClausesSaved;
    int nCnfMemoHits;
    int iCompactFrame;     // First compact-numbered frame, or -1 if never enabled.
    int nSimplifies, nReactivations;
    double timeSat, timeRefine, timeSimplify, timeResolve, timeTotal;
} Abs2_Par_t;

typedef struct Abs2_Man_t_ Abs2_Man_t;
typedef struct Fla_Par_t_
{
    int nFramesMax;        // Maximum BMC frames; zero means unlimited.
    int nTimeOut;          // Wall-clock seconds; zero means unlimited.
    int nConfLimit;        // CaDiCaL conflicts per query; exhaustion ends the abstraction session.
    int nFramesStable;     // Stable frames before starting PDR2.
    int nSatMode;          // CaDiCaL configuration, as in Abs2_Par_t.
    int nCutMax;           // Truth-table cut size, as in Abs2_Par_t.
    int nCompactDepth;     // Start compact SAT numbering at this depth; 0 disables.
    int nProveMode;        // PDR2: 0 schedule, 1 plain, 2 dynamic, 3 relative, 4/5 localization.
    int fUsePba;           // Prune concrete flops using failed assumptions.
    int fUseStart;         // Start from the existing flop map.
    int fRefineCex;        // Refine directly from PDR2 counterexamples.
    int fUseThread;        // Run PDR2 concurrently when pthreads are available.
    int fTrimPis;          // Remove unused abstract inputs before proving.
    int fRewrite;          // Rewrite each abstraction using the DRW API.
    int fVerbose;
    int fSilent;           // Suppress normal progress and result messages.
    int (*pFuncStop)(void *); // May be polled by both abstraction and prover threads.
    void * pStopData;
    int iFrame;            // Last completely proved BMC depth.
    int iFrameProved;      // Originating frame of a proved abstraction.
    int nProveCalls;       // Number of PDR2 calls.
    int nSpurious;         // Abstract counterexamples rejected by simulation.
    int nConcrete;         // Final number of concrete registers.
    double timeTotal;
    int fCollectStats;     // Collect CPU time of concurrent prover threads.
    abctime timeProveCpu;  // Excludes synchronous calls already in the owner time.
} Fla_Par_t;

typedef struct Abc_Frame_t_ Abc_Frame_t;
extern void Abs2_SetDefaultParams( Abs2_Par_t * pPars );
// The unrolling uses zero initial values. Explicit nonzero/unknown values
// must be normalized before calling the abstraction APIs.
extern int Abs2_ManCheckZeroInit( Gia_Man_t * pGia );
// Return 0 only for an independently simulated original counterexample,
// -1 for a valid overapproximation, and -2 for invalid input/internal failure.
// A bounded UNSAT result is not a safety proof. The map is stored in
// pGia->vFlopClasses (one means concrete); a counterexample in pGia->pCexSeq.
extern int Abs2_ManPerform( Gia_Man_t * pGia, Abs2_Par_t * pPars );
// Incremental interface. Run may be resumed after a depth limit or an explicit
// yield; a resource interruption ends the session. Stop transfers the map/CEX.
// Parameters and the input graph must remain alive until Stop; the caller
// must not modify the graph during the session. ReadClasses returns a
// borrowed map, which the caller must not modify. Unrolling storage grows
// with depth times the input size; use a depth/time limit to bound the run.
extern Abs2_Man_t * Abs2_ManStart( Gia_Man_t * pGia, Abs2_Par_t * pPars );
extern int Abs2_ManRun( Abs2_Man_t * p, int nFramesMax, int nStableMin );
extern Vec_Int_t * Abs2_ManReadClasses( Abs2_Man_t * p );
extern int Abs2_ManVerifyCex( Abs2_Man_t * p, Abc_Cex_t * pCex );
// Refine from a checked abstract trace. The map is the one passed to Derive;
// input order is original PIs followed by abstract flops in register order.
// Returns added flops, -1 on interruption, -2 on an invalid abstract trace.
extern int Abs2_ManRefine( Abs2_Man_t * p, Abc_Cex_t * pCex, Vec_Int_t * vClasses );
extern void Abs2_ManStop( Abs2_Man_t * p );
extern Gia_Man_t * Abs2_ManDerive( Gia_Man_t * pGia, Vec_Int_t * vClasses );
// Internal cut builder for a plain AND/CI unrolling. Root must be an AND;
// vEncoded/vKeep cover all object IDs. Returns eliminated occurrences, or -1
// on interruption; vCnf contains Gia literals with zero clause separators.
extern int Abs2_CnfResolve( Gia_Man_t * pGia, int Root, Vec_Int_t * vEncoded,
                           Vec_Int_t * vKeep, int Mode, int fMuxProp, Vec_Int_t * vCnf,
                           int * pnClausesSaved, int (*pStop)(void *), void * pData );
extern void Abs2_CnfStart( Gia_Man_t * pGia, int Root, int fMuxProp, Vec_Int_t * vCnf );
extern int Abs2_CnfCombine( Vec_Int_t * vMain, Vec_Int_t * vSide, int Pivot, int fKeep,
                           Vec_Int_t * vScratch, int (*pStop)(void *), void * pData );
extern int Abs2_Command( Abc_Frame_t * pAbc, int argc, char ** argv );
// Stand-alone verification: 1 proved, 0 checked original CEX, -1 undecided,
// -2 invalid input/internal failure. The original design is retained.
extern void Fla_ManSetDefaultParams( Fla_Par_t * pPars );
extern int Gia_ManPerformFla( Gia_Man_t * pGia, Fla_Par_t * pPars );

ABC_NAMESPACE_HEADER_END
#endif
