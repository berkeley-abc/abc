/**HFile****************************************************************

  FileName    [lms.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation and target-delay optimization.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 4, 2026.]

  Revision    [$Id: lms.h,v 1.00 2026/10/04 00:00:00 alanmi Exp $]

***********************************************************************/
#ifndef ABC__bool__lms__lms_h
#define ABC__bool__lms__lms_h

#include "misc/util/abc_global.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Lms_Gen_t_ Lms_Gen_t;
typedef struct Lms_Collect_t_ Lms_Collect_t;
typedef struct Lms_Eval_t_ Lms_Eval_t;
typedef struct Gia_Man_t_ Gia_Man_t;

// A candidate has IDs 0=false, 1..nVars=inputs, then nAnds ANDs in
// topological order. Each fanin and Root is a literal (2*ID + complement).
// pFans contains 2*nAnds fanin literals. pDepths contains nVars depths
// (-1 for an unused input). Arrays are borrowed until the callback returns.
// With Lms_GenStartXor, depths use unit AND/XOR levels while pFans still
// contains only AND nodes (three per XOR). Return nonzero to continue;
// return 0 to abort generation.
typedef int (*Lms_GenVisit_t)( void * pData, int nVars, const int * pFans,
    int nAnds, int Root, const int * pDepths );

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// === lmsBuiltin.c ===================================================
// Decode on demand; caller frees writable AIGER bytes with ABC_FREE.
// Returns NULL and length zero on failure. File writers return 1 on success,
// refuse existing outputs, and do not change the current LMS manager.
extern char * Lms_BuiltinDecode( int * pnBytes );
extern char * Lms_BuiltinDecodeXor( int * pnBytes );
extern int Lms_EmbedWrite( const char * pInput, const char * pOutput, FILE * pError );
extern int Lms_BuiltinWrite( const char * pOutput, FILE * pError );

// === lmsEval.c ======================================================
// Borrow immutable class offsets (nClasses+1), packed four-bit pin depths,
// and the legacy char area array until Stop. Find returns the first minimum
// delay/area candidate in the class, with exactly the legacy float-to-int
// delay semantics. Each class must contain at least one candidate.
extern Lms_Eval_t * Lms_EvalStart( int nVars, int nClasses, const int * pStarts,
    const word * pDelays, const char * pAreas );
extern void Lms_EvalStop( Lms_Eval_t * p );
extern int Lms_EvalFind( Lms_Eval_t * p, int Class, int nVars,
    const float * pTimes, int * pDelay );
extern void Lms_EvalStats( Lms_Eval_t * p, FILE * pFile );
extern void Lms_EvalResetStats( Lms_Eval_t * p );
// Optional exact winner memoization. Enabling clears the bounded cache.
extern void Lms_EvalCacheEnable( Lms_Eval_t * p, int fEnable );

// === lmsGen.c =======================================================
// Truth is a 64-bit truth table stretched to six inputs. All nVars inputs
// must be essential and occupy the low input indices (2 <= nVars <= 6).
// Arrivals are integer AIG levels in [0, 1000000]; a common offset is removed.
// The context caches kernels and the last function's decomposition setup.
// Generate returns the candidate count (0 if none), or -1 on invalid input
// or a callback failure. Oversize trials and excess profiles are skipped.
// Candidates retain input
// order and polarity. Recording-stage validation/canonicalization is performed
// by Lms_LibGenerate, not this callback API. No recorded library is used.
extern Lms_Gen_t * Lms_GenStart( void );
extern Lms_Gen_t * Lms_GenStartXor( void );
extern void        Lms_GenStop( Lms_Gen_t * p );
extern int         Lms_GenGenerate( Lms_Gen_t * p, word Truth, int nVars,
    const int * pArrivals, Lms_GenVisit_t pVisit, void * pData );
// Profiles omitted by the pool capacity in the most recent query.
extern int         Lms_GenSkipped( Lms_Gen_t * p );

// === lmsLib.c / lmsCollect.c =========================================
// Offline file interface. Returns 1 on success, 0 on failure. The output
// library must not exist. Diagnostics are written to pError.
extern int Lms_LibGenerate( const char * pInput, const char * pOutput, FILE * pError );
extern int Lms_LibGenerateXor( const char * pInput, const char * pOutput, FILE * pError );
// The collector owns samples, never library structures. Add expects a valid
// truth/arrival pair, normalizes arrival offsets, and does not canonicalize.
// Write overwrites its file without clearing samples; returns 1 on success,
// 0 on failure (including a collector capacity overflow).
extern Lms_Collect_t * Lms_CollectStart( void );
extern void Lms_CollectStop( Lms_Collect_t * p );
extern void Lms_CollectAdd( Lms_Collect_t * p, word Truth, int nVars, const int * pArrivals );
extern int Lms_CollectWrite( Lms_Collect_t * p, const char * pFileName, FILE * pError );

// === lmsOne.c =======================================================
// Treat every CI/CO as a primary terminal, including flop terminals.
// Invalid input returns NULL. Uses resubstitution, the active/built-in six-input
// library when compatible. Area is heuristic.
// CutSize (4..16) applies to delay candidates and area recovery alike.
// Iterate the critical-path optimizer to saturation or StopLevel (-1 means
// no stopping bound). Cache only graph-independent recipes between passes.
// If the stopping bound is not met, first recover area at the input depth.
// At loop exit, repeat recovery while area or depth strictly improves.
// An already-met stopping bound remains a no-op.
// AreaGrowth is the maximum percent node growth of one recovered pass;
// -1 permits unlimited growth. Recovered-batch growth above 1%, or above the
// area limit, prices the remaining composition banks before accepting a pass.
// A feasible over-budget pass retries once with the full helper cut budget,
// retaining the cheaper feasible batch. Enforce the area limit only afterward.
// XOR mode derives a native XAG and counts each AND/XOR as one gate/level.
// Optional escalation first recovers after a miss, rebuilding candidates
// if the graph improves, then widens uncovered roots and fanin helpers to
// at least 12 leaves/128 cuts. Unchanged graphs retain their candidate bank.
// Once feasible, widen cut neighborhoods while the rebuilt batch area falls.
extern Gia_Man_t * Lms_TwoPerform( Gia_Man_t * pGia, int StopLevel, int CutSize,
    int Cuts, int Nodes, int Trials, double AreaGrowth, int fXor, int fEscalate, int fVerbose );
// The visitor borrows the recovered input, each accepted pass and any further
// improvement found during final recovery.
// A zero pass limit runs the ordinary search to its stopping condition.
typedef void (*Lms_TwoVisit_t)( void * pData, Gia_Man_t * pGia, int Depth );
extern Gia_Man_t * Lms_TwoPerformTrace( Gia_Man_t * pGia, int StopLevel, int CutSize,
    int Cuts, int Nodes, int Trials, double AreaGrowth, int fXor, int fEscalate, int fVerbose,
    int nPassLimit, Lms_TwoVisit_t pVisit, void * pData );
extern Gia_Man_t * Lms_TwoPerformTraceTimed( Gia_Man_t * pGia, int StopLevel, int CutSize,
    int Cuts, int Nodes, int Trials, double AreaGrowth, int fXor, int fEscalate, int fVerbose,
    int nPassLimit, Lms_TwoVisit_t pVisit, void * pData, abctime Deadline );

// === lmsCuts.c ======================================================
// Six-input cuts over a combinational AND/XOR GIA, including ordered choices;
// no IF mapper is used. Siblings must point to earlier internal nodes.
// Initialize choice phases with Gia_ManSetPhase before calling the collector.
// Truth includes output polarity and repeats to fill one word. Leaf IDs
// are sorted, and every leaf is essential. Cost returns the library delay
// for integer leaf arrivals, capped at ABC_INFINITY-1 (ABC_INFINITY for a
// missing function), and writes area. Exact feasibility is checked by the DP.
// Cost also fills Match once: the library class (-1 for misses/degenerates),
// canonical-to-leaf permutation, and input/output phase bits. Visit borrows
// this result with the retained cut; it need not canonicalize the truth again.
// vCiArrs supplies nonnegative CI arrivals below ABC_INFINITY, or defaults
// to zero when absent. Delays count unit AND/XOR gates.
// Visit receives retained cuts at nodes with ordinary consumers (all gates
// when no choices are present); arrays are borrowed until it returns.
// Visit returns positive to continue, zero for failure, or negative for an
// intentional stop without an error diagnostic. Collection returns 1 only
// when completed, and 0 after either failure or an intentional stop.
typedef struct Lms_CutMatch_t_ Lms_CutMatch_t;
struct Lms_CutMatch_t_ { int Class; char Perm[6]; unsigned char Phase; };
typedef int (*Lms_CutCost_t)( word Truth, int nLeaves, const int * pTimes, int * pArea, Lms_CutMatch_t * pMatch );
typedef int (*Lms_CutVisit_t)( void * pData, int Root, int nLeaves, const int * pLeaves, word Truth, const Lms_CutMatch_t * pMatch );
extern int Lms_CutsCollect( Gia_Man_t * pGia, int Cuts, Lms_CutCost_t pCost,
    Lms_CutVisit_t pVisit, void * pData, int fVerbose );
// Optional per-object cut budgets in [1, 128]; NULL uses the uniform budget.
extern int Lms_CutsCollectBudgeted( Gia_Man_t * pGia, int Cuts, const int * pLimits,
    Lms_CutCost_t pCost, Lms_CutVisit_t pVisit, void * pData, int fVerbose );
extern int Lms_CutsCollectBudgetedTimed( Gia_Man_t * pGia, int Cuts, const int * pLimits,
    Lms_CutCost_t pCost, Lms_CutVisit_t pVisit, void * pData, int fVerbose, abctime Deadline );
// Recollect after a uniform Cuts pass with unchanged graph, timing, library
// and cost callback.
// Visit only changed budgets and their transitive gate/choice consumers.
// The caller must retain the first bank; fanin sets are still recomputed.
extern int Lms_CutsRecollect( Gia_Man_t * pGia, int Cuts, const int * pLimits,
    Lms_CutCost_t pCost, Lms_CutVisit_t pVisit, void * pData, int fVerbose );

// === lmsTarget.c ====================================================
// Experimental target-delay selection from a directly enumerated cut bank.
// Flop outputs/inputs are exposed as primary inputs/outputs in the result.
// vCiArrs/vCoReqs supply integer arrival/required times in CI/CO order.
// Times are nonnegative and below ABC_INFINITY; CO requirements also accept
// ABC_INFINITY for no constraint. Target >= 0 caps every CO requirement.
// Target -1 uses vCoReqs, or the bank's earliest maximum output arrival if
// vCoReqs is absent. Missing CI arrivals are zero. Infeasibility returns NULL.
// Results preserve both constraint vectors and, when either was provided,
// report actual unit-AND output arrivals in vCoArrs.
// Memory is the deadline-table budget in MiB; 0 retains every distinct state.
// Choice alternatives join the bank; successful results contain no choices.
extern Gia_Man_t * Lms_TargetPerform( Gia_Man_t * pGia, int Target, int Cuts,
    int Rounds, int Exact, int DpMode, int Memory, int fVerbose );
// CriticalCuts > Cuts adds a pilot-guided collection at zero-slack cover roots
// and their internal GIA nodes, stopping at other live cover roots.
// Zero disables it. First-pass candidates remain available and win cost ties.
extern Gia_Man_t * Lms_TargetPerformAdaptive( Gia_Man_t * pGia, int Target, int Cuts,
    int Rounds, int Exact, int DpMode, int Memory, int CriticalCuts, int fVerbose );
// Extended entry: Target retains its hard-deadline semantics. StopLevel is
// an independent lower stopping bound (-1 disables it); an unreachable
// stopping bound still permits progress. A hard deadline or explicit output
// requirement always takes precedence. The command uses Target = -1.
// With fXor, derive/retain native XORs and count AND/XOR as one gate/level.
// Borrow a cached private native library (the active rec_start3 -x library,
// or the combined built-ins), leaving the existing manager/costs intact.
// The combinational result carries unit-XAG CO arrivals in native mode.
extern Gia_Man_t * Lms_TargetPerformEx( Gia_Man_t * pGia, int Target, int StopLevel, int Cuts,
    int Rounds, int Exact, int DpMode, int Memory, int CriticalCuts, int fXor, int fVerbose );
extern int Lms_XorLevelNum( Gia_Man_t * pGia );
// Recorded-cut library integration used by LMS and IF.
extern int Abc_RecTargetReady3( void );
extern int Abc_RecMapCache3( int fStart );
extern int Abc_NtkRecStartBuiltin3( FILE * pOut, FILE * pError );
// Release the private native library between optimizations (also at shutdown).
extern void Abc_RecTargetXorClear3( void );
// Save one canonical binding. PO profile arrays remain valid through selection
// and union recovery; NULL denotes a constant or one-leaf zero-area cut.
extern void Lms_TargetCut( void * pData, int Root, int nLeaves,
    const int * pLeaves, int Compl, const int * pPos, int nPos );

ABC_NAMESPACE_HEADER_END
#endif
