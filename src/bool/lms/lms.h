/**HFile****************************************************************

  FileName    [lms.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS library generation.]

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

ABC_NAMESPACE_HEADER_END
#endif
