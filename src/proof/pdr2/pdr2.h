/**CFile****************************************************************

  FileName    [pdr2.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__proof__pdr2__pdr2_h
#define ABC__proof__pdr2__pdr2_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/aig/aig.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

enum { PDR2_SCHED_DIRECT = 0, PDR2_SCHED_BASE = 3, PDR2_SCHED_TUNED, PDR2_SCHED_TUNED_DIRECT, PDR2_SCHED_CHECKED };
typedef struct Pdr2_Par_t_ Pdr2_Par_t;
struct Gip_Options_t_;
struct Pdr2_Par_t_
{
    int nFrameMax;        // limit on frame count (0 = no limit)
    int nTimeOut;         // timeout in seconds (0 = no limit)
    int nRandomSeed;      // seed for the internal random generator
    int fCtg;             // generalization with counterexamples to generalization
    int nInputPolicy;     // internal per-run override: -1 ordinary, 0 environment, 1 inputs, 2 adaptive inputs
    int fDynamic;         // CTG effort chosen from the obligation activity (disables dropping)
    int nDynLimitMax;     // cap on the CTG blocking effort in dynamic mode
    int nDynAct;          // activity threshold for CTG in dynamic mode
    int nDynTime;         // first dynamic slice in nominal seconds of propagations (0 = dynamic mode only)
    int nCtgTime;         // first CTG slice in nominal seconds of propagations
    int fDynFirst;        // start with a dynamic phase (otherwise with a CTG phase)
    int fShareInf;        // pass the invariant lemmas of each run to the other
    int nDynExplode;      // switch to CTG when a level handles this many obligations (and 3x the previous max; 0 = never)
    int nLevelRestart;    // millions of solver propagations at one level before the obligation queue is restarted (budget doubles; 0 = never)
    int fTimeGen;         // time generalization: 0 = off, 1 = only the placement in frame infinity, 2 = also the frame jumps
    int fSemContain;      // semantic containment check of obligations
    int fKeepObl;         // keep obligations pushed beyond the last frame for the next level
    int nQueueOrder;      // within a frame: 0 = deepest chain (rIC3), 1 = shortest cube then newest creation,
                          // 2 = most recently queued (treb), 3 = shortest cube then most recently queued
    int nCtgMax;          // max number of CTGs handled per literal drop
    int nCtgLimit;        // CTG blocking effort limit
    int fCtgMic;          // generalize the lemmas blocking CTGs (otherwise use the inductive core)
    int fCtgLocal;        // rebuild the SAT domain per CTG query instead of fixing the full MIC cone
    int fDropPo;          // drop proof obligations that keep failing
    int nDropAct;         // activity above which an obligation is dropped (CTG mode)
    int nDynDropAct;      // the same in dynamic mode (0 = never drop)
    int fParentLemma;     // order literals of a cube by the parent lemma
    int fLift;            // use cheap SAT-model lifting before the SAT-core lift
    int fPropHyp;         // assert the property in completed frames
    int fBlockInduct;     // assume the negation of the cube when blocking it (relative induction, as pdr/treb)
    int nPrefix;         // try this many literals before a blocking cube at least four times larger
    int fCtiCache;        // cache counterexamples to propagation
    int nCtpMax;          // attempts to block a counterexample to propagation (0 = disabled)
    int fUseAbs;          // localization abstraction of flops
    int nAbsStart;        // start the abstraction after this many seconds (0 = from the start)
    int fAbsCleanup;      // remove unused flops from the abstraction at each new frame
    int fAbsRefineAll;    // refine with all pseudo-inputs of a spurious counterexample
    int fAbsReset;        // gate flop outputs with a reset flop (treb's encoding of the initial state)
    int fAbsRefineXsim;   // refine by ternary-simulation minimization (treb style)
    int nAbsRefineMode;   // 0 = recorded pseudo-inputs fixed, others follow the logic; 1 = all flops outside the abstraction fixed;
                          // 2 = also all of them are candidates, flop by flop (treb); 3 = 2 + the property output of every frame stays known
    int nAbsRuns;         // number of abstraction runs added to the alternating schedule (0..2)
    int fDynRun;          // the plain run with dynamic generalization in the alternating schedule (0 = only its abstraction run)
    int fSimRun;          // run CTG generalization with the weakening by simulation as another alternating run
    int nBmcTime;         // time limit (sec) of a BMC stage run once after the first slice of the schedule (0 = none)
    int nAbsTime;         // first abstraction slice in nominal seconds of propagations
    int fTopCtg;          // minimum CTG effort for top-level obligations in dynamic mode
    int fInfPromote;      // move a new lemma straight to frame infinity when it is inductive relative to the invariant lemmas
    int nMicMode;         // 0 = rIC3's MIC (down / ctg_down), 1 = treb's two-orbit literal removal with core shrinking
    int nMicFailLimit;    // stop MIC after this many consecutive failed drops (0 = no limit)
    int nDownCacheMode;   // 0 = necessary literals, 1 = removed literals (rIC3), 2 = cache disabled
    int nCtgSmall;        // use plain down for cores of at most this size (0 = off)
    int nCtgMinRate;      // adapt CTG when literal-drop success is below this percentage (0 = off)
    int nLiftIters;       // max number of lifting iterations (0 = until no change)
    int fSparseLift;      // collect lifting inputs/latches from small SAT trails/domains
    int fWarmStart;       // import invariant-safe SAT learning and heuristics into new frames
    int nLiftSim;         // weaken the predecessor by justification and ternary simulation (treb): 0 = no, 1 = before the SAT core, 2 = instead of it
    int nLiftSimOrder;    // order of the removal trials: 0 = highest activity first (treb), 1 = lowest first, 2 = by flop index
    int fPreproc;         // simplify the design with signal correspondence (scorr) first
    int fPartRun;         // internal decomposed-property invocation (forces COI, prevents recursion)
    int fShiftRun;        // internal lookahead depth (0 = original property)
    int fStrideRun;       // internal invocation on several transitions per step
    int fPredRun;         // internal invocation with redundant state predicates
    int nInitLiReg;       // internal: 1-based LI whose function constrains initial states (0 = none)
    int nInitWitnessPi;   // internal: 1-based first PI used only as an initial-state witness
    int nInitWitnessNum;  // number of such PIs, independent of the transition and property
    Vec_Wec_t * vPartCandidates; // borrowed candidate clauses exchanged between property parts
    int nPreprocTime;     // time limit of the simplification in seconds
    int fVerify;          // verify the inductive invariant when proved
    int fVerifyComplete;  // with fVerify, reject incomplete verification (0 = retain master's deadline behavior)
    int fDumpInv;         // dump the inductive invariant
    int fVerbose;         // verbose output
    int fVeryVerbose;     // very verbose output
    int fSilent;          // totally silent execution
    int RunId;            // identifier passed to the termination callback
    int (*pFuncStop)(int); // cooperative termination callback (NULL = none)
    int nPropUnit;        // solver propagations per nominal second (0 = the default, 12 M; small values let tests reach the slice ends and restarts)
    ABC_INT64_T nPropLimit; // soft propagation budget (0 = unlimited; a nonzero budget skips BMC)
                           // the in-flight obligation can use one extra slice before stopping
    int iFrame;           // output: the number of frames explored
    int nPhasesRun;       // output: the number of schedule phases run
    int nRestartsRun;     // output: the number of level restarts in all runs
    int fBmcDecided;      // output: the BMC stage decided the property
    char * pInvFileName;  // invariant file name
    abctime timePolicyStop; // outer deadline for fixed-depth CNF construction (-1 = standalone, 0 = unlimited)
    const struct Gip_Options_t_ * pOptions;
    int iSchedule;
};

// Borrowed for one frame-hint callback. Levels 1..iLevel store delta clauses;
// level iLevel+1 stores clauses proved at infinity. A zero deadline is unlimited.
typedef struct Pdr2_Frame_t_ Pdr2_Frame_t;
struct Pdr2_Man_t_;
struct Pdr2_Frame_t_
{
    Aig_Man_t *          pAig;
    int                  iLevel;
    abctime              TimeStop;
    struct Pdr2_Man_t_ * pMan;      // private to the PDR2 accessors
};
// Append candidates to the supplied vector. Return one if blocking closed a frame.
typedef int (*Pdr2_FrameHintFunc)( const Pdr2_Frame_t *, Vec_Wec_t *, void * );

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// pdr2Core.c
extern void               Pdr2_ManSetDefaultParams( Pdr2_Par_t * pPars );
extern int                Pdr2_ManSolve( Aig_Man_t * p, Pdr2_Par_t * pPars );
extern int                Pdr2_ManSolveAbstraction( Aig_Man_t * p, Pdr2_Par_t * pPars );
extern int                Pdr2_ManSolveInit( Aig_Man_t * p, Vec_Int_t * vInit, Pdr2_Par_t * pPars );
extern int                Pdr2_ManSolveHints( Aig_Man_t * pAig, Vec_Wec_t * vCubes, abctime TimeStop,
                              int (*pFuncStop)(int), int * piFrame, int fVerbose );
extern int                Pdr2_ManSolveFrameHints( Aig_Man_t * pAig, Vec_Wec_t * vCubes, abctime TimeStop,
                              int (*pFuncStop)(int), int * piFrame, int fVerbose, Pdr2_FrameHintFunc pFuncFrame, void * pFrameData );
extern int                Pdr2_FrameIsStopped( const Pdr2_Frame_t * pFrame );
// Returns the cube size, or -1 at the end. Removed entries have NULL literals.
// The borrowed literals remain valid until the next blocking call.
extern int                Pdr2_FrameReadCube( const Pdr2_Frame_t * pFrame, int iLevel, int iCube, const int ** ppLits );
// On success vCube contains the generalized cube and pfClosed reports convergence.
extern int                Pdr2_FrameBlockCube( const Pdr2_Frame_t * pFrame, int iLevel, Vec_Int_t * vCube,
                              int nConfLimit, abctime TimeStop, int * pfClosed );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
