/**CFile****************************************************************

  FileName    [pdr2Int.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Internal declarations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2Int.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__proof__pdr2__pdr2Int_h
#define ABC__proof__pdr2__pdr2Int_h

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "aig/saig/saig.h"
#include "sat/cnf/cnf.h"
#include "misc/vec/vec.h"
#include "misc/util/utilTruth.h"
#include "proof/pdr/gipsat/gipsat.h"
#include "pdr2.h"

ABC_NAMESPACE_HEADER_START

// nominal solver speed: the time slices of the alternating runs are measured in propagations
// (a deterministic unit of work), with this many per nominal second
#define PDR2_PROPS_PER_SEC  12000000.0
#define PDR2_SOLVER_UNRESTRICTED  3
static inline double Pdr2_ManPropUnit( Pdr2_Par_t * pPars ) { return pPars->nPropUnit > 0 ? (double)pPars->nPropUnit : PDR2_PROPS_PER_SEC; }

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

// literal conventions:
//   flop literal  = Abc_Var2Lit( flopIndex, fCompl )    (cubes, lemmas, activity)
//   PI literal    = Abc_Var2Lit( piIndex, fCompl )      (counterexample inputs)
//   GipSAT literal = Abc_Var2Lit( SAT variable, fCompl ) (solver assumptions/clauses)
//   SAT variables are AIG object IDs or the context's compact variable numbers.

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pdr2_Cube_t_ Pdr2_Cube_t;
typedef struct Pdr2_Obl_t_  Pdr2_Obl_t;
typedef struct Pdr2_Lem_t_  Pdr2_Lem_t;
typedef struct Pdr2_Man_t_  Pdr2_Man_t;

// immutable sorted cube of flop literals with a 64-bit literal signature
struct Pdr2_Cube_t_
{
    int           nRefs;
    int           nLits;
    word          Sign;
    int           Lits[1];    // trailing storage is extended by Pdr2_CubeAlloc
};

// proof obligation
struct Pdr2_Obl_t_
{
    int           Stamp;     // insertion number in the queue (newest first in treb's order)
    int           nRefs;
    int           iFrame;
    int           nDepth;    // number of steps to the bad state
    int           iPos;      // position in the queue heap (-1 = not queued)
    unsigned      Id;        // creation number (tie break)
    double        Act;       // how many times it was processed (decays when pushed)
    Pdr2_Cube_t * pState;    // state cube (flop literals)
    Vec_Int_t *   vInputs;   // PI literals of the model (for counterexamples)
    Vec_Int_t *   vPpis;     // literals of abstracted flops dropped from the state (pseudo-inputs)
    Pdr2_Obl_t *  pNext;     // the obligation this one leads to (towards the bad state)
};

// lemma stored in a frame
struct Pdr2_Lem_t_
{
    Pdr2_Cube_t * pCube;     // blocked cube
    Pdr2_Obl_t *  pObl;      // obligation it was derived from (may be NULL)
    int           fRemoved;  // no longer in its frame
    int           iFrame;    // frame of the lemma (-1 = infinity)
    int           iSlot;     // position in its frame vector (a hint, checked before use)
    // cached counterexamples to propagation (slots in the CTI pool, -1 = none):
    // a state of the lemma's frame (resp. of the inf lemmas) with a transition into the cube
    int           iCti;
    int           iCtiInf;
    int           Id;        // index into the manager's table of current frames (shared with the solvers)
};

// generalization parameters (rIC3's DropVarParameter)
typedef struct Pdr2_MicPar_t_
{
    int           nLimit;    // CTG blocking effort
    int           nMax;      // max CTGs per literal
    int           nLevel;    // 1 = ctg_down, 0 = plain down
} Pdr2_MicPar_t;

// A transition-only implication: the CI core implies all target literals.
// Targets precede the core in Lits. No frame lemma is used in this proof.
typedef struct Pdr2_LiftMemo_t_
{
    int nKey, nCore;
    int Lits[1];
} Pdr2_LiftMemo_t;
// the query kinds of the mask PDR2_JFTR_SCOPE: bit (1 << PDR2_JQ_*) selects a kind (default 63 = all)
enum {
    PDR2_JQ_BAD = 0,           //  1: the bad-state query
    PDR2_JQ_BLOCK,             //  2: the query that blocks a proof obligation
    PDR2_JQ_MIC,               //  4: the generalization queries
    PDR2_JQ_PUSH,              //  8: the push of a new lemma
    PDR2_JQ_PROP,              // 16: the propagation query
    PDR2_JQ_INF                // 32: promotion and propagation to infinity
};

struct Pdr2_Man_t_
{
    // input data
    Pdr2_Par_t *  pPars;
    Aig_Man_t *   pAig;
    int           nRegs;
    int           nPis;
    char *        pInit;         // per flop: the initial value, 0, 1 or 2 (don't-care)
    char *        pInitState;    // per flop: scratch for an initial state (Pdr2_ManInitState)
    // solver infrastructure
    Cnf_Man_t *   pCnfMan;
    Gip_Ctx_t *   pCtx;
    Vec_Ptr_t *   vSolvers;      // Gip_Solver_t *, one per frame
    Gip_Solver_t * pInf;         // solver with the inf lemmas
    Gip_Solver_t * pLift;        // solver for predecessor lifting
    Gip_Solver_t * pInitSat;     // independent initial-predicate intersection queries
    Gip_Solver_t * pBadRoot;     // private solver restricted to bad states
    Gip_Solver_t * pBadBase;     // frame solver whose clauses it mirrors
    int           nBadRootMode, iBadRootFrame, nBadRootBuilds;
    Vec_Int_t *   vInitAssump;
    int           fInitUnknown, fInitEmpty;
    ABC_INT64_T   nInitQueries;
    Gip_Solver_t * pShared;      // optional single solver for finite frames 1..nSharedSlots-1
    Vec_Int_t *   vSharedLemFrame; // greatest frame of each lemma already inserted into pShared
    Vec_Int_t *   vSharedAssump; // query assumptions plus the frame activation literal
    Vec_Int_t *   vSharedSeeds;  // optional domain rebuilt from the queried frame's active lemmas
    int           nSharedMode;  // 1 = original, 2 = pin guards, 3 = local domain, 4 = separate frontier
    int           nSharedSlots; // reserved activation variables; 0 disables sharing
    int           iSharedBase;  // first reserved SAT variable
    word *        pReachStates; // sampled reachable states, [flop][depth], 64 traces per word
    word *        pReachInputs; // recorded inputs for optional trace splicing
    Abc_Cex_t *   pReachCex;    // concrete, independently validated counterexample
    int           fReachFilter;
    int           fReachCex;
    ABC_INT64_T   nReachCexChecks;
    ABC_INT64_T   nReachCexMatches;
    ABC_INT64_T   nReachCexRejected;
    int           nReachStride;
    int           nReachFrames;
    int           fReachReady;
    ABC_INT64_T   nReachChecks;
    ABC_INT64_T   nReachReject;
    abctime       timeReach;
    int *         pLoVar;        // flop -> GipSAT var of the register output
    int *         pLiLit;        // flop -> GipSAT literal of the register input
    int *         pPiVar;        // PI -> GipSAT var
    int *         pVar2Ci;       // optional SAT var -> CI index (PIs, then latches), -1 otherwise
    Vec_Int_t *   vLiftCis;      // sparse lifting candidates, sorted by CI index
    int           nLiftMemoMode; // 1 = measure, 2 = reuse for CTGs, 3 = reuse all
    int           nLiftPiMode;   // 1 = target-cone inputs, 2 = UNSAT-core inputs
    ABC_INT64_T   nLiftPiBefore, nLiftPiAfter;
    int           nCnfJustMode;  // 1 = then SAT core, 2 = justification alone, 3 = only for an input-first model
    int           nInputScope;   // input-first query mask: bad, blocking, other relative, lifting, containment
    int           nJftrScope;    // jftr query mask: bad, blocking, generalization, push, propagation, infinity
    int           nInputBadLimit; // optional input-first conflict limit for bad-state queries only
    int           fInputBlockQuery;
    char *        pCnfJustMark;
    Vec_Int_t *   vCnfJustWork;
    ABC_INT64_T   nCnfJustHits, nCnfJustFails, nCnfJustNodes;
    abctime       timeCnfJust;
    int           nBadPhaseConfs, fBadPhaseProbe, nBadRephases;
    Pdr2_LiftMemo_t ** pLiftMemo; // 256 buckets of 16 bounded entries
    unsigned char * pLiftMemoNext;
    Vec_Int_t *   vLiftMemoKey;
    Vec_Int_t *   vLiftMemoCore;
    ABC_INT64_T   nLiftMemoBytes;
    ABC_INT64_T   nLiftMemoChecks, nLiftMemoHits, nLiftMemoWeakHits;
    ABC_INT64_T   nLiftMemoReuse, nLiftMemoStores;
    int           nMicCexMode;  // 1 = count opportunities, 2 = reject witnessed failed drops
    word *        pMicCexBits;  // per flop: source value/mask and successor value/mask, 128 slots
    word          MicCexLive[2];
    int           MicCexFrame[128];
    unsigned      iMicCexNext;
    ABC_INT64_T   nMicCexChecks, nMicCexHits, nMicCexStores, nMicCexKilled;
    int           nPredictMode; // 1 = parent prediction before MIC, 2 = also skip MIC on success
    int           GuardLit;       // register literal required along bad traces, -1 when unused
    int           GuardLo, GuardLi;  // corresponding current and next SAT literals, -1 when unused
    int           nStrengthenOnDemand;
    ABC_INT64_T   nStrengthenTrials, nStrengthenAvoided;
    int           nDropHistory;
    unsigned char * pDropHistory; // attempts and successes per signed literal and context
    ABC_INT64_T   nDropHistorySkipped;
    int           nJoinPush;
    int           nResolveLimit;    // recent opposite-literal occurrences examined per pivot
    ABC_INT64_T   nResolveCubes, nResolveLits;
    ABC_INT64_T   nJoinTries, nJoinProofs, nJoinLocal, nJoinQueries;
    int           nMicGroup;    // use grouped relative-induction queries for top-level MIC
    ABC_INT64_T   nGroupQueries, nGroupLits, nGroupLevels;
    int           nMicGap;      // skip literal dropping this far below the frontier
    int           nGenTimeMode; // reuse the blocking proof's frame before generalization
    ABC_INT64_T   nMicGapSkipped, nGenTimeJumps, nGenTimeInf;
    int           nKindTime, nKindNext, nKindMax, nKindCalls, fKindProved;
    abctime       timeKind;
    int           nHintTime, nHintNext, nHintCalls;
    abctime       timeHint;
    ABC_INT64_T   nPredictCalls, nPredictQueries, nPredictProved, nPredictSaved;
    abctime       timePredict;
    int           VarBad;        // GipSAT var of the property output
    // frames and lemmas
    Vec_Ptr_t *   vFrames;       // Vec_Ptr_t * of Pdr2_Lem_t *, one per frame
    Vec_Ptr_t *   vInf;          // Pdr2_Lem_t * at frame infinity
    Vec_Ptr_t *   vGarbage;      // removed lemma records, freed at safe points
    Vec_Ptr_t *   vMicScratch;   // per MIC recursion depth: zeroed flags over the literals (keep, mark)
    int           nMicDepth;     // current MIC recursion depth
    Vec_Ptr_t *   pWatch;        // per flop literal: lemmas watching it (frames >= 1 and infinity)
    Vec_Ptr_t *   pOcc;          // per flop literal: lemmas containing it (the buffers of both are allocated by the first push)
    int           iEarly;        // lowest frame changed since the last propagation
    Vec_Ptr_t *   vLog;          // Pdr2_Cube_t *: every lemma ever added, in order
    Vec_Int_t *   vLogFrame;     // frame of each logged lemma (-1 = infinity)
    // pool of cached counterexamples to propagation, bit-parallel over the slots:
    // row of a flop = its values (and known-mask) in all cached states
    word *        pCtiVal;       // [nRegs][nCtiCap/64]
    word *        pCtiMask;      // [nRegs][nCtiCap/64]
    word *        pCtiLive;      // [nCtiCap/64]: slot holds a valid state
    int           nCtiCap;       // slots allocated (multiple of 64)
    int           nCtiUsed;      // high-water mark of slots handed out
    Vec_Int_t *   vCtiFree;      // free slots
    Pdr2_Lem_t ** pCtiLem;       // slot -> lemma
    int *         pCtiFrame;     // slot -> frame of the state (-1 = inf lemmas)
    ABC_INT64_T   nCtiKilled;
    // proof obligations
    Vec_Ptr_t *   vQueue;        // binary heap of Pdr2_Obl_t *
    unsigned      nOblIds;
    Pdr2_Obl_t *  pCexObl;       // the obligation that reached the initial states
    // abstraction
    char *        pAbs;          // per flop: 1 if in the abstraction
    char *        pAbsUsed;      // per flop: scratch
    char *        pAbsVals;      // simulation values (2 x number of objects)
    int           nAbsFlops;
    int           nAbsCexes;
    int           nAbsRefined;
    int           nAbsCleaned;
    int           nAbsXsimRefs;  // refinements by ternary simulation (the others by justification)
    int           nAbsFixups;    // flops added to keep projected cubes non-initial
    int           nAbsStale;     // obligation chains discarded because a fixup changed the abstraction
    int           nAbsCut;       // counterexample checks canceled by the deadline
    int           fAbsActive;    // the abstraction is in use
    int           fExhausted;    // the frame limit was reached: the run cannot continue
    int           fStarted;      // the frame sequence was created
    int           fAlternate;    // this plain run can yield early to the portfolio on an obligation explosion
    int           nInfExported;  // inf lemmas already passed to the other manager
    abctime       timeGlobal;    // overall deadline (0 = none)
    int           nOblsLevel;    // obligations handled at the current level
    int           nOblsLevelMax; // max over the previous levels
    ABC_INT64_T   nProps;        // solver propagations (all queries)
    ABC_INT64_T   nConflicts;    // solver conflicts (all queries)
    ABC_INT64_T   nCleanL;       // learnt-clause cleanups in the solvers (all queries)
    ABC_INT64_T   nCleanLNone;   // learnt-clause cleanups that removed no clause
    ABC_INT64_T   nPropsLevelStart; // propagation count at the start of the current level
    ABC_INT64_T   nPropsRestartStart; // propagation count at the last restart of the level (or its start)
    ABC_INT64_T   propLimit;     // end of the current time slice in propagations (0 = none)
    ABC_INT64_T   propSlice;     // size of the current slice in propagations (grace for the obligation in progress)
    abctime       timeSlice;     // optional wall-time slice boundary, checked between obligations
    abctime       timeSliceHard; // one more slice of grace before an unfinished query is canceled
    int           fQueryCut;     // a query of the current slice was canceled by a resource limit
    int           iStage;        // 0 = blocking, 1 = finite propagation pending, 2 = propagation to infinity pending
    int           fSweepCut;     // a propagation sweep was cut by an undecided query
    Vec_Int_t *   vLemFrame;     // lemma id -> current frame (GIP_FRAME_INF for invariants); read by the solvers
    int           IdInit;        // id of the initial-state units (frame 0)
    int           IdProp;        // id of the property units (frame = last completed frame)
    int           IdInf;         // id with frame infinity
    int           iCoreFrame;    // after an UNSAT query: the lowest frame its proof used (GIP_FRAME_INF = none)
    int           fPushInf;      // the last push found the lemma inductive relative to the invariants alone
    int           fTimeGenCheck; // verify every time-generalization jump with a query (debugging)
    ABC_INT64_T   nTgJumps;      // time generalization: pushes that skipped frames
    ABC_INT64_T   nTgFrames;     // frames skipped
    ABC_INT64_T   nTgInf;        // lemmas placed in frame infinity directly
    ABC_INT64_T   nTgChecks;     // verification queries (debugging)
    ABC_INT64_T   nTgFailed;     // verification failures (debugging)
    ABC_INT64_T   nTgUndecided;  // verification queries canceled by the deadline (debugging)
    ABC_INT64_T   nIdChecks;     // checks that no two live lemmas share an id (debugging)
    ABC_INT64_T   nIdShared;     // ids found shared by two live lemmas (debugging)
    ABC_INT64_T   nIdFresh;      // derived lemmas given a new id because their source stays live
    double        LevelRestartBudget; // propagations at the current level before a restart
    int           nLevelRestarts;// obligation queues restarted because a level took too long
    ABC_INT64_T   nLemmasLevel;  // lemma count at the start of the current level
    int           iResetFlop;    // the reset flop added by the gating transformation (-1 = none)
    abctime       timeAbs;
    // activity
    double *      pAct;          // per flop
    double        ActInc;
    // the last SAT query (for lifting)
    Gip_Solver_t * pLastSolver;
    Vec_Int_t *   vLastAssump;   // GipSAT assumption literals of the last query
    Vec_Int_t *   vRelInd;       // flop literals of the last relative induction query (in order)
    // scratch
    Vec_Int_t *   vLits4;
    Vec_Int_t *   vAssump;       // GipSAT assumptions of a relative query
    Vec_Int_t *   vCst1;         // GipSAT constraint clause (negated cube)
    Vec_Int_t *   vCst2;         // GipSAT constraint clause (extra)
    Vec_Int_t *   vLem;          // GipSAT lemma clause
    Vec_Int_t *   vLift1;        // GipSAT input literals for lifting
    Vec_Int_t *   vLift2;        // GipSAT assumptions for lifting
    Vec_Int_t *   vLift3;        // GipSAT lifting clause
    char *        pLitMark;      // per flop literal
    char *        pVarMark;      // per GipSAT var
    unsigned      RandState;
    // statistics
    abctime       timeStart;
    abctime       timeLimit;
    abctime       timeBlocked;
    abctime       timeGetPred;
    abctime       timeLift;      // all liftings (obligations, CTGs, propagation), wherever they are counted
    abctime       timeLiftSim;   // the weakening by simulation inside the liftings
    int           nMicNest;      // nesting of MIC calls (a CTG generalized inside a down): the time is counted once
    abctime       timeRun;       // time spent inside this manager (the alternating runs share the clock)
    abctime       timeMic;
    abctime       timePush;
    abctime       timeGetBad;
    abctime       timeProp;
    abctime       timePropInf;
    abctime       timeCleanL;    // learnt-clause cleanups (inside the query times)
    ABC_INT64_T   nSolves;
    ABC_INT64_T   nWarmCopied;   // invariant-safe SAT facts/clauses copied into new frames
    ABC_INT64_T   nSparseScans;  // lifting scans replaced with a smaller trail/domain scan
    ABC_INT64_T   nMics;
    int *         pSimInitBound; // last frame retaining each initial bit in a ternary reachable-state envelope
    int           nSimInitSteps;
    ABC_INT64_T   nSimInitSeeds;
    abctime       timeSimInit;
    char *        pPhaseSimState;
    char *        pPhaseSimValues;
    int           nPhaseSimFrame;
    int           nPhaseSimSeeds;
    abctime       timePhaseSim;
    ABC_INT64_T   nMicLits;
    ABC_INT64_T   nMicDropOk;
    ABC_INT64_T   nMicDropFail;
    ABC_INT64_T   nMicEarlyStop;
    ABC_INT64_T   nDowns;
    ABC_INT64_T   nDownQueries;  // SAT queries of the plain downs
    ABC_INT64_T   nDownRetries, nDownStopped;
    int           nDropConfLimit; // conflict allowance per optional minimization query
    ABC_INT64_T   nDropConfCuts;  // literal-drop trials that exhausted their conflict allowance
    int           nDownMode;      // optional budget for joins after the first counterexample
    ABC_INT64_T   nDownCacheHits;
    ABC_INT64_T   nCtgBypassed;
    ABC_INT64_T   nSolverClones;
    abctime       timeSolverClone;
    ABC_INT64_T   nSatDecisions;
    ABC_INT64_T   nJustTested;
    ABC_INT64_T   nJustSkipped;
    ABC_INT64_T   nWatchLists;
    ABC_INT64_T   nWatchSkipped;
    int           nQueryCuts;    // queries canceled by the overrun limit of the slices
    int           fBlockCut;     // the last slice ended between two obligations of the blocking loop
    ABC_INT64_T   nDownJoined;   // plain downs proved after one or more joins
    ABC_INT64_T   nCtgsBlocked;
    ABC_INT64_T   nObls;
    ABC_INT64_T   nOblLits;
    ABC_INT64_T   nOblsDropped;
    int           nBadDumps;     // diagnostic bad-state query snapshots
    ABC_INT64_T   nPrefixCalls, nPrefixProved, nPrefixSaved;
    ABC_INT64_T   nLemmas;
    ABC_INT64_T   nLemmaLits;
    ABC_INT64_T   nLiftCalls, nLiftCone, nLiftFlip, nLiftCore, nLiftSim, nLiftSimFail, nLiftSimBad, nLiftSimCut;
    ABC_INT64_T   nQueuePushes;  // insertion counter of the obligation queue
    ABC_INT64_T   nInfPromoted;  // lemmas moved to frame infinity right after generalization
    ABC_INT64_T   nInfPromoteCalls;
    ABC_INT64_T   nInfPromotedTg; // lemmas moved to frame infinity by time generalization
    char *        pLiftVals;    // simulation values of one frame for the weakening by simulation
    char *        pLiftMark;    // marks of the targets (1) and of the justified objects (2)
    char *        pLiftPi;      // marks of the assigned inputs
    int *         pLiftTrav;    // traversal ids: the objects in the cone of the targets of the current call
    int           nLiftTrav;
    Vec_Int_t *   vLiftCone;    // the cone of the targets in topological order
    Vec_Int_t *   vLiftUndo;
    Vec_Int_t *   vLiftWork;
    Vec_Int_t *   vLiftJust;
    Vec_Int_t *   vLiftVisit;
    ABC_INT64_T   nInfLemmas;
    ABC_INT64_T   nPropCalls;
    ABC_INT64_T   nCtpCalls;     // counterexamples to propagation considered for blocking
    ABC_INT64_T   nCtpBlocked;   // counterexamples blocked at the preceding frame
    ABC_INT64_T   nCtpPushed;    // propagation queries proved after blocking a counterexample
    ABC_INT64_T   nPropSkipped;
    ABC_INT64_T   nPropInfCalls;
    ABC_INT64_T   nPropInfSkipped;
    ABC_INT64_T   nSemContained;
    struct Pdr2_BadSat_t_ * pBadSat; // mapped property solver owned by this manager
    int           fReuseBadSat;      // an expensive bad-state query triggered reuse
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int          Pdr2_ManFrameNum( Pdr2_Man_t * p )             { return Vec_PtrSize(p->vFrames);                             }
static inline int          Pdr2_ManLevel( Pdr2_Man_t * p )                { return Vec_PtrSize(p->vFrames) - 1;                         }
static inline Vec_Ptr_t *  Pdr2_ManFrame( Pdr2_Man_t * p, int k )         { return (Vec_Ptr_t *)Vec_PtrEntry( p->vFrames, k );          }
static inline Gip_Solver_t * Pdr2_ManSolver( Pdr2_Man_t * p, int k )      { return (Gip_Solver_t *)Vec_PtrEntry( p->vSolvers, k );      }
static inline int          Pdr2_LitLo( Pdr2_Man_t * p, int Lit )          { return Abc_Var2Lit( p->pLoVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit) ); }
static inline int          Pdr2_LitLi( Pdr2_Man_t * p, int Lit )          { return p->pLiLit[Abc_Lit2Var(Lit)] ^ Abc_LitIsCompl(Lit); }
static inline word         Pdr2_LitSign( int Lit )                        { return (word)1 << (Lit & 63);                               }
// value of a flop literal (current state) in a SAT model: GIP_TRUE/GIP_FALSE/GIP_NONE
static inline Gip_Solver_t * Pdr2_SolverActual( Gip_Solver_t * pSat )    { return pSat->pShared ? pSat->pShared : pSat; }
static inline int          Pdr2_SolverValue( Gip_Solver_t * pSat, int v ) { return Pdr2_SolverActual(pSat)->pValue[v]; }
static inline int          Pdr2_SolverFlip( Gip_Solver_t * pSat, int v ) { return Gip_SolverFlipToNone(Pdr2_SolverActual(pSat), v); }
// the value of a register in the last model; where an early answer left it unassigned, its value in the completion
static inline int          Pdr2_SolverCompletedValue( Gip_Solver_t * pSat, int Var )
{
    Gip_Solver_t * pAct = Pdr2_SolverActual( pSat );
    int Value = pAct->pValue[Var];
    if ( Value == GIP_NONE && pAct->Jftr.fEarly && pAct->pCtx->pLoIdx[Var] >= 0 )
        Value = Gip_SolverCompletionValue( pAct, Var );
    return Value;
}
static inline int          Pdr2_ManLitValue( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Lit )
{
    Gip_Solver_t * pAct = Pdr2_SolverActual( pSat );
    int LitLo = Pdr2_LitLo( p, Lit ), Value;
    if ( !pAct->Jftr.fEarly )
        return Gip_SolverLitValue( pAct, LitLo );
    Value = Pdr2_SolverCompletedValue( pAct, Gip_LitVar(LitLo) );
    return Value == GIP_NONE ? GIP_NONE : (Value == GIP_TRUE) ^ Gip_LitCompl(LitLo) ? GIP_TRUE : GIP_FALSE;
}
// the jftr request (GIP_JFTR_*) of a query of kind PDR2_JQ_*: none when PDR2_JFTR_SCOPE deselects the kind
static inline int          Pdr2_ManJftrReq( Pdr2_Man_t * p, int Kind, int Request )
{
    return ((p->nJftrScope >> Kind) & 1) ? Request : GIP_JFTR_NONE;
}
// a flop literal excludes the initial states iff its flop has a defined initial value opposite to it
// (a literal of a don't-care flop never does); a cube intersects them iff no literal excludes them
static inline int          Pdr2_ManLitIsNonInit( Pdr2_Man_t * p, int Lit ) { return p->pInit[Abc_Lit2Var(Lit)] == Abc_LitIsCompl(Lit);    }
extern int                Pdr2_ManInitialQuery( Pdr2_Man_t * p, int * pLits, int nLits );
static inline int          Pdr2_CubeIsInit( Pdr2_Man_t * p, Pdr2_Cube_t * pCube ) { int i; for ( i = 0; i < pCube->nLits; i++ ) if ( Pdr2_ManLitIsNonInit(p, pCube->Lits[i]) ) return 0; return !p->pInitSat || Pdr2_ManInitialQuery(p,pCube->Lits,pCube->nLits) != GIP_UNSAT; }
// The global deadline or cancellation (not the slice limit: work that does not count propagations must not
// stop at slice ends, or a resumed run would not follow the trajectory of an uninterrupted one)
static inline int          Pdr2_ManPastDeadline( Pdr2_Man_t * p )         { return p->fInitUnknown || (p->timeLimit && Abc_Clock() > p->timeLimit) || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId)); }
static inline int          Pdr2_LitsAreInit( Pdr2_Man_t * p, Vec_Int_t * vLits ) { int i, Lit; Vec_IntForEachEntry( vLits, Lit, i ) if ( Pdr2_ManLitIsNonInit(p, Lit) ) return 0; return !p->pInitSat || Pdr2_ManInitialQuery(p,Vec_IntArray(vLits),Vec_IntSize(vLits)) != GIP_UNSAT; }

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// pdr2Man.c
extern Pdr2_Man_t *       Pdr2_ManStart( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars );
extern void               Pdr2_ManStop( Pdr2_Man_t * p );
extern Pdr2_Cube_t *      Pdr2_CubeAlloc( int * pLits, int nLits );
extern Pdr2_Cube_t *      Pdr2_CubeAllocVec( Vec_Int_t * vLits );
extern void               Pdr2_CubeRef( Pdr2_Cube_t * p );
extern void               Pdr2_CubeDeref( Pdr2_Cube_t * p );
extern int                Pdr2_CubeSubsume( Pdr2_Cube_t * pA, Pdr2_Cube_t * pB );
extern int                Pdr2_CubeEqual( Pdr2_Cube_t * pA, Pdr2_Cube_t * pB );
extern int                Pdr2_CubeSubsumeMarked( Pdr2_Man_t * p, Pdr2_Cube_t * pA, Pdr2_Cube_t * pB );
extern void               Pdr2_CubeToVec( Pdr2_Cube_t * p, Vec_Int_t * vLits );
extern Pdr2_Obl_t *       Pdr2_OblAlloc( Pdr2_Man_t * p, int iFrame, Pdr2_Cube_t * pState, Vec_Int_t * vInputs, Vec_Int_t * vPpis, int nDepth, Pdr2_Obl_t * pNext );
extern void               Pdr2_OblRef( Pdr2_Obl_t * p );
extern void               Pdr2_OblDeref( Pdr2_Obl_t * p );
extern void               Pdr2_OblPushTo( Pdr2_Obl_t * p, int iFrame );
extern void               Pdr2_QueuePush( Pdr2_Man_t * p, Pdr2_Obl_t * pObl );
extern Pdr2_Obl_t *       Pdr2_QueuePop( Pdr2_Man_t * p, int iFrameMax );
extern int                Pdr2_QueueRemove( Pdr2_Man_t * p, Pdr2_Obl_t * pObl );
extern void               Pdr2_QueueClear( Pdr2_Man_t * p );
extern Pdr2_Lem_t *       Pdr2_LemAlloc( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame );
extern Pdr2_Lem_t *       Pdr2_LemAllocId( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame, int Id );
extern void               Pdr2_LemPush( Vec_Ptr_t * vFrame, Pdr2_Lem_t * pLem );
extern int                Pdr2_LemFind( Vec_Ptr_t * vFrame, Pdr2_Lem_t * pLem );
extern void               Pdr2_ManIndexRebuild( Pdr2_Man_t * p );
extern Pdr2_Lem_t *       Pdr2_ManIndexFindSubsuming( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, int iFrameMin, int iFrameMax, int fInf, int fEqualOnly, int fLowest );
extern void               Pdr2_LemRemove( Pdr2_Man_t * p, Vec_Ptr_t * vFrame, int iPos );
extern void               Pdr2_ManCollectGarbage( Pdr2_Man_t * p, int fForce );
extern void               Pdr2_LemCacheCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, Gip_Solver_t * pSat, int iFrame );
extern void               Pdr2_LemFreeCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, int fInfToo );
extern void               Pdr2_LemInheritInfCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, Pdr2_Lem_t * pFrom );
extern int                Pdr2_LemCtiValid( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, int iFrame );
extern void               Pdr2_ManActBump( Pdr2_Man_t * p, Vec_Int_t * vCube );
extern void               Pdr2_ManSortByAct( Pdr2_Man_t * p, Vec_Int_t * vCube, int fAscending );
extern unsigned           Pdr2_ManRandom( Pdr2_Man_t * p );
extern int                Pdr2_ManRandomBool( Pdr2_Man_t * p, double Prob );
extern void               Pdr2_ManShuffle( Pdr2_Man_t * p, Vec_Int_t * vLits );
extern void               Pdr2_ManShufflePtr( Pdr2_Man_t * p, Vec_Ptr_t * vPtrs );
extern void               Pdr2_ManInitState( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, char * pState );
extern Abc_Cex_t *        Pdr2_ManDeriveCex( Pdr2_Man_t * p );
extern int                Pdr2_ManVerifyInvariant( Pdr2_Man_t * p );
extern int                Pdr2_ManDumpInvariant( Pdr2_Man_t * p, int fTransformed );
extern void               Pdr2_ManPrintProgress( Pdr2_Man_t * p, int fForce );
extern void               Pdr2_ManPrintStats( Pdr2_Man_t * p );
extern int                Pdr2_ManTimedOut( Pdr2_Man_t * p );
extern int                Pdr2_ManReachContains( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube );
extern int                Pdr2_ManReachTryCex( Pdr2_Man_t * p, Pdr2_Obl_t * pObl );
// pdr2Sat.c
extern Gip_Solver_t *     Pdr2_ManNewSolver( Pdr2_Man_t * p, int k );
extern void               Pdr2_ManSolverAddLemma( Pdr2_Man_t * p, Gip_Solver_t * pSat, Pdr2_Cube_t * pCube, int Id );
extern int                Pdr2_ManSolveRelative( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls );
extern int                Pdr2_ManTryDrop( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls );
extern int                Pdr2_ManSolveRelativeJftr( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls, int Request );
extern int                Pdr2_ManTryDropJftr( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls, int Request );
extern int                Pdr2_ManSolveBad( Pdr2_Man_t * p );
extern int                Pdr2_ManSolveContained( Pdr2_Man_t * p, Gip_Solver_t * pSat, Pdr2_Cube_t * pCube );
extern int                Pdr2_ManInductiveCore( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCore );
extern void               Pdr2_ManGetPred( Pdr2_Man_t * p, int fStrengthen, Vec_Int_t * vCube, Vec_Int_t * vInputs );
extern void               Pdr2_ManMicCexStore( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Frame );
extern void               Pdr2_ManShareCompleted( Pdr2_Man_t * p, int Frame );
extern int                Pdr2_ManMicCexFind( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube, char * pKeep );
extern int                Pdr2_ManWindowBmc( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Seconds, int nGroup );
extern Aig_Man_t *        Pdr2_ManDupCoi( Aig_Man_t * pAig, Vec_Int_t ** pvPis, Vec_Int_t ** pvRegs );
extern Aig_Man_t *        Pdr2_ManDupResetCoi( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars, abctime Stop, Vec_Int_t ** pvPis, Vec_Int_t ** pvRegs );
extern int                Pdr2_ManSolveTail( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Depth );
extern int                Pdr2_ManSolveInputLatches( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars );
extern int                Pdr2_ManLogicLeaves( Aig_Man_t * pAig, Aig_Obj_t * pRoot, int fOr, int Limit, Vec_Ptr_t * vLeaves );
extern int                Pdr2_ManSolveMutex( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Minimum );
extern int                Pdr2_ManCombSafe( Aig_Man_t * pAig, Pdr2_Par_t * pPars, abctime timeGlobal, Aig_Man_t * pTraceAig, Vec_Int_t * vInit );
extern int                Pdr2_ManMappedBad( Pdr2_Man_t * p, int Seconds, Vec_Int_t * vModel );
extern void               Pdr2_ManStopBadSat( Pdr2_Man_t * p );
extern int                Pdr2_ManMappedInvariant( Pdr2_Man_t * p, Aig_Man_t * pMiter );
extern void               Pdr2_ManSeedProjection( Pdr2_Man_t * p, int Width );
extern int                Pdr2_ManProjectedComb( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, abctime Stop, int Width );
extern int                Pdr2_ManSampleProperty( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Width );
extern int                Pdr2_ManSolveGla( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Layers );
extern int                Pdr2_ManFirstBad( Aig_Man_t * pAig, Abc_Cex_t * pCex );
extern int                Pdr2_ManFindGuard( Aig_Man_t * pAig, int fNext );
extern void               Pdr2_ManSetMicDomain( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube );
extern void               Pdr2_ManSolverAddUnit( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Lit );
extern void               Pdr2_ManUnsetMicDomain( Pdr2_Man_t * p, Gip_Solver_t * pSat );
// pdr2Abs.c
extern void               Pdr2_ManSimWeaken( Pdr2_Man_t * p, Vec_Int_t * vCube, Vec_Int_t * vInputs );
extern void               Pdr2_ManAbsProject( Pdr2_Man_t * p, Vec_Int_t * vCube, Vec_Int_t * vPpis );
extern void               Pdr2_ManAbsCleanup( Pdr2_Man_t * p );
extern void               Pdr2_ManAbsStart( Pdr2_Man_t * p );
extern Aig_Man_t *        Pdr2_ManDupGatedInit( Aig_Man_t * pAig, char * pInit, char ** ppInitNew );
extern int                Pdr2_ManAbsCheckCex( Pdr2_Man_t * p, Pdr2_Obl_t * pObl );
// pdr2Core.c
extern int                Pdr2_ManSolveInt( Pdr2_Man_t * p );
extern int                Pdr2_ManHasMuxReduction( Aig_Man_t * pAig, Pdr2_Par_t * pPars, abctime Stop );
// pdr2Policy.c
extern void               Pdr2_ManPrintFeatures( Aig_Man_t * pAig );
extern void               Pdr2_ManPrintPolicy( Aig_Man_t * pAig, Vec_Int_t * vInit, int fTuned );
extern void               Pdr2_ManPrintPolicyParams( Pdr2_Par_t * pPars );
extern int                Pdr2_ManCheckedProbe( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int fStride );
extern int                Pdr2_ManSolvePolicy( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
