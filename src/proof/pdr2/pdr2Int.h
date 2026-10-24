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
static inline double Pdr2_ManPropUnit( Pdr2_Par_t * pPars ) { return pPars->nPropUnit > 0 ? (double)pPars->nPropUnit : PDR2_PROPS_PER_SEC; }

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

// literal conventions:
//   flop literal  = Abc_Var2Lit( flopIndex, fCompl )    (cubes, lemmas, activity)
//   PI literal    = Abc_Var2Lit( piIndex, fCompl )      (counterexample inputs)
//   GipSAT literal = Abc_Var2Lit( objectId, fCompl )    (solver assumptions/clauses)

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
    int *         pLoVar;        // flop -> GipSAT var of the register output
    int *         pLiVar;        // flop -> GipSAT var of the register input
    int *         pPiVar;        // PI -> GipSAT var
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
    ABC_INT64_T   nMics;
    ABC_INT64_T   nMicLits;
    ABC_INT64_T   nMicDropOk;
    ABC_INT64_T   nMicDropFail;
    ABC_INT64_T   nDowns;
    ABC_INT64_T   nDownQueries;  // SAT queries of the plain downs
    int           nQueryCuts;    // queries canceled by the overrun limit of the slices
    int           fBlockCut;     // the last slice ended between two obligations of the blocking loop
    ABC_INT64_T   nDownJoined;   // plain downs proved after one or more joins
    ABC_INT64_T   nCtgsBlocked;
    ABC_INT64_T   nObls;
    ABC_INT64_T   nOblLits;
    ABC_INT64_T   nOblsDropped;
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
    ABC_INT64_T   nPropSkipped;
    ABC_INT64_T   nPropInfCalls;
    ABC_INT64_T   nPropInfSkipped;
    ABC_INT64_T   nSemContained;
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

static inline int          Pdr2_ManFrameNum( Pdr2_Man_t * p )             { return Vec_PtrSize(p->vFrames);                             }
static inline int          Pdr2_ManLevel( Pdr2_Man_t * p )                { return Vec_PtrSize(p->vFrames) - 1;                         }
static inline Vec_Ptr_t *  Pdr2_ManFrame( Pdr2_Man_t * p, int k )         { return (Vec_Ptr_t *)Vec_PtrEntry( p->vFrames, k );          }
static inline Gip_Solver_t * Pdr2_ManSolver( Pdr2_Man_t * p, int k )      { return (Gip_Solver_t *)Vec_PtrEntry( p->vSolvers, k );      }
static inline int          Pdr2_LitLo( Pdr2_Man_t * p, int Lit )          { return Abc_Var2Lit( p->pLoVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit) ); }
static inline int          Pdr2_LitLi( Pdr2_Man_t * p, int Lit )          { return Abc_Var2Lit( p->pLiVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit) ); }
static inline word         Pdr2_LitSign( int Lit )                        { return (word)1 << (Lit & 63);                               }
// value of a flop literal (current state) in a SAT model: GIP_TRUE/GIP_FALSE/GIP_NONE
static inline int          Pdr2_ManLitValue( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Lit ) { return Gip_SolverLitValue( pSat, Pdr2_LitLo(p, Lit) ); }
// a flop literal excludes the initial states iff its flop has a defined initial value opposite to it
// (a literal of a don't-care flop never does); a cube intersects them iff no literal excludes them
static inline int          Pdr2_ManLitIsNonInit( Pdr2_Man_t * p, int Lit ) { return p->pInit[Abc_Lit2Var(Lit)] == Abc_LitIsCompl(Lit);    }
static inline int          Pdr2_CubeIsInit( Pdr2_Man_t * p, Pdr2_Cube_t * pCube ) { int i; for ( i = 0; i < pCube->nLits; i++ ) if ( Pdr2_ManLitIsNonInit(p, pCube->Lits[i]) ) return 0; return 1; }
// the global deadline only (not the slice limit: work that does not count propagations must not
// stop at slice ends, or a resumed run would not follow the trajectory of an uninterrupted one)
static inline int          Pdr2_ManPastDeadline( Pdr2_Man_t * p )         { return p->timeLimit && Abc_Clock() > p->timeLimit;          }
static inline int          Pdr2_LitsAreInit( Pdr2_Man_t * p, Vec_Int_t * vLits ) { int i, Lit; Vec_IntForEachEntry( vLits, Lit, i ) if ( Pdr2_ManLitIsNonInit(p, Lit) ) return 0; return 1; }

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
// pdr2Sat.c
extern Gip_Solver_t *     Pdr2_ManNewSolver( Pdr2_Man_t * p, int k );
extern void               Pdr2_ManSolverAddLemma( Pdr2_Man_t * p, Gip_Solver_t * pSat, Pdr2_Cube_t * pCube, int Id );
extern int                Pdr2_ManSolveRelative( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls );
extern int                Pdr2_ManSolveBad( Pdr2_Man_t * p );
extern int                Pdr2_ManSolveContained( Pdr2_Man_t * p, Gip_Solver_t * pSat, Pdr2_Cube_t * pCube );
extern int                Pdr2_ManInductiveCore( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCore );
extern void               Pdr2_ManGetPred( Pdr2_Man_t * p, int fStrengthen, Vec_Int_t * vCube, Vec_Int_t * vInputs );
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

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
