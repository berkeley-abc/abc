/**CFile****************************************************************

  FileName    [imcInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Internal declarations.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcInt.h,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__proof__imc__imcInt_h
#define ABC__proof__imc__imcInt_h

#include "imc.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "sat/bsat/satSolver2.h"
#include "sat/cadical/ccadical.h"

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

#define IMC_PRED_MAX 512

typedef struct Imc_Sat_t_ Imc_Sat_t;
typedef struct Imc_Prf_t_ Imc_Prf_t;
struct Imc_Sat_t_
{
    sat_solver *  pSat;     // incremental induction solver
    sat_solver2 * pSat2;    // solver recording resolution chains
    int nVars;             // next unused SAT variable
    int fUnsat;            // contradiction detected while adding clauses
    CCaDiCaL * pCad;       // CaDiCaL image solver
    Imc_Prf_t * pPrf;      // C interpolator for its LRAT refutation
    int fDual;             // resolution labels use the reversed partitions
    Vec_Str_t * vLoaded;   // loaded transition CNF definitions
    Vec_Str_t * vLoadedB;  // loaded prefix CNF definitions
    Vec_Str_t * vShared;   // register interfaces already connected to the prefix
    Vec_Int_t * vMap;      // template variable to allocated SAT variable
    Vec_Int_t * vCapture;  // borrowed normalized-clause cache during suffix encoding
    Gia_Man_t * pCompose;  // persistent hashed transition and composed frontiers
    Vec_Int_t * vComposeVars; // composed node to SAT literal, or -1
    Vec_Int_t * vComposeNext; // next-state literals in pCompose
    FILE * pProof;         // persistent incremental proof stream
    int iGuard;            // activation variable of the current frontier
    int fPending;          // image SAT query suspended at a conflict budget
    int Query[2];          // unchanged assumptions when resuming that query
};

typedef struct Imc_Unr_t_ Imc_Unr_t;
typedef struct Imc_Man_t_ Imc_Man_t;
struct Imc_Man_t_
{
    Gia_Man_t * pGia;       // user's transition system
    Imc_Unr_t * pUnroll;    // persistent mapped bounded-transition chunks
    int fExtendUnroll;      // extend concrete unrollings instead of rebuilding
    Gia_Man_t * pPred;      // combinational predicates of boundary registers
    Gia_Man_t * pInvariant; // independently checked reachable-state restriction
    Imc_Par_t * pPars;      // limits and output statistics
    Aig_Man_t * pAig;       // combinational view of one transition
    Cnf_Dat_t * pCnf;       // mapped CNF, computed once
    Cnf_Dat_t * pCnfB;      // backward reachable prefix or forward bad suffix
    Cnf_Dat_t * pCnfF;      // current frontier, shared by the three encodings
    Vec_Int_t * vFrontVars; // input variables in the frontier CNF
    Vec_Int_t * vFrontUsed; // state inputs used by the current frontier
    Vec_Int_t * vCnfStart; // first defining clause of each transition variable
    Vec_Int_t * vCnfCount; // number of defining clauses
    Vec_Int_t * vSharedUsed; // next-state outputs needed by the forward suffix
    Vec_Int_t * vCnfStartB;// first defining clause of each prefix variable
    Vec_Int_t * vCnfCountB;// number of prefix defining clauses
    Vec_Int_t * vPrefix;   // prefix state variables, ordered by frame and register
    Vec_Int_t * vResets;   // optional initial-state resets in the bounded prefix
    int iFront;            // frontier output variable
    Vec_Int_t * vMapB;     // suffix CNF variable to template variable key
    Vec_Int_t * vSuffixClauses; // normalized forward suffix clauses, length-prefixed
    Vec_Int_t * vSuffixMap; // template map after allocating the cached suffix
    int nSuffixStart;      // SAT variable count before the cached suffix
    int nSuffixVars;       // SAT variable count after the cached suffix
    unsigned nSuffixGeneration; // transition unrolling identity
    unsigned nCachedGeneration; // unrolling used by the normalized cache
    Vec_Int_t * vImagePis; // template input keys by frame; translate through Image.vMap
    Vec_Int_t * vImageBad; // forward bad keys or backward prefix activation variables
    Vec_Int_t * vPis;       // input variables in the transition CNF
    Vec_Int_t * vRos;       // current-state variables
    Vec_Int_t * vRis;       // next-state variables (interpolation interface)
    int iBad;              // bad-output variable
    Imc_Sat_t Ind;         // persistent solver for the union of frontiers
    Imc_Sat_t Image;       // reusable image solver and its resolution proof
    Vec_Int_t * vStates;  // state variables for combinational containment
    int nImageCalls;       // queries since the last suffix change
    int nRefinements;      // state bits added by batched predicate refinement
    int fRefined;          // restart after an abstract counterexample
    int iUnion;            // positive accumulated frontier union (current state, or next state backward)
    int iPredClass;        // original circuit: 0 generic, 1 recorded state, 2 linear words
    int nHouFiltered;      // candidates rejected by simulation in the last Houdini call
    int nHouBlocked;       // initially unseen guard groups
    int nHouExpanded;      // groups expanded using induction models
    int nHouSatFiltered;   // concrete SAT transitions used by the prefilter
    int nHouCandidates;    // candidates materialized in the last Houdini call
    int nHouConfMax;       // total early-Houdini conflict budget; 0 is unlimited
    int nHouCoreRemoved;    // templates discarded after safety-core dependency closure
    int nHouDemandRefresh; // safety queries after a demanded successor was refuted
    int nHouDemandRetained;// active premises preserved through demand refresh
    int nHouDemandFallback;// refreshes that return to ordinary Houdini
    int nHouDemandExpanded;// blocked guard groups expanded while demand is active
    int nHouMinimized;     // active templates removed by safety-core minimization
    int nQueryConfLimit;   // internal cooperative query budget; 0 means unlimited
    int fIndPending;       // containment/induction query awaiting more conflicts
    int iIndQuery;         // saved assumption of the pending induction query
    word nSatVisits;       // MiniSat watch-list entries inspected by queries
    word nItpNodes;        // raw interpolant nodes processed by DAR
    word nConflicts;       // conflicts spent by image and induction queries
    abctime TimeStop;      // absolute wall-time deadline
    abctime timeSat;       // image SAT queries
    abctime timeItp;       // interpolant construction
    abctime timeInd;       // induction queries
    abctime timeTotal;     // starting monotonic wall clock
};

typedef struct Imc_Search_t_ Imc_Search_t;
struct Imc_Search_t_
{
    Imc_Man_t Man;
    Imc_Par_t Pars;
    Gia_Man_t * pFront, * pReached, * pDelta;
    int nFrames, nImages, iReached;
    int Stage;             // 0: unroll, 1: containment, 2: image
    int fDone;             // terminal result or a non-budget failure
    int fFineFrames, nFrontMax, fCostProbe;
    int nSliceConflicts;   // adaptive allowance for a search with a pending query
    word nSteps;           // completed or suspended SAT queries
};

typedef struct Imc_Sched_t_ Imc_Sched_t;
struct Imc_Sched_t_
{
    int Scores[2];         // recent completed depth/image progress, never wall time
    int Last, nConsecutive;
};

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline void Imc_CexSetBit( unsigned * p, int i ) { p[i >> 5] |= 1u << (i & 31); }
static inline int  Imc_CexHasBit( unsigned * p, int i ) { return (p[i >> 5] >> (i & 31)) & 1u; }

extern int         Imc_ManScheduleNext( Imc_Sched_t * p, int First, int fDone0, int fDone1 );
extern void        Imc_ManScheduleUpdate( Imc_Sched_t * p, int Dir, Imc_Search_t * pSearch, int Frames, int Images, int Front );
extern int         Imc_ManSimulate( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime Budget );
extern int         Imc_ManWalk( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime Budget );
extern int         Imc_ManWalkCached( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime Budget, Aig_Man_t * pAig, Cnf_Dat_t * pCnf );
extern Gia_Man_t * Imc_ManSeqSweep( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart );
extern int Imc_ManSeqSweepAllowed( int nAnds, int nRegs );
extern int Imc_ManSeqSweepUseful( int nAnds, int nRegs, int nNewAnds, int nNewRegs );
extern word        Imc_ManSimInput( int iPi, int iFrame, int iWord, word * pSeed );
extern int         Imc_ManPredicateClass( Gia_Man_t * pGia, int * pfAfterInit );
extern Gia_Man_t * Imc_ManFindPredicates( Gia_Man_t * pGia, abctime TimeStop, int fCoarse, int iPredClass, int fAfterInit );
extern Gia_Man_t * Imc_ManExpandPredicates( Gia_Man_t * pImage, Gia_Man_t * pPred );
extern Gia_Man_t * Imc_ManPredicateInvariant( Imc_Man_t * p, int * pfSafe );
extern int         Imc_SatNewVar( Imc_Sat_t * p, int fPartA );
extern Gia_Man_t * Imc_ManRewriteBdd( Gia_Man_t * p, int nLimit, abctime TimeStop );
extern Gia_Man_t * Imc_ManRewriteSat( Gia_Man_t * p, abctime TimeStop );
extern void        Imc_SatAddClause( Imc_Sat_t * p, int * pLits, int nLits, int fPartA );
extern void        Imc_SatAddCnf( Imc_Sat_t * p, Cnf_Dat_t * pCnf, int Offset, int fPartA );
extern int         Imc_SatAddGia( Imc_Sat_t * p, Gia_Man_t * pGia, Vec_Int_t * vVars, int fPartA );
extern int         Imc_ManCheckInitial( Imc_Man_t * p );
extern int         Imc_ManCheckInvariant( Imc_Man_t * p, Gia_Man_t * pReached );
extern int         Imc_ManCheckInductive( Imc_Man_t * p, Gia_Man_t * pInvariant );
extern void        Imc_ManSetFront( Imc_Man_t * p, Gia_Man_t * pFront );
extern void        Imc_CnfMap( Cnf_Dat_t * pCnf, Vec_Int_t ** pvStart, Vec_Int_t ** pvCount );
extern Abc_Cex_t * Imc_ManReplay( Imc_Man_t * p, Abc_Cex_t * pTrace, int Boundary, Vec_Str_t * vBoundary );
extern void        Imc_ManRefinePredicates( Imc_Man_t * p, Vec_Str_t * vMismatch );
extern int         Imc_ManExtendSuffix( Imc_Man_t * p, int nFrames );
extern void        Imc_ManUnrollStop( Imc_Man_t * p );
extern int         Imc_ManBuildSuffix( Imc_Man_t * p, int nFrames );
extern void        Imc_ManImageStop( Imc_Man_t * p );
extern void        Imc_ManIndStart( Imc_Man_t * p );
extern int         Imc_ManIndCheck( Imc_Man_t * p );
extern int         Imc_ManSearchRun( Imc_Search_t * p, int nQueries, int nConflicts );
extern int         Imc_ManSearchNextFrame( Imc_Search_t * pSearch );
extern int         Imc_ManSearchGrowBudget( int Limit );
extern int         Imc_ManSearchCanContinue( Imc_Search_t * pSearch );
extern int         Imc_ManSearchCompatible( Imc_Search_t * pSearch, Gia_Man_t * pGia, Imc_Par_t * pPars );
extern void        Imc_ManSearchStop( Imc_Search_t * p );
extern Gia_Man_t * Imc_ManImage( Imc_Man_t * p, Gia_Man_t * pFront, int nFrames, int fInitial, int * pStatus );
extern FILE *      Imc_ProofFile( void );
extern int         Imc_ProofSeek( FILE * pFile, ABC_INT64_T Offset, int Origin );
extern ABC_INT64_T  Imc_ProofTell( FILE * pFile );
extern Imc_Prf_t * Imc_PrfStart( Vec_Int_t * vGlobals, int nVarsA, int nVars, int fDual, int fPudlak, int fIncremental );
extern void        Imc_PrfStop( Imc_Prf_t * p );
extern void        Imc_PrfRestart( Imc_Prf_t * p );
extern void        Imc_PrfSetVar( Imc_Prf_t * p, int Var, int fPartA );
extern void        Imc_PrfAssertGlobals( Imc_Prf_t * p, Vec_Int_t * vGlobals );
extern int         Imc_PrfAddRoot( Imc_Prf_t * p, int * pLits, int nLits, int fPartA );
extern Gia_Man_t * Imc_PrfRead( Imc_Prf_t * p, FILE * pFile, int nVars, int fAutoItp, int fMinimize, abctime TimeStop );
extern int         Imc_PrfWasMinimized( Imc_Prf_t * p );
extern Gia_Man_t * Imc_PrfWeaken( Imc_Prf_t * p, Gia_Man_t * pImage, Vec_Int_t * vGlobals, int nVars, int LitB, abctime TimeStop );
extern Gia_Man_t * Imc_PrfReadIncremental( Imc_Prf_t * p, FILE * pFile, int nVars, int LitA, int LitB, abctime TimeStop );
extern Gia_Man_t * Imc_PrfReadSat( Imc_Prf_t * p, sat_solver2 * pSat, abctime TimeStop );
extern int         Imc_PrfCheck( Imc_Prf_t * p, Gia_Man_t * pImage, Vec_Int_t * vGlobals, int nVars, int LitA, int LitB, int nConfLimit, abctime TimeStop );

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
