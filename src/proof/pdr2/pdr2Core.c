/**CFile****************************************************************

  FileName    [pdr2Core.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [The main loop: blocking, generalization, propagation.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2Core.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <limits.h>
#include <math.h>
#include "pdr2Int.h"
#include "proof/ssw/ssw.h"
#include "proof/imc/imc.h"
#include "proof/cec/cec.h"
#include "opt/dar/dar.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satSolver.h"
#include "sat/cadical/ccadical.h"
#include "sat/kissat/kissat.h"
#include "aig/ioa/ioa.h"
#include "aig/gia/giaAig.h"
#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#include "bdd/llb/llb.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define PDR2_BLOCK_SUCCESS   1
#define PDR2_BLOCK_FAILURE   0
#define PDR2_BLOCK_PROVED    2
#define PDR2_BLOCK_TIMEOUT  (-1)
#define PDR2_BLOCK_RESTART  (-2)

static void Pdr2_ManMic( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube, Vec_Int_t * vCst, Pdr2_MicPar_t Par );
static void Pdr2_ManSimSeedFrame( Pdr2_Man_t * p, int Frame );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets the default parameters.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManSetDefaultParams( Pdr2_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Pdr2_Par_t) );
    pPars->timePolicyStop = -1;
    pPars->iSchedule = PDR2_SCHED_TUNED;
    pPars->nFrameMax     =       0;  // limit on frame count
    pPars->nTimeOut      =       0;  // timeout in seconds
    pPars->nRandomSeed   =       0;  // random seed
    pPars->nPropLimit    =       Gip_OptionGet("PDR2_PROP_LIMIT") ? Abc_MaxInt(0, Abc_MinInt(1000000000, atoi(Gip_OptionGet("PDR2_PROP_LIMIT")))) : 0; // deterministic diagnostic work budget
    pPars->fCtg          =       1;  // CTG generalization
    pPars->fDynamic      =       1;  // dynamic CTG effort
    pPars->nDynLimitMax  =       1;  // cap on CTG effort in dynamic mode
    pPars->nDynAct       =      10;  // activity threshold in dynamic mode
    pPars->nDynTime      =       4;  // first budget of the dynamic phases
    pPars->nCtgTime      =      16;  // first budget of the CTG phases
    pPars->fDynFirst     =       0;  // the CTG phase comes first
    pPars->fShareInf     =       0;  // pass invariant lemmas between the two runs (hurt Ex65/Ex67)
    pPars->nDynExplode   =   10000;  // obligations per level that end the dynamic mode
    pPars->nLevelRestart =       0;  // millions of propagations at one level before the obligation queue is restarted
    pPars->fTimeGen      =       Gip_OptionGet("PDR2_TIMEGEN") ? atoi(Gip_OptionGet("PDR2_TIMEGEN")) : 2;  // time generalization
    pPars->fSemContain   =       0;  // semantic containment check
    pPars->fKeepObl      =       1;  // keep obligations beyond the frontier
    pPars->nQueueOrder   =       1;  // treb's order: shortest cube first, newest first
    pPars->nCtgMax       =       3;  // max CTGs per literal
    pPars->nCtgLimit     =       1;
    pPars->fCtgMic       =       1;  // generalize CTG-blocking lemmas
    pPars->fCtgLocal     =       Gip_OptionGet("PDR2_CTGLOCAL") ? atoi(Gip_OptionGet("PDR2_CTGLOCAL")) != 0 : 0;
    pPars->fDropPo       =       1;  // drop failing obligations
    pPars->nDropAct      =      20;  // dropping threshold
    pPars->nDynDropAct   =       0;  // dropping threshold in dynamic mode (0 = never)
    pPars->fParentLemma  =       1;  // parent lemma ordering
    pPars->fLift         =       1;  // flip-to-none lifting
    pPars->fPropHyp      =       1;
    pPars->fBlockInduct  =       0;  // relative induction in the blocking query  // property as inductive hypothesis
    pPars->nPrefix       =       Gip_OptionGet("PDR2_PREFIX") ? Abc_MaxInt(0, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_PREFIX")))) : 0;
    pPars->fCtiCache     =       1;  // cache counterexamples to propagation
    pPars->nCtpMax       =       Gip_OptionGet("PDR2_CTP") ? Abc_MaxInt(0, Abc_MinInt(8, atoi(Gip_OptionGet("PDR2_CTP")))) : 0;
    pPars->fUseAbs       =       0;  // localization abstraction
    pPars->nAbsStart     =       0;  // abstraction start time
    pPars->fAbsCleanup   =       1;  // abstraction cleanup
    pPars->fAbsRefineAll =       0;  // refine with all pseudo-inputs
    pPars->fAbsReset     =       1;  // reset-flop gating with the abstraction
    pPars->fAbsRefineXsim=       1;  // X-simulation refinement
    pPars->nAbsRefineMode=       0;  // refinement variant (see pdr2.h)
    pPars->nAbsRuns      =       2;  // abstraction runs added to the alternating schedule
    pPars->fDynRun       =       Gip_OptionGet("PDR2_DYNRUN") ? atoi(Gip_OptionGet("PDR2_DYNRUN")) : 0;  // plain dynamic run (finished 0 of 76 IWLS and 0 of 111 mike4 examples)
    pPars->fSimRun       =       0;  // weakening by simulation as another alternating run
    pPars->nBmcTime      =       Gip_OptionGet("PDR2_BMC") ? atoi(Gip_OptionGet("PDR2_BMC")) : 2;  // BMC stage after the first slice
    pPars->nAbsTime      =       8;  // first budget of the abstraction phases
    pPars->fTopCtg       =       0;  // CTG for top-level obligations (was unreachable in the measured runs)
    pPars->fInfPromote   =       0;  // immediate promotion to frame infinity
    pPars->nMicMode      =       0;  // generalization procedure
    pPars->nMicFailLimit =       Gip_OptionGet("PDR2_MICFAIL") ? Abc_MaxInt(0, Abc_MinInt(32, atoi(Gip_OptionGet("PDR2_MICFAIL")))) : 0;
    pPars->nDownCacheMode =      Gip_OptionGet("PDR2_DOWNCACHE") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_DOWNCACHE")))) : 0;
    pPars->nCtgSmall =           Gip_OptionGet("PDR2_CTGSMALL") ? Abc_MaxInt(0, Abc_MinInt(64, atoi(Gip_OptionGet("PDR2_CTGSMALL")))) : 0;
    pPars->nCtgMinRate =         Gip_OptionGet("PDR2_CTGRATE") ? Abc_MaxInt(0, Abc_MinInt(100, atoi(Gip_OptionGet("PDR2_CTGRATE")))) : 0;
    pPars->nLiftIters    =       0;  // lifting iterations
    pPars->fSparseLift   =       Gip_OptionGet("PDR2_SPARSELIFT") ? atoi(Gip_OptionGet("PDR2_SPARSELIFT")) != 0 : 0;
    pPars->fWarmStart    =       Gip_OptionGet("PDR2_WARM") ? atoi(Gip_OptionGet("PDR2_WARM")) != 0 : 0;
    pPars->nLiftSim      =       0;  // weakening by simulation
    pPars->nLiftSimOrder =       0;  // its order
    pPars->fPreproc      =       0;  // scorr preprocessing
    pPars->nPreprocTime  =      10;  // its time limit
    pPars->fVerify       =       1;  // verify the invariant
    pPars->fDumpInv      =       0;  // dump the invariant
    pPars->fVerbose      =       0;  // verbose output
    pPars->fVeryVerbose  =       0;  // very verbose output
    pPars->fSilent       =       0;  // silent execution
    pPars->iFrame        =      -1;  // explored up to this frame
}

/**Function*************************************************************

  Synopsis    [Re-queues an obligation at a frame, unless it is beyond the frontier.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Pdr2_ManRequeue( Pdr2_Man_t * p, Pdr2_Obl_t * pObl, int iFrame )
{
    Pdr2_OblPushTo( pObl, iFrame );
    if ( p->pPars->fKeepObl || iFrame <= Pdr2_ManLevel(p) )
        Pdr2_QueuePush( p, pObl );
}

/**Function*************************************************************

  Synopsis    [Opens a new frame.]

  Description [The new solver carries the transition relation and the
  lemmas of frame infinity; the solver of frame 0 has the initial states.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManExtend( Pdr2_Man_t * p )
{
    int k = Pdr2_ManFrameNum( p );
    Vec_Ptr_t * vFrame = Vec_PtrAlloc( 100 );
    p->nOblsLevelMax = Abc_MaxInt( p->nOblsLevelMax, p->nOblsLevel );
    p->nOblsLevel = 0;
    p->nLemmasLevel = p->nLemmas;
    // the restart budget of a level starts at the base value or at the work the previous level
    // took, whichever is larger (the levels of a hard example take long legitimately)
    p->LevelRestartBudget = Abc_MaxDouble( 1e6 * p->pPars->nLevelRestart * Pdr2_ManPropUnit(p->pPars) / PDR2_PROPS_PER_SEC, (double)(p->nProps - p->nPropsLevelStart) );
    p->nPropsLevelStart = p->nPropsRestartStart = p->nProps;
    if ( k > 0 && p->pPars->fPropHyp )
    {
        Pdr2_ManSolverAddUnit( p, Pdr2_ManSolver(p, k-1), Abc_Var2Lit(p->VarBad, 1) );
        Vec_IntWriteEntry( p->vLemFrame, p->IdProp, k - 1 );  // the property holds in the completed frames
    }
    if ( k > 0 )
        Pdr2_ManAbsCleanup( p );
    if ( p->nSharedMode == 4 && k > 1 && k - 1 < p->nSharedSlots )
        Pdr2_ManShareCompleted( p, k - 1 );
    Vec_PtrPush( p->vSolvers, Pdr2_ManNewSolver( p, k == 0 ? 1 : 2 ) );
    Vec_PtrPush( p->vFrames, vFrame );
    if ( k == 0 )
    {
        // frame 0 holds the cubes excluded by the initial states (one literal opposite to the
        // initial value per flop with a defined one)
        int i, Lit;
        for ( i = 0; i < p->nRegs; i++ )
        {
            Pdr2_Cube_t * pCube;
            if ( p->pInit[i] == 2 )
                continue;
            Lit = Abc_Var2Lit( i, p->pInit[i] );
            pCube = Pdr2_CubeAlloc( &Lit, 1 );
            Vec_PtrPush( vFrame, Pdr2_LemAlloc( p, pCube, NULL, 0 ) );
            Pdr2_CubeDeref( pCube );
        }
    }
    else if ( p->pSimInitBound )
        Pdr2_ManSimSeedFrame( p, k );
}

/**Function*************************************************************

  Synopsis    [Checks if the cube is subsumed by a lemma at frame k or above.]

  Description [Returns the frame of the subsuming lemma, -1 if none. If the
  subsuming lemma is at frame infinity, returns -1 and sets *pfInf.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManTrivialContained( Pdr2_Man_t * p, int iFrame, Pdr2_Cube_t * pCube, int * pfInf )
{
    Pdr2_Lem_t * pLem = Pdr2_ManIndexFindSubsuming( p, pCube, iFrame, ABC_INFINITY, 1, 0, 1 );
    *pfInf = 0;
    if ( pLem == NULL )
        return -1;
    if ( pLem->iFrame == -1 )
    {
        *pfInf = 1;
        return -1;
    }
    return pLem->iFrame;
}

/**Function*************************************************************

  Synopsis    [Adds a lemma (blocked cube) to a frame.]

  Description [The clause is added to the solvers of frames 1..iFrame
  unless a stronger lemma already covers the lower frames. Lemmas
  subsumed by the new one are removed. Returns 1 if a frame became empty,
  meaning that an inductive invariant was found.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Pdr2_Lem_t * Pdr2_LemAllocFrom( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame, Pdr2_Lem_t * pFrom )
{
    // the pushed lemma takes the id of the record it comes from if that record is retired: its
    // clauses (a superset of the new cube) are implied by the new lemma, so they too hold up to the
    // new frame; a source that stays live (a stronger lemma covers its frame, so the removal skipped
    // it) keeps its id, because two live records of one id would share its frame tag and moving
    // the weaker record (a push, a promotion) would move the tag of the stronger clauses
    int fReuse = pFrom && pFrom->fRemoved;
    Pdr2_Lem_t * pLem = Pdr2_LemAllocId( p, pCube, pObl, iFrame, fReuse ? pFrom->Id : -1 );
    p->nIdFresh += pFrom && !fReuse;
    // and inherits the counterexample to propagation to infinity
    Pdr2_LemInheritInfCti( p, pLem, pFrom );
    return pLem;
}
// checks that every id has at most one live record (debugging): the frame of an id is the
// frame of its record, so two live records with one id would share (and move) one frame tag
static void Pdr2_ManCheckIds( Pdr2_Man_t * p )
{
    Vec_Int_t * vOwner = Vec_IntStartFull( Vec_IntSize(p->vLemFrame) );
    Vec_Ptr_t * vFrame;
    Pdr2_Lem_t * pLem;
    int i, k;
    p->nIdChecks++;
    for ( k = 0; k <= Pdr2_ManFrameNum(p); k++ )
    {
        vFrame = k < Pdr2_ManFrameNum(p) ? Pdr2_ManFrame(p, k) : p->vInf;
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vFrame, pLem, i )
        {
            if ( pLem->fRemoved )
                continue;
            if ( Vec_IntEntry(vOwner, pLem->Id) >= 0 && p->nIdShared++ == 0 && !p->pPars->fSilent )
                Abc_Print( 1, "LEMMA ID CHECK FAILED: id %d is shared by live lemmas of frames %d and %d.\n", pLem->Id, Vec_IntEntry(vOwner, pLem->Id), k );
            Vec_IntWriteEntry( vOwner, pLem->Id, k );
        }
    }
    Vec_IntFree( vOwner );
}
static int Pdr2_ManAddLemma( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube, int fContainedCheck, Pdr2_Obl_t * pObl, Pdr2_Lem_t * pFrom )
{
    Pdr2_Cube_t * pCube = Pdr2_CubeAllocVec( vCube );
    Pdr2_Lem_t * pLem, * pSub;
    Vec_Ptr_t * vOcc;
    int i, k, Lit, iBegin = 1, fInvFound = 0, fInf, iMinOcc, fEqual = 0;
    assert( pCube->nLits > 0 );
    if ( iFrame == 0 )
    {
        Pdr2_Lem_t * pNew = Pdr2_LemAlloc( p, pCube, pObl, 0 );
        Pdr2_ManSolverAddLemma( p, Pdr2_ManSolver(p, 0), pCube, pNew->Id );
        Vec_PtrPush( Pdr2_ManFrame(p, 0), pNew );
        Pdr2_CubeDeref( pCube );
        return 0;
    }
    if ( fContainedCheck && (Pdr2_ManTrivialContained( p, iFrame, pCube, &fInf ) >= 0 || fInf) )
    {
        Pdr2_CubeDeref( pCube );
        return 0;
    }
    // a lemma contained in the new one at frame i covers frames 1..i
    pSub = Pdr2_ManIndexFindSubsuming( p, pCube, 1, iFrame, 0, 0, 0 );
    if ( pSub )
    {
        iBegin = pSub->iFrame + 1;
        fEqual = pSub->pCube->nLits == pCube->nLits;
    }
    // remove the lemmas of frames iBegin..iFrame subsumed by the new one
    iMinOcc = pCube->Lits[0];
    for ( i = 1; i < pCube->nLits; i++ )
        if ( Vec_PtrSize(&p->pOcc[pCube->Lits[i]]) < Vec_PtrSize(&p->pOcc[iMinOcc]) )
            iMinOcc = pCube->Lits[i];
    vOcc = &p->pOcc[iMinOcc];
    Vec_PtrForEachEntry( Pdr2_Lem_t *, vOcc, pLem, k )
    {
        if ( pLem->fRemoved || pLem->iFrame == -1 || pLem->iFrame < iBegin || pLem->iFrame > iFrame )
            continue;
        if ( pLem == pSub || !Pdr2_CubeSubsume( pCube, pLem->pCube ) )
            continue;
        i = Pdr2_LemFind( Pdr2_ManFrame(p, pLem->iFrame), pLem );
        assert( i >= 0 );
        Pdr2_LemRemove( p, Pdr2_ManFrame(p, pLem->iFrame), i );
    }
    pSub = fEqual ? Pdr2_ManIndexFindSubsuming( p, pCube, iBegin - 1, iBegin - 1, 0, 1, 0 ) : NULL;
    if ( pSub )
    {
        // the same lemma exists at frame iBegin-1: move it up
        int fEmpty;
        Vec_Ptr_t * vFrame = Pdr2_ManFrame( p, pSub->iFrame );
        i = Pdr2_LemFind( vFrame, pSub );
        assert( i >= 0 );
        Pdr2_LemRemove( p, vFrame, i );
        {
            Pdr2_Lem_t * pNew = Pdr2_LemAllocFrom( p, pCube, pObl, iFrame, pFrom ? pFrom : pSub );
            for ( k = iBegin; k <= iFrame; k++ )
                Pdr2_ManSolverAddLemma( p, Pdr2_ManSolver(p, k), pCube, pNew->Id );
            Pdr2_LemPush( Pdr2_ManFrame(p, iFrame), pNew );
        }
        p->iEarly = Abc_MinInt( p->iEarly, iBegin );
        if ( p->pPars->fCtiCache )
        {
            Pdr2_CubeRef( pCube );
            Vec_PtrPush( p->vLog, pCube );
            Vec_IntPush( p->vLogFrame, iFrame );
        }
        fEmpty = Vec_PtrSize(vFrame) == 0 && pSub->iFrame != iFrame;
        Pdr2_CubeDeref( pCube );
        return fEmpty;
    }
    for ( k = iBegin; k < iFrame; k++ )
        if ( Vec_PtrSize(Pdr2_ManFrame(p, k)) == 0 )
            fInvFound = 1;
    {
        Pdr2_Lem_t * pNew = Pdr2_LemAllocFrom( p, pCube, pObl, iFrame, pFrom );
        for ( k = iBegin; k <= iFrame; k++ )
            Pdr2_ManSolverAddLemma( p, Pdr2_ManSolver(p, k), pCube, pNew->Id );
        Pdr2_LemPush( Pdr2_ManFrame(p, iFrame), pNew );
    }
    p->iEarly = Abc_MinInt( p->iEarly, iBegin );
    p->nLemmas++;
    p->nLemmaLits += pCube->nLits;
    if ( p->pPars->fCtiCache )
    {
        Pdr2_CubeRef( pCube );
        Vec_PtrPush( p->vLog, pCube );
        Vec_IntPush( p->vLogFrame, iFrame );
    }
    (void)Lit;
    Pdr2_CubeDeref( pCube );
    return fInvFound;
}

/**Function*************************************************************

  Synopsis    [Computes prefix bounds on reachable register values by ternary simulation.]

  Description []

***********************************************************************/
// A monotone ternary envelope for states reachable in at most k steps.
// Joining every image with the previous envelope keeps only initial values
// that are guaranteed throughout the prefix, as required by nested frames.
static void Pdr2_ManSimInitBounds( Pdr2_Man_t * p )
{
    char * pState, * pValues;
    Aig_Obj_t * pObj;
    int Step, i, a, b, nChanged, Last = 0, Stable = 0;
    int MaxSteps = Gip_OptionGet("PDR2_SIMINIT") ? Abc_MinInt(512, atoi(Gip_OptionGet("PDR2_SIMINIT"))) : 0;
    abctime Start = Abc_Clock(), Deadline = Start + 2 * (abctime)CLOCKS_PER_SEC;
    if ( MaxSteps <= 0 || p->pPars->fUseAbs || Aig_ManBufNum(p->pAig) ) return;
    if ( p->timeGlobal && Deadline > p->timeGlobal ) Deadline = p->timeGlobal;
    p->pSimInitBound = ABC_CALLOC( int, p->nRegs+1 );
    pState = ABC_ALLOC( char, p->nRegs+1 );
    memcpy( pState, p->pInit, p->nRegs );
    pValues = ABC_ALLOC( char, Aig_ManObjNumMax(p->pAig) );
    memset( pValues, 2, Aig_ManObjNumMax(p->pAig) );
    pValues[Aig_ObjId(Aig_ManConst1(p->pAig))] = 1;
    for ( Step = 1; Step <= MaxSteps; Step++ )
    {
        if ( Abc_Clock() >= Deadline || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId)) ) break;
        Saig_ManForEachLo( p->pAig, pObj, i ) pValues[Aig_ObjId(pObj)] = pState[i];
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            a = pValues[Aig_ObjFaninId0(pObj)];
            b = pValues[Aig_ObjFaninId1(pObj)];
            if ( a != 2 ) a ^= Aig_ObjFaninC0(pObj);
            if ( b != 2 ) b ^= Aig_ObjFaninC1(pObj);
            pValues[Aig_ObjId(pObj)] = Aig_ObjIsExor(pObj) ? (a == 2 || b == 2 ? 2 : a ^ b) :
                (a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2);
        }
        nChanged = 0;
        Saig_ManForEachLi( p->pAig, pObj, i )
        {
            if ( pState[i] == 2 ) continue;
            a = pValues[Aig_ObjFaninId0(pObj)];
            if ( a != 2 ) a ^= Aig_ObjFaninC0(pObj);
            if ( a == pState[i] ) continue;
            pState[i] = 2;
            p->pSimInitBound[i] = Step - 1;
            nChanged++;
        }
        Last = Step;
        if ( !nChanged ) { Stable = 1; break; }
    }
    for ( i = 0; i < p->nRegs; i++ )
        if ( pState[i] != 2 ) p->pSimInitBound[i] = Stable ? GIP_FRAME_INF : Last;
    p->nSimInitSteps = Last;
    p->timeSimInit = Abc_Clock() - Start;
    ABC_FREE( pState ); ABC_FREE( pValues );
}

/**Function*************************************************************

  Synopsis    [Adds initial-value bounds certified for the given frame.]

  Description []

***********************************************************************/
static void Pdr2_ManSimSeedFrame( Pdr2_Man_t * p, int Frame )
{
    Vec_Int_t * vUnit = Vec_IntAlloc( 1 );
    Gip_Solver_t * pCheck = NULL;
    int i, Lit;
    if ( Gip_OptionGet("PDR2_SIMINIT_CHECK") )
    {
        // Independently check the simulation step with the original CNF and
        // only the previous ternary envelope, without any learned PDR lemma.
        pCheck = Gip_SolverNew( p->pCtx );
        for ( i = 0; i < p->nRegs; i++ )
            if ( p->pInit[i] != 2 && p->pSimInitBound[i] >= Frame - 1 )
            {
                Lit = Pdr2_LitLo( p, Abc_Var2Lit(i, !p->pInit[i]) );
                Gip_SolverAddLemma( pCheck, &Lit, 1 );
            }
    }
    for ( i = 0; i < p->nRegs; i++ )
    {
        if ( p->pInit[i] == 2 || p->pSimInitBound[i] < Frame ) continue;
        Lit = Abc_Var2Lit( i, p->pInit[i] );
        if ( pCheck )
        {
            int Next = Pdr2_LitLi(p, Lit);
            int Status = Gip_SolverSolve( pCheck, &Next, 1, NULL, NULL, 0, -1 );
            if ( Status != GIP_UNSAT )
            {
                if ( Status == GIP_SAT )
                    Abc_Print( -1, "Simulation initialization check FAILED at frame %d for flop %d.\n", Frame, i );
                assert( Status != GIP_SAT );
                continue;
            }
        }
        Vec_IntClear( vUnit ); Vec_IntPush( vUnit, Lit );
        Pdr2_ManAddLemma( p, Frame, vUnit, 1, NULL, NULL );
        p->nSimInitSeeds++;
    }
    if ( pCheck ) Gip_SolverFree( pCheck );
    Vec_IntFree( vUnit );
}

/**Function*************************************************************

  Synopsis    [Moves a lemma of a frame to frame infinity.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManAddInfLemma( Pdr2_Man_t * p, int iFrame, Pdr2_Lem_t * pLem )
{
    Vec_Ptr_t * vLast = Pdr2_ManFrame( p, iFrame );
    Pdr2_Lem_t * pTemp;
    int i;
    // remove the record (and any equal lemma) from the last frame
    Vec_PtrForEachEntry( Pdr2_Lem_t *, vLast, pTemp, i )
        if ( pTemp == pLem || Pdr2_CubeEqual( pTemp->pCube, pLem->pCube ) )
        {
            Pdr2_LemRemove( p, vLast, i );
            i--;
        }
    {
        Pdr2_Lem_t * pNew = Pdr2_LemAlloc( p, pLem->pCube, NULL, -1 );
        Pdr2_ManSolverAddLemma( p, p->pInf, pLem->pCube, pNew->Id );
        Vec_PtrPush( p->vInf, pNew );
        // the clauses of the old record (in the frame solvers) are invariants now
        Vec_IntWriteEntry( p->vLemFrame, pLem->Id, GIP_FRAME_INF );
    }
    p->nInfLemmas++;
    if ( p->pPars->fCtiCache )
    {
        Pdr2_CubeRef( pLem->pCube );
        Vec_PtrPush( p->vLog, pLem->pCube );
        Vec_IntPush( p->vLogFrame, -1 );
    }
}

/**Function*************************************************************

  Synopsis    [Returns a lemma of the previous frame contained in the cube.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Pdr2_Cube_t * Pdr2_ManParentLemma( Pdr2_Man_t * p, Vec_Int_t * vCube, int iFrame )
{
    Pdr2_Cube_t * pCube;
    Pdr2_Lem_t * pLem;
    if ( iFrame <= 1 )
        return NULL;
    pCube = Pdr2_CubeAllocVec( vCube );
    pLem = Pdr2_ManIndexFindSubsuming( p, pCube, iFrame - 1, iFrame - 1, 0, 0, 0 );
    Pdr2_CubeDeref( pCube );
    return pLem ? pLem->pCube : NULL;
}

/**Function*************************************************************

  Synopsis    [Literal-set containment of an unsorted vector in a cube.]

  Description [Returns 1 if all literals of vA belong to the cube (whose
  literals are sorted).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_LitsInCube( Vec_Int_t * vA, Pdr2_Cube_t * pB )
{
    int i, Lit, lo, hi, mid;
    if ( Vec_IntSize(vA) > pB->nLits )
        return 0;
    Vec_IntForEachEntry( vA, Lit, i )
    {
        if ( !(pB->Sign & Pdr2_LitSign(Lit)) )
            return 0;
        for ( lo = 0, hi = pB->nLits; lo < hi; )
        {
            mid = (lo + hi) >> 1;
            if ( pB->Lits[mid] < Lit )
                lo = mid + 1;
            else
                hi = mid;
        }
        if ( lo == pB->nLits || pB->Lits[lo] != Lit )
            return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Pushes a lemma to higher frames while it stays inductive.]

  Description [Returns the first frame where the lemma is not inductive
  (level+1 if it reached the end). The cube may be strengthened by cores.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// verifies a time-generalization step: the cube must be inductive relative to frame iFrame
static void Pdr2_ManTimeGenCheck( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube )
{
    // the check is a diagnostic: its query runs without the slice budget (a canceled query is
    // not a failure) and leaves the state of the search (core frame, budget, cut flag) as it was
    Vec_Int_t * vTmp = Vec_IntDup( vCube );
    ABC_INT64_T propLimit = p->propLimit, nProps = p->nProps, nConflicts = p->nConflicts;
    int iSave = p->iCoreFrame, fQueryCut = p->fQueryCut, RetValue;
    p->nTgChecks++;
    p->propLimit = 0;
    RetValue = Pdr2_ManSolveRelative( p, iFrame == -1 ? p->pInf : Pdr2_ManSolver(p, iFrame), vTmp, 1, NULL );
    if ( RetValue == 0 )
    {
        p->nTgFailed++;
        if ( !p->pPars->fSilent )
            Abc_Print( 1, "TIME GENERALIZATION CHECK FAILED: a cube of %d literals is not inductive relative to frame %d.\n", Vec_IntSize(vCube), iFrame );
    }
    else if ( RetValue == -1 )
        p->nTgUndecided++;
    p->propLimit  = propLimit;
    p->nProps     = nProps;
    p->nConflicts = nConflicts;
    p->fQueryCut  = fQueryCut;
    p->iCoreFrame = iSave;
    Vec_IntFree( vTmp );
}
// moves the last lemma of the frame to frame infinity if it is the given cube
static void Pdr2_ManPromoteLast( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube )
{
    Pdr2_Lem_t * pLem;
    int k, fSame;
    if ( Vec_PtrSize(Pdr2_ManFrame(p, iFrame)) == 0 )
        return;
    pLem = (Pdr2_Lem_t *)Vec_PtrEntryLast( Pdr2_ManFrame(p, iFrame) );
    fSame = pLem->pCube->nLits == Vec_IntSize(vCube);
    for ( k = 0; fSame && k < pLem->pCube->nLits; k++ )
        if ( Vec_IntFind(vCube, pLem->pCube->Lits[k]) == -1 )
            fSame = 0;
    if ( !fSame )
        return;
    if ( p->fTimeGenCheck )
        Pdr2_ManTimeGenCheck( p, -1, vCube );
    if ( pLem->pObl )
        Pdr2_QueueRemove( p, pLem->pObl );
    Pdr2_ManAddInfLemma( p, iFrame, pLem );
    p->nInfPromotedTg++;
}
static int Pdr2_ManPushLemma( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube )
{
    Vec_Int_t * vCore = Vec_IntAlloc( 100 );
    abctime clk = Abc_Clock();
    int i, RetValue, Result = Pdr2_ManLevel(p) + 1;
    p->fPushInf = 0;
    for ( i = iFrame + 1; i <= Pdr2_ManLevel(p); )
    {
        RetValue = Pdr2_ManSolveRelativeJftr( p, Pdr2_ManSolver(p, i-1), vCube, 1, NULL,
                                              Pdr2_ManJftrReq(p, PDR2_JQ_PUSH, GIP_JFTR_ANSWER) );
        if ( RetValue != 1 )
        {
            Result = i;
            break;
        }
        if ( Pdr2_ManInductiveCore( p, Pdr2_ManSolver(p, i-1), vCore ) )
        {
            Vec_IntClear( vCube );
            Vec_IntAppend( vCube, vCore );
        }
        if ( p->pPars->fTimeGen )
        {
            // time generalization: the proof used lemmas of frames >= T only (and the proof
            // applies to the core, a subset of the assumptions), so the cube is inductive
            // relative to every frame up to T and holds up to frame T+1; when no frame lemma
            // was used it holds in every reachable state
            int T = p->iCoreFrame, iNext;
            if ( T >= GIP_FRAME_INF )
            {
                p->fPushInf = 1;
                p->nTgInf++;
                break;
            }
            iNext = p->pPars->fTimeGen >= 2 ? Abc_MaxInt( i + 1, T + 2 ) : i + 1;
            if ( iNext > i + 1 )
            {
                p->nTgJumps++;
                p->nTgFrames += Abc_MinInt( iNext, Pdr2_ManLevel(p) + 1 ) - (i + 1);
                if ( p->fTimeGenCheck )
                    Pdr2_ManTimeGenCheck( p, Abc_MinInt( T, Pdr2_ManLevel(p) - 1 ), vCube );
            }
            i = iNext;
        }
        else
            i++;
    }
    Vec_IntFree( vCore );
    p->timePush += Abc_Clock() - clk;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Plain "down": joins the cube with counterexamples to induction.]

  Description [Returns 1 and the inductive core in vOut if the cube (or a
  subset of it) becomes inductive relative to frame iFrame-1; 0 otherwise.
  The literals in pKeep must stay. vCexS/vCexT cache earlier
  counterexamples to induction as (predecessor, successor) cubes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManDown( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube, char * pKeep, Vec_Int_t * vFull,
                         Vec_Int_t * vCst, Vec_Ptr_t * vCexS, Vec_Ptr_t * vCexT, Vec_Int_t * vOut )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, iFrame - 1 );
    Vec_Int_t * vCur = Vec_IntDup( vCube );
    Vec_Int_t * vOrd = Vec_IntAlloc( 100 );
    Vec_Int_t * vTmp = Vec_IntAlloc( 100 );
    int i, k, Lit, Var, Value, RetValue, fFail, nTries = 0, Result = 0;
    int fOneQuery = p->nDownMode == 1 || p->nDownMode == 2 ||
        (p->nDownMode == 3 && p->nDownRetries >= 512 &&
         64*(p->nDownJoined+1) < p->nDownRetries && (p->nDowns & 31));
    p->nDowns++;
    while ( 1 )
    {
        if ( Pdr2_LitsAreInit(p, vCur) )
            break;
        // cached counterexamples to induction
        fFail = 0;
        for ( k = 0; k < Vec_PtrSize(vCexS); k++ )
            if ( !Pdr2_LitsInCube( vCur, (Pdr2_Cube_t *)Vec_PtrEntry(vCexS, k) ) &&
                  Pdr2_LitsInCube( vCur, (Pdr2_Cube_t *)Vec_PtrEntry(vCexT, k) ) )
            {
                fFail = 1;
                p->nDownCacheHits++;
                break;
            }
        if ( fFail )
            break;
        Vec_IntClear( vOrd );
        Vec_IntAppend( vOrd, vCur );
        Pdr2_ManSortByAct( p, vOrd, 0 );
        nTries++;
        p->nDownQueries++;
        if ( p->nDownMode && nTries > 1 ) p->nDownRetries++;
        RetValue = Pdr2_ManTryDropJftr( p, pSat, vOrd, 1, vCst, Pdr2_ManJftrReq(p, PDR2_JQ_MIC, GIP_JFTR_WALK) );
        if ( RetValue == -1 )
            break;
        if ( RetValue == 1 )
        {
            if ( Pdr2_ManInductiveCore( p, pSat, vOut ) )
                Result = 1, p->nDownJoined += nTries > 1;
            break;
        }
        if ( fOneQuery && p->nDownMode != 1 )
        {
            // Save the transition as a reason to reject future drops. Only
            // an UNSAT induction query above can certify a stronger lemma.
            if ( p->pPars->nDownCacheMode != 2 )
            {
                Vec_IntClear(vOrd);
                Vec_IntClear(vTmp);
                Vec_IntForEachEntry(vFull, Lit, i)
                {
                    Var = Abc_Lit2Var(Lit);
                    Value = Pdr2_SolverCompletedValue(pSat, p->pLoVar[Var]);
                    if ( Value != GIP_NONE ) Vec_IntPush(vOrd, Abc_Var2Lit(Var, Value == GIP_FALSE));
                    Value = Gip_SolverLitValue(Pdr2_SolverActual(pSat), p->pLiLit[Var]);
                    if ( Value != GIP_NONE ) Vec_IntPush(vTmp, Abc_Var2Lit(Var, Value == GIP_FALSE));
                }
                Vec_PtrPush(vCexS, Pdr2_CubeAllocVec(vOrd));
                Vec_PtrPush(vCexT, Pdr2_CubeAllocVec(vTmp));
            }
            p->nDownStopped++;
            break;
        }
        // keep the literals of the model that are needed
        fFail = 0;
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vCur, Lit, i )
        {
            Value = Pdr2_ManLitValue( p, pSat, Lit );
            if ( pKeep[Lit] )
            {
                if ( Value == GIP_TRUE )
                    Vec_IntPush( vTmp, Lit );
                else
                {
                    fFail = 1;
                    break;
                }
            }
            else if ( Value == GIP_TRUE && !Pdr2_SolverFlip( pSat, p->pLoVar[Abc_Lit2Var(Lit)] ) )
                Vec_IntPush( vTmp, Lit );
        }
        Vec_IntClear( vCur );
        Vec_IntAppend( vCur, vTmp );
        // This cache can only reject a drop, never certify one. The default
        // stores necessary source assignments. Mode 1 follows rIC3's heuristic
        // of storing assignments that can be removed instead; mode 2 disables
        // the cache. Both enabled modes perform the same model weakening.
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vFull, Lit, i )
        {
            Var = p->pLoVar[Abc_Lit2Var(Lit)];
            Value = Pdr2_SolverCompletedValue( pSat, Var );
            if ( Value != GIP_NONE )
            {
                int fRemoved = Pdr2_SolverFlip( pSat, Var );
                if ( Pdr2_SolverActual(pSat)->Jftr.fEarly || fRemoved == (p->pPars->nDownCacheMode == 1) )
                    Vec_IntPush( vTmp, Abc_Var2Lit(Abc_Lit2Var(Lit), Value == GIP_FALSE) );
            }
        }
        if ( p->pPars->nDownCacheMode != 2 )
            Vec_PtrPush( vCexS, Pdr2_CubeAllocVec( vTmp ) );
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vFull, Lit, i )
        {
            Value = Gip_SolverLitValue( Pdr2_SolverActual(pSat), p->pLiLit[Abc_Lit2Var(Lit)] );
            if ( Value != GIP_NONE )
                Vec_IntPush( vTmp, Abc_Var2Lit(Abc_Lit2Var(Lit), Value == GIP_FALSE) );
        }
        if ( p->pPars->nDownCacheMode != 2 )
            Vec_PtrPush( vCexT, Pdr2_CubeAllocVec( vTmp ) );
        if ( fOneQuery ) { p->nDownStopped++; break; }
        if ( fFail )
            break;
    }
    Vec_IntFree( vCur );
    Vec_IntFree( vOrd );
    Vec_IntFree( vTmp );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries to block a cube at a frame with limited effort.]

  Description [Used for counterexamples to generalization. On success,
  the cube is generalized (plain down, with the constraint) and added as a
  lemma. Returns 1 on success.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManTrivialBlockRec( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vLemma, Vec_Int_t * vCst, int * pLimit, Pdr2_MicPar_t Par )
{
    Gip_Solver_t * pSat;
    Vec_Int_t * vOrd, * vMic, * vPred, * vInputs;
    int RetValue, Result = 0, iPushed;
    if ( iFrame == 0 )
        return 0;
    if ( Pdr2_LitsAreInit(p, vLemma) )
        return 0;
    if ( *pLimit == 0 )
        return 0;
    (*pLimit)--;
    pSat    = Pdr2_ManSolver( p, iFrame - 1 );
    vOrd    = Vec_IntAlloc( 100 );
    vMic    = Vec_IntAlloc( 100 );
    vPred   = Vec_IntAlloc( 100 );
    vInputs = Vec_IntAlloc( 100 );
    while ( 1 )
    {
        Vec_IntClear( vOrd );
        Vec_IntAppend( vOrd, vLemma );
        Pdr2_ManSortByAct( p, vOrd, 0 );
        RetValue = Pdr2_ManTryDropJftr( p, pSat, vOrd, 1, vCst, Pdr2_ManJftrReq(p, PDR2_JQ_MIC, GIP_JFTR_WALK) );
        if ( RetValue == 1 )
        {
            if ( !Pdr2_ManInductiveCore( p, pSat, vMic ) )
                break;
            if ( p->pPars->fCtgMic )
                Pdr2_ManMic( p, iFrame, vMic, vCst, Par );
            iPushed = Pdr2_ManPushLemma( p, iFrame, vMic );
            Pdr2_ManAddLemma( p, iPushed - 1, vMic, 0, NULL, NULL );
            if ( p->fPushInf && iPushed - 1 == Pdr2_ManLevel(p) )
                Pdr2_ManPromoteLast( p, iPushed - 1, vMic );
            p->nCtgsBlocked++;
            Result = 1;
            break;
        }
        if ( RetValue == -1 || *pLimit == 0 )
            break;
        Pdr2_ManGetPred( p, 0, vPred, vInputs );
        Pdr2_ManAbsProject( p, vPred, NULL );
        if ( !Pdr2_ManTrivialBlockRec( p, iFrame - 1, vPred, vCst, pLimit, Par ) )
            break;
    }
    Vec_IntFree( vOrd );
    Vec_IntFree( vMic );
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    return Result;
}
static int Pdr2_ManTrivialBlock( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vLemma, Vec_Int_t * vCst, Pdr2_MicPar_t Par )
{
    int Limit = Par.nLimit;
    return Pdr2_ManTrivialBlockRec( p, iFrame, vLemma, vCst, &Limit, Par );
}

/**Function*************************************************************

  Synopsis    ["Down" with counterexamples to generalization.]

  Description [Like Pdr2_ManDown, but a counterexample to induction may
  first be blocked at the previous frame (as a lemma), up to Par.nMax
  times per round, before the cube is joined with it.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManCtgDown( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube, char * pKeep, Vec_Int_t * vFull, Pdr2_MicPar_t Par, Vec_Int_t * vOut )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, iFrame - 1 );
    Vec_Int_t * vCur = Vec_IntDup( vCube );
    Vec_Int_t * vOrd = Vec_IntAlloc( 100 );
    Vec_Int_t * vTmp = Vec_IntAlloc( 100 );
    Vec_Int_t * vPred = Vec_IntAlloc( 100 );
    Vec_Int_t * vInputs = Vec_IntAlloc( 100 );
    Vec_Int_t * vCst = Vec_IntAlloc( 100 );
    Pdr2_MicPar_t SubPar = Par;
    int i, Lit, RetValue, fFail, nCtgs = 0, Result = 0;
    SubPar.nLevel = Par.nLevel - 1;
    // the constraint clause "not full"
    Vec_IntForEachEntry( vFull, Lit, i )
        Vec_IntPush( vCst, Abc_LitNot(Lit) );
    p->nDowns++;
    while ( 1 )
    {
        if ( Pdr2_LitsAreInit(p, vCur) )
            break;
        if ( p->nMicCexMode && Pdr2_ManMicCexFind(p, iFrame - 1, vCur, pKeep) && p->nMicCexMode == 2 )
            break;
        Vec_IntClear( vOrd );
        Vec_IntAppend( vOrd, vCur );
        Pdr2_ManSortByAct( p, vOrd, 0 );
        RetValue = Pdr2_ManTryDropJftr( p, pSat, vOrd, 1, NULL, Pdr2_ManJftrReq(p, PDR2_JQ_MIC, GIP_JFTR_WALK) );
        if ( RetValue == -1 )
            break;
        if ( RetValue == 1 )
        {
            if ( Pdr2_ManInductiveCore( p, pSat, vOut ) )
                Result = 1;
            break;
        }
        if ( p->nMicCexMode ) Pdr2_ManMicCexStore( p, pSat, iFrame - 1 );
        fFail = 0;
        Vec_IntForEachEntry( vCur, Lit, i )
            if ( pKeep[Lit] && Pdr2_ManLitValue( p, pSat, Lit ) != GIP_TRUE )
            {
                fFail = 1;
                break;
            }
        if ( fFail )
            break;
        // the lifted counterexample to induction
        Pdr2_ManGetPred( p, 0, vPred, vInputs );
        Pdr2_ManAbsProject( p, vPred, NULL );
        if ( nCtgs < Par.nMax && iFrame > 1 && !Pdr2_LitsAreInit(p, vPred) )
        {
            // blocking the CTG adds lemmas to the solvers, so the fixed domain is released meanwhile
            if ( !p->pPars->fCtgLocal )
                Pdr2_ManUnsetMicDomain( p, pSat );
            fFail = Pdr2_ManTrivialBlock( p, iFrame - 1, vPred, vCst, SubPar );
            if ( !p->pPars->fCtgLocal )
                Pdr2_ManSetMicDomain( p, pSat, vFull );
            if ( p->fQueryCut )
                break;
            if ( fFail )
            {
                nCtgs++;
                continue;
            }
        }
        nCtgs = 0;
        // join the cube with the counterexample
        Vec_IntForEachEntry( vPred, Lit, i )
            p->pLitMark[Lit] = 1;
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vCur, Lit, i )
        {
            if ( p->pLitMark[Lit] )
                Vec_IntPush( vTmp, Lit );
            else if ( pKeep[Lit] )
                fFail = 1;
        }
        Vec_IntForEachEntry( vPred, Lit, i )
            p->pLitMark[Lit] = 0;
        if ( fFail )
            break;
        Vec_IntClear( vCur );
        Vec_IntAppend( vCur, vTmp );
    }
    Vec_IntFree( vCur );
    Vec_IntFree( vOrd );
    Vec_IntFree( vTmp );
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    Vec_IntFree( vCst );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Minimal inductive subclause by dropping literals.]

  Description [Generalizes the cube (in place) relative to frame iFrame-1.
  Literals are tried in increasing activity order (or shuffled 20% of the
  time); literals not in the parent lemma are tried first. Each drop is
  checked with down (Par.nLevel = 0) or ctg_down (Par.nLevel = 1).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManMic( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube, Vec_Int_t * vCst, Pdr2_MicPar_t Par )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, iFrame - 1 );
    Vec_Int_t * vRemoved = Vec_IntAlloc( 100 );
    Vec_Int_t * vFull = Vec_IntAlloc( 100 );
    Vec_Int_t * vNew = Vec_IntAlloc( 100 );
    Vec_Int_t * vTmp = Vec_IntAlloc( 100 );
    Vec_Int_t * vInit = Vec_IntDup( vCube );
    Vec_Ptr_t * vCexS = Vec_PtrAlloc( 16 );
    Vec_Ptr_t * vCexT = Vec_PtrAlloc( 16 );
    char * pKeep, * pMark;
    Pdr2_Cube_t * pParent, * pTemp;
    abctime clk = Abc_Clock();
    int i, k, Lit, iNew, nFailed = 0, fFixedDomain = Par.nLevel == 0 || !p->pPars->fCtgLocal;
    int Context = (iFrame > 2) + 2 * (Vec_IntSize(vCube) > 12);
    unsigned char * pHistory = p->pDropHistory ? p->pDropHistory + (size_t)4 * Context * p->nRegs : NULL;
    int fUseHistory = p->nDropHistory != 4 || (p->nMics >= 64 && p->nMicLits >= 10 * p->nMics &&
                       p->nMicDropFail > 6 * p->nMicDropOk);
    if ( p->fReachFilter && p->nReachStride && Gip_OptionGet("PDR2_REACH_CHECK") )
        assert( !Pdr2_ManReachContains(p, iFrame, vCube) );
    p->nMicNest++;
    // the flags are reused by recursion depth (a CTG may be generalized inside a down) and are
    // zero between calls: pMark is cleared where it is used, pKeep over the initial literals
    if ( Vec_PtrSize(p->vMicScratch) == p->nMicDepth )
        Vec_PtrPush( p->vMicScratch, ABC_CALLOC( char, 4 * p->nRegs ) );
    pKeep = (char *)Vec_PtrEntry( p->vMicScratch, p->nMicDepth++ );
    pMark = pKeep + 2 * p->nRegs;
    if ( fFixedDomain )
        Pdr2_ManSetMicDomain( p, pSat, vCube );
    p->nMics++;
    p->nMicLits += Vec_IntSize( vCube );
    if ( Pdr2_ManRandomBool( p, 0.2 ) )
        Pdr2_ManShuffle( p, vCube );
    else
        Pdr2_ManSortByAct( p, vCube, 1 );
    if ( p->pPars->fParentLemma && (pParent = Pdr2_ManParentLemma( p, vCube, iFrame )) )
    {
        // literals outside the parent lemma go first
        for ( i = 0; i < pParent->nLits; i++ )
            pMark[pParent->Lits[i]] = 1;
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vCube, Lit, i )
            if ( !pMark[Lit] )
                Vec_IntPush( vTmp, Lit );
        Vec_IntForEachEntry( vCube, Lit, i )
            if ( pMark[Lit] )
                Vec_IntPush( vTmp, Lit );
        for ( i = 0; i < pParent->nLits; i++ )
            pMark[pParent->Lits[i]] = 0;
        Vec_IntClear( vCube );
        Vec_IntAppend( vCube, vTmp );
    }
    i = 0;
    while ( i < Vec_IntSize(vCube) )
    {
        int fOk;
        unsigned char * pCounts;
        Lit = Vec_IntEntry( vCube, i );
        pCounts = pHistory ? pHistory + 2 * Lit : NULL;
        if ( fUseHistory && pCounts && pCounts[0] >= (p->nDropHistory == 1 ? 8 : 4) &&
             (p->nDropHistory == 1 ? 16 : p->nDropHistory == 2 ? 8 : 4) * pCounts[1] < pCounts[0] &&
             ((p->nMics + 13u * (unsigned)Lit) & 15) )
        {
            // Recheck occasionally. A skipped literal is still eligible to
            // disappear in the proof core of a different, successful drop.
            p->nDropHistorySkipped++;
            i++;
            continue;
        }
        if ( pKeep[Lit] )
        {
            i++;
            continue;
        }
        Vec_IntClear( vRemoved );
        Vec_IntForEachEntry( vCube, Lit, k )
            if ( k != i )
                Vec_IntPush( vRemoved, Lit );
        Vec_IntClear( vFull );
        Vec_IntAppend( vFull, vCube );
        if ( p->fReachFilter && p->nReachStride && Pdr2_ManReachContains(p, iFrame, vRemoved) )
            fOk = 0, p->nReachReject++;
        else if ( Par.nLevel == 0 )
            fOk = Pdr2_ManDown( p, iFrame, vRemoved, pKeep, vFull, vCst, vCexS, vCexT, vNew );
        else
            fOk = Pdr2_ManCtgDown( p, iFrame, vRemoved, pKeep, vFull, Par, vNew );
        if ( pCounts && !p->fQueryCut )
        {
            if ( pCounts[0] == 32 ) { pCounts[0] >>= 1; pCounts[1] >>= 1; }
            pCounts[0]++;
            pCounts[1] += fOk;
        }
        if ( fOk )
        {
            nFailed = 0;
            p->nMicDropOk++;
            // the new cube is the old one restricted to the result; continue after the tried literals
            Vec_IntForEachEntry( vNew, Lit, k )
                pMark[Lit] = 1;
            Vec_IntClear( vTmp );
            Vec_IntForEachEntry( vCube, Lit, k )
                if ( pMark[Lit] )
                    Vec_IntPush( vTmp, Lit );
            Vec_IntForEachEntry( vNew, Lit, k )
                pMark[Lit] = 0;
            for ( k = 0; k < i; k++ )
                pMark[Vec_IntEntry(vCube, k)] = 1;
            iNew = Vec_IntSize( vTmp );
            Vec_IntForEachEntry( vTmp, Lit, k )
                if ( !pMark[Lit] )
                {
                    iNew = k;
                    break;
                }
            for ( k = 0; k < i; k++ )
                pMark[Vec_IntEntry(vCube, k)] = 0;
            Vec_IntClear( vCube );
            Vec_IntAppend( vCube, vTmp );
            i = iNew;
            if ( fFixedDomain )
            {
                Pdr2_ManUnsetMicDomain( p, pSat );
                Pdr2_ManSetMicDomain( p, pSat, vCube );
            }
        }
        else if ( p->fQueryCut )
        {
            // a resource limit canceled the query: keep the last proved cube and yield
            break;
        }
        else
        {
            p->nMicDropFail++;
            pKeep[Vec_IntEntry(vCube, i)] = 1;
            i++;
            // vCube is still the last proved inductive cube. Stopping here
            // changes lemma quality, but never accepts an unproved literal drop.
            if ( p->pPars->nMicFailLimit && ++nFailed >= p->pPars->nMicFailLimit )
            {
                p->nMicEarlyStop++;
                break;
            }
        }
    }
    if ( fFixedDomain )
        Pdr2_ManUnsetMicDomain( p, pSat );
    Pdr2_ManActBump( p, vCube );
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vCexS, pTemp, i )
        Pdr2_CubeDeref( pTemp );
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vCexT, pTemp, i )
        Pdr2_CubeDeref( pTemp );
    Vec_PtrFree( vCexS );
    Vec_PtrFree( vCexT );
    Vec_IntFree( vRemoved );
    Vec_IntFree( vFull );
    Vec_IntFree( vNew );
    Vec_IntFree( vTmp );
    Vec_IntForEachEntry( vInit, Lit, i )
        pKeep[Lit] = 0;
    Vec_IntFree( vInit );
    p->nMicDepth--;
    if ( --p->nMicNest == 0 )
        p->timeMic += Abc_Clock() - clk;
}

/**Function*************************************************************

  Synopsis    [treb's generalization: literal removal with core shrinking.]

  Description [Each literal, in ascending activity order, is removed in
  turn and the cube is checked for inductiveness relative to the frame
  (with the negated cube assumed); on success the UNSAT core replaces the
  cube. The orbit over the literals is repeated until a full orbit brings
  no removal, at most twice. No down or CTG handling.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManMicTreb( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, iFrame - 1 );
    Vec_Int_t * vOrder = Vec_IntDup( vCube );
    Vec_Int_t * vTry = Vec_IntAlloc( 100 );
    Vec_Int_t * vCore = Vec_IntAlloc( 100 );
    abctime clk = Abc_Clock();
    int n = Vec_IntSize( vOrder ), i = 0, iLast = 0, Count, Lit, Lit2, k, RetValue, nFailed = 0;
    p->nMicNest++;
    p->nMics++;
    p->nMicLits += Vec_IntSize( vCube );
    if ( n > 1 )
    {
        Pdr2_ManSetMicDomain( p, pSat, vCube );
        if ( Pdr2_ManRandomBool( p, 0.2 ) )
            Pdr2_ManShuffle( p, vOrder );
        else
            Pdr2_ManSortByAct( p, vOrder, 1 );
        for ( Count = 0; Count < 2 * n; Count++ )
        {
            Lit = Vec_IntEntry( vOrder, i );
            if ( Vec_IntFind(vCube, Lit) >= 0 && Vec_IntSize(vCube) > 1 )
            {
                Vec_IntClear( vTry );
                Vec_IntForEachEntry( vCube, Lit2, k )
                    if ( Lit2 != Lit )
                        Vec_IntPush( vTry, Lit2 );
                if ( !Pdr2_LitsAreInit(p, vTry) )
                {
                    Pdr2_ManSortByAct( p, vTry, 0 );
                    RetValue = Pdr2_ManTryDropJftr( p, pSat, vTry, 1, NULL,
                                                    Pdr2_ManJftrReq(p, PDR2_JQ_MIC, GIP_JFTR_WALK) );
                    if ( RetValue == 1 && Pdr2_ManInductiveCore( p, pSat, vCore ) )
                    {
                        nFailed = 0;
                        p->nMicDropOk++;
                        Vec_IntClear( vCube );
                        Vec_IntAppend( vCube, vCore );
                        iLast = i;
                        Pdr2_ManUnsetMicDomain( p, pSat );
                        Pdr2_ManSetMicDomain( p, pSat, vCube );
                    }
                    else
                    {
                        p->nMicDropFail++;
                        if ( RetValue == -1 )
                            break;
                        if ( p->pPars->nMicFailLimit && ++nFailed >= p->pPars->nMicFailLimit )
                        {
                            p->nMicEarlyStop++;
                            break;
                        }
                    }
                }
            }
            i = (i + 1) % n;
            if ( i == iLast )
                break;
        }
        Pdr2_ManUnsetMicDomain( p, pSat );
    }
    Pdr2_ManActBump( p, vCube );
    Vec_IntFree( vOrder );
    Vec_IntFree( vTry );
    Vec_IntFree( vCore );
    if ( --p->nMicNest == 0 )
        p->timeMic += Abc_Clock() - clk;
}


/**Function*************************************************************

  Synopsis    [Tests a candidate derived from a parent lemma before minimization.]

  Description []

***********************************************************************/
// Try a previously learned subcube as the whole generalization. A failed
// query identifies next-state literals that the prediction omitted; add one
// high-activity literal and retry, at most four queries. A candidate is used
// only after an UNSAT relative-induction proof and an initial-state check.
static int Pdr2_ManPredictParent( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube )
{
    Pdr2_Cube_t * pParent = Pdr2_ManParentLemma( p, vCube, Frame );
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, Frame - 1 );
    Vec_Int_t * vTry, * vCore;
    abctime clk;
    int Iter, i, Lit, Best, Ret, Result = 0;
    double Act;
    if ( !pParent || pParent->nLits >= Vec_IntSize(vCube) ) return 0;
    clk = Abc_Clock();
    p->nPredictCalls++;
    vTry = Vec_IntAlloc( Vec_IntSize(vCube) );
    vCore = Vec_IntAlloc( Vec_IntSize(vCube) );
    Pdr2_CubeToVec( pParent, vTry );
    Pdr2_ManSetMicDomain( p, pSat, vCube );
    for ( Iter = 0; Iter < 4 && Vec_IntSize(vTry) < Vec_IntSize(vCube); Iter++ )
    {
        if ( Pdr2_LitsAreInit(p, vTry) ) break;
        Pdr2_ManSortByAct( p, vTry, 0 );
        p->nPredictQueries++;
        Ret = Pdr2_ManTryDropJftr( p, pSat, vTry, 1, NULL, Pdr2_ManJftrReq(p, PDR2_JQ_MIC, GIP_JFTR_WALK) );
        if ( Ret == -1 ) break;
        if ( Ret == 1 )
        {
            if ( Pdr2_ManInductiveCore(p, pSat, vCore) )
            {
                p->nPredictProved++;
                p->nPredictSaved += Vec_IntSize(vCube) - Vec_IntSize(vCore);
                Vec_IntClear( vCube );
                Vec_IntAppend( vCube, vCore );
                Result = 1;
            }
            break;
        }
        Best = -1;
        Act = -1.0;
        Vec_IntForEachEntry( vCube, Lit, i )
            if ( Vec_IntFind(vTry, Lit) == -1 &&
                 Gip_SolverLitValue(Pdr2_SolverActual(pSat), Pdr2_LitLi(p, Lit)) == GIP_FALSE &&
                 p->pAct[Abc_Lit2Var(Lit)] > Act )
                Best = Lit, Act = p->pAct[Abc_Lit2Var(Lit)];
        if ( Best == -1 ) break;
        Vec_IntPush( vTry, Best );
    }
    Pdr2_ManUnsetMicDomain( p, pSat );
    Vec_IntFree( vTry );
    Vec_IntFree( vCore );
    p->timePredict += Abc_Clock() - clk;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Generalizes an inductive cube by restoring literals challenged by a model.]

  Description [Starts with its most active literals. A transition into this
  tentative cube tells which omitted next-state literals can rule it out.
  Restore one such literal and check again. Only a proved core that also
  excludes the initial states replaces the original cube.]

  SideEffects []

***********************************************************************/
static void Pdr2_ManMicGroup( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver(p, Frame - 1);
    Vec_Int_t * vOrder = Vec_IntDup(vCube), * vTry = Vec_IntAlloc(Vec_IntSize(vCube));
    Vec_Int_t * vCore = Vec_IntAlloc(Vec_IntSize(vCube));
    int n = Vec_IntSize(vCube), Head, i, Iter, Lit, Best, Ret;
    abctime Start = Abc_Clock();
    p->nMics++;
    p->nMicLits += n;
    Pdr2_ManSortByAct(p, vOrder, 0);
    Head = p->nMicGroup == 2 ? 1 : Abc_MaxInt(1, n / 2);
    for ( i = 0; i < Head; ++i )
        Vec_IntPush(vTry, Vec_IntEntry(vOrder, i));
    if ( Pdr2_LitsAreInit(p, vTry) )
    {
        for ( i = Head; i < n; ++i )
            if ( Pdr2_ManLitIsNonInit(p, Vec_IntEntry(vOrder, i)) ) break;
        if ( i < n )
        {
            Lit = Vec_IntEntry(vOrder, i);
            Vec_IntWriteEntry(vOrder, i, Vec_IntEntry(vOrder, Head));
            Vec_IntWriteEntry(vOrder, Head++, Lit);
            Vec_IntPush(vTry, Lit);
        }
    }
    Pdr2_ManSetMicDomain(p, pSat, vCube);
    for ( Iter = 0; Iter < (p->nMicGroup == 2 ? 12 : 6) && Head < n; ++Iter )
    {
        if ( Pdr2_LitsAreInit(p, vTry) ) break;
        p->nGroupQueries++;
        Ret = Pdr2_ManTryDrop(p, pSat, vTry, 1, NULL);
        if ( Ret < 0 ) break;
        if ( Ret == 1 )
        {
            if ( Pdr2_ManInductiveCore(p, pSat, vCore) )
            {
                p->nGroupLits += n - Vec_IntSize(vCore);
                Vec_IntClear(vCube);
                Vec_IntAppend(vCube, vCore);
            }
            break;
        }
        Best = -1;
        for ( i = Head; i < n; ++i )
        {
            Lit = Vec_IntEntry(vOrder, i);
            Ret = Gip_SolverLitValue(Pdr2_SolverActual(pSat), Pdr2_LitLi(p, Lit));
            if ( Ret == GIP_FALSE ) { Best = i; break; }
            if ( Ret != GIP_TRUE && Best < 0 ) Best = i;
        }
        if ( Best < 0 ) break;
        Lit = Vec_IntEntry(vOrder, Best);
        Vec_IntWriteEntry(vOrder, Best, Vec_IntEntry(vOrder, Head));
        Vec_IntWriteEntry(vOrder, Head++, Lit);
        Vec_IntPush(vTry, Lit);
    }
    Pdr2_ManUnsetMicDomain(p, pSat);
    Pdr2_ManActBump(p, vCube);
    Vec_IntFree(vOrder);
    Vec_IntFree(vTry);
    Vec_IntFree(vCore);
    p->timeMic += Abc_Clock() - Start;
}

typedef struct Pdr2_MicHits_t_
{
    unsigned Rows[25], Best;
    int Sizes[25], nRows, nBest, nVisits;
} Pdr2_MicHits_t;

/**Function*************************************************************

  Synopsis    [Finds a short set of literals that hits the observed countermodels.]

***********************************************************************/
static void Pdr2_MicPickHits( Pdr2_MicHits_t * p, unsigned Selected, int Size )
{
    int i, Min = -1;
    unsigned Bits, Bit;
    if ( Size >= p->nBest || ++p->nVisits > 2048 ) return;
    for ( i = 0; i < p->nRows; i++ )
        if ( !(p->Rows[i] & Selected) && (Min < 0 || p->Sizes[i] < p->Sizes[Min]) ) Min = i;
    if ( Min < 0 )
    {
        p->Best = Selected;
        p->nBest = Size;
        return;
    }
    for ( Bits = p->Rows[Min]; Bits && Size+1 < p->nBest && p->nVisits <= 2048; Bits &= Bits-1 )
    {
        Bit = Bits & (0u - Bits);
        Pdr2_MicPickHits(p, Selected | Bit, Size+1);
    }
}

/**Function*************************************************************

  Synopsis    [Uses successive transition models to propose a small inductive core.]

  Description [Each row names literals that would exclude a previous target
  assignment. A hit only selects the next SAT assumptions. The returned
  reduction must exclude initial states and pass the full induction query.]

***********************************************************************/
static int Pdr2_ManMicHitModels( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube,
    Vec_Int_t * vSource, Vec_Int_t * vTry, Vec_Int_t * vCore )
{
    Pdr2_MicHits_t Hits = { {0}, 0, {0}, 1, 0, 0 };
    int i, Lit, Ret, Trials, n = Vec_IntSize(vCube), Limit = p->nMicGroup == 7 ? 12 : 24;
    unsigned All = (1u << n) - 1;
    Vec_IntForEachEntry(vCube, Lit, i)
        if ( Pdr2_ManLitIsNonInit(p, Lit) ) { Hits.Rows[0] |= 1u << i; Hits.Sizes[0]++; }
    if ( !Hits.Rows[0] ) return 0;
    for ( Trials = 0; Trials < Limit; )
    {
        Hits.Best = All; Hits.nBest = n; Hits.nVisits = 0;
        Pdr2_MicPickHits(&Hits, 0, 0);
        if ( Hits.Best == All ) break;
        Vec_IntClear(vTry);
        Vec_IntForEachEntry(vCube, Lit, i)
            if ( Hits.Best & (1u << i) ) Vec_IntPush(vTry, Lit);
        Trials++;
        Ret = Pdr2_ManTryDrop(p, pSat, vTry, 0, vSource);
        if ( Ret < 0 ) break;
        if ( Ret == 1 )
        {
            if ( Pdr2_ManInductiveCore(p, pSat, vCore) )
            {
                Vec_IntClear(vCube); Vec_IntAppend(vCube, vCore);
            }
            break;
        }
        Vec_IntForEachEntry(vCube, Lit, i)
            if ( !(Hits.Best & (1u << i)) &&
                 Gip_SolverLitValue(Pdr2_SolverActual(pSat), Pdr2_LitLi(p, Lit)) != GIP_TRUE )
            {
                Hits.Rows[Hits.nRows] |= 1u << i;
                Hits.Sizes[Hits.nRows]++;
            }
        if ( !Hits.Rows[Hits.nRows] ) break;
        Hits.nRows++;
    }
    return Trials;
}

/**Function*************************************************************

  Synopsis    [Drops groups of target literals with a fixed source clause.]

  Description [All candidate cubes are subsets of the original cube. Their
  blocking clauses imply the original blocking clause, so a proof with the
  original source clause establishes relative induction for the reduced
  cube. The SAT solver can retain assumption decisions and guarded learnt
  clauses for this whole sequence.]

***********************************************************************/
static void Pdr2_ManMicBatch( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver(p, Frame-1);
    Vec_Int_t * vSource = Vec_IntAlloc(Vec_IntSize(vCube)), * vTry = Vec_IntAlloc(Vec_IntSize(vCube));
    Vec_Int_t * vCore = Vec_IntAlloc(Vec_IntSize(vCube));
    int i, Lit, End, Begin, Width, Ret, fBatch, Trials = 0, Original = Vec_IntSize(vCube);
    int Limit = p->nMicGroup == 4 ? 6 : 24;
    abctime Start = Abc_Clock();
    p->nMics++;
    p->nMicLits += Original;
    Pdr2_ManSortByAct(p, vCube, 0);
    Vec_IntForEachEntry(vCube, Lit, i) Vec_IntPush(vSource, Abc_LitNot(Lit));
    Pdr2_ManSetMicDomain(p, pSat, vCube);
    fBatch = p->nMicGroup != 6 && !pSat->pShared && !pSat->pLoaded && pSat->fTempDomain;
    if ( fBatch )
        Gip_SolverStartBatch( pSat, Original );
    End = Original;
    Width = Abc_MaxInt(1, Original/2);
    if ( p->nMicGroup >= 7 && Original <= 20 && !p->pInitSat )
    {
        Trials = Pdr2_ManMicHitModels(p, pSat, vCube, vSource, vTry, vCore);
        End = 0;
    }
    while ( End > 0 && Vec_IntSize(vCube) > 1 && Trials < Limit )
    {
        Begin = Abc_MaxInt(0, End-Width);
        Vec_IntClear(vTry);
        Vec_IntForEachEntry(vCube, Lit, i)
            if ( i < Begin || i >= End ) Vec_IntPush(vTry, Lit);
        Ret = 0;
        if ( Vec_IntSize(vTry) && !Pdr2_LitsAreInit(p, vTry) )
        {
            Trials++;
            Ret = Pdr2_ManTryDrop(p, pSat, vTry, 0, vSource);
            if ( Ret < 0 ) break;
            if ( Ret == 1 && Pdr2_ManInductiveCore(p, pSat, vCore) )
            {
                Vec_IntClear(vCube); Vec_IntAppend(vCube, vCore);
                End = Abc_MinInt(Begin, Vec_IntSize(vCube));
                Width = Abc_MaxInt(1, Abc_MinInt(2 * Width, Vec_IntSize(vCube)/2));
                continue;
            }
        }
        if ( End - Begin > 1 ) Width = (End - Begin) / 2;
        else End--;
    }
    if ( fBatch )
        p->nGroupLevels += Gip_SolverStopBatch( pSat );
    Pdr2_ManUnsetMicDomain(p, pSat);
    p->nGroupQueries += Trials;
    p->nGroupLits += Original - Vec_IntSize(vCube);
    Pdr2_ManActBump(p, vCube);
    Vec_IntFree(vSource); Vec_IntFree(vTry); Vec_IntFree(vCore);
    p->timeMic += Abc_Clock() - Start;
}

/**Function*************************************************************

  Synopsis    [Generalizes toward an inductive clause in a weaker future frame.]

  Description [A failed push exhibits a source state outside the cube. Join
  that state with the cube by keeping their common literals. The new cube
  excludes this very transition from its relative-induction query. Continue
  only while the cube shrinks and still excludes initial states. Every
  retained result has an explicit induction proof at its reported frame.]

  SideEffects []

***********************************************************************/
static int Pdr2_ManJoinPush( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube, int * pFrame, int * pInf )
{
    int i, k, Lit, Ret, Best, Level = Pdr2_ManLevel(p);
    int Future = p->nJoinPush == 2 && Frame < Level ? Frame : -1;
    int Result = 0;
    Vec_Int_t * vTry = Vec_IntDup(vCube), * vCore = Vec_IntAlloc(Vec_IntSize(vCube));
    Gip_Solver_t * pSat = Future < 0 ? p->pInf : Pdr2_ManSolver(p, Future);
    p->nJoinTries++;
    Pdr2_ManSetMicDomain(p, pSat, vCube);
    for ( k = 0; k < 5; ++k )
    {
        p->nJoinQueries++;
        Ret = Pdr2_ManSolveRelative(p, pSat, vTry, 1, NULL);
        if ( Ret < 0 ) break;
        if ( Ret == 1 )
        {
            if ( Pdr2_ManInductiveCore(p, pSat, vCore) )
            {
                p->nJoinProofs++;
                if ( Future < 0 ) *pInf = 1;
                else *pFrame = Future + 1;
                Result = 1;
            }
            break;
        }
        Best = 0;
        Vec_IntForEachEntry(vTry, Lit, i)
            if ( Pdr2_ManLitValue(p, pSat, Lit) == GIP_TRUE ) Vec_IntWriteEntry(vTry, Best++, Lit);
        if ( Best == Vec_IntSize(vTry) ) break;
        Vec_IntShrink(vTry, Best);
        if ( !Best || Pdr2_LitsAreInit(p, vTry) ) break;
    }
    Pdr2_ManUnsetMicDomain(p, pSat);
    if ( !Result && p->nJoinPush == 3 && !p->fQueryCut && Vec_IntSize(vTry) &&
         Vec_IntSize(vTry) < Vec_IntSize(vCube) && !Pdr2_LitsAreInit(p, vTry) )
    {
        pSat = Pdr2_ManSolver(p, Frame - 1);
        p->nJoinQueries++;
        if ( Pdr2_ManSolveRelative(p, pSat, vTry, 1, NULL) == 1 && Pdr2_ManInductiveCore(p, pSat, vCore) )
        {
            p->nJoinLocal++;
            Result = 1;
        }
    }
    if ( Result )
    {
        Vec_IntClear(vCube);
        Vec_IntAppend(vCube, vCore);
    }
    Vec_IntFree(vCore);
    Vec_IntFree(vTry);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Resolves a blocked cube against clauses valid at its frame.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManResolveCube( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube )
{
    Pdr2_Cube_t Flipped = {0};
    Pdr2_Lem_t * pLem;
    Vec_Ptr_t * vOcc;
    int i, j, Lit, End, nBefore = Vec_IntSize(vCube);
    word Sign = 0;
    Vec_IntForEachEntry( vCube, Lit, i )
    {
        p->pLitMark[Lit] = 1;
        Sign |= Pdr2_LitSign(Lit);
    }
    // For pivot x in D & x, look for a stored cube contained in D & !x.
    // If both halves are blocked through Frame, D is blocked there too.
    // The signature is only a filter; every hit is checked literal by literal.
    for ( i = nBefore - 1; i >= 0 && Vec_IntSize(vCube) > 1; --i )
    {
        Lit = Vec_IntEntry(vCube,i);
        p->pLitMark[Lit] = 0; p->pLitMark[Lit^1] = 1;
        Flipped.nLits = Vec_IntSize(vCube);
        Flipped.Sign = Sign | Pdr2_LitSign(Lit^1);
        vOcc = &p->pOcc[Lit^1];
        End = Abc_MaxInt(0, Vec_PtrSize(vOcc) - p->nResolveLimit);
        for ( j = Vec_PtrSize(vOcc) - 1; j >= End; --j )
        {
            pLem = (Pdr2_Lem_t *)Vec_PtrEntry(vOcc,j);
            if ( pLem->fRemoved || (pLem->iFrame != -1 && (Frame == -1 || pLem->iFrame < Frame)) ) continue;
            if ( Pdr2_CubeSubsumeMarked(p, pLem->pCube, &Flipped) ) break;
        }
        p->pLitMark[Lit^1] = 0;
        if ( j < End ) p->pLitMark[Lit] = 1;
        else Vec_IntDrop(vCube,i);
    }
    Vec_IntForEachEntry( vCube, Lit, i ) p->pLitMark[Lit] = 0;
    if ( Vec_IntSize(vCube) < nBefore )
    {
        p->nResolveCubes++; p->nResolveLits += nBefore - Vec_IntSize(vCube);
        if ( Gip_OptionGet("PDR2_RESOLVE_CHECK") )
        {
            int fInit = Pdr2_LitsAreInit(p, vCube);
            assert(!fInit || p->fInitUnknown);
            (void)fInit;
            if ( !p->fInitUnknown ) Pdr2_ManTimeGenCheck(p, Frame == -1 ? -1 : Frame-1, vCube);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Generalizes a blocked obligation into a lemma.]

  Description [Returns 1 if an inductive invariant was found.]

***********************************************************************/
static int Pdr2_ManGeneralize( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, pObl->iFrame - 1 );
    Vec_Int_t * vMic = Vec_IntAlloc( 100 );
    Pdr2_MicPar_t Par;
    int iFrame, RetValue, fPredicted = 0, fJoined = 0, GenFrame = pObl->iFrame, fCoreInf = 0;
    Par.nLimit = 0;
    Par.nMax   = 0;
    Par.nLevel = 0;
    if ( p->pPars->fDynamic )
    {
        // the effort grows with the activity of the obligations this one leads to (rIC3's dynamic mode)
        if ( pObl->pNext )
        {
            Pdr2_Obl_t * pNext = pObl->pNext;
            double Act = pNext->Act;
            int c;
            for ( c = 0; c < 2 && pNext->pNext; c++ )
            {
                pNext = pNext->pNext;
                Act = Abc_MaxDouble( Act, pNext->Act );
            }
            if ( Act >= 40.0 && p->pPars->nDynAct <= 10 )
            {
                Par.nLimit = (int)floor( pow(Act - 40.0, 0.45) * 2.0 + 5.0 + 0.5 );
                Par.nMax   = 5;
                Par.nLevel = 1;
            }
            else if ( Act >= (double)p->pPars->nDynAct )
            {
                Par.nLimit = 1;
                Par.nMax   = (int)(Act - p->pPars->nDynAct) / 10 + 2;
                Par.nLevel = 1;
            }
        }
        // the lemmas blocking bad states decide how many of them must be enumerated: keep CTG for them
        if ( p->pPars->fTopCtg && pObl->nDepth == 0 && Par.nLevel == 0 )
        {
            Par.nLimit = 1;
            Par.nMax   = p->pPars->nCtgMax;
            Par.nLevel = 1;
        }
        // unbounded CTG effort can flood the frames with lemmas
        Par.nLimit = Abc_MinInt( Par.nLimit, p->pPars->nDynLimitMax );
        Par.nMax   = Abc_MinInt( Par.nMax, p->pPars->nCtgMax );
    }
    else if ( p->pPars->fCtg )
    {
        Par.nLimit = p->pPars->nCtgLimit;
        Par.nMax   = p->pPars->nCtgMax;
        Par.nLevel = 1;
    }
    if ( !Pdr2_ManInductiveCore( p, pSat, vMic ) )
    {
        // cannot happen for an obligation that excludes the initial states
        Pdr2_CubeToVec( pObl->pState, vMic );
    }
    else if ( p->nGenTimeMode && p->pPars->fTimeGen )
    {
        // The blocking query already establishes relative induction up to
        // its dependency frame. Generalize there, without first re-proving
        // the unchanged core in every intermediate frame. Initial-state
        // exclusion was checked (and repaired if necessary) above.
        int T = p->iCoreFrame;
        fCoreInf = p->nGenTimeMode >= 2 && T >= GIP_FRAME_INF;
        GenFrame = Abc_MaxInt(GenFrame, T >= GIP_FRAME_INF ? Pdr2_ManLevel(p) :
                                      Abc_MinInt(Pdr2_ManLevel(p), T + 1));
        p->nGenTimeJumps += GenFrame > pObl->iFrame;
        p->nGenTimeInf += fCoreInf;
        if ( p->fTimeGenCheck && (fCoreInf || GenFrame > pObl->iFrame) )
            Pdr2_ManTimeGenCheck(p, fCoreInf ? -1 : GenFrame-1, vMic);
    }
    if ( p->nJoinPush && !fCoreInf && Vec_IntSize(vMic) >= 2 )
        fJoined = Pdr2_ManJoinPush(p, GenFrame, vMic, &GenFrame, &fCoreInf);
    if ( p->nPredictMode && !fCoreInf && !fJoined )
        fPredicted = Pdr2_ManPredictParent( p, GenFrame, vMic );
    if ( p->nResolveLimit && Vec_IntSize(vMic) > 1 )
        Pdr2_ManResolveCube(p, fCoreInf ? -1 : GenFrame, vMic);
    // Select generalization effort inside the same frame database. Every
    // accepted drop still needs an UNSAT induction query. The rate-based
    // selector samples CTG periodically so it can recover from a poor phase.
    if ( Par.nLevel > 0 && !p->pPars->fDynamic &&
         ((p->pPars->nCtgSmall && Vec_IntSize(vMic) <= p->pPars->nCtgSmall) ||
          (p->pPars->nCtgMinRate && p->nMicDropOk + p->nMicDropFail >= 256 &&
           100 * p->nMicDropOk < p->pPars->nCtgMinRate * (p->nMicDropOk + p->nMicDropFail) &&
           (p->nMics & 15) != 0)) )
    {
        Par.nLevel = 0;
        p->nCtgBypassed++;
    }
    if ( fCoreInf || fJoined || (fPredicted && p->nPredictMode == 2) ||
         (Gip_OptionGet("PDR2_MIC_CORE_ONLY") && atoi(Gip_OptionGet("PDR2_MIC_CORE_ONLY"))) )
        Pdr2_ManActBump( p, vMic );
    else if ( p->nMicGap && Pdr2_ManLevel(p) - GenFrame >= p->nMicGap )
    {
        // Keep the proved inductive core. Only optional literal removal is
        // omitted; placement, subsumption and proof checks remain unchanged.
        p->nMicGapSkipped++;
        Pdr2_ManActBump(p, vMic);
    }
    else if ( p->nMicGroup >= 4 && Vec_IntSize(vMic) >= 2 )
        Pdr2_ManMicBatch(p, GenFrame, vMic);
    else if ( p->nMicGroup && Vec_IntSize(vMic) >= (p->nMicGroup == 3 ? 12 : 2) )
        Pdr2_ManMicGroup(p, GenFrame, vMic);
    else if ( p->pPars->nMicMode == 1 )
        Pdr2_ManMicTreb( p, GenFrame, vMic );
    else
        Pdr2_ManMic( p, GenFrame, vMic, NULL, Par );
    if ( fCoreInf )
        iFrame = Pdr2_ManLevel(p) + 1, p->fPushInf = 1;
    else
        iFrame = Pdr2_ManPushLemma( p, GenFrame, vMic );
    Pdr2_ManRequeue( p, pObl, iFrame );
    RetValue = Pdr2_ManAddLemma( p, iFrame - 1, vMic, 0, pObl, NULL );
    if ( p->fPushInf && RetValue == 0 && iFrame - 1 == Pdr2_ManLevel(p) )
        Pdr2_ManPromoteLast( p, iFrame - 1, vMic );
    else if ( p->pPars->fInfPromote && RetValue == 0 && iFrame - 1 == Pdr2_ManLevel(p) && Vec_PtrSize(Pdr2_ManFrame(p, iFrame - 1)) > 0 )
    {
        // a lemma pushed up to the last frame that is inductive relative to the invariant lemmas
        // alone holds in every reachable state: it need not wait for the end of the level
        Pdr2_Lem_t * pLem = (Pdr2_Lem_t *)Vec_PtrEntryLast( Pdr2_ManFrame(p, iFrame - 1) );
        int k, Lit, fSame = pLem->pCube->nLits == Vec_IntSize(vMic);
        for ( k = 0; fSame && k < pLem->pCube->nLits; k++ )
            if ( Vec_IntFind(vMic, pLem->pCube->Lits[k]) == -1 )
                fSame = 0;
        if ( fSame )
        {
            p->nInfPromoteCalls++;
            p->nPropInfCalls++;
            Pdr2_CubeToVec( pLem->pCube, vMic );
            k = Pdr2_ManSolveRelativeJftr( p, p->pInf, vMic, 1, NULL, Pdr2_ManJftrReq(p, PDR2_JQ_INF, GIP_JFTR_WALK) );
            if ( k == 1 )
            {
                if ( pLem->pObl )
                    Pdr2_QueueRemove( p, pLem->pObl );
                Pdr2_ManAddInfLemma( p, iFrame - 1, pLem );
                p->nInfPromoted++;
            }
            else if ( k == 0 && p->pPars->fCtiCache )
                Pdr2_LemCacheCti( p, pLem, p->pInf, -1 );
            (void)Lit;
        }
    }
    Vec_IntFree( vMic );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    [Tries a short prefix before the full relative blocking query.]

  Description []

***********************************************************************/
// A blocked prefix also blocks the full cube. A satisfiable prefix does not
// supply a predecessor of the full cube, so retry the full query before lifting.
// Excluding initial states is required when the prefix strengthens the query.
static int Pdr2_ManSolveBlockedInt( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube )
{
    int i, RetValue = 0, nPrefix = p->pPars->nPrefix;
    int Request = Pdr2_ManJftrReq( p, PDR2_JQ_BLOCK, GIP_JFTR_WALK_SHRINK );
    if ( nPrefix && Vec_IntSize(vCube) >= 4 * nPrefix )
    {
        Vec_Int_t * vPrefix = Vec_IntAlloc( nPrefix );
        for ( i = 0; i < nPrefix; i++ )
            Vec_IntPush( vPrefix, Vec_IntEntry(vCube, i) );
        if ( !Pdr2_LitsAreInit(p, vPrefix) )
        {
            p->nPrefixCalls++;
            RetValue = Pdr2_ManSolveRelativeJftr( p, pSat, vPrefix, p->pPars->fBlockInduct, NULL, Request );
            if ( RetValue == 1 )
            {
                p->nPrefixProved++;
                p->nPrefixSaved += Vec_IntSize(vCube) - nPrefix;
            }
        }
        Vec_IntFree( vPrefix );
        if ( RetValue != 0 )
            return RetValue;
    }
    return Pdr2_ManSolveRelativeJftr( p, pSat, vCube, p->pPars->fBlockInduct, NULL, Request );
}

/**Function*************************************************************

  Synopsis    [Runs and measures a blocking query for an obligation cube.]

  Description []

***********************************************************************/
static int Pdr2_ManSolveBlocked( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube )
{
    int Result;
    assert(!p->fInputBlockQuery);
    p->fInputBlockQuery = 1;
    Result = Pdr2_ManSolveBlockedInt(p, pSat, vCube);
    p->fInputBlockQuery = 0;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Blocks all obligations of frames up to the current level.]

  Description [Returns PDR2_BLOCK_SUCCESS when the queue is empty,
  PDR2_BLOCK_FAILURE when an obligation reached the initial states
  (p->pCexObl is set), PDR2_BLOCK_PROVED when a frame became empty,
  PDR2_BLOCK_TIMEOUT on a resource limit.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManBlock( Pdr2_Man_t * p )
{
    Pdr2_Obl_t * pObl, * pNew;
    Pdr2_Cube_t * pCube;
    Vec_Int_t * vPred = Vec_IntAlloc( 100 );
    Vec_Int_t * vInputs = Vec_IntAlloc( 100 );
    Vec_Int_t * vPpis = Vec_IntAlloc( 100 );
    abctime clk;
    int iFound, fInf, RetValue, Result = PDR2_BLOCK_SUCCESS;
    // (not when resuming a slice that ended inside this loop: the uninterrupted run would not
    // collect there, and a collection rebuilds the index, whose order steers the trajectory)
    if ( !p->fBlockCut )
        Pdr2_ManCollectGarbage( p, 0 );
    p->fBlockCut = 0;
    while ( 1 )
    {
        // a slice (or the deadline) ends between obligations, before the next one is popped, so
        // that the queue is left exactly as it is and a resumed run follows the same trajectory
        if ( Pdr2_ManTimedOut(p) )
        {
            p->fBlockCut = 1;
            Result = PDR2_BLOCK_TIMEOUT;
            break;
        }
        if ( !(pObl = Pdr2_QueuePop( p, Pdr2_ManLevel(p) )) )
            break;
        // a level that takes too long restarts its obligation queue (the lemmas are kept): the
        // trajectory of a level is chaotic, and a fresh start from the bad states often avoids
        // a run of long cubes; the budget doubles with every restart
        if ( p->pPars->nLevelRestart > 0 && (double)(p->nProps - p->nPropsRestartStart) > p->LevelRestartBudget )
        {
            if ( p->pPars->fVerbose && !p->pPars->fSilent )
                Abc_Print( 1, "Restarting level %d after %.0f M propagations (%d obligations at this level, %d queued).\n",
                    Pdr2_ManLevel(p), p->LevelRestartBudget / 1e6, p->nOblsLevel, Vec_PtrSize(p->vQueue) + 1 );
            p->nLevelRestarts++;
            p->LevelRestartBudget *= 2;
            p->nPropsRestartStart = p->nProps;
            p->RandState = p->RandState * 2654435761u + 12345u + (unsigned)p->nLevelRestarts;
            Pdr2_OblDeref( pObl );
            Pdr2_QueueClear( p );
            continue;
        }
        // a dynamic phase ends early when a level needs very many obligations (weak generalization)
        p->nOblsLevel++;
        if ( p->fAlternate && p->pPars->fDynamic && p->pPars->nDynExplode &&
             p->nOblsLevel > p->pPars->nDynExplode && p->nOblsLevel > 3 * p->nOblsLevelMax )
        {
            p->nOblsLevelMax = p->nOblsLevel;
            if ( p->pPars->fVerbose && !p->pPars->fSilent )
                Abc_Print( 1, "Ending the dynamic phase at level %d (%d obligations at this level).\n", Pdr2_ManLevel(p), p->nOblsLevel );
            Pdr2_QueuePush( p, pObl );
            Pdr2_OblDeref( pObl );
            Result = PDR2_BLOCK_RESTART;
            break;
        }
        if ( p->fReachCex && Pdr2_ManReachTryCex(p, pObl) )
        {
            p->pCexObl = pObl;
            Result = PDR2_BLOCK_FAILURE;
            break;
        }
        // an obligation containing an initial state is a counterexample (if it is not spurious)
        if ( Pdr2_CubeIsInit(p, pObl->pState) )
        {
            RetValue = p->fInitUnknown ? -1 : p->fAbsActive ? Pdr2_ManAbsCheckCex( p, pObl ) : 1;
            if ( RetValue == -1 )
            {
                // the deadline canceled the check: the obligation goes back to the queue
                Pdr2_QueuePush( p, pObl );
                Pdr2_OblDeref( pObl );
                Result = PDR2_BLOCK_TIMEOUT;
                break;
            }
            if ( RetValue == 0 )
            {
                // the abstraction was refined: all obligations are stale
                Pdr2_QueueClear( p );
                Pdr2_OblDeref( pObl );
                continue;
            }
            p->pCexObl = pObl;
            Result = PDR2_BLOCK_FAILURE;
            break;
        }
        // skip obligations already blocked by lemmas
        iFound = Pdr2_ManTrivialContained( p, pObl->iFrame, pObl->pState, &fInf );
        if ( iFound >= 0 || fInf )
        {
            if ( !fInf )
                Pdr2_ManRequeue( p, pObl, iFound + 1 );
            Pdr2_OblDeref( pObl );
            continue;
        }
        if ( p->pPars->fSemContain )
        {
            // the frame's lemmas may exclude the cube without any one of them containing it
            RetValue = Pdr2_ManSolveContained( p, Pdr2_ManSolver(p, pObl->iFrame), pObl->pState );
            if ( RetValue == 1 )
            {
                p->nSemContained++;
                Pdr2_ManRequeue( p, pObl, pObl->iFrame + 1 );
                Pdr2_OblDeref( pObl );
                continue;
            }
        }
        pObl->Act += 1.0;
        if ( p->pPars->fDropPo && (p->pPars->fDynamic ? (p->pPars->nDynDropAct > 0 && pObl->Act > p->pPars->nDynDropAct) : pObl->Act > p->pPars->nDropAct) )
        {
            p->nOblsDropped++;
            Pdr2_OblDeref( pObl );
            continue;
        }
        // is the obligation blocked by the previous frame?
        clk = Abc_Clock();
        Pdr2_CubeToVec( pObl->pState, p->vLits4 );
        Pdr2_ManSortByAct( p, p->vLits4, 0 );
        RetValue = Pdr2_ManSolveBlocked( p, Pdr2_ManSolver(p, pObl->iFrame - 1), p->vLits4 );
        p->timeBlocked += Abc_Clock() - clk;
        if ( RetValue == -1 )
        {
            Pdr2_QueuePush( p, pObl );
            Pdr2_OblDeref( pObl );
            Result = PDR2_BLOCK_TIMEOUT;
            break;
        }
        if ( RetValue == 1 )
        {
            int fProved = Pdr2_ManGeneralize( p, pObl );
            Pdr2_OblDeref( pObl );
            if ( fProved )
            {
                Result = PDR2_BLOCK_PROVED;
                break;
            }
            continue;
        }
        // create the predecessor obligation
        Pdr2_ManGetPred( p, 1, vPred, vInputs );
        Pdr2_ManAbsProject( p, vPred, vPpis );
        pCube = Pdr2_CubeAllocVec( vPred );
        pNew = Pdr2_OblAlloc( p, pObl->iFrame - 1, pCube, vInputs, vPpis, pObl->nDepth + 1, pObl );
        Pdr2_CubeDeref( pCube );
        Pdr2_QueuePush( p, pNew );
        Pdr2_OblDeref( pNew );
        Pdr2_QueuePush( p, pObl );
        Pdr2_OblDeref( pObl );
    }
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    Vec_IntFree( vPpis );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Propagates lemmas to higher frames.]

  Description [Returns 1 if a frame became empty (an inductive invariant
  was found).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_LemCompareByLen( const void * p1, const void * p2 )
{
    const Pdr2_Lem_t * pLem1 = *(Pdr2_Lem_t * const *)p1;
    const Pdr2_Lem_t * pLem2 = *(Pdr2_Lem_t * const *)p2;
    int Diff = pLem1->pCube->nLits - pLem2->pCube->nLits;
    return Diff ? Diff : pLem1->iSlot - pLem2->iSlot;
}

/**Function*************************************************************

  Synopsis    [Attempts to block a predecessor that prevented lemma propagation.]

  Description []

***********************************************************************/
// A failed push supplies a predecessor in frame k. If it is inductive relative
// to frame k-1, blocking it strengthens frame k and may allow the push to pass.
// As in rIC3's propagate(), use plain MIC and bound the number of retries.
// Returns 2 on convergence, 1 when strengthened, 0 when not blockable, -1 on a cut.
static int Pdr2_ManBlockCtp( Pdr2_Man_t * p, int k, Vec_Int_t * vPred, Vec_Int_t * vInputs, Vec_Int_t * vCore )
{
    Pdr2_MicPar_t Par = { 0, 0, 0 };
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, k - 1 );
    int RetValue;
    p->nCtpCalls++;
    Pdr2_ManGetPred( p, 0, vPred, vInputs );
    Pdr2_ManAbsProject( p, vPred, NULL );
    if ( p->fQueryCut )
        return -1;
    if ( Pdr2_LitsAreInit(p, vPred) )
        return 0;
    Pdr2_ManSortByAct( p, vPred, 0 );
    RetValue = Pdr2_ManSolveRelativeJftr( p, pSat, vPred, 1, NULL, Pdr2_ManJftrReq(p, PDR2_JQ_MIC, GIP_JFTR_WALK) );
    if ( RetValue != 1 )
        return RetValue;
    if ( !Pdr2_ManInductiveCore( p, pSat, vCore ) )
        return 0;
    Pdr2_ManMic( p, k, vCore, NULL, Par );
    if ( p->fQueryCut )
        return -1;
    p->nCtpBlocked++;
    return Pdr2_ManAddLemma( p, k, vCore, 0, NULL, NULL ) ? 2 : 1;
}
static int Pdr2_ManPropagate( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vSnap = Vec_PtrAlloc( 1000 );
    Vec_Int_t * vCore = Vec_IntAlloc( 100 );
    Vec_Int_t * vPred = p->pPars->nCtpMax ? Vec_IntAlloc( 100 ) : NULL;
    Vec_Int_t * vInputs = p->pPars->nCtpMax ? Vec_IntAlloc( 100 ) : NULL;
    Vec_Ptr_t * vFrame;
    Pdr2_Lem_t * pLem;
    abctime clk = Abc_Clock();
    int k, i, j, RetValue, Result = 0, Level = Pdr2_ManLevel(p);
    Pdr2_ManCollectGarbage( p, 0 );
    for ( k = Abc_MaxInt(1, p->iEarly); k < Level; k++ )
    {
        vFrame = Pdr2_ManFrame( p, k );
        // Preserve input order for equal lengths on every qsort implementation.
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vFrame, pLem, i )
            pLem->iSlot = i;
        qsort( Vec_PtrArray(vFrame), (size_t)Vec_PtrSize(vFrame), sizeof(void *), Pdr2_LemCompareByLen );
        Vec_PtrClear( vSnap );
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vFrame, pLem, i )
        {
            pLem->iSlot = i;
            Vec_PtrPush( vSnap, pLem );
        }
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vSnap, pLem, i )
        {
            if ( pLem->fRemoved )
                continue;
            if ( p->pPars->fCtiCache && Pdr2_LemCtiValid( p, pLem, k ) )
            {
                p->nPropSkipped++;
                continue;
            }
            for ( j = 0; ; j++ )
            {
                Pdr2_CubeToVec( pLem->pCube, p->vLits4 );
                Pdr2_ManSortByAct( p, p->vLits4, 0 );
                p->nPropCalls++;
                // the model goes to the predecessor extraction of Pdr2_ManBlockCtp when j < nCtpMax
                RetValue = Pdr2_ManSolveRelativeJftr( p, Pdr2_ManSolver(p, k), p->vLits4, 0, NULL,
                    Pdr2_ManJftrReq(p, PDR2_JQ_PROP, j < p->pPars->nCtpMax ? GIP_JFTR_WALK_SHRINK : GIP_JFTR_ANSWER) );
                if ( RetValue == -1 )
                {
                    p->fSweepCut = 1;
                    goto finish;
                }
                if ( RetValue == 1 )
                    break;
                if ( p->pPars->fCtiCache )
                    Pdr2_LemCacheCti( p, pLem, Pdr2_ManSolver(p, k), k );
                if ( j == p->pPars->nCtpMax )
                    break;
                RetValue = Pdr2_ManBlockCtp( p, k, vPred, vInputs, vCore );
                if ( RetValue == -1 )
                {
                    p->fSweepCut = 1;
                    goto finish;
                }
                if ( RetValue == 2 )
                {
                    Result = 1;
                    goto finish;
                }
                if ( RetValue == 0 || pLem->fRemoved )
                {
                    RetValue = 0;
                    break;
                }
            }
            if ( RetValue == 0 )
                continue;
            p->nCtpPushed += j > 0;
            if ( !Pdr2_ManInductiveCore( p, Pdr2_ManSolver(p, k), vCore ) )
                Pdr2_CubeToVec( pLem->pCube, vCore );
            {
                int iTo = k + 1, fToInf = 0;
                if ( p->pPars->fTimeGen )
                {
                    // time generalization (see Pdr2_ManPushLemma)
                    int T = p->iCoreFrame;
                    if ( T >= GIP_FRAME_INF )
                        fToInf = 1, iTo = Level, p->nTgInf++;
                    else if ( T + 1 > k + 1 && p->pPars->fTimeGen >= 2 )
                    {
                        iTo = Abc_MinInt( T + 1, Level );
                        p->nTgJumps++;
                        p->nTgFrames += iTo - (k + 1);
                        if ( p->fTimeGenCheck )
                            Pdr2_ManTimeGenCheck( p, iTo - 1, vCore );
                    }
                }
                if ( pLem->pObl && pLem->pObl->iFrame < iTo + 1 && Pdr2_QueueRemove( p, pLem->pObl ) )
                    Pdr2_ManRequeue( p, pLem->pObl, iTo + 1 );
                Pdr2_ManAddLemma( p, iTo, vCore, 1, pLem->pObl, pLem );
                if ( fToInf )
                    Pdr2_ManPromoteLast( p, iTo, vCore );
                if ( p->fTimeGenCheck )
                    Pdr2_ManCheckIds( p );
            }
        }
        Pdr2_ManCollectGarbage( p, 0 );
        if ( Vec_PtrSize(vFrame) == 0 )
        {
            Result = 1;
            break;
        }
    }
    if ( !Result )
        p->iEarly = Level;
finish:
    Pdr2_ManCollectGarbage( p, 0 );
    Vec_PtrFree( vSnap );
    Vec_IntFree( vCore );
    Vec_IntFreeP( &vPred );
    Vec_IntFreeP( &vInputs );
    p->timeProp += Abc_Clock() - clk;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Moves lemmas of the last frame to frame infinity.]

  Description [A lemma inductive relative to the inf lemmas is an
  invariant. When it is not, the counterexample to propagation is used
  to pick another last-frame lemma to prove first.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManPropInfRec( Pdr2_Man_t * p, Vec_Ptr_t * vLast, Vec_Int_t * vCtp )
{
    Pdr2_Cube_t * pCtp;
    Pdr2_Lem_t * pLem = NULL, * pTemp;
    Vec_Int_t * vLits, * vPred, * vInputs;
    int i, RetValue, Result = 0;
    pCtp = Pdr2_CubeAllocVec( vCtp );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, vLast, pTemp, i )
        if ( Pdr2_CubeSubsume( pTemp->pCube, pCtp ) )
        {
            pLem = pTemp;
            Vec_PtrWriteEntry( vLast, i, Vec_PtrEntryLast(vLast) );
            Vec_PtrPop( vLast );
            break;
        }
    Pdr2_CubeDeref( pCtp );
    if ( pLem == NULL )
        return 0;
    vLits   = Vec_IntAlloc( 100 );
    vPred   = Vec_IntAlloc( 100 );
    vInputs = Vec_IntAlloc( 100 );
    while ( 1 )
    {
        Pdr2_CubeToVec( pLem->pCube, vLits );
        p->nPropInfCalls++;
        RetValue = Pdr2_ManSolveRelativeJftr( p, p->pInf, vLits, 1, NULL,
                                              Pdr2_ManJftrReq(p, PDR2_JQ_INF, GIP_JFTR_WALK) );
        if ( RetValue == 1 )
        {
            if ( pLem->pObl )
                Pdr2_QueueRemove( p, pLem->pObl );
            Pdr2_ManAddInfLemma( p, Pdr2_ManLevel(p), pLem );
            Result = 1;
            break;
        }
        if ( RetValue == -1 )
        {
            // the query was cut by the slice: the sweep is unfinished and its stage stays pending
            // (and restarts with a new order: not an exact resume, see Pdr2_ManSatSolve())
            p->fSweepCut = 1;
            break;
        }
        if ( p->pPars->fCtiCache )
            Pdr2_LemCacheCti( p, pLem, p->pInf, -1 );
        Pdr2_ManGetPred( p, 0, vPred, vInputs );
        if ( !Pdr2_ManPropInfRec( p, vLast, vPred ) )
            break;
    }
    Vec_IntFree( vLits );
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    return Result;
}
static void Pdr2_ManPropagateToInf( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vLast = Vec_PtrDup( Pdr2_ManFrame(p, Pdr2_ManLevel(p)) );
    Vec_Int_t * vLits = Vec_IntAlloc( 100 );
    Vec_Int_t * vPred = Vec_IntAlloc( 100 );
    Vec_Int_t * vInputs = Vec_IntAlloc( 100 );
    Pdr2_Lem_t * pLem;
    abctime clk = Abc_Clock();
    int RetValue;
    Pdr2_ManShufflePtr( p, vLast );
    while ( Vec_PtrSize(vLast) > 0 && !p->fSweepCut )
    {
        pLem = (Pdr2_Lem_t *)Vec_PtrPop( vLast );
        if ( pLem->fRemoved )
            continue;
        if ( p->pPars->fCtiCache && Pdr2_LemCtiValid( p, pLem, -1 ) )
        {
            p->nPropInfSkipped++;
            continue;
        }
        while ( 1 )
        {
            Pdr2_CubeToVec( pLem->pCube, vLits );
            p->nPropInfCalls++;
            RetValue = Pdr2_ManSolveRelativeJftr( p, p->pInf, vLits, 1, NULL,
                                                  Pdr2_ManJftrReq(p, PDR2_JQ_INF, GIP_JFTR_WALK) );
            if ( RetValue == 1 )
            {
                if ( pLem->pObl )
                    Pdr2_QueueRemove( p, pLem->pObl );
                Pdr2_ManAddInfLemma( p, Pdr2_ManLevel(p), pLem );
                break;
            }
            if ( RetValue == -1 )
            {
                p->fSweepCut = 1;
                break;
            }
            if ( p->pPars->fCtiCache )
                Pdr2_LemCacheCti( p, pLem, p->pInf, -1 );
            Pdr2_ManGetPred( p, 0, vPred, vInputs );
            if ( !Pdr2_ManPropInfRec( p, vLast, vPred ) )
                break;
        }
    }
    Vec_PtrFree( vLast );
    Vec_IntFree( vLits );
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    Pdr2_ManCollectGarbage( p, 0 );
    p->timePropInf += Abc_Clock() - clk;
}


/**Function*************************************************************

  Synopsis    [Maps a register literal to its current or next literal in the induction CNF.]

  Description []

***********************************************************************/
static int Pdr2_JointCnfLit( Cnf_Dat_t * pCnf, int Lit, int fNext )
{
    int Reg = Abc_Lit2Var( Lit );
    Aig_Obj_t * pObj = fNext ? Saig_ManLi(pCnf->pMan, Reg) : Saig_ManLo(pCnf->pMan, Reg);
    return Abc_Var2Lit( pCnf->pVarNums[Aig_ObjId(pObj)], Abc_LitIsCompl(Lit) );
}

/**Function*************************************************************

  Synopsis    [Certifies mutually inductive groups among the current frame lemmas.]

  Description [Each finite lemma initially excludes the reset states. A SAT
  model removes every candidate it violates in the successor. UNSAT proves
  all survivors together relative to the established invariant or to the
  preceding frame. An unfinished check leaves the frames untouched.]

***********************************************************************/
static void Pdr2_ManJointInduction( Pdr2_Man_t * p, int Seconds, int Max, int fFinite )
{
    abctime Start = Abc_Clock(), Stop = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    int Level = Pdr2_ManLevel(p), i, j, k, Count, Live, Rounds = 0, Added = 0, fProved = 0;
    Pdr2_Lem_t * pLem;
    Vec_Ptr_t * vCandidates, * vKnown;
    Vec_Int_t * vClause, * vAssume;
    Cnf_Dat_t * pCnf = NULL;
    sat_solver * pSat = NULL;
    if ( Level < 2 || p->GuardLit >= 0 || p->pPars->fUseAbs || p->pInitSat ||
         p->pPars->nInitLiReg || p->pPars->nPropLimit || Pdr2_ManPastDeadline(p) )
        return;
    if ( p->timeLimit && p->timeLimit < Stop ) Stop = p->timeLimit;
    if ( p->timeSlice && p->timeSlice < Stop ) Stop = p->timeSlice;
    vCandidates = Vec_PtrAlloc( Max );
    vKnown = Vec_PtrDup( p->vInf );
    if ( fFinite )
    {
        // F_{Level-1} holds in every source frame below Level. If H also
        // holds at reset and F_{Level-1} & H & T => H', it can be added to
        // every frame through Level in one step.
        Vec_PtrAppend( vKnown, Pdr2_ManFrame(p, Level - 1) );
        Vec_PtrAppend( vKnown, Pdr2_ManFrame(p, Level) );
    }
    vClause = Vec_IntAlloc( Max );
    vAssume = Vec_IntAlloc( Max );
    for ( k = Level - fFinite; k > 0 && Vec_PtrSize(vCandidates) < Max; k-- )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p,k), pLem, i )
        {
            if ( !pLem->fRemoved && !Pdr2_CubeIsInit(p, pLem->pCube) )
                Vec_PtrPush( vCandidates, pLem );
            if ( Vec_PtrSize(vCandidates) == Max ) break;
        }
    Count = Live = Vec_PtrSize( vCandidates );
    if ( Count < 2 || Abc_Clock() >= Stop ) goto finish;
    // Keep all outputs free. The CNF has no frame clauses or property assumption.
    pCnf = Cnf_DeriveSimple( p->pAig, Aig_ManCoNum(p->pAig) );
    if ( !pCnf ) goto finish;
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars + 2 * Count );
    sat_solver_set_runtime_limit( pSat, Stop );
    sat_solver_set_runid( pSat, p->pPars->RunId );
    sat_solver_set_stop_func( pSat, p->pPars->pFuncStop );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( (i & 1023) == 0 && (Abc_Clock() >= Stop || Pdr2_ManPastDeadline(p)) ) goto finish;
        if ( !sat_solver_addclause(pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]) ) goto finish;
    }
    for ( k = 0; k < 2; k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, k ? vCandidates : vKnown, pLem, i )
        {
            Pdr2_Cube_t * pCube = pLem->pCube;
            int Enable = Abc_Var2Lit( pCnf->nVars + i, 0 );
            int Fail = Abc_Var2Lit( pCnf->nVars + Count + i, 0 );
            if ( (i & 63) == 0 && (Abc_Clock() >= Stop || Pdr2_ManPastDeadline(p)) ) goto finish;
            Vec_IntClear( vClause );
            if ( k ) Vec_IntPush( vClause, Abc_LitNot(Enable) );
            for ( j = 0; j < pCube->nLits; j++ )
                Vec_IntPush( vClause, Abc_LitNot(Pdr2_JointCnfLit(pCnf, pCube->Lits[j], 0)) );
            if ( !sat_solver_addclause(pSat, Vec_IntArray(vClause), Vec_IntLimit(vClause)) ) goto finish;
            if ( !k ) continue;
            for ( j = 0; j < pCube->nLits; j++ )
            {
                int Pair[2] = { Abc_LitNot(Fail), Pdr2_JointCnfLit(pCnf, pCube->Lits[j], 1) };
                if ( !sat_solver_addclause(pSat, Pair, Pair + 2) ) goto finish;
            }
            Vec_IntPush( vAssume, Enable );
        }
    Vec_IntClear( vClause );
    for ( i = 0; i < Count; i++ )
        Vec_IntPush( vClause, Abc_Var2Lit(pCnf->nVars + Count + i, 0) );
    fProved = !sat_solver_addclause( pSat, Vec_IntArray(vClause), Vec_IntLimit(vClause) );
    while ( Live && !fProved && Abc_Clock() < Stop && !Pdr2_ManPastDeadline(p) )
    {
        int Prev = Live;
        int Ret = sat_solver_solve( pSat, Vec_IntArray(vAssume), Vec_IntLimit(vAssume), 0, 0, 0, 0 );
        Rounds++;
        if ( Ret == l_False ) { fProved = 1; break; }
        if ( Ret != l_True ) break;
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vCandidates, pLem, i )
        {
            Pdr2_Cube_t * pCube;
            if ( Abc_LitIsCompl(Vec_IntEntry(vAssume,i)) ) continue;
            pCube = pLem->pCube;
            for ( j = 0; j < pCube->nLits; j++ )
            {
                int Lit = Pdr2_JointCnfLit( pCnf, pCube->Lits[j], 1 );
                if ( sat_solver_var_value(pSat, Abc_Lit2Var(Lit)) == Abc_LitIsCompl(Lit) ) break;
            }
            if ( j < pCube->nLits ) continue;
            // Release the current-state clause and forbid this failure selector.
            Vec_IntWriteEntry( vAssume, i, Abc_Var2Lit(pCnf->nVars + Count + i, 1) );
            Live--;
        }
        if ( Live == Prev ) break;
    }
    if ( fProved )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vCandidates, pLem, i )
        {
            int Frame;
            Pdr2_Lem_t * pInf;
            if ( Abc_LitIsCompl(Vec_IntEntry(vAssume,i)) || pLem->fRemoved ) continue;
            Frame = pLem->iFrame;
            if ( fFinite )
            {
                if ( pLem->pObl && pLem->pObl->iFrame <= Level && Pdr2_QueueRemove(p, pLem->pObl) )
                    Pdr2_ManRequeue( p, pLem->pObl, Level + 1 );
                Pdr2_CubeToVec( pLem->pCube, vClause );
                Pdr2_ManAddLemma( p, Level, vClause, 1, pLem->pObl, pLem );
                p->iEarly = Abc_MinInt( p->iEarly, Frame );
                Added += pLem->fRemoved;
                continue;
            }
            if ( pLem->pObl ) Pdr2_QueueRemove( p, pLem->pObl );
            Pdr2_ManAddInfLemma( p, Frame, pLem );
            pInf = (Pdr2_Lem_t *)Vec_PtrEntryLast( p->vInf );
            for ( k = Frame + 1; k <= Level; k++ )
                Pdr2_ManSolverAddLemma( p, Pdr2_ManSolver(p,k), pInf->pCube, pInf->Id );
            p->iEarly = Abc_MinInt( p->iEarly, Frame );
            Added++;
        }
finish:
    if ( p->pPars->fVerbose && !p->pPars->fSilent && Count >= 2 )
        Abc_Print( 1, "Joint induction in frame %d promoted %d of %d lemmas in %d SAT calls to %s. Time = %.3f sec.\n",
            Level, Added, Count, Rounds, fFinite ? "the frontier" : "infinity", (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( pSat ) sat_solver_delete( pSat );
    if ( pCnf ) Cnf_DataFree( pCnf );
    Vec_IntFree( vAssume );
    Vec_IntFree( vClause );
    Vec_PtrFree( vKnown );
    Vec_PtrFree( vCandidates );
}

/**Function*************************************************************

  Synopsis    [Checks induction at a depth whose base frames PDR has already discharged.]

  Description []

***********************************************************************/
// Called only after the current frame contains no bad state. PDR has then
// established the base case through Level. The inductive-only engine may
// close at any k <= Level; no result from an unchecked base case is accepted.
static int Pdr2_ManKindStep( Pdr2_Man_t * p )
{
    int Level = Pdr2_ManLevel(p), Seconds = p->nKindTime, Ret;
    abctime Start = Abc_Clock(), Limit = p->timeGlobal;
    Aig_Man_t * pWork;
    if ( !Seconds || Level < p->nKindNext || Level > p->nKindMax ) return 0;
    p->nKindNext = Level >= p->nKindMax/2 ? p->nKindMax+1 : 2*Level;
    if ( (ABC_INT64_T)(Level+1) * Aig_ManNodeNum(p->pAig) > 2000000 ||
         Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) ) return 0;
    if ( p->timeSliceHard && (!Limit || p->timeSliceHard < Limit) ) Limit = p->timeSliceHard;
    if ( Limit ) Seconds = Abc_MinInt(Seconds, (int)((Limit-Start)/CLOCKS_PER_SEC));
    if ( Seconds <= 0 ) return 0;
    pWork = Aig_ManDupSimple(p->pAig);
    Ret = Saig_ManInduction(pWork, Seconds, Level+1, 10000, 0, 0, 0, 0, 0);
    Aig_ManStop(pWork);
    p->nKindCalls++;
    p->timeKind += Abc_Clock()-Start;
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1, "PDR-backed induction through frame %d: %s in %.3f sec.\n",
            Level, Ret == 1 ? "proved" : "no proof", (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    return p->fKindProved = Ret == 1;
}

/**Function*************************************************************

  Synopsis    [Advances the private random generator used to propose invariant clauses.]

  Description []

***********************************************************************/
static word Pdr2_SeedRandom( word * pState )
{
    *pState ^= *pState << 13; *pState ^= *pState >> 7; *pState ^= *pState << 17;
    return *pState;
}

/**Function*************************************************************

  Synopsis    [Tests whether the candidate cube excludes every allowed initial state.]

  Description []

***********************************************************************/
static int Pdr2_SeedInitExcluded( Pdr2_Man_t * p, int a, int b )
{
    int r = Abc_Lit2Var(a);
    if ( p->pInit[r] != 2 && p->pInit[r] == Abc_LitIsCompl(a) ) return 1;
    if ( b < 0 ) return 0;
    r = Abc_Lit2Var(b);
    return p->pInit[r] != 2 && p->pInit[r] == Abc_LitIsCompl(b);
}

/**Function*************************************************************

  Synopsis    [Derives invariant units from self-holding registers and constants.]

  Description []

***********************************************************************/
// Start with structurally self-holding initialized registers, then propagate
// already certified constants through the transition relation. Every newly
// accepted bit depends only on constants that are themselves invariant; the
// procedure can therefore stop between rounds without a SAT certification pass.
static void Pdr2_ManSeedStaticUnits( Pdr2_Man_t * p )
{
    unsigned char * pValues;
    Aig_Obj_t * pObj, * pNext;
    int i, Round, a, b, Value, Added = 0, Changed, Lit;
    Gip_Solver_t * pCheck = NULL;
    abctime Start = Abc_Clock(), Stop = Start + CLOCKS_PER_SEC / 20;
    if ( !Gip_OptionGet("PDR2_STATIC_UNITS") || !atoi(Gip_OptionGet("PDR2_STATIC_UNITS")) ||
         !p->nRegs || p->pPars->fUseAbs || p->pPars->nInitLiReg ||
         Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) ) return;
    if ( p->timeGlobal && Stop > p->timeGlobal ) Stop = p->timeGlobal;
    pValues = ABC_ALLOC(unsigned char, Aig_ManObjNumMax(p->pAig));
    memset(pValues, 2, Aig_ManObjNumMax(p->pAig));
    pValues[Aig_ObjId(Aig_ManConst1(p->pAig))] = 1;
    Saig_ManForEachLo(p->pAig, pObj, i)
        if ( p->pInit[i] < 2 && Aig_ObjChild0(Saig_ManLi(p->pAig, i)) == pObj )
            pValues[Aig_ObjId(pObj)] = p->pInit[i];
    for ( Round = 0; Round < 8 && Abc_Clock() < Stop; Round++ )
    {
        if ( p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId) ) break;
        Aig_ManForEachNode(p->pAig, pObj, i)
        {
            if ( (i & 1023) == 0 && Abc_Clock() >= Stop ) goto collected;
            a = pValues[Aig_ObjFaninId0(pObj)];
            b = pValues[Aig_ObjFaninId1(pObj)];
            if ( a < 2 ) a ^= Aig_ObjFaninC0(pObj);
            if ( b < 2 ) b ^= Aig_ObjFaninC1(pObj);
            pValues[Aig_ObjId(pObj)] = !a || !b ? 0 : a == 1 && b == 1 ? 1 : 2;
        }
        Changed = 0;
        Saig_ManForEachLo(p->pAig, pObj, i)
        {
            if ( p->pInit[i] == 2 || pValues[Aig_ObjId(pObj)] < 2 ) continue;
            pNext = Saig_ManLi(p->pAig, i);
            Value = pValues[Aig_ObjFaninId0(pNext)];
            if ( Value < 2 ) Value ^= Aig_ObjFaninC0(pNext);
            if ( Value != p->pInit[i] ) continue;
            pValues[Aig_ObjId(pObj)] = Value;
            Changed++;
        }
        if ( !Changed ) break;
    }
collected:
    if ( Gip_OptionGet("PDR2_STATIC_UNITS_CHECK") )
    {
        pCheck = Gip_SolverNew(p->pCtx);
        Saig_ManForEachLo(p->pAig, pObj, i)
            if ( pValues[Aig_ObjId(pObj)] < 2 )
            {
                Lit = Abc_LitNot(Pdr2_LitLo(p, Abc_Var2Lit(i, pValues[Aig_ObjId(pObj)])));
                Gip_SolverAddLemma(pCheck, &Lit, 1);
            }
        Saig_ManForEachLo(p->pAig, pObj, i)
            if ( pValues[Aig_ObjId(pObj)] < 2 )
            {
                Lit = Pdr2_LitLi(p, Abc_Var2Lit(i, pValues[Aig_ObjId(pObj)]));
                assert(Gip_SolverSolve(pCheck, &Lit, 1, NULL, NULL, 0, -1) == GIP_UNSAT);
            }
        Gip_SolverFree(pCheck);
    }
    Saig_ManForEachLo(p->pAig, pObj, i)
        if ( pValues[Aig_ObjId(pObj)] < 2 )
        {
            Pdr2_Cube_t * pCube;
            Pdr2_Lem_t * pNew;
            assert(pValues[Aig_ObjId(pObj)] == p->pInit[i]);
            Lit = Abc_Var2Lit(i, pValues[Aig_ObjId(pObj)]);
            pCube = Pdr2_CubeAlloc(&Lit, 1);
            assert(!Pdr2_CubeIsInit(p, pCube));
            pNew = Pdr2_LemAlloc(p, pCube, NULL, -1);
            Pdr2_ManSolverAddLemma(p, p->pInf, pCube, pNew->Id);
            Vec_PtrPush(p->vInf, pNew); p->nInfLemmas++; Added++;
            Pdr2_CubeDeref(pCube);
        }
    ABC_FREE(pValues);
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1, "Static unit invariants: %d accepted, %d rounds, %.3f sec.\n",
                  Added, Round, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
}

/**Function*************************************************************

  Synopsis    [Certifies simulated unit and binary clauses by a Houdini fixed point.]

  Description []

***********************************************************************/
// Learn a conjunction of unit/binary state clauses by a Houdini fixed
// point. Simulation only proposes candidates. The final set is accepted
// only after SAT proves Init => H and H & T => H'. No property assumption
// participates, and every surviving clause is installed simultaneously.
static void Pdr2_ManSeedInvariants( Pdr2_Man_t * p, int SecondsOverride )
{
    int Seconds = SecondsOverride > 0 ? SecondsOverride : Gip_OptionGet("PDR2_SEEDINV") ? Abc_MaxInt(0,Abc_MinInt(60,atoi(Gip_OptionGet("PDR2_SEEDINV")))) : 0;
    int Max = Gip_OptionGet("PDR2_SEEDINV_MAX") ? Abc_MaxInt(1,Abc_MinInt(32768,atoi(Gip_OptionGet("PDR2_SEEDINV_MAX")))) : 8192;
    int Steps = 32, nObj = Aig_ManObjNumMax(p->pAig), n = p->nRegs;
    word * pValues = NULL, * pHistory = NULL, Rand = ABC_CONST(0xb956d7986acbae31);
    unsigned char * pConst = NULL, * pActive = NULL;
    Vec_Int_t * vA = NULL, * vB = NULL, * vAssump = NULL, * vFail = NULL;
    Aig_Obj_t * pObj;
    Cnf_Dat_t * pCnf = NULL;
    sat_solver * pSat = NULL;
    int i, j, k, d, t, a, b, Mask, x, y, Count = 0, Live = 0, Added = 0, Rounds = 0, Proved = 0;
    int Vars, Lits[3], Ret = l_Undef;
    abctime Start = Abc_Clock(), Stop = Start+(abctime)Seconds*CLOCKS_PER_SEC;
    if ( !Seconds || p->pPars->nInitLiReg || !n || n > 8192 || Aig_ManNodeNum(p->pAig) > 300000 ||
         p->pPars->fUseAbs || p->pPars->nPropLimit ||
         Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) ) return;
    if ( p->timeGlobal && Stop > p->timeGlobal ) Stop = p->timeGlobal;
    pValues = ABC_CALLOC(word,nObj);
    pHistory = ABC_ALLOC(word,n*Steps);
    pConst = ABC_CALLOC(unsigned char,n);
    vA = Vec_IntAlloc(Max); vB = Vec_IntAlloc(Max);
    vAssump = Vec_IntAlloc(Max); vFail = Vec_IntAlloc(Max);
    pValues[Aig_ObjId(Aig_ManConst1(p->pAig))] = ~(word)0;
    Saig_ManForEachLo(p->pAig,pObj,i)
        pValues[Aig_ObjId(pObj)] = p->pInit[i] == 2 ? Pdr2_SeedRandom(&Rand) : p->pInit[i] ? ~(word)0 : 0;
    for ( t = 0; t < Steps; t++ )
    {
        if ( Abc_Clock() >= Stop || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId)) ) goto finish;
        Saig_ManForEachLo(p->pAig,pObj,i) pHistory[i*Steps+t] = pValues[Aig_ObjId(pObj)];
        Saig_ManForEachPi(p->pAig,pObj,i) pValues[Aig_ObjId(pObj)] = Pdr2_SeedRandom(&Rand);
        Aig_ManForEachNode(p->pAig,pObj,i)
        {
            word u = pValues[Aig_ObjId(Aig_ObjFanin0(pObj))], v = pValues[Aig_ObjId(Aig_ObjFanin1(pObj))];
            pValues[Aig_ObjId(pObj)] = (Aig_ObjFaninC0(pObj) ? ~u : u) & (Aig_ObjFaninC1(pObj) ? ~v : v);
        }
        // Evaluate every LI before changing any LO; direct register copies
        // must use the previous state as well.
        Saig_ManForEachLi(p->pAig,pObj,i)
            pValues[Aig_ObjId(pObj)] = pValues[Aig_ObjId(Aig_ObjFanin0(pObj))] ^ (Aig_ObjFaninC0(pObj) ? ~(word)0 : 0);
        Saig_ManForEachLo(p->pAig,pObj,i)
            pValues[Aig_ObjId(pObj)] = pValues[Aig_ObjId(Saig_ManLi(p->pAig,i))];
    }
    for ( i = 0; i < n && Vec_IntSize(vA) < Max; i++ )
    {
        word Any = 0, All = ~(word)0;
        for ( t = 0; t < Steps; t++ ) Any |= pHistory[i*Steps+t], All &= pHistory[i*Steps+t];
        pConst[i] = Any == 0 || All == ~(word)0;
        if ( !pConst[i] ) continue;
        a = Abc_Var2Lit(i, Any != 0);
        if ( Pdr2_SeedInitExcluded(p,a,-1) ) Vec_IntPush(vA,a), Vec_IntPush(vB,-1);
    }
    // Nearby registers first; a bounded neighborhood avoids quadratic
    // startup on very large state vectors. Small designs use all pairs.
    for ( d = 1; d < n && d <= (n <= 1024 ? n : 128) && Vec_IntSize(vA) < Max; d++ )
        for ( i = 0, j = d; j < n && Vec_IntSize(vA) < Max; i++, j++ )
        {
            if ( pConst[i] || pConst[j] ) continue;
            if ( (i & 255) == 0 && Abc_Clock() >= Stop ) goto finish;
            Mask = 0;
            for ( t = 0; t < Steps && Mask != 15; t++ )
            {
                word u = pHistory[i*Steps+t], v = pHistory[j*Steps+t];
                if ( ~u & ~v ) Mask |= 1;
                if ( ~u & v ) Mask |= 2;
                if ( u & ~v ) Mask |= 4;
                if ( u & v ) Mask |= 8;
            }
            for ( k = 0; k < 4 && Vec_IntSize(vA) < Max; k++ )
            {
                if ( Mask & (1 << k) ) continue;
                a = Abc_Var2Lit(i,!(k >> 1)); b = Abc_Var2Lit(j,!(k & 1));
                if ( Pdr2_SeedInitExcluded(p,a,b) ) Vec_IntPush(vA,a), Vec_IntPush(vB,b);
            }
        }
    Count = Live = Vec_IntSize(vA);
    if ( !Count || Abc_Clock() >= Stop ) goto finish;
    pCnf = Cnf_DeriveSimple(p->pAig,Aig_ManCoNum(p->pAig));
    if ( !pCnf ) goto finish;
    pSat = sat_solver_new(); Vars = pCnf->nVars;
    sat_solver_setnvars(pSat,Vars+2*Count);
    sat_solver_set_runtime_limit(pSat,Stop);
    sat_solver_set_runid(pSat,p->pPars->RunId);
    sat_solver_set_stop_func(pSat,p->pPars->pFuncStop);
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( (i & 1023) == 0 && Abc_Clock() >= Stop ) goto finish;
        if ( !sat_solver_addclause(pSat,pCnf->pClauses[i],pCnf->pClauses[i+1]) ) goto finish;
    }
    pActive = ABC_ALLOC(unsigned char,Count); memset(pActive,1,Count);
    for ( i = 0; i < Count; i++ )
    {
        a = Vec_IntEntry(vA,i); b = Vec_IntEntry(vB,i);
        x = pCnf->pVarNums[Aig_ObjId(Saig_ManLo(p->pAig,Abc_Lit2Var(a)))];
        Lits[0] = Abc_Var2Lit(Vars+i,1);
        Lits[1] = Abc_Var2Lit(x,!Abc_LitIsCompl(a));
        if ( b >= 0 )
        {
            y = pCnf->pVarNums[Aig_ObjId(Saig_ManLo(p->pAig,Abc_Lit2Var(b)))];
            Lits[2] = Abc_Var2Lit(y,!Abc_LitIsCompl(b));
        }
        // act_i => C_i(s)
        if ( !sat_solver_addclause(pSat,Lits,Lits+(b >= 0 ? 3 : 2)) ) goto finish;
        // fail_i => act_i AND NOT C_i(s')
        Lits[0] = Abc_Var2Lit(Vars+Count+i,1); Lits[1] = Abc_Var2Lit(Vars+i,0);
        if ( !sat_solver_addclause(pSat,Lits,Lits+2) ) goto finish;
        x = pCnf->pVarNums[Aig_ObjId(Saig_ManLi(p->pAig,Abc_Lit2Var(a)))];
        Lits[1] = Abc_Var2Lit(x,Abc_LitIsCompl(a));
        if ( !sat_solver_addclause(pSat,Lits,Lits+2) ) goto finish;
        if ( b >= 0 )
        {
            y = pCnf->pVarNums[Aig_ObjId(Saig_ManLi(p->pAig,Abc_Lit2Var(b)))];
            Lits[1] = Abc_Var2Lit(y,Abc_LitIsCompl(b));
            if ( !sat_solver_addclause(pSat,Lits,Lits+2) ) goto finish;
        }
        Vec_IntPush(vFail,Abc_Var2Lit(Vars+Count+i,0));
    }
    if ( !sat_solver_addclause(pSat,Vec_IntArray(vFail),Vec_IntArray(vFail)+Count) )
        Proved = 1;
    while ( Live && !Proved && Abc_Clock() < Stop )
    {
        int Removed = 0;
        Vec_IntClear(vAssump);
        for ( i = 0; i < Count; i++ ) Vec_IntPush(vAssump,Abc_Var2Lit(Vars+i,!pActive[i]));
        Ret = sat_solver_solve(pSat,Vec_IntArray(vAssump),Vec_IntArray(vAssump)+Count,50000,0,0,0);
        Rounds++;
        if ( Ret == l_False ) { Proved = 1; break; }
        if ( Ret != l_True ) break;
        for ( i = 0; i < Count; i++ )
        {
            if ( !pActive[i] ) continue;
            a = Vec_IntEntry(vA,i); b = Vec_IntEntry(vB,i);
            x = pCnf->pVarNums[Aig_ObjId(Saig_ManLi(p->pAig,Abc_Lit2Var(a)))];
            if ( !(sat_solver_var_value(pSat,x) ^ Abc_LitIsCompl(a)) ) continue;
            if ( b >= 0 )
            {
                y = pCnf->pVarNums[Aig_ObjId(Saig_ManLi(p->pAig,Abc_Lit2Var(b)))];
                if ( !(sat_solver_var_value(pSat,y) ^ Abc_LitIsCompl(b)) ) continue;
            }
            pActive[i] = 0; Removed++; Live--;
        }
        assert(Removed > 0);
    }
    if ( Proved )
    {
        Gip_Solver_t * pCheck = Gip_OptionGet("PDR2_SEEDINV_CHECK") ? Gip_SolverNew(p->pCtx) : NULL;
        // Independent checking uses GipSAT and the original context CNF,
        // with no activation encoding or facts learned by the seed solver.
        if ( pCheck )
        {
            for ( i = 0; i < Count; i++ ) if ( pActive[i] )
            {
                a = Vec_IntEntry(vA,i); b = Vec_IntEntry(vB,i);
                Lits[0] = Abc_LitNot(Pdr2_LitLo(p,a));
                if ( b >= 0 ) Lits[1] = Abc_LitNot(Pdr2_LitLo(p,b));
                Gip_SolverAddLemma(pCheck,Lits,b >= 0 ? 2 : 1);
            }
            for ( i = 0; i < Count; i++ ) if ( pActive[i] )
            {
                a = Vec_IntEntry(vA,i); b = Vec_IntEntry(vB,i);
                assert(Pdr2_SeedInitExcluded(p,a,b));
                Lits[0] = Pdr2_LitLi(p,a);
                if ( b >= 0 ) Lits[1] = Pdr2_LitLi(p,b);
                Ret = Gip_SolverSolve(pCheck,Lits,b >= 0 ? 2 : 1,NULL,NULL,0,-1);
                assert(Ret == GIP_UNSAT);
            }
            Gip_SolverFree(pCheck);
        }
        for ( i = 0; i < Count; i++ ) if ( pActive[i] )
        {
            Pdr2_Cube_t * pCube;
            Pdr2_Lem_t * pNew;
            Lits[0] = Vec_IntEntry(vA,i); Lits[1] = Vec_IntEntry(vB,i);
            pCube = Pdr2_CubeAlloc(Lits,Lits[1] >= 0 ? 2 : 1);
            assert(!Pdr2_CubeIsInit(p,pCube));
            pNew = Pdr2_LemAlloc(p,pCube,NULL,-1);
            Pdr2_ManSolverAddLemma(p,p->pInf,pCube,pNew->Id);
            Vec_PtrPush(p->vInf,pNew); p->nInfLemmas++; Added++;
            Pdr2_CubeDeref(pCube);
        }
    }
finish:
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1,"Seed invariants: %d accepted from %d candidates after %d rounds (%d surviving); %s. Time = %.3f sec.\n",
            Added,Count,Rounds,Live,Proved ? "inductive" : "not certified",(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( pSat ) sat_solver_delete(pSat);
    if ( pCnf ) Cnf_DataFree(pCnf);
    Vec_IntFreeP(&vA); Vec_IntFreeP(&vB); Vec_IntFreeP(&vAssump); Vec_IntFreeP(&vFail);
    ABC_FREE(pValues); ABC_FREE(pHistory); ABC_FREE(pConst); ABC_FREE(pActive);
}

/**Function*************************************************************

  Synopsis    [Searches a bounded unrolling strengthened with established PDR lemmas.]

  Description []

***********************************************************************/
// A bounded concrete witness search strengthened with the already proved
// frame clauses. A clause in F_k is used only at unrolling positions <= k;
// infinity clauses hold at every position. Only a replayed SAT answer is
// consumed. UNSAT and timeout leave the ordinary PDR proof untouched.
static int Pdr2_ManHintBmc( Pdr2_Man_t * p )
{
    int Level = Pdr2_ManLevel(p), Extra = Gip_OptionGet("PDR2_BMC_HINT_EXTRA") ? Abc_MaxInt(0,Abc_MinInt(32,atoi(Gip_OptionGet("PDR2_BMC_HINT_EXTRA")))) : 8;
    int Depth = Level+Extra, i, j, k, t, f, Lit, Ret = GIP_UNDEF, Added = 0;
    abctime Start = Abc_Clock(), Stop = Start+(abctime)p->nHintTime*CLOCKS_PER_SEC;
    Aig_Man_t * pUnroll = NULL;
    Aig_Obj_t ** pMap = NULL, * pObj, * pBad, * pGood, * pClause, * pMapped;
    Vec_Ptr_t * vNext = NULL;
    Vec_Int_t * vInit = NULL, * vPis = NULL;
    Pdr2_Lem_t * pLem;
    Cnf_Man_t * pCnf = NULL;
    Gip_Ctx_t * pCtx = NULL;
    Gip_Solver_t * pSat = NULL;
    Abc_Cex_t * pCex = NULL;
    if ( !p->nHintTime || Level < p->nHintNext || p->pPars->fUseAbs ||
         p->pPars->nPropLimit || p->pPars->nFrameMax || Depth > 64 ||
         (double)(Depth+1)*Aig_ManNodeNum(p->pAig) > 4000000 ||
         Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) ) return 0;
    p->nHintNext = Abc_MaxInt(Level+1,p->nHintNext*2);
    p->nHintCalls++;
    if ( p->timeGlobal && Stop > p->timeGlobal ) Stop = p->timeGlobal;
    if ( p->timeLimit && Stop > p->timeLimit ) Stop = p->timeLimit;
    if ( Stop <= Start ) return 0;
    pUnroll = Aig_ManStart(Abc_MaxInt(1000,Aig_ManNodeNum(p->pAig)));
    pMap = ABC_ALLOC(Aig_Obj_t *,Aig_ManObjNumMax(p->pAig));
    vNext = Vec_PtrAlloc(p->nRegs); vInit = Vec_IntAlloc(p->nRegs); vPis = Vec_IntAlloc((Depth+1)*p->nPis);
    pMap[Aig_ObjId(Aig_ManConst1(p->pAig))] = Aig_ManConst1(pUnroll);
    Saig_ManForEachLo(p->pAig,pObj,i)
    {
        pMapped = p->pInit[i] == 2 ? Aig_ObjCreateCi(pUnroll) : Aig_NotCond(Aig_ManConst1(pUnroll),!p->pInit[i]);
        pMap[Aig_ObjId(pObj)] = pMapped;
        Vec_IntPush(vInit,Aig_ObjToLit(pMapped));
    }
    pBad = Aig_ManConst0(pUnroll); pGood = Aig_ManConst1(pUnroll);
    for ( t = 0; t <= Depth; t++ )
    {
        if ( Abc_Clock() >= Stop || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId)) ) goto finish;
        // State clauses are mapped before advancing the state vector.
        if ( !Gip_OptionGet("PDR2_BMC_HINT_PLAIN") )
            for ( k = Abc_MaxInt(1,t); k <= Pdr2_ManFrameNum(p); k++ )
                Vec_PtrForEachEntry(Pdr2_Lem_t *,k == Pdr2_ManFrameNum(p) ? p->vInf : Pdr2_ManFrame(p,k),pLem,i)
                {
                    if ( pLem->fRemoved || pLem->pCube->nLits > 64 || Added >= 200000 ) continue;
                    pClause = Aig_ManConst0(pUnroll);
                    for ( j = 0; j < pLem->pCube->nLits; j++ )
                    {
                        Lit = pLem->pCube->Lits[j];
                        pMapped = pMap[Aig_ObjId(Saig_ManLo(p->pAig,Abc_Lit2Var(Lit)))];
                        pClause = Aig_Or(pUnroll,pClause,Aig_NotCond(pMapped,!Abc_LitIsCompl(Lit)));
                    }
                    pGood = Aig_And(pUnroll,pGood,pClause); Added++;
                }
        // After the frontier only infinity clauses are justified.
        if ( t > Pdr2_ManFrameNum(p) && !Gip_OptionGet("PDR2_BMC_HINT_PLAIN") )
            Vec_PtrForEachEntry(Pdr2_Lem_t *,p->vInf,pLem,i)
            {
                if ( pLem->fRemoved || pLem->pCube->nLits > 64 || Added >= 200000 ) continue;
                pClause = Aig_ManConst0(pUnroll);
                for ( j = 0; j < pLem->pCube->nLits; j++ )
                {
                    Lit = pLem->pCube->Lits[j];
                    pMapped = pMap[Aig_ObjId(Saig_ManLo(p->pAig,Abc_Lit2Var(Lit)))];
                    pClause = Aig_Or(pUnroll,pClause,Aig_NotCond(pMapped,!Abc_LitIsCompl(Lit)));
                }
                pGood = Aig_And(pUnroll,pGood,pClause); Added++;
            }
        Saig_ManForEachPi(p->pAig,pObj,i)
        {
            pMap[Aig_ObjId(pObj)] = Aig_ObjCreateCi(pUnroll);
            Vec_IntPush(vPis,Aig_ObjId(pMap[Aig_ObjId(pObj)]));
        }
        Aig_ManForEachNode(p->pAig,pObj,i)
        {
            pMap[Aig_ObjId(pObj)] = Aig_And(pUnroll,Aig_NotCond(pMap[Aig_ObjFaninId0(pObj)],Aig_ObjFaninC0(pObj)),
                                                                 Aig_NotCond(pMap[Aig_ObjFaninId1(pObj)],Aig_ObjFaninC1(pObj)));
            if ( (i & 4095) == 0 && Abc_Clock() >= Stop ) goto finish;
        }
        pObj = Aig_ManCo(p->pAig,0);
        pBad = Aig_Or(pUnroll,pBad,Aig_NotCond(pMap[Aig_ObjFaninId0(pObj)],Aig_ObjFaninC0(pObj)));
        Vec_PtrClear(vNext);
        Saig_ManForEachLi(p->pAig,pObj,i)
            Vec_PtrPush(vNext,Aig_NotCond(pMap[Aig_ObjFaninId0(pObj)],Aig_ObjFaninC0(pObj)));
        Saig_ManForEachLo(p->pAig,pObj,i) pMap[Aig_ObjId(pObj)] = (Aig_Obj_t *)Vec_PtrEntry(vNext,i);
    }
    Aig_ObjCreateCo(pUnroll,Aig_And(pUnroll,pBad,pGood));
    Aig_ManCleanup(pUnroll);
    if ( Abc_Clock() >= Stop ) goto finish;
    pCnf = Cnf_ManStart(); pCtx = Gip_CtxCreatePdr2(pUnroll, pCnf, 0); pSat = Gip_SolverNew(pCtx);
    pSat->TimeLimit = Stop; pSat->nConfLimit = 50000;
    pSat->RunId = p->pPars->RunId; pSat->pFuncStop = p->pPars->pFuncStop;
    pSat->fInputDecisions = Gip_OptionGet("PDR2_BMC_HINT_INPUTS") && atoi(Gip_OptionGet("PDR2_BMC_HINT_INPUTS"));
    Lit = Abc_Var2Lit(Gip_CtxObjVar(pCtx,Aig_ManCo(pUnroll,0)),0);
    if ( Abc_Clock() >= Stop ) goto finish;
    Ret = Gip_SolverSolve(pSat,&Lit,1,NULL,NULL,0,-1);
    if ( Ret != GIP_SAT ) goto finish;
    pCex = Abc_CexAlloc(p->nRegs,p->nPis,Depth+1); pCex->iPo = 0;
    for ( i = 0; i < p->nRegs; i++ )
    {
        pMapped = Aig_ObjFromLit(pUnroll,Vec_IntEntry(vInit,i));
        k = Aig_Regular(pMapped) == Aig_ManConst1(pUnroll) ? 1 : Gip_SolverVarValue(pSat,Gip_CtxObjVar(pCtx,Aig_Regular(pMapped))) == GIP_TRUE;
        if ( k ^ Aig_IsComplement(pMapped) ) Abc_InfoSetBit(pCex->pData,i);
    }
    Vec_IntForEachEntry(vPis,Lit,i)
        if ( Gip_SolverVarValue(pSat,Gip_CtxObjVar(pCtx,Aig_ManObj(pUnroll,Lit))) == GIP_TRUE )
            Abc_InfoSetBit(pCex->pData,p->nRegs+i);
    for ( f = 0; f <= Depth; f++ )
    {
        pCex->iFrame = f;
        pCex->nBits = p->nRegs+(f+1)*p->nPis;
        if ( Saig_ManVerifyCex(p->pAig,pCex) ) break;
    }
    if ( f <= Depth ) { p->pReachCex = pCex; pCex = NULL; }
    else Abc_Print(1,"PDR-guided BMC counterexample verification FAILED.\n");
finish:
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1,"PDR-guided BMC through %d: %s; %d frame clauses, %d nodes. Time = %.3f sec.\n",
            Depth,p->pReachCex ? "checked counterexample" : "no counterexample",Added,pUnroll ? Aig_ManNodeNum(pUnroll) : 0,(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( pCex ) Abc_CexFree(pCex);
    if ( pSat ) Gip_SolverFree(pSat);
    if ( pCtx ) Gip_CtxFree(pCtx);
    if ( pCnf ) Cnf_ManStop(pCnf);
    if ( pUnroll ) Aig_ManStop(pUnroll);
    ABC_FREE(pMap); Vec_PtrFreeP(&vNext); Vec_IntFreeP(&vInit); Vec_IntFreeP(&vPis);
    p->timeHint += Abc_Clock()-Start;
    return p->pReachCex != NULL;
}

typedef struct Pdr2_Hints_t_ Pdr2_Hints_t;
struct Pdr2_Hints_t_
{
    Vec_Wec_t * vCubes;
    Vec_Str_t * vUsed;
    int nTried, nAdded;
    Pdr2_FrameHintFunc pFuncFrame;
    void * pFrameData;
};

/**Function*************************************************************

  Synopsis    [Blocks and shortens a candidate cube at a particular frame.]

  Description [The caller supplies a mutable sorted cube of distinct
  register literals and the query conflict cap. Every accepted cube is
  disjoint from reset and relatively inductive at the preceding frame.]

***********************************************************************/
static int Pdr2_ManBlockHint( Pdr2_Man_t * p, int iFrame, Vec_Int_t * vCube, int * pfClosed )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver(p, iFrame - 1);
    int i, Lit;
    if ( Pdr2_LitsAreInit(p, vCube) || Pdr2_ManTryDrop(p, pSat, vCube, 1, NULL) != 1 )
        return 0;
    for ( i = Vec_IntSize(vCube) - 1; i >= 0 && Vec_IntSize(vCube) > 1 && !Pdr2_ManPastDeadline(p); i-- )
    {
        Lit = Vec_IntEntry(vCube, i);
        Vec_IntDrop(vCube, i);
        if ( Pdr2_LitsAreInit(p, vCube) || Pdr2_ManTryDrop(p, pSat, vCube, 1, NULL) != 1 )
            Vec_IntPushOrder(vCube, Lit);
    }
    *pfClosed = Pdr2_ManAddLemma(p, iFrame, vCube, 1, NULL, NULL);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Tests the enclosing PDR run for cancellation or timeout.]

***********************************************************************/
int Pdr2_FrameIsStopped( const Pdr2_Frame_t * pFrame )
{
    return Pdr2_ManPastDeadline(pFrame->pMan);
}

/**Function*************************************************************

  Synopsis    [Borrows the register literals of a delta or infinity cube.]

***********************************************************************/
int Pdr2_FrameReadCube( const Pdr2_Frame_t * pFrame, int iLevel, int iCube, const int ** ppLits )
{
    Vec_Ptr_t * v;
    Pdr2_Lem_t * pLem;
    *ppLits = NULL;
    if ( iLevel < 0 || iLevel > pFrame->iLevel + 1 || iCube < 0 )
        return -1;
    v = iLevel == pFrame->iLevel + 1 ? pFrame->pMan->vInf : Pdr2_ManFrame(pFrame->pMan, iLevel);
    if ( iCube >= Vec_PtrSize(v) )
        return -1;
    pLem = (Pdr2_Lem_t *)Vec_PtrEntry(v, iCube);
    if ( pLem->fRemoved )
        return 0;
    *ppLits = pLem->pCube->Lits;
    return pLem->pCube->nLits;
}

/**Function*************************************************************

  Synopsis    [Checks that a candidate names distinct registers in ascending order.]

***********************************************************************/
static int Pdr2_ManValidHint( Pdr2_Man_t * p, Vec_Int_t * vCube )
{
    int i, Lit, Last = -1;
    Vec_IntForEachEntry( vCube, Lit, i )
    {
        if ( Lit < 0 || Abc_Lit2Var(Lit) <= Last || Abc_Lit2Var(Lit) >= p->nRegs )
            return 0;
        Last = Abc_Lit2Var(Lit);
    }
    return Vec_IntSize(vCube) > 0;
}

/**Function*************************************************************

  Synopsis    [Checks and generalizes a feedback cube within the caller's budget.]

***********************************************************************/
int Pdr2_FrameBlockCube( const Pdr2_Frame_t * pFrame, int iLevel, Vec_Int_t * vCube,
    int nConfLimit, abctime TimeStop, int * pfClosed )
{
    Pdr2_Man_t * p = pFrame->pMan;
    abctime SavedTime = p->timeLimit;
    int SavedLimit = p->nDropConfLimit, Result = 0;
    *pfClosed = 0;
    if ( iLevel < 1 || iLevel > pFrame->iLevel || nConfLimit < 0 || !Pdr2_ManValidHint(p, vCube) )
        return 0;
    if ( TimeStop && (!SavedTime || TimeStop < SavedTime) )
        p->timeLimit = TimeStop;
    p->nDropConfLimit = nConfLimit;
    if ( !Pdr2_ManPastDeadline(p) )
        Result = Pdr2_ManBlockHint(p, iLevel, vCube, pfClosed);
    p->nDropConfLimit = SavedLimit;
    p->timeLimit = SavedTime;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries small candidate cubes at the newly opened frame.]

  Description [The candidate's complement must hold initially and be
  inductive relative to the preceding frame. Repeat both checks when
  dropping a literal. A capped or interrupted query cannot add a lemma.]

***********************************************************************/
static int Pdr2_ManAdmitHints( Pdr2_Man_t * p, Pdr2_Hints_t * pHints )
{
    int Level = Pdr2_ManLevel(p), Count = Vec_WecSize(pHints->vCubes);
    int k, Index, Offset, fClosed = 0, SavedLimit = p->nDropConfLimit;
    Vec_Int_t * vCube, * vTrial;
    if ( Level < 1 || !Count ) return 0;
    Offset = (int)(((word)(Level - 1) * 31) % Count);
    vTrial = Vec_IntAlloc(8);
    p->nDropConfLimit = 128;
    for ( k = 0; k < Abc_MinInt(64, Count) && !Pdr2_ManPastDeadline(p); k++ )
    {
        Index = (int)(((word)Offset + k) % Count);
        if ( Vec_StrEntry(pHints->vUsed, Index) ) continue;
        vCube = Vec_WecEntry(pHints->vCubes, Index);
        if ( Vec_IntSize(vCube) > 8 || !Pdr2_ManValidHint(p, vCube) )
        {
            Vec_StrWriteEntry(pHints->vUsed, Index, 1);
            continue;
        }
        if ( Pdr2_LitsAreInit(p, vCube) ) continue;
        pHints->nTried++;
        Vec_IntClear(vTrial);
        Vec_IntAppend(vTrial, vCube);
        if ( !Pdr2_ManBlockHint(p, Level, vTrial, &fClosed) ) continue;
        Vec_StrWriteEntry(pHints->vUsed, Index, 1);
        pHints->nAdded++;
        if ( fClosed ) break;
    }
    p->nDropConfLimit = SavedLimit;
    Vec_IntFree(vTrial);
    return fClosed;
}

/**Function*************************************************************

  Synopsis    [The main loop.]

  Description [Returns 1 if the property holds, 0 if it fails (the
  counterexample obligation chain is in p->pCexObl), -1 if undecided.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManSolveFrames( Pdr2_Man_t * p, Pdr2_Hints_t * pHints )
{
    Vec_Int_t * vPred = Vec_IntAlloc( 100 );
    Vec_Int_t * vInputs = Vec_IntAlloc( 100 );
    Vec_Int_t * vPpis = Vec_IntAlloc( 100 );
    Pdr2_Cube_t * pCube;
    Pdr2_Obl_t * pObl;
    abctime clk, clkRun = Abc_Clock();
    int RetValue, Result = -1;
    const char * pSoftSeconds = Gip_OptionGet("PDR2_FRAME_SOFT");
    const char * pJointTime = Gip_OptionGet("PDR2_JOINT_INDUCTION");
    const char * pJointMax = Gip_OptionGet("PDR2_JOINT_INDUCTION_MAX");
    const char * pJointFrame = Gip_OptionGet("PDR2_JOINT_INDUCTION_FRAME");
    int JointTime = pJointTime ? Abc_MinInt(10, atoi(pJointTime)) : 0;
    int JointMax = pJointMax ? Abc_MaxInt(2, Abc_MinInt(4096, atoi(pJointMax))) : 512;
    int fJointFrame = pJointFrame && atoi(pJointFrame) > 0;
    abctime HardDeadline = p->timeLimit, SoftDeadline = 0;
    ABC_INT64_T nPreviousObls = p->nObls;
    int nQuietFrames = 0;
    if ( pSoftSeconds && atoi(pSoftSeconds) > 0 && HardDeadline && !p->propSlice && !p->timeSlice )
    {
        SoftDeadline = p->timeStart + (abctime)atoi(pSoftSeconds) * CLOCKS_PER_SEC;
        if ( SoftDeadline < HardDeadline ) p->timeLimit = SoftDeadline;
        else SoftDeadline = 0;
    }
    if ( !p->fStarted )
    {
        if ( p->pInitSat )
        {
            RetValue = Pdr2_ManInitialQuery(p,NULL,0);
            if ( RetValue == GIP_UNSAT ) { p->fInitEmpty = 1; Result = 1; goto finish; }
            if ( RetValue == GIP_UNDEF ) { Result = -1; goto finish; }
        }
        Pdr2_ManSeedStaticUnits( p );
        Pdr2_ManSeedInvariants( p, 0 );
        if ( Gip_OptionGet("PDR2_PROJECT") ) Pdr2_ManSeedProjection(p, atoi(Gip_OptionGet("PDR2_PROJECT")));
        if ( !p->pPars->nInitLiReg ) Pdr2_ManSimInitBounds( p );
        Pdr2_ManExtend( p );
        p->fStarted = 1;
    }
    // a slice may have ended inside the propagation stages of the previous level (or a sweep
    // was cut by an undecided query): finish them before blocking, so that a resumed run goes
    // through the same stages as an uninterrupted one
    if ( p->iStage == 1 )
    {
        p->fSweepCut = 0;
        if ( Pdr2_ManPropagate( p ) ) { Result = 1; goto finish; }
        if ( p->fSweepCut ) { Result = -1; goto finish; }
        p->iStage = 2;
        if ( Pdr2_ManTimedOut(p) ) { Result = -1; goto finish; }
    }
    if ( p->iStage == 2 )
    {
        p->fSweepCut = 0;
        Pdr2_ManPropagateToInf( p );
        if ( p->fSweepCut ) { Result = -1; goto finish; }
        p->iStage = 0;
        if ( Pdr2_ManTimedOut(p) ) { Result = -1; goto finish; }
    }
    while ( 1 )
    {
        if ( Pdr2_ManHintBmc(p) ) { Result = 0; goto finish; }
        while ( 1 )
        {
            RetValue = Pdr2_ManBlock( p );
            if ( RetValue == PDR2_BLOCK_FAILURE ) { Result =  0; goto finish; }
            if ( RetValue == PDR2_BLOCK_PROVED )  { Result =  1; goto finish; }
            if ( RetValue == PDR2_BLOCK_TIMEOUT ) { Result = -1; goto finish; }
            if ( RetValue == PDR2_BLOCK_RESTART ) { Result = -1; goto finish; }
            clk = Abc_Clock();
            RetValue = Pdr2_ManSolveBad( p );
            p->timeGetBad += Abc_Clock() - clk;
            if ( RetValue == 1 )
                Pdr2_ManGetPred( p, 1, vPred, vInputs );
            if ( RetValue == -1 ) { Result = -1; goto finish; }
            if ( RetValue == 0 )
                break;
            Pdr2_ManAbsProject( p, vPred, vPpis );
            pCube = Pdr2_CubeAllocVec( vPred );
            pObl = Pdr2_OblAlloc( p, Pdr2_ManLevel(p), pCube, vInputs, vPpis, 0, NULL );
            Pdr2_CubeDeref( pCube );
            Pdr2_QueuePush( p, pObl );
            Pdr2_OblDeref( pObl );
        }
        Pdr2_ManPrintProgress( p, 0 );
        if ( JointTime > 0 && Pdr2_ManLevel(p) >= 2 &&
             Pdr2_ManLevel(p) % (Pdr2_ManLevel(p) < 16 ? 2 : 4) == 0 )
            Pdr2_ManJointInduction( p, JointTime, JointMax, fJointFrame );
        if ( Pdr2_ManKindStep(p) ) { Result = 1; goto finish; }
        // Requeued obligations can be discharged by existing clauses.
        // Count newly allocated obligations to distinguish them from new
        // predecessor searches while nearby frames are converging.
        if ( SoftDeadline )
        {
            nQuietFrames = p->nObls == nPreviousObls && p->nLemmas - p->nLemmasLevel <= 4 ? nQuietFrames + 1 : 0;
            nPreviousObls = p->nObls;
            p->timeLimit = nQuietFrames >= 2 ? HardDeadline : SoftDeadline;
            if ( Pdr2_ManPastDeadline(p) ) goto finish;
        }
        if ( p->pPars->fUseAbs && !p->fAbsActive && Abc_Clock() - p->timeStart >= (abctime)p->pPars->nAbsStart * CLOCKS_PER_SEC )
            Pdr2_ManAbsStart( p );
        if ( p->pPars->nFrameMax && Pdr2_ManLevel(p) >= p->pPars->nFrameMax )
        {
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Reached limit on the number of timeframes (%d).\n", p->pPars->nFrameMax );
            p->fExhausted = 1;
            Result = -1;
            goto finish;
        }
        Pdr2_ManExtend( p );
        if ( pHints && pHints->pFuncFrame )
        {
            Pdr2_Frame_t Frame = { p->pAig, Pdr2_ManLevel(p), p->timeLimit, p };
            if ( pHints->pFuncFrame(&Frame, pHints->vCubes, pHints->pFrameData) ) { Result = 1; goto finish; }
            Vec_StrFillExtra(pHints->vUsed, Vec_WecSize(pHints->vCubes), 0);
        }
        if ( pHints && Pdr2_ManAdmitHints(p, pHints) ) { Result = 1; goto finish; }
        p->iStage = 1;
        p->fSweepCut = 0;
        if ( Pdr2_ManPropagate( p ) )
        {
            Result = 1;
            goto finish;
        }
        if ( p->fSweepCut ) { Result = -1; goto finish; }
        p->iStage = 2;
        if ( Pdr2_ManTimedOut(p) ) { Result = -1; goto finish; }
        p->fSweepCut = 0;
        Pdr2_ManPropagateToInf( p );
        if ( p->fSweepCut ) { Result = -1; goto finish; }
        p->iStage = 0;
        if ( Pdr2_ManTimedOut(p) ) { Result = -1; goto finish; }
    }
finish:
    p->timeLimit = HardDeadline;
    if ( p->fInitUnknown ) Result = -1;
    if ( Result == -1 && p->timeGlobal && Abc_Clock() > p->timeGlobal && !p->pPars->fSilent )
        Abc_Print( 1, "Reached timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOut, Pdr2_ManLevel(p) );
    p->timeRun += Abc_Clock() - clkRun;
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    Vec_IntFree( vPpis );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs the ordinary PDR frame loop.]

***********************************************************************/
int Pdr2_ManSolveInt( Pdr2_Man_t * p )
{
    return Pdr2_ManSolveFrames(p, NULL);
}

/**Function*************************************************************

  Synopsis    [Checks one zero-initialized property using candidate register cubes.]

  Description [The caller owns the candidates. Each is a sorted cube of
  at most eight register literals. Verify the final invariant on the full
  transition relation, and replay a counterexample before returning it.]

***********************************************************************/
int Pdr2_ManSolveFrameHints( Aig_Man_t * pAig, Vec_Wec_t * vCubes, abctime TimeStop,
    int (*pFuncStop)(int), int * piFrame, int fVerbose, Pdr2_FrameHintFunc pFuncFrame, void * pFrameData )
{
    Pdr2_Hints_t Hints = { NULL, NULL, 0, 0, pFuncFrame, pFrameData };
    Pdr2_Par_t Pars;
    Gip_Options_t Options;
    Pdr2_Man_t * p;
    int Result = -1;
    *piFrame = -1;
    Abc_CexFreeP(&pAig->pSeqModel);
    if ( !Aig_ManRegNum(pAig) || Saig_ManPoNum(pAig) != 1 || Saig_ManConstrNum(pAig) ||
         Aig_ManExorNum(pAig) || Aig_ManBufNum(pAig) ||
         (TimeStop && Abc_Clock() >= TimeStop) || (pFuncStop && pFuncStop(0)) )
        return -1;
    if ( vCubes )
    {
        Hints.vCubes = vCubes;
        Hints.vUsed = Vec_StrStart(Vec_WecSize(vCubes));
    }
    memset(&Options, 0, sizeof(Options));
    Options.fIsolate = 1;
    Gip_OptionsPush(&Options);
    Pdr2_ManSetDefaultParams(&Pars);
    Pars.fUseAbs = Pars.fVerbose = 0;
    Pars.fCtg = Pars.fSilent = Pars.fVerifyComplete = 1;
    Pars.pFuncStop = pFuncStop;
    Aig_ManSetCioIds(pAig);
    p = Pdr2_ManStart(pAig, NULL, &Pars);
    p->timeGlobal = p->timeLimit = TimeStop;
    if ( p->GuardLit < 0 && !Pdr2_ManPastDeadline(p) )
        Result = Pdr2_ManSolveFrames(p, vCubes ? &Hints : NULL);
    if ( p->fStarted ) *piFrame = Abc_MaxInt(0, Pdr2_ManLevel(p) - 1);
    if ( Result == 1 && Pdr2_ManVerifyInvariant(p) != 1 ) Result = -1;
    if ( Result == 0 )
    {
        Abc_Cex_t * pCex = p->pCexObl || p->pReachCex ? Pdr2_ManDeriveCex(p) : NULL;
        if ( pCex && Saig_ManVerifyCex(pAig, pCex) )
        {
            *piFrame = pCex->iFrame;
            pAig->pSeqModel = pCex;
        }
        else
        {
            Abc_CexFreeP(&pCex);
            Result = -1;
        }
    }
    if ( fVerbose )
        Abc_Print(1, "PDR2: %d candidate cubes, %d relative queries, %d admitted.\n",
            vCubes ? Vec_WecSize(vCubes) : 0, Hints.nTried, Hints.nAdded);
    Pdr2_ManStop(p);
    Gip_OptionsPop(&Options);
    Vec_StrFreeP(&Hints.vUsed);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs concrete PDR with a fixed list of candidate register cubes.]

***********************************************************************/
int Pdr2_ManSolveHints( Aig_Man_t * pAig, Vec_Wec_t * vCubes, abctime TimeStop,
    int (*pFuncStop)(int), int * piFrame, int fVerbose )
{
    return Pdr2_ManSolveFrameHints(pAig, vCubes, TimeStop, pFuncStop, piFrame, fVerbose, NULL, NULL);
}

/**Function*************************************************************

  Synopsis    [Passes the invariant lemmas found by one manager to the other.]

  Description [The inf lemmas of a manager form an inductive invariant,
  so each of them holds in every reachable state and can be added to the
  other manager's frames and inf solver.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManImportInf( Pdr2_Man_t * pTo, Pdr2_Man_t * pFrom )
{
    Pdr2_Lem_t * pLem;
    int i, k;
    if ( pFrom == NULL )
        return;
    for ( i = pFrom->nInfExported; i < Vec_PtrSize(pFrom->vInf); i++ )
    {
        pLem = (Pdr2_Lem_t *)Vec_PtrEntry( pFrom->vInf, i );
        if ( Pdr2_ManIndexFindSubsuming( pTo, pLem->pCube, 1, 0, 1, 0, 0 ) )
            continue;
        {
            Pdr2_Lem_t * pNew = Pdr2_LemAlloc( pTo, pLem->pCube, NULL, -1 );
            Pdr2_ManSolverAddLemma( pTo, pTo->pInf, pLem->pCube, pNew->Id );
            for ( k = 1; k < Vec_PtrSize(pTo->vSolvers); k++ )
                Pdr2_ManSolverAddLemma( pTo, (Gip_Solver_t *)Vec_PtrEntry(pTo->vSolvers, k), pLem->pCube, pNew->Id );
            Vec_PtrPush( pTo->vInf, pNew );
        }
        pTo->nInfLemmas++;
        if ( pTo->pPars->fCtiCache )
        {
            Pdr2_CubeRef( pLem->pCube );
            Vec_PtrPush( pTo->vLog, pLem->pCube );
            Vec_IntPush( pTo->vLogFrame, -1 );
        }
    }
    pFrom->nInfExported = Vec_PtrSize( pFrom->vInf );
}

/**Function*************************************************************

  Synopsis    [Rechecks candidate invariants received from another property partition.]

  Description []

***********************************************************************/
// Parts exchange suggestions, never unchecked assumptions. Each imported
// clause must exclude every initial state and be relatively inductive under
// T and the invariants already accepted by this receiver. This also makes
// projection onto a different sequential cone safe: unmapped clauses are
// skipped, and retained clauses are proved again in the receiving machine.
static void Pdr2_ManImportPartCandidates( Pdr2_Man_t * p, Vec_Wec_t * vPool,
                                         Vec_Int_t * vRegs, int nOriginalRegs )
{
    Vec_Int_t * vMap, * vCube, * vAssump, * vClause, * vRow;
    Gip_Solver_t * pSat = p->pInf;
    abctime Start = Abc_Clock(), Stop;
    int Seconds = Gip_OptionGet("PDR2_PART_SHARE") ? atoi(Gip_OptionGet("PDR2_PART_SHARE")) : 0;
    int i, j, Lit, Reg, Tested = 0, Added = 0;
    if ( !vPool || !Vec_WecSize(vPool) || Seconds <= 0 ) return;
    Stop = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( p->timeGlobal && Stop > p->timeGlobal ) Stop = p->timeGlobal;
    vMap = Vec_IntStartFull(nOriginalRegs);
    for ( i = 0; i < p->nRegs; i++ )
    {
        Reg = vRegs ? Vec_IntEntry(vRegs, i) : i;
        if ( Reg >= 0 && Reg < nOriginalRegs ) Vec_IntWriteEntry(vMap, Reg, i);
    }
    vCube = Vec_IntAlloc(16); vAssump = Vec_IntAlloc(16); vClause = Vec_IntAlloc(16);
    Vec_WecForEachLevel(vPool, vRow, i)
    {
        Pdr2_Cube_t * pCube;
        int Ret, * pClause, nClause;
        if ( Abc_Clock() >= Stop || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId)) ) break;
        Vec_IntClear(vCube);
        Vec_IntForEachEntry(vRow, Lit, j)
        {
            Reg = Abc_Lit2Var(Lit);
            if ( Reg >= nOriginalRegs || Vec_IntEntry(vMap, Reg) < 0 ) break;
            Vec_IntPush(vCube, Abc_Var2Lit(Vec_IntEntry(vMap, Reg), Abc_LitIsCompl(Lit)));
        }
        if ( j < Vec_IntSize(vRow) || !Vec_IntSize(vCube) ) continue;
        pCube = Pdr2_CubeAllocVec(vCube);
        if ( Pdr2_CubeIsInit(p, pCube) || Pdr2_ManIndexFindSubsuming(p, pCube, 1, 0, 1, 0, 0) )
        { Pdr2_CubeDeref(pCube); continue; }
        Vec_IntClear(vAssump); Vec_IntClear(vClause);
        for ( j = 0; j < pCube->nLits; j++ )
        {
            Vec_IntPush(vAssump, Pdr2_LitLi(p, pCube->Lits[j]));
            Vec_IntPush(vClause, Abc_LitNot(Pdr2_LitLo(p, pCube->Lits[j])));
        }
        pClause = Vec_IntArray(vClause); nClause = Vec_IntSize(vClause);
        pSat->nConfLimit = 1000; pSat->TimeLimit = Stop;
        Ret = Gip_SolverSolve(pSat, Vec_IntArray(vAssump), Vec_IntSize(vAssump), &pClause, &nClause, 1, -1);
        Tested++;
        if ( Ret == GIP_UNSAT )
        {
            Pdr2_Lem_t * pNew = Pdr2_LemAlloc(p, pCube, NULL, -1);
            Pdr2_ManSolverAddLemma(p, pSat, pCube, pNew->Id);
            Vec_PtrPush(p->vInf, pNew);
            p->nInfLemmas++;
            Added++;
        }
        Pdr2_CubeDeref(pCube);
    }
    Gip_SolverReset(pSat);
    pSat->nConfLimit = 0; pSat->TimeLimit = 0;
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1, "Property-part candidates: %d imported after %d induction checks, %d available. Time = %.3f sec.\n",
            Added, Tested, Vec_WecSize(vPool), (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Vec_IntFree(vMap); Vec_IntFree(vCube); Vec_IntFree(vAssump); Vec_IntFree(vClause);
}

/**Function*************************************************************

  Synopsis    [Translates candidate invariants into the original register numbering.]

  Description []

***********************************************************************/
static void Pdr2_ManExportPartCandidates( Pdr2_Man_t * p, Vec_Wec_t * vPool, Vec_Int_t * vRegs )
{
    Vec_Int_t * vCube = Vec_IntAlloc(16), * vRow;
    Pdr2_Lem_t * pLem;
    int k, i, j, t;
    // Infinity first, then the frontier. Keep the exchange bounded and prefer
    // short clauses; candidates may come from an unfinished part as well.
    for ( k = Pdr2_ManFrameNum(p); k >= 1 && Vec_WecSize(vPool) < 2048; k-- )
        Vec_PtrForEachEntry(Pdr2_Lem_t *, k == Pdr2_ManFrameNum(p) ? p->vInf : Pdr2_ManFrame(p, k), pLem, i)
        {
            if ( pLem->fRemoved || pLem->pCube->nLits > 8 || Vec_WecSize(vPool) >= 2048 ) continue;
            Vec_IntClear(vCube);
            for ( j = 0; j < pLem->pCube->nLits; j++ )
            {
                int Lit = pLem->pCube->Lits[j], Reg = Abc_Lit2Var(Lit);
                Vec_IntPush(vCube, Abc_Var2Lit(vRegs ? Vec_IntEntry(vRegs, Reg) : Reg, Abc_LitIsCompl(Lit)));
            }
            Vec_IntSort(vCube, 0);
            Vec_WecForEachLevel(vPool, vRow, t)
                if ( Vec_IntSize(vRow) == Vec_IntSize(vCube) &&
                     !memcmp(Vec_IntArray(vRow), Vec_IntArray(vCube), sizeof(int)*Vec_IntSize(vCube)) ) break;
            if ( t == Vec_WecSize(vPool) )
                Vec_IntAppend(Vec_WecPushLevel(vPool), vCube);
        }
    Vec_IntFree(vCube);
}

/**Function*************************************************************

  Synopsis    [Derives the design with all-zero initial values.]

  Description [For the engines that assume them (the BMC stage). A flop
  initialized to 1 is complemented. A flop with a don't-care initial value
  is replaced in the first frame by a new primary input (added after the
  others, in the order of the flops), selected by a new last register that
  is 0 in the first frame and 1 after it. Returns the number of the new
  inputs in *pnNewPis.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Aig_Man_t * Pdr2_ManDupZeroInit( Aig_Man_t * pAig, char * pInit, int * pnNewPis )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pFirst;
    Vec_Ptr_t * vNewPis = Vec_PtrAlloc( 100 );
    int i, k = 0;
    pNew = Aig_ManStart( Aig_ManObjNumMax(pAig) + 2 * Aig_ManRegNum(pAig) + 2 );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pNew );
    Saig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    // the inputs giving the first-frame values of the don't-care flops
    Saig_ManForEachLo( pAig, pObj, i )
        if ( pInit[i] == 2 )
            Vec_PtrPush( vNewPis, Aig_ObjCreateCi(pNew) );
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_NotCond( Aig_ObjCreateCi(pNew), pInit[i] == 1 );
    if ( Vec_PtrSize(vNewPis) )
    {
        pFirst = Aig_ObjCreateCi( pNew );
        Saig_ManForEachLo( pAig, pObj, i )
            if ( pInit[i] == 2 )
                pObj->pData = Aig_Mux( pNew, pFirst, (Aig_Obj_t *)pObj->pData, (Aig_Obj_t *)Vec_PtrEntry(vNewPis, k++) );
    }
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Saig_ManForEachPo( pAig, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_NotCond(Aig_ObjChild0Copy(pObj), pInit[i] == 1) );
    if ( Vec_PtrSize(vNewPis) )
        Aig_ObjCreateCo( pNew, Aig_ManConst1(pNew) );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(pAig) + (Vec_PtrSize(vNewPis) > 0) );
    Aig_ManCleanup( pNew );
    *pnNewPis = Vec_PtrSize( vNewPis );
    Vec_PtrFree( vNewPis );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Maps a counterexample of Pdr2_ManDupZeroInit() back.]

  Description [The inputs of the original design keep their values; the
  initial state takes the defined initial values and, for the don't-care
  flops, the values of the new inputs in the first frame.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Pdr2_ManCexFromZeroInit( Aig_Man_t * pAig, char * pInit, Abc_Cex_t * pCexZero )
{
    int nPis = Saig_ManPiNum(pAig), nRegs = Aig_ManRegNum(pAig);
    Abc_Cex_t * pCex = Abc_CexAlloc( nRegs, nPis, pCexZero->iFrame + 1 );
    int i, f, k = 0;
    pCex->iPo    = pCexZero->iPo;
    pCex->iFrame = pCexZero->iFrame;
    for ( i = 0; i < nRegs; i++ )
        if ( pInit[i] == 2 ? Abc_InfoHasBit(pCexZero->pData, pCexZero->nRegs + nPis + k++) : pInit[i] == 1 )
            Abc_InfoSetBit( pCex->pData, i );
    for ( f = 0; f <= pCex->iFrame; f++ )
        for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(pCexZero->pData, pCexZero->nRegs + f * pCexZero->nPis + i) )
                Abc_InfoSetBit( pCex->pData, nRegs + f * nPis + i );
    return pCex;
}


/**Function*************************************************************

  Synopsis    [Checks the caller's cancellation callback during simulation.]

  Description []

***********************************************************************/
static int Pdr2_ManSimTraceStop( void * pData )
{
    Pdr2_Par_t * pPars = (Pdr2_Par_t *)pData;
    return pPars->pFuncStop && pPars->pFuncStop(pPars->RunId);
}

/**Function*************************************************************

  Synopsis    [Searches for and replays a witness from bounded simulation and state walks.]

  Description []

***********************************************************************/
static int Pdr2_ManSimTrace( Aig_Man_t * pAigOrig, char * pInit, Pdr2_Par_t * pPars,
                             abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Seconds = Gip_OptionGet("PDR2_SIMTRACE") ? Abc_MaxInt(0, Abc_MinInt(60, atoi(Gip_OptionGet("PDR2_SIMTRACE")))) : 0;
    int Mode = Gip_OptionGet("PDR2_SIMTRACE_MODE") ? atoi(Gip_OptionGet("PDR2_SIMTRACE_MODE")) & 3 : 3;
    int i, nExtra = 0, Result;
    abctime Start = Abc_Clock(), Budget = (abctime)Seconds*CLOCKS_PER_SEC;
    Aig_Man_t * pWork = pAigOrig;
    Gia_Man_t * pGia;
    Imc_Par_t Pars;
    Abc_Cex_t * pCex;
    *ppCex = NULL;
    if ( !Seconds || !Mode || pPars->nPropLimit || pPars->nFrameMax ||
         Aig_ManBufNum(pAigOrig) || Aig_ManExorNum(pAigOrig) ) return -1;
    if ( timeGlobal && timeGlobal-Start < Budget ) Budget = timeGlobal-Start;
    if ( Budget <= 0 || Pdr2_ManSimTraceStop(pPars) ) return -1;
    for ( i = 0; i < Aig_ManRegNum(pAigOrig); i++ ) if ( pInit[i] ) break;
    if ( i < Aig_ManRegNum(pAigOrig) ) pWork = Pdr2_ManDupZeroInit(pAigOrig, pInit, &nExtra);
    pGia = Gia_ManFromAigSimple(pWork);
    Imc_ManSetDefaultParams(&Pars);
    Pars.nTimeOut = 0; Pars.fVerbose = 0;
    Budget -= Abc_Clock()-Start;
    Result = Budget > 0 ? Imc_ManFindCexWithStop(pGia, &Pars, Budget, Mode, Pdr2_ManSimTraceStop, pPars) : 0;
    pCex = Result ? pGia->pCexSeq : NULL;
    if ( pCex )
    {
        pGia->pCexSeq = NULL;
        if ( pWork != pAigOrig )
        {
            *ppCex = Pdr2_ManCexFromZeroInit(pAigOrig, pInit, pCex);
            Abc_CexFree(pCex);
        }
        else *ppCex = pCex;
        if ( !Saig_ManVerifyCex(pAigOrig, *ppCex) )
        {
            Abc_Print(1, "Concrete simulation counterexample verification FAILED.\n");
            Abc_CexFreeP(ppCex);
        }
    }
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Concrete simulation (mode %d): %s in %.3f sec.\n", Mode,
            *ppCex ? "checked counterexample" : "no counterexample", (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Gia_ManStop(pGia);
    if ( pWork != pAigOrig ) Aig_ManStop(pWork);
    return *ppCex ? 0 : -1;
}

/**Function*************************************************************

  Synopsis    [Checks an induction step and its matching base prefix.]

  Description []

***********************************************************************/
// First discover a sufficient induction depth, then discharge every base
// frame. An inductive step alone is never accepted as a safety proof.
static int Pdr2_ManKindPrefix( Aig_Man_t * pAigOrig, char * pInit, Pdr2_Par_t * pPars,
                               abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Seconds = Gip_OptionGet("PDR2_KIND_PREFIX") ? Abc_MaxInt(0, Abc_MinInt(300, atoi(Gip_OptionGet("PDR2_KIND_PREFIX")))) : 0;
    int MaxDepth = Gip_OptionGet("PDR2_KIND_DEPTH") ? Abc_MaxInt(1, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_KIND_DEPTH")))) : 64;
    int StepTime = Gip_OptionGet("PDR2_KIND_STEP") ? Abc_MaxInt(1, Abc_MinInt(60, atoi(Gip_OptionGet("PDR2_KIND_STEP")))) : 2;
    int i, nExtra = 0, Depth = -1, Step, Result = -1, Left;
    abctime Start = Abc_Clock(), Stop = Start + (abctime)Seconds*CLOCKS_PER_SEC;
    Aig_Man_t * pWork;
    Saig_ParBmc_t Pars;
    Abc_Cex_t * pCex = NULL;
    *ppCex = NULL;
    if ( !Seconds || pPars->nPropLimit || pPars->nFrameMax || pPars->pFuncStop ||
         pPars->fDumpInv || pPars->fVerifyComplete || !Aig_ManRegNum(pAigOrig) ||
         Aig_ManBufNum(pAigOrig) || Aig_ManExorNum(pAigOrig) ||
         (double)(MaxDepth+1)*Aig_ManNodeNum(pAigOrig) > 2000000 ) return -1;
    if ( timeGlobal && timeGlobal < Stop ) Stop = timeGlobal;
    Left = (int)((Stop-Abc_Clock())/CLOCKS_PER_SEC);
    if ( Left < 1 ) return -1;
    for ( i = 0; i < Aig_ManRegNum(pAigOrig); i++ ) if ( pInit[i] ) break;
    pWork = i < Aig_ManRegNum(pAigOrig) ? Pdr2_ManDupZeroInit(pAigOrig, pInit, &nExtra) : Aig_ManDupSimple(pAigOrig);
    Step = Saig_ManInductionWithDepth(pWork, Abc_MinInt(StepTime, Left), MaxDepth+1, 10000, 0, 0, 0, 0, 0, &Depth);
    Left = (int)((Stop-Abc_Clock())/CLOCKS_PER_SEC);
    Saig_ParBmcSetDefaultParams(&Pars);
    Pars.iFrame = -1;
    if ( Step == 1 && Depth >= 0 && Left >= 1 )
    {
        Pars.nTimeOut = Left;
        Pars.nFramesMax = Depth+1;
        Pars.nStart = Pars.nFramesJump = 0;
        Pars.nConfLimit = 100000;
        Pars.fSilent = 1;
        Result = Saig_ManBmcScalable(pWork, &Pars);
        if ( Result == 0 && pWork->pSeqModel )
        {
            pCex = pWork->pSeqModel; pWork->pSeqModel = NULL;
            if ( i < Aig_ManRegNum(pAigOrig) )
            {
                *ppCex = Pdr2_ManCexFromZeroInit(pAigOrig, pInit, pCex);
                Abc_CexFree(pCex);
            }
            else *ppCex = pCex;
            if ( !Saig_ManVerifyCex(pAigOrig, *ppCex) )
            {
                Abc_Print(1, "Induction-base counterexample verification FAILED.\n");
                Abc_CexFreeP(ppCex);
            }
            Result = *ppCex ? 0 : -1;
        }
        else if ( Result == 0 ) Result = -1;
        // With no frame skipping or solve-all mode, iFrame is the last
        // fully checked frame, including on timeout/conflict-limit exits.
        else if ( Result == -1 && Pars.iFrame >= Depth ) Result = 1;
    }
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Induction prelude: step %s at %d, base through %d; %s in %.3f sec.\n",
            Step == 1 ? "proved" : "undecided", Depth, Pars.iFrame,
            Result == 1 ? "proved" : *ppCex ? "checked counterexample" : "undecided",
            (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Aig_ManStop(pWork);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs a bounded BMC stage on the concrete design.]

  Description [Returns 0 with a counterexample in ppCex, 1 if all
  reachable states were visited, and -1 if undecided. The stage has a
  wall-time budget and also respects the remaining global deadline. BMC
  assumes all-zero initial values: with other initial values (pInit),
  it runs on the design of Pdr2_ManDupZeroInit() and the counterexample
  is mapped back.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManBmcStage( Aig_Man_t * pAigOrig, char * pInit, Pdr2_Par_t * pPars, abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    Saig_ParBmc_t Pars;
    Abc_Cex_t * pCex = NULL;
    Aig_Man_t * pAig = pAigOrig;
    abctime clk = Abc_Clock();
    int i, RetValue, nTime = pPars->nBmcTime, nNewPis = 0;
    *ppCex = NULL;
    // The BMC stage and its zero-reset conversion require a sequential AND/inverter graph.
    if ( !Aig_ManRegNum(pAigOrig) || Aig_ManExorNum(pAigOrig) || Aig_ManBufNum(pAigOrig) )
        return -1;
    if ( timeGlobal )
    {
        int Left = (int)((timeGlobal - Abc_Clock()) / CLOCKS_PER_SEC);
        if ( Left < 1 )
            return -1;
        nTime = Abc_MinInt( nTime, Left );
    }
    for ( i = 0; i < Aig_ManRegNum(pAigOrig); i++ )
        if ( pInit[i] )
            break;
    if ( i < Aig_ManRegNum(pAigOrig) )
        pAig = Pdr2_ManDupZeroInit( pAigOrig, pInit, &nNewPis );
    Saig_ParBmcSetDefaultParams( &Pars );
    Pars.nTimeOut = nTime;
    Pars.timeCnfStop = pPars->timePolicyStop < 0 ? timeGlobal : pPars->timePolicyStop;
    if ( Gip_OptionGet("PDR2_BMC_CONFS") )
        Pars.nConfLimit = Abc_MaxInt( 1, atoi(Gip_OptionGet("PDR2_BMC_CONFS")) );
    if ( Gip_OptionGet("PDR2_BMC_FRAMES") )
        Pars.nFramesMax = Abc_MaxInt( 1, atoi(Gip_OptionGet("PDR2_BMC_FRAMES")) );
    if ( Gip_OptionGet("PDR2_BMC_HORIZON") )
    {
        Pars.nStart = Abc_MaxInt(Gip_OptionGet("PDR2_BMC_TERMS") ? 0 : 1, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_BMC_HORIZON"))));
        Pars.nFramesMax = Pars.nStart + 1;
        Pars.fUseCadical = 1;
    }
    Pars.fSilent  = 1;
    Pars.RunId = pPars->RunId;
    Pars.pFuncStop = pPars->pFuncStop;
    if ( Gip_OptionGet("PDR2_BMC_HORIZON") && Gip_OptionGet("PDR2_BMC_TERMS") )
    {
        Bmc_GiaPar_t GiaPars;
        Gia_Man_t * pGia = Gia_ManFromAigSimple(pAig);
        Bmc_GiaSetDefaultParams(&GiaPars);
        GiaPars.nTimeOut = nTime; GiaPars.TimeToStop = timeGlobal;
        if ( Gip_OptionGet("PDR2_BMC_CONFS") ) GiaPars.nConfLimit = Pars.nConfLimit;
        GiaPars.nMemoryLimit = 2048;
        GiaPars.fSilent = 1; GiaPars.fVerbose = pPars->fVerbose && !pPars->fSilent;
        GiaPars.pFuncStop = Pdr2_ManSimTraceStop; GiaPars.pStopData = pPars;
        RetValue = Bmc_GiaFindTarget(pGia, &GiaPars, Pars.nStart, atoi(Gip_OptionGet("PDR2_BMC_TERMS")),
                                   Gip_OptionGet("PDR2_BMC_WINDOW") ? atoi(Gip_OptionGet("PDR2_BMC_WINDOW")) : 0,
                                   Gip_OptionGet("PDR2_BMC_POLAR") && atoi(Gip_OptionGet("PDR2_BMC_POLAR")));
        if ( RetValue == 0 )
        {
            Abc_CexFreeP(&pAig->pSeqModel);
            pAig->pSeqModel = pGia->pCexSeq; pGia->pCexSeq = NULL;
        }
        Gia_ManStop(pGia);
        Pars.iFrame = GiaPars.iFrame;
    }
    else RetValue = Saig_ManBmcScalable( pAig, &Pars );
    if ( RetValue == 0 && pAig->pSeqModel )
    {
        pCex = pAig->pSeqModel;
        pAig->pSeqModel = NULL;
    }
    else if ( RetValue == 0 || Pars.nStart )
        RetValue = -1;
    if ( pAig != pAigOrig )
    {
        if ( pCex )
        {
            Abc_Cex_t * pCexOrig = Pdr2_ManCexFromZeroInit( pAigOrig, pInit, pCex );
            Abc_CexFree( pCex );
            pCex = pCexOrig;
        }
        Aig_ManStop( pAig );
    }
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "BMC stage (%d sec): %s at frame %d.  Time = %.2f sec\n", nTime,
            pCex ? "counterexample" : RetValue == 1 ? "all reachable states visited" : "no counterexample",
            pCex ? pCex->iFrame : Pars.iFrame, (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
    *ppCex = pCex;
    return RetValue;
}

typedef struct Pdr2_ExplicitState_t_ Pdr2_ExplicitState_t;
struct Pdr2_ExplicitState_t_ { unsigned State, Parent, Input; };
typedef struct Pdr2_Explicit_t_ Pdr2_Explicit_t;
struct Pdr2_Explicit_t_
{
    Pdr2_ExplicitState_t * pStates;
    word * pHash;
    unsigned nStates, nAlloc, nHash, nMax;
};

/**Function*************************************************************

  Synopsis    [Hashes a concrete register assignment.]

  Description []

***********************************************************************/
static unsigned Pdr2_ExplicitHash( unsigned State )
{
    State ^= State >> 16; State *= 0x7feb352du;
    State ^= State >> 15; State *= 0x846ca68bu;
    return State ^ (State >> 16);
}

/**Function*************************************************************

  Synopsis    [Adds an unseen assignment and its predecessor to the reachability queue.]

  Description []

***********************************************************************/
// The hash stores the full state and its queue index, so no fingerprint
// collision can be mistaken for an already visited state.
static int Pdr2_ExplicitInsert( Pdr2_Explicit_t * p, unsigned State, unsigned Parent, unsigned Input )
{
    unsigned h = Pdr2_ExplicitHash(State) & (p->nHash - 1), i;
    while ( p->pHash[h] )
    {
        if ( (unsigned)(p->pHash[h] >> 32) == State ) return 0;
        h = (h + 1) & (p->nHash - 1);
    }
    if ( p->nStates == p->nMax ) return -1;
    if ( 2 * p->nStates >= p->nHash )
    {
        word * pOld = p->pHash;
        unsigned nOld = p->nHash;
        p->nHash *= 2;
        p->pHash = ABC_CALLOC( word, p->nHash );
        for ( i = 0; i < nOld; i++ ) if ( pOld[i] )
        {
            h = Pdr2_ExplicitHash((unsigned)(pOld[i] >> 32)) & (p->nHash - 1);
            while ( p->pHash[h] ) h = (h + 1) & (p->nHash - 1);
            p->pHash[h] = pOld[i];
        }
        ABC_FREE( pOld );
        h = Pdr2_ExplicitHash(State) & (p->nHash - 1);
        while ( p->pHash[h] ) h = (h + 1) & (p->nHash - 1);
    }
    if ( p->nStates == p->nAlloc )
    {
        p->nAlloc = Abc_MinInt( 2 * p->nAlloc, p->nMax );
        p->pStates = ABC_REALLOC( Pdr2_ExplicitState_t, p->pStates, p->nAlloc );
    }
    p->pStates[p->nStates].State = State;
    p->pStates[p->nStates].Parent = Parent;
    p->pStates[p->nStates].Input = Input;
    p->pHash[h] = ((word)State << 32) | (word)(++p->nStates);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reconstructs a counterexample from the explicit search's predecessor links.]

  Description []

***********************************************************************/
static Abc_Cex_t * Pdr2_ExplicitCex( Pdr2_Explicit_t * p, unsigned Index, unsigned Input, int nRegs, int nPis )
{
    unsigned i = Index, nSteps = 0, Root;
    int b, f;
    Abc_Cex_t * pCex;
    while ( p->pStates[i].Parent != ~0u ) { nSteps++; i = p->pStates[i].Parent; }
    Root = p->pStates[i].State;
    pCex = Abc_CexAlloc( nRegs, nPis, nSteps + 1 );
    pCex->iFrame = nSteps;
    pCex->iPo = 0;
    for ( b = 0; b < nRegs; b++ )
        if ( (Root >> b) & 1 ) Abc_InfoSetBit( pCex->pData, b );
    i = Index;
    for ( f = nSteps; f >= 0; f-- )
    {
        for ( b = 0; b < nPis; b++ )
            if ( (Input >> b) & 1 ) Abc_InfoSetBit( pCex->pData, nRegs + f * nPis + b );
        Input = p->pStates[i].Input;
        if ( f ) i = p->pStates[i].Parent;
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Explores the concrete reachable states using word-parallel transition evaluation.]

  Description []

***********************************************************************/
// Enumerate every successor of every reachable state, packing up to 64
// state/input pairs into one AIG evaluation. A resource stop is undecided;
// only exhausting the exact visited-state queue is a proof.
static int Pdr2_ManExplicitReach( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars, abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    static const word Truth[6] = { ABC_CONST(0xaaaaaaaaaaaaaaaa), ABC_CONST(0xcccccccccccccccc),
        ABC_CONST(0xf0f0f0f0f0f0f0f0), ABC_CONST(0xff00ff00ff00ff00),
        ABC_CONST(0xffff0000ffff0000), ABC_CONST(0xffffffff00000000) };
    Pdr2_Explicit_t E = { NULL, NULL, 0, 1024, 2048, 1u << 22 };
    Aig_Obj_t * pObj;
    word * pValues, Bad, Mask, a, b;
    unsigned Base = 0, Unknown[32], nUnknown = 0, Head = 0, State, Input, Next, j, g, c, lane, nGroup, nLanes;
    unsigned nInputs, nPack, nChunks;
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig), i, k, RetValue = -1;
    int nSeconds = Gip_OptionGet("PDR2_EXPLICIT") ? atoi(Gip_OptionGet("PDR2_EXPLICIT")) : 0;
    abctime Start = Abc_Clock(), Deadline;
    if ( nSeconds <= 0 || nRegs > 32 || nPis > 8 || pPars->nFrameMax || pPars->nPropLimit || Aig_ManBufNum(pAig) ) return -1;
    Deadline = Start + (abctime)nSeconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Deadline > timeGlobal ) Deadline = timeGlobal;
    if ( Gip_OptionGet("PDR2_EXPLICIT_MAX") )
        E.nMax = Abc_MaxInt( 1, Abc_MinInt( 1 << 26, atoi(Gip_OptionGet("PDR2_EXPLICIT_MAX")) ) );
    for ( i = 0; i < nRegs; i++ )
        if ( pInit[i] == 2 ) Unknown[nUnknown++] = i;
        else if ( pInit[i] == 1 ) Base |= 1u << i;
    if ( nUnknown > 20 || (1u << nUnknown) > E.nMax ) return -1;
    E.nAlloc = Abc_MinInt( E.nAlloc, E.nMax );
    E.pStates = ABC_ALLOC( Pdr2_ExplicitState_t, E.nAlloc );
    E.pHash = ABC_CALLOC( word, E.nHash );
    pValues = ABC_CALLOC( word, Aig_ManObjNumMax(pAig) );
    for ( j = 0; j < (1u << nUnknown); j++ )
    {
        State = Base;
        for ( k = 0; k < (int)nUnknown; k++ ) State |= ((j >> k) & 1) << Unknown[k];
        Pdr2_ExplicitInsert( &E, State, ~0u, 0 );
    }
    nInputs = 1u << nPis;
    nPack = nPis < 6 ? 64 / nInputs : 1;
    nChunks = nPis > 6 ? nInputs / 64 : 1;
    pValues[Aig_ObjId(Aig_ManConst1(pAig))] = ~(word)0;
    while ( Head < E.nStates )
    {
        if ( Abc_Clock() >= Deadline || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) goto finish;
        nGroup = Abc_MinInt( nPack, E.nStates - Head );
        nLanes = nPis < 6 ? nGroup * nInputs : 64;
        Saig_ManForEachLo( pAig, pObj, i )
        {
            a = 0;
            for ( g = 0; g < nGroup; g++ )
                if ( (E.pStates[Head + g].State >> i) & 1 )
                    a |= nPis >= 6 ? ~(word)0 : (((word)1 << nInputs) - 1) << (g * nInputs);
            pValues[Aig_ObjId(pObj)] = a;
        }
        for ( c = 0; c < nChunks; c++ )
        {
            Saig_ManForEachPi( pAig, pObj, i )
                pValues[Aig_ObjId(pObj)] = i < 6 ? Truth[i] : ((c >> (i - 6)) & 1) ? ~(word)0 : 0;
            Aig_ManForEachNode( pAig, pObj, i )
            {
                a = pValues[Aig_ObjId(Aig_ObjFanin0(pObj))] ^ (Aig_ObjFaninC0(pObj) ? ~(word)0 : 0);
                b = pValues[Aig_ObjId(Aig_ObjFanin1(pObj))] ^ (Aig_ObjFaninC1(pObj) ? ~(word)0 : 0);
                pValues[Aig_ObjId(pObj)] = Aig_ObjIsExor(pObj) ? a ^ b : a & b;
            }
            Aig_ManForEachCo( pAig, pObj, i )
                pValues[Aig_ObjId(pObj)] = pValues[Aig_ObjId(Aig_ObjFanin0(pObj))] ^ (Aig_ObjFaninC0(pObj) ? ~(word)0 : 0);
            Bad = pValues[Aig_ObjId(Aig_ManCo(pAig, 0))];
            Mask = nLanes == 64 ? ~(word)0 : ((word)1 << nLanes) - 1;
            if ( Bad & Mask )
            {
                for ( lane = 0; lane < nLanes; lane++ ) if ( (Bad >> lane) & 1 ) break;
                g = nPis < 6 ? lane / nInputs : 0;
                Input = nPis < 6 ? lane % nInputs : 64 * c + lane;
                *ppCex = Pdr2_ExplicitCex( &E, Head + g, Input, nRegs, nPis );
                RetValue = 0;
                goto finish;
            }
            for ( lane = 0; lane < nLanes; lane++ )
            {
                Next = 0;
                Saig_ManForEachLi( pAig, pObj, i )
                    Next |= (unsigned)((pValues[Aig_ObjId(pObj)] >> lane) & 1) << i;
                g = nPis < 6 ? lane / nInputs : 0;
                Input = nPis < 6 ? lane % nInputs : 64 * c + lane;
                if ( Pdr2_ExplicitInsert(&E, Next, Head + g, Input) < 0 ) goto finish;
            }
        }
        Head += nGroup;
    }
    RetValue = 1;
finish:
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Explicit reachability: %u states visited, %u expanded; %s. Time = %.3f sec.\n",
            E.nStates, Head, RetValue == 1 ? "proved" : RetValue == 0 ? "counterexample" : "resource limit",
            (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    ABC_FREE( E.pStates ); ABC_FREE( E.pHash ); ABC_FREE( pValues );
    return RetValue;
}
#ifdef ABC_USE_CUDD
typedef struct Pdr2_BddStop_t_ { Pdr2_Par_t * pPars; abctime Deadline; } Pdr2_BddStop_t;

/**Function*************************************************************

  Synopsis    [Checks the deadline and cancellation callback for BDD operations.]

  Description []

***********************************************************************/
static int Pdr2_BddStop( void * pData )
{
    Pdr2_BddStop_t * p = (Pdr2_BddStop_t *)pData;
    return Abc_Clock() >= p->Deadline || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId));
}

/**Function*************************************************************

  Synopsis    [Takes a reference to a successfully constructed BDD.]

  Description []

***********************************************************************/
static DdNode * Pdr2_BddRef( DdNode * p ) { if ( p ) Cudd_Ref( p ); return p; }

/**Function*************************************************************

  Synopsis    [Checks safety by repeated squaring of the BDD transition relation.]

  Description []

***********************************************************************/
// Relation squaring includes identity, so iteration k covers all paths of
// length at most 2^k. A closed safe set is an exact proof. A reachable bad
// state merely falls back to PDR, which supplies and verifies the trace.
static int Pdr2_ManBddSquare( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars, abctime timeGlobal )
{
    int Seconds = Gip_OptionGet("PDR2_BDDSQUARE") ? atoi(Gip_OptionGet("PDR2_BDDSQUARE")) : 0;
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig), nVars;
    int MaxRegs = Gip_OptionGet("PDR2_BDD_REGS") ? Abc_MinInt(2048, atoi(Gip_OptionGet("PDR2_BDD_REGS"))) : 64;
    int MaxPis = Gip_OptionGet("PDR2_BDD_PIS") ? Abc_MinInt(8192, atoi(Gip_OptionGet("PDR2_BDD_PIS"))) : 32;
    int fEarlyQ = Gip_OptionGet("PDR2_BDD_EARLYQ") && atoi(Gip_OptionGet("PDR2_BDD_EARLYQ"));
    int VarOrder = Gip_OptionGet("PDR2_BDD_ORDER") ? atoi(Gip_OptionGet("PDR2_BDD_ORDER")) : 0;
    int i, Iter = 0, Result = -1, fBad = 0, fCheck = Gip_OptionGet("PDR2_BDD_CHECK") != NULL;
    unsigned Limit = Gip_OptionGet("PDR2_BDD_NODES") ? Abc_MaxInt(1024, atoi(Gip_OptionGet("PDR2_BDD_NODES"))) : 1000000;
    abctime Start = Abc_Clock();
    Pdr2_BddStop_t Stop;
    Aig_Obj_t * pObj;
    DdManager * dd;
    DdNode ** pNodes, * bRelation, * bOneStep, * bStates, * bInitial, * bBad, * bIdentity;
    DdNode * bCubeX, * bCubeZ, * bCubePi, * bTmp, * bTmp2, * bLeft, * bRight, * a, * b;
    int * pYtoX, * pYtoZ, * pXtoZ, * pLastPi;
    const char * pPhase = "AIG functions";
    if ( Seconds <= 0 || nRegs > MaxRegs || nPis > MaxPis || pPars->nFrameMax || pPars->nPropLimit || Aig_ManBufNum(pAig) ) return -1;
    nVars = 3 * nRegs + nPis;
    Stop.pPars = pPars;
    Stop.Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Stop.Deadline > timeGlobal ) Stop.Deadline = timeGlobal;
    dd = Cudd_Init( nVars, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    if ( !dd ) return -1;
    Cudd_SetMaxLive( dd, Limit );
    Cudd_SetStopCallback( dd, Pdr2_BddStop, &Stop );
    if ( VarOrder >= 1 && VarOrder <= 3 )
    {
        int * pOrder = ABC_ALLOC( int, nVars+1 ), j = 0, Ret;
        if ( VarOrder == 1 )
        {
            for ( i = 0; i < nPis; i++ ) pOrder[j++] = 3*nRegs+i;
            for ( i = 0; i < 3*nRegs; i++ ) pOrder[j++] = i;
        }
        else if ( VarOrder == 2 )
            for ( i = 0; i < Abc_MaxInt(nRegs, nPis); i++ )
            {
                if ( i < nRegs ) pOrder[j++] = 3*i;
                if ( i < nPis ) pOrder[j++] = 3*nRegs+i;
                if ( i < nRegs ) { pOrder[j++] = 3*i+1; pOrder[j++] = 3*i+2; }
            }
        else
        {
            int Id, Var, k;
            Aig_Obj_t * pNode;
            int * pCiVar = ABC_ALLOC( int, Aig_ManObjNumMax(pAig) );
            char * pSeen = ABC_CALLOC( char, Aig_ManObjNumMax(pAig) );
            Vec_Int_t * vStack = Vec_IntAlloc( 100 );
            Saig_ManForEachPi( pAig, pObj, i ) pCiVar[Aig_ObjId(pObj)] = 3*nRegs+i;
            Saig_ManForEachLo( pAig, pObj, i ) pCiVar[Aig_ObjId(pObj)] = 3*i;
            // Keep state triples together, but visit their sources in circuit
            // DFS order so variables used by the same arithmetic cone tend
            // to be adjacent instead of separated into interface-wide words.
            Aig_ManForEachCo( pAig, pObj, k )
            {
                Vec_IntPush( vStack, Aig_ObjFaninId0(pObj) );
                while ( Vec_IntSize(vStack) )
                {
                    Id = Vec_IntPop( vStack );
                    if ( pSeen[Id] ) continue;
                    pSeen[Id] = 1;
                    pNode = Aig_ManObj( pAig, Id );
                    if ( Aig_ObjIsCi(pNode) )
                    {
                        Var = pCiVar[Id]; pOrder[j++] = Var;
                        if ( Var < 3*nRegs ) { pOrder[j++] = Var+1; pOrder[j++] = Var+2; }
                    }
                    else if ( Aig_ObjIsNode(pNode) )
                    {
                        Vec_IntPush( vStack, Aig_ObjFaninId1(pNode) );
                        Vec_IntPush( vStack, Aig_ObjFaninId0(pNode) );
                    }
                }
            }
            Aig_ManForEachCi( pAig, pObj, i ) if ( !pSeen[Aig_ObjId(pObj)] )
            {
                Var = pCiVar[Aig_ObjId(pObj)]; pOrder[j++] = Var;
                if ( Var < 3*nRegs ) { pOrder[j++] = Var+1; pOrder[j++] = Var+2; }
            }
            Vec_IntFree( vStack ); ABC_FREE( pSeen ); ABC_FREE( pCiVar );
        }
        assert( j == nVars );
        Ret = Cudd_ShuffleHeap( dd, pOrder );
        ABC_FREE( pOrder );
        if ( !Ret ) { Cudd_Quit(dd); return -1; }
    }
    if ( Gip_OptionGet("PDR2_BDD_REORDER") && atoi(Gip_OptionGet("PDR2_BDD_REORDER")) )
        Cudd_AutodynEnable( dd, CUDD_REORDER_SIFT );
    pNodes = ABC_CALLOC( DdNode *, Aig_ManObjNumMax(pAig) );
    pYtoX = ABC_ALLOC( int, nVars+1 );
    pYtoZ = ABC_ALLOC( int, nVars+1 );
    pXtoZ = ABC_ALLOC( int, nVars+1 );
    pLastPi = ABC_ALLOC( int, nPis+1 );
    for ( i = 0; i < nPis; i++ ) pLastPi[i] = -1;
    for ( i = 0; i < nVars; i++ ) pYtoX[i] = pYtoZ[i] = pXtoZ[i] = i;
    for ( i = 0; i < nRegs; i++ )
    {
        pYtoX[3*i] = 3*i+1; pYtoX[3*i+1] = 3*i;
        pYtoZ[3*i+1] = 3*i+2; pYtoZ[3*i+2] = 3*i+1;
        pXtoZ[3*i] = 3*i+2; pXtoZ[3*i+2] = 3*i;
    }
    pNodes[Aig_ObjId(Aig_ManConst1(pAig))] = Pdr2_BddRef( Cudd_ReadOne(dd) );
    Saig_ManForEachPi( pAig, pObj, i ) pNodes[Aig_ObjId(pObj)] = Pdr2_BddRef( Cudd_bddIthVar(dd, 3*nRegs+i) );
    Saig_ManForEachLo( pAig, pObj, i ) pNodes[Aig_ObjId(pObj)] = Pdr2_BddRef( Cudd_bddIthVar(dd, 3*i) );
    Aig_ManForEachNode( pAig, pObj, i )
    {
        a = Cudd_NotCond( pNodes[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj) );
        b = Cudd_NotCond( pNodes[Aig_ObjFaninId1(pObj)], Aig_ObjFaninC1(pObj) );
        bTmp = Aig_ObjIsExor(pObj) ? Cudd_bddXor(dd, a, b) : Cudd_bddAnd(dd, a, b);
        if ( !bTmp ) goto done;
        pNodes[Aig_ObjId(pObj)] = Pdr2_BddRef( bTmp );
    }
    Aig_ManForEachCo( pAig, pObj, i )
        pNodes[Aig_ObjId(pObj)] = Pdr2_BddRef( Cudd_NotCond(pNodes[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj)) );
    // Once the last next-state function using an input is conjoined, that
    // input can be existentially projected immediately. Fusing conjunction
    // and projection avoids constructing unnecessary input correlations.
    pPhase = "input supports";
    if ( fEarlyQ )
        Saig_ManForEachLi( pAig, pObj, i )
        {
            int j, * pSupp;
            if ( Pdr2_BddStop(&Stop) ) goto done;
            pSupp = Cudd_SupportIndex( dd, pNodes[Aig_ObjId(pObj)] );
            if ( !pSupp ) goto done;
            for ( j = 0; j < nPis; j++ ) if ( pSupp[3*nRegs+j] ) pLastPi[j] = i;
            ABC_FREE( pSupp );
        }
    pPhase = "transition relation";
    bRelation = Pdr2_BddRef( Cudd_ReadOne(dd) );
    bIdentity = Pdr2_BddRef( Cudd_ReadOne(dd) );
    bStates = Pdr2_BddRef( Cudd_ReadOne(dd) );
    bCubeX = Pdr2_BddRef( Cudd_ReadOne(dd) );
    bCubeZ = Pdr2_BddRef( Cudd_ReadOne(dd) );
    bCubePi = Pdr2_BddRef( Cudd_ReadOne(dd) );
    Saig_ManForEachLi( pAig, pObj, i )
    {
        bTmp = Pdr2_BddRef( Cudd_bddXnor(dd, Cudd_bddIthVar(dd, 3*i+1), pNodes[Aig_ObjId(pObj)]) );
        if ( !bTmp ) goto done;
        if ( fEarlyQ )
        {
            DdNode * bQuant = Pdr2_BddRef( Cudd_ReadOne(dd) );
            int j;
            for ( j = 0; j < nPis; j++ ) if ( pLastPi[j] == i )
            {
                DdNode * bNext = Pdr2_BddRef( Cudd_bddAnd(dd, bQuant, Cudd_bddIthVar(dd, 3*nRegs+j)) );
                if ( !bNext ) goto done;
                Cudd_RecursiveDeref( dd, bQuant ); bQuant = bNext;
            }
            bTmp2 = Pdr2_BddRef( Cudd_bddAndAbstract(dd, bRelation, bTmp, bQuant) );
            Cudd_RecursiveDeref( dd, bQuant );
        }
        else
            bTmp2 = Pdr2_BddRef( Cudd_bddAnd(dd, bRelation, bTmp) );
        if ( !bTmp2 ) goto done;
        Cudd_RecursiveDeref( dd, bTmp ); Cudd_RecursiveDeref( dd, bRelation ); bRelation = bTmp2;
        bTmp = Pdr2_BddRef( Cudd_bddXnor(dd, Cudd_bddIthVar(dd, 3*i), Cudd_bddIthVar(dd, 3*i+1)) );
        if ( !bTmp ) goto done;
        bTmp2 = Pdr2_BddRef( Cudd_bddAnd(dd, bIdentity, bTmp) );
        if ( !bTmp2 ) goto done;
        Cudd_RecursiveDeref( dd, bTmp ); Cudd_RecursiveDeref( dd, bIdentity ); bIdentity = bTmp2;
        if ( pInit[i] != 2 )
        {
            bTmp = Pdr2_BddRef( Cudd_bddAnd(dd, bStates, Cudd_NotCond(Cudd_bddIthVar(dd, 3*i), !pInit[i])) );
            if ( !bTmp ) goto done;
            Cudd_RecursiveDeref( dd, bStates ); bStates = bTmp;
        }
        bTmp = Pdr2_BddRef( Cudd_bddAnd(dd, bCubeX, Cudd_bddIthVar(dd, 3*i)) );
        if ( !bTmp ) goto done;
        Cudd_RecursiveDeref( dd, bCubeX ); bCubeX = bTmp;
        bTmp = Pdr2_BddRef( Cudd_bddAnd(dd, bCubeZ, Cudd_bddIthVar(dd, 3*i+2)) );
        if ( !bTmp ) goto done;
        Cudd_RecursiveDeref( dd, bCubeZ ); bCubeZ = bTmp;
    }
    for ( i = 0; i < nPis; i++ )
    {
        bTmp = Pdr2_BddRef( Cudd_bddAnd(dd, bCubePi, Cudd_bddIthVar(dd, 3*nRegs+i)) );
        if ( !bTmp ) goto done;
        Cudd_RecursiveDeref( dd, bCubePi ); bCubePi = bTmp;
    }
    pPhase = "input projection";
    bBad = Pdr2_BddRef( Cudd_bddExistAbstract(dd, pNodes[Aig_ObjId(Aig_ManCo(pAig,0))], bCubePi) );
    if ( !bBad ) goto done;
    bTmp = Pdr2_BddRef( Cudd_bddExistAbstract(dd, bRelation, bCubePi) );
    if ( !bTmp ) goto done;
    Cudd_RecursiveDeref( dd, bRelation ); bRelation = bTmp;
    bOneStep = Pdr2_BddRef( bRelation );
    bInitial = Pdr2_BddRef( bStates );
    bTmp = Pdr2_BddRef( Cudd_bddOr(dd, bRelation, bIdentity) );
    if ( !bTmp ) goto done;
    Cudd_RecursiveDeref( dd, bRelation ); bRelation = bTmp;
    Cudd_RecursiveDeref( dd, bIdentity );
    for ( i = 0; i < Aig_ManObjNumMax(pAig); i++ )
        if ( pNodes[i] ) { Cudd_RecursiveDeref(dd, pNodes[i]); pNodes[i] = NULL; }
    pPhase = "closure";
    while ( !Pdr2_BddStop(&Stop) )
    {
        bTmp = Pdr2_BddRef( Cudd_bddAnd(dd, bStates, bBad) );
        if ( !bTmp ) goto done;
        fBad = bTmp != Cudd_Not(Cudd_ReadOne(dd));
        Cudd_RecursiveDeref( dd, bTmp );
        if ( fBad ) goto done;
        bTmp = Pdr2_BddRef( Cudd_bddAndAbstract(dd, bStates, bRelation, bCubeX) );
        if ( !bTmp ) goto done;
        bTmp2 = Pdr2_BddRef( Cudd_bddPermute(dd, bTmp, pYtoX) );
        if ( !bTmp2 ) goto done;
        Cudd_RecursiveDeref( dd, bTmp );
        if ( bTmp2 == bStates )
        {
            if ( fCheck )
            {
                DdNode * bCheck = Pdr2_BddRef( Cudd_bddAndAbstract(dd, bStates, bOneStep, bCubeX) );
                DdNode * bCheckX;
                if ( !bCheck ) goto done;
                bCheckX = Pdr2_BddRef( Cudd_bddPermute(dd, bCheck, pYtoX) );
                if ( !bCheckX ) goto done;
                assert( Cudd_bddLeq(dd, bCheckX, bStates) && Cudd_bddLeq(dd, bInitial, bStates) );
                Cudd_RecursiveDeref( dd, bCheck ); Cudd_RecursiveDeref( dd, bCheckX );
            }
            Result = 1;
            goto done;
        }
        Cudd_RecursiveDeref( dd, bStates ); bStates = bTmp2;
        bLeft = Pdr2_BddRef( Cudd_bddPermute(dd, bRelation, pYtoZ) );
        if ( !bLeft ) goto done;
        bRight = Pdr2_BddRef( Cudd_bddPermute(dd, bRelation, pXtoZ) );
        if ( !bRight ) goto done;
        bTmp = Pdr2_BddRef( Cudd_bddAndAbstract(dd, bLeft, bRight, bCubeZ) );
        if ( !bTmp ) goto done;
        Cudd_RecursiveDeref( dd, bLeft ); Cudd_RecursiveDeref( dd, bRight );
        Cudd_RecursiveDeref( dd, bRelation ); bRelation = bTmp;
        Iter++;
    }
done:
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "BDD relation squaring: %d iterations, %.0f peak nodes; %s (%s). Time = %.3f sec.\n",
            Iter, (double)Cudd_ReadPeakNodeCount(dd), Result == 1 ? "proved" : fBad ? "bad state reachable; trace deferred to PDR" : "resource limit", pPhase, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC );
    Cudd_SetStopCallback( dd, NULL, NULL );
    Cudd_Quit( dd );
    ABC_FREE( pNodes ); ABC_FREE( pYtoX ); ABC_FREE( pYtoZ ); ABC_FREE( pXtoZ ); ABC_FREE( pLastPi );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Constructs a sequential cone with unconstrained inputs at its boundary.]

  Description []

***********************************************************************/
// Localize the transition relation for a proof-only prelude. State outside
// a bounded backward cone becomes a fresh unconstrained input at each step.
// Every concrete trace projects to an abstract trace. Thus unreachability
// transfers to the original machine; abstract counterexamples do not.
static Aig_Man_t * Pdr2_ManBddAbstract( Aig_Man_t * pAig, char * pInit,
                                     int Depth, char ** ppInit )
{
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig), i, k, d, nKeep = 0;
    char * pKeep = ABC_CALLOC(char, nRegs+1), * pInitAll;
    Vec_Ptr_t * vWork = Vec_PtrAlloc(100);
    Vec_Int_t * vAdded = Vec_IntAlloc(100), * vPis, * vRegs;
    Aig_Obj_t * pObj;
    Aig_Man_t * pAll, * pNew;
    Aig_ManSetCioIds(pAig);
    Vec_PtrPush(vWork, Aig_ManCo(pAig, 0));
    for ( d = 0; d <= Depth; d++ )
    {
        Aig_ManIncrementTravId(pAig);
        Vec_IntClear(vAdded);
        while ( Vec_PtrSize(vWork) )
        {
            pObj = (Aig_Obj_t *)Vec_PtrPop(vWork);
            if ( Aig_ObjIsTravIdCurrent(pAig, pObj) ) continue;
            Aig_ObjSetTravIdCurrent(pAig, pObj);
            if ( Aig_ObjIsNode(pObj) )
            {
                Vec_PtrPush(vWork, Aig_ObjFanin0(pObj));
                Vec_PtrPush(vWork, Aig_ObjFanin1(pObj));
            }
            else if ( Aig_ObjIsCo(pObj) ) Vec_PtrPush(vWork, Aig_ObjFanin0(pObj));
            else if ( Aig_ObjIsCi(pObj) && Aig_ObjCioId(pObj) >= nPis )
            {
                i = Aig_ObjCioId(pObj) - nPis;
                if ( !pKeep[i] ) pKeep[i] = 1, nKeep++, Vec_IntPush(vAdded, i);
            }
        }
        if ( d < Depth )
            Vec_IntForEachEntry(vAdded, i, k)
                Vec_PtrPush(vWork, Saig_ManLi(pAig, i));
    }
    pAll = Aig_ManStart(Aig_ManObjNumMax(pAig));
    pAll->pName = Abc_UtilStrsav(pAig->pName);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pAll);
    Saig_ManForEachPi(pAig, pObj, i) pObj->pData = Aig_ObjCreateCi(pAll);
    Saig_ManForEachLo(pAig, pObj, i)
        if ( !pKeep[i] ) pObj->pData = Aig_ObjCreateCi(pAll);
    pInitAll = ABC_CALLOC(char, nKeep+1);
    nKeep = 0;
    Saig_ManForEachLo(pAig, pObj, i)
        if ( pKeep[i] )
        {
            pObj->pData = Aig_ObjCreateCi(pAll);
            pInitAll[nKeep++] = pInit[i];
        }
    Aig_ManForEachNode(pAig, pObj, i)
        pObj->pData = Aig_And(pAll, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ObjCreateCo(pAll, Aig_ObjChild0Copy(Aig_ManCo(pAig, 0)));
    Saig_ManForEachLi(pAig, pObj, i)
        if ( pKeep[i] ) Aig_ObjCreateCo(pAll, Aig_ObjChild0Copy(pObj));
    Aig_ManSetRegNum(pAll, nKeep);
    Aig_ManCleanup(pAll);
    pNew = Pdr2_ManDupCoi(pAll, &vPis, &vRegs);
    *ppInit = ABC_CALLOC(char, Aig_ManRegNum(pNew)+1);
    Vec_IntForEachEntry(vRegs, d, i) (*ppInit)[i] = pInitAll[d];
    Aig_ManStop(pAll);
    Vec_IntFree(vPis); Vec_IntFree(vRegs); Vec_IntFree(vAdded); Vec_PtrFree(vWork);
    ABC_FREE(pKeep); ABC_FREE(pInitAll);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Checks safety with bounded partitioned BDD image computation.]

  Description []

***********************************************************************/
// Use the existing partitioned image engine without materializing a single
// transition relation. Its proof-only interface is cancellable and has a
// memory bound. SAT/limits fall back to PDR and its checked counterexamples.
static int Pdr2_ManPartBdd( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars, abctime timeGlobal )
{
    int Seconds = Gip_OptionGet("PDR2_PARTBDD") ? atoi(Gip_OptionGet("PDR2_PARTBDD")) : 0;
    int MaxRegs = Gip_OptionGet("PDR2_PARTBDD_REGS") ? atoi(Gip_OptionGet("PDR2_PARTBDD_REGS")) : 512;
    int MaxPis = Gip_OptionGet("PDR2_PARTBDD_PIS") ? atoi(Gip_OptionGet("PDR2_PARTBDD_PIS")) : 1024;
    int Memory = Gip_OptionGet("PDR2_PARTBDD_MEM") ? Abc_MaxInt(64, Abc_MinInt(4096, atoi(Gip_OptionGet("PDR2_PARTBDD_MEM")))) : 512;
    int AbsDepth = Gip_OptionGet("PDR2_PARTBDD_ABS") ? Abc_MaxInt(0, Abc_MinInt(16, atoi(Gip_OptionGet("PDR2_PARTBDD_ABS")))) : -1;
    Pdr2_BddStop_t Stop;
    Gia_ParLlb_t Pars;
    Aig_Man_t * pWork, * pAbstract = NULL;
    char * pInitAbstract = NULL;
    abctime Start = Abc_Clock();
    int i, nExtra = 0, Ret;
    if ( Seconds <= 0 || !Aig_ManRegNum(pAig) ||
         Aig_ManNodeNum(pAig) > (AbsDepth >= 0 ? 2000000 : 200000) ||
         pPars->nFrameMax || pPars->nPropLimit || Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ||
         (Gip_OptionGet("PDR2_PARTBDD_PART") && atoi(Gip_OptionGet("PDR2_PARTBDD_PART")) && !pPars->fPartRun) ) return -1;
    Stop.pPars = pPars;
    Stop.Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Stop.Deadline > timeGlobal ) Stop.Deadline = timeGlobal;
    if ( Stop.Deadline - Start < CLOCKS_PER_SEC ) return -1;
    if ( AbsDepth >= 0 )
    {
        pAbstract = Pdr2_ManBddAbstract(pAig, pInit, AbsDepth, &pInitAbstract);
        if ( pPars->fVerbose && !pPars->fSilent )
            Abc_Print(1, "BDD localization depth %d: %d -> %d flops, %d -> %d nodes, %d abstract inputs.\n",
                AbsDepth, Aig_ManRegNum(pAig), Aig_ManRegNum(pAbstract), Aig_ManNodeNum(pAig),
                Aig_ManNodeNum(pAbstract), Saig_ManPiNum(pAbstract));
        pAig = pAbstract; pInit = pInitAbstract;
    }
    if ( !Aig_ManRegNum(pAig) || Aig_ManRegNum(pAig) > MaxRegs ||
         Saig_ManPiNum(pAig) > MaxPis || Aig_ManNodeNum(pAig) > 200000 || Pdr2_BddStop(&Stop) )
    {
        if ( pAbstract ) Aig_ManStop(pAbstract);
        ABC_FREE(pInitAbstract);
        return -1;
    }
    for ( i = 0; i < Aig_ManRegNum(pAig); i++ ) if ( pInit[i] ) break;
    pWork = i == Aig_ManRegNum(pAig) ? Aig_ManDupSimple(pAig) : Pdr2_ManDupZeroInit(pAig, pInit, &nExtra);
    Llb_ManSetDefaultParams(&Pars);
    Pars.fCluster = Pars.fReorder = Pars.fVerbose = Pars.fVeryVerbose = 0;
    Pars.fSilent = 1;
    Pars.nBddMax = 100;
    Pars.nClusterMax = 500;
    Pars.nIterMax = 1000000;
    Pars.TimeLimit = (int)((Stop.Deadline - Start) / CLOCKS_PER_SEC);
    if ( (unsigned long)Memory > (ULONG_MAX >> 20) )
        Memory = (int)(ULONG_MAX >> 20);
    Ret = Llb_Nonlin4ProofWithStop(pWork, &Pars, Pdr2_BddStop, &Stop, (unsigned long)Memory << 20);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Partitioned BDD reachability: %d frames, %s, memory limit %d MiB. Time = %.3f sec.\n",
            Pars.iFrame, Ret == 1 ? "proved" : "no proof", Memory, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Aig_ManStop(pWork);
    if ( pAbstract ) Aig_ManStop(pAbstract);
    ABC_FREE(pInitAbstract);
    return Ret == 1 ? 1 : -1;
}
#else

/**Function*************************************************************

  Synopsis    [Checks safety by repeated squaring of the BDD transition relation.]

  Description []

***********************************************************************/
static int Pdr2_ManBddSquare( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars, abctime timeGlobal ) { return -1; }

/**Function*************************************************************

  Synopsis    [Checks safety with bounded partitioned BDD image computation.]

  Description []

***********************************************************************/
static int Pdr2_ManPartBdd( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars, abctime timeGlobal ) { return -1; }
#endif

/**Function*************************************************************

  Synopsis    [Copies a sequential cone and records its original input and register indices.]

  Description []

***********************************************************************/
// Project the sequential cone while preserving CI/register order. The maps
// name each retained input/register in the source manager. No SAT reasoning
// or initial-state assumption is involved in this structural reduction.
Aig_Man_t * Pdr2_ManDupCoi( Aig_Man_t * pAig, Vec_Int_t ** pvPis, Vec_Int_t ** pvRegs )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    Vec_Ptr_t * vWork = Vec_PtrAlloc( 100 );
    int i, nPis = Saig_ManPiNum(pAig);
    assert( Saig_ManPoNum(pAig) == 1 );
    Aig_ManSetCioIds( pAig );
    Aig_ManIncrementTravId( pAig );
    Vec_PtrPush( vWork, Aig_ManCo(pAig, 0) );
    while ( Vec_PtrSize(vWork) )
    {
        pObj = (Aig_Obj_t *)Vec_PtrPop( vWork );
        if ( Aig_ObjIsTravIdCurrent(pAig, pObj) ) continue;
        Aig_ObjSetTravIdCurrent( pAig, pObj );
        if ( Aig_ObjIsNode(pObj) )
        {
            Vec_PtrPush( vWork, Aig_ObjFanin0(pObj) );
            Vec_PtrPush( vWork, Aig_ObjFanin1(pObj) );
        }
        else if ( Aig_ObjIsCo(pObj) || Aig_ObjIsBuf(pObj) )
            Vec_PtrPush( vWork, Aig_ObjFanin0(pObj) );
        else if ( Saig_ObjIsLo(pAig, pObj) )
            Vec_PtrPush( vWork, Saig_ObjLoToLi(pAig, pObj) );
    }
    Vec_PtrFree( vWork );
    pNew = Aig_ManStart( Aig_ManNodeNum(pAig) );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    *pvPis = Vec_IntAlloc( 100 );
    *pvRegs = Vec_IntAlloc( 100 );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( pAig, pObj, i )
        if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        {
            pObj->pData = Aig_ObjCreateCi( pNew );
            Vec_IntPush( i < nPis ? *pvPis : *pvRegs, i < nPis ? i : i-nPis );
        }
    Aig_ManForEachNode( pAig, pObj, i )
        if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Aig_ManForEachCo( pAig, pObj, i )
        if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
            Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManSetRegNum( pNew, Vec_IntSize(*pvRegs) );
    Aig_ManSetCioIds( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Collects the leaves of a conjunction or disjunction.]

  Description []

***********************************************************************/
// Flatten a conjunction (fOr=0) or disjunction (fOr=1) without distributing
// any other gates. Keeping literal polarities makes the decomposition exact.
int Pdr2_ManLogicLeaves( Aig_Man_t * pAig, Aig_Obj_t * pRoot, int fOr, int Limit, Vec_Ptr_t * vLeaves )
{
    Vec_Ptr_t * vWork = Vec_PtrAlloc( 100 );
    char * pSeen = ABC_CALLOC( char, 2*Aig_ManObjNumMax(pAig) );
    Aig_Obj_t * pLit, * pObj;
    int Complete = 1, Key;
    Vec_PtrClear( vLeaves );
    Vec_PtrPush( vWork, pRoot );
    while ( Vec_PtrSize(vWork) )
    {
        pLit = (Aig_Obj_t *)Vec_PtrPop( vWork );
        pObj = Aig_Regular( pLit );
        Key = Abc_Var2Lit( Aig_ObjId(pObj), Aig_IsComplement(pLit) );
        if ( pSeen[Key] ) continue;
        pSeen[Key] = 1;
        if ( Aig_ObjIsAnd(pObj) && Aig_IsComplement(pLit) == fOr )
        {
            Vec_PtrPush( vWork, Aig_NotCond(Aig_ObjChild1(pObj), fOr) );
            Vec_PtrPush( vWork, Aig_NotCond(Aig_ObjChild0(pObj), fOr) );
        }
        else
        {
            Vec_PtrPush( vLeaves, pLit );
            if ( Vec_PtrSize(vLeaves) > Limit ) { Complete = 0; break; }
        }
    }
    Vec_PtrFree( vWork );
    ABC_FREE( pSeen );
    return Complete;
}

/**Function*************************************************************

  Synopsis    [Finds a state literal required on every prefix of a bad trace.]

  Description [If bad implies g and g' implies g, then g holds throughout
  every bad trace. To assume g' on the final cycle as well, require that
  bad implies g'. Check these implications by exact conjunction containment.]

  SideEffects []

***********************************************************************/
int Pdr2_ManFindGuard( Aig_Man_t * pAig, int fNext )
{
    Vec_Ptr_t * vBad = Vec_PtrAlloc(32), * vNext = Vec_PtrAlloc(32);
    Aig_Obj_t * pLit, * pLeaf, * pNext;
    unsigned char * pBadLeaves = NULL;
    int Limit = Gip_OptionGet("PDR2_GUARD_TERMS") ?
        Abc_MaxInt(1, Abc_MinInt(1000000, atoi(Gip_OptionGet("PDR2_GUARD_TERMS")))) : 2048;
    int i, j, Trials = 0, Result = -1;
    Aig_ManSetCioIds(pAig);
    if ( !Pdr2_ManLogicLeaves(pAig, Aig_ObjChild0(Aig_ManCo(pAig, 0)), 0, Limit, vBad) ) goto done;
    if ( fNext )
    {
        pBadLeaves = ABC_CALLOC( unsigned char, Aig_ManObjNumMax(pAig) );
        Vec_PtrForEachEntry( Aig_Obj_t *, vBad, pLit, i )
            pBadLeaves[Aig_ObjId(Aig_Regular(pLit))] |= 1 << Aig_IsComplement(pLit);
    }
    Vec_PtrForEachEntry(Aig_Obj_t *, vBad, pLit, i)
    {
        Aig_Obj_t * pLo = Aig_Regular(pLit);
        if ( !Saig_ObjIsLo(pAig, pLo) ) continue;
        if ( ++Trials > 32 ) break;
        pNext = Aig_NotCond(Aig_ObjChild0(Saig_ObjLoToLi(pAig, pLo)), Aig_IsComplement(pLit));
        if ( !Pdr2_ManLogicLeaves(pAig, pNext, 0, Limit, vNext) || Vec_PtrFind(vNext, pLit) < 0 ) continue;
        if ( fNext )
        {
            Vec_PtrForEachEntry(Aig_Obj_t *, vNext, pLeaf, j)
                if ( !(pBadLeaves[Aig_ObjId(Aig_Regular(pLeaf))] & (1 << Aig_IsComplement(pLeaf))) ) break;
            if ( j < Vec_PtrSize(vNext) ) continue;
        }
        Result = Abc_Var2Lit(Aig_ObjCioId(pLo) - Saig_ManPiNum(pAig), Aig_IsComplement(pLit));
        break;
    }
done:
    ABC_FREE(pBadLeaves);
    Vec_PtrFree(vBad);
    Vec_PtrFree(vNext);
    return Result;
}


// bad = common AND (a OR b OR ...). Each child checks one exact disjunct
// after sequential cone reduction. A child counterexample is a counterexample
// to the original property; a proof requires every disjunct to be proved.
typedef struct Pdr2_PartRank_t_
{
    int Id, nPis, nRegs, nNodes, Count;
} Pdr2_PartRank_t;

/**Function*************************************************************

  Synopsis    [Compares property partitions using their structural ranking.]

  Description []

***********************************************************************/
static int Pdr2_PartRankCompare( const void * pA, const void * pB )
{
    const Pdr2_PartRank_t * a = (const Pdr2_PartRank_t *)pA, * b = (const Pdr2_PartRank_t *)pB;
    if ( a->Count != b->Count ) return a->Count < b->Count ? -1 : 1;
    if ( a->nNodes != b->nNodes ) return a->nNodes > b->nNodes ? -1 : 1;
    return (a->Id > b->Id) - (a->Id < b->Id);
}

/**Function*************************************************************

  Synopsis    [Simplifies logic guarded by an absorbing validity flag.]

  Description []

***********************************************************************/
// A bad-state conjunct may be an absorbing validity flag. Every trace that
// reaches bad keeps that flag active at all preceding steps. Cofactor all
// active-path logic, but retain explicit sticky flags and their bad guards.
// Thus the transformed and original machines have exactly the same bad
// traces, even though their transitions may differ after a flag is disabled.
static Aig_Man_t * Pdr2_ManStickyCofactor( Aig_Man_t * pAig, Pdr2_Par_t * pPars, abctime Deadline )
{
    int Mode = Gip_OptionGet("PDR2_STICKY") ? atoi(Gip_OptionGet("PDR2_STICKY")) : 0;
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig), i, k, Reg, Inactive, nFound = 0;
    char * pFlags, * pValues;
    Vec_Ptr_t * vLeaves, * vLos;
    Aig_Obj_t * pObj, * pLit, * pBad, * pNext;
    Aig_Man_t * pNew = NULL;
    abctime Start = Abc_Clock(), Stop = Start + 2*CLOCKS_PER_SEC;
    if ( !Mode || !nRegs || pPars->fDumpInv || pPars->fVerifyComplete ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) || Aig_ManNodeNum(pAig) > 2000000 ) return NULL;
    if ( Deadline && Deadline < Stop ) Stop = Deadline;
    vLeaves = Vec_PtrAlloc(100);
    if ( !Pdr2_ManLogicLeaves(pAig, Aig_ObjChild0(Aig_ManCo(pAig, 0)), 0, 256, vLeaves) )
    { Vec_PtrFree(vLeaves); return NULL; }
    Aig_ManSetCioIds(pAig);
    pFlags = ABC_CALLOC(char, nRegs);
    pValues = ABC_ALLOC(char, Aig_ManObjNumMax(pAig));
    memset(pValues, 2, Aig_ManObjNumMax(pAig));
    pValues[Aig_ObjId(Aig_ManConst1(pAig))] = 1;
    Vec_PtrForEachEntry(Aig_Obj_t *, vLeaves, pLit, k)
    {
        pObj = Aig_Regular(pLit);
        if ( !Aig_ObjIsCi(pObj) || Aig_ObjCioId(pObj) < nPis ) continue;
        if ( nFound == 16 || Abc_Clock() >= Stop ||
             (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) break;
        Reg = Aig_ObjCioId(pObj)-nPis;
        if ( pFlags[Reg] ) continue;
        Inactive = Aig_IsComplement(pLit);
        pValues[Aig_ObjId(pObj)] = Inactive;
        Aig_ManForEachNode(pAig, pObj, i)
        {
            int a = pValues[Aig_ObjFaninId0(pObj)], b = pValues[Aig_ObjFaninId1(pObj)];
            if ( a < 2 ) a ^= Aig_ObjFaninC0(pObj);
            if ( b < 2 ) b ^= Aig_ObjFaninC1(pObj);
            pValues[Aig_ObjId(pObj)] = a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
        }
        pObj = Saig_ManLi(pAig, Reg);
        i = pValues[Aig_ObjFaninId0(pObj)];
        if ( i < 2 && (i ^ Aig_ObjFaninC0(pObj)) == Inactive )
            pFlags[Reg] = 2-Inactive, nFound++;
        pValues[Aig_ObjId(Saig_ManLo(pAig, Reg))] = 2;
    }
    if ( !nFound ) goto finish;
    pNew = Aig_ManStart(Aig_ManNodeNum(pAig));
    pNew->pName = Abc_UtilStrsav(pAig->pName);
    vLos = Vec_PtrAlloc(nRegs);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi(pAig, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);
    Saig_ManForEachLo(pAig, pObj, i)
    {
        Aig_Obj_t * pCi = Aig_ObjCreateCi(pNew);
        Vec_PtrPush(vLos, pCi);
        pObj->pData = pFlags[i] ? Aig_NotCond(Aig_ManConst1(pNew), pFlags[i] == 1) : pCi;
    }
    Aig_ManForEachNode(pAig, pObj, i)
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    pBad = Aig_ObjChild0Copy(Aig_ManCo(pAig, 0));
    for ( i = 0; i < nRegs; i++ ) if ( pFlags[i] )
        pBad = Aig_And(pNew, pBad, Aig_NotCond((Aig_Obj_t *)Vec_PtrEntry(vLos, i), pFlags[i] == 1));
    Aig_ObjCreateCo(pNew, pBad);
    Saig_ManForEachLi(pAig, pObj, i)
    {
        pNext = Aig_ObjChild0Copy(pObj);
        if ( pFlags[i] )
            pNext = pFlags[i] == 1 ? Aig_Or(pNew, (Aig_Obj_t *)Vec_PtrEntry(vLos, i), pNext) :
                                    Aig_And(pNew, (Aig_Obj_t *)Vec_PtrEntry(vLos, i), pNext);
        Aig_ObjCreateCo(pNew, pNext);
    }
    Aig_ManSetRegNum(pNew, nRegs);
    Aig_ManCleanup(pNew);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Sticky validity cofactoring: %d absorbing guards, nodes %d -> %d. Time = %.3f sec.\n",
            nFound, Aig_ManNodeNum(pAig), Aig_ManNodeNum(pNew), (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Vec_PtrFree(vLos);
    if ( Mode == 1 && 100*(ABC_INT64_T)Aig_ManNodeNum(pNew) > 98*(ABC_INT64_T)Aig_ManNodeNum(pAig) )
        Aig_ManStop(pNew), pNew = NULL;
finish:
    ABC_FREE(pFlags); ABC_FREE(pValues); Vec_PtrFree(vLeaves);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Orders property partitions using their cone sizes and structural signatures.]

  Description []

***********************************************************************/
// Prioritize structural outliers. Repeated data lanes often have identical
// cone sizes; a distinctive lane is a useful bug-finding candidate. This is
// only a search order: no proof is inferred from matching signatures.
static void Pdr2_ManRankParts( Aig_Man_t * pAig, Vec_Ptr_t * vAnd, int Best, Vec_Ptr_t * vChoice, int fVerbose )
{
    int nParts = Vec_PtrSize(vChoice), i, j;
    Pdr2_PartRank_t * pRanks = ABC_CALLOC( Pdr2_PartRank_t, nParts );
    Vec_Ptr_t * vWork = Vec_PtrAlloc( 100 ), * vOld = Vec_PtrDup( vChoice );
    Aig_Obj_t * pObj, * pLit;
    Aig_ManSetCioIds( pAig );
    for ( i = 0; i < nParts; i++ )
    {
        pRanks[i].Id = i;
        Aig_ManIncrementTravId( pAig );
        Vec_PtrForEachEntry( Aig_Obj_t *, vAnd, pLit, j )
            Vec_PtrPush( vWork, Aig_Regular(j == Best ? (Aig_Obj_t *)Vec_PtrEntry(vChoice, i) : pLit) );
        while ( Vec_PtrSize(vWork) )
        {
            pObj = (Aig_Obj_t *)Vec_PtrPop( vWork );
            if ( Aig_ObjIsTravIdCurrent(pAig, pObj) ) continue;
            Aig_ObjSetTravIdCurrent( pAig, pObj );
            if ( Aig_ObjIsNode(pObj) )
            {
                pRanks[i].nNodes++;
                Vec_PtrPush( vWork, Aig_ObjFanin0(pObj) );
                Vec_PtrPush( vWork, Aig_ObjFanin1(pObj) );
            }
            else if ( Aig_ObjIsCo(pObj) )
                Vec_PtrPush( vWork, Aig_ObjFanin0(pObj) );
            else if ( Saig_ObjIsLo(pAig, pObj) )
            {
                pRanks[i].nRegs++;
                Vec_PtrPush( vWork, Saig_ObjLoToLi(pAig, pObj) );
            }
            else if ( Saig_ObjIsPi(pAig, pObj) ) pRanks[i].nPis++;
        }
    }
    for ( i = 0; i < nParts; i++ )
        for ( j = 0; j < nParts; j++ )
            pRanks[i].Count += pRanks[i].nNodes == pRanks[j].nNodes &&
                              pRanks[i].nRegs == pRanks[j].nRegs && pRanks[i].nPis == pRanks[j].nPis;
    qsort( pRanks, nParts, sizeof(Pdr2_PartRank_t), Pdr2_PartRankCompare );
    for ( i = 0; i < nParts; i++ )
        Vec_PtrWriteEntry( vChoice, i, Vec_PtrEntry(vOld, pRanks[i].Id) );
    if ( fVerbose )
        Abc_Print( 1, "Property part ordering: first part %d, signature shared by %d/%d parts, %d inputs, %d flops, %d nodes.\n",
            pRanks[0].Id+1, pRanks[0].Count, nParts, pRanks[0].nPis, pRanks[0].nRegs, pRanks[0].nNodes );
    Vec_PtrFree( vOld );
    Vec_PtrFree( vWork );
    ABC_FREE( pRanks );
}

/**Function*************************************************************

  Synopsis    [Checks the supplied input and latch permutation on two sequential machines.]

  Description []

***********************************************************************/
// Verify an isomorphism of the complete sequential machine. In addition to
// the bad output, every next-state function must match under the same latch
// permutation. Equal cone sizes or a canonical signature alone prove nothing.
// The caller restricts reuse to all-zero initial states.
static int Pdr2_ManCheckPartMap( Aig_Man_t * pOld, Aig_Man_t * pNew, Vec_Int_t * vMap )
{
    Aig_Obj_t * pObj;
    int i, k, nPis = Saig_ManPiNum(pOld), Result = 0;
    char * pSeen = ABC_CALLOC( char, Aig_ManCiNum(pOld) );
    Aig_ManConst1(pNew)->pData = Aig_ManConst1(pOld);
    Aig_ManForEachCi( pNew, pObj, i )
    {
        k = vMap ? Vec_IntEntry(vMap, i) : i;
        if ( k < 0 || k >= Aig_ManCiNum(pOld) || pSeen[k] || (i < nPis) != (k < nPis) ) goto done;
        pSeen[k] = 1;
        pObj->pData = Aig_ManCi( pOld, k );
    }
    Aig_ManForEachNode( pNew, pObj, i )
    {
        pObj->pData = Aig_TableLookupTwo( pOld, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        if ( !pObj->pData ) goto done;
    }
    if ( Aig_ObjChild0Copy(Aig_ManCo(pNew, 0)) != Aig_ObjChild0(Aig_ManCo(pOld, 0)) ) goto done;
    Saig_ManForEachLi( pNew, pObj, i )
    {
        k = vMap ? Vec_IntEntry(vMap, nPis+i)-nPis : i;
        if ( Aig_ObjChild0Copy(pObj) != Aig_ObjChild0(Saig_ManLi(pOld, k)) ) goto done;
    }
    Result = 1;
done:
    ABC_FREE( pSeen );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tests whether two projected property machines are sequentially isomorphic.]

  Description []

***********************************************************************/
static int Pdr2_ManPartIso( Aig_Man_t * pOld, Aig_Man_t * pNew,
                          Vec_Int_t ** pvOldPerm, Vec_Int_t ** pvNewPerm )
{
    Vec_Int_t * vMap;
    int i, Entry, Result;
    if ( Aig_ManCiNum(pOld) != Aig_ManCiNum(pNew) ||
         Aig_ManRegNum(pOld) != Aig_ManRegNum(pNew) ||
         Aig_ManNodeNum(pOld) != Aig_ManNodeNum(pNew) ) return 0;
    if ( Pdr2_ManCheckPartMap(pOld, pNew, NULL) ) return 1;
    if ( !*pvOldPerm ) *pvOldPerm = Saig_ManFindIsoPerm( pOld, 0 );
    if ( !*pvNewPerm ) *pvNewPerm = Saig_ManFindIsoPerm( pNew, 0 );
    if ( Vec_IntSize(*pvOldPerm) != Aig_ManCiNum(pOld) ||
         Vec_IntSize(*pvNewPerm) != Aig_ManCiNum(pNew) ) return 0;
    vMap = Vec_IntStartFull( Aig_ManCiNum(pNew) );
    Vec_IntForEachEntry( *pvNewPerm, Entry, i )
    {
        if ( Entry < 0 || Entry >= Vec_IntSize(vMap) || Vec_IntEntry(vMap, Entry) >= 0 )
        { Vec_IntFree(vMap); return 0; }
        Vec_IntWriteEntry( vMap, Entry, Vec_IntEntry(*pvOldPerm, i) );
    }
    Result = Pdr2_ManCheckPartMap( pOld, pNew, vMap );
    Vec_IntFree( vMap );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Constructs the property for a selected group of disjuncts.]

  Description []

***********************************************************************/
static Aig_Man_t * Pdr2_ManBuildPart( Aig_Man_t * pAig, Vec_Ptr_t * vAnd, int Best,
                                    Vec_Ptr_t * vChoice, int First, int Count )
{
    Aig_Man_t * pPart = Aig_ManDupSimple( pAig );
    Aig_Obj_t * pBad = Aig_ManConst1(pPart), * pLit, * pTerm;
    int j, k;
    Vec_PtrForEachEntry( Aig_Obj_t *, vAnd, pLit, j )
    {
        if ( j == Best )
        {
            pTerm = Aig_ManConst0( pPart );
            for ( k = 0; k < Count; k++ )
            {
                pLit = (Aig_Obj_t *)Vec_PtrEntry(vChoice, First+k);
                pTerm = Aig_Or( pPart, pTerm, Aig_NotCond((Aig_Obj_t *)Aig_Regular(pLit)->pData, Aig_IsComplement(pLit)) );
            }
        }
        else pTerm = Aig_NotCond((Aig_Obj_t *)Aig_Regular(pLit)->pData, Aig_IsComplement(pLit));
        pBad = Aig_And( pPart, pBad, pTerm );
    }
    Aig_ObjPatchFanin0( pPart, Aig_ManCo(pPart, 0), pBad );
    return pPart;
}

/**Function*************************************************************

  Synopsis    [Keeps one representative of each verified class of isomorphic property machines.]

  Description []

***********************************************************************/
// Isomorphic projected machines have the same safety answer, even before
// either is solved. Keep one representative of each verified class, and
// solve their disjunction together. This is a reachability-preserving
// property reduction, not pointwise Boolean equivalence. Any retained-part
// counterexample still directly satisfies the original property.
static Aig_Man_t * Pdr2_ManReduceParts( Aig_Man_t * pAig, Vec_Ptr_t * vAnd, int Best,
                                     Vec_Ptr_t * vChoice, int Width, Pdr2_Par_t * pPars, abctime Deadline )
{
    Vec_Ptr_t * vClasses = Vec_PtrAlloc( 16 ), * vPerms = Vec_PtrAlloc( 16 );
    Vec_Int_t * vKeep = Vec_IntAlloc( 100 );
    Aig_Man_t * pResult = NULL;
    Aig_Obj_t * pLit, * pBad, * pTerm;
    abctime Start = Abc_Clock();
    int i, j, k, nRemoved = 0, nParts = Vec_PtrSize(vChoice);
    for ( i = 0; i < nParts; i += Width )
    {
        Aig_Man_t * pPart, * pIso;
        Vec_Int_t * vPis, * vRegs, * vPerm = NULL;
        int Count = Abc_MinInt(Width, nParts-i), Found = 0;
        if ( Abc_Clock() >= Deadline || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
        {
            // An interrupted comparison only leaves more representatives.
            for ( ; i < nParts; i += Width ) Vec_IntPush( vKeep, i );
            break;
        }
        pPart = Pdr2_ManBuildPart( pAig, vAnd, Best, vChoice, i, Count );
        pIso = Pdr2_ManDupCoi( pPart, &vPis, &vRegs );
        Aig_ManStop( pPart );
        Vec_IntFree( vPis ); Vec_IntFree( vRegs );
        if ( Aig_ManNodeNum(pIso) <= 5000 && Aig_ManRegNum(pIso) <= 512 && Aig_ManCiNum(pIso) <= 4096 )
        {
            for ( k = 0; k < Vec_PtrSize(vClasses); k++ )
            {
                Vec_Int_t * vOld = (Vec_Int_t *)Vec_PtrEntry(vPerms, k);
                Found = Pdr2_ManPartIso( (Aig_Man_t *)Vec_PtrEntry(vClasses, k), pIso, &vOld, &vPerm );
                Vec_PtrWriteEntry( vPerms, k, vOld );
                if ( Found ) break;
            }
            if ( !Found && Vec_PtrSize(vClasses) < 64 )
            {
                Vec_PtrPush( vClasses, pIso ); pIso = NULL;
                Vec_PtrPush( vPerms, vPerm ); vPerm = NULL;
            }
        }
        if ( Found ) nRemoved++;
        else Vec_IntPush( vKeep, i );
        if ( pIso ) Aig_ManStop( pIso );
        Vec_IntFreeP( &vPerm );
    }
    if ( nRemoved )
    {
        pResult = Aig_ManDupSimple( pAig );
        pBad = Aig_ManConst1( pResult );
        Vec_PtrForEachEntry( Aig_Obj_t *, vAnd, pLit, j )
        {
            if ( j == Best )
            {
                pTerm = Aig_ManConst0( pResult );
                Vec_IntForEachEntry( vKeep, i, k )
                {
                    int t, Count = Abc_MinInt(Width, nParts-i);
                    for ( t = 0; t < Count; t++ )
                    {
                        pLit = (Aig_Obj_t *)Vec_PtrEntry(vChoice, i+t);
                        pTerm = Aig_Or( pResult, pTerm, Aig_NotCond((Aig_Obj_t *)Aig_Regular(pLit)->pData, Aig_IsComplement(pLit)) );
                    }
                }
            }
            else pTerm = Aig_NotCond((Aig_Obj_t *)Aig_Regular(pLit)->pData, Aig_IsComplement(pLit));
            pBad = Aig_And( pResult, pBad, pTerm );
        }
        Aig_ObjPatchFanin0( pResult, Aig_ManCo(pResult, 0), pBad );
    }
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Property isomorphism reduction: %d groups kept, %d removed by complete sequential mappings. Time = %.3f sec.\n",
            Vec_IntSize(vKeep), nRemoved, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC );
    for ( i = 0; i < Vec_PtrSize(vClasses); i++ ) Aig_ManStop( (Aig_Man_t *)Vec_PtrEntry(vClasses, i) );
    for ( i = 0; i < Vec_PtrSize(vPerms); i++ )
        if ( Vec_PtrEntry(vPerms, i) ) Vec_IntFree( (Vec_Int_t *)Vec_PtrEntry(vPerms, i) );
    Vec_PtrFree( vClasses ); Vec_PtrFree( vPerms ); Vec_IntFree( vKeep );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Checks property disjuncts and transfers their results to the original machine.]

  Description []

***********************************************************************/
static int Pdr2_ManSplitProperty( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                                 abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Seconds = Gip_OptionGet("PDR2_SPLIT") ? atoi(Gip_OptionGet("PDR2_SPLIT")) : 0;
    int MaxParts = Gip_OptionGet("PDR2_SPLIT_MAX") ? Abc_MaxInt(1, Abc_MinInt(1024, atoi(Gip_OptionGet("PDR2_SPLIT_MAX")))) : 2;
    int Width = Gip_OptionGet("PDR2_SPLIT_WIDTH") ? Abc_MaxInt(1, Abc_MinInt(1024, atoi(Gip_OptionGet("PDR2_SPLIT_WIDTH")))) : 1;
    int Slice = Gip_OptionGet("PDR2_SPLIT_SLICE") ? Abc_MaxInt(1, atoi(Gip_OptionGet("PDR2_SPLIT_SLICE"))) : 0;
    Vec_Ptr_t * vAnd, * vOr, * vChoice = NULL;
    Vec_Ptr_t * vProved = Vec_PtrAlloc( 16 ), * vPerms = Vec_PtrAlloc( 16 );
    Vec_Int_t * vInit;
    Vec_Wec_t * vCandidates = NULL;
    Aig_Obj_t * pLit, * pBad;
    abctime Start, Deadline;
    int i, j, Best = -1, Result = -1, nProved = 0, nTried = 0, nReuse = 0;
    int IsoSeconds = Gip_OptionGet("PDR2_ISOREDUCE") ? atoi(Gip_OptionGet("PDR2_ISOREDUCE")) : 0;
    int fIso = IsoSeconds > 0 || (Gip_OptionGet("PDR2_SPLIT_ISO") && atoi(Gip_OptionGet("PDR2_SPLIT_ISO")));
    *ppCex = NULL;
    if ( Seconds <= 0 || pPars->fPartRun || pPars->nPropLimit || pPars->nFrameMax ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) )
    { Vec_PtrFree(vProved); Vec_PtrFree(vPerms); return -1; }
    Start = Abc_Clock();
    if ( Gip_OptionGet("PDR2_PART_SHARE") && atoi(Gip_OptionGet("PDR2_PART_SHARE")) > 0 )
        vCandidates = Vec_WecAlloc(100);
    Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && timeGlobal < Deadline ) Deadline = timeGlobal;
    vAnd = Vec_PtrAlloc( 100 );
    vOr = Vec_PtrAlloc( 100 );
    vInit = Vec_IntAlloc( Aig_ManRegNum(pAig) );
    for ( i = 0; i < Aig_ManRegNum(pAig); i++ )
    {
        Vec_IntPush( vInit, pInit[i] );
        if ( pInit[i] != 0 ) fIso = 0;
    }
    if ( !Pdr2_ManLogicLeaves(pAig, Aig_ObjChild0(Aig_ManCo(pAig, 0)), 0, 256, vAnd) ) goto done;
    Vec_PtrForEachEntry( Aig_Obj_t *, vAnd, pLit, i )
        if ( Aig_IsComplement(pLit) && Aig_ObjIsAnd(Aig_Regular(pLit)) &&
             Pdr2_ManLogicLeaves(pAig, pLit, 1, 1024, vOr) && Vec_PtrSize(vOr) > 1 &&
             (!vChoice || Vec_PtrSize(vOr) > Vec_PtrSize(vChoice)) )
        {
            Vec_PtrFreeP( &vChoice );
            vChoice = Vec_PtrDup( vOr );
            Best = i;
        }
    if ( !vChoice ) goto done;
    if ( IsoSeconds > 0 && fIso )
    {
        abctime IsoDeadline = Abc_Clock() + (abctime)IsoSeconds * CLOCKS_PER_SEC;
        Aig_Man_t * pReduced = Pdr2_ManReduceParts( pAig, vAnd, Best, vChoice, Width, pPars,
                                                   IsoDeadline < Deadline ? IsoDeadline : Deadline );
        if ( pReduced )
        {
            Pdr2_Par_t Child = *pPars;
            abctime Remaining = Deadline - Abc_Clock();
            if ( Remaining >= CLOCKS_PER_SEC )
            {
                Child.nTimeOut = (int)(Remaining / CLOCKS_PER_SEC);
                Child.fPartRun = 1;
                Child.fUseAbs = Child.fDynamic = Child.nAbsRuns = Child.nDynTime = 0;
                Child.fPreproc = Child.fDumpInv = Child.nBmcTime = 0;
                if ( Gip_OptionGet("PDR2_PART_ABS") && atoi(Gip_OptionGet("PDR2_PART_ABS")) )
                {
                    Child.fUseAbs = Child.fBlockInduct = Child.fAbsRefineAll = 1;
                }
                Result = Pdr2_ManSolveInit( pReduced, vInit, &Child );
                nTried = 1;
                if ( Result == 1 ) nProved = Vec_PtrSize(vChoice);
                if ( Result == 0 && pReduced->pSeqModel )
                {
                    *ppCex = pReduced->pSeqModel;
                    pReduced->pSeqModel = NULL;
                }
            }
            Aig_ManStop( pReduced );
            goto done;
        }
    }
    if ( Gip_OptionGet("PDR2_SPLIT_ORDER") && atoi(Gip_OptionGet("PDR2_SPLIT_ORDER")) )
        Pdr2_ManRankParts( pAig, vAnd, Best, vChoice, pPars->fVerbose && !pPars->fSilent );
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Property decomposition: %d shared conjuncts, %d disjuncts, trying at most %d in %d sec.\n",
            Vec_PtrSize(vAnd)-1, Vec_PtrSize(vChoice), MaxParts, Seconds );
    for ( i = 0; i < Vec_PtrSize(vChoice) && i < MaxParts; i += Width )
    {
        Aig_Man_t * pPart, * pIso = NULL;
        Vec_Int_t * vPerm = NULL;
        Pdr2_Par_t Child = *pPars;
        abctime Remaining = Deadline - Abc_Clock();
        int Ret = -1, k, fReuse = 0, Count = Abc_MinInt(Width, Vec_PtrSize(vChoice)-i);
        if ( Remaining < CLOCKS_PER_SEC || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) break;
        // Whole seconds round down, leaving the outer deadline authoritative.
        Child.nTimeOut = (int)(Remaining / CLOCKS_PER_SEC);
        if ( Slice && Child.nTimeOut > Slice ) Child.nTimeOut = Slice;
        Child.fPartRun = 1;
        Child.vPartCandidates = vCandidates;
        // Use concrete CTG by default. The optional abstract child uses
        // conservative refinement with all recorded pseudo-inputs.
        Child.fUseAbs = 0;
        Child.fDynamic = 0;
        Child.nAbsRuns = 0;
        Child.nDynTime = 0;
        Child.fPreproc = 0;
        Child.fDumpInv = 0;
        Child.nBmcTime = 0;
        if ( Gip_OptionGet("PDR2_PART_ABS") && atoi(Gip_OptionGet("PDR2_PART_ABS")) )
            Child.fUseAbs = Child.fBlockInduct = Child.fAbsRefineAll = 1;
        pPart = Aig_ManDupSimple( pAig );
        pBad = Aig_ManConst1( pPart );
        Vec_PtrForEachEntry( Aig_Obj_t *, vAnd, pLit, j )
        {
            Aig_Obj_t * pTerm;
            if ( j == Best )
            {
                pTerm = Aig_ManConst0( pPart );
                for ( k = 0; k < Count; k++ )
                {
                    pLit = (Aig_Obj_t *)Vec_PtrEntry(vChoice, i+k);
                    pTerm = Aig_Or( pPart, pTerm, Aig_NotCond((Aig_Obj_t *)Aig_Regular(pLit)->pData, Aig_IsComplement(pLit)) );
                }
            }
            else pTerm = Aig_NotCond((Aig_Obj_t *)Aig_Regular(pLit)->pData, Aig_IsComplement(pLit));
            pBad = Aig_And( pPart, pBad, pTerm );
        }
        Aig_ObjPatchFanin0( pPart, Aig_ManCo(pPart, 0), pBad );
        if ( fIso )
        {
            Vec_Int_t * vPis, * vRegs;
            pIso = Pdr2_ManDupCoi( pPart, &vPis, &vRegs );
            Vec_IntFree( vPis ); Vec_IntFree( vRegs );
            // Bound canonicalization work. Large parts still run normally.
            if ( Aig_ManNodeNum(pIso) <= 5000 && Aig_ManRegNum(pIso) <= 512 && Aig_ManCiNum(pIso) <= 4096 )
                for ( k = 0; k < Vec_PtrSize(vProved); k++ )
                {
                    Vec_Int_t * vOld = (Vec_Int_t *)Vec_PtrEntry(vPerms, k);
                    fReuse = Pdr2_ManPartIso( (Aig_Man_t *)Vec_PtrEntry(vProved, k), pIso, &vOld, &vPerm );
                    Vec_PtrWriteEntry( vPerms, k, vOld );
                    if ( fReuse ) break;
                }
            else { Aig_ManStop(pIso); pIso = NULL; }
        }
        if ( pPars->fVerbose && !pPars->fSilent )
            Abc_Print( 1, "Property parts %d..%d/%d.\n", i+1, i+Count, Vec_PtrSize(vChoice) );
        if ( fReuse ) { Ret = 1; nReuse++; }
        else
        {
            const char * pWindow = Gip_OptionGet("PDR2_PART_WINDOW");
            Ret = -1;
            if ( pWindow && atoi(pWindow) > 0 )
            {
                int Seconds = Abc_MinInt(20, Child.nTimeOut);
                Ret = Pdr2_ManWindowBmc(pPart, vInit, &Child, Seconds, Abc_MinInt(256, atoi(pWindow)));
                Remaining = Deadline - Abc_Clock();
                if ( Remaining >= CLOCKS_PER_SEC ) Child.nTimeOut = Abc_MinInt(Child.nTimeOut, (int)(Remaining / CLOCKS_PER_SEC));
            }
            if ( Ret == -1 && Remaining >= CLOCKS_PER_SEC ) Ret = Pdr2_ManSolveInit(pPart, vInit, &Child);
            nTried++;
        }
        if ( Ret == 0 && pPart->pSeqModel )
        {
            *ppCex = pPart->pSeqModel;
            pPart->pSeqModel = NULL;
            Result = 0;
        }
        if ( Ret == 1 ) nProved += Count;
        if ( Ret == 1 && !fReuse && pIso && Vec_PtrSize(vProved) < 64 )
        {
            Vec_PtrPush( vProved, pIso ); pIso = NULL;
            Vec_PtrPush( vPerms, vPerm ); vPerm = NULL;
        }
        if ( pIso ) Aig_ManStop( pIso );
        Vec_IntFreeP( &vPerm );
        Aig_ManStop( pPart );
        if ( Result == 0 ) break;
    }
    if ( nProved == Vec_PtrSize(vChoice) ) Result = 1;
done:
    if ( pPars->fVerbose && !pPars->fSilent && vChoice )
        Abc_Print( 1, "Property decomposition result: %d tried, %d proved (%d isomorphic proofs reused); %s. Time = %.3f sec.\n",
            nTried, nProved, nReuse, Result == 0 ? "counterexample" : Result == 1 ? "proved" : "undecided", (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC );
    for ( i = 0; i < Vec_PtrSize(vProved); i++ ) Aig_ManStop( (Aig_Man_t *)Vec_PtrEntry(vProved, i) );
    for ( i = 0; i < Vec_PtrSize(vPerms); i++ )
        if ( Vec_PtrEntry(vPerms, i) ) Vec_IntFree( (Vec_Int_t *)Vec_PtrEntry(vPerms, i) );
    Vec_PtrFree( vProved ); Vec_PtrFree( vPerms );
    Vec_PtrFree( vAnd );
    Vec_PtrFree( vOr );
    Vec_PtrFreeP( &vChoice );
    Vec_IntFree( vInit );
    Vec_WecFreeP( &vCandidates );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Solves the safety property of the AIG.]

  Description [Returns 1 if proved, 0 if failed (the counterexample is in
  pAig->pSeqModel), and -1 if undecided. By default three runs alternate
  in doubling propagation budgets: CTG, abstraction with dynamic
  generalization, and abstraction with CTG. Each run resumes its own
  state. A time-limited BMC stage follows the first unfinished slice.
  Invariant sharing is optional and limited to runs 0 and 1. The initial
  value of each flop is given in vInit as 0, 1, or 2 (don't-care); NULL
  means all 0. The counterexample and the invariant refer to the flops of
  the design in their original polarities.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManSolve( Aig_Man_t * pAig, Pdr2_Par_t * pPars )
{
    return Pdr2_ManSolveInit( pAig, NULL, pPars );
}

/**Function*************************************************************

  Synopsis    [Moves a safety property forward while checking its initial time steps.]

  Description []

***********************************************************************/
// If bad is false initially, safety is equivalent to safety of
// bad(T(state,input), fresh_input). Fresh copies of property inputs are
// essential: equating the two time steps would incorrectly restrict traces.
// A shifted counterexample is extended by one original time step below.
static int Pdr2_ManShiftProperty( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                                 abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Seconds = Gip_OptionGet("PDR2_SHIFT") ? atoi(Gip_OptionGet("PDR2_SHIFT")) : 0;
    int MaxDepth = Gip_OptionGet("PDR2_SHIFT_DEPTH") ? Abc_MaxInt(1, Abc_MinInt(4, atoi(Gip_OptionGet("PDR2_SHIFT_DEPTH")))) : 1;
    int nObjs = Aig_ManObjNumMax(pAig), nPis = Saig_ManPiNum(pAig), nRegs = Aig_ManRegNum(pAig);
    int i, a, b, Var, nExtra = 0, Result = -1;
    char * pVals = NULL, * pNeed = NULL;
    Aig_Obj_t ** pFuture = NULL, * pObj, * pRoot;
    Aig_Man_t * pNew = NULL;
    Vec_Ptr_t * vWork = NULL;
    Vec_Int_t * vExtra = NULL, * vInit = NULL;
    Pdr2_Par_t Child = *pPars;
    abctime Start, Deadline, Remaining;
    *ppCex = NULL;
    if ( Seconds <= 0 || pPars->fShiftRun >= MaxDepth || pPars->fPartRun || !nRegs || pPars->nFrameMax || pPars->nPropLimit ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ) return -1;
    Start = Abc_Clock(); Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Deadline > timeGlobal ) Deadline = timeGlobal;
    pVals = ABC_ALLOC( char, nObjs );
    memset( pVals, 2, nObjs );
    pVals[Aig_ObjId(Aig_ManConst1(pAig))] = 1;
    Saig_ManForEachLo( pAig, pObj, i ) pVals[Aig_ObjId(pObj)] = pInit[i];
    Aig_ManForEachNode( pAig, pObj, i )
    {
        a = pVals[Aig_ObjFaninId0(pObj)]; if ( a != 2 ) a ^= Aig_ObjFaninC0(pObj);
        b = pVals[Aig_ObjFaninId1(pObj)]; if ( b != 2 ) b ^= Aig_ObjFaninC1(pObj);
        pVals[Aig_ObjId(pObj)] = a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
    }
    pRoot = Aig_ObjChild0( Aig_ManCo(pAig, 0) );
    a = pVals[Aig_ObjId(Aig_Regular(pRoot))]; if ( a != 2 ) a ^= Aig_IsComplement(pRoot);
    // Unknown is not a proof of initial safety. An optional bounded SAT
    // query can discharge the condition without weakening the initial set.
    if ( a != 0 && Gip_OptionGet("PDR2_SHIFT_INIT") && atoi(Gip_OptionGet("PDR2_SHIFT_INIT")) > 0 )
    {
        Cnf_Man_t * pCnfMan;
        Gip_Ctx_t * pCtx;
        Gip_Solver_t * pSat;
        abctime InitStop = Abc_Clock() + 2*CLOCKS_PER_SEC;
        int Lit, Ret;
        if ( InitStop > Deadline ) InitStop = Deadline;
        pCnfMan = Cnf_ManStart();
        pCtx = Gip_CtxCreatePdr2( pAig, pCnfMan, 1 );
        pSat = Gip_SolverNew( pCtx );
        pSat->TimeLimit = InitStop;
        pSat->nConfLimit = Abc_MaxInt(1, Abc_MinInt(100000, atoi(Gip_OptionGet("PDR2_SHIFT_INIT"))));
        pSat->RunId = pPars->RunId; pSat->pFuncStop = pPars->pFuncStop;
        Saig_ManForEachLo( pAig, pObj, i )
            if ( pInit[i] != 2 )
            {
                Lit = Gip_Lit( Gip_CtxObjVar(pCtx, pObj), !pInit[i] );
                Gip_SolverAddClauseTag( pSat, &Lit, 1, GIP_CLA_LEMMA, (unsigned)GIP_FRAME_INF << 1 );
            }
        Lit = Gip_Lit( Gip_CtxObjVar(pCtx, Aig_ManCo(pAig, 0)), 0 );
        Ret = Gip_SolverSolve( pSat, &Lit, 1, NULL, NULL, 0, -1 );
        if ( pPars->fVerbose && !pPars->fSilent )
            Abc_Print( 1, "Property-shift initial SAT check: %s.\n", Ret == GIP_UNSAT ? "safe" : Ret == GIP_SAT ? "counterexample" : "resource limit" );
        if ( Ret == GIP_UNSAT ) a = 0;
        else if ( Ret == GIP_SAT )
        {
            Abc_Cex_t * d = Abc_CexAlloc( nRegs, nPis, 1 );
            d->iPo = d->iFrame = 0;
            Saig_ManForEachLo( pAig, pObj, i )
                if ( pSat->pValue[Gip_CtxObjVar(pCtx, pObj)] == GIP_TRUE ) Abc_InfoSetBit( d->pData, i );
            Saig_ManForEachPi( pAig, pObj, i )
                if ( pSat->pValue[Gip_CtxObjVar(pCtx, pObj)] == GIP_TRUE ) Abc_InfoSetBit( d->pData, nRegs+i );
            if ( Saig_ManVerifyCex(pAig, d) ) { *ppCex = d; Result = 0; }
            else { Abc_CexFree(d); Abc_Print(1, "Property-shift initial counterexample verification FAILED.\n"); }
        }
        Gip_SolverFree( pSat ); Gip_CtxFree( pCtx ); Cnf_ManStop( pCnfMan );
    }
    if ( a != 0 ) goto done;
    pNeed = ABC_CALLOC( char, nObjs );
    vWork = Vec_PtrAlloc( 100 );
    Vec_PtrPush( vWork, Aig_Regular(pRoot) );
    while ( Vec_PtrSize(vWork) )
    {
        pObj = (Aig_Obj_t *)Vec_PtrPop(vWork);
        if ( pNeed[Aig_ObjId(pObj)] ) continue;
        pNeed[Aig_ObjId(pObj)] = 1;
        if ( Aig_ObjIsNode(pObj) )
        {
            Vec_PtrPush( vWork, Aig_ObjFanin0(pObj) );
            Vec_PtrPush( vWork, Aig_ObjFanin1(pObj) );
        }
    }
    pNew = Aig_ManStart( 2*Aig_ManNodeNum(pAig) );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    pFuture = ABC_CALLOC( Aig_Obj_t *, nObjs );
    Aig_ManConst1(pAig)->pData = pFuture[Aig_ObjId(Aig_ManConst1(pAig))] = Aig_ManConst1(pNew);
    Saig_ManForEachPi( pAig, pObj, i ) pObj->pData = Aig_ObjCreateCi( pNew );
    vExtra = Vec_IntStartFull( nPis );
    Saig_ManForEachPi( pAig, pObj, i )
        if ( pNeed[Aig_ObjId(pObj)] )
        {
            Vec_IntWriteEntry( vExtra, i, nPis+nExtra++ );
            pFuture[Aig_ObjId(pObj)] = Aig_ObjCreateCi( pNew );
        }
    Saig_ManForEachLo( pAig, pObj, i ) pObj->pData = Aig_ObjCreateCi( pNew );
    Aig_ManForEachNode( pAig, pObj, i ) pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Saig_ManForEachLo( pAig, pObj, i ) pFuture[Aig_ObjId(pObj)] = Aig_ObjChild0Copy( Saig_ManLi(pAig, i) );
    Aig_ManForEachNode( pAig, pObj, i )
        if ( pNeed[Aig_ObjId(pObj)] )
            pFuture[Aig_ObjId(pObj)] = Aig_And( pNew,
                Aig_NotCond(pFuture[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj)),
                Aig_NotCond(pFuture[Aig_ObjFaninId1(pObj)], Aig_ObjFaninC1(pObj)) );
    Aig_ObjCreateCo( pNew, Aig_NotCond(pFuture[Aig_ObjId(Aig_Regular(pRoot))], Aig_IsComplement(pRoot)) );
    Saig_ManForEachLi( pAig, pObj, i ) Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ManSetRegNum( pNew, nRegs ); Aig_ManSetCioIds( pNew );
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Property shifted one transition: initial safety established; %d fresh inputs.\n", nExtra );
    Remaining = Deadline - Abc_Clock();
    if ( Remaining < CLOCKS_PER_SEC ) goto done;
    vInit = Vec_IntAlloc( nRegs );
    for ( i = 0; i < nRegs; i++ ) Vec_IntPush( vInit, pInit[i] );
    Child.nTimeOut = (int)(Remaining / CLOCKS_PER_SEC);
    Child.fShiftRun = pPars->fShiftRun + 1;
    Child.fUseAbs = Child.fDynamic = Child.nAbsRuns = Child.nDynTime = 0;
    Child.fPreproc = Child.fDumpInv = Child.nBmcTime = 0;
    Result = Pdr2_ManSolveInit( pNew, vInit, &Child );
    if ( Result == 0 && pNew->pSeqModel )
    {
        Abc_Cex_t * c = pNew->pSeqModel, * d = Abc_CexAlloc( nRegs, nPis, c->iFrame+2 );
        int f;
        assert( c->nRegs == nRegs && c->nPis == nPis+nExtra );
        d->iPo = 0; d->iFrame = c->iFrame+1;
        for ( i = 0; i < nRegs; i++ )
            if ( Abc_InfoHasBit(c->pData, i) ) Abc_InfoSetBit( d->pData, i );
        for ( f = 0; f <= c->iFrame; f++ )
            for ( i = 0; i < nPis; i++ )
                if ( Abc_InfoHasBit(c->pData, nRegs+f*c->nPis+i) ) Abc_InfoSetBit( d->pData, nRegs+f*nPis+i );
        Vec_IntForEachEntry( vExtra, Var, i )
            if ( Var >= 0 && Abc_InfoHasBit(c->pData, nRegs+c->iFrame*c->nPis+Var) )
                Abc_InfoSetBit( d->pData, nRegs+d->iFrame*nPis+i );
        if ( Saig_ManVerifyCex(pAig, d) ) *ppCex = d;
        else
        {
            Abc_Print( 1, "Property-shift counterexample verification FAILED.\n" );
            Abc_CexFree( d ); Result = -1;
        }
    }
done:
    if ( pNew ) Aig_ManStop( pNew );
    ABC_FREE( pVals ); ABC_FREE( pNeed ); ABC_FREE( pFuture );
    Vec_PtrFreeP( &vWork ); Vec_IntFreeP( &vExtra ); Vec_IntFreeP( &vInit );
    return Result;
}

static int Pdr2_ManReverse( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                           abctime timeGlobal, Abc_Cex_t ** ppCex );

/**Function*************************************************************

  Synopsis    [Selects the primary input vector for a substep of a grouped transition.]

***********************************************************************/
static int Pdr2_StrideInputSlot( int k, int Stride, int Pattern )
{
    switch ( Pattern )
    {
    case 1: return 0;
    case 2: return k != 0;
    case 3: return k & 1;
    case 4: return k == 0 ? 0 : k + 1 == Stride && Stride > 2 ? 2 : 1;
    case 5: return k >= Stride / 2;
    default: return k;
    }
}

/**Function*************************************************************

  Synopsis    [Shortens a candidate trace to the first original bad output.]

  Description [The caller has checked the trace interface and length. A
  successful return preserves ABC's exact bit count for the retained prefix.]

***********************************************************************/
int Pdr2_ManFirstBad( Aig_Man_t * pAig, Abc_Cex_t * pCex )
{
    int i, f, Found = 0;
    Aig_Obj_t * pObj;
    char * pValues = ABC_CALLOC(char, Aig_ManObjNumMax(pAig));
    pValues[Aig_ObjId(Aig_ManConst1(pAig))] = 1;
    Saig_ManForEachLo( pAig, pObj, i ) pValues[Aig_ObjId(pObj)] = Abc_InfoHasBit(pCex->pData, i);
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        Saig_ManForEachPi( pAig, pObj, i )
            pValues[Aig_ObjId(pObj)] = Abc_InfoHasBit(pCex->pData, pCex->nRegs + f*pCex->nPis + i);
        Aig_ManForEachNode( pAig, pObj, i )
            pValues[Aig_ObjId(pObj)] = (pValues[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj)) &
                                      (pValues[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj));
        Aig_ManForEachCo( pAig, pObj, i )
            pValues[Aig_ObjId(pObj)] = pValues[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
        if ( pValues[Aig_ObjId(Aig_ManCo(pAig, 0))] )
        {
            pCex->iFrame = f;
            pCex->nBits = pCex->nRegs + (f+1)*pCex->nPis;
            Found = 1;
            break;
        }
        Saig_ManForEachLo( pAig, pObj, i ) pValues[Aig_ObjId(pObj)] = pValues[Aig_ObjId(Saig_ManLi(pAig, i))];
    }
    ABC_FREE(pValues);
    return Found;
}

/**Function*************************************************************

  Synopsis    [Groups consecutive transitions and checks each intermediate bad output.]

  Description []

***********************************************************************/
// Decode the number of original inputs consumed by this grouped frame.
static int Pdr2_StrideCexSteps( Abc_Cex_t * c, int f, int Stride, int Phase )
{
    int k, Count = 1, Select = c->nRegs + (f+1)*c->nPis - (Stride-1);
    if ( !Phase ) return Stride;
    if ( f == c->iFrame ) return 1;
    if ( f && Phase == 1 ) return Stride;
    for ( k = 0; k < Stride-1; k++ )
        if ( Abc_InfoHasBit(c->pData, Select+k) )
            Count = k+2;
    return Count;
}

// A fixed stride observes every intermediate bad output. Alternatively,
// observe block boundaries and allow the first block to take h in [1,K]
// original steps. Every positive depth is h + m*K, and each selected block
// expands to an original trace, even if later blocks also select their length.
static int Pdr2_ManStride( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                          abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Stride = Gip_OptionGet("PDR2_STRIDE") ? Abc_MinInt(16, atoi(Gip_OptionGet("PDR2_STRIDE"))) : 0;
    int Seconds = Gip_OptionGet("PDR2_STRIDE_TIME") ? atoi(Gip_OptionGet("PDR2_STRIDE_TIME")) : 60;
    int nPis = Saig_ManPiNum(pAig), nRegs = Aig_ManRegNum(pAig), i, k, Result = -1;
    int Pattern = Gip_OptionGet("PDR2_STRIDE_PATTERN") ? Abc_MaxInt(0, Abc_MinInt(5, atoi(Gip_OptionGet("PDR2_STRIDE_PATTERN")))) : 0;
    int Phase = !Pattern && Gip_OptionGet("PDR2_STRIDE_PHASE") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_STRIDE_PHASE")))) : 0;
    int nChoice = Phase && Stride > 1 ? Stride - 1 : 0;
    int nSlots = !Pattern ? Stride : Pattern == 1 ? 1 : Pattern == 4 ? Abc_MinInt(Stride, 3) : 2;
    int PartOnly = Gip_OptionGet("PDR2_STRIDE_PART") && atoi(Gip_OptionGet("PDR2_STRIDE_PART"));
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pBad, * pStarted = NULL;
    Vec_Ptr_t * vNext, * vSelected;
    Vec_Int_t * vInit;
    Pdr2_Par_t Child = *pPars;
    abctime Start, Deadline, Remaining;
    *ppCex = NULL;
    if ( Stride < 2 || Seconds <= 0 || pPars->fStrideRun || (PartOnly && !pPars->fPartRun) ||
         !nRegs || pPars->nFrameMax || pPars->nPropLimit ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ||
         (ABC_INT64_T)Stride * (nPis + (ABC_INT64_T)Aig_ManNodeNum(pAig) + 1) + 2 * (ABC_INT64_T)nRegs +
         (ABC_INT64_T)nChoice * (3*(ABC_INT64_T)nRegs+2) + 4 > INT_MAX / 2 ||
         (ABC_INT64_T)Stride * Aig_ManNodeNum(pAig) > 4000000 ) return -1;
    Start = Abc_Clock(); Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Deadline > timeGlobal ) Deadline = timeGlobal;
    pNew = Aig_ManStart( Stride*Aig_ManNodeNum(pAig) );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    vNext = Vec_PtrAlloc( nRegs ); vInit = Vec_IntAlloc( nRegs );
    vSelected = Phase ? Vec_PtrAlloc(nRegs) : NULL;
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    for ( k = 0; k < nSlots; k++ )
        for ( i = 0; i < nPis; i++ ) Aig_ObjCreateCi( pNew );
    for ( i = 0; i < nChoice; i++ )
        Aig_ObjCreateCi( pNew );
    Saig_ManForEachLo( pAig, pObj, i )
    {
        pObj->pData = Aig_ObjCreateCi( pNew );
        Vec_IntPush( vInit, pInit[i] );
    }
    if ( Phase == 1 )
    {
        pStarted = Aig_ObjCreateCi( pNew );
        Vec_IntPush( vInit, 0 );
    }
    pBad = Aig_ManConst0( pNew );
    for ( k = 0; k < Stride; k++ )
    {
        int Slot = Pdr2_StrideInputSlot(k, Stride, Pattern);
        Saig_ManForEachPi( pAig, pObj, i ) pObj->pData = Aig_ManCi(pNew, Slot*nPis+i);
        Aig_ManForEachNode( pAig, pObj, i )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        if ( !Phase || k == 0 )
            pBad = Aig_Or( pNew, pBad, Aig_ObjChild0Copy(Aig_ManCo(pAig, 0)) );
        Vec_PtrClear( vNext );
        Saig_ManForEachLi( pAig, pObj, i ) Vec_PtrPush( vNext, Aig_ObjChild0Copy(pObj) );
        if ( Phase && k == 0 )
            Vec_PtrAppend( vSelected, vNext );
        else if ( Phase )
        {
            Aig_Obj_t * pChoose = Aig_ManCi( pNew, nSlots*nPis+k-1 );
            if ( pStarted ) pChoose = Aig_Or( pNew, pChoose, pStarted );
            Vec_PtrForEachEntry( Aig_Obj_t *, vNext, pObj, i )
                Vec_PtrWriteEntry( vSelected, i, Aig_Mux(pNew, pChoose, pObj, (Aig_Obj_t *)Vec_PtrEntry(vSelected, i)) );
        }
        // Update state simultaneously; a next-state literal may be an old LO.
        Saig_ManForEachLo( pAig, pObj, i ) pObj->pData = Vec_PtrEntry(vNext, i);
    }
    Aig_ObjCreateCo( pNew, pBad );
    Vec_PtrForEachEntry( Aig_Obj_t *, Phase ? vSelected : vNext, pObj, i ) Aig_ObjCreateCo( pNew, pObj );
    if ( pStarted ) Aig_ObjCreateCo( pNew, Aig_ManConst1(pNew) );
    Aig_ManSetRegNum( pNew, Vec_IntSize(vInit) ); Aig_ManSetCioIds( pNew ); Aig_ManCleanup( pNew );
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Transition stride %d: inputs %d -> %d, flops %d, nodes %d -> %d; %s.\n",
            Stride, nPis, Saig_ManPiNum(pNew), nRegs, Aig_ManNodeNum(pAig), Aig_ManNodeNum(pNew),
            Phase == 1 ? "selectable first block length" : Phase == 2 ? "selectable block lengths" : "all intermediate bad states checked" );
    Remaining = Deadline - Abc_Clock();
    if ( Remaining < CLOCKS_PER_SEC ) goto done;
    Child.nTimeOut = (int)(Remaining/CLOCKS_PER_SEC);
    Child.fStrideRun = Child.fPartRun = 1;
    Child.fDynamic = Child.nAbsRuns = Child.nDynTime = 0;
    if ( Child.fUseAbs ) Child.fAbsRefineAll = 1;
    Child.fPreproc = Child.fDumpInv = Child.nBmcTime = 0;
    if ( Pattern && Gip_OptionGet("PDR2_STRIDE_BOUNDED") )
        Result = Pdr2_ManWindowBmc(pNew, vInit, &Child, Child.nTimeOut, 1);
    else if ( Gip_OptionGet("PDR2_STRIDE_REVERSE") && atoi(Gip_OptionGet("PDR2_STRIDE_REVERSE")) )
    {
        // Reverse the grouped relation directly. Its bad predicate still
        // includes every intermediate original step, and both mappings
        // independently replay their reconstructed counterexample.
        Child.fStrideRun = Child.fPartRun = 0;
        char * pReset = ABC_CALLOC( char, Vec_IntSize(vInit) );
        memcpy( pReset, pInit, nRegs );
        Result = Pdr2_ManReverse(pNew,pReset,&Child,Deadline,&pNew->pSeqModel);
        ABC_FREE( pReset );
    }
    else
        Result = Pdr2_ManSolveInit( pNew, vInit, &Child );
    // Repeated primary inputs restrict the possible traces. A failed search
    // can only return undecided to the original safety problem.
    if ( Pattern && (Result != 0 || !pNew->pSeqModel) ) Result = -1;
    if ( Result == 0 && pNew->pSeqModel )
    {
        Abc_Cex_t * c = pNew->pSeqModel, * d;
        int f, Frames, OutFrame = 0;
        assert( c->nRegs == Vec_IntSize(vInit) && c->nPis == nSlots*nPis+nChoice );
        if ( (ABC_INT64_T)Stride * ((ABC_INT64_T)c->iFrame + 1) > (2000000000 - nRegs) / Abc_MaxInt(nPis,1) )
        { Result = -1; goto done; }
        Frames = Stride * (c->iFrame+1);
        d = Abc_CexAlloc( nRegs, nPis, Frames );
        d->iPo = 0; d->iFrame = Frames-1;
        for ( i = 0; i < nRegs; i++ )
            if ( Abc_InfoHasBit(c->pData, i) ) Abc_InfoSetBit(d->pData, i);
        for ( f = 0; f <= c->iFrame; f++ )
        {
            int Count = Pdr2_StrideCexSteps( c, f, Stride, Phase );
            for ( k = 0; k < Count; k++, OutFrame++ )
            {
                int Source = c->nRegs + f*c->nPis + Pdr2_StrideInputSlot(k, Stride, Pattern)*nPis;
                for ( i = 0; i < nPis; i++ )
                    if ( Abc_InfoHasBit(c->pData, Source+i) ) Abc_InfoSetBit(d->pData, nRegs+OutFrame*nPis+i);
            }
        }
        d->iFrame = OutFrame-1;
        d->nBits = nRegs + OutFrame*nPis;
        if ( Pdr2_ManFirstBad(pAig, d) && Saig_ManVerifyCex(pAig, d) ) *ppCex = d;
        else
        {
            Abc_Print( 1, "Transition-stride counterexample verification FAILED.\n" );
            Abc_CexFree( d ); Result = -1;
        }
    }
done:
    Aig_ManStop( pNew ); Vec_PtrFreeP( &vSelected ); Vec_PtrFree( vNext ); Vec_IntFree( vInit );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tests whether the bad output is impossible for arbitrary state and inputs.]

  Description []

***********************************************************************/
static int Pdr2_ManCombSweep( Aig_Man_t ** ppCone, Pdr2_Par_t * pPars, abctime Deadline, int * pCancelled )
{
    Cec_ParCec_t Pars;
    Cec_ParLimit_t Limits;
    Gia_Man_t * pGia = Gia_ManFromAigSimple(*ppCone), * pReduced = NULL, * pMiter;
    int Ret;
    // The second output is the constant specification. A counterexample to
    // this equality is a free state and cannot witness sequential failure.
    Gia_ManAppendCo(pGia, 0);
    Cec_ManCecSetDefaultParams(&Pars);
    Pars.fSilent = 1;
    if ( atoi(Gip_OptionGet("PDR2_CSAFE_CEC")) > 1 )
        Pars.nBTLimit = Abc_MinInt(10000, atoi(Gip_OptionGet("PDR2_CSAFE_CEC")));
    memset(&Limits, 0, sizeof(Limits));
    Limits.TimeToStop = Deadline;
    Limits.RunId = pPars->RunId;
    Limits.pFuncStop = pPars->pFuncStop;
    Limits.pCancelled = pCancelled;
    Ret = Cec_ManVerifyWithLimits(pGia, &Pars, &Limits, &pReduced);
    if ( pReduced && !*pCancelled )
    {
        pMiter = Gia_ManTransformMiter(pReduced);
        Aig_ManStop(*ppCone);
        *ppCone = Gia_ManToAigSimple(pMiter);
        Gia_ManStop(pMiter);
    }
    Gia_ManStopP(&pReduced);
    Gia_ManStop(pGia);
    return Ret;
}

static int Pdr2_ManCombSatStop( void * pData )
{
    return Cec_ManIsStopped( (Cec_ParLimit_t *)pData );
}

/**Function*************************************************************

  Synopsis    [Loads a cut-mapped CNF into the selected SAT solver.]

***********************************************************************/
static int Pdr2_ManLoadMappedCnf( Cnf_Dat_t * pCnf, kissat * pKis, CCaDiCaL * pCad, Cec_ParLimit_t * pLimits )
{
    int i, * pLit;
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( (i & 1023) == 0 && Cec_ManIsStopped(pLimits) ) return 0;
        for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
        {
            int Lit = Abc_Lit2Var(*pLit) + 1;
            if ( Abc_LitIsCompl(*pLit) ) Lit = -Lit;
            if ( pKis ) kissat_add( pKis, Lit );
            else ccadical_add( pCad, Lit );
        }
        if ( pKis ) kissat_add( pKis, 0 );
        else ccadical_add( pCad, 0 );
    }
    return !Cec_ManIsStopped(pLimits);
}

/**Function*************************************************************

  Synopsis    [Checks the asserted bad output using mapped CNF.]

***********************************************************************/
static int Pdr2_ManCombMapped( Aig_Man_t * pCone, Pdr2_Par_t * pPars, abctime Stop, int nConfs, int fKissat, Vec_Int_t * vModel )
{
    Cec_ParLimit_t Limits = { Stop, pPars->RunId, pPars->pFuncStop, NULL };
    Cnf_Man_t * pMan = Cnf_ManStart();
    Cnf_Dat_t * pCnf = Cnf_DeriveWithMan( pMan, pCone, 0 );
    CCaDiCaL * pCad = NULL;
    kissat * pKis = NULL;
    int i, Ret = 0;
    Cnf_DataTranformPolarity( pCnf, 0 );
    if ( fKissat )
    {
        pKis = kissat_init();
        kissat_set_option( pKis, "quiet", 1 );
        kissat_set_terminate( pKis, &Limits, Pdr2_ManCombSatStop );
        kissat_set_conflict_limit( pKis, (unsigned)nConfs );
    }
    else
    {
        pCad = ccadical_init();
        ccadical_set_option( pCad, "quiet", 1 );
        ccadical_set_terminate( pCad, &Limits, Pdr2_ManCombSatStop );
        ccadical_limit( pCad, "conflicts", nConfs );
    }
    if ( Pdr2_ManLoadMappedCnf(pCnf, pKis, pCad, &Limits) )
        Ret = pKis ? kissat_solve(pKis) : ccadical_solve(pCad);
    if ( pPars->fVerbose && !pPars->fSilent )
    {
        if ( pKis ) Abc_Print( 1, "Mapped cone Kissat: budget %d conflicts, result %d.\n", nConfs, Ret );
        else Abc_Print( 1, "Mapped cone SAT: %d conflicts, budget %d, result %d.\n",
            ccadical_conflicts(pCad), nConfs, Ret );
    }
    if ( Ret == 10 && vModel )
    {
        Aig_Obj_t * pObj;
        int MaxVar = pKis ? pCnf->nVars : ccadical_vars(pCad);
        Aig_ManForEachCi( pCone, pObj, i )
        {
            int Var = pCnf->pVarNums[Aig_ObjId(pObj)] + 1;
            int Value = Var > 0 && Var <= MaxVar && (pKis ? kissat_value(pKis, Var) : ccadical_val(pCad, Var)) > 0;
            Vec_IntPush( vModel, Value ^ pObj->fPhase );
        }
    }
    if ( pKis ) kissat_release( pKis );
    else ccadical_release( pCad );
    Cnf_DataFree( pCnf );
    Cnf_ManStop( pMan );
    return Ret == 20 ? GIP_UNSAT : Ret == 10 ? GIP_SAT : GIP_UNDEF;
}

/**Function*************************************************************

  Synopsis    [Copies the bad output and its original CI coordinates.]

***********************************************************************/
static Aig_Man_t * Pdr2_ManCopyBad( Pdr2_Man_t * p, abctime Stop, Aig_Obj_t ** ppBad )
{
    Aig_Man_t * pOrig = p->pAig, * pCone = Aig_ManStart(Aig_ManObjNumMax(pOrig));
    Vec_Ptr_t * vCopy = Vec_PtrStart(Aig_ManObjNumMax(pOrig));
    Aig_Obj_t * pObj, * pLeft, * pRight;
    int i;
    Vec_PtrWriteEntry( vCopy, Aig_ObjId(Aig_ManConst1(pOrig)), Aig_ManConst1(pCone) );
    Aig_ManForEachCi( pOrig, pObj, i )
        Vec_PtrWriteEntry( vCopy, Aig_ObjId(pObj), Aig_ObjCreateCi(pCone) );
    Aig_ManForEachNode( pOrig, pObj, i )
    {
        if ( (i & 4095) == 0 && (Abc_Clock() >= Stop || Pdr2_ManPastDeadline(p)) )
        {
            Aig_ManStop(pCone);
            Vec_PtrFree(vCopy);
            return NULL;
        }
        pLeft = (Aig_Obj_t *)Vec_PtrEntry( vCopy, Aig_ObjId(Aig_ObjFanin0(pObj)) );
        pRight = (Aig_Obj_t *)Vec_PtrEntry( vCopy, Aig_ObjId(Aig_ObjFanin1(pObj)) );
        Vec_PtrWriteEntry( vCopy, Aig_ObjId(pObj),
            Aig_And(pCone, Aig_NotCond(pLeft, Aig_ObjFaninC0(pObj)), Aig_NotCond(pRight, Aig_ObjFaninC1(pObj))) );
    }
    pObj = Aig_ManCo(pOrig, 0);
    *ppBad = Aig_NotCond((Aig_Obj_t *)Vec_PtrEntry(vCopy, Aig_ObjId(Aig_ObjFanin0(pObj))), Aig_ObjFaninC0(pObj));
    Vec_PtrFree(vCopy);
    return pCone;
}

typedef struct Pdr2_BadSat_t_ Pdr2_BadSat_t;
struct Pdr2_BadSat_t_
{
    CCaDiCaL * pSat;
    Vec_Int_t * vCi;  // signed DIMACS variables in original CI order
    int nVars, nQueries;
};

/**Function*************************************************************

  Synopsis    [Releases the mapped property solver and its input map.]

***********************************************************************/
void Pdr2_ManStopBadSat( Pdr2_Man_t * p )
{
    if ( p->pBadSat == NULL ) return;
    ccadical_release(p->pBadSat->pSat);
    Vec_IntFree(p->pBadSat->vCi);
    ABC_FREE(p->pBadSat);
}

/**Function*************************************************************

  Synopsis    [Maps the bad output once and freezes its input variables.]

***********************************************************************/
static int Pdr2_ManStartBadSat( Pdr2_Man_t * p, Cec_ParLimit_t * pLimits )
{
    Aig_Obj_t * pBad, * pObj;
    Aig_Man_t * pCone = Pdr2_ManCopyBad(p, pLimits->TimeToStop, &pBad);
    Pdr2_BadSat_t * pBadSat;
    Cnf_Man_t * pMan;
    Cnf_Dat_t * pCnf;
    int i, Var, Complete = 0;
    if ( pCone == NULL ) return 0;
    Aig_ObjCreateCo(pCone, pBad);
    Aig_ManCleanup(pCone);
    pMan = Cnf_ManStart();
    pCnf = Cnf_DeriveWithMan(pMan, pCone, 0);
    Cnf_DataTranformPolarity(pCnf, 0);
    if ( pCnf->nVars < INT_MAX - Aig_ManCiNum(pCone) && !Cec_ManIsStopped(pLimits) )
    {
        p->pBadSat = pBadSat = ABC_CALLOC(Pdr2_BadSat_t, 1);
        pBadSat->pSat = ccadical_init();
        ccadical_set_option(pBadSat->pSat, "quiet", 1);
        pBadSat->nVars = pCnf->nVars;
        pBadSat->vCi = Vec_IntAlloc(Aig_ManCiNum(pCone));
        Aig_ManForEachCi(pCone, pObj, i)
        {
            Var = pCnf->pVarNums[Aig_ObjId(pObj)];
            Var = Var < 0 ? ++pBadSat->nVars : Var + 1;
            Vec_IntPush(pBadSat->vCi, pObj->fPhase ? -Var : Var);
            ccadical_freeze(pBadSat->pSat, Var);
        }
        Complete = Pdr2_ManLoadMappedCnf(pCnf, NULL, pBadSat->pSat, pLimits);
        if ( !Complete ) Pdr2_ManStopBadSat(p);
    }
    Cnf_DataFree(pCnf);
    Cnf_ManStop(pMan);
    Aig_ManStop(pCone);
    return Complete;
}

/**Function*************************************************************

  Synopsis    [Reuses the property CNF across independent frontier queries.]

  Description [All frame clauses share a fresh selector. Its negative unit
  retires the whole batch even if clause loading is interrupted. Reset
  assumptions are scoped to frame zero. Only the property is permanent.]

***********************************************************************/
static int Pdr2_ManReuseBadSat( Pdr2_Man_t * p, abctime Stop, Vec_Int_t * vModel )
{
    Cec_ParLimit_t Limits = { Stop, p->pPars->RunId, p->pPars->pFuncStop, NULL };
    Pdr2_BadSat_t * pBadSat;
    Pdr2_Lem_t * pLem;
    Vec_Ptr_t * vFrame;
    int i, j, k, Lit, Var, Act, Level = Pdr2_ManLevel(p), Ret = 0;
    if ( !p->pBadSat && !Pdr2_ManStartBadSat(p, &Limits) ) return GIP_UNDEF;
    pBadSat = p->pBadSat;
    if ( pBadSat->nQueries == INT_MAX - pBadSat->nVars ) return GIP_UNDEF;
    Act = pBadSat->nVars + ++pBadSat->nQueries;
    ccadical_freeze(pBadSat->pSat, Act);
    for ( k = 0; k < 2; k++ )
    {
        vFrame = k ? p->vInf : Pdr2_ManFrame(p, Level);
        Vec_PtrForEachEntry(Pdr2_Lem_t *, vFrame, pLem, i)
        {
            if ( (i & 255) == 0 && Cec_ManIsStopped(&Limits) ) goto finish;
            if ( pLem->fRemoved ) continue;
            ccadical_add(pBadSat->pSat, -Act);
            for ( j = 0; j < pLem->pCube->nLits; j++ )
            {
                Lit = pLem->pCube->Lits[j];
                Var = Vec_IntEntry(pBadSat->vCi, p->nPis+Abc_Lit2Var(Lit));
                ccadical_add(pBadSat->pSat, Abc_LitIsCompl(Lit) ? Var : -Var);
            }
            ccadical_add(pBadSat->pSat, 0);
        }
    }
    if ( Cec_ManIsStopped(&Limits) ) goto finish;
    if ( Level == 0 )
        for ( i = 0; i < p->nRegs; i++ )
            if ( p->pInit[i] < 2 )
            {
                Var = Vec_IntEntry(pBadSat->vCi, p->nPis+i);
                ccadical_assume(pBadSat->pSat, p->pInit[i] ? Var : -Var);
            }
    ccadical_assume(pBadSat->pSat, Act);
    ccadical_set_terminate(pBadSat->pSat, &Limits, Pdr2_ManCombSatStop);
    ccadical_limit(pBadSat->pSat, "conflicts", 10000000);
    Ret = ccadical_solve(pBadSat->pSat);
    ccadical_set_terminate(pBadSat->pSat, NULL, NULL);
    if ( Ret == 10 )
        Vec_IntForEachEntry(pBadSat->vCi, Var, i)
            Vec_IntPush(vModel, (ccadical_val(pBadSat->pSat, Abc_AbsInt(Var)) > 0) ^ (Var < 0));
finish:
    ccadical_add(pBadSat->pSat, -Act);
    ccadical_add(pBadSat->pSat, 0);
    ccadical_melt(pBadSat->pSat, Act);
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1, "Mapped bad-state CaDiCaL: query %d, frame %d, result %d.\n", pBadSat->nQueries, Level, Ret);
    return Ret == 20 ? GIP_UNSAT : Ret == 10 ? GIP_SAT : GIP_UNDEF;
}

/**Function*************************************************************

  Synopsis    [Checks the current frontier and bad output using mapped CNF.]

  Description [A model assigns original inputs and flops in CI order.
  Omitting solver-private clauses weakens the query. The caller therefore
  checks a SAT model in the frame solver before using it for lifting.]

***********************************************************************/
int Pdr2_ManMappedBad( Pdr2_Man_t * p, int Seconds, Vec_Int_t * vModel )
{
    Aig_Man_t * pCone;
    Aig_Obj_t * pBad, * pSignal, * pBlocked;
    Vec_Ptr_t * vTerms, * vCube, * vFrame;
    Pdr2_Lem_t * pLem;
    const char * pValue = Gip_OptionGet("PDR2_BAD_REUSE_SECS");
    int Reuse = pValue ? Abc_MinInt(60, atoi(pValue)) : -1;
    int i, j, k, Lit, Level = Pdr2_ManLevel(p), Ret = GIP_UNDEF;
    abctime Start = Abc_Clock(), Stop = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( p->timeLimit && Stop > p->timeLimit ) Stop = p->timeLimit;
    if ( p->timeSliceHard && Stop > p->timeSliceHard ) Stop = p->timeSliceHard;
    if ( Abc_Clock() >= Stop || Pdr2_ManPastDeadline(p) ) return GIP_UNDEF;
    if ( Reuse == 0 || p->fReuseBadSat ) return Pdr2_ManReuseBadSat(p, Stop, vModel);
    pCone = Pdr2_ManCopyBad(p, Stop, &pBad);
    if ( pCone == NULL ) return GIP_UNDEF;
    vTerms = Vec_PtrAlloc(64);
    vCube = Vec_PtrAlloc(32);
    Vec_PtrPush(vTerms, pBad);
    if ( Level == 0 )
        for ( i = 0; i < p->nRegs; i++ )
            if ( p->pInit[i] < 2 )
                Vec_PtrPush( vTerms, Aig_NotCond(Aig_ManCi(pCone, p->nPis+i), !p->pInit[i]) );
    for ( k = 0; k < 2; k++ )
    {
        vFrame = k ? p->vInf : Pdr2_ManFrame(p, Level);
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vFrame, pLem, i )
        {
            if ( (i & 255) == 0 && (Abc_Clock() >= Stop || Pdr2_ManPastDeadline(p)) ) goto finish;
            if ( pLem->fRemoved ) continue;
            Vec_PtrClear( vCube );
            for ( j = 0; j < pLem->pCube->nLits; j++ )
            {
                Lit = pLem->pCube->Lits[j];
                pSignal = Aig_ManCi(pCone, p->nPis + Abc_Lit2Var(Lit));
                Vec_PtrPush( vCube, Aig_NotCond(pSignal, Abc_LitIsCompl(Lit)) );
            }
            pBlocked = Vec_PtrSize(vCube) ? Aig_Multi(pCone, (Aig_Obj_t **)Vec_PtrArray(vCube), Vec_PtrSize(vCube), AIG_OBJ_AND)
                                         : Aig_ManConst1(pCone);
            Vec_PtrPush( vTerms, Aig_Not(pBlocked) );
        }
    }
    pBad = Aig_Multi(pCone, (Aig_Obj_t **)Vec_PtrArray(vTerms), Vec_PtrSize(vTerms), AIG_OBJ_AND);
    if ( pBad == Aig_ManConst0(pCone) )
        Ret = GIP_UNSAT;
    else if ( pBad != Aig_ManConst1(pCone) )
    {
        Aig_ObjCreateCo(pCone, pBad);
        Aig_ManCleanup(pCone);
        if ( Abc_Clock() < Stop && !Pdr2_ManPastDeadline(p) )
            Ret = Pdr2_ManCombMapped(pCone, p->pPars, Stop, 10000000, 1, vModel);
    }
finish:
    Vec_PtrFree(vCube);
    Vec_PtrFree(vTerms);
    Aig_ManStop(pCone);
    if ( Reuse > 0 && Abc_Clock() - Start >= (abctime)Reuse * CLOCKS_PER_SEC )
        p->fReuseBadSat = 1;
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Checks the single failure output of the unrestricted proof miter.]

***********************************************************************/
int Pdr2_ManMappedInvariant( Pdr2_Man_t * p, Aig_Man_t * pMiter )
{
    Vec_Ptr_t * vInputs = Vec_PtrAlloc( 100 );
    Vec_Ptr_t * vOutputs = Vec_PtrAlloc( 1 );
    Aig_Man_t * pFail;
    int Ret;
    // The mapper asserts every output. Extract the failure cone and treat
    // the state as free input so that next-state outputs cannot constrain it.
    Vec_PtrPush( vOutputs, Aig_ManCo(pMiter, 0) );
    Aig_SupportNodes(pMiter, (Aig_Obj_t **)Vec_PtrArray(vOutputs), 1, vInputs);
    pFail = Aig_ManDupSimpleDfsPart(pMiter, vInputs, vOutputs);
    Vec_PtrFree(vOutputs);
    Vec_PtrFree(vInputs);
    assert( Aig_ManCoNum(pFail) == 1 && Aig_ManRegNum(pFail) == 0 );
    Ret = Pdr2_ManCombMapped(pFail, p->pPars, p->timeGlobal, INT_MAX, 1, NULL);
    Aig_ManStop(pFail);
    return Ret == GIP_UNSAT ? 1 : Ret == GIP_SAT ? 0 : -1;
}

/**Function*************************************************************

  Synopsis    [Replays an all-state SAT model's inputs from the actual reset.]

***********************************************************************/
static int Pdr2_ManCombTrace( Aig_Man_t * pAig, Vec_Int_t * vInit, Vec_Ptr_t * vSupport,
                              Vec_Int_t * vModel, int Frames )
{
    int nPis = Saig_ManPiNum(pAig), nRegs = Aig_ManRegNum(pAig);
    int i, f, Value;
    Abc_Cex_t * pCex;
    Frames = Abc_MinInt(Frames, Abc_MaxInt(1, 4000000 / Aig_ManObjNumMax(pAig)));
    if ( (ABC_INT64_T)nPis * Frames + nRegs > INT_MAX )
        return 0;
    pCex = Abc_CexAlloc( nRegs, nPis, Frames );
    pCex->iPo = 0;
    pCex->iFrame = Frames - 1;
    for ( i = 0; i < nRegs; i++ )
        if ( vInit && Vec_IntEntry(vInit, i) == 1 )
            Abc_InfoSetBit( pCex->pData, i );
    if ( vModel )
        Vec_IntForEachEntry( vModel, Value, i )
        {
            int Ci = Aig_ObjCioId((Aig_Obj_t *)Vec_PtrEntry(vSupport, i));
            if ( !Value ) continue;
            if ( Ci < nPis )
                for ( f = 0; f < Frames; f++ )
                    Abc_InfoSetBit( pCex->pData, nRegs + f*nPis + Ci );
            else if ( vInit && Vec_IntEntry(vInit, Ci-nPis) == 2 )
                Abc_InfoSetBit( pCex->pData, Ci-nPis );
        }
    if ( Pdr2_ManFirstBad(pAig, pCex) && Saig_ManVerifyCex(pAig, pCex) )
    {
        Abc_CexFreeP( &pAig->pSeqModel );
        pAig->pSeqModel = pCex;
        return 1;
    }
    Abc_CexFree( pCex );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Proves combinational safety for all current states.]

***********************************************************************/
// A bounded proof that bad is impossible even with arbitrary current state.
// Only the combinational property cone is needed; adding the unrelated
// next-state functions would waste both SAT setup time and memory. This is
// particularly useful after property lookahead removes monitor registers.
int Pdr2_ManCombSafe( Aig_Man_t * pAig, Pdr2_Par_t * pPars, abctime timeGlobal, Aig_Man_t * pTraceAig, Vec_Int_t * vInit )
{
    int Confs = Gip_OptionGet("PDR2_CSAFE") ? atoi(Gip_OptionGet("PDR2_CSAFE")) : 0;
    int Seconds = Gip_OptionGet("PDR2_CSAFE_TIME") ? Abc_MaxInt(1, atoi(Gip_OptionGet("PDR2_CSAFE_TIME"))) : 1;
    int Lit, Ret, fCancelled = 0, fTrace = 0;
    int TraceFrames = pTraceAig && Gip_OptionGet("PDR2_CSAFE_TRACE") ?
        Abc_MaxInt(0, Abc_MinInt(32, atoi(Gip_OptionGet("PDR2_CSAFE_TRACE")))) : 0;
    int fKissat = Gip_OptionGet("PDR2_CSAFE_KISSAT") && atoi(Gip_OptionGet("PDR2_CSAFE_KISSAT"));
    abctime Start, Deadline;
    Vec_Ptr_t * vPis, * vPos;
    Vec_Int_t * vModel = NULL;
    Aig_Man_t * pCone;
    Cnf_Man_t * pCnfMan;
    Gip_Ctx_t * pCtx;
    Gip_Solver_t * pSat;
    if ( (pPars->fVerify && pPars->fVerifyComplete) || Confs <= 0 || pPars->nPropLimit || pPars->nFrameMax ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ) return -1;
    if ( Gip_OptionGet("PDR2_CSAFE_PART") && atoi(Gip_OptionGet("PDR2_CSAFE_PART")) && !pPars->fPartRun ) return -1;
    Start = Abc_Clock(); Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Deadline > timeGlobal ) Deadline = timeGlobal;
    if ( Start >= Deadline || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) return -1;
    if ( Aig_ObjChild0(Aig_ManCo(pAig,0)) == Aig_ManConst0(pAig) ) return 1;
    if ( Aig_ObjChild0(Aig_ManCo(pAig,0)) == Aig_ManConst1(pAig) )
        return TraceFrames && Pdr2_ManCombTrace(pTraceAig, vInit, NULL, NULL, 1) ? 0 : -1;
    if ( TraceFrames )
    {
        assert( Aig_ManCiNum(pAig) == Aig_ManCiNum(pTraceAig) );
        Aig_ManSetCioIds( pAig );
    }
    vPis = Vec_PtrAlloc(100); vPos = Vec_PtrAlloc(1);
    Vec_PtrPush(vPos, Aig_ManCo(pAig,0));
    Aig_SupportNodes(pAig, (Aig_Obj_t **)Vec_PtrArray(vPos), 1, vPis);
    pCone = Aig_ManDupSimpleDfsPart(pAig, vPis, vPos);
    Vec_PtrFree(vPos);
    if ( Gip_OptionGet("PDR2_CSAFE_CEC") )
    {
        Ret = Pdr2_ManCombSweep(&pCone, pPars, Start + (Deadline-Start)/2, &fCancelled);
        if ( Ret != -1 || fCancelled || Abc_Clock() >= Deadline )
        {
            Ret = Ret == 1 ? GIP_UNSAT : Ret == 0 ? GIP_SAT : GIP_UNDEF;
            goto finish;
        }
    }
    Aig_ManSetCioIds(pCone);
    if ( fKissat || (Gip_OptionGet("PDR2_CSAFE_CADICAL") && atoi(Gip_OptionGet("PDR2_CSAFE_CADICAL"))) )
    {
        // Sweeping may reorder or remove support variables.  The original
        // support maps the unswept CNF model directly to design inputs.
        if ( TraceFrames && !Gip_OptionGet("PDR2_CSAFE_CEC") )
            vModel = Vec_IntAlloc( Vec_PtrSize(vPis) );
        Ret = Pdr2_ManCombMapped( pCone, pPars, Deadline, Confs, fKissat, vModel );
        if ( Ret == GIP_SAT && vModel && Abc_Clock() < Deadline &&
             (!pPars->pFuncStop || !pPars->pFuncStop(pPars->RunId)) )
            fTrace = Pdr2_ManCombTrace( pTraceAig, vInit, vPis, vModel, TraceFrames );
        goto finish;
    }
    pCnfMan = Cnf_ManStart(); pCtx = Gip_CtxCreatePdr2(pCone, pCnfMan, 1);
    pSat = Gip_SolverNew(pCtx);
    pSat->TimeLimit = Deadline; pSat->nConfLimit = Abc_MinInt(Confs,1000000);
    pSat->RunId = pPars->RunId; pSat->pFuncStop = pPars->pFuncStop;
    Lit = Gip_Lit(Gip_CtxObjVar(pCtx,Aig_ManCo(pCone,0)),0);
    Ret = Gip_SolverSolve(pSat,&Lit,1,NULL,NULL,0,-1);
    Gip_SolverFree(pSat); Gip_CtxFree(pCtx); Cnf_ManStop(pCnfMan);
finish:
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1,"Combinational safety check: %s; %d cone inputs, %d nodes. Time = %.3f sec.\n",
            Ret == GIP_UNSAT ? "proved" : Ret == GIP_SAT ? "not combinationally safe" : "resource limit",
            Aig_ManCiNum(pCone), Aig_ManNodeNum(pCone), (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Aig_ManStop(pCone);
    Vec_PtrFree(vPis);
    Vec_IntFreeP(&vModel);
    return Ret == GIP_UNSAT ? 1 : fTrace ? 0 : -1;
}

/**Function*************************************************************

  Synopsis    [Samples a cut of the bad output on one common clock edge.]

  Description [For bad = h(g1,...,gm) add registers qj' = gj and use
  started & h(q) as the bad output. After startup its value is exactly
  the previous bad output, including when the cut depends on inputs.
  Discard the last input vector when transferring a witness.]

***********************************************************************/
int Pdr2_ManSampleProperty( Aig_Man_t * p, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Width )
{
    int i, j, Id, Best, Result = -1, nRegs = Aig_ManRegNum(p), nPis = Saig_ManPiNum(p);
    Aig_Man_t * pNew = NULL;
    Aig_Obj_t * pObj, * pFan, * pStart;
    Vec_Int_t * vCut, * vNewInit = NULL;
    Vec_Ptr_t * vAux = NULL, * vDrivers = NULL, * vNext = NULL;
    Pdr2_Par_t Child = *pPars;
    abctime Start = Abc_Clock();
    if ( Width < 2 || Width > 64 || !nRegs || Saig_ManPoNum(p) != 1 || Saig_ManConstrNum(p) ||
         Aig_ManBufNum(p) || Aig_ManExorNum(p) || pPars->fDumpInv || pPars->fVerifyComplete ||
         (vInit && Vec_IntSize(vInit) != nRegs) ) return -1;
    pObj = Aig_ObjFanin0(Aig_ManCo(p, 0));
    if ( !Aig_ObjIsNode(pObj) ) return -1;
    vCut = Vec_IntAlloc(Width);
    Vec_IntPush(vCut, Aig_ObjId(pObj));
    Aig_ManIncrementTravId(p);
    for ( j = 0; j < 4*Width && Vec_IntSize(vCut) < Width; j++ )
    {
        Best = -1;
        Vec_IntForEachEntry( vCut, Id, i )
        {
            pObj = Aig_ManObj(p, Id);
            if ( Aig_ObjIsNode(pObj) && (Best < 0 ||
                 Aig_ObjLevel(pObj) > Aig_ObjLevel(Aig_ManObj(p, Vec_IntEntry(vCut, Best)))) ) Best = i;
        }
        if ( Best < 0 ) break;
        pObj = Aig_ManObj(p, Vec_IntEntry(vCut, Best));
        Vec_IntDrop(vCut, Best);
        Aig_ObjSetTravIdCurrent(p, pObj);
        pFan = Aig_ObjFanin0(pObj);
        if ( !Aig_ObjIsConst1(pFan) && !Aig_ObjIsTravIdCurrent(p, pFan) ) Vec_IntPushUnique(vCut, Aig_ObjId(pFan));
        pFan = Aig_ObjFanin1(pObj);
        if ( !Aig_ObjIsConst1(pFan) && !Aig_ObjIsTravIdCurrent(p, pFan) ) Vec_IntPushUnique(vCut, Aig_ObjId(pFan));
    }
    if ( !Vec_IntSize(vCut) ) goto done;
    pNew = Aig_ManStart(Aig_ManNodeNum(p));
    pNew->pName = Abc_UtilStrsav(p->pName);
    vNewInit = vInit ? Vec_IntDup(vInit) : Vec_IntStart(nRegs);
    vAux = Vec_PtrAlloc(Width); vDrivers = Vec_PtrAlloc(Width); vNext = Vec_PtrAlloc(nRegs);
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( p, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    for ( i = 0; i < Vec_IntSize(vCut); i++ )
    {
        Vec_PtrPush(vAux, Aig_ObjCreateCi(pNew));
        Vec_IntPush(vNewInit, 0);
    }
    pStart = Aig_ObjCreateCi(pNew);
    Vec_IntPush(vNewInit, 0);
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Saig_ManForEachLi( p, pObj, i ) Vec_PtrPush(vNext, Aig_ObjChild0Copy(pObj));
    Vec_IntForEachEntry( vCut, Id, i ) Vec_PtrPush(vDrivers, Aig_ManObj(p, Id)->pData);
    Vec_IntForEachEntry( vCut, Id, i ) Aig_ManObj(p, Id)->pData = Vec_PtrEntry(vAux, i);
    Aig_ManForEachNode( p, pObj, i )
        if ( Aig_ObjIsTravIdCurrent(p, pObj) )
            pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ObjCreateCo(pNew, Aig_And(pNew, pStart, Aig_ObjChild0Copy(Aig_ManCo(p, 0))));
    Vec_PtrForEachEntry( Aig_Obj_t *, vNext, pObj, i ) Aig_ObjCreateCo(pNew, pObj);
    Vec_PtrForEachEntry( Aig_Obj_t *, vDrivers, pObj, i ) Aig_ObjCreateCo(pNew, pObj);
    Aig_ObjCreateCo(pNew, Aig_ManConst1(pNew));
    Aig_ManSetRegNum(pNew, Vec_IntSize(vNewInit));
    Aig_ManSetCioIds(pNew);
    Aig_ManCleanup(pNew);
    if ( pPars->nTimeOut )
    {
        Child.nTimeOut -= (int)((Abc_Clock() - Start) / CLOCKS_PER_SEC);
        if ( Child.nTimeOut < 1 ) goto done;
    }
    if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) ) goto done;
    if ( pPars->fVerbose )
        Abc_Print(1, "Sampled property: %d registered cut signals, %d original flops.\n", Vec_IntSize(vCut), nRegs);
    Result = Pdr2_ManSolveInit(pNew, vNewInit, &Child);
    if ( Result == 0 )
    {
        Abc_Cex_t * c = pNew->pSeqModel, * d;
        Result = -1;
        if ( !c || c->iFrame < 1 || c->nRegs != Vec_IntSize(vNewInit) || c->nPis != nPis ) goto done;
        d = Abc_CexAlloc(nRegs, nPis, c->iFrame);
        d->iPo = 0; d->iFrame = c->iFrame - 1;
        for ( i = 0; i < nRegs; ++i ) if ( Abc_InfoHasBit(c->pData, i) ) Abc_InfoSetBit(d->pData, i);
        for ( i = 0; i < nPis*c->iFrame; ++i )
            if ( Abc_InfoHasBit(c->pData, c->nRegs+i) ) Abc_InfoSetBit(d->pData, nRegs+i);
        if ( Saig_ManVerifyCex(p, d) )
        {
            Abc_CexFreeP(&p->pSeqModel);
            p->pSeqModel = d; pPars->iFrame = d->iFrame; Result = 0;
        }
        else Abc_CexFree(d);
    }
done:
    if ( pNew ) Aig_ManStop(pNew);
    Vec_IntFree(vCut); Vec_IntFreeP(&vNewInit);
    Vec_PtrFreeP(&vAux); Vec_PtrFreeP(&vDrivers); Vec_PtrFreeP(&vNext);
    return Result;
}

typedef struct Pdr2_PredRank_t_ { int Id, Score; } Pdr2_PredRank_t;

/**Function*************************************************************

  Synopsis    [Compares state-predicate candidates for redundant register encoding.]

  Description []

***********************************************************************/
static int Pdr2_PredRankCompare( const void * a, const void * b )
{
    const Pdr2_PredRank_t * x = (const Pdr2_PredRank_t *)a, * y = (const Pdr2_PredRank_t *)b;
    return x->Score != y->Score ? (x->Score < y->Score ? 1 : -1) : (x->Id > y->Id) - (x->Id < y->Id);
}

/**Function*************************************************************

  Synopsis    [Introduces redundant registers for selected state predicates.]

  Description []

***********************************************************************/
// Give PDR a small vocabulary of shared Boolean state predicates. For a
// selected state-only function h, add q_h with init h(init) and transition
// q_h' = h(T_new). Replace occurrences of h in the old logic by q_h.
// q_h = h(state) is therefore an invariant by construction. No input may
// occur in h, and unknown initial states are skipped to avoid losing their
// correlations. This is an exact redundant-state encoding, not abstraction.
static int Pdr2_ManPredicates( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                              abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Max = Gip_OptionGet("PDR2_PREDICATES") ? Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_PREDICATES"))) : 0;
    int Seconds = Gip_OptionGet("PDR2_PRED_TIME") ? atoi(Gip_OptionGet("PDR2_PRED_TIME")) : 60;
    int Kind = Gip_OptionGet("PDR2_PRED_KIND") ? atoi(Gip_OptionGet("PDR2_PRED_KIND")) : 1;
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig), nObjs = Aig_ManObjNumMax(pAig);
    int i, k, Id, nRanks = 0, nAux, Result = -1;
    char * pPure, * pVals;
    int * pSelect;
    Pdr2_PredRank_t * pRanks;
    Aig_Obj_t * pObj, ** pFuture;
    Aig_Man_t * pNew = NULL;
    Vec_Int_t * vInit = NULL;
    Pdr2_Par_t Child = *pPars;
    abctime Start, Deadline, Remaining;
    *ppCex = NULL;
    if ( Max <= 0 || Seconds <= 0 || pPars->fPredRun || !nRegs || pPars->nFrameMax || pPars->nPropLimit ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) || Aig_ManNodeNum(pAig) > 2000000 ) return -1;
    for ( i = 0; i < nRegs; i++ ) if ( pInit[i] == 2 ) return -1;
    Start = Abc_Clock(); Deadline = Start + (abctime)Seconds * CLOCKS_PER_SEC;
    if ( timeGlobal && Deadline > timeGlobal ) Deadline = timeGlobal;
    pPure = ABC_CALLOC( char, nObjs ); pVals = ABC_CALLOC( char, nObjs );
    pSelect = ABC_ALLOC( int, nObjs ); memset(pSelect, 0xff, sizeof(int)*nObjs);
    pFuture = ABC_CALLOC( Aig_Obj_t *, nObjs );
    pRanks = ABC_ALLOC( Pdr2_PredRank_t, Abc_MaxInt(1, Aig_ManNodeNum(pAig)) );
    Id = Aig_ObjId(Aig_ManConst1(pAig)); pPure[Id] = pVals[Id] = 1;
    Saig_ManForEachLo( pAig, pObj, i ) { pPure[Aig_ObjId(pObj)] = 1; pVals[Aig_ObjId(pObj)] = pInit[i]; }
    Aig_ManForEachNode( pAig, pObj, i )
    {
        Id = Aig_ObjId(pObj);
        pPure[Id] = pPure[Aig_ObjFaninId0(pObj)] && pPure[Aig_ObjFaninId1(pObj)];
        pVals[Id] = (pVals[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj)) &
                    (pVals[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj));
        if ( !pPure[Id] || Aig_ObjLevel(pObj) < 2 || (Kind == 1 && Aig_ObjRefs(pObj) < 2) ) continue;
        pRanks[nRanks].Id = Id;
        pRanks[nRanks++].Score = Kind == 2 ?
            1024*Abc_MinInt(Aig_ObjLevel(pObj),100000) + Abc_MinInt(Aig_ObjRefs(pObj),1023) :
            1024*Abc_MinInt(Aig_ObjRefs(pObj),100000) + Abc_MinInt(Aig_ObjLevel(pObj),1023);
    }
    nAux = Abc_MinInt(Max, nRanks);
    if ( !nAux ) goto done;
    qsort( pRanks, nRanks, sizeof(Pdr2_PredRank_t), Pdr2_PredRankCompare );
    for ( k = 0; k < nAux; k++ ) pSelect[pRanks[k].Id] = k;
    pNew = Aig_ManStart( 2*Aig_ManNodeNum(pAig) );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    vInit = Vec_IntAlloc( nRegs+nAux );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    pFuture[Aig_ObjId(Aig_ManConst1(pAig))] = Aig_ManConst1(pNew);
    Aig_ManForEachCi( pAig, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    for ( k = 0; k < nAux; k++ ) Aig_ObjCreateCi(pNew);
    for ( i = 0; i < nRegs; i++ ) Vec_IntPush(vInit, pInit[i]);
    for ( k = 0; k < nAux; k++ ) Vec_IntPush(vInit, pVals[pRanks[k].Id]);
    Aig_ManForEachNode( pAig, pObj, i )
    {
        k = pSelect[Aig_ObjId(pObj)];
        pObj->pData = k < 0 ? Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj)) : Aig_ManCi(pNew, nPis+nRegs+k);
    }
    // Evaluate the original h functions on the rewritten next state. Do
    // not replace a selected h by its current q_h during this second copy.
    Saig_ManForEachLo( pAig, pObj, i ) pFuture[Aig_ObjId(pObj)] = Aig_ObjChild0Copy(Saig_ManLi(pAig, i));
    Aig_ManForEachNode( pAig, pObj, i )
        if ( pPure[Aig_ObjId(pObj)] )
            pFuture[Aig_ObjId(pObj)] = Aig_And(pNew,
                Aig_NotCond(pFuture[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj)),
                Aig_NotCond(pFuture[Aig_ObjFaninId1(pObj)], Aig_ObjFaninC1(pObj)));
    Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(Aig_ManCo(pAig, 0)));
    Saig_ManForEachLi( pAig, pObj, i ) Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));
    for ( k = 0; k < nAux; k++ ) Aig_ObjCreateCo(pNew, pFuture[pRanks[k].Id]);
    Aig_ManSetRegNum(pNew, nRegs+nAux); Aig_ManSetCioIds(pNew); Aig_ManCleanup(pNew);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "State predicate extension: %d of %d candidates, flops %d -> %d, nodes %d -> %d (kind %d).\n",
            nAux, nRanks, nRegs, nRegs+nAux, Aig_ManNodeNum(pAig), Aig_ManNodeNum(pNew), Kind);
    Remaining = Deadline-Abc_Clock(); if ( Remaining < CLOCKS_PER_SEC ) goto done;
    Child.nTimeOut = (int)(Remaining/CLOCKS_PER_SEC);
    Child.fPredRun = Child.fPartRun = 1;
    Child.fDynamic = Child.nAbsRuns = Child.nDynTime = 0;
    Child.fPreproc = Child.fDumpInv = Child.nBmcTime = 0;
    if ( Child.fUseAbs ) Child.fAbsRefineAll = 1;
    Result = Pdr2_ManSolveInit(pNew, vInit, &Child);
    if ( Result == 0 && pNew->pSeqModel )
    {
        Abc_Cex_t * c = pNew->pSeqModel, * d = Abc_CexAlloc(nRegs, nPis, c->iFrame+1);
        assert(c->nRegs == nRegs+nAux && c->nPis == nPis);
        d->iPo = 0; d->iFrame = c->iFrame;
        for ( i = 0; i < nRegs; i++ ) if ( Abc_InfoHasBit(c->pData,i) ) Abc_InfoSetBit(d->pData,i);
        for ( i = 0; i < nPis*(c->iFrame+1); i++ )
            if ( Abc_InfoHasBit(c->pData,c->nRegs+i) ) Abc_InfoSetBit(d->pData,nRegs+i);
        if ( Saig_ManVerifyCex(pAig,d) ) *ppCex = d;
        else { Abc_Print(1,"State-predicate counterexample verification FAILED.\n"); Abc_CexFree(d); Result = -1; }
    }
done:
    if ( pNew ) Aig_ManStop(pNew);
    Vec_IntFreeP(&vInit); ABC_FREE(pPure); ABC_FREE(pVals); ABC_FREE(pSelect); ABC_FREE(pRanks); ABC_FREE(pFuture);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Builds a reverse search with the original bad-state set as its initial condition.]

  Description []

***********************************************************************/
// Reverse search with the exact bad-state set as its initial condition.
// The final original input vector is kept in frozen state registers. An
// otherwise unused LI exposes the initial predicate to the frame-0 solver.
static int Pdr2_ManReverseInitial( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                                  abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    int Seconds = Gip_OptionGet("PDR2_REVERSE") ? Abc_MaxInt(0,Abc_MinInt(900,atoi(Gip_OptionGet("PDR2_REVERSE")))) : 0;
    int MaxRegs = Gip_OptionGet("PDR2_REVERSE_REGS") ? Abc_MaxInt(1,atoi(Gip_OptionGet("PDR2_REVERSE_REGS"))) : 1024;
    int fWitness = Gip_OptionGet("PDR2_REVERSE_WITNESS") && atoi(Gip_OptionGet("PDR2_REVERSE_WITNESS"));
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig);
    int nNewPis = nRegs+nPis+(fWitness ? nPis : 0), nNewRegs = nRegs+(fWitness ? 0 : nPis)+2;
    int i, j, f, Result = -1;
    int SeedTime = Gip_OptionGet("PDR2_REVERSE_SEED") ? Abc_MaxInt(0,Abc_MinInt(30,atoi(Gip_OptionGet("PDR2_REVERSE_SEED")))) : 0;
    abctime Start = Abc_Clock(), Stop = Start+(abctime)Seconds*CLOCKS_PER_SEC, Left;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pValid, * pInitBad, * pInitLit, * pConsistent;
    Vec_Ptr_t * vNext;
    Vec_Int_t * vInit, * vRow;
    Vec_Wec_t * vSeed = NULL;
    Aig_Obj_t * pSeedCurrent, * pSeedNext, * pClause;
    Pdr2_Par_t Child = *pPars;
    *ppCex = NULL;
    if ( !Seconds || !nRegs || nRegs > MaxRegs || nNewRegs > 20000 ||
         pPars->fPartRun || pPars->fShiftRun || pPars->fStrideRun || pPars->fPredRun ||
         pPars->fDumpInv || pPars->nFrameMax || pPars->nPropLimit ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) || Aig_ManNodeNum(pAig) > 200000 ) return -1;
    if ( timeGlobal && timeGlobal < Stop ) Stop = timeGlobal;
    if ( Stop-Abc_Clock() < CLOCKS_PER_SEC ) return -1;
    vSeed = Vec_WecAlloc(100);
    if ( SeedTime )
    {
        Pdr2_Par_t SeedPars = *pPars;
        Pdr2_Man_t * pSeed;
        Pdr2_Lem_t * pLem;
        SeedPars.fUseAbs = SeedPars.nInitLiReg = 0;
        pSeed = Pdr2_ManStart(pAig,pInit,&SeedPars);
        pSeed->timeGlobal = Stop;
        Pdr2_ManSeedInvariants(pSeed,SeedTime);
        Vec_PtrForEachEntry(Pdr2_Lem_t *,pSeed->vInf,pLem,i)
            Vec_IntPushArray(Vec_WecPushLevel(vSeed),pLem->pCube->Lits,pLem->pCube->nLits);
        Pdr2_ManStop(pSeed);
        if ( pPars->fVerbose && !pPars->fSilent )
            Abc_Print(1,"Reverse guidance: %d certified forward invariants.\n",Vec_WecSize(vSeed));
    }
    pNew = Aig_ManStart(2*Aig_ManNodeNum(pAig)+10*nRegs);
    pNew->pName = Abc_UtilStrsav(pAig->pName);
    for ( i = 0; i < nNewPis+nNewRegs; i++ ) Aig_ObjCreateCi(pNew);
    pValid = Aig_ManCi(pNew,nNewPis+nRegs+(fWitness ? 0 : nPis));
    vNext = Vec_PtrAlloc(nRegs); vInit = Vec_IntAlloc(nNewRegs);
    Vec_IntFill(vInit,nNewRegs,2); Vec_IntWriteEntry(vInit,nRegs+(fWitness ? 0 : nPis),1);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,i);
    Saig_ManForEachLo(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,nPis+i);
    Aig_ManForEachNode(pAig,pObj,i) pObj->pData = Aig_And(pNew,Aig_ObjChild0Copy(pObj),Aig_ObjChild1Copy(pObj));
    Saig_ManForEachLi(pAig,pObj,i) Vec_PtrPush(vNext,Aig_ObjChild0Copy(pObj));
    pConsistent = Aig_ManConst1(pNew);
    for ( i = 0; i < nRegs; i++ )
        pConsistent = Aig_And(pNew,pConsistent,Aig_Not(Aig_Exor(pNew,
            (Aig_Obj_t *)Vec_PtrEntry(vNext,i),Aig_ManCi(pNew,nNewPis+i))));
    pSeedNext = Aig_ManConst1(pNew);
    Vec_WecForEachLevel(vSeed,vRow,i)
    {
        int Lit;
        pClause = Aig_ManConst0(pNew);
        Vec_IntForEachEntry(vRow,Lit,j)
            pClause = Aig_Or(pNew,pClause,Aig_NotCond(Aig_ManCi(pNew,nPis+Abc_Lit2Var(Lit)),!Abc_LitIsCompl(Lit)));
        pSeedNext = Aig_And(pNew,pSeedNext,pClause);
    }
    pConsistent = Aig_And(pNew,pConsistent,pSeedNext);
    Saig_ManForEachPi(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,(fWitness ? nPis+nRegs : nNewPis+nRegs)+i);
    Saig_ManForEachLo(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,nNewPis+i);
    Aig_ManForEachNode(pAig,pObj,i) pObj->pData = Aig_And(pNew,Aig_ObjChild0Copy(pObj),Aig_ObjChild1Copy(pObj));
    pInitBad = Aig_ObjChild0Copy(Aig_ManCo(pAig,0));
    pSeedCurrent = Aig_ManConst1(pNew);
    Vec_WecForEachLevel(vSeed,vRow,i)
    {
        int Lit;
        pClause = Aig_ManConst0(pNew);
        Vec_IntForEachEntry(vRow,Lit,j)
            pClause = Aig_Or(pNew,pClause,Aig_NotCond(Aig_ManCi(pNew,nNewPis+Abc_Lit2Var(Lit)),!Abc_LitIsCompl(Lit)));
        pSeedCurrent = Aig_And(pNew,pSeedCurrent,pClause);
    }
    // Every original counterexample stays inside these forward invariants.
    // Both endpoints of each retained reverse transition must satisfy them.
    pInitBad = Aig_And(pNew,pInitBad,pSeedCurrent);
    pConsistent = Aig_And(pNew,pConsistent,pSeedCurrent);
    pInitLit = Aig_ManConst1(pNew);
    for ( i = 0; i < nRegs; i++ ) if ( pInit[i] != 2 )
        pInitLit = Aig_And(pNew,pInitLit,Aig_NotCond(Aig_ManCi(pNew,nNewPis+i),pInit[i] == 0));
    Aig_ObjCreateCo(pNew,Aig_And(pNew,pInitLit,pValid));
    for ( i = 0; i < nRegs; i++ ) Aig_ObjCreateCo(pNew,Aig_ManCi(pNew,nPis+i));
    if ( !fWitness )
        for ( i = 0; i < nPis; i++ ) Aig_ObjCreateCo(pNew,Aig_ManCi(pNew,nNewPis+nRegs+i));
    Aig_ObjCreateCo(pNew,Aig_And(pNew,pValid,pConsistent));
    Aig_ObjCreateCo(pNew,pInitBad);
    Aig_ManSetRegNum(pNew,nNewRegs); Aig_ManSetCioIds(pNew); Aig_ManCleanup(pNew);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1,"Reverse transition with exact initial predicate: %d inputs, %d flops, %d nodes.\n",nNewPis,nNewRegs,Aig_ManNodeNum(pNew));
    Left = Stop-Abc_Clock();
    if ( Left >= CLOCKS_PER_SEC && (!pPars->pFuncStop || !pPars->pFuncStop(pPars->RunId)) )
    {
        Child.nTimeOut = (int)(Left/CLOCKS_PER_SEC);
        Child.fPartRun = Child.fStrideRun = Child.fPredRun = 1; Child.fShiftRun = 4;
        Child.fDynamic = Child.nAbsRuns = Child.nDynTime = Child.fUseAbs = 0;
        Child.fPreproc = Child.fDumpInv = Child.nBmcTime = 0;
        Child.nInitLiReg = nNewRegs;
        Child.nInitWitnessPi = fWitness ? nPis+nRegs+1 : 0;
        Child.nInitWitnessNum = fWitness ? nPis : 0;
        Child.fVerify = Child.fVerifyComplete = 1;
        Result = Pdr2_ManSolveInit(pNew,vInit,&Child);
    }
    if ( Result == 0 && pNew->pSeqModel )
    {
        Abc_Cex_t * c = pNew->pSeqModel, * d = Abc_CexAlloc(nRegs,nPis,c->iFrame+1);
        int Depth = c->iFrame;
        assert(c->nRegs == nNewRegs && c->nPis == nNewPis);
        d->iFrame = Depth; d->iPo = 0;
        for ( i = 0; i < nRegs; i++ )
            if ( Abc_InfoHasBit(c->pData,Depth ? c->nRegs+(Depth-1)*nNewPis+nPis+i : i) ) Abc_InfoSetBit(d->pData,i);
        for ( f = 0; f < Depth; f++ ) for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(c->pData,c->nRegs+(Depth-1-f)*nNewPis+i) ) Abc_InfoSetBit(d->pData,nRegs+f*nPis+i);
        for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(c->pData,(fWitness ? c->nRegs+nPis+nRegs : nRegs)+i) ) Abc_InfoSetBit(d->pData,nRegs+Depth*nPis+i);
        if ( Saig_ManVerifyCex(pAig,d) ) *ppCex = d;
        else { Abc_Print(1,"Exact-initial reverse counterexample verification FAILED.\n"); Abc_CexFree(d); Result = -1; }
    }
    else if ( Result == 0 ) Result = -1;
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1,"Exact-initial reverse reachability: %s in %.3f sec.\n",Result == 1 ? "proved" : *ppCex ? "checked counterexample" : "undecided",(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Vec_PtrFree(vNext); Vec_IntFree(vInit); Vec_WecFree(vSeed); Aig_ManStop(pNew);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Checks reachability with a relational encoding of backward transitions.]

  Description []

***********************************************************************/
// Encode the relational reverse transition with nondeterministic inputs.
// A persistent valid bit rejects any step whose guessed predecessor does
// not transition to the current state. At the first step, an independent
// input vector witnesses the original bad predicate. The reverse target is
// the original initial-state predicate. This preserves finite bad traces.
static int Pdr2_ManReverse( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
                           abctime timeGlobal, Abc_Cex_t ** ppCex )
{
    if ( Gip_OptionGet("PDR2_REVERSE_INIT") && atoi(Gip_OptionGet("PDR2_REVERSE_INIT")) )
        return Pdr2_ManReverseInitial(pAig,pInit,pPars,timeGlobal,ppCex);
    int Seconds = Gip_OptionGet("PDR2_REVERSE") ? Abc_MaxInt(0, Abc_MinInt(900, atoi(Gip_OptionGet("PDR2_REVERSE")))) : 0;
    int MaxRegs = Gip_OptionGet("PDR2_REVERSE_REGS") ? Abc_MaxInt(1, atoi(Gip_OptionGet("PDR2_REVERSE_REGS"))) : 1024;
    int nRegs = Aig_ManRegNum(pAig), nPis = Saig_ManPiNum(pAig), nNewPis = nRegs+2*nPis;
    int i, f, Result = -1;
    abctime Start = Abc_Clock(), Stop = Start+(abctime)Seconds*CLOCKS_PER_SEC, Left;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pValid, * pFirst, * pGate, * pInitLit, * pConsistent;
    Vec_Ptr_t * vNext;
    Vec_Int_t * vInit;
    Pdr2_Par_t Child = *pPars;
    *ppCex = NULL;
    if ( !Seconds || !nRegs || nRegs > MaxRegs || nNewPis > 20000 ||
         pPars->fPartRun || pPars->fShiftRun || pPars->fStrideRun || pPars->fPredRun ||
         pPars->fDumpInv || pPars->nFrameMax || pPars->nPropLimit ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) || Aig_ManNodeNum(pAig) > 200000 ) return -1;
    if ( timeGlobal && timeGlobal < Stop ) Stop = timeGlobal;
    if ( Stop-Abc_Clock() < CLOCKS_PER_SEC ) return -1;
    pNew = Aig_ManStart(2*Aig_ManNodeNum(pAig)+10*nRegs);
    pNew->pName = Abc_UtilStrsav(pAig->pName);
    for ( i = 0; i < nNewPis+nRegs+2; i++ ) Aig_ObjCreateCi(pNew);
    pValid = Aig_ManCi(pNew,nNewPis+nRegs);
    pFirst = Aig_ManCi(pNew,nNewPis+nRegs+1);
    vNext = Vec_PtrAlloc(nRegs);
    vInit = Vec_IntStartFull(nRegs+2);
    Vec_IntFill(vInit,nRegs+2,2);
    Vec_IntWriteEntry(vInit,nRegs,1); Vec_IntWriteEntry(vInit,nRegs+1,1);
    // Transition inputs and guessed predecessor state.
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,i);
    Saig_ManForEachLo(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,nPis+i);
    Aig_ManForEachNode(pAig,pObj,i)
        pObj->pData = Aig_And(pNew,Aig_ObjChild0Copy(pObj),Aig_ObjChild1Copy(pObj));
    Saig_ManForEachLi(pAig,pObj,i) Vec_PtrPush(vNext,Aig_ObjChild0Copy(pObj));
    pConsistent = Aig_ManConst1(pNew);
    for ( i = 0; i < nRegs; i++ )
        pConsistent = Aig_And(pNew,pConsistent,Aig_Not(Aig_Exor(pNew,
            (Aig_Obj_t *)Vec_PtrEntry(vNext,i),Aig_ManCi(pNew,nNewPis+i))));
    // The final bad-state inputs are independent of the preceding step's
    // transition inputs, including for a one-step original counterexample.
    Saig_ManForEachPi(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,nPis+nRegs+i);
    Saig_ManForEachLo(pAig,pObj,i) pObj->pData = Aig_ManCi(pNew,nNewPis+i);
    Aig_ManForEachNode(pAig,pObj,i)
        pObj->pData = Aig_And(pNew,Aig_ObjChild0Copy(pObj),Aig_ObjChild1Copy(pObj));
    pGate = Aig_Or(pNew,Aig_Not(pFirst),Aig_ObjChild0Copy(Aig_ManCo(pAig,0)));
    pInitLit = Aig_ManConst1(pNew);
    for ( i = 0; i < nRegs; i++ ) if ( pInit[i] != 2 )
        pInitLit = Aig_And(pNew,pInitLit,Aig_NotCond(Aig_ManCi(pNew,nNewPis+i),pInit[i] == 0));
    Aig_ObjCreateCo(pNew,Aig_And(pNew,pInitLit,Aig_And(pNew,pValid,pGate)));
    for ( i = 0; i < nRegs; i++ ) Aig_ObjCreateCo(pNew,Aig_ManCi(pNew,nPis+i));
    Aig_ObjCreateCo(pNew,Aig_And(pNew,pValid,Aig_And(pNew,pGate,pConsistent)));
    Aig_ObjCreateCo(pNew,Aig_ManConst0(pNew));
    Aig_ManSetRegNum(pNew,nRegs+2); Aig_ManSetCioIds(pNew); Aig_ManCleanup(pNew);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1,"Reverse transition: %d inputs, %d flops, %d nodes.\n",nNewPis,nRegs+2,Aig_ManNodeNum(pNew));
    Left = Stop-Abc_Clock();
    if ( Left >= CLOCKS_PER_SEC && (!pPars->pFuncStop || !pPars->pFuncStop(pPars->RunId)) )
    {
        Child.nTimeOut = (int)(Left/CLOCKS_PER_SEC);
        Child.fPartRun = Child.fStrideRun = Child.fPredRun = 1; Child.fShiftRun = 4;
        Child.fDynamic = Child.nAbsRuns = Child.nDynTime = Child.fUseAbs = 0;
        Child.fPreproc = Child.fDumpInv = Child.nBmcTime = 0;
        Result = Pdr2_ManSolveInit(pNew,vInit,&Child);
    }
    if ( Result == 0 && pNew->pSeqModel )
    {
        Abc_Cex_t * c = pNew->pSeqModel, * d = Abc_CexAlloc(nRegs,nPis,c->iFrame+1);
        int Depth = c->iFrame;
        assert(c->nRegs == nRegs+2 && c->nPis == nNewPis);
        d->iFrame = Depth; d->iPo = 0;
        for ( i = 0; i < nRegs; i++ )
            if ( Abc_InfoHasBit(c->pData,Depth ? c->nRegs+(Depth-1)*nNewPis+nPis+i : i) )
                Abc_InfoSetBit(d->pData,i);
        for ( f = 0; f < Depth; f++ ) for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(c->pData,c->nRegs+(Depth-1-f)*nNewPis+i) )
                Abc_InfoSetBit(d->pData,nRegs+f*nPis+i);
        for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(c->pData,c->nRegs+nPis+nRegs+i) )
                Abc_InfoSetBit(d->pData,nRegs+Depth*nPis+i);
        if ( Saig_ManVerifyCex(pAig,d) ) *ppCex = d;
        else { Abc_Print(1,"Reverse counterexample verification FAILED.\n"); Abc_CexFree(d); Result = -1; }
    }
    else if ( Result == 0 ) Result = -1;
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1,"Reverse reachability: %s in %.3f sec.\n",Result == 1 ? "proved" : *ppCex ? "checked counterexample" : "undecided",(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Vec_PtrFree(vNext); Vec_IntFree(vInit); Aig_ManStop(pNew);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Merges registers with equal reset phases and identical signed drivers.]

  Description [Complementary drivers can share a register if their reset
  values are also complementary. The copy preserves all CI indices so
  that the following cone reduction can use its usual witness mapping.]

***********************************************************************/
static Aig_Man_t * Pdr2_StrideMergeRegs( Aig_Man_t * p, char * pInit, int * pCount )
{
    Vec_Ptr_t * vMap;
    Aig_Obj_t * pObj;
    Aig_Man_t * pNew = NULL;
    int i, Key, First, nPis = Saig_ManPiNum(p), * pRepr;
    *pCount = 0;
    if ( Aig_ManRegNum(p) < 2 || p->vFlopReprs || Aig_ManObjNumMax(p) > 1500000 ) return NULL;
    pRepr = ABC_FALLOC(int, 2*Aig_ManObjNumMax(p));
    vMap = Vec_PtrDup(p->vCis);
    Saig_ManForEachLi(p, pObj, i)
    {
        if ( pInit[i] == 2 ) continue;
        Key = Abc_Var2Lit(Aig_ObjFaninId0(pObj), pInit[i] ^ Aig_ObjFaninC0(pObj));
        First = pRepr[Key];
        if ( First < 0 ) pRepr[Key] = i;
        else
        {
            Vec_PtrWriteEntry(vMap, nPis+i, Aig_NotCond(Saig_ManLo(p, First), pInit[i] ^ pInit[First]));
            (*pCount)++;
        }
    }
    if ( *pCount ) pNew = Aig_ManRemap(p, vMap);
    ABC_FREE(pRepr); Vec_PtrFree(vMap);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns the image of a signed edge in a duplicated AIG.]

***********************************************************************/
static inline Aig_Obj_t * Pdr2_MuxImage( Aig_Obj_t ** pMap, Aig_Obj_t * pEdge )
{
    return Aig_NotCond(pMap[Aig_ObjId(Aig_Regular(pEdge))], Aig_IsComplement(pEdge));
}

/**Function*************************************************************

  Synopsis    [Rebuilds selected multiplexers from their positive product terms.]

  Description [A regular AIG multiplexer root is a product of two negated
  products. Rebuilding its positive sum of products preserves the full
  transition relation, all outputs, and the order of the interface.]

***********************************************************************/
static Aig_Man_t * Pdr2_ManMuxPhase( Aig_Man_t * p, Pdr2_Par_t * pPars, abctime Stop, int Mode, int * pfUseful )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pC, * pT, * pE, ** pMap;
    int i, fXor, nMux = 0, nXor = 0, nEqual = 0;
    if ( Mode < 1 || Mode > 3 || Aig_ManBufNum(p) || Aig_ManExorNum(p) ) return NULL;
    pNew = Aig_ManStart(Aig_ManNodeNum(p));
    pNew->pName = Abc_UtilStrsav(p->pName);
    pNew->pSpec = Abc_UtilStrsav(p->pSpec);
    pMap = ABC_ALLOC(Aig_Obj_t *, Aig_ManObjNumMax(p));
    pMap[Aig_ObjId(Aig_ManConst1(p))] = Aig_ManConst1(pNew);
    Aig_ManForEachCi(p, pObj, i)
        pMap[Aig_ObjId(pObj)] = Aig_ObjCreateCi(pNew);
    Aig_ManForEachNode(p, pObj, i)
    {
        if ( !(i & 4095) && ((Stop && Abc_Clock() >= Stop) ||
             (pPars && pPars->pFuncStop && pPars->pFuncStop(pPars->RunId))) ) goto skip;
        if ( Aig_ObjIsMuxType(pObj) )
        {
            pC = Aig_ObjRecognizeMux(pObj, &pT, &pE);
            fXor = pT == Aig_Not(pE);
            if ( Mode == 1 || Mode == (fXor ? 3 : 2) )
            {
                pT = Pdr2_MuxImage(pMap, pT);
                pE = Pdr2_MuxImage(pMap, pE);
                // Rewriting earlier gates can make the two data inputs equal.
                pMap[i] = pT == pE ? pT : Aig_Mux(pNew, Pdr2_MuxImage(pMap, pC), pT, pE);
                nEqual += pT == pE;
                nXor += fXor;
                nMux += !fXor;
                continue;
            }
        }
        pMap[i] = Aig_And(pNew, Pdr2_MuxImage(pMap, Aig_ObjChild0(pObj)),
            Pdr2_MuxImage(pMap, Aig_ObjChild1(pObj)));
    }
    if ( pfUseful )
    {
        *pfUseful = nEqual && 5 * (nMux + nXor) >= Aig_ManNodeNum(p) && 20 * nXor >= Aig_ManNodeNum(p);
        goto skip;
    }
    if ( !nMux && !nXor ) goto skip;
    Aig_ManForEachCo(p, pObj, i)
        Aig_ObjCreateCo(pNew, Pdr2_MuxImage(pMap, Aig_ObjChild0(pObj)));
    Aig_ManSetRegNum(pNew, Aig_ManRegNum(p));
    Aig_ManCleanup(pNew);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Multiplexer polarity: %d multiplexers and %d XORs, %d -> %d nodes.\n",
            nMux, nXor, Aig_ManNodeNum(p), Aig_ManNodeNum(pNew));
    ABC_FREE(pMap);
    return pNew;
skip:
    ABC_FREE(pMap);
    Aig_ManStop(pNew);
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Tests whether multiplexer rewriting collapses data inputs in a mux-rich circuit.]

***********************************************************************/
int Pdr2_ManHasMuxReduction( Aig_Man_t * p, Pdr2_Par_t * pPars, abctime Stop )
{
    int fUseful = 0;
    if ( Aig_ManRegNum(p) < 32 || Aig_ManRegNum(p) > 512 || Aig_ManNodeNum(p) > 25000 ||
         Aig_ManObjNumMax(p) > 100000 ) return 0;
    Pdr2_ManMuxPhase(p, pPars, Stop, 1, &fUseful);
    return fUseful;
}

int Pdr2_ManCheckedProbe( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int fStride )
{
    Abc_Cex_t * pCex = NULL;
    char * pInit = ABC_CALLOC( char, Aig_ManRegNum(pAig) + 1 );
    int i, Result;
    assert( !vInit || Vec_IntSize(vInit) == Aig_ManRegNum(pAig) );
    for ( i = 0; vInit && i < Vec_IntSize(vInit); i++ )
        pInit[i] = (char)Vec_IntEntry(vInit, i);
    if ( fStride && Gip_OptionGet("PDR2_STRIDE_REVERSE") && atoi(Gip_OptionGet("PDR2_STRIDE_REVERSE")) )
        Result = -1;
    else if ( fStride )
        Result = Pdr2_ManStride( pAig, pInit, pPars, pPars->timePolicyStop, &pCex );
    else
    {
        pPars->nBmcTime = pPars->nTimeOut;
        Result = Pdr2_ManBmcStage( pAig, pInit, pPars, pPars->timePolicyStop, &pCex );
        if ( Result != 0 ) Result = -1;
    }
    ABC_FREE( pInit );
    if ( Result == 0 && !pCex ) Result = -1;
    if ( Result == 0 )
    {
        Abc_CexFreeP( &pAig->pSeqModel );
        pAig->pSeqModel = pCex;
        pPars->iFrame = pCex->iFrame;
        pPars->fBmcDecided = !fStride;
    }
    else Abc_CexFreeP( &pCex );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Checks sequential safety with an explicit register reset vector.]

***********************************************************************/
static int Pdr2_ManSolveCore( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    static const char * const pRunNames[5] = { "dynamic generalization", "CTG generalization", "abstraction with dynamic generalization",
        "CTG generalization with weakening by simulation", "abstraction with CTG generalization" };
    Pdr2_Man_t * p = NULL, * pMan[5] = { NULL, NULL, NULL, NULL, NULL };
    Pdr2_Par_t Pars[5];
    Aig_Man_t * pAigUsed = pAig, * pAigGated = NULL, * pAigRun[5];
    Abc_Cex_t * pCex, * pCexBmc = NULL;
    abctime timeStart = Abc_Clock();
    abctime timeGlobal = pPars->nTimeOut ? timeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    double Budget[5];
    ABC_INT64_T PropsLeft = pPars->nPropLimit, PropsBefore;
    char RunName[5][80];
    char * pInit, * pInitGated = NULL, * pInitOrig = NULL;
    Vec_Int_t * vCoiPis = NULL, * vCoiRegs = NULL;
    int fGatedRun[5] = { 0, 0, 0, 0, 0 }, Order[5];
    const char * pRewrite = Gip_OptionGet("PDR2_REWRITE");
    int StridePrep = pPars->fStrideRun && Gip_OptionGet("PDR2_STRIDE_PREP") ?
        atoi(Gip_OptionGet("PDR2_STRIDE_PREP")) : 0;
    int fWallSlices = Gip_OptionGet("PDR2_WALLSLICES") && atoi(Gip_OptionGet("PDR2_WALLSLICES"));
    int Race = Gip_OptionGet("PDR2_RACE") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_RACE")))) : 0;
    int RacePreferred = 0, fSimTraceDone = 0, fKindPrefixDone = 0, fReverseDone = 0;
    int fRequireInv = pPars->fVerify && pPars->fVerifyComplete;
    double RaceSlice = Gip_OptionGet("PDR2_RACE_SLICE_MS") ?
        Abc_MaxInt(1, Abc_MinInt(60000, atoi(Gip_OptionGet("PDR2_RACE_SLICE_MS")))) / 1000.0 : 2.0;
    int RetValue = -1, fOrPos = 0, fPreproc = 0, fAlternate, nRuns, nAbsRuns, iPhase = 0, k = 0, j, fBmcDone = 0, fInitZero = 1, fExplicitDone = 0, fBddDone = 0, fSplitDone = 0, fShiftDone = 0, fStrideDone = 0, fPredDone = 0, fCombDone = 0;
    if ( pPars->timePolicyStop > 0 && (!timeGlobal || pPars->timePolicyStop < timeGlobal) )
        timeGlobal = pPars->timePolicyStop;
    Abc_CexFreeP( &pAig->pSeqModel );
    if ( (timeGlobal && timeStart >= timeGlobal) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
        return -1;
    if ( Gip_OptionGet("PDR2_PLAN") )
    {
        Pdr2_ManPrintPolicy(pAig, vInit, pPars->iSchedule == PDR2_SCHED_TUNED);
        return -1;
    }
    if ( Gip_OptionGet("PDR2_FEATURES") )
    {
        Pdr2_ManPrintFeatures(pAig);
        return -1;
    }
    if ( Gip_OptionGet("PDR2_PARAMS") )
    {
        Pdr2_ManPrintPolicyParams(pPars);
        return -1;
    }
    if ( Saig_ManConstrNum(pAig) > 0 )
    {
        if ( !pPars->fSilent )
            Abc_Print( 1, "Pdr2_ManSolve(): Constraints are not supported.\n" );
        return -1;
    }
    if ( vInit && Vec_IntSize(vInit) != Aig_ManRegNum(pAig) )
    {
        if ( !pPars->fSilent )
            Abc_Print( 1, "Pdr2_ManSolve(): The number of initial values (%d) differs from the number of flops (%d).\n", Vec_IntSize(vInit), Aig_ManRegNum(pAig) );
        return -1;
    }
    // the initial values (the flops of all the designs below come first, in the same order)
    pInit = ABC_CALLOC( char, Aig_ManRegNum(pAig) + 1 );
    for ( j = 0; vInit && j < Vec_IntSize(vInit); j++ )
    {
        if ( Vec_IntEntry(vInit, j) < 0 || Vec_IntEntry(vInit, j) > 2 )
        {
            if ( !pPars->fSilent )
                Abc_Print( 1, "Pdr2_ManSolve(): The initial value of flop %d is %d (expected 0, 1, or 2 for don't-care).\n", j, Vec_IntEntry(vInit, j) );
            ABC_FREE( pInit );
            return -1;
        }
        pInit[j] = (char)Vec_IntEntry( vInit, j );
        fInitZero &= pInit[j] == 0;
    }
    if ( pPars->iSchedule == PDR2_SCHED_CHECKED && fRequireInv && fInitZero && Saig_ManPoNum(pAig) == 1 &&
         !Aig_ManBufNum(pAig) && !Aig_ManExorNum(pAig) && Aig_ManRegNum(pAig) &&
         Aig_ManNodeNum(pAig) < 500000 && Aig_ManObjNumMax(pAig) <= 1000000 &&
         !pPars->fDumpInv && !pPars->nFrameMax && !pPars->nInitLiReg &&
         !pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun &&
         (!timeGlobal || timeGlobal - timeStart >= 4 * (abctime)CLOCKS_PER_SEC) )
    {
        int Result = Pdr2_ManSolvePolicy( pAig, vInit, pPars );
        if ( Result >= 0 || (pPars->nPropLimit && Result == -1) || (timeGlobal && Abc_Clock() >= timeGlobal) ||
             (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
        {
            ABC_FREE( pInit );
            return Result < 0 ? -1 : Result;
        }
    }
    if ( (pPars->iSchedule == PDR2_SCHED_TUNED || pPars->iSchedule == PDR2_SCHED_BASE) &&
         fInitZero && Saig_ManPoNum(pAig) == 1 && !Aig_ManBufNum(pAig) && !Aig_ManExorNum(pAig) &&
         !pPars->fDumpInv && !pPars->fVerifyComplete &&
         !pPars->nFrameMax && !pPars->nPropLimit && !pPars->nInitLiReg &&
         !pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun )
    {
        ABC_FREE( pInit );
        return Pdr2_ManSolvePolicy( pAig, vInit, pPars );
    }
    if ( pPars->nInitLiReg )
    {
        assert(pPars->nInitLiReg > 0 && pPars->nInitLiReg <= Aig_ManRegNum(pAig) && Saig_ManPoNum(pAig) == 1);
        goto init_runs;
    }
    if ( Saig_ManPoNum(pAig) != 1 )
    {
        pAigUsed = Saig_ManDupOrpos( pAig );
        fOrPos = 1;
    }
    // A completed invariant check uses the original latch interface.
    if ( fRequireInv ) goto init_runs;
    if ( (pPars->fPartRun || pPars->fShiftRun || (Gip_OptionGet("PDR2_COI") && atoi(Gip_OptionGet("PDR2_COI"))) ||
          (Gip_OptionGet("PDR2_RESET_COI") && !pPars->fDumpInv && !pPars->fVerifyComplete)) && !Aig_ManBufNum(pAigUsed) && !Aig_ManExorNum(pAigUsed) )
    {
        Aig_Man_t * pTemp, * pMerged = NULL, * pSource = pAigUsed;
        int i, Merged, nPisOld = Saig_ManPiNum(pAigUsed), nRegsOld = Aig_ManRegNum(pAigUsed);
        abctime clk = Abc_Clock();
        if ( StridePrep == 3 && !pPars->fDumpInv && !pPars->fVerifyComplete && !pPars->vPartCandidates )
            pMerged = Pdr2_StrideMergeRegs(pAigUsed, pInit, &Merged);
        if ( pMerged )
        {
            pSource = pMerged;
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print(1, "Stride register merging: %d equal or complementary next-state functions.\n", Merged);
        }
        if ( Gip_OptionGet("PDR2_RESET_COI") && !pPars->fDumpInv && !pPars->fVerifyComplete )
            pTemp = Pdr2_ManDupResetCoi(pSource, pInit, pPars, timeGlobal, &vCoiPis, &vCoiRegs);
        else pTemp = Pdr2_ManDupCoi( pSource, &vCoiPis, &vCoiRegs );
        if ( pMerged ) Aig_ManStop(pMerged);
        pInitOrig = pInit;
        pInit = ABC_CALLOC( char, Aig_ManRegNum(pTemp) + 1 );
        for ( i = 0; i < Aig_ManRegNum(pTemp); i++ )
        {
            assert( Vec_IntEntry(vCoiRegs, i) >= 0 );
            pInit[i] = pInitOrig[Vec_IntEntry(vCoiRegs, i)];
        }
        if ( pPars->fVerbose && !pPars->fSilent )
            Abc_Print( 1, "Sequential cone reduction: inputs %d -> %d, flops %d -> %d, nodes %d -> %d. Time = %.3f sec.\n",
                nPisOld, Saig_ManPiNum(pTemp), nRegsOld, Aig_ManRegNum(pTemp), Aig_ManNodeNum(pAigUsed), Aig_ManNodeNum(pTemp), (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC );
        if ( fOrPos ) Aig_ManStop( pAigUsed );
        pAigUsed = pTemp;
        fOrPos = fPreproc = 1;
    }
    // Safety-preserving active-path simplification. The original input and
    // register order is retained, so replay maps back as for preprocessing.
    // The existing preprocessing CEX path assumes zero initialization.
    if ( fInitZero )
    {
        Aig_Man_t * pTemp = Pdr2_ManStickyCofactor(pAigUsed, pPars, timeGlobal);
        if ( pTemp )
        {
            if ( fOrPos ) Aig_ManStop(pAigUsed);
            pAigUsed = pTemp; fOrPos = fPreproc = 1;
        }
    }
    if ( Gip_OptionGet("PDR2_MUX_PHASE") )
    {
        Aig_Man_t * pTemp = Pdr2_ManMuxPhase(pAigUsed, pPars, timeGlobal, atoi(Gip_OptionGet("PDR2_MUX_PHASE")), NULL);
        if ( pTemp )
        {
            if ( fOrPos ) Aig_ManStop(pAigUsed);
            pAigUsed = pTemp;
            fOrPos = 1;
        }
    }
    // In a grouped transition the cone maps preserve the original reset
    // vector and the chosen values of its don't-cares. Balancing and
    // combinational rewriting preserve the order and functions of the COs.
    if ( Aig_ManNodeNum(pAigUsed) && ((vCoiPis && (StridePrep == 1 || StridePrep == 2)) ||
         (fInitZero && pRewrite && atoi(pRewrite) > 0 &&
          ((!pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun) ||
           (Gip_OptionGet("PDR2_REWRITE_PART") && atoi(Gip_OptionGet("PDR2_REWRITE_PART")))))) )
    {
        Aig_Man_t * pTemp;
        abctime Start = Abc_Clock(), OldStop = pAigUsed->Time2Quit;
        abctime Stop = Start + (abctime)((StridePrep == 1 || StridePrep == 2) ? 8 : atoi(pRewrite))*CLOCKS_PER_SEC;
        if ( timeGlobal && Stop > timeGlobal ) Stop = timeGlobal;
        pAigUsed->Time2Quit = Stop;
        pTemp = StridePrep == 1 ? Dar_ManBalance(pAigUsed, 0) : Dar_ManRwsat(pAigUsed, 1, 0);
        pAigUsed->Time2Quit = OldStop;
        if ( pTemp )
        {
            assert(Aig_ManCiNum(pTemp) == Aig_ManCiNum(pAigUsed) &&
                   Aig_ManCoNum(pTemp) == Aig_ManCoNum(pAigUsed) &&
                   Aig_ManRegNum(pTemp) == Aig_ManRegNum(pAigUsed));
            pTemp->Time2Quit = 0;
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print(1,"Combinational rewriting: nodes %d -> %d, flops %d. Time = %.3f sec.\n",
                    Aig_ManNodeNum(pAigUsed), Aig_ManNodeNum(pTemp), Aig_ManRegNum(pTemp), (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
            if ( fOrPos ) Aig_ManStop(pAigUsed);
            pAigUsed = pTemp; fOrPos = fPreproc = 1;
        }
        else if ( pPars->fVerbose && !pPars->fSilent )
            Abc_Print(1,"Combinational rewriting reached its budget; original logic retained. Time = %.3f sec.\n",(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    }
    // Combinational SAT sweeping treats every register output as a free
    // input and every next-state function as an output. No sequential
    // assumption participates in an equivalence used for this reduction.
    if ( fInitZero && !pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun &&
         Gip_OptionGet("PDR2_FRAIG") && atoi(Gip_OptionGet("PDR2_FRAIG")) > 0 &&
         !Aig_ManBufNum(pAigUsed) && !Aig_ManExorNum(pAigUsed) && Aig_ManNodeNum(pAigUsed) <= 2000000 )
    {
        int nRegs = Aig_ManRegNum(pAigUsed), Cancelled = 0;
        abctime Start = Abc_Clock();
        Cec_ParFra_t Fra;
        Cec_ParLimit_t Limits = {0};
        Gia_Man_t * pGia, * pReduced;
        Aig_Man_t * pTemp = NULL;
        Limits.TimeToStop = Start+(abctime)Abc_MinInt(60,atoi(Gip_OptionGet("PDR2_FRAIG")))*CLOCKS_PER_SEC;
        if ( timeGlobal && timeGlobal < Limits.TimeToStop ) Limits.TimeToStop = timeGlobal;
        Limits.RunId = pPars->RunId; Limits.pFuncStop = pPars->pFuncStop; Limits.pCancelled = &Cancelled;
        Cec_ManFraSetDefaultParams(&Fra);
        Fra.pLimits = &Limits; Fra.fCheckMiter = Fra.fVerbose = 0;
        Fra.nItersMax = 2; Fra.nBTLimit = 100;
        pGia = Gia_ManFromAigSimple(pAigUsed);
        // Gia_ManSetRegNum initializes a combinational manager; clearing a
        // populated sequential count uses the count itself.
        pGia->nRegs = 0;
        pReduced = Cec_ManIsStopped(&Limits) ? NULL : Cec_ManSatSweeping(pGia,&Fra,1);
        if ( pReduced && Gia_ManCiNum(pReduced) == Aig_ManCiNum(pAigUsed) &&
             Gia_ManCoNum(pReduced) == Aig_ManCoNum(pAigUsed) )
        {
            Gia_ManSetRegNum(pReduced,nRegs);
            pTemp = Gia_ManToAigSimple(pReduced);
        }
        if ( pReduced ) Gia_ManStop(pReduced);
        Gia_ManStop(pGia);
        if ( pTemp )
        {
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print(1,"Combinational SAT sweeping: nodes %d -> %d, flops %d. Time = %.3f sec.\n",
                    Aig_ManNodeNum(pAigUsed),Aig_ManNodeNum(pTemp),nRegs,(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
            if ( fOrPos ) Aig_ManStop(pAigUsed);
            pAigUsed = pTemp; fOrPos = fPreproc = 1;
        }
    }
    if ( pPars->fPreproc && Aig_ManRegNum(pAigUsed) == 0 && pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Preprocessing (scorr) is skipped: the design has no registers.\n" );
    else if ( pPars->fPreproc && Saig_ManPiNum(pAigUsed) == 0 && pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Preprocessing (scorr) is skipped: the design has no primary inputs.\n" );
    else if ( pPars->fPreproc && !fInitZero && pPars->fVerbose && !pPars->fSilent )
        Abc_Print( 1, "Preprocessing (scorr) is skipped: it assumes that all initial values are 0.\n" );
    if ( pPars->fPreproc && Saig_ManPiNum(pAigUsed) > 0 && Aig_ManRegNum(pAigUsed) > 0 && fInitZero )
    {
        // sequentially equivalent simplification: the counterexample inputs carry over
        Ssw_Pars_t SswPars;
        Aig_Man_t * pTemp;
        int fLatchOnly = Gip_OptionGet("PDR2_LCORR") && atoi(Gip_OptionGet("PDR2_LCORR"));
        abctime clk = Abc_Clock();
        if ( fLatchOnly )
            Ssw_ManSetDefaultParamsLcorr( &SswPars );
        else
            Ssw_ManSetDefaultParams( &SswPars );
        SswPars.TimeLimit = pPars->nPreprocTime;
        if ( pPars->nTimeOut )
        {
            // the simplification cannot take more than what is left of the overall limit
            int Left = pPars->nTimeOut - (int)((Abc_Clock() - timeStart) / CLOCKS_PER_SEC);
            if ( SswPars.TimeLimit == 0 || SswPars.TimeLimit > Left )
                SswPars.TimeLimit = Abc_MaxInt( 1, Left );
        }
        pTemp = Ssw_SignalCorrespondence( pAigUsed, &SswPars );
        if ( pTemp )
        {
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print( 1, "Preprocessing (%s): flops %d -> %d, nodes %d -> %d.  Time = %.2f sec\n",
                    fLatchOnly ? "lcorr" : "scorr", Aig_ManRegNum(pAigUsed), Aig_ManRegNum(pTemp), Aig_ManNodeNum(pAigUsed), Aig_ManNodeNum(pTemp), (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
            if ( fOrPos )
                Aig_ManStop( pAigUsed );
            pAigUsed = pTemp;
            fOrPos = 1;
            fPreproc = 1;
        }
    }
    // Diagnostic survey: export the bounded preprocessing result without
    // allocating any PDR solver or spending time on subsequent proof queries.
    if ( Gip_OptionGet("PDR2_PREPROC_DUMP") && fInitZero )
    {
        Ioa_WriteAiger( pAigUsed, (char *)Gip_OptionGet("PDR2_PREPROC_DUMP"), 0, 0 );
        Abc_Print( 1, "Preprocessing survey: flops %d -> %d, nodes %d -> %d. Time = %.3f sec.\n",
            Aig_ManRegNum(pAig), Aig_ManRegNum(pAigUsed), Aig_ManNodeNum(pAig), Aig_ManNodeNum(pAigUsed),
            (double)(Abc_Clock() - timeStart) / CLOCKS_PER_SEC );
        if ( fOrPos ) Aig_ManStop( pAigUsed );
        ABC_FREE( pInit );
        ABC_FREE( pInitOrig );
        Vec_IntFreeP( &vCoiPis );
        Vec_IntFreeP( &vCoiRegs );
        return -1;
    }
init_runs:
    // the runs: 0 = dynamic generalization (optional, PDR2_DYNRUN), 1 = CTG generalization, 2 and 4 =
    // abstraction with dynamic and with CTG generalization (optional, -B), 3 = CTG generalization
    // with the weakening by simulation (optional, -V); with -t, runs 0 and 1
    // both use the abstraction (with different seeds): the trajectory of an abstraction run is
    // chaotic, and alternating two runs bounds the loss from an unlucky one
    fAlternate = pPars->fDynamic && pPars->nDynTime > 0;
    nAbsRuns = pPars->nAbsRuns;
    nRuns = 2;
    Order[0] = pPars->fDynFirst ? 0 : 1;
    Order[1] = pPars->fDynFirst ? 1 : 0;
    // the plain dynamic run is optional: it finished no IWLS example (300 s) and no mike4 example
    // (120 s) in the runs of October 20, its slices delaying the others by 4 of 36 nominal sec
    if ( !pPars->fDynRun && fAlternate && !pPars->fUseAbs )
        Order[0] = 1, nRuns = 1;
    if ( fAlternate && !pPars->fUseAbs && nAbsRuns > 0 )
        Order[nRuns++] = 2;
    if ( fAlternate && !pPars->fUseAbs && pPars->fSimRun )
        Order[nRuns++] = 3;
    if ( fAlternate && !pPars->fUseAbs && nAbsRuns > 1 )
        Order[nRuns++] = 4;
    if ( !fAlternate )
        nRuns = 1;
    if ( pPars->fPartRun || pPars->fShiftRun || pPars->fStrideRun || pPars->fPredRun ||
         pPars->fUseAbs || pPars->nPropLimit || pPars->nFrameMax ) Race = 0;
    if ( Race )
    {
        fAlternate = fWallSlices = 1;
        nRuns = 2; nAbsRuns = 0;
        Order[0] = 0; Order[1] = 1;
    }
    for ( k = 0; k < 5; k++ )
    {
        Pars[k] = *pPars;
        // Derive a nonnegative seed without signed overflow at the largest input seed.
        Pars[k].nRandomSeed = (int)(((unsigned)pPars->nRandomSeed + (unsigned)k) & 0x7fffffffu);
        pAigRun[k] = pAigUsed;
    }
    Pars[1].fDynamic = 0;
    Pars[2].fUseAbs = 1;
    Pars[2].nRandomSeed = pPars->nRandomSeed;  // the abstraction run behaves as -t does (its results are very seed-sensitive)
    Pars[2].fBlockInduct = 1;  // the abstraction run uses relative induction (as -t does by default)
    Pars[3].fDynamic = 0;
    Pars[3].nLiftSim = 2;
    Pars[3].nRandomSeed = Pars[1].nRandomSeed;  // the CTG run's seed, as in the runs that solved Ex41 and Ex02
    Pars[4].fUseAbs = 1;
    Pars[4].fDynamic = 0;
    Pars[4].fBlockInduct = 1;
    Pars[4].nRandomSeed = Pars[1].nRandomSeed;
    if ( Race )
    {
        Pars[0].fDynamic = Pars[1].fDynamic = 0;
        Pars[0].nRandomSeed = Pars[1].nRandomSeed = pPars->nRandomSeed;
        Pars[0].nInputPolicy = -1;
        Pars[1].nInputPolicy = 2;
    }
    // the abstraction runs work on the design with a reset flop (built when the first of them starts)
    if ( !fRequireInv && pPars->fAbsReset && pPars->fUseAbs )
        fGatedRun[0] = fGatedRun[1] = 1;
    if ( !fRequireInv && pPars->fAbsReset && fAlternate && !pPars->fUseAbs && nAbsRuns > 0 )
        fGatedRun[2] = fGatedRun[4] = 1;
    Budget[0] = pPars->fUseAbs ? Abc_MaxInt( 1, pPars->nAbsTime ) : pPars->nDynTime;
    Budget[1] = pPars->fUseAbs ? Abc_MaxInt( 1, pPars->nAbsTime ) : Abc_MaxInt( 1, pPars->nCtgTime );
    for ( k = 0; k < 5; k++ )
        snprintf( RunName[k], sizeof(RunName[k]), "%s%s", pRunNames[k], (k < 2 && Pars[k].fUseAbs) ? " with abstraction" : "" );
    Budget[2] = Abc_MaxInt( 1, pPars->nAbsTime );
    Budget[3] = Abc_MaxInt( 1, pPars->nAbsTime );
    Budget[4] = Abc_MaxInt( 1, pPars->nAbsTime );
    if ( Race )
    {
        Budget[0] = Budget[1] = RaceSlice;
        snprintf(RunName[0], sizeof(RunName[0]), "ordinary CTG");
        snprintf(RunName[1], sizeof(RunName[1]), "input-first CTG");
    }
    for ( iPhase = 0; ; iPhase++ )
    {
        k = fAlternate ? Order[iPhase % nRuns] : 0;
        if ( Race == 2 && iPhase >= 2 )
        {
            double Score[2] = {0, 0};
            for ( j = 0; j < 2; j++ )
                if ( pMan[j] && pMan[j]->fStarted )
                {
                    int Level = Pdr2_ManLevel(pMan[j]);
                    int Inf = Vec_PtrSize(pMan[j]->vInf);
                    int Last = Level > 0 ? Vec_PtrSize(Pdr2_ManFrame(pMan[j], Level)) : 0;
                    Score[j] = Level + (Level > 0 ? 0.9 * Inf / (Inf + Last + 1.0) : 0);
                }
            RacePreferred = Score[1] > Score[0] + 0.01;
            // Three longer slices follow the currently deeper proof. A
            // short probe of the other retained manager prevents permanent
            // starvation; every manager keeps its frames and learned clauses.
            k = (iPhase % 4 == 1) ? !RacePreferred : RacePreferred;
            if ( k != RacePreferred ) Budget[k] = RaceSlice;
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print(1, "PDR race progress: ordinary %.3f, inputs %.3f; selected %d.\n", Score[0], Score[1], k);
        }
        // These engines cannot supply the invariant required by a strict verification request.
        if ( !pPars->nInitLiReg && !fRequireInv )
        {
        if ( iPhase == 0 && (RetValue = Pdr2_ManCombSafe(pAigUsed, pPars, timeGlobal, NULL, NULL)) == 1 )
        {
            fBmcDone = fCombDone = 1;
            break;
        }
        if ( iPhase == 0 && !pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun &&
             ((RetValue = Pdr2_ManSimTrace(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 || Gip_OptionGet("PDR2_SIMTRACE_ONLY")) )
        {
            fBmcDone = RetValue != -1;
            fSimTraceDone = 1;
            break;
        }
        if ( iPhase == 0 && !pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun &&
             ((RetValue = Pdr2_ManKindPrefix(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 || Gip_OptionGet("PDR2_KIND_ONLY")) )
        {
            fBmcDone = RetValue != -1;
            fKindPrefixDone = 1;
            break;
        }
        if ( iPhase == 0 && !pPars->fPartRun && !pPars->fShiftRun && !pPars->fStrideRun && !pPars->fPredRun &&
             !(Gip_OptionGet("PDR2_STRIDE_REVERSE") && atoi(Gip_OptionGet("PDR2_STRIDE_REVERSE"))) &&
             ((RetValue = Pdr2_ManReverse(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 || Gip_OptionGet("PDR2_REVERSE_ONLY")) )
        {
            fBmcDone = RetValue != -1;
            fReverseDone = 1;
            break;
        }
        if ( iPhase == 0 && !pPars->fPartRun && pPars->fShiftRun <
             (Gip_OptionGet("PDR2_SHIFT_DEPTH") ? Abc_MaxInt(1, Abc_MinInt(4, atoi(Gip_OptionGet("PDR2_SHIFT_DEPTH")))) : 1) &&
             ((RetValue = Pdr2_ManShiftProperty(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 ||
              (!pPars->fShiftRun && Gip_OptionGet("PDR2_SHIFT_ONLY"))) )
        {
            fBmcDone = RetValue != -1;
            fShiftDone = 1;
            break;
        }
        // Bounded concrete preludes do not need any per-frame SAT managers.
        // They consume the same global deadline and use the common final
        // counterexample mapping/verification path.
        if ( iPhase == 0 && ((RetValue = Pdr2_ManPartBdd(pAigUsed, pInit, pPars, timeGlobal)) != -1 ||
             (Gip_OptionGet("PDR2_PARTBDD_ONLY") &&
              (!Gip_OptionGet("PDR2_PARTBDD_PART") || !atoi(Gip_OptionGet("PDR2_PARTBDD_PART")) || pPars->fPartRun))) )
        {
            fBmcDone = RetValue != -1;
            fBddDone = 1;
            break;
        }
        if ( iPhase == 0 && ((RetValue = Pdr2_ManBddSquare(pAigUsed, pInit, pPars, timeGlobal)) != -1 || Gip_OptionGet("PDR2_BDD_ONLY")) )
        {
            fBmcDone = RetValue != -1;
            fBddDone = 1;
            break;
        }
        if ( iPhase == 0 && ((RetValue = Pdr2_ManExplicitReach(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 || Gip_OptionGet("PDR2_EXPLICIT_ONLY")) )
        {
            fBmcDone = RetValue != -1;
            fExplicitDone = 1;
            break;
        }
        if ( iPhase == 0 && !pPars->nPropLimit && pPars->nFrameMax == 0 &&
             Gip_OptionGet("PDR2_BMCFIRST") && atoi(Gip_OptionGet("PDR2_BMCFIRST")) > 0 )
        {
            Pdr2_Par_t BmcPars = *pPars;
            BmcPars.nBmcTime = atoi(Gip_OptionGet("PDR2_BMCFIRST"));
            RetValue = Pdr2_ManBmcStage( pAigUsed, pInit, &BmcPars, timeGlobal, &pCexBmc );
            if ( RetValue != -1 || Gip_OptionGet("PDR2_BMC_ONLY") )
            {
                fBmcDone = RetValue != -1;
                break;
            }
        }
        if ( iPhase == 0 && !pPars->fPartRun &&
             ((RetValue = Pdr2_ManSplitProperty(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 || Gip_OptionGet("PDR2_SPLIT_ONLY")) )
        {
            fBmcDone = RetValue != -1;
            fSplitDone = 1;
            break;
        }
        if ( (timeGlobal && Abc_Clock() >= timeGlobal) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
            break;
        if ( iPhase == 0 && !pPars->fStrideRun &&
             ((RetValue = Pdr2_ManStride(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 ||
              (Gip_OptionGet("PDR2_STRIDE_ONLY") && (!Gip_OptionGet("PDR2_STRIDE_PART") || pPars->fPartRun))) )
        {
            fBmcDone = RetValue != -1;
            fStrideDone = 1;
            break;
        }
        }
        if ( pMan[k] == NULL )
        {
            if ( !pPars->nInitLiReg && !fRequireInv && iPhase == 0 && !pPars->fPredRun &&
                 ((RetValue = Pdr2_ManPredicates(pAigUsed, pInit, pPars, timeGlobal, &pCexBmc)) != -1 || Gip_OptionGet("PDR2_PRED_ONLY")) )
            {
                fBmcDone = RetValue != -1;
                fPredDone = 1;
                break;
            }
            if ( fGatedRun[k] )
            {
                if ( pAigGated == NULL )
                    pAigGated = Pdr2_ManDupGatedInit( pAigUsed, pInit, &pInitGated );
                pAigRun[k] = pAigGated;
            }
            pMan[k] = Pdr2_ManStart( pAigRun[k], fGatedRun[k] ? pInitGated : pInit, &Pars[k] );
            pMan[k]->timeStart  = timeStart;
            pMan[k]->timeGlobal = timeGlobal;
            pMan[k]->fAlternate = fAlternate && !Pars[k].fUseAbs;  // (the explosion trigger is for the plain dynamic run)
            if ( pPars->vPartCandidates && !fGatedRun[k] && !pPars->fPreproc &&
                 !pPars->fStrideRun && !pPars->fPredRun )
                Pdr2_ManImportPartCandidates(pMan[k], pPars->vPartCandidates, vCoiRegs, Aig_ManRegNum(pAig));
            if ( fGatedRun[k] )
            {
                pMan[k]->iResetFlop = pMan[k]->nRegs - 1;
                if ( pMan[k]->fAbsActive && !pMan[k]->pAbs[pMan[k]->iResetFlop] )
                {
                    pMan[k]->pAbs[pMan[k]->iResetFlop] = 1;
                    pMan[k]->nAbsFlops++;
                }
            }
        }
        p = pMan[k];
        if ( fAlternate )
        {
            // invariant lemmas are shared between the two plain runs only (the abstraction run encodes the initial state differently)
            if ( pPars->fShareInf && k < 2 && pMan[!k] )
                Pdr2_ManImportInf( p, pMan[!k] );
            // a slice ends after a budget of solver propagations (nominal seconds), not of time,
            // so that a run's trajectory does not depend on the machine load; only the global
            // deadline is a time limit
            p->timeLimit = timeGlobal;
            p->propSlice = (ABC_INT64_T)(Budget[k] * Pdr2_ManPropUnit(pPars));
            p->propLimit = p->nProps + p->propSlice;
            if ( fWallSlices )
            {
                abctime clkSlice = Abc_Clock();
                p->timeSlice = clkSlice + (abctime)(Budget[k] * CLOCKS_PER_SEC);
                p->timeSliceHard = clkSlice + (abctime)(2 * Budget[k] * CLOCKS_PER_SEC);
                p->propLimit = p->propSlice = 0;
            }
            p->fQueryCut = 0;
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print( 1, "Phase %d: %s for %.0f %s sec (resuming at level %d with %d inf lemmas).\n",
                    iPhase, RunName[k], Budget[k], fWallSlices ? "wall" : "nominal", p->fStarted ? Pdr2_ManLevel(p) : 0, Vec_PtrSize(p->vInf) );
        }
        else
            p->timeLimit = timeGlobal, p->propLimit = 0, p->propSlice = 0;
        // An enclosing abstraction loop can bound one invocation even in
        // non-alternating mode. Share the budget across scheduled managers.
        if ( pPars->nPropLimit > 0 && (!p->propSlice || PropsLeft < p->propSlice) )
            p->propSlice = PropsLeft, p->propLimit = p->nProps + PropsLeft;
        PropsBefore = p->nProps;
        RetValue = Pdr2_ManSolveInt( p );
        if ( RetValue == 1 && (p->fKindProved || p->fInitEmpty) ) fBmcDone = 1;
        if ( pPars->nPropLimit > 0 ) PropsLeft -= p->nProps - PropsBefore;
        if ( RetValue != -1 || !fAlternate )
            break;
        if ( pPars->nPropLimit > 0 && PropsLeft <= 0 )
            break;
        if ( (timeGlobal && Abc_Clock() >= timeGlobal) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
            break;
        if ( p->fExhausted )
            break;  // the frame limit ends the schedule (every run would stop at the same depth)
        Budget[k] *= 2;
        if ( Race && Budget[k] > 64 * RaceSlice ) Budget[k] = 64 * RaceSlice;
        // after the first slice (the examples that finish there pay nothing), a short BMC run
        // catches shallow counterexamples of designs on which every PDR frame is expensive
        if ( !pPars->nInitLiReg && !fRequireInv && iPhase == 0 && !pPars->nPropLimit && pPars->nBmcTime > 0 && pPars->nFrameMax == 0 && (RetValue = Pdr2_ManBmcStage( pAigUsed, pInit, pPars, timeGlobal, &pCexBmc )) != -1 )
        {
            fBmcDone = 1;
            break;
        }
        // BMC may itself have observed cancellation. Do not allocate the
        // next scheduled manager after the enclosing run has been retired.
        if ( (timeGlobal && Abc_Clock() >= timeGlobal) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
            break;
    }
    pPars->iFrame = pCexBmc ? pCexBmc->iFrame : p && p->fStarted ? Pdr2_ManLevel( p ) : 0;
    pPars->nPhasesRun = iPhase + 1;
    pPars->nRestartsRun = 0;
    pPars->fBmcDecided = fBmcDone;
    // Cancellation retires unfinished search, not an answer already found.
    // Counterexamples still undergo simulation below; requested invariant
    // verification remains cancellable and must complete when required.
    for ( j = 0; j < 5; j++ )
        if ( pMan[j] )
            pPars->nRestartsRun += pMan[j]->nLevelRestarts;
    if ( RetValue == 0 )
    {
        pCex = pCexBmc ? pCexBmc : Pdr2_ManDeriveCex( p );
        if ( (fGatedRun[k] && !pCexBmc) || fPreproc )
        {
            // the counterexample refers to the transformed design, which has the same
            // primary inputs: keep the input sequence; the initial state takes the defined
            // initial values and, for the don't-care flops (only in the gated design, whose
            // first flops are those of the design), the values chosen by the run
            Abc_Cex_t * pCexOrig;
            if ( vCoiPis )
            {
                int f, i, Orig;
                assert( pCex->nPis == Vec_IntSize(vCoiPis) );
                pCexOrig = Abc_CexAlloc( Aig_ManRegNum(pAig), Saig_ManPiNum(pAig), pCex->iFrame+1 );
                pCexOrig->iFrame = pCex->iFrame;
                pCexOrig->iPo = pCex->iPo;
                for ( f = 0; f <= pCex->iFrame; f++ )
                    Vec_IntForEachEntry( vCoiPis, Orig, i )
                    {
                        assert( Orig >= 0 );
                        if ( Abc_InfoHasBit(pCex->pData, pCex->nRegs + f*pCex->nPis + i) )
                            Abc_InfoSetBit( pCexOrig->pData, pCexOrig->nRegs + f*pCexOrig->nPis + Orig );
                    }
                for ( j = 0; j < Aig_ManRegNum(pAig); j++ )
                    if ( pInitOrig[j] == 1 ) Abc_InfoSetBit( pCexOrig->pData, j );
                // Signal correspondence is skipped for nonzero/don't-care
                // initial values, so this register map remains exact.
                Vec_IntForEachEntry( vCoiRegs, Orig, i )
                    if ( pInitOrig[Orig] == 2 && Abc_InfoHasBit(pCex->pData, i) )
                        Abc_InfoSetBit( pCexOrig->pData, Orig );
            }
            else
            {
                pCexOrig = Abc_CexDup( pCex, Aig_ManRegNum(pAig) );
                for ( j = 0; j < Aig_ManRegNum(pAig); j++ )
                    if ( pInit[j] == 2 ? fGatedRun[k] && Abc_InfoHasBit(pCex->pData, j) : pInit[j] == 1 )
                        Abc_InfoSetBit( pCexOrig->pData, j );
            }
            Abc_CexFree( pCex );
            pCex = pCexOrig;
        }
        if ( Saig_ManPoNum(pAig) != 1 )
            pCex->iPo = Saig_ManFindFailedPoCex( pAig, pCex );
        // the trace must start in an initial state (the simulation takes any register values)
        for ( j = 0; j < Aig_ManRegNum(pAig); j++ )
            if ( (pInitOrig ? pInitOrig[j] : pInit[j]) != 2 &&
                 Abc_InfoHasBit(pCex->pData, j) != (pInitOrig ? pInitOrig[j] : pInit[j]) )
                break;
        if ( p && p->fInitUnknown )
        {
            Abc_CexFree(pCex); RetValue = -1;
        }
        else if ( j < Aig_ManRegNum(pAig) )
        {
            if ( !pPars->fSilent )
                Abc_Print( 1, "Pdr2_ManSolve(): The counterexample does not start in an initial state (flop %d).\n", j );
            Abc_CexFree( pCex );
            RetValue = -1;
        }
        else if ( !Saig_ManVerifyCex( pAig, pCex ) )
        {
            if ( !pPars->fSilent )
                Abc_Print( 1, "Pdr2_ManSolve(): Counterexample verification has FAILED.\n" );
            Abc_CexFree( pCex );
            RetValue = -1;
        }
        else
        {
            ABC_FREE( pAig->pSeqModel );
            pAig->pSeqModel = pCex;
        }
    }
    else if ( RetValue == 1 && fBmcDone )
    {
        // With no initial states the false invariant is inductive. Check its initiation independently.
        if ( fRequireInv )
        {
            RetValue = -1;
            if ( p && p->fInitEmpty )
            {
                Gip_Solver_t * pCheck = Pdr2_ManNewSolver(p, 1);
                pCheck->TimeLimit = p->timeGlobal;
                if ( Gip_SolverSolve(pCheck, NULL, 0, NULL, NULL, 0, -1) == GIP_UNSAT ) RetValue = 1;
                Gip_SolverFree(pCheck);
            }
        }
        // An exhaustive reachability proof leaves no PDR invariant.
        if ( RetValue == 1 && pPars->fDumpInv && !pPars->fSilent )
            Abc_Print( 1, "The property was proved by %s; there is no single PDR invariant to dump.\n", p && p->fInitEmpty ? "empty initial-state predicate" : p && p->fKindProved ? "k-induction with a PDR-verified base" : fCombDone ? "combinational safety" : fPredDone ? "state predicate extension" : fStrideDone ? "transition grouping" : fShiftDone ? "property lookahead" : fSplitDone ? "property decomposition" : fBddDone ? "BDD reachability" : fExplicitDone ? "explicit reachability" : "BMC" );
    }
    else if ( RetValue == 1 )
    {
        int Verify = pPars->fVerify ? Pdr2_ManVerifyInvariant( p ) : 1;
        // Preserve standalone proofs if only the optional invariant check
        // reaches its deadline. Embedding callers can require a completed
        // check; an explicit cancellation still retires an incomplete one.
        if ( Verify == 0 || (Verify < 0 && (pPars->fVerifyComplete ||
             (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)))) )
        {
            if ( Verify == 0 && !pPars->fSilent )
                Abc_Print( 1, "Pdr2_ManSolve(): Invariant verification has FAILED.\n" );
            RetValue = -1;
        }
        // the invariant is over the flops of the solved design (gated or preprocessed for some runs)
        if ( pPars->fDumpInv && RetValue == 1 )
            Pdr2_ManDumpInvariant( p, fGatedRun[k] || fPreproc );
    }
    if ( pPars->fVerbose && !pPars->fSilent )
    {
        if ( fCombDone )
            Abc_Print( 1, "Finished by combinational safety.\n" );
        else if ( fPredDone )
            Abc_Print( 1, "Finished by state predicate extension.\n" );
        else if ( fStrideDone )
            Abc_Print( 1, "Finished by transition grouping.\n" );
        else if ( fShiftDone )
            Abc_Print( 1, "Finished by property lookahead.\n" );
        else if ( fSplitDone )
            Abc_Print( 1, "Finished by property decomposition.\n" );
        else if ( fBddDone )
            Abc_Print( 1, "Finished by BDD reachability.\n" );
        else if ( fExplicitDone )
            Abc_Print( 1, "Finished by explicit reachability.\n" );
        else if ( fSimTraceDone )
            Abc_Print(1, "Finished by concrete simulation.\n");
        else if ( fReverseDone )
            Abc_Print(1,"Finished by reverse reachability.\n");
        else if ( fKindPrefixDone )
            Abc_Print(1, "Finished by k-induction with a BMC-verified base.\n");
        else if ( p && p->fKindProved )
            Abc_Print(1, "Finished by k-induction with a PDR-verified base.\n");
        else if ( p && p->fInitEmpty )
            Abc_Print(1,"Finished by proving the initial-state predicate empty.\n");
        else if ( fBmcDone )
            Abc_Print( 1, "Finished by the BMC stage %s phase 0.\n", p ? "after" : "before" );
        else if ( fAlternate )
            Abc_Print( 1, "Finished in phase %d (%s); statistics of this run:\n", iPhase, RunName[k] );
        if ( p && p->fStarted ) Pdr2_ManPrintStats( p );
        if ( fAlternate )
        {
            ABC_INT64_T nPropsAll = 0;
            for ( j = 0; j < 5; j++ )
                if ( pMan[j] )
                    nPropsAll += pMan[j]->nProps;
            Abc_Print( 1, "Solver propagations in all runs = %.1f M.\n", nPropsAll / 1e6 );
            // the slices are equal in propagations, not in time: the time of each run
            for ( j = 0; j < 5; j++ )
                if ( pMan[j] )
                    Abc_Print( 1, "Run %d (%s): %.2f sec, %.1f M propagations, MIC %.2f sec, lifting %.2f sec (simulation %.2f sec), abstraction %.2f sec.\n",
                        j, RunName[j], (double)pMan[j]->timeRun / CLOCKS_PER_SEC, pMan[j]->nProps / 1e6, (double)pMan[j]->timeMic / CLOCKS_PER_SEC,
                        (double)pMan[j]->timeLift / CLOCKS_PER_SEC, (double)pMan[j]->timeLiftSim / CLOCKS_PER_SEC, (double)pMan[j]->timeAbs / CLOCKS_PER_SEC );
        }
    }
    for ( j = 0; j < 5; j++ )
        if ( pMan[j] )
        {
            if ( pPars->vPartCandidates && !fGatedRun[j] && !pPars->fPreproc &&
                 !pPars->fStrideRun && !pPars->fPredRun )
                Pdr2_ManExportPartCandidates(pMan[j], pPars->vPartCandidates, vCoiRegs);
            Pdr2_ManStop( pMan[j] );
        }
    if ( pAigGated )
        Aig_ManStop( pAigGated );
    if ( fOrPos )
        Aig_ManStop( pAigUsed );
    ABC_FREE( pInitGated );
    ABC_FREE( pInit );
    ABC_FREE( pInitOrig );
    Vec_IntFreeP( &vCoiPis );
    Vec_IntFreeP( &vCoiRegs );
    return RetValue;
}

int Pdr2_ManSolveInit( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    const char * pKeys[] = { "PDR2_WATCH_PACK", "PDR2_WATCH_AHEAD", "PDR2_DROP_HISTORY" };
    const char * pValues[] = { "1", "4", "4" };
    Gip_Options_t Options;
    int Result, Schedule = pPars->iSchedule;
    int fTunedDirect = Schedule == PDR2_SCHED_TUNED_DIRECT || Schedule == PDR2_SCHED_CHECKED ||
                       (Schedule == PDR2_SCHED_TUNED && pPars->fVerifyComplete);
    if ( !fTunedDirect && !pPars->pOptions )
        return Pdr2_ManSolveCore( pAig, vInit, pPars );
    memset( &Options, 0, sizeof(Options) );
    Options.nOptions = fTunedDirect ? 3 : 0;
    Options.pKeys = pKeys;
    Options.pValues = pValues;
    Options.pOverrides = pPars->pOptions;
    Gip_OptionsPush( &Options );
    if ( Schedule == PDR2_SCHED_TUNED && pPars->fVerify && pPars->fVerifyComplete )
        pPars->iSchedule = PDR2_SCHED_CHECKED;
    else if ( fTunedDirect && Schedule != PDR2_SCHED_CHECKED )
        pPars->iSchedule = PDR2_SCHED_DIRECT;
    Result = Pdr2_ManSolveCore( pAig, vInit, pPars );
    pPars->iSchedule = Schedule;
    Gip_OptionsPop( &Options );
    return Result;
}

int Pdr2_ManSolveAbstraction( Aig_Man_t * pAig, Pdr2_Par_t * pPars )
{
    Pdr2_Par_t Probe = *pPars;
    abctime Start = Abc_Clock(), ProbeStop = Start + 3 * (abctime)CLOCKS_PER_SEC;
    abctime Deadline = pPars->nTimeOut ? Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    abctime Saved = pPars->timePolicyStop;
    int Result;
    if ( Saved > 0 && (!Deadline || Saved < Deadline) ) Deadline = Saved;
    if ( Deadline && Deadline < ProbeStop ) ProbeStop = Deadline;
    Probe.iSchedule = PDR2_SCHED_TUNED_DIRECT;
    Probe.fDynamic = 0;
    Probe.nLiftSim = 2;
    Probe.nMicMode = Probe.fBlockInduct = 1;
    Probe.timePolicyStop = ProbeStop;
    Result = Pdr2_ManSolve( pAig, &Probe );
    if ( Result < 0 && !pPars->nPropLimit && (!Deadline || ProbeStop < Deadline) &&
         (!pPars->pFuncStop || !pPars->pFuncStop(pPars->RunId)) )
    {
        pPars->timePolicyStop = Deadline;
        Result = Pdr2_ManSolve( pAig, pPars );
        pPars->timePolicyStop = Saved;
        pPars->nPhasesRun += Probe.nPhasesRun;
        pPars->nRestartsRun += Probe.nRestartsRun;
    }
    else
    {
        pPars->iFrame = Probe.iFrame;
        pPars->nPhasesRun = Probe.nPhasesRun;
        pPars->nRestartsRun = Probe.nRestartsRun;
        pPars->fBmcDecided = Probe.fBmcDecided;
    }
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
