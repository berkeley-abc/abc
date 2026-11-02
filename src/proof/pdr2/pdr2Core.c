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

#include <math.h>
#include "pdr2Int.h"
#include "proof/ssw/ssw.h"
#include "sat/bmc/bmc.h"

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
    pPars->nFrameMax     =       0;  // limit on frame count
    pPars->nTimeOut      =       0;  // timeout in seconds
    pPars->nRandomSeed   =       0;  // random seed
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
    pPars->fTimeGen      =       getenv("PDR2_TIMEGEN") ? atoi(getenv("PDR2_TIMEGEN")) : 2;  // time generalization
    pPars->fSemContain   =       0;  // semantic containment check
    pPars->fKeepObl      =       1;  // keep obligations beyond the frontier
    pPars->nQueueOrder   =       1;  // treb's order: shortest cube first, newest first
    pPars->nCtgMax       =       3;  // max CTGs per literal
    pPars->nCtgLimit     =       1;
    pPars->fCtgMic       =       1;  // generalize CTG-blocking lemmas
    pPars->fDropPo       =       1;  // drop failing obligations
    pPars->nDropAct      =      20;  // dropping threshold
    pPars->nDynDropAct   =       0;  // dropping threshold in dynamic mode (0 = never)
    pPars->fParentLemma  =       1;  // parent lemma ordering
    pPars->fLift         =       1;  // flip-to-none lifting
    pPars->fPropHyp      =       1;
    pPars->fBlockInduct  =       0;  // relative induction in the blocking query  // property as inductive hypothesis
    pPars->fCtiCache     =       1;  // cache counterexamples to propagation
    pPars->fUseAbs       =       0;  // localization abstraction
    pPars->nAbsStart     =       0;  // abstraction start time
    pPars->fAbsCleanup   =       1;  // abstraction cleanup
    pPars->fAbsRefineAll =       0;  // refine with all pseudo-inputs
    pPars->fAbsReset     =       1;  // reset-flop gating with the abstraction
    pPars->fAbsRefineXsim=       1;  // X-simulation refinement
    pPars->nAbsRefineMode=       0;  // refinement variant (see pdr2.h)
    pPars->nAbsRuns      =       2;  // abstraction runs added to the alternating schedule
    pPars->fDynRun       =       getenv("PDR2_DYNRUN") ? atoi(getenv("PDR2_DYNRUN")) : 0;  // plain dynamic run (finished 0 of 76 IWLS and 0 of 111 mike4 examples)
    pPars->fSimRun       =       0;  // weakening by simulation as another alternating run
    pPars->nBmcTime      =       getenv("PDR2_BMC") ? atoi(getenv("PDR2_BMC")) : 2;  // BMC stage after the first slice
    pPars->nAbsTime      =       8;  // first budget of the abstraction phases
    pPars->fTopCtg       =       0;  // CTG for top-level obligations (was unreachable in the measured runs)
    pPars->fInfPromote   =       0;  // immediate promotion to frame infinity
    pPars->nMicMode      =       0;  // generalization procedure
    pPars->nLiftIters    =       0;  // lifting iterations
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
            if ( Vec_IntEntry(vOwner, pLem->Id) >= 0 && p->nIdShared++ == 0 )
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
        RetValue = Pdr2_ManSolveRelative( p, Pdr2_ManSolver(p, i-1), vCube, 1, NULL );
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
                break;
            }
        if ( fFail )
            break;
        Vec_IntClear( vOrd );
        Vec_IntAppend( vOrd, vCur );
        Pdr2_ManSortByAct( p, vOrd, 0 );
        nTries++;
        p->nDownQueries++;
        RetValue = Pdr2_ManSolveRelative( p, pSat, vOrd, 1, vCst );
        if ( RetValue == -1 )
            break;
        if ( RetValue == 1 )
        {
            if ( Pdr2_ManInductiveCore( p, pSat, vOut ) )
                Result = 1, p->nDownJoined += nTries > 1;
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
            else if ( Value == GIP_TRUE && !Gip_SolverFlipToNone( pSat, p->pLoVar[Abc_Lit2Var(Lit)] ) )
                Vec_IntPush( vTmp, Lit );
        }
        Vec_IntClear( vCur );
        Vec_IntAppend( vCur, vTmp );
        // record the counterexample to induction (predecessor, successor); the predecessor keeps
        // the assignments that stay necessary after the others are flipped to none (any completion
        // of it is a predecessor of the successor)
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vFull, Lit, i )
        {
            Var = p->pLoVar[Abc_Lit2Var(Lit)];
            Value = pSat->pValue[Var];
            if ( Value != GIP_NONE && !Gip_SolverFlipToNone( pSat, Var ) )
                Vec_IntPush( vTmp, Abc_Var2Lit(Abc_Lit2Var(Lit), Value == GIP_FALSE) );
        }
        Vec_PtrPush( vCexS, Pdr2_CubeAllocVec( vTmp ) );
        Vec_IntClear( vTmp );
        Vec_IntForEachEntry( vFull, Lit, i )
        {
            Value = pSat->pValue[p->pLiVar[Abc_Lit2Var(Lit)]];
            if ( Value != GIP_NONE )
                Vec_IntPush( vTmp, Abc_Var2Lit(Abc_Lit2Var(Lit), Value == GIP_FALSE) );
        }
        Vec_PtrPush( vCexT, Pdr2_CubeAllocVec( vTmp ) );
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
        RetValue = Pdr2_ManSolveRelative( p, pSat, vOrd, 1, vCst );
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
        Vec_IntClear( vOrd );
        Vec_IntAppend( vOrd, vCur );
        Pdr2_ManSortByAct( p, vOrd, 0 );
        RetValue = Pdr2_ManSolveRelative( p, pSat, vOrd, 1, NULL );
        if ( RetValue == -1 )
            break;
        if ( RetValue == 1 )
        {
            if ( Pdr2_ManInductiveCore( p, pSat, vOut ) )
                Result = 1;
            break;
        }
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
            Pdr2_ManUnsetMicDomain( p, pSat );
            fFail = Pdr2_ManTrivialBlock( p, iFrame - 1, vPred, vCst, SubPar );
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
    int i, k, Lit, iNew;
    p->nMicNest++;
    // the flags are reused by recursion depth (a CTG may be generalized inside a down) and are
    // zero between calls: pMark is cleared where it is used, pKeep over the initial literals
    if ( Vec_PtrSize(p->vMicScratch) == p->nMicDepth )
        Vec_PtrPush( p->vMicScratch, ABC_CALLOC( char, 4 * p->nRegs ) );
    pKeep = (char *)Vec_PtrEntry( p->vMicScratch, p->nMicDepth++ );
    pMark = pKeep + 2 * p->nRegs;
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
        Lit = Vec_IntEntry( vCube, i );
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
        if ( Par.nLevel == 0 )
            fOk = Pdr2_ManDown( p, iFrame, vRemoved, pKeep, vFull, vCst, vCexS, vCexT, vNew );
        else
            fOk = Pdr2_ManCtgDown( p, iFrame, vRemoved, pKeep, vFull, Par, vNew );
        if ( fOk )
        {
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
            Pdr2_ManUnsetMicDomain( p, pSat );
            Pdr2_ManSetMicDomain( p, pSat, vCube );
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
        }
    }
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
    int n = Vec_IntSize( vOrder ), i = 0, iLast = 0, Count, Lit, Lit2, k, RetValue;
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
                    RetValue = Pdr2_ManSolveRelative( p, pSat, vTry, 1, NULL );
                    if ( RetValue == 1 && Pdr2_ManInductiveCore( p, pSat, vCore ) )
                    {
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

  Synopsis    [Generalizes a blocked obligation into a lemma.]

  Description [Returns 1 if an inductive invariant was found.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManGeneralize( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, pObl->iFrame - 1 );
    Vec_Int_t * vMic = Vec_IntAlloc( 100 );
    Pdr2_MicPar_t Par;
    int iFrame, RetValue;
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
    if ( p->pPars->nMicMode == 1 )
        Pdr2_ManMicTreb( p, pObl->iFrame, vMic );
    else
        Pdr2_ManMic( p, pObl->iFrame, vMic, NULL, Par );
    iFrame = Pdr2_ManPushLemma( p, pObl->iFrame, vMic );
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
            k = Pdr2_ManSolveRelative( p, p->pInf, vMic, 1, NULL );
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
            if ( p->pPars->fVerbose )
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
            if ( p->pPars->fVerbose )
                Abc_Print( 1, "Ending the dynamic phase at level %d (%d obligations at this level).\n", Pdr2_ManLevel(p), p->nOblsLevel );
            Pdr2_QueuePush( p, pObl );
            Pdr2_OblDeref( pObl );
            Result = PDR2_BLOCK_RESTART;
            break;
        }
        // an obligation containing an initial state is a counterexample (if it is not spurious)
        if ( Pdr2_CubeIsInit(p, pObl->pState) )
        {
            RetValue = p->fAbsActive ? Pdr2_ManAbsCheckCex( p, pObl ) : 1;
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
        RetValue = Pdr2_ManSolveRelative( p, Pdr2_ManSolver(p, pObl->iFrame - 1), p->vLits4, p->pPars->fBlockInduct, NULL );
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
static int Pdr2_ManPropagate( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vSnap = Vec_PtrAlloc( 1000 );
    Vec_Int_t * vCore = Vec_IntAlloc( 100 );
    Vec_Ptr_t * vFrame;
    Pdr2_Lem_t * pLem;
    abctime clk = Abc_Clock();
    int k, i, RetValue, Result = 0, Level = Pdr2_ManLevel(p);
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
            Pdr2_CubeToVec( pLem->pCube, p->vLits4 );
            Pdr2_ManSortByAct( p, p->vLits4, 0 );
            p->nPropCalls++;
            RetValue = Pdr2_ManSolveRelative( p, Pdr2_ManSolver(p, k), p->vLits4, 0, NULL );
            if ( RetValue == -1 )
            {
                p->fSweepCut = 1;
                goto finish;
            }
            if ( RetValue == 0 )
            {
                if ( p->pPars->fCtiCache )
                    Pdr2_LemCacheCti( p, pLem, Pdr2_ManSolver(p, k), k );
                continue;
            }
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
        RetValue = Pdr2_ManSolveRelative( p, p->pInf, vLits, 1, NULL );
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
            RetValue = Pdr2_ManSolveRelative( p, p->pInf, vLits, 1, NULL );
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

  Synopsis    [The main loop.]

  Description [Returns 1 if the property holds, 0 if it fails (the
  counterexample obligation chain is in p->pCexObl), -1 if undecided.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManSolveInt( Pdr2_Man_t * p )
{
    Vec_Int_t * vPred = Vec_IntAlloc( 100 );
    Vec_Int_t * vInputs = Vec_IntAlloc( 100 );
    Vec_Int_t * vPpis = Vec_IntAlloc( 100 );
    Pdr2_Cube_t * pCube;
    Pdr2_Obl_t * pObl;
    abctime clk, clkRun = Abc_Clock();
    int RetValue, Result = -1;
    if ( !p->fStarted )
    {
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
    if ( Result == -1 && p->timeGlobal && Abc_Clock() > p->timeGlobal && !p->pPars->fSilent )
        Abc_Print( 1, "Reached timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOut, Pdr2_ManLevel(p) );
    p->timeRun += Abc_Clock() - clkRun;
    Vec_IntFree( vPred );
    Vec_IntFree( vInputs );
    Vec_IntFree( vPpis );
    return Result;
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
    Pars.fSilent  = 1;
    RetValue = Saig_ManBmcScalable( pAig, &Pars );
    if ( RetValue == 0 && pAig->pSeqModel )
    {
        pCex = pAig->pSeqModel;
        pAig->pSeqModel = NULL;
    }
    else if ( RetValue == 0 )
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
    if ( pPars->fVerbose )
        Abc_Print( 1, "BMC stage (%d sec): %s at frame %d.  Time = %.2f sec\n", nTime,
            pCex ? "counterexample" : RetValue == 1 ? "all reachable states visited" : "no counterexample",
            pCex ? pCex->iFrame : Pars.iFrame, (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
    *ppCex = pCex;
    return RetValue;
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
int Pdr2_ManSolveInit( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    static const char * pRunNames[5] = { "dynamic generalization", "CTG generalization", "abstraction with dynamic generalization",
        "CTG generalization with weakening by simulation", "abstraction with CTG generalization" };
    Pdr2_Man_t * p = NULL, * pMan[5] = { NULL, NULL, NULL, NULL, NULL };
    Pdr2_Par_t Pars[5];
    Aig_Man_t * pAigUsed = pAig, * pAigGated = NULL, * pAigRun[5];
    Abc_Cex_t * pCex, * pCexBmc = NULL;
    abctime timeStart = Abc_Clock();
    abctime timeGlobal = pPars->nTimeOut ? timeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    double Budget[5];
    char RunName[5][80];
    char * pInit, * pInitGated = NULL;
    int fGatedRun[5] = { 0, 0, 0, 0, 0 }, Order[5];
    int RetValue = -1, fOrPos = 0, fPreproc = 0, fAlternate, nRuns, nAbsRuns, iPhase = 0, k = 0, j, fBmcDone = 0, fInitZero = 1;
    if ( Saig_ManConstrNum(pAig) > 0 )
    {
        Abc_Print( 1, "Pdr2_ManSolve(): Constraints are not supported.\n" );
        return -1;
    }
    if ( vInit && Vec_IntSize(vInit) != Aig_ManRegNum(pAig) )
    {
        Abc_Print( 1, "Pdr2_ManSolve(): The number of initial values (%d) differs from the number of flops (%d).\n", Vec_IntSize(vInit), Aig_ManRegNum(pAig) );
        return -1;
    }
    // the initial values (the flops of all the designs below come first, in the same order)
    pInit = ABC_CALLOC( char, Aig_ManRegNum(pAig) + 1 );
    for ( j = 0; vInit && j < Vec_IntSize(vInit); j++ )
    {
        if ( Vec_IntEntry(vInit, j) < 0 || Vec_IntEntry(vInit, j) > 2 )
        {
            Abc_Print( 1, "Pdr2_ManSolve(): The initial value of flop %d is %d (expected 0, 1, or 2 for don't-care).\n", j, Vec_IntEntry(vInit, j) );
            ABC_FREE( pInit );
            return -1;
        }
        pInit[j] = (char)Vec_IntEntry( vInit, j );
        fInitZero &= pInit[j] == 0;
    }
    if ( Saig_ManPoNum(pAig) != 1 )
    {
        pAigUsed = Saig_ManDupOrpos( pAig );
        fOrPos = 1;
    }
    if ( pPars->fPreproc && Saig_ManPiNum(pAigUsed) == 0 && pPars->fVerbose )
        Abc_Print( 1, "Preprocessing (scorr) is skipped: the design has no primary inputs.\n" );
    else if ( pPars->fPreproc && !fInitZero && pPars->fVerbose )
        Abc_Print( 1, "Preprocessing (scorr) is skipped: it assumes that all initial values are 0.\n" );
    if ( pPars->fPreproc && Saig_ManPiNum(pAigUsed) > 0 && fInitZero )
    {
        // sequentially equivalent simplification: the counterexample inputs carry over
        Ssw_Pars_t SswPars;
        Aig_Man_t * pTemp;
        abctime clk = Abc_Clock();
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
            if ( pPars->fVerbose )
                Abc_Print( 1, "Preprocessing (scorr): flops %d -> %d, nodes %d -> %d.  Time = %.2f sec\n",
                    Aig_ManRegNum(pAigUsed), Aig_ManRegNum(pTemp), Aig_ManNodeNum(pAigUsed), Aig_ManNodeNum(pTemp), (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
            if ( fOrPos )
                Aig_ManStop( pAigUsed );
            pAigUsed = pTemp;
            fOrPos = 1;
            fPreproc = 1;
        }
    }
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
    // the abstraction runs work on the design with a reset flop (built when the first of them starts)
    if ( pPars->fAbsReset && pPars->fUseAbs )
        fGatedRun[0] = fGatedRun[1] = 1;
    if ( pPars->fAbsReset && fAlternate && !pPars->fUseAbs && nAbsRuns > 0 )
        fGatedRun[2] = fGatedRun[4] = 1;
    Budget[0] = pPars->fUseAbs ? Abc_MaxInt( 1, pPars->nAbsTime ) : pPars->nDynTime;
    Budget[1] = pPars->fUseAbs ? Abc_MaxInt( 1, pPars->nAbsTime ) : Abc_MaxInt( 1, pPars->nCtgTime );
    for ( k = 0; k < 5; k++ )
        snprintf( RunName[k], sizeof(RunName[k]), "%s%s", pRunNames[k], (k < 2 && Pars[k].fUseAbs) ? " with abstraction" : "" );
    Budget[2] = Abc_MaxInt( 1, pPars->nAbsTime );
    Budget[3] = Abc_MaxInt( 1, pPars->nAbsTime );
    Budget[4] = Abc_MaxInt( 1, pPars->nAbsTime );
    for ( iPhase = 0; ; iPhase++ )
    {
        k = fAlternate ? Order[iPhase % nRuns] : 0;
        if ( pMan[k] == NULL )
        {
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
            p->fQueryCut = 0;
            if ( pPars->fVerbose )
                Abc_Print( 1, "Phase %d: %s for %.0f nominal sec (resuming at level %d with %d inf lemmas).\n",
                    iPhase, RunName[k], Budget[k], p->fStarted ? Pdr2_ManLevel(p) : 0, Vec_PtrSize(p->vInf) );
        }
        else
            p->timeLimit = timeGlobal, p->propLimit = 0, p->propSlice = 0;
        RetValue = Pdr2_ManSolveInt( p );
        if ( RetValue != -1 || !fAlternate )
            break;
        if ( timeGlobal && Abc_Clock() >= timeGlobal )
            break;
        if ( p->fExhausted )
            break;  // the frame limit ends the schedule (every run would stop at the same depth)
        Budget[k] *= 2;
        // after the first slice (the examples that finish there pay nothing), a short BMC run
        // catches shallow counterexamples of designs on which every PDR frame is expensive
        if ( iPhase == 0 && pPars->nBmcTime > 0 && pPars->nFrameMax == 0 && (RetValue = Pdr2_ManBmcStage( pAigUsed, pInit, pPars, timeGlobal, &pCexBmc )) != -1 )
        {
            fBmcDone = 1;
            break;
        }
    }
    pPars->iFrame = pCexBmc ? pCexBmc->iFrame : Pdr2_ManLevel( p );
    pPars->nPhasesRun = iPhase + 1;
    pPars->nRestartsRun = 0;
    pPars->fBmcDecided = fBmcDone;
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
            Abc_Cex_t * pCexOrig = Abc_CexDup( pCex, Aig_ManRegNum(pAig) );
            for ( j = 0; j < Aig_ManRegNum(pAig); j++ )
                if ( pInit[j] == 2 ? fGatedRun[k] && Abc_InfoHasBit(pCex->pData, j) : pInit[j] == 1 )
                    Abc_InfoSetBit( pCexOrig->pData, j );
            Abc_CexFree( pCex );
            pCex = pCexOrig;
        }
        if ( Saig_ManPoNum(pAig) != 1 )
            pCex->iPo = Saig_ManFindFailedPoCex( pAig, pCex );
        // the trace must start in an initial state (the simulation takes any register values)
        for ( j = 0; j < Aig_ManRegNum(pAig); j++ )
            if ( pInit[j] != 2 && Abc_InfoHasBit(pCex->pData, j) != pInit[j] )
                break;
        if ( j < Aig_ManRegNum(pAig) )
        {
            Abc_Print( 1, "Pdr2_ManSolve(): The counterexample does not start in an initial state (flop %d).\n", j );
            Abc_CexFree( pCex );
            RetValue = -1;
        }
        else if ( !Saig_ManVerifyCex( pAig, pCex ) )
        {
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
        // the proof is by exhaustive BMC, which leaves no inductive invariant
        if ( pPars->fDumpInv )
            Abc_Print( 1, "The property was proved by BMC visiting all reachable states; there is no invariant to dump.\n" );
    }
    else if ( RetValue == 1 )
    {
        if ( pPars->fVerify && Pdr2_ManVerifyInvariant( p ) == 0 )
        {
            Abc_Print( 1, "Pdr2_ManSolve(): Invariant verification has FAILED.\n" );
            RetValue = -1;
        }
        // the invariant is over the flops of the solved design (gated or preprocessed for some runs)
        if ( pPars->fDumpInv && RetValue == 1 )
            Pdr2_ManDumpInvariant( p, fGatedRun[k] || fPreproc );
    }
    if ( pPars->fVerbose )
    {
        if ( fBmcDone )
            Abc_Print( 1, "Finished by the BMC stage after phase 0; statistics of the run of phase 0:\n" );
        else if ( fAlternate )
            Abc_Print( 1, "Finished in phase %d (%s); statistics of this run:\n", iPhase, RunName[k] );
        Pdr2_ManPrintStats( p );
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
            Pdr2_ManStop( pMan[j] );
    if ( pAigGated )
        Aig_ManStop( pAigGated );
    if ( fOrPos )
        Aig_ManStop( pAigUsed );
    ABC_FREE( pInitGated );
    ABC_FREE( pInit );
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
