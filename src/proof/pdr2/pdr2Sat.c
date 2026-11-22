/**CFile****************************************************************

  FileName    [pdr2Sat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [SAT solver interface: relative induction, cores, lifting.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2Sat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdr2Int.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Repeats a shared-solver query in an independently reconstructed frame.]

  Description []

***********************************************************************/
// Diagnostic differential check: rebuild the requested frame independently,
// without activation literals or shared learnt clauses, then repeat the query.
static void Pdr2_ManCheckSharedQuery( Pdr2_Man_t * p, int Frame, int Result,
                                    int * pLits, int nLits, int ** pCst, int * nCst, int nC )
{
    Gip_Solver_t * pCheck;
    Pdr2_Lem_t * pLem;
    int i, k, Lit, Check;
    if ( Result == GIP_UNDEF ) return;
    pCheck = Pdr2_ManNewSolver( p, Frame == 0 ? 1 : 0 );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        Pdr2_ManSolverAddLemma( p, pCheck, pLem->pCube, pLem->Id );
    for ( k = Frame; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            Pdr2_ManSolverAddLemma( p, pCheck, pLem->pCube, pLem->Id );
    if ( p->pPars->fPropHyp && Frame < Pdr2_ManLevel(p) )
    {
        Lit = Abc_Var2Lit( p->VarBad, 1 );
        Gip_SolverAddLemmaId( pCheck, &Lit, 1, p->IdProp );
    }
    pCheck->TimeLimit = p->timeGlobal;
    Check = Gip_SolverSolve( pCheck, pLits, nLits, pCst, nCst, nC, -1 );
    if ( Check != GIP_UNDEF && Check != Result )
        Abc_Print( 1, "SHARED QUERY CHECK FAILED: frame %d shared %d independent %d.\n", Frame, Result, Check );
    assert( Check == GIP_UNDEF || Check == Result );
    Gip_SolverFree( pCheck );
}

/**Function*************************************************************

  Synopsis    [Decides whether a solver of the manager may request the jftr mode.]

  Description [The conditions of pdr2; GipSAT ignores a request for a
  solver or a context the mode is not defined for (see gipJftr.c). pSat
  is a frame handle or an actual solver.]

***********************************************************************/
static int Pdr2_ManJftrEligible( Pdr2_Man_t * p, Gip_Solver_t * pSat )
{
    // the manager: no unit over a register input (initial-state predicate, trace guard), no shared solver, and no
    // predecessor extraction that reads a full model (CNF justification, lifting memo)
    if ( p->pPars->nInitLiReg || p->pInitSat || p->GuardLit >= 0 )
        return 0;
    if ( p->nSharedSlots || p->pShared )
        return 0;
    if ( p->nCnfJustMode || p->nLiftMemoMode )
        return 0;
    // the solver: not the private bad-state solver, and of the manager's context
    return pSat != p->pBadRoot && pSat->pCtx == p->pCtx;
}

// the jftr request of one physical solve, set before every Gip_SolverSolve (the solver consumes it)
static inline void Pdr2_ManSatSetJftr( Pdr2_Man_t * p, Gip_Solver_t * pHandle, int Request )
{
    Gip_SolverSetJftr( Pdr2_SolverActual(pHandle), Pdr2_ManJftrEligible(p, pHandle) ? Request : GIP_JFTR_NONE );
}

// runs one SAT query and accounts for its cost (the propagation count is the deterministic
// measure of work used by the level restarts)
static void Pdr2_ManSeedPhases( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Frame, int Mode );
static inline int Pdr2_ManSatSolve( Pdr2_Man_t * p, Gip_Solver_t * pSat, int * pLits, int nLits, int ** pCst, int * nCst, int nC, int QueryKind, int nDropConfs, int Request )
{
    Gip_Solver_t * pHandle = pSat;
    pSat = Pdr2_SolverActual( pSat );
    ABC_INT64_T nProps = pSat->Stats.nPropagations, nConfs = pSat->Stats.nConflicts;
    ABC_INT64_T nDecisions = pSat->Stats.nDecisions, nJustTested = pSat->nJustChecks, nJustSkipped = pSat->nJustSkipped;
    ABC_INT64_T nWatchLists = pSat->nWatchLists, nWatchSkipped = pSat->nWatchSkipped;
    ABC_INT64_T nCleanL = pSat->Stats.nCleanL, nCleanLNone = pSat->Stats.nCleanLNone;
    abctime timeCleanL = pSat->Stats.timeCleanL;
    int RetValue, nGuards = 0;
    int InputConfSaved = pSat->nInputConfLimit;
    if ( QueryKind == 1 && p->nInputBadLimit >= 0 && !p->pPars->fUseAbs )
        pSat->nInputConfLimit = p->nInputBadLimit;
    if ( p->nInputScope )
    {
        int Enabled = (p->nInputScope & QueryKind) != 0;
        if ( pSat->fInputDecisions && !Enabled )
        {
            int i, Var;
            // MIC may retain a fixed domain across several queries. Restore
            // every internal variable skipped by the preceding input policy.
            Vec_IntForEachEntry(pSat->Domain.Set.vSet, Var, i)
                if ( pSat->pValue[Var] == GIP_NONE ) Gip_VsidsPush(&pSat->Vsids, Var);
        }
        pSat->fInputDecisions = Enabled;
    }
    if ( pHandle->pShared )
    {
        // Logical frame identity belongs to the handle, not to the shared
        // solver: a nested CTG can query another frame before this one resumes.
        Gip_SolverUnsetDomain( pSat );
        Gip_SolverReset( pSat );
        Vec_IntClear( p->vSharedAssump );
        Vec_IntPush( p->vSharedAssump, Gip_Lit(p->iSharedBase + pHandle->iSharedFrame, 0) );
        nGuards = 1;
        // The predecessor guard being false forces the whole earlier prefix
        // false through the chain. Those frames are irrelevant to this query.
        if ( p->nSharedMode >= 2 && pHandle->iSharedFrame > 1 )
        {
            Vec_IntPush( p->vSharedAssump, Gip_Lit(p->iSharedBase + pHandle->iSharedFrame - 1, 1) );
            nGuards++;
        }
        Vec_IntPushArray( p->vSharedAssump, pLits, nLits );
        pLits = Vec_IntArray( p->vSharedAssump );
        nLits = Vec_IntSize( p->vSharedAssump );
        if ( p->nSharedMode == 3 )
        {
            Pdr2_Lem_t * pLem;
            int i, j, k;
            Vec_IntClear( p->vSharedSeeds );
            Vec_IntPush( p->vSharedSeeds, Gip_Lit(p->pCtx->varConst, 0) );
            Vec_IntPushArray( p->vSharedSeeds, pLits, nLits );
            if ( pHandle->vSharedDomain )
                Vec_IntAppend( p->vSharedSeeds, pHandle->vSharedDomain );
            for ( i = 0; i < nC; i++ )
                Vec_IntPushArray( p->vSharedSeeds, pCst[i], nCst[i] );
            Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
                for ( j = 0; j < pLem->pCube->nLits; j++ )
                    Vec_IntPush( p->vSharedSeeds, Pdr2_LitLo(p, pLem->pCube->Lits[j]) );
            for ( k = pHandle->iSharedFrame; k < Pdr2_ManFrameNum(p); k++ )
            {
                if ( k < p->nSharedSlots )
                    Vec_IntPush( p->vSharedSeeds, Gip_Lit(p->iSharedBase + k, 0) );
                Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
                    for ( j = 0; j < pLem->pCube->nLits; j++ )
                        Vec_IntPush( p->vSharedSeeds, Pdr2_LitLo(p, pLem->pCube->Lits[j]) );
            }
            if ( p->pPars->fPropHyp && pHandle->iSharedFrame < Pdr2_ManLevel(p) )
                Vec_IntPush( p->vSharedSeeds, Gip_Lit(p->VarBad, 0) );
            // All earlier guarded clauses are disabled. Restrict the domain
            // to the active frame, its invariant clauses, and this query.
            pSat->Domain.nFixed = 0;
            Gip_DomainReset( &pSat->Domain );
            Gip_SolverSetDomain( pSat, Vec_IntArray(p->vSharedSeeds), Vec_IntSize(p->vSharedSeeds) );
        }
        else if ( pHandle->vSharedDomain )
            Gip_SolverSetDomain( pSat, Vec_IntArray(pHandle->vSharedDomain), Vec_IntSize(pHandle->vSharedDomain) );
    }
    pSat->nConfLimit = p->fBadPhaseProbe ? p->nBadPhaseConfs : nDropConfs;
    pSat->TimeLimit  = p->timeLimit;
    if ( p->timeSliceHard && (!pSat->TimeLimit || p->timeSliceHard < pSat->TimeLimit) )
        pSat->TimeLimit = p->timeSliceHard;
    // a slice ends between obligations; the obligation in progress may overrun it by at most
    // one more slice budget in total, after which every query is canceled (a safety valve for
    // pathological obligations). Exact resume (a run in the schedule follows the trajectory of
    // the same run alone) holds only while this valve does not fire: a canceled query has no
    // counterpart in an uninterrupted run, and the canceled propagation sweeps restart (with a
    // new order) instead of continuing; nQueryCuts counts the canceled queries
    if ( p->propLimit )
    {
        ABC_INT64_T Left = p->propLimit + p->propSlice - p->nProps;
        pSat->nPropLimit = nProps + (Left > 0 ? Left : 1);
    }
    else
        pSat->nPropLimit = 0;
    p->nSolves++;
    // evaluated here, after the per-query policy adjustments above
    Pdr2_ManSatSetJftr( p, pHandle, Request );
    RetValue = Gip_SolverSolve( pSat, pLits, nLits, pCst, nCst, nC, -1 );
    if ( RetValue == GIP_UNDEF && p->fBadPhaseProbe && pSat->nConfLimit > 0 &&
         pSat->Stats.nConflicts >= pSat->nConfCounted + pSat->nConfLimit &&
         (!pSat->TimeLimit || Abc_Clock() < pSat->TimeLimit) &&
         (!pSat->nPropLimit || pSat->Stats.nPropagations < pSat->nPropLimit) &&
         (!pSat->pFuncStop || !pSat->pFuncStop(pSat->RunId)) )
    {
        // A heuristic retry of the SAME query, retaining ordinary learnt
        // clauses and respecting the original time/propagation deadline.
        // The first conflict-limited result is never reported as a proof.
        assert(nC == 0);
        if ( pHandle->pShared && pSat->fTempDomain )
        {
            Vec_Int_t * vSeeds = p->nSharedMode == 3 ? p->vSharedSeeds : pHandle->vSharedDomain;
            assert(vSeeds);
            // Reinstall this frame's decision domain for the uncapped retry.
            Gip_SolverUnsetDomain(pSat);
            Gip_SolverSetDomain(pSat, Vec_IntArray(vSeeds), Vec_IntSize(vSeeds));
        }
        else
            Gip_SolverReset(pSat);
        Pdr2_ManSeedPhases(p, pSat, Pdr2_ManLevel(p), 2);
        pSat->nConfLimit = 0;
        p->nBadRephases++; p->nSolves++;
        Pdr2_ManSatSetJftr( p, pHandle, Request );   // each physical solve needs its own request
        RetValue = Gip_SolverSolve(pSat, pLits, nLits, pCst, nCst, nC, -1);
    }
    pSat->nConfLimit = 0;
    if ( pHandle->pShared && Gip_OptionGet("PDR2_SHARED_CHECK") )
        Pdr2_ManCheckSharedQuery( p, pHandle->iSharedFrame, RetValue, pLits + nGuards, nLits - nGuards, pCst, nCst, nC );
    if ( RetValue == GIP_UNDEF && nDropConfs && pSat->Stats.nConflicts - nConfs >= nDropConfs &&
         (!pSat->TimeLimit || Abc_Clock() < pSat->TimeLimit) &&
         (!pSat->nPropLimit || pSat->Stats.nPropagations < pSat->nPropLimit) &&
         (!pSat->pFuncStop || !pSat->pFuncStop(pSat->RunId)) )
        p->nDropConfCuts++;
    else if ( RetValue == GIP_UNDEF )
    {
        p->fQueryCut = 1;
        p->nQueryCuts += (pSat->nPropLimit > 0 && pSat->Stats.nPropagations >= pSat->nPropLimit) ||
                        (p->timeSliceHard && Abc_Clock() >= p->timeSliceHard);
    }
    p->nProps     += pSat->Stats.nPropagations - nProps;
    p->nConflicts += pSat->Stats.nConflicts - nConfs;
    p->nSatDecisions += pSat->Stats.nDecisions - nDecisions;
    p->nJustTested += pSat->nJustChecks - nJustTested;
    p->nJustSkipped += pSat->nJustSkipped - nJustSkipped;
    p->nWatchLists += pSat->nWatchLists - nWatchLists;
    p->nWatchSkipped += pSat->nWatchSkipped - nWatchSkipped;
    p->nCleanL    += pSat->Stats.nCleanL - nCleanL;
    p->nCleanLNone += pSat->Stats.nCleanLNone - nCleanLNone;
    p->timeCleanL += pSat->Stats.timeCleanL - timeCleanL;
    if ( RetValue == GIP_UNSAT )
        p->iCoreFrame = pSat->iCoreFrame;
    pSat->nInputConfLimit = InputConfSaved;
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Computes a deterministic phase seed independently of the proof search.]

  Description []

***********************************************************************/
static unsigned Pdr2_ManPhaseHash( unsigned x )
{
    x ^= x >> 16; x *= 0x7feb352du;
    x ^= x >> 15; x *= 0x846ca68bu;
    return x ^ (x >> 16);
}

/**Function*************************************************************

  Synopsis    [Sets SAT polarity preferences using a simulated transition.]

  Description []

***********************************************************************/
// Seed a new frame's decision phases with a coherent simulated transition
// at that depth. This changes only preferred SAT polarities, never clauses,
// assignments, or proof state. A separate hash leaves PDR's RNG untouched.
static void Pdr2_ManSeedPhases( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Frame, int Mode )
{
    Aig_Obj_t * pObj;
    int i, Var;
    unsigned Seed = (unsigned)p->pPars->nRandomSeed;
    abctime Start = Abc_Clock();
    if ( Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) ) return;
    if ( !p->pPhaseSimValues )
    {
        p->pPhaseSimValues = ABC_CALLOC( char, Aig_ManObjNumMax(p->pAig) );
        p->pPhaseSimState = ABC_CALLOC( char, p->nRegs+1 );
        for ( i = 0; i < p->nRegs; i++ )
            p->pPhaseSimState[i] = p->pInit[i] == 2 ? Pdr2_ManPhaseHash(Seed+(unsigned)i) & 1 : p->pInit[i];
    }
    for ( ; ; p->nPhaseSimFrame++ )
    {
        char * v = p->pPhaseSimValues;
        v[Aig_ObjId(Aig_ManConst1(p->pAig))] = 1;
        Saig_ManForEachPi( p->pAig, pObj, i )
            v[Aig_ObjId(pObj)] = Mode == 2 ? 0 : Mode == 3 ? 1 :
                Pdr2_ManPhaseHash(Seed ^ ((unsigned)i * 2654435761u) ^ ((unsigned)p->nPhaseSimFrame * 2246822519u)) & 1;
        Saig_ManForEachLo( p->pAig, pObj, i ) v[Aig_ObjId(pObj)] = p->pPhaseSimState[i];
        Aig_ManForEachNode( p->pAig, pObj, i )
            v[Aig_ObjId(pObj)] = (v[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj)) &
                                (v[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj));
        Aig_ManForEachCo( p->pAig, pObj, i )
            v[Aig_ObjId(pObj)] = v[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
        if ( p->nPhaseSimFrame >= Frame ) break;
        Saig_ManForEachLi( p->pAig, pObj, i ) p->pPhaseSimState[i] = v[Aig_ObjId(pObj)];
    }
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        Var = p->pCtx->pObj2Var ? p->pCtx->pObj2Var[Aig_ObjId(pObj)] : Aig_ObjId(pObj);
        if ( Var >= 0 ) pSat->pPhase[Var] = p->pPhaseSimValues[Aig_ObjId(pObj)] ? GIP_TRUE : GIP_FALSE;
    }
    p->nPhaseSimSeeds++;
    p->timePhaseSim += Abc_Clock() - Start;
}

/**Function*************************************************************

  Synopsis    [Creates a solver over the transition relation.]

  Description [Type 0: plain. Type 1: with the initial states as unit
  clauses (the flops with a defined initial value). Type 2: with the
  lemmas of frame infinity. PDR2_SOLVER_UNRESTRICTED contains only the
  original transition relation, for lifting and certificate checking.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gip_Solver_t * Pdr2_ManNewSolver( Pdr2_Man_t * p, int Type )
{
    if ( Type == 2 && p->nSharedMode == 4 && Vec_PtrSize(p->vSolvers) < p->nSharedSlots )
    {
        int k = Vec_PtrSize(p->vSolvers), Chain[2], Lit;
        assert( k > 0 );
        if ( !p->pShared )
        {
            p->pShared = Pdr2_ManNewSolver( p, 0 );
            if ( p->pPars->fPropHyp )
            {
                // Only completed frames will query this solver. A permanent
                // property unit recovers the root propagation of per-frame SAT.
                // Tag 1 is conservative: no proof using it may jump over frame 1.
                Lit = Abc_Var2Lit( p->VarBad, 1 );
                Gip_SolverLoadVar( p->pShared, p->VarBad );
                Gip_SolverAddClauseTag( p->pShared, &Lit, 1, GIP_CLA_LEMMA, 2u );
            }
        }
        Gip_SolverUnsetDomain( p->pShared );
        Gip_SolverReset( p->pShared );
        Gip_SolverAddDomain( p->pShared, p->iSharedBase + k, 0 );
        if ( k > 1 )
        {
            Chain[0] = Gip_Lit( p->iSharedBase + k - 1, 1 );
            Chain[1] = Gip_Lit( p->iSharedBase + k, 0 );
            Gip_SolverAddLemmaId( p->pShared, Chain, 2, -1 );
        }
        // The frontier itself is an ordinary solver until the frame completes.
    }
    if ( Type == 2 && p->nSharedSlots && p->nSharedMode != 4 && Vec_PtrSize(p->vSolvers) < p->nSharedSlots )
    {
        Pdr2_Lem_t * pLem;
        Gip_Solver_t * pHandle = ABC_CALLOC( Gip_Solver_t, 1 );
        int i, k = Vec_PtrSize(p->vSolvers), Chain[2];
        assert( k > 0 );
        if ( !p->pShared )
            p->pShared = Pdr2_ManNewSolver( p, 0 );
        pHandle->pShared = p->pShared;
        pHandle->iSharedFrame = k;
        // a_k implies a_(k+1): querying k enables exactly the suffix of
        // applicable guarded lemmas. Earlier activations may remain false.
        Gip_SolverUnsetDomain( p->pShared );
        Gip_SolverReset( p->pShared );
        Gip_SolverAddDomain( p->pShared, p->iSharedBase + k, 0 );
        if ( k > 1 )
        {
            Chain[0] = Gip_Lit( p->iSharedBase + k - 1, 1 );
            Chain[1] = Gip_Lit( p->iSharedBase + k, 0 );
            Gip_SolverAddLemmaId( p->pShared, Chain, 2, -1 );
        }
        Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
            Pdr2_ManSolverAddLemma( p, pHandle, pLem->pCube, pLem->Id );
        return pHandle;
    }
    int Clone = Type == 2 && Gip_OptionGet("PDR2_CLONE") ? atoi(Gip_OptionGet("PDR2_CLONE")) : 0;
    Gip_Solver_t * pSat;
    if ( Clone )
    {
        Gip_Solver_t * pSrc = Clone == 2 ? p->pLift : p->pInf;
        abctime clk = Abc_Clock();
        assert( !pSrc->fTempDomain );
        Gip_SolverReset( pSrc );
        pSat = Gip_SolverCloneRoot( pSrc );
        p->nSolverClones++;
        p->timeSolverClone += Abc_Clock() - clk;
    }
    else
        pSat = Gip_OptionGet("PDR2_LAZYCNF") && atoi(Gip_OptionGet("PDR2_LAZYCNF")) ?
               Gip_SolverNewLazy( p->pCtx ) : Gip_SolverNew( p->pCtx );
    pSat->RunId = p->pPars->RunId;
    if ( p->pPars->nInputPolicy )
    {
        pSat->fInputDecisions = p->pPars->nInputPolicy > 0;
        pSat->nInputConfLimit = p->pPars->nInputPolicy == 2 ? 128 : 0;
    }
    if ( Gip_OptionGet("PDR2_RECYCLE_LIFT") ) pSat->nRecycleMode = 0;
    // Ternary weakening currently expects the fully decided source model.
    // Keep its original solver behavior until partial-input handling is fixed.
    if ( p->pPars->nLiftSim ) pSat->fJustify = 0;
    // Changing decision policies inside an abstract query exposed a stale
    // pseudo-input trace in refinement. Keep the previously validated fixed
    // input-first policy there; adaptive fallback is a concrete-engine option.
    if ( p->pPars->fUseAbs ) pSat->nInputConfLimit = pSat->nInputMillis = 0;
    pSat->pFuncStop = p->pPars->pFuncStop;
    pSat->fFastClean = 1;
    pSat->fCleanSkip = 1;
    Gip_SolverSetLemFrames( pSat, p->vLemFrame );
    if ( Type != PDR2_SOLVER_UNRESTRICTED && p->GuardLo >= 0 )
    {
        Gip_SolverAddLemmaId(pSat, &p->GuardLo, 1, -1);
        if ( p->GuardLi >= 0 ) Gip_SolverAddLemmaId(pSat, &p->GuardLi, 1, -1);
    }
    if ( Type == 1 )
    {
        int i, Lit;
        for ( i = 0; i < p->nRegs; i++ )
        {
            if ( p->pInit[i] == 2 )
                continue;
            Lit = Abc_Var2Lit( p->pLoVar[i], !p->pInit[i] );
            Gip_SolverAddLemmaId( pSat, &Lit, 1, p->IdInit );
        }
        if ( p->pPars->nInitLiReg )
        {
            Lit = p->pLiLit[p->pPars->nInitLiReg-1];
            Gip_SolverAddLemmaId(pSat,&Lit,1,p->IdInit);
        }
    }
    else if ( Type == 2 )
    {
        Pdr2_Lem_t * pLem;
        int i;
        if ( Clone != 1 )
            Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
                Pdr2_ManSolverAddLemma( p, pSat, pLem->pCube, pLem->Id );
        if ( p->pPars->fWarmStart && !Clone )
            p->nWarmCopied += Gip_SolverWarmStart( pSat, p->pInf );
        if ( !Clone && Gip_OptionGet("PDR2_WARMLIFT") && atoi(Gip_OptionGet("PDR2_WARMLIFT")) )
        {
            // Isolate which reusable information makes full lifting-solver
            // clones fast: saved phases (1), activities (2), T-only facts and
            // learned clauses (4). The new frame keeps its normal watch order.
            Gip_SolverReset( p->pLift );
            p->nWarmCopied += Gip_SolverWarmStartMode( pSat, p->pLift, atoi(Gip_OptionGet("PDR2_WARMLIFT")) );
        }
        if ( Gip_OptionGet("PDR2_PHASESIM") && atoi(Gip_OptionGet("PDR2_PHASESIM")) > 0 )
            Pdr2_ManSeedPhases( p, pSat, Vec_PtrSize(p->vSolvers), atoi(Gip_OptionGet("PDR2_PHASESIM")) );
    }
    return pSat;
}

/**Function*************************************************************

  Synopsis    [Moves a completed frame and its active lemmas into the shared SAT solver.]

  Description []

***********************************************************************/
void Pdr2_ManShareCompleted( Pdr2_Man_t * p, int Frame )
{
    Gip_Solver_t * pOld = Pdr2_ManSolver( p, Frame );
    Gip_Solver_t * pHandle = ABC_CALLOC( Gip_Solver_t, 1 );
    Pdr2_Lem_t * pLem;
    int i, k;
    assert( p->nSharedMode == 4 && Frame > 0 && Frame < p->nSharedSlots );
    assert( p->pShared && !pOld->pShared );
    pHandle->pShared = p->pShared;
    pHandle->iSharedFrame = Frame;
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        Pdr2_ManSolverAddLemma( p, pHandle, pLem->pCube, pLem->Id );
    for ( k = Frame; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            Pdr2_ManSolverAddLemma( p, pHandle, pLem->pCube, pLem->Id );
    if ( p->pLastSolver == pOld ) p->pLastSolver = NULL;
    Vec_PtrWriteEntry( p->vSolvers, Frame, pHandle );
    Gip_SolverFree( pOld );
}


/**Function*************************************************************

  Synopsis    [Invalidates generalization witnesses excluded by a newly installed lemma.]

  Description []

***********************************************************************/
// A cached partial source must visibly satisfy every newly applicable lemma.
// Unknown literals never certify satisfaction: such a witness is discarded.
static void Pdr2_ManMicCexInvalidate( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, int Frame )
{
    int w, i, s;
    for ( w = 0; w < 2; w++ )
    {
        word Kill = p->MicCexLive[w];
        for ( i = 0; Kill && i < pCube->nLits; i++ )
        {
            int Lit = pCube->Lits[i];
            word * b = p->pMicCexBits + 8 * Abc_Lit2Var(Lit);
            word Match = Abc_LitIsCompl(Lit) ? ~b[w] : b[w];
            Kill &= ~b[2+w] | Match;
        }
        for ( s = 0; Kill && s < 64; s++ )
            if ( (Kill & ((word)1 << s)) && p->MicCexFrame[64*w+s] <= Frame )
            {
                p->MicCexLive[w] &= ~((word)1 << s);
                Kill &= ~((word)1 << s);
                p->nMicCexKilled++;
            }
    }
}

/**Function*************************************************************

  Synopsis    [Adds the clause blocking the cube in the current state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManSolverAddLemma( Pdr2_Man_t * p, Gip_Solver_t * pSat, Pdr2_Cube_t * pCube, int Id )
{
    int i;
    if ( p->nMicCexMode && Id >= 0 )
        Pdr2_ManMicCexInvalidate( p, pCube, Vec_IntEntry(p->vLemFrame, Id) );
    if ( pSat->pShared )
    {
        int Frame = Vec_IntEntry( p->vLemFrame, Id );
        assert( Frame > 0 );
        while ( Vec_IntSize(p->vSharedLemFrame) <= Id )
            Vec_IntPush( p->vSharedLemFrame, -1 );
        if ( Vec_IntEntry(p->vSharedLemFrame, Id) >= Frame )
            return;
        Vec_IntWriteEntry( p->vSharedLemFrame, Id, Frame );
        Vec_IntClear( p->vLem );
        if ( Frame != GIP_FRAME_INF )
            Vec_IntPush( p->vLem, Gip_Lit(p->iSharedBase + Abc_MinInt(Frame, p->nSharedSlots-1), 1) );
        for ( i = 0; i < pCube->nLits; i++ )
            Vec_IntPush( p->vLem, Abc_LitNot(Pdr2_LitLo(p, pCube->Lits[i])) );
        Gip_SolverUnsetDomain( pSat->pShared );
        Gip_SolverAddLemmaId( pSat->pShared, Vec_IntArray(p->vLem), Vec_IntSize(p->vLem), Id );
        return;
    }
    Vec_IntClear( p->vLem );
    for ( i = 0; i < pCube->nLits; i++ )
        Vec_IntPush( p->vLem, Abc_LitNot( Pdr2_LitLo(p, pCube->Lits[i]) ) );
    Gip_SolverAddLemmaId( pSat, Vec_IntArray(p->vLem), Vec_IntSize(p->vLem), Id );
    // The private bad-state solver is only strengthened with frame clauses.
    // Its conditional learned clauses never flow back into a frame solver.
    if ( p->pBadRoot && p->pBadBase == pSat )
        Gip_SolverAddLemmaId( p->pBadRoot, Vec_IntArray(p->vLem), Vec_IntSize(p->vLem), Id );
}

/**Function*************************************************************

  Synopsis    [Adds a unit clause without extending the decision domain.]

  Description [Used to assert the property in completed frames: the fact
  is propagated at level 0, so the domain is unaffected.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManSolverAddUnit( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Lit )
{
    // Property units are added when a frame is completed. Clear the small
    // cache as well; no witness may outlive an unrecorded root constraint.
    if ( p->nMicCexMode ) p->MicCexLive[0] = p->MicCexLive[1] = 0;
    if ( pSat->pShared )
    {
        int Clause[2] = { Lit, Gip_Lit(p->iSharedBase + pSat->iSharedFrame, 1) };
        Gip_SolverUnsetDomain( pSat->pShared );
        Gip_SolverAddLemmaId( pSat->pShared, Clause, 2, p->IdProp );
        return;
    }
    Gip_SolverReset( pSat );
    Gip_SolverLoadVar( pSat, Abc_Lit2Var(Lit) );
    if ( Gip_SolverLitValue( pSat, Lit ) == GIP_TRUE )
        return;
    // A backward viability restriction can leave a completed frame empty.
    assert( p->GuardLo >= 0 || Gip_SolverLitValue( pSat, Lit ) == GIP_NONE );
    Gip_SolverAddClauseTag( pSat, &Lit, 1, GIP_CLA_LEMMA, ((unsigned)p->IdProp << 1) | 1 );
    assert( p->GuardLo >= 0 || !pSat->fTrivialUnsat );
}

/**Function*************************************************************

  Synopsis    [Relative induction query.]

  Description [Checks whether the cube (flop literals, in the given order,
  which becomes the assumption order) is reachable in one step from the
  states of the solver, optionally strengthened with the clause blocking
  the cube itself (fStrengthen) and with one more clause given as flop
  literals (vCstCls). Returns 1 if UNSAT (blocked), 0 if SAT, -1 if
  undecided. Records the query for Pdr2_ManInductiveCore and Pdr2_ManGetPred.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManSolveRelativeLimit( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls, int nDropConfs, int Request )
{
    int * pCst[2], nCst[2], nC = 0;
    int i, Lit, RetValue;
    Vec_IntClear( p->vRelInd );
    Vec_IntAppend( p->vRelInd, vCube );
    Vec_IntClear( p->vAssump );
    Vec_IntForEachEntry( vCube, Lit, i )
        Vec_IntPush( p->vAssump, Pdr2_LitLi(p, Lit) );
    Vec_IntClear( p->vLastAssump );
    Vec_IntAppend( p->vLastAssump, p->vAssump );
    p->pLastSolver = pSat;
    if ( fStrengthen && !vCstCls && p->nStrengthenOnDemand > 0 &&
         Vec_IntSize(vCube) >= p->nStrengthenOnDemand )
    {
        // A predecessor outside the cube already satisfies the temporary
        // clause. An UNSAT result without that clause proves a stronger fact.
        p->nStrengthenTrials++;
        RetValue = Pdr2_ManSatSolve(p, pSat, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump),
                                    NULL, NULL, 0, p->fInputBlockQuery ? 2 : 4, nDropConfs, GIP_JFTR_NONE);
        if ( RetValue == GIP_UNDEF ) return -1;
        if ( RetValue == GIP_UNSAT ) { p->nStrengthenAvoided++; return 1; }
        Vec_IntForEachEntry(vCube, Lit, i)
            if ( Pdr2_ManLitValue(p, pSat, Lit) == GIP_FALSE )
            {
                p->nStrengthenAvoided++;
                return 0;
            }
    }
    if ( fStrengthen )
    {
        Vec_IntClear( p->vCst1 );
        Vec_IntForEachEntry( vCube, Lit, i )
            Vec_IntPush( p->vCst1, Abc_LitNot( Pdr2_LitLo(p, Lit) ) );
        pCst[nC] = Vec_IntArray( p->vCst1 );
        nCst[nC] = Vec_IntSize( p->vCst1 );
        nC++;
    }
    if ( vCstCls )
    {
        Vec_IntClear( p->vCst2 );
        Vec_IntForEachEntry( vCstCls, Lit, i )
            Vec_IntPush( p->vCst2, Pdr2_LitLo(p, Lit) );
        pCst[nC] = Vec_IntArray( p->vCst2 );
        nCst[nC] = Vec_IntSize( p->vCst2 );
        nC++;
    }
    RetValue = Pdr2_ManSatSolve( p, pSat, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump), pCst, nCst, nC, p->fInputBlockQuery ? 2 : 4, nDropConfs, Request );
    if ( RetValue == GIP_UNSAT )
        return 1;
    if ( RetValue == GIP_SAT )
        return 0;
    return -1;
}

int Pdr2_ManSolveRelative( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls )
{
    return Pdr2_ManSolveRelativeLimit( p, pSat, vCube, fStrengthen, vCstCls, 0, GIP_JFTR_NONE );
}

// Optional minimization may keep its last proved cube when a trial times out.
int Pdr2_ManTryDrop( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls )
{
    return Pdr2_ManSolveRelativeLimit( p, pSat, vCube, fStrengthen, vCstCls, p->nDropConfLimit, GIP_JFTR_NONE );
}

// the same two queries with a jftr request (GIP_JFTR_*)
int Pdr2_ManSolveRelativeJftr( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen,
                               Vec_Int_t * vCstCls, int Request )
{
    return Pdr2_ManSolveRelativeLimit( p, pSat, vCube, fStrengthen, vCstCls, 0, Request );
}
int Pdr2_ManTryDropJftr( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen,
                         Vec_Int_t * vCstCls, int Request )
{
    return Pdr2_ManSolveRelativeLimit( p, pSat, vCube, fStrengthen, vCstCls, p->nDropConfLimit, Request );
}

/**Function*************************************************************

  Synopsis    [Tries a cut-mapped solver when a frontier query runs out of conflicts.]

***********************************************************************/
static int Pdr2_ManSolveBadMapped( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Lit, int Seconds, int Request )
{
    const char * pOption = Gip_OptionGet("PDR2_BAD_MAPPED_CONFS");
    int Limit = pOption ? Abc_MaxInt(0, atoi(pOption)) : 512;
    Vec_Int_t * vModel, * vFixed;
    int i, Bit, Var, Ret;
    if ( Limit )
    {
        ABC_INT64_T Cuts = p->nDropConfCuts;
        Ret = Pdr2_ManSatSolve(p, pSat, &Lit, 1, NULL, NULL, 0, 1, Limit, Request);
        if ( Ret != GIP_UNDEF || p->nDropConfCuts == Cuts ) return Ret;
        p->nDropConfCuts = Cuts;
    }
    vModel = Vec_IntAlloc(p->nPis + p->nRegs);
    Ret = Pdr2_ManMappedBad(p, Seconds, vModel);
    if ( Ret == GIP_UNSAT )
    {
        p->iCoreFrame = Pdr2_ManLevel(p);
        Vec_IntFree(vModel);
        return Ret;
    }
    if ( Ret == GIP_SAT )
    {
        assert( Vec_IntSize(vModel) == p->nPis + p->nRegs );
        vFixed = Vec_IntAlloc(Vec_IntSize(vModel) + 1);
        Vec_IntPush(vFixed, Lit);
        Vec_IntForEachEntry( vModel, Bit, i )
        {
            Var = i < p->nPis ? p->pPiVar[i] : p->pLoVar[i-p->nPis];
            Vec_IntPush(vFixed, Abc_Var2Lit(Var, !Bit));
        }
        // Lifting consumes the frame solver's model and the original bad
        // literal in vLastAssump. Use the CI assignments for this call only.
        Ret = Pdr2_ManSatSolve(p, pSat, Vec_IntArray(vFixed), Vec_IntSize(vFixed), NULL, NULL, 0, 1, 0, GIP_JFTR_NONE);
        Vec_IntFree(vFixed);
        if ( Ret != GIP_UNSAT )
        {
            Vec_IntFree(vModel);
            return Ret;
        }
    }
    Vec_IntFree(vModel);
    if ( Pdr2_ManPastDeadline(p) ) return GIP_UNDEF;
    return Pdr2_ManSatSolve(p, pSat, &Lit, 1, NULL, NULL, 0, 1, 0, Request);
}

/**Function*************************************************************

  Synopsis    [Checks for a bad state in the last frame.]

  Description [Returns 1 if a bad state exists (SAT), 0 if none (UNSAT),
  -1 if undecided.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManSolveBad( Pdr2_Man_t * p )
{
    Gip_Solver_t * pSat = Pdr2_ManSolver( p, Pdr2_ManLevel(p) );
    int Lit = Abc_Var2Lit( p->VarBad, 0 ), RetValue;
    int Request = Pdr2_ManJftrReq( p, PDR2_JQ_BAD, GIP_JFTR_WALK_SHRINK );
    const char * pPrefix = Gip_OptionGet( "PDR2_DUMP_BAD" );
    const char * pMapped = Gip_OptionGet( "PDR2_BAD_MAPPED_SECS" );
    char FileName[4096];
    if ( p->nBadRootMode && !p->pPars->fUseAbs && !p->pPars->nInitLiReg && !p->nSharedSlots )
    {
        if ( !p->pBadRoot || p->pBadBase != pSat || p->iBadRootFrame != Pdr2_ManLevel(p) )
        {
            if ( p->pLastSolver == p->pBadRoot ) p->pLastSolver = NULL;
            if ( p->pBadRoot ) Gip_SolverFree(p->pBadRoot);
            Gip_SolverUnsetDomain(pSat);
            Gip_SolverReset(pSat);
            p->pBadRoot = Gip_SolverCloneRoot(pSat);
            p->pBadBase = pSat;
            p->iBadRootFrame = Pdr2_ManLevel(p);
            p->nBadRootBuilds++;
            // Bad is permanent only in this private solver. A new frame
            // gets a fresh copy because the frame constraints weaken.
            Gip_SolverAddLemmaId(p->pBadRoot, &Lit, 1, -1);
        }
        pSat = p->pBadRoot;
        if ( p->nBadRootMode == 2 && !pSat->fTrivialUnsat )
        {
            Gip_SolverReset(pSat);
            pSat->nLastSimplify = pSat->Stats.nSolves - 101;
            Gip_SolverSimplify(pSat);
        }
    }
    if ( Gip_OptionGet("PDR2_PHASEBAD") && atoi(Gip_OptionGet("PDR2_PHASEBAD")) &&
         Gip_OptionGet("PDR2_PHASESIM") && atoi(Gip_OptionGet("PDR2_PHASESIM")) > 0 )
    {
        Gip_Solver_t * pActual = Pdr2_SolverActual(pSat);
        if ( pActual->fTempDomain ) Gip_SolverUnsetDomain(pActual);
        Gip_SolverReset( pActual );
        Pdr2_ManSeedPhases( p, pActual, Pdr2_ManLevel(p), atoi(Gip_OptionGet("PDR2_PHASESIM")) );
    }
    if ( pPrefix && p->nBadDumps < 16 )
    {
        int n = snprintf( FileName, sizeof(FileName), "%s_a%d_d%d_s%d_l%d_f%04d_q%04d.cnf", pPrefix,
            p->pPars->fUseAbs, p->pPars->fDynamic, p->pPars->nRandomSeed, p->pPars->nLiftSim,
            Pdr2_ManLevel(p), p->nBadDumps++ );
        if ( n > 0 && n < (int)sizeof(FileName) )
            Pdr2_SolverActual(pSat)->pDumpFile = FileName;
    }
    Vec_IntClear( p->vLastAssump );
    Vec_IntPush( p->vLastAssump, Lit );
    p->pLastSolver = pSat;
    p->fBadPhaseProbe = p->nBadPhaseConfs > 0;
    if ( pMapped && atoi(pMapped) > 0 && !p->pPars->fUseAbs && !p->pInitSat && p->GuardLit < 0 &&
         !p->pPars->nPropLimit && !p->propLimit && !p->propSlice && !p->nSharedSlots &&
         !p->nBadRootMode && !p->fBadPhaseProbe && !pPrefix &&
         !Aig_ManBufNum(p->pAig) && !Aig_ManExorNum(p->pAig) )
        RetValue = Pdr2_ManSolveBadMapped(p, pSat, Lit, Abc_MinInt(60, atoi(pMapped)), Request);
    else
        RetValue = Pdr2_ManSatSolve( p, pSat, &Lit, 1, NULL, NULL, 0, 1, 0, Request );
    if ( pSat == p->pBadRoot && Gip_OptionGet("PDR2_BADROOT_CHECK") )
        Pdr2_ManCheckSharedQuery(p, Pdr2_ManLevel(p), RetValue, &Lit, 1, NULL, NULL, 0);
    p->fBadPhaseProbe = 0;
    Pdr2_SolverActual(pSat)->pDumpFile = NULL;
    if ( RetValue == GIP_SAT )
        return 1;
    if ( RetValue == GIP_UNSAT )
        return 0;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Checks if the cube is excluded by the clauses of the frame.]

  Description [Returns 1 if the frame's lemmas exclude the cube (UNSAT),
  0 if some state of the frame is in the cube, -1 if undecided.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManSolveContained( Pdr2_Man_t * p, Gip_Solver_t * pSat, Pdr2_Cube_t * pCube )
{
    int i, RetValue;
    Vec_IntClear( p->vAssump );
    for ( i = 0; i < pCube->nLits; i++ )
        Vec_IntPush( p->vAssump, Pdr2_LitLo(p, pCube->Lits[i]) );
    Vec_IntClear( p->vLastAssump );
    Vec_IntAppend( p->vLastAssump, p->vAssump );
    p->pLastSolver = pSat;
    RetValue = Pdr2_ManSatSolve( p, pSat, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump), NULL, NULL, 0, 16, 0, GIP_JFTR_NONE );
    if ( RetValue == GIP_UNSAT )
        return 1;
    if ( RetValue == GIP_SAT )
        return 0;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Extracts the inductive core after an UNSAT relative query.]

  Description [Keeps the literals of the last query whose next-state
  assumption is in the UNSAT core, in the query order. If the result
  intersects the initial states, the first literal contradicting them is
  added back. Returns 0 if no such literal exists.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManInductiveCore( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCore )
{
    int i, Lit, fNonInit = 0, iNew = -1;
    assert( pSat == p->pLastSolver );
    pSat = Pdr2_SolverActual( pSat );
    Vec_IntClear( vCore );
    Vec_IntForEachEntry( p->vRelInd, Lit, i )
        if ( Gip_SolverUnsatHas( pSat, Pdr2_LitLi(p, Lit) ) )
        {
            Vec_IntPush( vCore, Lit );
            if ( Pdr2_ManLitIsNonInit(p, Lit) )
                fNonInit = 1;
        }
    if ( fNonInit )
        return 1;
    if ( p->pInitSat )
    {
        if ( Pdr2_ManInitialQuery(p,Vec_IntArray(vCore),Vec_IntSize(vCore)) == GIP_UNSAT ) return 1;
        if ( Pdr2_ManInitialQuery(p,Vec_IntArray(p->vRelInd),Vec_IntSize(p->vRelInd)) != GIP_UNSAT ) return 0;
        // Unite the independent initial-exclusion core with the relative
        // induction core, preserving the original query's literal order.
        Vec_IntClear(vCore);
        Vec_IntForEachEntry(p->vRelInd,Lit,i)
            if ( Gip_SolverUnsatHas(pSat,Pdr2_LitLi(p,Lit)) ||
                 Gip_SolverUnsatHas(p->pInitSat,Pdr2_LitLo(p,Lit)) ) Vec_IntPush(vCore,Lit);
        return 1;
    }
    Vec_IntForEachEntry( p->vRelInd, Lit, i )
        if ( Pdr2_ManLitIsNonInit(p, Lit) )
        {
            iNew = i;
            break;
        }
    if ( iNew == -1 )
        return 0;
    Vec_IntClear( vCore );
    Vec_IntForEachEntry( p->vRelInd, Lit, i )
        if ( i == iNew || Gip_SolverUnsatHas( pSat, Pdr2_LitLi(p, Lit) ) )
            Vec_IntPush( vCore, Lit );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Collects the relevant input or register indices for sparse lifting.]

  Description []

***********************************************************************/
// Preserve the original CI order, since flip-to-none and assumption order affect
// the trajectory. Fall back to the linear scan when a sparse scan plus sorting
// is unlikely to save work. The trail may contain variables flipped to NONE;
// the caller still checks their current model values.
static Vec_Int_t * Pdr2_ManLiftCis( Pdr2_Man_t * p, Vec_Int_t * vVars, int fLits, int fInputs )
{
    int i, v, Ci, nCis = fInputs ? p->nPis : p->nRegs;
    if ( !p->pPars->fSparseLift || !p->pVar2Ci || Vec_IntSize(vVars) >= nCis / 4 )
        return NULL;
    Vec_IntClear( p->vLiftCis );
    Vec_IntForEachEntry( vVars, v, i )
    {
        Ci = p->pVar2Ci[fLits ? Abc_Lit2Var(v) : v];
        if ( Ci < 0 || (fInputs ? Ci >= p->nPis : Ci < p->nPis) )
            continue;
        Vec_IntPush( p->vLiftCis, fInputs ? Ci : Ci - p->nPis );
    }
    Vec_IntSort( p->vLiftCis, 0 );
    p->nSparseScans++;
    return p->vLiftCis;
}

/**Function*************************************************************

  Synopsis    [Saves a predecessor and successor that refute a literal-drop attempt.]

  Description []

***********************************************************************/
void Pdr2_ManMicCexStore( Pdr2_Man_t * p, Gip_Solver_t * pSat, int Frame )
{
    int i, Slot = p->iMicCexNext++ & 127, w = Slot >> 6;
    word Bit = (word)1 << (Slot & 63);
    pSat = Pdr2_SolverActual( pSat );
    assert( !p->fAbsActive );
    for ( i = 0; i < p->nRegs; i++ )
    {
        word * b = p->pMicCexBits + 8 * i;
        int S = pSat->pValue[p->pLoVar[i]], T = Gip_SolverLitValue(pSat, p->pLiLit[i]);
        b[w] = (b[w] & ~Bit) | (S == GIP_TRUE ? Bit : 0);
        b[2+w] = (b[2+w] & ~Bit) | (S != GIP_NONE ? Bit : 0);
        b[4+w] = (b[4+w] & ~Bit) | (T == GIP_TRUE ? Bit : 0);
        b[6+w] = (b[6+w] & ~Bit) | (T != GIP_NONE && Gip_DomainHas(&pSat->Domain, Abc_Lit2Var(p->pLiLit[i])) ? Bit : 0);
    }
    p->MicCexFrame[Slot] = Frame;
    p->MicCexLive[w] |= Bit;
    p->nMicCexStores++;
}

/**Function*************************************************************

  Synopsis    [Rechecks a cached generalization witness against the current frame.]

  Description []

***********************************************************************/
static void Pdr2_ManMicCexCheck( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube, int Slot )
{
    Gip_Solver_t * pCheck = Pdr2_ManNewSolver( p, Frame == 0 ? 1 : 0 );
    Pdr2_Lem_t * pLem;
    Vec_Int_t * vAssump = Vec_IntAlloc( p->nRegs + Vec_IntSize(vCube) );
    int i, k, Lit, Ret, w = Slot >> 6;
    word Bit = (word)1 << (Slot & 63);
    if ( Frame > 0 )
    {
        Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
            Pdr2_ManSolverAddLemma( p, pCheck, pLem->pCube, pLem->Id );
        for ( k = Frame; k < Pdr2_ManFrameNum(p); k++ )
            Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
                Pdr2_ManSolverAddLemma( p, pCheck, pLem->pCube, pLem->Id );
    }
    // Add directly: the diagnostic must not clear or mutate the witness pool.
    if ( p->pPars->fPropHyp && Frame < Pdr2_ManLevel(p) )
    {
        Lit = Abc_Var2Lit( p->VarBad, 1 );
        Gip_SolverAddLemmaId( pCheck, &Lit, 1, p->IdProp );
    }
    for ( i = 0; i < p->nRegs; i++ )
    {
        word * b = p->pMicCexBits + 8 * i;
        if ( b[2+w] & Bit ) Vec_IntPush( vAssump, Abc_Var2Lit(p->pLoVar[i], !(b[w] & Bit)) );
    }
    Vec_IntForEachEntry( vCube, Lit, i ) Vec_IntPush( vAssump, Pdr2_LitLi(p, Lit) );
    Ret = Gip_SolverSolve( pCheck, Vec_IntArray(vAssump), Vec_IntSize(vAssump), NULL, NULL, 0, -1 );
    if ( Ret != GIP_SAT ) Abc_Print( 1, "MIC WITNESS CHECK FAILED: frame %d, result %d.\n", Frame, Ret );
    assert( Ret == GIP_SAT );
    Vec_IntFree( vAssump );
    Gip_SolverFree( pCheck );
}

/**Function*************************************************************

  Synopsis    [Searches stored counterexamples for a witness against a candidate cube.]

  Description []

***********************************************************************/
int Pdr2_ManMicCexFind( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube, char * pKeep )
{
    int w, i, s, Lit;
    p->nMicCexChecks++;
    for ( w = 0; w < 2; w++ )
    {
        word Match = p->MicCexLive[w], FailsKeep = 0;
        Vec_IntForEachEntry( vCube, Lit, i )
        {
            word * b = p->pMicCexBits + 8 * Abc_Lit2Var(Lit);
            Match &= b[6+w] & (Abc_LitIsCompl(Lit) ? ~b[4+w] : b[4+w]);
            if ( pKeep[Lit] ) FailsKeep |= b[2+w] & (Abc_LitIsCompl(Lit) ? b[w] : ~b[w]);
            if ( !Match ) break;
        }
        Match &= FailsKeep;
        for ( s = 0; Match && s < 64; s++ )
            if ( (Match & ((word)1 << s)) && p->MicCexFrame[64*w+s] == Frame )
            {
                p->nMicCexHits++;
                if ( Gip_OptionGet("PDR2_MICCEX_CHECK") ) Pdr2_ManMicCexCheck( p, Frame, vCube, 64*w+s );
                return 1;
            }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Selects a cache bucket for a lifting target.]

  Description []

***********************************************************************/
static unsigned Pdr2_ManLiftMemoBucket( Pdr2_Man_t * p )
{
    unsigned Hash = 2166136261u;
    int i, Lit;
    Vec_IntForEachEntry( p->vLiftMemoKey, Lit, i )
        Hash = (Hash ^ (unsigned)Lit) * 16777619u;
    return Hash & 255;
}

/**Function*************************************************************

  Synopsis    [Looks up a previously justified lifting cube.]

  Description []

***********************************************************************/
static Pdr2_LiftMemo_t * Pdr2_ManLiftMemoFind( Pdr2_Man_t * p, Gip_Solver_t * pModel )
{
    unsigned Bucket;
    int i, j;
    Vec_IntClear( p->vLiftMemoKey );
    Vec_IntAppend( p->vLiftMemoKey, p->vLastAssump );
    Vec_IntSort( p->vLiftMemoKey, 0 );
    Vec_IntClear( p->vLiftMemoCore );
    Bucket = Pdr2_ManLiftMemoBucket( p );
    p->nLiftMemoChecks++;
    for ( i = 0; i < 16; i++ )
    {
        Pdr2_LiftMemo_t * pMemo = p->pLiftMemo[16 * Bucket + i];
        if ( !pMemo || pMemo->nKey != Vec_IntSize(p->vLiftMemoKey) ||
             memcmp(pMemo->Lits, Vec_IntArray(p->vLiftMemoKey), sizeof(int) * pMemo->nKey) )
            continue;
        for ( j = 0; j < pMemo->nCore; j++ )
            if ( Gip_SolverLitValue(pModel, pMemo->Lits[pMemo->nKey + j]) != GIP_TRUE )
                break;
        if ( j == pMemo->nCore )
            return pMemo;
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Saves the current target with its justified predecessor and input cube.]

  Description []

***********************************************************************/
static void Pdr2_ManLiftMemoSave( Pdr2_Man_t * p )
{
    int Bucket = Pdr2_ManLiftMemoBucket( p );
    int Slot = 16 * Bucket + (p->pLiftMemoNext[Bucket]++ & 15);
    int nKey = Vec_IntSize(p->vLiftMemoKey), nCore = Vec_IntSize(p->vLiftMemoCore);
    size_t Bytes = sizeof(Pdr2_LiftMemo_t) + sizeof(int) * (nKey + nCore);
    Pdr2_LiftMemo_t * pMemo = p->pLiftMemo[Slot];
    if ( pMemo )
    {
        p->nLiftMemoBytes -= sizeof(Pdr2_LiftMemo_t) + sizeof(int) * (pMemo->nKey + pMemo->nCore);
        ABC_FREE( pMemo );
        p->pLiftMemo[Slot] = NULL;
    }
    if ( p->nLiftMemoBytes + Bytes > ((ABC_INT64_T)128 << 20) ) return;
    pMemo = (Pdr2_LiftMemo_t *)ABC_ALLOC( char, Bytes );
    pMemo->nKey = nKey;
    pMemo->nCore = nCore;
    if ( nKey ) memcpy( pMemo->Lits, Vec_IntArray(p->vLiftMemoKey), sizeof(int) * nKey );
    if ( nCore ) memcpy( pMemo->Lits + nKey, Vec_IntArray(p->vLiftMemoCore), sizeof(int) * nCore );
    p->pLiftMemo[Slot] = pMemo;
    p->nLiftMemoBytes += Bytes;
    p->nLiftMemoStores++;
}

/**Function*************************************************************

  Synopsis    [Independently verifies the cached predecessor implication.]

  Description []

***********************************************************************/
static void Pdr2_ManLiftMemoCheck( Pdr2_Man_t * p, Pdr2_LiftMemo_t * pMemo )
{
    Gip_Solver_t * pCheck = Pdr2_ManNewSolver( p, PDR2_SOLVER_UNRESTRICTED );
    Vec_Int_t * vClause = Vec_IntAlloc( pMemo->nKey );
    int i, Ret, * pClause, nClause;
    for ( i = 0; i < pMemo->nKey; i++ )
        Vec_IntPush( vClause, Abc_LitNot(pMemo->Lits[i]) );
    pClause = Vec_IntArray( vClause );
    nClause = Vec_IntSize( vClause );
    Ret = Gip_SolverSolve( pCheck, pMemo->Lits + pMemo->nKey, pMemo->nCore, &pClause, &nClause, 1, -1 );
    if ( Ret != GIP_UNSAT ) Abc_Print( 1, "LIFT MEMO CHECK FAILED: result %d.\n", Ret );
    assert( Ret == GIP_UNSAT );
    Vec_IntFree( vClause );
    Gip_SolverFree( pCheck );
}

/**Function*************************************************************

  Synopsis    [Follows the functional CNF to justify targets with circuit inputs.]

  Description []

***********************************************************************/
// Justify each target through the immutable functional CNF. For a gate's
// model value, clauses not satisfied by that output need one true fanin.
// Recursively justifying those fanins leaves only CI premises. The resulting
// cube contains the source model and forces every target for all completions
// of its omitted CIs. Frame clauses and learned clauses are not needed here.
static int Pdr2_ManCnfJustify( Pdr2_Man_t * p, Gip_Solver_t * pModel, Vec_Int_t * vCube, Vec_Int_t * vInputs )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    Vec_Int_t * vWork = p->vCnfJustWork;
    abctime Start = Abc_Clock();
    int i, Var, Lit, Ci, Obj, c, Value, fOk = 1;
    Vec_IntClear( vWork );
    Vec_IntForEachEntry( p->vLastAssump, Lit, i )
    {
        Var = Abc_Lit2Var(Lit);
        if ( Gip_SolverLitValue(pModel, Lit) != GIP_TRUE ) { fOk = 0; break; }
        if ( !p->pCnfJustMark[Var] )
        {
            p->pCnfJustMark[Var] = 1;
            Vec_IntPush( vWork, Var );
        }
    }
    for ( i = 0; fOk && i < Vec_IntSize(vWork); i++ )
    {
        if ( !(i & 1023) && Pdr2_ManPastDeadline(p) ) { fOk = 0; break; }
        Var = Vec_IntEntry(vWork, i);
        Value = pModel->pValue[Var];
        assert( Value != GIP_NONE );
        if ( Var == p->pCtx->varConst )
        {
            if ( Value != GIP_TRUE ) fOk = 0;
            continue;
        }
        Ci = p->pVar2Ci[Var];
        if ( Ci >= 0 )
        {
            if ( Ci < p->nPis ) Vec_IntPush(vInputs, Abc_Var2Lit(Ci, Value == GIP_FALSE));
            else Vec_IntPush(vCube, Abc_Var2Lit(Ci - p->nPis, Value == GIP_FALSE));
            continue;
        }
        Obj = p->pCtx->pVar2Obj ? p->pCtx->pVar2Obj[Var] : Var;
        if ( pCnf->pObj2Count[Obj] <= 0 ) { fOk = 0; break; }
        for ( c = pCnf->pObj2Clause[Obj]; c < pCnf->pObj2Clause[Obj] + pCnf->pObj2Count[Obj]; c++ )
        {
            int * pLit, Best = -1, ScoreBest = -0x7fffffff;
            for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
            {
                int v = Abc_Lit2Var(*pLit), Score, Id;
                if ( Gip_SolverLitValue(pModel, *pLit) != GIP_TRUE ) continue;
                if ( p->pCnfJustMark[v] ) { Best = v; break; }
                Id = p->pCtx->pVar2Obj ? p->pCtx->pVar2Obj[v] : v;
                // Existing premises cost nothing; next prefer PIs and shallow
                // gates to keep the state part of the justification short.
                Score = p->pVar2Ci[v] >= 0 && p->pVar2Ci[v] < p->nPis ? 1000000 :
                        -(int)Aig_ObjLevel(Aig_ManObj(p->pAig, Id));
                if ( Best < 0 || Score > ScoreBest ) { Best = v; ScoreBest = Score; }
            }
            if ( Best < 0 ) { fOk = 0; break; }
            if ( !p->pCnfJustMark[Best] )
            {
                p->pCnfJustMark[Best] = 1;
                Vec_IntPush(vWork, Best);
            }
        }
    }
    p->nCnfJustNodes += Vec_IntSize(vWork);
    Vec_IntForEachEntry(vWork, Var, i) p->pCnfJustMark[Var] = 0;
    if ( fOk )
    {
        Vec_IntSort(vCube, 0);
        Vec_IntSort(vInputs, 0);
        p->nCnfJustHits++;
    }
    else
    {
        Vec_IntClear(vCube);
        Vec_IntClear(vInputs);
        p->nCnfJustFails++;
    }
    p->timeCnfJust += Abc_Clock() - Start;
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Checks a justified input cube against a fresh SAT query.]

  Description []

***********************************************************************/
static void Pdr2_ManCnfJustCheck( Pdr2_Man_t * p, Vec_Int_t * vCube, Vec_Int_t * vInputs )
{
    Gip_Solver_t * pCheck = Pdr2_ManNewSolver(p, PDR2_SOLVER_UNRESTRICTED);
    Vec_Int_t * vPremise = Vec_IntAlloc(Vec_IntSize(vCube) + Vec_IntSize(vInputs));
    int i, Lit, Ret, * pClause = Vec_IntArray(p->vLift3), nClause = Vec_IntSize(p->vLift3);
    Vec_IntForEachEntry(vCube, Lit, i) Vec_IntPush(vPremise, Pdr2_LitLo(p, Lit));
    Vec_IntForEachEntry(vInputs, Lit, i) Vec_IntPush(vPremise, Abc_Var2Lit(p->pPiVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit)));
    Ret = Gip_SolverSolve(pCheck, Vec_IntArray(vPremise), Vec_IntSize(vPremise), &pClause, &nClause, 1, -1);
    if ( Ret != GIP_UNSAT ) Abc_Print(1, "CNF JUSTIFICATION CHECK FAILED: result %d.\n", Ret);
    assert(Ret == GIP_UNSAT);
    Vec_IntFree(vPremise);
    Gip_SolverFree(pCheck);
}

/**Function*************************************************************

  Synopsis    [Lifts the predecessor state found by the last SAT query.]

  Description [The last query was SAT on p->pLastSolver with assumptions
  p->vLastAssump (next-state literals of a cube, or the bad literal).
  The model's inputs and the latches in the cone of the assumptions form
  a state leading to the target. The latch literals that can be
  unassigned without breaking any clause are dropped first (flip to
  none); then the lift solver computes a minimal subset of latch
  literals that, with the inputs, still implies the target (UNSAT core
  of "state and inputs and not target"). With fStrengthen, this is
  repeated with different literal orders while the cube shrinks.
  Returns the lifted cube (flop literals) and the input literals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManGetPred( Pdr2_Man_t * p, int fStrengthen, Vec_Int_t * vCube, Vec_Int_t * vInputs )
{
    Gip_Solver_t * pModel = Pdr2_SolverActual( p->pLastSolver );
    Vec_Int_t * vCis;
    abctime clk = Abc_Clock();
    int i, k, j, nCis, Lit, Var, Value, Iter, nOld, RetValue, nCone = 0, nFlip, nSim;
    int * pCls, nCls, fMemoProved = 0, fCnfJust = 0;
    if ( p->GuardLo >= 0 ) Vec_IntPushUnique(p->vLastAssump, p->GuardLo);
    if ( p->GuardLi >= 0 ) Vec_IntPushUnique(p->vLastAssump, p->GuardLi);
    assert( !pModel->Jftr.fEarly || pModel->Jftr.fWalkClosed );
    assert( !pModel->Jftr.fEarly || (!p->nLiftMemoMode && !p->nCnfJustMode) );
    Vec_IntClear( vCube );
    Vec_IntClear( vInputs );
    if ( p->nLiftMemoMode )
    {
        Pdr2_LiftMemo_t * pMemo = Pdr2_ManLiftMemoFind( p, pModel );
        if ( pMemo )
        {
            p->nLiftMemoHits++;
            p->nLiftMemoWeakHits += !fStrengthen;
            if ( Gip_OptionGet("PDR2_LIFTMEMO_CHECK") ) Pdr2_ManLiftMemoCheck( p, pMemo );
            if ( p->nLiftMemoMode >= 2 && (!fStrengthen || p->nLiftMemoMode == 3) )
            {
                for ( i = 0; i < pMemo->nCore; i++ )
                {
                    int Lit = pMemo->Lits[pMemo->nKey + i], Ci = p->pVar2Ci[Abc_Lit2Var(Lit)];
                    assert( Ci >= 0 );
                    if ( Ci < p->nPis )
                        Vec_IntPush( vInputs, Abc_Var2Lit(Ci, Abc_LitIsCompl(Lit)) );
                    else
                        Vec_IntPush( vCube, Abc_Var2Lit(Ci - p->nPis, Abc_LitIsCompl(Lit)) );
                }
                p->nLiftMemoReuse++;
                p->nLiftCalls++;
                p->nLiftCore += Vec_IntSize( vCube );
                clk = Abc_Clock() - clk;
                p->timeLift += clk;
                if ( fStrengthen ) p->timeGetPred += clk;
                return;
            }
        }
    }
    // the clause "not target": negation of the last assumptions
    Vec_IntClear( p->vLift3 );
    Vec_IntForEachEntry( p->vLastAssump, Lit, i )
    {
        Vec_IntPush( p->vLift3, Abc_LitNot(Lit) );
        p->pVarMark[Abc_Lit2Var(Lit)] = 1;
    }
    // Inputs outside the target cone cannot affect the lifted implication.
    // Set the lifting domain before collecting the model's input premises.
    Gip_SolverSetDomain( p->pLift, Vec_IntArray(p->vLift3), Vec_IntSize(p->vLift3) );
    if ( p->nCnfJustMode && (p->nCnfJustMode != 3 || (pModel->fInputDecisions && !pModel->fInputAbandoned)) &&
         Pdr2_ManCnfJustify(p, pModel, vCube, vInputs) )
    {
        fCnfJust = 1;
        if ( Gip_OptionGet("PDR2_CNFJUST_CHECK") ) Pdr2_ManCnfJustCheck(p, vCube, vInputs);
        Vec_IntClear(p->vLift1);
        Vec_IntForEachEntry(vInputs, Lit, i)
            Vec_IntPush(p->vLift1, Abc_Var2Lit(p->pPiVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit)));
        Vec_IntForEachEntry(p->vLastAssump, Lit, i) p->pVarMark[Abc_Lit2Var(Lit)] = 0;
        p->nLiftCalls++;
        p->nLiftCone += Vec_IntSize(vCube);
        p->nLiftFlip += Vec_IntSize(vCube);
        nCone = nFlip = Vec_IntSize(vCube);
        goto lift_ready;
    }
    // input values of the model
    Vec_IntClear( p->vLift1 );
    vCis = Pdr2_ManLiftCis( p, pModel->vTrail, 1, 1 );
    nCis = vCis ? Vec_IntSize(vCis) : p->nPis;
    for ( j = 0; j < nCis; j++ )
    {
        i = vCis ? Vec_IntEntry(vCis, j) : j;
        Value = pModel->pValue[p->pPiVar[i]];
        if ( Value == GIP_NONE )
            continue;
        p->nLiftPiBefore++;
        if ( (p->nLiftPiMode & 1) && !Gip_DomainHas(&p->pLift->Domain, p->pPiVar[i]) )
            continue;
        Vec_IntPush( p->vLift1, Abc_Var2Lit(p->pPiVar[i], Value == GIP_FALSE) );
        Vec_IntPush( vInputs, Abc_Var2Lit(i, Value == GIP_FALSE) );
    }
    // latch values of the model restricted to the cone, minus the unneeded ones
    vCis = Pdr2_ManLiftCis( p, p->pLift->Domain.Set.vSet, 0, 0 );
    nCis = vCis ? Vec_IntSize(vCis) : p->nRegs;
    for ( j = 0; j < nCis; j++ )
    {
        i = vCis ? Vec_IntEntry(vCis, j) : j;
        Var = p->pLoVar[i];
        if ( !Gip_DomainHas( &p->pLift->Domain, Var ) )
            continue;
        Value = pModel->pValue[Var];
        if ( Value == GIP_NONE )
            continue;
        p->nLiftCone++;
        nCone++;
        // (with the weakening by simulation the latches keep their model values: the cube must
        // contain the model state, or the obligation may be one the frames already exclude)
        if ( p->pPars->fLift && !p->pPars->nLiftSim && !p->pVarMark[Var] && Gip_SolverFlipToNone( pModel, Var ) )
            continue;
        Vec_IntPush( vCube, Abc_Var2Lit(i, Value == GIP_FALSE) );
    }
    p->nLiftCalls++;
    p->nLiftFlip += Vec_IntSize( vCube );
    nFlip = Vec_IntSize( vCube );
    Vec_IntForEachEntry( p->vLastAssump, Lit, i )
        p->pVarMark[Abc_Lit2Var(Lit)] = 0;
    // weakening by justification and ternary simulation
    if ( p->pPars->nLiftSim )
    {
        abctime clkSim = Abc_Clock();
        // the weakening by simulation starts from every assigned latch of the model, so that its
        // cube contains the model state (a cube outside the frame would be requeued forever);
        // the structural justification may also reach latches the targets do not depend on
        // functionally (they are outside the lifting domain, which follows the CNF): those are
        // dropped afterwards, the implication of the targets does not need them
        Vec_IntClear( vCube );
        // an early answer: the completed registers are not on the trail, so the sparse scan of the trail misses them
        vCis = pModel->Jftr.fEarly ? NULL : Pdr2_ManLiftCis( p, pModel->vTrail, 1, 0 );
        nCis = vCis ? Vec_IntSize(vCis) : p->nRegs;
        for ( j = 0; j < nCis; j++ )
        {
            i = vCis ? Vec_IntEntry(vCis, j) : j;
            Value = Pdr2_SolverCompletedValue( pModel, p->pLoVar[i] );
            if ( Value != GIP_NONE )
                Vec_IntPush( vCube, Abc_Var2Lit(i, Value == GIP_FALSE) );
        }
        Pdr2_ManSimWeaken( p, vCube, vInputs );
        p->timeLiftSim += Abc_Clock() - clkSim;
        k = 0;
        Vec_IntForEachEntry( vCube, Lit, i )
            if ( Gip_DomainHas( &p->pLift->Domain, p->pLoVar[Abc_Lit2Var(Lit)] ) )
                Vec_IntWriteEntry( vCube, k++, Lit );
        Vec_IntShrink( vCube, k );
        Vec_IntClear( p->vLift1 );
        Vec_IntForEachEntry( vInputs, Lit, i )
            Vec_IntPush( p->vLift1, Abc_Var2Lit(p->pPiVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit)) );
        // the weakened cube must agree with the model (checked, never expected to fail)
        Vec_IntForEachEntry( vCube, Lit, i )
        {
            Value = pModel->pValue[p->pLoVar[Abc_Lit2Var(Lit)]];
            if ( Value != GIP_NONE && (Value == GIP_TRUE) == Abc_LitIsCompl(Lit) )
            {
                if ( p->nLiftSimBad++ == 0 && !p->pPars->fSilent )
                    Abc_Print( 1, "Pdr2_ManGetPred(): Warning: the weakened cube disagrees with the model.\n" );
                break;
            }
        }
    }
lift_ready:
    p->nLiftSim += Vec_IntSize( vCube );
    nSim = Vec_IntSize( vCube );
    // minimal premise iterations
    pCls = Vec_IntArray( p->vLift3 );
    nCls = Vec_IntSize( p->vLift3 );
    for ( Iter = 0; Vec_IntSize(vCube) > 0 && p->pPars->nLiftIters >= 0 && p->pPars->nLiftSim != 2 && (!fCnfJust || p->nCnfJustMode != 2); Iter++ )
    {
        if ( Iter == 0 )
            Pdr2_ManSortByAct( p, vCube, 0 );
        else if ( Iter == 1 )
            Vec_IntReverseOrder( vCube );
        else
            Pdr2_ManShuffle( p, vCube );
        nOld = Vec_IntSize( vCube );
        Vec_IntClear( p->vLift2 );
        Vec_IntAppend( p->vLift2, p->vLift1 );
        Vec_IntForEachEntry( vCube, Lit, i )
            Vec_IntPush( p->vLift2, Pdr2_LitLo(p, Lit) );
        RetValue = Pdr2_ManSatSolve( p, p->pLift, Vec_IntArray(p->vLift2), Vec_IntSize(p->vLift2), &pCls, &nCls, 1, 8, 0, GIP_JFTR_NONE );
        if ( RetValue != GIP_UNSAT )
        {
            // on a timeout the current cube is kept: it still implies the target
            if ( RetValue == GIP_SAT && !p->pPars->fSilent )
                Abc_Print( 1, "Pdr2_ManGetPred(): Internal error: the lifting query is SAT.\n" );
            break;
        }
        k = 0;
        Vec_IntForEachEntry( vCube, Lit, i )
            if ( Gip_SolverUnsatHas( p->pLift, Pdr2_LitLo(p, Lit) ) )
                Vec_IntWriteEntry( vCube, k++, Lit );
        Vec_IntShrink( vCube, k );
        if ( p->nLiftPiMode & 2 )
        {
            // The same UNSAT core proves sufficiency of both the retained
            // state literals and retained inputs. Missing inputs are free.
            k = 0;
            Vec_IntForEachEntry( vInputs, Lit, i )
                if ( Gip_SolverUnsatHas(p->pLift, Abc_Var2Lit(p->pPiVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit))) )
                    Vec_IntWriteEntry( vInputs, k++, Lit );
            Vec_IntShrink( vInputs, k );
            Vec_IntClear( p->vLift1 );
            Vec_IntForEachEntry( vInputs, Lit, i )
                Vec_IntPush( p->vLift1, Abc_Var2Lit(p->pPiVar[Abc_Lit2Var(Lit)], Abc_LitIsCompl(Lit)) );
        }
        if ( p->nLiftMemoMode )
        {
            Vec_IntClear( p->vLiftMemoCore );
            Vec_IntForEachEntry( p->vLift2, Lit, i )
                if ( Gip_SolverUnsatHas(p->pLift, Lit) )
                {
                    assert( p->pVar2Ci[Abc_Lit2Var(Lit)] >= 0 );
                    Vec_IntPush( p->vLiftMemoCore, Lit );
                }
            fMemoProved = 1;
        }
        if ( Vec_IntSize(vCube) == nOld || !fStrengthen )
            break;
        if ( p->pPars->nLiftIters && Iter + 1 >= p->pPars->nLiftIters )
            break;
    }
    Gip_SolverUnsetDomain( p->pLift );
    p->nLiftPiAfter += Vec_IntSize(vInputs);
    if ( fMemoProved ) Pdr2_ManLiftMemoSave( p );
    p->nLiftCore += Vec_IntSize( vCube );
    if ( p->pPars->fVeryVerbose && !p->pPars->fSilent && fStrengthen && (p->nLiftCalls % 50) == 0 )
        Abc_Print( 1, "Lift %d: target %d literals, cone %d, after flipping %d, after simulation %d, after the SAT core %d.\n",
            (int)p->nLiftCalls, Vec_IntSize(p->vLastAssump), nCone, nFlip, nSim, Vec_IntSize(vCube) );
    // (the lifting of CTG predecessors is counted in the MIC time, that of the propagation in
    // the propagation times; timeLift covers all of them)
    clk = Abc_Clock() - clk;
    p->timeLift += clk;
    if ( fStrengthen )
        p->timeGetPred += clk;
}

/**Function*************************************************************

  Synopsis    [Fixes the decision domain of a solver for a MIC round.]

  Description [The domain is the cone of the cube's current- and
  next-state variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManSetMicDomain( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube )
{
    int i, Lit;
    Vec_IntClear( p->vLem );
    Vec_IntForEachEntry( vCube, Lit, i )
    {
        Vec_IntPush( p->vLem, Pdr2_LitLo(p, Lit) );
        Vec_IntPush( p->vLem, Pdr2_LitLi(p, Lit) );
    }
    if ( pSat->pShared )
    {
        Vec_IntFreeP( &pSat->vSharedDomain );
        pSat->vSharedDomain = Vec_IntDup( p->vLem );
    }
    else
        Gip_SolverSetDomain( pSat, Vec_IntArray(p->vLem), Vec_IntSize(p->vLem) );
}
void Pdr2_ManUnsetMicDomain( Pdr2_Man_t * p, Gip_Solver_t * pSat )
{
    if ( pSat->pShared )
    {
        Vec_IntFreeP( &pSat->vSharedDomain );
        Gip_SolverUnsetDomain( pSat->pShared );
    }
    else
        Gip_SolverUnsetDomain( pSat );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
