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

// runs one SAT query and accounts for its cost (the propagation count is the deterministic
// measure of work used by the level restarts)
static inline int Pdr2_ManSatSolve( Pdr2_Man_t * p, Gip_Solver_t * pSat, int * pLits, int nLits, int ** pCst, int * nCst, int nC )
{
    ABC_INT64_T nProps = pSat->Stats.nPropagations, nConfs = pSat->Stats.nConflicts;
    ABC_INT64_T nCleanL = pSat->Stats.nCleanL, nCleanLNone = pSat->Stats.nCleanLNone;
    abctime timeCleanL = pSat->Stats.timeCleanL;
    int RetValue;
    pSat->nConfLimit = 0;
    pSat->TimeLimit  = p->timeLimit;
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
    RetValue = Gip_SolverSolve( pSat, pLits, nLits, pCst, nCst, nC, -1 );
    if ( RetValue == GIP_UNDEF )
    {
        p->fQueryCut = 1;
        p->nQueryCuts += pSat->nPropLimit > 0 && pSat->Stats.nPropagations >= pSat->nPropLimit;
    }
    p->nProps     += pSat->Stats.nPropagations - nProps;
    p->nConflicts += pSat->Stats.nConflicts - nConfs;
    p->nCleanL    += pSat->Stats.nCleanL - nCleanL;
    p->nCleanLNone += pSat->Stats.nCleanLNone - nCleanLNone;
    p->timeCleanL += pSat->Stats.timeCleanL - timeCleanL;
    if ( RetValue == GIP_UNSAT )
        p->iCoreFrame = pSat->iCoreFrame;
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a solver over the transition relation.]

  Description [Type 0: plain. Type 1: with the initial states as unit
  clauses (the flops with a defined initial value). Type 2: with the
  lemmas of frame infinity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gip_Solver_t * Pdr2_ManNewSolver( Pdr2_Man_t * p, int Type )
{
    Gip_Solver_t * pSat = Gip_SolverNew( p->pCtx );
    pSat->fFastClean = 1;
    pSat->fCleanSkip = 1;
    Gip_SolverSetLemFrames( pSat, p->vLemFrame );
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
    }
    else if ( Type == 2 )
    {
        Pdr2_Lem_t * pLem;
        int i;
        Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
            Pdr2_ManSolverAddLemma( p, pSat, pLem->pCube, pLem->Id );
    }
    return pSat;
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
    Vec_IntClear( p->vLem );
    for ( i = 0; i < pCube->nLits; i++ )
        Vec_IntPush( p->vLem, Abc_LitNot( Pdr2_LitLo(p, pCube->Lits[i]) ) );
    Gip_SolverAddLemmaId( pSat, Vec_IntArray(p->vLem), Vec_IntSize(p->vLem), Id );
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
    Gip_SolverReset( pSat );
    if ( Gip_SolverLitValue( pSat, Lit ) == GIP_TRUE )
        return;
    assert( Gip_SolverLitValue( pSat, Lit ) == GIP_NONE );
    Gip_SolverAddClauseTag( pSat, &Lit, 1, GIP_CLA_LEMMA, ((unsigned)p->IdProp << 1) | 1 );
    assert( !pSat->fTrivialUnsat );
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
int Pdr2_ManSolveRelative( Pdr2_Man_t * p, Gip_Solver_t * pSat, Vec_Int_t * vCube, int fStrengthen, Vec_Int_t * vCstCls )
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
    RetValue = Pdr2_ManSatSolve( p, pSat, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump), pCst, nCst, nC );
    if ( RetValue == GIP_UNSAT )
        return 1;
    if ( RetValue == GIP_SAT )
        return 0;
    return -1;
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
    Vec_IntClear( p->vLastAssump );
    Vec_IntPush( p->vLastAssump, Lit );
    p->pLastSolver = pSat;
    RetValue = Pdr2_ManSatSolve( p, pSat, &Lit, 1, NULL, NULL, 0 );
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
    RetValue = Pdr2_ManSatSolve( p, pSat, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump), NULL, NULL, 0 );
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
    Gip_Solver_t * pModel = p->pLastSolver;
    abctime clk = Abc_Clock();
    int i, k, Lit, Var, Value, Iter, nOld, RetValue, nCone = 0, nFlip, nSim;
    int * pCls, nCls;
    Vec_IntClear( vCube );
    Vec_IntClear( vInputs );
    // the clause "not target": negation of the last assumptions
    Vec_IntClear( p->vLift3 );
    Vec_IntForEachEntry( p->vLastAssump, Lit, i )
    {
        Vec_IntPush( p->vLift3, Abc_LitNot(Lit) );
        p->pVarMark[Abc_Lit2Var(Lit)] = 1;
    }
    // input values of the model
    Vec_IntClear( p->vLift1 );
    for ( i = 0; i < p->nPis; i++ )
    {
        Value = pModel->pValue[p->pPiVar[i]];
        if ( Value == GIP_NONE )
            continue;
        Vec_IntPush( p->vLift1, Abc_Var2Lit(p->pPiVar[i], Value == GIP_FALSE) );
        Vec_IntPush( vInputs, Abc_Var2Lit(i, Value == GIP_FALSE) );
    }
    // the decision domain of the lift solver is the cone of the target
    Gip_SolverSetDomain( p->pLift, Vec_IntArray(p->vLift3), Vec_IntSize(p->vLift3) );
    // latch values of the model restricted to the cone, minus the unneeded ones
    for ( i = 0; i < p->nRegs; i++ )
    {
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
        for ( i = 0; i < p->nRegs; i++ )
        {
            Value = pModel->pValue[p->pLoVar[i]];
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
                if ( p->nLiftSimBad++ == 0 )
                    Abc_Print( 1, "Pdr2_ManGetPred(): Warning: the weakened cube disagrees with the model.\n" );
                break;
            }
        }
    }
    p->nLiftSim += Vec_IntSize( vCube );
    nSim = Vec_IntSize( vCube );
    // minimal premise iterations
    pCls = Vec_IntArray( p->vLift3 );
    nCls = Vec_IntSize( p->vLift3 );
    for ( Iter = 0; Vec_IntSize(vCube) > 0 && p->pPars->nLiftIters >= 0 && p->pPars->nLiftSim != 2; Iter++ )
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
        RetValue = Pdr2_ManSatSolve( p, p->pLift, Vec_IntArray(p->vLift2), Vec_IntSize(p->vLift2), &pCls, &nCls, 1 );
        if ( RetValue != GIP_UNSAT )
        {
            // on a timeout the current cube is kept: it still implies the target
            if ( RetValue == GIP_SAT )
                Abc_Print( 1, "Pdr2_ManGetPred(): Internal error: the lifting query is SAT.\n" );
            break;
        }
        k = 0;
        Vec_IntForEachEntry( vCube, Lit, i )
            if ( Gip_SolverUnsatHas( p->pLift, Pdr2_LitLo(p, Lit) ) )
                Vec_IntWriteEntry( vCube, k++, Lit );
        Vec_IntShrink( vCube, k );
        if ( Vec_IntSize(vCube) == nOld || !fStrengthen )
            break;
        if ( p->pPars->nLiftIters && Iter + 1 >= p->pPars->nLiftIters )
            break;
    }
    Gip_SolverUnsetDomain( p->pLift );
    p->nLiftCore += Vec_IntSize( vCube );
    if ( p->pPars->fVeryVerbose && fStrengthen && (p->nLiftCalls % 50) == 0 )
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
    Gip_SolverSetDomain( pSat, Vec_IntArray(p->vLem), Vec_IntSize(p->vLem) );
}
void Pdr2_ManUnsetMicDomain( Pdr2_Man_t * p, Gip_Solver_t * pSat )
{
    Gip_SolverUnsetDomain( pSat );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
