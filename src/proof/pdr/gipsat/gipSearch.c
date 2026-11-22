/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#include <math.h>
#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

// internal search result: the per-round conflict budget was exhausted
#define GIP_RESTART (-2)

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void Gip_SolverNewLevel( Gip_Solver_t * p )
{
    Vec_IntPush( p->vPosInTrail, Vec_IntSize(p->vTrail) );
}

/**Function*************************************************************

  Synopsis    [Reconsiders deferred decisions when watched clauses can become active.]

  Description []

***********************************************************************/
// A skipped variable stays on this list until backtracking. New watches wake
// individual variables; backtracking wakes all of them because satisfied
// clauses can lose their satisfying assignment. No clause is removed.
void Gip_SolverWakeSkipped( Gip_Solver_t * p, int fVsids )
{
    int Var;
    if ( !p->fJustify ) return;
    while ( Vec_IntSize(p->vJustSkip) )
    {
        Var = Vec_IntPop( p->vJustSkip );
        if ( fVsids && p->pValue[Var] == GIP_NONE && Gip_DomainHas(&p->Domain, Var) )
            Gip_VsidsPush( &p->Vsids, Var );
        p->pJustSkip[Var] = 0;
    }
}

/**Function*************************************************************

  Synopsis    [Tests whether a clause already holds or lies outside the query domain.]

  Description []

***********************************************************************/
static int Gip_SolverClauseSatisfiedOrOutside( Gip_Solver_t * p, int Cref )
{
    int i, Lit, * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    int nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    for ( i = 0; i < nLits; i++ )
    {
        Lit = pLits[i];
        if ( Gip_SolverLitValue(p, Lit) == GIP_TRUE ||
             (Gip_SolverLitValue(p, Lit) == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(Lit))) )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks whether a variable's watched clauses still require a decision.]

  Description []

***********************************************************************/
int Gip_SolverCanSkipDecision( Gip_Solver_t * p, int Var )
{
    int k, i;
    p->nJustChecks++;
    for ( k = 0; k < 2; k++ )
    {
        Gip_WVec_t * pW = &p->pWatchers[2*Var+k];
        for ( i = 0; i < pW->nSize; i++ )
            if ( Gip_SolverLitValue(p, pW->pArray[i].blocker) != GIP_TRUE &&
                 !Gip_SolverClauseSatisfiedOrOutside(p, Gip_WatchRef(pW->pArray[i].clause)) )
                return 0;
    }
    if ( !p->pJustSkip[Var] )
        Vec_IntPush( p->vJustSkip, Var );
    p->pJustSkip[Var] = 1;
    p->nJustSkipped++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks that the returned partial assignment justifies the query.]

  Description []

***********************************************************************/
void Gip_SolverCheckPartialModel( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    Vec_Int_t * vLists[4] = { p->Cdb.vTrans, p->Cdb.vLemmas, p->Cdb.vLearnt, p->Cdb.vTemp };
    int k, i, Cref;
    for ( i = 0; i < nAssump; i++ )
        assert( Gip_SolverLitValue(p, pAssump[i]) == GIP_TRUE );
    for ( k = 0; k < 4; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                assert( Gip_SolverClauseSatisfiedOrOutside(p, Cref) );
}

/**Function*************************************************************

  Synopsis    [Backtracks to the given level, saving phases.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverBacktrack( Gip_Solver_t * p, int Level, int fVsids )
{
    if ( Gip_SolverLevelOf(p) <= Level )
    {
        Gip_SolverWakeSkipped( p, fVsids );
        return;
    }
    if ( p->Jftr.nConfLimit )
        Gip_SolverJftrBacktrack( p, Level );
    // the jftr mode does not consume the decision queue, so nothing is put back
    if ( p->Jftr.fActive )
        fVsids = 0;
    while ( Vec_IntSize(p->vTrail) > Vec_IntEntry(p->vPosInTrail, Level) )
    {
        int Lit = Vec_IntPop( p->vTrail );
        int Var = Gip_LitVar( Lit );
        Gip_SolverSetNone( p, Var );
        if ( fVsids )
            Gip_VsidsPush( &p->Vsids, Var );
        if ( !p->Jftr.fActive )   // the jftr part of a solve leaves the saved phases alone
            p->pPhase[Var] = (char)(1 ^ Gip_LitCompl(Lit));
    }
    p->nPropagated = Vec_IntEntry( p->vPosInTrail, Level );
    Vec_IntShrink( p->vPosInTrail, Level );
    Gip_SolverWakeSkipped( p, fVsids );
}

/**Function*************************************************************

  Synopsis    [One restart round of CDCL search.]

  Description [Returns GIP_SAT/GIP_UNSAT when decided, GIP_RESTART when
  the per-round conflict budget (noc) is exhausted, GIP_UNDEF when a
  global limit (conflicts/time) canceled the solve.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gip_SolverSearch( Gip_Solver_t * p, int * pAssump, int nAssump, double noc )
{
    double numConflict = 0.0;
    while ( 1 )
    {
        int Conflict = Gip_SolverPropagate( p );
        if ( Conflict != GIP_CREF_NONE )
        {
            int btl;
            numConflict += 1.0;
            p->Stats.nConflicts++;
            if ( Gip_SolverLevelOf(p) == 0 )
            {
                Gip_LitSetClear( &p->UnsatCore );
                p->fTrivialUnsat = 1;
                p->iTrivialFrame = p->iCoreFrame = Gip_SolverConflictFrame( p, Conflict );
                return GIP_UNSAT;
            }
            btl = Gip_SolverAnalyze( p, Conflict, p->vLearntCls );
            Gip_SolverBacktrack( p, btl, 1 );
            if ( Vec_IntSize(p->vLearntCls) == 1 )
            {
                assert( btl == 0 );
                Gip_SolverAssign( p, Vec_IntEntry(p->vLearntCls, 0), GIP_CREF_NONE );
                p->pTag0[Gip_LitVar(Vec_IntEntry(p->vLearntCls, 0))] = p->iAnaFrame;
            }
            else
            {
                int Kind = GIP_CLA_LEARNT, i, Lit, Cref;
                Vec_IntForEachEntry( p->vLearntCls, Lit, i )
                    if ( Gip_LitVar(Lit) == p->constrainAct )
                        Kind = GIP_CLA_TEMPORARY;
                Cref = Gip_SolverAttachClauseTag( p, Vec_IntArray(p->vLearntCls), Vec_IntSize(p->vLearntCls), Kind, (unsigned)p->iAnaFrame << 1 );
                Gip_CdbBump( &p->Cdb, Cref );
                Gip_SolverAssign( p, Gip_ClaLits(&p->Cdb.Alloc, Cref)[0], Cref );
            }
            Gip_VsidsDecay( &p->Vsids );
            Gip_CdbDecay( &p->Cdb );
        }
        else
        {
            if ( (p->nConfLimit > 0 && p->Stats.nConflicts >= p->nConfCounted + p->nConfLimit) ||
                 (p->nPropLimit > 0 && p->Stats.nPropagations >= p->nPropLimit) ||
                 ((p->TimeLimit || p->pFuncStop) && p->Stats.nPropagations >= p->nTimeCheck && Gip_SolverTimedOut(p)) )
            {
                Gip_SolverBacktrack( p, nAssump, 1 );
                p->fCanceled = 1;
                return GIP_UNDEF;
            }
            if ( noc >= 0 && numConflict >= noc )
            {
                Gip_SolverBacktrack( p, nAssump, 1 );
                return GIP_RESTART;
            }
            Gip_SolverCleanLearnt( p, 0 );
            // place assumptions one decision level at a time
            while ( Gip_SolverLevelOf(p) < nAssump )
            {
                int a = pAssump[Gip_SolverLevelOf(p)];
                int v = Gip_SolverLitValue( p, a );
                if ( v == GIP_TRUE )
                {
                    Gip_SolverNewLevel( p );
                    if ( Gip_SolverLevelOf(p) == nAssump && !p->Jftr.fActive )
                        Gip_SolverPrepareVsids( p );
                }
                else if ( v == GIP_FALSE )
                {
                    Gip_SolverAnalyzeUnsatCore( p, a );
                    return GIP_UNSAT;
                }
                else
                {
                    Gip_SolverNewLevel( p );
                    Gip_SolverAssign( p, a, GIP_CREF_NONE );
                    if ( Gip_SolverLevelOf(p) == nAssump && !p->Jftr.fActive )
                        Gip_SolverPrepareVsids( p );
                    goto continue_main;
                }
            }
            if ( p->Jftr.fActive )
            {
                if ( p->Stats.nConflicts - p->nConfCounted >= p->Jftr.nConfLimit )
                {
                    // the budget ran out: the rest of the solve is the ordinary GipSAT search, from the assumptions
                    Gip_SolverJftrHandover( p, nAssump );
                    goto continue_main;
                }
                if ( !Gip_SolverJftrDecide( p ) )
                {
                    p->Jftr.fEarly = 1;
                    return GIP_SAT;
                }
            }
            else if ( !Gip_SolverDecide( p ) )
                return GIP_SAT;
        }
continue_main:;
    }
}

static double Gip_Luby( double y, unsigned x )
{
    unsigned size = 1, seq = 0;
    while ( size < x + 1 )
    {
        seq++;
        size = 2 * size + 1;
    }
    while ( size - 1 != x )
    {
        size = (size - 1) >> 1;
        seq--;
        x %= size;
    }
    return pow( y, (double)seq );
}

/**Function*************************************************************

  Synopsis    [Search with luby restarts.]

  Description [nRestartLimit < 0 means unlimited. After 10 restarts,
  switches from the approximate bucket to the exact activity heap.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverSearchWithRestart( Gip_Solver_t * p, int * pAssump, int nAssump, int nRestartLimit )
{
    unsigned restarts = 0;
    // With assumptions, Search prepares the decision queue after installing
    // the last one. An assumption-free query must prepare it here; otherwise
    // an empty queue can report SAT before deciding the permanent domain.
    // In jftr mode the queue is prepared at the hand-over to the ordinary search (Gip_SolverJftrHandover).
    if ( nAssump == 0 && !p->Jftr.fActive )
        Gip_SolverPrepareVsids( p );
    while ( 1 )
    {
        double restBase;
        int res;
        if ( nRestartLimit >= 0 && restarts >= (unsigned)nRestartLimit )
            return GIP_UNDEF;
        if ( restarts > 10 && p->Vsids.fEnableBucket && !p->Jftr.fActive )
        {
            int i, d;
            p->Vsids.fEnableBucket = 0;
            Gip_HeapClear( &p->Vsids.Heap );
            Vec_IntForEachEntry( p->Domain.Set.vSet, d, i )
                if ( p->pValue[d] == GIP_NONE )
                    Gip_VsidsPush( &p->Vsids, d );
        }
        restBase = Gip_Luby( 2.0, restarts );
        res = Gip_SolverSearch( p, pAssump, nAssump, restBase * 100.0 );
        if ( res == GIP_RESTART )
        {
            restarts++;
            continue;
        }
        return res;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
