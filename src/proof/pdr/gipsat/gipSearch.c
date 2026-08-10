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

void Gip_SolverAssign( Gip_Solver_t * p, int Lit, int Reason )
{
    int Var = Gip_LitVar( Lit );
    Vec_IntPush( p->vTrail, Lit );
    Gip_SolverSetLit( p, Lit );
    p->pReason[Var] = Reason;
    p->pLevel[Var] = (unsigned)Gip_SolverLevelOf( p );
}

void Gip_SolverNewLevel( Gip_Solver_t * p )
{
    Vec_IntPush( p->vPosInTrail, Vec_IntSize(p->vTrail) );
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
        return;
    while ( Vec_IntSize(p->vTrail) > Vec_IntEntry(p->vPosInTrail, Level) )
    {
        int Lit = Vec_IntPop( p->vTrail );
        int Var = Gip_LitVar( Lit );
        Gip_SolverSetNone( p, Var );
        if ( fVsids )
            Gip_VsidsPush( &p->Vsids, Var );
        p->pPhase[Var] = (char)(1 ^ Gip_LitCompl(Lit));
    }
    p->nPropagated = Vec_IntEntry( p->vPosInTrail, Level );
    Vec_IntShrink( p->vPosInTrail, Level );
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
            if ( p->nConfLimit > 0 && p->Stats.nConflicts >= p->nConfCounted + p->nConfLimit )
            {
                Gip_SolverBacktrack( p, nAssump, 1 );
                p->fCanceled = 1;
                return GIP_UNDEF;
            }
            if ( p->TimeLimit && (p->Stats.nConflicts & 1023) == 0 && Abc_Clock() > p->TimeLimit )
            {
                Gip_SolverBacktrack( p, nAssump, 1 );
                p->fCanceled = 1;
                return GIP_UNDEF;
            }
            if ( Gip_SolverLevelOf(p) == 0 )
            {
                Gip_LitSetClear( &p->UnsatCore );
                return GIP_UNSAT;
            }
            btl = Gip_SolverAnalyze( p, Conflict, p->vLearntCls );
            Gip_SolverBacktrack( p, btl, 1 );
            if ( Vec_IntSize(p->vLearntCls) == 1 )
            {
                assert( btl == 0 );
                Gip_SolverAssign( p, Vec_IntEntry(p->vLearntCls, 0), GIP_CREF_NONE );
            }
            else
            {
                int Kind = GIP_CLA_LEARNT, i, Lit, Cref;
                Vec_IntForEachEntry( p->vLearntCls, Lit, i )
                    if ( Gip_LitVar(Lit) == p->constrainAct )
                        Kind = GIP_CLA_TEMPORARY;
                Cref = Gip_SolverAttachClause( p, Vec_IntArray(p->vLearntCls), Vec_IntSize(p->vLearntCls), Kind );
                Gip_CdbBump( &p->Cdb, Cref );
                Gip_SolverAssign( p, Gip_ClaLits(&p->Cdb.Alloc, Cref)[0], Cref );
            }
            Gip_VsidsDecay( &p->Vsids );
            Gip_CdbDecay( &p->Cdb );
        }
        else
        {
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
                    if ( Gip_SolverLevelOf(p) == nAssump )
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
                    if ( Gip_SolverLevelOf(p) == nAssump )
                        Gip_SolverPrepareVsids( p );
                    goto continue_main;
                }
            }
            if ( !Gip_SolverDecide( p ) )
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
    while ( 1 )
    {
        double restBase;
        int res;
        if ( nRestartLimit >= 0 && restarts >= (unsigned)nRestartLimit )
            return GIP_UNDEF;
        if ( restarts > 10 && p->Vsids.fEnableBucket )
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
