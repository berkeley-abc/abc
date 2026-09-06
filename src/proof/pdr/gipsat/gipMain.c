/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Gip_SolverSimplifyClause( Gip_Solver_t * p, int * pLits, int nLits );

/**Function*************************************************************

  Synopsis    [Creates a solver over the shared context.]

  Description [Loads the entire static CNF as transition clauses.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gip_Solver_t * Gip_SolverNew( Gip_Ctx_t * pCtx )
{
    Gip_Solver_t * p = ABC_CALLOC( Gip_Solver_t, 1 );
    int i, c, Conflict;
    p->pCtx = pCtx;
    p->nVars = pCtx->nVars;
    p->constrainAct = pCtx->nVars;
    p->nVarsAlloc = pCtx->nVars + 1;
    p->pValue  = ABC_ALLOC( char, p->nVarsAlloc );
    p->pPhase  = ABC_ALLOC( char, p->nVarsAlloc );
    p->pMark   = ABC_CALLOC( char, p->nVarsAlloc );
    p->pLevel  = ABC_CALLOC( unsigned, p->nVarsAlloc );
    p->pReason = ABC_ALLOC( int, p->nVarsAlloc );
    for ( i = 0; i < p->nVarsAlloc; i++ )
    {
        p->pValue[i]  = GIP_NONE;
        p->pPhase[i]  = GIP_NONE;
        p->pReason[i] = GIP_CREF_NONE;
    }
    p->pWatchers = ABC_CALLOC( Gip_WVec_t, 2 * p->nVarsAlloc );
    Gip_CdbInit( &p->Cdb );
    Gip_VsidsInit( &p->Vsids, p->nVarsAlloc );
    Gip_DomainInit( &p->Domain, p->nVarsAlloc, pCtx->varConst );
    Gip_LitSetInit( &p->UnsatCore, p->nVarsAlloc );
    p->vTrail      = Vec_IntAlloc( 1000 );
    p->vPosInTrail = Vec_IntAlloc( 100 );
    p->vClear      = Vec_IntAlloc( 100 );
    p->vAnaStack   = Vec_IntAlloc( 100 );
    p->vLearntCls  = Vec_IntAlloc( 100 );
    p->vSimpCls    = Vec_IntAlloc( 100 );
    p->vSeeds      = Vec_IntAlloc( 100 );
    p->vAssump     = Vec_IntAlloc( 16 );
    p->nLastNumLemma = 1000;
    for ( c = 0; c < pCtx->pCnf->nClauses; c++ )
        Gip_SolverAddClauseInner( p, pCtx->pCnf->pClauses[c],
            (int)(pCtx->pCnf->pClauses[c+1] - pCtx->pCnf->pClauses[c]), GIP_CLA_TRANS );
    Conflict = Gip_SolverPropagate( p );
    assert( Conflict == GIP_CREF_NONE );
    assert( !p->fTrivialUnsat );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverFree( Gip_Solver_t * p )
{
    int i;
    if ( p == NULL )
        return;
    for ( i = 0; i < 2 * p->nVarsAlloc; i++ )
        ABC_FREE( p->pWatchers[i].pArray );
    ABC_FREE( p->pWatchers );
    ABC_FREE( p->pValue );
    ABC_FREE( p->pPhase );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pLevel );
    ABC_FREE( p->pReason );
    Gip_CdbFree( &p->Cdb );
    Gip_VsidsFree( &p->Vsids );
    Gip_DomainFree( &p->Domain );
    Gip_LitSetFree( &p->UnsatCore );
    Vec_IntFreeP( &p->vTrail );
    Vec_IntFreeP( &p->vPosInTrail );
    Vec_IntFreeP( &p->vClear );
    Vec_IntFreeP( &p->vAnaStack );
    Vec_IntFreeP( &p->vLearntCls );
    Vec_IntFreeP( &p->vSimpCls );
    Vec_IntFreeP( &p->vSeeds );
    Vec_IntFreeP( &p->vAssump );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Level-0 clause simplification.]

  Description [Sorts literals, drops duplicates and false literals,
  detects tautologies and satisfied clauses. Fills p->vSimpCls. Returns
  0 if the clause should be dropped; an empty result sets fTrivialUnsat.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gip_SolverSimplifyClause( Gip_Solver_t * p, int * pLits, int nLits )
{
    int i, k = 0, prev = -1;
    assert( Gip_SolverLevelOf(p) == 0 );
    Vec_IntClear( p->vSimpCls );
    for ( i = 0; i < nLits; i++ )
        Vec_IntPush( p->vSimpCls, pLits[i] );
    Vec_IntSort( p->vSimpCls, 0 );
    for ( i = 0; i < Vec_IntSize(p->vSimpCls); i++ )
    {
        int Lit = Vec_IntEntry( p->vSimpCls, i );
        int v;
        if ( Lit == prev )
            continue;
        if ( prev != -1 && Lit == Gip_LitNot(prev) )
            return 0;
        prev = Lit;
        v = Gip_SolverLitValue( p, Lit );
        if ( v == GIP_TRUE )
            return 0;
        if ( v == GIP_FALSE )
            continue;
        Vec_IntWriteEntry( p->vSimpCls, k++, Lit );
    }
    Vec_IntShrink( p->vSimpCls, k );
    if ( k == 0 )
    {
        p->fTrivialUnsat = 1;
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Simplifies and attaches a clause; returns CRef or GIP_CREF_NONE.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverAddClauseInner( Gip_Solver_t * p, int * pLits, int nLits, int Kind )
{
    int i, Lit;
    if ( !Gip_SolverSimplifyClause( p, pLits, nLits ) )
        return GIP_CREF_NONE;
    Vec_IntForEachEntry( p->vSimpCls, Lit, i )
        if ( Gip_LitVar(Lit) == p->constrainAct )
            Kind = GIP_CLA_TEMPORARY;
    if ( Vec_IntSize(p->vSimpCls) == 1 )
    {
        Lit = Vec_IntEntry( p->vSimpCls, 0 );
        assert( Gip_LitVar(Lit) != p->constrainAct );
        assert( Gip_SolverLitValue(p, Lit) == GIP_NONE );
        Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
        if ( Gip_SolverPropagate(p) != GIP_CREF_NONE )
            p->fTrivialUnsat = 1;
        return GIP_CREF_NONE;
    }
    return Gip_SolverAttachClause( p, Vec_IntArray(p->vSimpCls), Vec_IntSize(p->vSimpCls), Kind );
}

/**Function*************************************************************

  Synopsis    [Backtracks to level 0 and drops temporaries and local domain.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverReset( Gip_Solver_t * p )
{
    Gip_SolverBacktrack( p, 0, 0 );
    Gip_SolverCleanTemporary( p );
    p->fPreparedVsids = 0;
    Gip_DomainReset( &p->Domain );
    assert( !p->fTempDomain );
}

/**Function*************************************************************

  Synopsis    [Adds a lemma clause.]

  Description [The only external entry for frame cubes; permanently
  extends the fixed domain with the lemma variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverAddLemma( Gip_Solver_t * p, int * pLits, int nLits )
{
    int i;
    Gip_SolverReset( p );
    for ( i = 0; i < nLits; i++ )
        Gip_SolverAddDomain( p, Gip_LitVar(pLits[i]), 1 );
    Gip_SolverAddClauseInner( p, pLits, nLits, GIP_CLA_LEMMA );
}

/**Function*************************************************************

  Synopsis    [Starts a query round.]

  Description [Attaches the constraint clauses as temporaries and builds
  the local domain from the seeds. Returns 0 if a constraint clause
  simplifies to a unit (query is UNSAT).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Gip_SolverNewRound( Gip_Solver_t * p, Vec_Int_t * vSeeds,
                               int ** ppCstCls, int * pnCstLits, int nCst, int fBucket )
{
    int c, i;
    Gip_SolverBacktrack( p, 0, p->fTempDomain );
    Gip_SolverCleanTemporary( p );
    p->fPreparedVsids = 0;
    for ( c = 0; c < nCst; c++ )
    {
        Vec_IntClear( p->vAssump );   // scratch here; real assumptions built later
        for ( i = 0; i < pnCstLits[c]; i++ )
            Vec_IntPush( p->vAssump, ppCstCls[c][i] );
        Vec_IntPush( p->vAssump, Gip_Lit(p->constrainAct, 1) );
        if ( !Gip_SolverSimplifyClause( p, Vec_IntArray(p->vAssump), Vec_IntSize(p->vAssump) ) )
            continue;
        assert( Vec_IntSize(p->vSimpCls) > 0 );
        if ( Vec_IntSize(p->vSimpCls) == 1 )
            return 0;
        Gip_SolverAttachClause( p, Vec_IntArray(p->vSimpCls), Vec_IntSize(p->vSimpCls), GIP_CLA_TEMPORARY );
    }
    if ( !p->fTempDomain )
    {
        Gip_DomainEnableLocal( p, vSeeds );
        assert( !Gip_DomainHas(&p->Domain, p->constrainAct) );
        Gip_DomainInsert( &p->Domain, p->constrainAct );
        if ( fBucket )
        {
            p->Vsids.fEnableBucket = 1;
            Gip_BucketClear( &p->Vsids.Bucket );
        }
        else
        {
            p->Vsids.fEnableBucket = 0;
            Gip_HeapClear( &p->Vsids.Heap );
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Full query entry point.]

  Description [Solves under the given assumptions and temporary
  constraint clauses. Returns GIP_SAT/GIP_UNSAT/GIP_UNDEF.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverSolve( Gip_Solver_t * p,
                     int * pAssump, int nAssump,
                     int ** ppCstCls, int * pnCstLits, int nCst,
                     int nRestartLimit )
{
    abctime clk;
    int i, c, res, * pUse, nUse;
    p->fCanceled = 0;
    p->nConfCounted = p->Stats.nConflicts;
    if ( p->fTrivialUnsat )
    {
        Gip_LitSetClear( &p->UnsatCore );
        return GIP_UNSAT;
    }
    p->Stats.nSolves++;
    clk = Abc_Clock();
    if ( Gip_SolverPropagate(p) != GIP_CREF_NONE )
    {
        p->fTrivialUnsat = 1;
        Gip_LitSetClear( &p->UnsatCore );
        p->Stats.timeSolve += Abc_Clock() - clk;
        return GIP_UNSAT;
    }
    // domain seeds = assumption vars + constraint vars
    Vec_IntClear( p->vSeeds );
    for ( i = 0; i < nAssump; i++ )
        Vec_IntPush( p->vSeeds, Gip_LitVar(pAssump[i]) );
    for ( c = 0; c < nCst; c++ )
        for ( i = 0; i < pnCstLits[c]; i++ )
            Vec_IntPush( p->vSeeds, Gip_LitVar(ppCstCls[c][i]) );
    if ( nCst > 0 )
    {
        if ( !Gip_SolverNewRound( p, p->vSeeds, ppCstCls, pnCstLits, nCst, 1 ) )
        {
            Gip_LitSetClear( &p->UnsatCore );
            p->Stats.timeSolve += Abc_Clock() - clk;
            return GIP_UNSAT;
        }
        // assumptions = [constrainAct] ++ pAssump
        Vec_IntClear( p->vAssump );
        Vec_IntPush( p->vAssump, Gip_Lit(p->constrainAct, 0) );
        for ( i = 0; i < nAssump; i++ )
            Vec_IntPush( p->vAssump, pAssump[i] );
        pUse = Vec_IntArray( p->vAssump );
        nUse = Vec_IntSize( p->vAssump );
    }
    else
    {
        res = Gip_SolverNewRound( p, p->vSeeds, NULL, NULL, 0, 1 );
        assert( res );
        pUse = pAssump;
        nUse = nAssump;
    }
    Gip_SolverCleanLearnt( p, 1 );
    Gip_SolverSimplify( p );
    res = Gip_SolverSearchWithRestart( p, pUse, nUse, nRestartLimit );
    p->Stats.timeSolve += Abc_Clock() - clk;
    return res;
}

/**Function*************************************************************

  Synopsis    [Model value of a variable; unassigned counts as 0.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverVarValue( Gip_Solver_t * p, int Var )
{
    return p->pValue[Var] == GIP_TRUE ? 1 : 0;
}

/**Function*************************************************************

  Synopsis    [Checks whether a literal is in the last unsat core.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverUnsatHas( Gip_Solver_t * p, int Lit )
{
    return Gip_LitSetHas( &p->UnsatCore, Lit );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
