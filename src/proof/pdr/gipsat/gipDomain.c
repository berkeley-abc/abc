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

static inline int * Gip_CtxDep( Gip_Ctx_t * p, int Var, int * pnDeps )
{
    *pnDeps = p->pDepOffset[Var+1] - p->pDepOffset[Var];
    return p->pDepData + p->pDepOffset[Var];
}

void Gip_VarSetInit( Gip_VarSet_t * p, int nVarsAlloc )
{
    p->vSet = Vec_IntAlloc( 100 );
    p->pHas = ABC_CALLOC( char, nVarsAlloc );
}

void Gip_VarSetFree( Gip_VarSet_t * p )
{
    Vec_IntFreeP( &p->vSet );
    ABC_FREE( p->pHas );
}

void Gip_LitSetInit( Gip_LitSet_t * p, int nVarsAlloc )
{
    p->vSet = Vec_IntAlloc( 100 );
    p->pHas = ABC_CALLOC( char, 2 * nVarsAlloc );
}

void Gip_LitSetFree( Gip_LitSet_t * p )
{
    Vec_IntFreeP( &p->vSet );
    ABC_FREE( p->pHas );
}

/**Function*************************************************************

  Synopsis    [Initializes the domain; the constant var is permanent.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_DomainInit( Gip_Domain_t * p, int nVarsAlloc, int varConst )
{
    Gip_VarSetInit( &p->Set, nVarsAlloc );
    Gip_VarSetInsert( &p->Set, varConst );
    p->nFixed = 1;
}

void Gip_DomainFree( Gip_Domain_t * p )
{
    Gip_VarSetFree( &p->Set );
}

// drop everything after the fixed prefix
void Gip_DomainReset( Gip_Domain_t * p )
{
    while ( Vec_IntSize(p->Set.vSet) > p->nFixed )
        p->Set.pHas[ Vec_IntPop(p->Set.vSet) ] = 0;
}

int Gip_DomainHas( Gip_Domain_t * p, int Var )
{
    return Gip_VarSetHas( &p->Set, Var );
}

void Gip_DomainInsert( Gip_Domain_t * p, int Var )
{
    Gip_VarSetInsert( &p->Set, Var );
}

/**Function*************************************************************

  Synopsis    [Per-query local domain = dep closure of the seeds.]

  Description [BFS from index nFixed following the dep table.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_DomainEnableLocal( Gip_Solver_t * p, Vec_Int_t * vSeeds )
{
    Gip_Domain_t * pDom = &p->Domain;
    int i, v, now;
    Gip_DomainReset( pDom );
    Vec_IntForEachEntry( vSeeds, v, i )
        Gip_DomainInsert( pDom, v );
    now = pDom->nFixed;
    while ( now < Vec_IntSize(pDom->Set.vSet) )
    {
        int nDeps, j, * pDeps;
        v = Vec_IntEntry( pDom->Set.vSet, now );
        now++;
        pDeps = Gip_CtxDep( p->pCtx, v, &nDeps );
        for ( j = 0; j < nDeps; j++ )
            Gip_DomainInsert( pDom, pDeps[j] );
    }
}

/**Function*************************************************************

  Synopsis    [Permanently adds a variable and its dep closure.]

  Description [Called for every literal of every added lemma clause.
  Extends the fixed prefix; skips already-assigned vars.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverAddDomain( Gip_Solver_t * p, int Var, int fDeps )
{
    Gip_Domain_t * pDom = &p->Domain;
    assert( Gip_SolverLevelOf(p) == 0 );
    if ( p->pValue[Var] != GIP_NONE )
        return;
    Gip_DomainReset( pDom );
    Gip_VarSetInsert( &pDom->Set, Var );
    if ( fDeps )
    {
        Vec_Int_t * vQueue = p->vSeeds; // scratch (safe: not used concurrently)
        int nDeps, j, d, * pDeps;
        Vec_IntClear( vQueue );
        pDeps = Gip_CtxDep( p->pCtx, Var, &nDeps );
        for ( j = 0; j < nDeps; j++ )
            Vec_IntPush( vQueue, pDeps[j] );
        while ( Vec_IntSize(vQueue) > 0 )
        {
            d = Vec_IntPop( vQueue );
            if ( Gip_VarSetHas(&pDom->Set, d) )
                continue;
            Gip_VarSetInsert( &pDom->Set, d );
            pDeps = Gip_CtxDep( p->pCtx, d, &nDeps );
            for ( j = 0; j < nDeps; j++ )
                Vec_IntPush( vQueue, pDeps[j] );
        }
    }
    pDom->nFixed = Vec_IntSize( pDom->Set.vSet );
}

/**Function*************************************************************

  Synopsis    [Pushes all unassigned domain vars into VSIDS.]

  Description [Also lazily compacts the fixed prefix: assigned fixed
  vars are removed for good.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gip_SolverPushToVsids( Gip_Solver_t * p )
{
    Gip_Domain_t * pDom = &p->Domain;
    int now = 0, d;
    assert( Gip_SolverLevelOf(p) == 0 );
    while ( now < pDom->nFixed )
    {
        d = Vec_IntEntry( pDom->Set.vSet, now );
        if ( p->pValue[d] == GIP_NONE )
        {
            Gip_VsidsPush( &p->Vsids, d );
            now++;
        }
        else
        {
            // swap set[now] <-> set[nFixed-1], then swap-remove index nFixed-1
            int last = Vec_IntEntry( pDom->Set.vSet, pDom->nFixed - 1 );
            Vec_IntWriteEntry( pDom->Set.vSet, now, last );
            Vec_IntWriteEntry( pDom->Set.vSet, pDom->nFixed - 1, d );
            pDom->Set.pHas[d] = 0;
            Vec_IntWriteEntry( pDom->Set.vSet, pDom->nFixed - 1, Vec_IntEntryLast(pDom->Set.vSet) );
            Vec_IntPop( pDom->Set.vSet );
            pDom->nFixed--;
        }
    }
    while ( now < Vec_IntSize(pDom->Set.vSet) )
    {
        Gip_VsidsPush( &p->Vsids, Vec_IntEntry(pDom->Set.vSet, now) );
        now++;
    }
}

/**Function*************************************************************

  Synopsis    [Fixes a temporary domain for a whole MIC round.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverSetDomain( Gip_Solver_t * p, int * pLits, int nLits )
{
    int i;
    Vec_IntClear( p->vSeeds );
    for ( i = 0; i < nLits; i++ )
        Vec_IntPush( p->vSeeds, Gip_LitVar(pLits[i]) );
    Gip_SolverReset( p );
    p->fTempDomain = 1;
    Gip_DomainEnableLocal( p, p->vSeeds );
    assert( !Gip_DomainHas(&p->Domain, p->constrainAct) );
    Gip_DomainInsert( &p->Domain, p->constrainAct );
    p->Vsids.fEnableBucket = 1;
    Gip_BucketClear( &p->Vsids.Bucket );
    Gip_SolverPushToVsids( p );
}

void Gip_SolverUnsetDomain( Gip_Solver_t * p )
{
    p->fTempDomain = 0;
}

/**Function*************************************************************

  Synopsis    [Late VSIDS fill, once all assumptions are placed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverPrepareVsids( Gip_Solver_t * p )
{
    int i, d;
    if ( !p->fPreparedVsids && !p->fTempDomain )
    {
        p->fPreparedVsids = 1;
        Vec_IntForEachEntry( p->Domain.Set.vSet, d, i )
            if ( p->pValue[d] == GIP_NONE )
                Gip_VsidsPush( &p->Vsids, d );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
