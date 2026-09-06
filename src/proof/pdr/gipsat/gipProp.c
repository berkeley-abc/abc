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

static inline void Gip_WVecPush( Gip_WVec_t * p, int Cref, int Blocker )
{
    if ( p->nSize == p->nCap )
    {
        p->nCap = p->nCap ? 2*p->nCap : 4;
        p->pArray = ABC_REALLOC( Gip_Wat_t, p->pArray, p->nCap );
    }
    p->pArray[p->nSize].clause  = Cref;
    p->pArray[p->nSize].blocker = Blocker;
    p->nSize++;
}

static inline void Gip_WVecSwapRemove( Gip_WVec_t * p, int i )
{
    p->pArray[i] = p->pArray[p->nSize-1];
    p->nSize--;
}

/**Function*************************************************************

  Synopsis    [Attaches the first two literals of a clause to the watchers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_WatchersAttach( Gip_Solver_t * p, int Cref )
{
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[0])], Cref, pLits[1] );
    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], Cref, pLits[0] );
}

void Gip_WatchersDetach( Gip_Solver_t * p, int Cref )
{
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    int k, i;
    for ( k = 0; k < 2; k++ )
    {
        Gip_WVec_t * pW = &p->pWatchers[Gip_LitNot(pLits[k])];
        for ( i = pW->nSize - 1; i >= 0; i-- )
            if ( pW->pArray[i].clause == Cref )
            {
                Gip_WVecSwapRemove( pW, i );
                break;
            }
    }
}

// full propagation, used at decision level 0
static int Gip_SolverPropagateFull( Gip_Solver_t * p )
{
    Gip_Alloc_t * pA = &p->Cdb.Alloc;
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry( p->vTrail, p->nPropagated++ );
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int wlen = pWs->nSize;
        int w = 0;
        p->Stats.nPropagations++;
        while ( w < wlen )
        {
            int blocker = pDat[w].blocker;
            int cid, * pLits, c0, len, i;
            if ( Gip_SolverLitValue(p, blocker) == GIP_TRUE )
            {
                w++;
                continue;
            }
            cid = pDat[w].clause;
            pLits = Gip_ClaLits( pA, cid );
            if ( pLits[0] == Gip_LitNot(Lit) )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker && Gip_SolverLitValue(p, c0) == GIP_TRUE )
            {
                pDat[w].blocker = c0;
                w++;
                continue;
            }
            len = Gip_ClaLen( pA, cid );
            for ( i = 2; i < len; i++ )
            {
                if ( Gip_SolverLitValue(p, pLits[i]) != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    wlen--;
                    pDat[w] = pDat[wlen];
                    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    goto next_cls;
                }
            }
            pDat[w].blocker = c0;
            if ( Gip_SolverLitValue(p, c0) == GIP_FALSE )
            {
                pWs->nSize = wlen;
                return cid;
            }
            Gip_SolverAssign( p, c0, cid );
            w++;
next_cls:;
        }
        pWs->nSize = wlen;
    }
    return GIP_CREF_NONE;
}

// domain-restricted propagation, used at levels > 0: clauses watched by
// out-of-domain variables are skipped, so variables outside the domain
// are never assigned above level 0
static int Gip_SolverPropagateDomain( Gip_Solver_t * p )
{
    Gip_Alloc_t * pA = &p->Cdb.Alloc;
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry( p->vTrail, p->nPropagated++ );
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int wlen = pWs->nSize;
        int w = 0;
        p->Stats.nPropagations++;
        while ( w < wlen )
        {
            int blocker = pDat[w].blocker;
            int cid, * pLits, c0, len, i, v;
            v = Gip_SolverLitValue( p, blocker );
            if ( v == GIP_TRUE || !Gip_DomainHas(&p->Domain, Gip_LitVar(blocker)) )
            {
                w++;
                continue;
            }
            cid = pDat[w].clause;
            pLits = Gip_ClaLits( pA, cid );
            if ( pLits[0] == Gip_LitNot(Lit) )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker )
            {
                v = Gip_SolverLitValue( p, c0 );
                if ( v == GIP_TRUE || !Gip_DomainHas(&p->Domain, Gip_LitVar(c0)) )
                {
                    pDat[w].blocker = c0;
                    w++;
                    continue;
                }
            }
            len = Gip_ClaLen( pA, cid );
            for ( i = 2; i < len; i++ )
            {
                if ( Gip_SolverLitValue(p, pLits[i]) != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    wlen--;
                    pDat[w] = pDat[wlen];
                    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    goto next_cls;
                }
            }
            pDat[w].blocker = c0;
            if ( Gip_SolverLitValue(p, c0) == GIP_FALSE )
            {
                pWs->nSize = wlen;
                return cid;
            }
            Gip_SolverAssign( p, c0, cid );
            w++;
next_cls:;
        }
        pWs->nSize = wlen;
    }
    return GIP_CREF_NONE;
}

/**Function*************************************************************

  Synopsis    [Propagates; returns the conflict CRef or GIP_CREF_NONE.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverPropagate( Gip_Solver_t * p )
{
    if ( Gip_SolverLevelOf(p) == 0 )
        return Gip_SolverPropagateFull( p );
    return Gip_SolverPropagateDomain( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
