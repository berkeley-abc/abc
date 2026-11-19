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
    Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[0]) );
    Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[1]) );
    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[0])], Cref, pLits[1] );
    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], Cref, pLits[0] );
    Gip_SolverWakeWatch( p, pLits[0] );
    Gip_SolverWakeWatch( p, pLits[1] );
}

void Gip_WatchersDetach( Gip_Solver_t * p, int Cref )
{
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    int k, i;
    for ( k = 0; k < 2; k++ )
    {
        Gip_WVec_t * pW = &p->pWatchers[Gip_LitNot(pLits[k])];
        Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[k]) );
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
    const char * pVal = p->pLitVal;
    unsigned * pData = pA->pData;
    if ( p->nPropagated < Vec_IntSize(p->vTrail) )
        Gip_SolverResetWatchEpoch( p );
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry( p->vTrail, p->nPropagated++ );
        int NotLit = Gip_LitNot( Lit );
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int wlen = pWs->nSize;
        int w = 0;
        p->Stats.nPropagations++;
        while ( w < wlen )
        {
            int blocker = pDat[w].blocker;
            int cid, * pLits, c0, len, i;
            if ( (pVal[blocker] & 3) == GIP_TRUE )
            {
                w++;
                continue;
            }
            cid = pDat[w].clause;
            pLits = (int *)(pData + cid + 1);
            if ( pLits[0] == NotLit )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker && (pVal[c0] & 3) == GIP_TRUE )
            {
                pDat[w].blocker = c0;
                w++;
                continue;
            }
            len = (int)(pData[cid] >> 5);
            for ( i = 2; i < len; i++ )
            {
                if ( (pVal[pLits[i]] & 3) != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    wlen--;
                    pDat[w] = pDat[wlen];
                    Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[1]) );
                    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    Gip_SolverWakeWatch( p, pLits[1] );
                    goto next_cls;
                }
            }
            pDat[w].blocker = c0;
            if ( (pVal[c0] & 3) == GIP_FALSE )
            {
                pWs->nSize = wlen;
                return cid;
            }
            Gip_SolverAssign( p, c0, cid );
            {
                // a level-0 fact depends on its reason clause and on the facts falsifying the rest
                int Frame = Gip_SolverClaFrame( p, cid );
                for ( i = 1; i < len; i++ )
                    if ( p->pTag0[Gip_LitVar(pLits[i])] < Frame )
                        Frame = p->pTag0[Gip_LitVar(pLits[i])];
                p->pTag0[Gip_LitVar(c0)] = Frame;
            }
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
    const char * pVal = p->pLitVal;
    const char * pDom = p->Domain.Set.pHas;
    unsigned * pData = pA->pData;
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry( p->vTrail, p->nPropagated++ );
        int NotLit = Gip_LitNot( Lit );
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int wlen = pWs->nSize;
        int w = 0;
        p->Stats.nPropagations++;
        while ( w < wlen )
        {
            int blocker = pDat[w].blocker;
            int cid, * pLits, c0, len, i;
            if ( pVal[blocker] == GIP_TRUE || !pDom[Gip_LitVar(blocker)] )
            {
                w++;
                continue;
            }
            cid = pDat[w].clause;
            pLits = (int *)(pData + cid + 1);
            if ( pLits[0] == NotLit )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker && (pVal[c0] == GIP_TRUE || !pDom[Gip_LitVar(c0)]) )
            {
                pDat[w].blocker = c0;
                w++;
                continue;
            }
            len = (int)(pData[cid] >> 5);
            for ( i = 2; i < len; i++ )
            {
                if ( pVal[pLits[i]] != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    wlen--;
                    pDat[w] = pDat[wlen];
                    Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[1]) );
                    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    Gip_SolverWakeWatch( p, pLits[1] );
                    goto next_cls;
                }
            }
            pDat[w].blocker = c0;
            if ( pVal[c0] == GIP_FALSE )
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

  Synopsis    [Propagates in the query domain while caching irrelevant watch lists.]

  Description []

***********************************************************************/
// Cache entire watch lists that cannot affect the fixed query domain.
static int Gip_SolverPropagateDomainSkip( Gip_Solver_t * p )
{
    Gip_Alloc_t * pA = &p->Cdb.Alloc;
    const char * pVal = p->pLitVal;
    const char * pDom = p->Domain.Set.pHas;
    unsigned * pData = pA->pData;
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry( p->vTrail, p->nPropagated++ );
        int NotLit = Gip_LitNot( Lit );
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int wlen = pWs->nSize;
        int w = 0, AllOutside = 1;
        p->Stats.nPropagations++;
        p->nWatchLists++;
        if ( p->pSkipWatch[Lit] == p->nWatchEpoch )
        {
            if ( p->fCheckSkipWatch )
                for ( w = 0; w < wlen; w++ )
                    assert( !pDom[Gip_LitVar(pDat[w].blocker)] );
            p->nWatchSkipped++;
            continue;
        }
        while ( w < wlen )
        {
            int blocker = pDat[w].blocker;
            int cid, * pLits, c0, len, i;
            if ( !pDom[Gip_LitVar(blocker)] )
            {
                w++;
                continue;
            }
            AllOutside = 0;
            if ( (pVal[blocker] & 3) == GIP_TRUE )
            {
                w++;
                continue;
            }
            cid = pDat[w].clause;
            pLits = (int *)(pData + cid + 1);
            if ( pLits[0] == NotLit )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker && ((pVal[c0] & 3) == GIP_TRUE || !pDom[Gip_LitVar(c0)]) )
            {
                pDat[w].blocker = c0;
                w++;
                continue;
            }
            len = (int)(pData[cid] >> 5);
            for ( i = 2; i < len; i++ )
            {
                if ( (pVal[pLits[i]] & 3) != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    wlen--;
                    pDat[w] = pDat[wlen];
                    Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[1]) );
                    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    Gip_SolverWakeWatch( p, pLits[1] );
                    goto next_cls;
                }
            }
            pDat[w].blocker = c0;
            if ( (pVal[c0] & 3) == GIP_FALSE )
            {
                pWs->nSize = wlen;
                return cid;
            }
            Gip_SolverAssign( p, c0, cid );
            w++;
next_cls:;
        }
        pWs->nSize = wlen;
        if ( AllOutside ) p->pSkipWatch[Lit] = p->nWatchEpoch;
    }
    return GIP_CREF_NONE;
}

/**Function*************************************************************

  Synopsis    [Propagates using the active portion of each watch list.]

  Description []

***********************************************************************/
// Partition each visited list into active and out-of-domain prefixes once
// per domain epoch. Only blocker membership is cached, never its truth value.
// A domain change invalidates every partition; insertion, detachment and
// flip-to-none invalidate the affected lists through the existing hooks.
static int Gip_SolverPropagateDomainPartition( Gip_Solver_t * p )
{
    const char * pVal = p->pLitVal;
    const char * pDom = p->Domain.Set.pHas;
    unsigned * pData = p->Cdb.Alloc.pData;
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry(p->vTrail, p->nPropagated++), NotLit = Gip_LitNot(Lit);
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int w = 0, wlen = pWs->nSize, active, i;
        p->Stats.nPropagations++;
        p->nPartWatchLists++;
        p->nPartWatchEntries += wlen;
        if ( p->pSkipWatch[Lit] != p->nWatchEpoch )
        {
            active = wlen;
            while ( w < active )
            {
                if ( pDom[Gip_LitVar(pDat[w].blocker)] ) w++;
                else
                {
                    Gip_Wat_t Temp = pDat[w];
                    pDat[w] = pDat[--active]; pDat[active] = Temp;
                }
            }
            p->pActiveWatch[Lit] = active;
            p->pSkipWatch[Lit] = p->nWatchEpoch;
            p->nPartWatchRebuilt++;
        }
        else active = p->pActiveWatch[Lit];
        if ( p->fCheckSkipWatch )
        {
            assert(active >= 0 && active <= wlen);
            for ( i = 0; i < wlen; i++ )
                assert(!!pDom[Gip_LitVar(pDat[i].blocker)] == (i < active));
        }
        p->nPartWatchSkipped += wlen - active;
        w = 0;
        while ( w < active )
        {
            int blocker = pDat[w].blocker, cid, * pLits, c0, len;
            if ( (pVal[blocker] & 3) == GIP_TRUE ) { w++; continue; }
            cid = pDat[w].clause;
            pLits = (int *)(pData + cid + 1);
            if ( pLits[0] == NotLit )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker && !pDom[Gip_LitVar(c0)] )
            {
                Gip_Wat_t Temp;
                pDat[w].blocker = c0;
                Temp = pDat[w]; pDat[w] = pDat[--active]; pDat[active] = Temp;
                continue;
            }
            if ( c0 != blocker && (pVal[c0] & 3) == GIP_TRUE )
            {
                pDat[w].blocker = c0; w++; continue;
            }
            len = (int)(pData[cid] >> 5);
            for ( i = 2; i < len; i++ )
                if ( (pVal[pLits[i]] & 3) != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    // Remove from both the active prefix and the full list.
                    pDat[w] = pDat[--active];
                    pDat[active] = pDat[--wlen];
                    Gip_SolverInvalidateWatch(p, Gip_LitNot(pLits[1]));
                    Gip_WVecPush(&p->pWatchers[Gip_LitNot(pLits[1])], cid, c0);
                    Gip_SolverWakeWatch(p, pLits[1]);
                    goto next_partition_clause;
                }
            pDat[w].blocker = c0;
            if ( (pVal[c0] & 3) == GIP_FALSE )
            {
                pWs->nSize = wlen; p->pActiveWatch[Lit] = active;
                return cid;
            }
            Gip_SolverAssign(p, c0, cid);
            w++;
next_partition_clause:;
        }
        pWs->nSize = wlen; p->pActiveWatch[Lit] = active;
    }
    return GIP_CREF_NONE;
}

/**Function*************************************************************

  Synopsis    [Propagates using domain membership stored alongside literal values.]

  Description []

***********************************************************************/
// Packed query-domain flags remove a dependent membership-table lookup.
static int Gip_SolverPropagateDomainPacked( Gip_Solver_t * p )
{
    Gip_Alloc_t * pA = &p->Cdb.Alloc;
    const char * pVal = p->pLitVal;
    unsigned * pData = pA->pData;
    while ( p->nPropagated < Vec_IntSize(p->vTrail) )
    {
        int Lit = Vec_IntEntry( p->vTrail, p->nPropagated++ );
        int NotLit = Gip_LitNot( Lit );
        Gip_WVec_t * pWs = &p->pWatchers[Lit];
        Gip_Wat_t * pDat = pWs->pArray;
        int wlen = pWs->nSize;
        int w = 0;
        p->Stats.nPropagations++;
        while ( w < wlen )
        {
            int blocker = pDat[w].blocker;
            int cid, * pLits, c0, len, i;
            if ( (pVal[blocker] & 5) != 4 )
            {
                w++;
                continue;
            }
            cid = pDat[w].clause;
            pLits = (int *)(pData + cid + 1);
            if ( pLits[0] == NotLit )
            {
                int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
            }
            c0 = pLits[0];
            if ( c0 != blocker && ((pVal[c0] & 5) != 4) )
            {
                pDat[w].blocker = c0;
                w++;
                continue;
            }
            len = (int)(pData[cid] >> 5);
            for ( i = 2; i < len; i++ )
            {
                if ( (pVal[pLits[i]] & 3) != GIP_FALSE )
                {
                    int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                    wlen--;
                    pDat[w] = pDat[wlen];
                    Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[1]) );
                    Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    Gip_SolverWakeWatch( p, pLits[1] );
                    goto next_cls;
                }
            }
            pDat[w].blocker = c0;
            if ( (pVal[c0] & 3) == GIP_FALSE )
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
    if ( p->pActiveWatch ) return Gip_SolverPropagateDomainPartition(p);
    if ( p->pSkipWatch ) return Gip_SolverPropagateDomainSkip(p);
    return p->Domain.Set.pLitFlags ? Gip_SolverPropagateDomainPacked(p) : Gip_SolverPropagateDomain(p);
}

/**Function*************************************************************

  Synopsis    [Tries to unassign a variable without breaking any clause.]

  Description [Port of rIC3's DagCnfSolver::flip_to_none. Used after a
  SAT answer to detect assignments that no clause depends on: every
  clause watching the true literal of Var must stay satisfied by another
  literal (or be left undetermined by an unassigned literal outside the
  decision domain). Returns 1 if Var is now unassigned, 0 if its value
  was needed and has been restored. Level-0 (implied) vars never flip.]

  SideEffects [On success, Var reads as unassigned until the next solve.]

  SeeAlso     []

***********************************************************************/
int Gip_SolverFlipToNone( Gip_Solver_t * p, int Var )
{
    Gip_Alloc_t * pA = &p->Cdb.Alloc;
    Gip_WVec_t * pWs;
    int Lit, w;
    if ( p->pValue[Var] == GIP_NONE )
        return 1;
    // With a partial model, a true literal need not be watched: both watched
    // literals may remain unassigned. The watch-only weakening below assumes
    // a fully assigned domain and would then miss clauses depending on Var.
    // Retain assigned literals and let the separate SAT-core lift remove them.
    if ( p->fJustify )
        return 0;
    if ( p->pLevel[Var] == 0 )
        return 0;
    Lit = Gip_Lit( Var, p->pValue[Var] == GIP_FALSE );   // the true literal of Var
    Gip_SolverInvalidateWatch( p, 2*Var );
    Gip_SolverInvalidateWatch( p, 2*Var+1 );
    Gip_SolverSetNone( p, Var );
    pWs = &p->pWatchers[Gip_LitNot(Lit)];                  // clauses watching Lit
    for ( w = 0; w < pWs->nSize; )
    {
        int cid = pWs->pArray[w].clause;
        int * pLits = Gip_ClaLits( pA, cid );
        int len = Gip_ClaLen( pA, cid ), i, v, c0;
        if ( pLits[0] == Lit )
        {
            int t = pLits[0]; pLits[0] = pLits[1]; pLits[1] = t;
        }
        assert( pLits[1] == Lit );
        c0 = pLits[0];
        v = Gip_SolverLitValue( p, c0 );
        if ( v == GIP_TRUE || (v != GIP_FALSE && !Gip_DomainHas(&p->Domain, Gip_LitVar(c0))) )
        {
            pWs->pArray[w].blocker = c0;
            w++;
            continue;
        }
        for ( i = 2; i < len; i++ )
        {
            v = Gip_SolverLitValue( p, pLits[i] );
            if ( v == GIP_TRUE || (v == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(pLits[i]))) )
            {
                int t = pLits[1]; pLits[1] = pLits[i]; pLits[i] = t;
                Gip_WVecSwapRemove( pWs, w );
                Gip_SolverInvalidateWatch( p, Gip_LitNot(pLits[1]) );
                Gip_WVecPush( &p->pWatchers[Gip_LitNot(pLits[1])], cid, c0 );
                    Gip_SolverWakeWatch( p, pLits[1] );
                goto next_cls;
            }
        }
        // the clause is satisfied only by Lit: restore the value
        Gip_SolverSetLit( p, Lit );
        return 0;
next_cls:;
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
