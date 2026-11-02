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

#define GIP_ALLOC_MIN (1 << 20)   // 1M words

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static void Gip_AllocInit( Gip_Alloc_t * p, unsigned nCapacity )
{
    p->nCap = Abc_MaxInt( nCapacity, GIP_ALLOC_MIN );
    p->pData = ABC_ALLOC( unsigned, p->nCap );
    p->nSize = 0;
    p->nWasted = 0;
}

static void Gip_AllocGrow( Gip_Alloc_t * p, unsigned nWords )
{
    if ( p->nSize + nWords <= p->nCap )
        return;
    while ( p->nSize + nWords > p->nCap )
        p->nCap *= 2;
    p->pData = ABC_REALLOC( unsigned, p->pData, p->nCap );
}

// clause words: 1 header + nLits + (learnt ? 1 : 0)
static inline unsigned Gip_ClaWords( Gip_Alloc_t * p, int Cref )
{
    return 1 + (unsigned)Gip_ClaLen(p, Cref) + (unsigned)Gip_ClaIsLearnt(p, Cref) + 1;
}

static int Gip_AllocClause( Gip_Alloc_t * p, int * pLits, int nLits, int fTrans, int fLearnt, unsigned TagWord )
{
    int cid, i;
    unsigned nWords = 1 + (unsigned)nLits + (unsigned)(fLearnt != 0) + 1;
    assert( !(fTrans && fLearnt) );
    Gip_AllocGrow( p, nWords );
    cid = (int)p->nSize;
    p->pData[cid] = ((unsigned)nLits << 5) | (unsigned)(fTrans != 0) | ((unsigned)(fLearnt != 0) << 1);
    for ( i = 0; i < nLits; i++ )
        p->pData[cid + 1 + i] = (unsigned)pLits[i];
    if ( fLearnt )
    {
        float zero = 0.0;
        memcpy( p->pData + cid + 1 + nLits, &zero, 4 );
    }
    p->pData[cid + 1 + nLits + (fLearnt != 0)] = TagWord;
    p->nSize += nWords;
    assert( p->nSize < (unsigned)GIP_CREF_NONE );
    return cid;
}

static int Gip_AllocFrom( Gip_Alloc_t * p, unsigned * pFrom, unsigned nWords )
{
    int cid;
    Gip_AllocGrow( p, nWords );
    cid = (int)p->nSize;
    memcpy( p->pData + cid, pFrom, sizeof(unsigned) * nWords );
    p->nSize += nWords;
    return cid;
}

// relocate clause into new arena; forwarding pointer stored in lits[0] slot
static int Gip_AllocReloc( Gip_Alloc_t * pFrom, int Cref, Gip_Alloc_t * pTo )
{
    unsigned nWords;
    int rcid;
    if ( Gip_ClaIsReloced(pFrom, Cref) )
        return (int)pFrom->pData[Cref + 1];
    nWords = Gip_ClaWords( pFrom, Cref );
    rcid = Gip_AllocFrom( pTo, pFrom->pData + Cref, nWords );
    Gip_ClaSetReloced( pFrom, Cref );
    pFrom->pData[Cref + 1] = (unsigned)rcid;
    return rcid;
}

/**Function*************************************************************

  Synopsis    [Initializes the clause database.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_CdbInit( Gip_Cdb_t * p )
{
    Gip_AllocInit( &p->Alloc, GIP_ALLOC_MIN );
    p->vTrans  = Vec_IntAlloc( 1000 );
    p->vLemmas = Vec_IntAlloc( 100 );
    p->vLearnt = Vec_IntAlloc( 100 );
    p->vTemp   = Vec_IntAlloc( 16 );
    p->actInc  = 1.0;
}

void Gip_CdbFree( Gip_Cdb_t * p )
{
    ABC_FREE( p->Alloc.pData );
    Vec_IntFreeP( &p->vTrans );
    Vec_IntFreeP( &p->vLemmas );
    Vec_IntFreeP( &p->vLearnt );
    Vec_IntFreeP( &p->vTemp );
}

static int Gip_CdbAlloc( Gip_Cdb_t * p, int * pLits, int nLits, int Kind, unsigned TagWord )
{
    int cid = Gip_AllocClause( &p->Alloc, pLits, nLits, Kind == GIP_CLA_TRANS, Kind == GIP_CLA_LEARNT, TagWord );
    switch ( Kind )
    {
        case GIP_CLA_TRANS:     Vec_IntPush( p->vTrans,  cid ); break;
        case GIP_CLA_LEMMA:     Vec_IntPush( p->vLemmas, cid ); break;
        case GIP_CLA_LEARNT:    Vec_IntPush( p->vLearnt, cid ); break;
        case GIP_CLA_TEMPORARY: Vec_IntPush( p->vTemp,   cid ); break;
        default: assert( 0 );
    }
    return cid;
}

static void Gip_CdbFreeClause( Gip_Cdb_t * p, int Cref )
{
    Gip_ClaSetRemoved( &p->Alloc, Cref );
    p->Alloc.nWasted += Gip_ClaWords( &p->Alloc, Cref );
}

/**Function*************************************************************

  Synopsis    [Attaches a clause to the database and the watchers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverAttachClauseTag( Gip_Solver_t * p, int * pLits, int nLits, int Kind, unsigned TagWord )
{
    int cid;
    assert( nLits > 1 );
    cid = Gip_CdbAlloc( &p->Cdb, pLits, nLits, Kind, TagWord );
    Gip_WatchersAttach( p, cid );
    return cid;
}
int Gip_SolverAttachClause( Gip_Solver_t * p, int * pLits, int nLits, int Kind )
{
    return Gip_SolverAttachClauseTag( p, pLits, nLits, Kind, (unsigned)GIP_FRAME_INF << 1 );
}
// lowers the frame tag of a clause (a dependency on a clause or fact of that frame): a finite
// dependency freezes the tag at the lower of the two frames, because a tag that follows the
// clause's own lemma would rise above the dependency when that lemma is pushed or promoted
void Gip_SolverLowerTag( Gip_Solver_t * p, int Cref, int Frame )
{
    int Cur = Gip_SolverClaFrame( p, Cref );
    if ( Frame == GIP_FRAME_INF )
        return;
    Gip_ClaSetTagWord( &p->Cdb.Alloc, Cref, (unsigned)(Frame < Cur ? Frame : Cur) << 1 );
}
// the lowest frame a conflict at level 0 depends on: the clause and the facts falsifying it
int Gip_SolverConflictFrame( Gip_Solver_t * p, int Cref )
{
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    int i, nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref ), Frame = Gip_SolverClaFrame( p, Cref );
    for ( i = 0; i < nLits; i++ )
        if ( p->pLevel[Gip_LitVar(pLits[i])] == 0 && p->pTag0[Gip_LitVar(pLits[i])] < Frame )
            Frame = p->pTag0[Gip_LitVar(pLits[i])];
    return Frame;
}

void Gip_SolverDetachClause( Gip_Solver_t * p, int Cref )
{
    Gip_WatchersDetach( p, Cref );
    Gip_CdbFreeClause( &p->Cdb, Cref );
}

/**Function*************************************************************

  Synopsis    [Removes all temporary clauses and the constrainAct assignment.]

  Description [Unlike rIC3, nPropagated is decremented for every removed
  trail entry below the propagation frontier, keeping BCP consistent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverCleanTemporary( Gip_Solver_t * p )
{
    while ( Vec_IntSize(p->Cdb.vTemp) > 0 )
        Gip_SolverDetachClause( p, Vec_IntPop(p->Cdb.vTemp) );
    if ( p->pValue[p->constrainAct] != GIP_NONE )
    {
        int i, Lit, k = 0;
        Vec_IntForEachEntry( p->vTrail, Lit, i )
        {
            if ( Gip_LitVar(Lit) != p->constrainAct )
                Vec_IntWriteEntry( p->vTrail, k++, Lit );
            else if ( i < p->nPropagated )
                p->nPropagated--;
        }
        Vec_IntShrink( p->vTrail, k );
        Gip_SolverSetNone( p, p->constrainAct );
    }
}

static int Gip_SolverLocked( Gip_Solver_t * p, int Cref )
{
    int Lit0 = Gip_ClaLits( &p->Cdb.Alloc, Cref )[0];
    return Gip_SolverLitValue( p, Lit0 ) == GIP_TRUE && p->pReason[Gip_LitVar(Lit0)] == Cref;
}

// sort helper for clean_learnt: descending activity
typedef struct Gip_ActPair_t_ { float act; int cref; int order; } Gip_ActPair_t;
// quickselect: afterwards a[0..k) hold the k entries with the largest activities (unordered)
static void Gip_SelectTop( Gip_ActPair_t * a, int n, int k )
{
    int lo = 0, hi = n - 1;
    if ( k >= n )
        return;
    while ( lo < hi )
    {
        float pivot = a[(lo + hi) / 2].act;
        int i = lo, j = hi;
        while ( i <= j )
        {
            while ( a[i].act > pivot ) i++;
            while ( a[j].act < pivot ) j--;
            if ( i <= j )
            {
                Gip_ActPair_t t = a[i]; a[i] = a[j]; a[j] = t;
                i++; j--;
            }
        }
        if ( k <= j )
            hi = j;
        else if ( k >= i )
            lo = i;
        else
            break;
    }
}
static int Gip_ActPairCmp( const void * a, const void * b )
{
    const Gip_ActPair_t * pa = (const Gip_ActPair_t *)a, * pb = (const Gip_ActPair_t *)b;
    if ( pa->act > pb->act ) return -1;
    if ( pa->act < pb->act ) return 1;
    // Keep equal-activity clauses in their input order on every platform.
    return pa->order - pb->order;
}

/**Function*************************************************************

  Synopsis    [Reduces the learnt clause set.]

  Description [Keeps the top third by activity; below that keeps only
  locked or binary clauses; then garbage-collects.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverCleanLearnt( Gip_Solver_t * p, int fFull )
{
    int nLearnt = Vec_IntSize( p->Cdb.vLearnt );
    int nTrans  = Vec_IntSize( p->Cdb.vTrans );
    Gip_ActPair_t * pPairs;
    int i, l;
    abctime clk;
    if ( !( (fFull && nLearnt * 15 > nTrans) || (nLearnt > nTrans && (!p->fCleanSkip || nLearnt > p->nCleanWait)) ) )
        return;
    // without a conflict since a cleaning that removed nothing (no new clause, the same
    // activities), the cleaning would again remove nothing
    if ( p->fCleanSkip && p->nCleanIdle == p->Stats.nConflicts )
        return;
    clk = Abc_Clock();
    pPairs = ABC_ALLOC( Gip_ActPair_t, nLearnt );
    Vec_IntForEachEntry( p->Cdb.vLearnt, l, i )
    {
        pPairs[i].act  = Gip_ClaAct( &p->Cdb.Alloc, l );
        pPairs[i].cref = l;
        pPairs[i].order = i;
    }
    // the original (rIC3) cleaning sorts all learnt clauses by activity; the selection keeps the
    // same number of clauses but breaks ties differently and leaves them unordered
    if ( p->fFastClean )
        Gip_SelectTop( pPairs, nLearnt, nLearnt / 3 + 1 );
    else
        qsort( pPairs, (size_t)nLearnt, sizeof(Gip_ActPair_t), Gip_ActPairCmp );
    Vec_IntClear( p->Cdb.vLearnt );
    for ( i = 0; i < nLearnt; i++ )
    {
        l = pPairs[i].cref;
        if ( i > nLearnt / 3 && !Gip_SolverLocked(p, l) && Gip_ClaLen(&p->Cdb.Alloc, l) > 2 )
            Gip_SolverDetachClause( p, l );
        else
            Vec_IntPush( p->Cdb.vLearnt, l );
    }
    ABC_FREE( pPairs );
    p->Stats.nCleanL++;
    p->Stats.nCleanLDel += nLearnt - Vec_IntSize(p->Cdb.vLearnt);
    p->Stats.nCleanLNone += nLearnt == Vec_IntSize(p->Cdb.vLearnt);
    p->nCleanIdle = nLearnt == Vec_IntSize(p->Cdb.vLearnt) ? p->Stats.nConflicts : -1;
    // when the kept clauses (locked or binary) still exceed the threshold, the cleaning would
    // repeat at every decision while removing little: wait until the learnt clauses grow by 1/16
    // (with fCleanSkip, set by pdr2; pdr -s cleans as before)
    nLearnt = Vec_IntSize( p->Cdb.vLearnt );
    p->nCleanWait = nLearnt > nTrans ? nLearnt + nLearnt / 16 : 0;
    Gip_SolverGarbageCollect( p );
    p->Stats.timeCleanL += Abc_Clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Removes one literal in place (self-subsumption).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverStrengthenClause( Gip_Solver_t * p, int Cref, int Lit )
{
    Gip_Alloc_t * pA = &p->Cdb.Alloc;
    int * pLits = Gip_ClaLits( pA, Cref );
    int nLits = Gip_ClaLen( pA, Cref );
    int pos, fLearnt = Gip_ClaIsLearnt( pA, Cref );
    assert( nLits > 2 );
    for ( pos = 0; pos < nLits; pos++ )
        if ( pLits[pos] == Lit )
            break;
    assert( pos < nLits );
    Gip_WatchersDetach( p, Cref );
    // swap_remove: move last literal into pos; the trailing words (activity if learnt, tag)
    // move down into the freed literal slot
    pLits[pos] = pLits[nLits-1];
    for ( pos = 0; pos < fLearnt + 1; pos++ )
        pA->pData[Cref + nLits + pos] = pA->pData[Cref + nLits + 1 + pos];
    Gip_ClaSetLen( pA, Cref, nLits - 1 );
    Gip_WatchersAttach( p, Cref );
}

/**Function*************************************************************

  Synopsis    [Compacts the arena when a third of it is wasted.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverGarbageCollect( Gip_Solver_t * p )
{
    Gip_Alloc_t * pOld = &p->Cdb.Alloc;
    Gip_Alloc_t New;
    int i, j, Lit, Cref;
    if ( pOld->nWasted * 3 <= pOld->nSize )
        return;
    Gip_AllocInit( &New, pOld->nSize - pOld->nWasted );
    // watchers
    for ( i = 0; i < 2 * p->nVarsAlloc; i++ )
        for ( j = 0; j < p->pWatchers[i].nSize; j++ )
            p->pWatchers[i].pArray[j].clause = Gip_AllocReloc( pOld, p->pWatchers[i].pArray[j].clause, &New );
    // clause lists
    Vec_IntForEachEntry( p->Cdb.vTrans, Cref, i )
        Vec_IntWriteEntry( p->Cdb.vTrans, i, Gip_AllocReloc(pOld, Cref, &New) );
    Vec_IntForEachEntry( p->Cdb.vLemmas, Cref, i )
        Vec_IntWriteEntry( p->Cdb.vLemmas, i, Gip_AllocReloc(pOld, Cref, &New) );
    Vec_IntForEachEntry( p->Cdb.vLearnt, Cref, i )
        Vec_IntWriteEntry( p->Cdb.vLearnt, i, Gip_AllocReloc(pOld, Cref, &New) );
    Vec_IntForEachEntry( p->Cdb.vTemp, Cref, i )
        Vec_IntWriteEntry( p->Cdb.vTemp, i, Gip_AllocReloc(pOld, Cref, &New) );
    // reasons of trail literals
    Vec_IntForEachEntry( p->vTrail, Lit, i )
        if ( p->pReason[Gip_LitVar(Lit)] != GIP_CREF_NONE )
            p->pReason[Gip_LitVar(Lit)] = Gip_AllocReloc( pOld, p->pReason[Gip_LitVar(Lit)], &New );
    ABC_FREE( pOld->pData );
    p->Cdb.Alloc = New;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
