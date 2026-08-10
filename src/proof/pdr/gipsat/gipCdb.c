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
    return 1 + (unsigned)Gip_ClaLen(p, Cref) + (unsigned)Gip_ClaIsLearnt(p, Cref);
}

static int Gip_AllocClause( Gip_Alloc_t * p, int * pLits, int nLits, int fTrans, int fLearnt )
{
    int cid, i;
    unsigned nWords = 1 + (unsigned)nLits + (unsigned)(fLearnt != 0);
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

static int Gip_CdbAlloc( Gip_Cdb_t * p, int * pLits, int nLits, int Kind )
{
    int cid = Gip_AllocClause( &p->Alloc, pLits, nLits, Kind == GIP_CLA_TRANS, Kind == GIP_CLA_LEARNT );
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

  Synopsis    [Bumps the activity of a learnt clause.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_CdbBump( Gip_Cdb_t * p, int Cref )
{
    float act;
    if ( !Gip_ClaIsLearnt(&p->Alloc, Cref) )
        return;
    act = Gip_ClaAct( &p->Alloc, Cref ) + p->actInc;
    Gip_ClaSetAct( &p->Alloc, Cref, act );
    if ( act > (float)1e20 )
    {
        int i, l;
        Vec_IntForEachEntry( p->vLearnt, l, i )
            Gip_ClaSetAct( &p->Alloc, l, Gip_ClaAct(&p->Alloc, l) * (float)1e-20 );
        p->actInc *= (float)1e-20;
    }
}

void Gip_CdbDecay( Gip_Cdb_t * p )
{
    p->actInc *= (float)(1.0 / 0.99);
}

/**Function*************************************************************

  Synopsis    [Attaches a clause to the database and the watchers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverAttachClause( Gip_Solver_t * p, int * pLits, int nLits, int Kind )
{
    int cid;
    assert( nLits > 1 );
    cid = Gip_CdbAlloc( &p->Cdb, pLits, nLits, Kind );
    Gip_WatchersAttach( p, cid );
    return cid;
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
typedef struct Gip_ActPair_t_ { float act; int cref; } Gip_ActPair_t;
static int Gip_ActPairCmp( const void * a, const void * b )
{
    float fa = ((Gip_ActPair_t *)a)->act, fb = ((Gip_ActPair_t *)b)->act;
    if ( fa > fb ) return -1;
    if ( fa < fb ) return 1;
    return 0;
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
    if ( !( (fFull && nLearnt * 15 > nTrans) || nLearnt > nTrans ) )
        return;
    clk = Abc_Clock();
    pPairs = ABC_ALLOC( Gip_ActPair_t, nLearnt );
    Vec_IntForEachEntry( p->Cdb.vLearnt, l, i )
    {
        pPairs[i].act  = Gip_ClaAct( &p->Cdb.Alloc, l );
        pPairs[i].cref = l;
    }
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
    // swap_remove: move last literal into pos; if learnt, move the
    // activity word into the freed literal slot
    pLits[pos] = pLits[nLits-1];
    if ( fLearnt )
        pA->pData[Cref + nLits] = pA->pData[Cref + nLits + 1];
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
