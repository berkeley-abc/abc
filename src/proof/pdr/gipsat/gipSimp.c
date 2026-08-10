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

// clauses longer than this many literals do not participate in subsumption
#define GIP_SUBSUME_MAX_LEN  100

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// in-place literal removal from a clause (non-watched position only)
static void Gip_ClaSwapRemoveLit( Gip_Alloc_t * pA, int Cref, int j )
{
    int * pLits = Gip_ClaLits( pA, Cref );
    int nLits = Gip_ClaLen( pA, Cref );
    assert( j > 1 && nLits > 2 );
    pLits[j] = pLits[nLits-1];
    if ( Gip_ClaIsLearnt(pA, Cref) )
        pA->pData[Cref + nLits] = pA->pData[Cref + nLits + 1];
    Gip_ClaSetLen( pA, Cref, nLits - 1 );
}

// removes satisfied clauses; strips false literals
static void Gip_SolverSimplifySatisfiedList( Gip_Solver_t * p, Vec_Int_t * vClauses )
{
    int i = 0;
    while ( i < Vec_IntSize(vClauses) )
    {
        int Cref = Vec_IntEntry( vClauses, i );
        int j = 0, fRemoved = 0;
        while ( j < Gip_ClaLen(&p->Cdb.Alloc, Cref) )
        {
            int Lit = Gip_ClaLits( &p->Cdb.Alloc, Cref )[j];
            int v = Gip_SolverLitValue( p, Lit );
            if ( v == GIP_TRUE )
            {
                Vec_IntWriteEntry( vClauses, i, Vec_IntEntryLast(vClauses) );
                Vec_IntPop( vClauses );
                Gip_SolverDetachClause( p, Cref );
                fRemoved = 1;
                break;
            }
            if ( v == GIP_FALSE )
            {
                if ( j <= 1 )
                {
                    // a watched literal is false at level 0; BCP invariant
                    // guarantees the clause is satisfied -- drop it
                    Vec_IntWriteEntry( vClauses, i, Vec_IntEntryLast(vClauses) );
                    Vec_IntPop( vClauses );
                    Gip_SolverDetachClause( p, Cref );
                    fRemoved = 1;
                    break;
                }
                Gip_ClaSwapRemoveLit( &p->Cdb.Alloc, Cref, j );
            }
            else
                j++;
        }
        if ( !fRemoved )
            i++;
    }
}

/**Function*************************************************************

  Synopsis    [Removes clauses satisfied at level 0 from all lists.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gip_SolverSimplifySatisfied( Gip_Solver_t * p )
{
    assert( Gip_SolverLevelOf(p) == 0 );
    if ( p->nLastNumAssign >= Vec_IntSize(p->vTrail) )
        return;
    Gip_SolverSimplifySatisfiedList( p, p->Cdb.vLemmas );
    Gip_SolverSimplifySatisfiedList( p, p->Cdb.vLearnt );
    Gip_SolverSimplifySatisfiedList( p, p->Cdb.vTrans );
    p->nLastNumAssign = Vec_IntSize( p->vTrail );
}

typedef struct Gip_SubEnt_t_
{
    int          Cref;
    Vec_Int_t *  vSorted;    // literals sorted ascending
} Gip_SubEnt_t;

// stable counting sort by clause length (lengths are 2..GIP_SUBSUME_MAX_LEN);
// ties keep insertion order, so the result is machine-independent
static void Gip_SubEntSortByLen( Gip_SubEnt_t * pEnts, int nEnts )
{
    int pOffset[GIP_SUBSUME_MAX_LEN + 2] = {0};
    Gip_SubEnt_t * pTmp;
    int i, len, sum = 0;
    for ( i = 0; i < nEnts; i++ )
    {
        len = Vec_IntSize( pEnts[i].vSorted );
        assert( len >= 0 && len <= GIP_SUBSUME_MAX_LEN );
        pOffset[len]++;
    }
    for ( i = 0; i <= GIP_SUBSUME_MAX_LEN + 1; i++ )
    {
        int c = pOffset[i];
        pOffset[i] = sum;
        sum += c;
    }
    pTmp = ABC_ALLOC( Gip_SubEnt_t, nEnts );
    for ( i = 0; i < nEnts; i++ )
        pTmp[ pOffset[Vec_IntSize(pEnts[i].vSorted)]++ ] = pEnts[i];
    memcpy( pEnts, pTmp, sizeof(Gip_SubEnt_t) * nEnts );
    ABC_FREE( pTmp );
}

// returns 1 (full subsume) with *pDiff = -1, or 0 with *pDiff = the single
// literal l of vSelf whose negation appears in vOther (self-subsumption
// candidate), or 0 with *pDiff = -1 (no relation). Both inputs sorted,
// one literal per variable.
static int Gip_SubsumeExceptOne( Vec_Int_t * vSelf, Vec_Int_t * vOther, int * pDiff )
{
    int i = 0, j = 0, nDiff = 0;
    *pDiff = -1;
    if ( Vec_IntSize(vSelf) > Vec_IntSize(vOther) )
        return 0;
    while ( i < Vec_IntSize(vSelf) )
    {
        int a, b;
        if ( j >= Vec_IntSize(vOther) )
            { *pDiff = -1; return 0; }
        a = Vec_IntEntry( vSelf, i );
        b = Vec_IntEntry( vOther, j );
        if ( Gip_LitVar(a) == Gip_LitVar(b) )
        {
            if ( a != b )
            {
                if ( ++nDiff > 1 )
                    { *pDiff = -1; return 0; }
                *pDiff = a;
            }
            i++; j++;
        }
        else if ( Gip_LitVar(b) < Gip_LitVar(a) )
            j++;
        else
            { *pDiff = -1; return 0; }
    }
    if ( nDiff == 0 )
        { *pDiff = -1; return 1; }
    return 0;
}

static void Gip_SubEntRefresh( Gip_Solver_t * p, Gip_SubEnt_t * pEnt )
{
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, pEnt->Cref );
    int nLits = Gip_ClaLen( &p->Cdb.Alloc, pEnt->Cref );
    int i;
    Vec_IntClear( pEnt->vSorted );
    for ( i = 0; i < nLits; i++ )
        Vec_IntPush( pEnt->vSorted, pLits[i] );
    Vec_IntSort( pEnt->vSorted, 0 );
}

/**Function*************************************************************

  Synopsis    [Forward subsumption + self-subsumption over the lemma list.]

  Description [Overlong clauses are excluded from subsumption but kept
  in the lemma list. The lemma list is rewritten in place.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Gip_SolverSimplifySubsume( Gip_Solver_t * p )
{
    Vec_Int_t * vLemmas = p->Cdb.vLemmas;
    int nEnts = 0, i, j, Cref;
    Gip_SubEnt_t * pEnts;
    Vec_Ptr_t * vOccurs;    // per var: Vec_Int_t* of entry indices (lazy)
    if ( Vec_IntSize(vLemmas) == 0 )
        return;
    pEnts = ABC_ALLOC( Gip_SubEnt_t, Vec_IntSize(vLemmas) );
    Vec_IntForEachEntry( vLemmas, Cref, i )
    {
        if ( Gip_ClaLen(&p->Cdb.Alloc, Cref) > GIP_SUBSUME_MAX_LEN )
            continue;
        pEnts[nEnts].Cref = Cref;
        pEnts[nEnts].vSorted = Vec_IntAlloc( Gip_ClaLen(&p->Cdb.Alloc, Cref) );
        Gip_SubEntRefresh( p, &pEnts[nEnts] );
        nEnts++;
    }
    Gip_SubEntSortByLen( pEnts, nEnts );
    // occurs table over entry indices
    vOccurs = Vec_PtrStart( p->nVarsAlloc );
    for ( i = 0; i < nEnts; i++ )
    {
        int Lit;
        Vec_IntForEachEntry( pEnts[i].vSorted, Lit, j )
        {
            Vec_Int_t * vO = (Vec_Int_t *)Vec_PtrEntry( vOccurs, Gip_LitVar(Lit) );
            if ( vO == NULL )
            {
                vO = Vec_IntAlloc( 8 );
                Vec_PtrWriteEntry( vOccurs, Gip_LitVar(Lit), vO );
            }
            Vec_IntPush( vO, i );
        }
    }
    for ( i = 0; i < nEnts; i++ )
    {
        int bestLit = -1, bestOcc = ABC_INFINITY, Lit, sub, k;
        Vec_Int_t * vCand;
        if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, pEnts[i].Cref) )
            continue;
        // pick the literal with the fewest occurrences
        Vec_IntForEachEntry( pEnts[i].vSorted, Lit, j )
        {
            Vec_Int_t * vO = (Vec_Int_t *)Vec_PtrEntry( vOccurs, Gip_LitVar(Lit) );
            int nOcc = vO ? Vec_IntSize(vO) : 0;
            if ( nOcc < bestOcc )
            {
                bestOcc = nOcc;
                bestLit = Lit;
            }
        }
        vCand = (Vec_Int_t *)Vec_PtrEntry( vOccurs, Gip_LitVar(bestLit) );
        if ( vCand == NULL )
            continue;
        Vec_IntForEachEntry( vCand, sub, k )
        {
            int diff, res;
            if ( sub == i )
                continue;
            if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, pEnts[sub].Cref) )
                continue;
            if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, pEnts[i].Cref) )
                break;
            res = Gip_SubsumeExceptOne( pEnts[i].vSorted, pEnts[sub].vSorted, &diff );
            if ( res )
            {
                Gip_SolverDetachClause( p, pEnts[sub].Cref );
                p->Stats.nSubsume++;
            }
            else if ( diff != -1 )
            {
                p->Stats.nSelfSubsume++;
                if ( Vec_IntSize(pEnts[i].vSorted) == Vec_IntSize(pEnts[sub].vSorted) )
                {
                    if ( Vec_IntSize(pEnts[i].vSorted) > 2 )
                    {
                        Gip_SolverDetachClause( p, pEnts[sub].Cref );
                        Gip_SolverStrengthenClause( p, pEnts[i].Cref, diff );
                        Gip_SubEntRefresh( p, &pEnts[i] );
                    }
                }
                else
                {
                    Gip_SolverStrengthenClause( p, pEnts[sub].Cref, Gip_LitNot(diff) );
                    Gip_SubEntRefresh( p, &pEnts[sub] );
                }
            }
        }
    }
    // rebuild the lemma list: overlong clauses (skipped above) + survivors
    {
        Vec_Int_t * vNew = Vec_IntAlloc( Vec_IntSize(vLemmas) );
        Vec_IntForEachEntry( vLemmas, Cref, i )
            if ( Gip_ClaLen(&p->Cdb.Alloc, Cref) > GIP_SUBSUME_MAX_LEN && !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                Vec_IntPush( vNew, Cref );
        for ( i = 0; i < nEnts; i++ )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, pEnts[i].Cref) )
                Vec_IntPush( vNew, pEnts[i].Cref );
        Vec_IntClear( vLemmas );
        Vec_IntAppend( vLemmas, vNew );
        Vec_IntFree( vNew );
    }
    for ( i = 0; i < nEnts; i++ )
        Vec_IntFree( pEnts[i].vSorted );
    ABC_FREE( pEnts );
    {
        Vec_Int_t * vO;
        Vec_PtrForEachEntry( Vec_Int_t *, vOccurs, vO, i )
            if ( vO ) Vec_IntFree( vO );
        Vec_PtrFree( vOccurs );
    }
}

/**Function*************************************************************

  Synopsis    [Top-level simplify, throttled by solve count.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_SolverSimplify( Gip_Solver_t * p )
{
    abctime clk;
    assert( Gip_SolverLevelOf(p) == 0 );
    if ( p->Stats.nSolves <= p->nLastSimplify + 100 )
        return;
    clk = Abc_Clock();
    if ( p->nLastNumAssign < Vec_IntSize(p->vTrail) )
        Gip_SolverSimplifySatisfied( p );
    if ( p->nLastNumLemma + 1000 < Vec_IntSize(p->Cdb.vLemmas) )
    {
        Gip_SolverSimplifySubsume( p );
        p->nLastNumLemma = Vec_IntSize( p->Cdb.vLemmas );
    }
    Gip_SolverGarbageCollect( p );
    p->nLastSimplify = p->Stats.nSolves;
    p->Stats.timeSimplify += Abc_Clock() - clk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
