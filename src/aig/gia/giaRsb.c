/**CFile****************************************************************

  FileName    [giaRsb.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact GIA-based resubstitution.]

  Synopsis    [Window resubstitution with compact truth tables and deferred levels.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaRsb.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "aig/gia/giaEdit.h"

ABC_NAMESPACE_IMPL_START

enum
{
    RSUB_LEAF_MAX = 16,
    RSUB_DIV_MAX = 150,
    RSUB_CUT_FANOUT_MAX = 100000
};
enum
{
    RSUB_CACHE_BINS = 65536,
    RSUB_CACHE_LIMIT = 16384
};
enum
{
    RSUB_NEIGHBOR_ROUNDS = 3,
    RSUB_NEIGHBOR_BINS = 262144,
    RSUB_NEIGHBOR_TRIES = 4
};
enum
{
    RSUB_RECIPE_LIMIT = 16384,
    RSUB_RECIPE_PER_KEY = 8,
    RSUB_RECIPE_ROOT_MAX = 64,
    RSUB_RECIPE_MATCH_MAX = 4 * RSUB_DIV_MAX
};
typedef struct Rsub_Cut_t_ Rsub_Cut_t;
typedef struct Rsub_Man_t_ Rsub_Man_t;
typedef struct Rsub_Cache_t_ Rsub_Cache_t;

struct Rsub_Cache_t_
{
    Rsub_Cache_t * pNext;
    unsigned Hash;
    int nCode, A, B, Phase;
    unsigned Code[1];
};

typedef struct Rsub_Early_t_
{
    struct Rsub_Early_t_ * Next;
    int nLeaves, nNodes, Root, A, B, Phase;
    unsigned ZeroMask;
    unsigned short Ops[2 * RSUB_DIV_MAX];
    unsigned char Used[RSUB_DIV_MAX];
} Rsub_Early_t;
typedef struct Rsub_Neighbor_t_
{
    unsigned Hash;
    int Count, Good, nRecipes;
    Rsub_Early_t * Recipes;
} Rsub_Neighbor_t;

typedef struct Rsub_Match_t_
{
    int Slot, Id;
    struct Rsub_Match_t_ * Next;
} Rsub_Match_t;

struct Rsub_Cut_t_
{
    int Leaves[RSUB_LEAF_MAX];
    int nLeaves, Saved;
};

struct Rsub_Man_t_
{
    Gie_Man_t M;
    int nCutMax, nSteps, nMinSaved, fVerbose;
    Vec_Int_t *vNodes, *vDivs, *vTodo;
    word * pSims;
    Rsub_Cache_t ** pCache;
    int nCache, nCacheBins;
    unsigned * pNeighborhood;
    Rsub_Neighbor_t * pNeighbors;
    int nNeighborBins, nNeighborSkips, nEarlyItems, nEarlyHits;
    double nCacheHits, nCacheMisses;
    int nWords;
    abctime timeCuts, timeDivs, timeSim, timeSearch, timeUpdate;
    double nCuts, nDivs;
    int nLimited, nRewritten, nMerged, nConst, nEqual, nPair, nSkipped;
};

/**Function*************************************************************

  Synopsis    [Finds a bounded search-history and recipe bucket.]

  Description [Colliding keys evict their old recipes. Slack and the global equality
  filter distinguish neighborhoods with different replacement opportunities.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Rsub_Neighbor_t * Rsub_NeighborFind( Rsub_Man_t * p, int Id )
{
    unsigned Hash = p->pNeighborhood[Id] ^ ( p->M.pObjs[Id].CanEqual * 0x9e3779b9u );
    int Slack = p->M.fKeepLevel ? Abc_MinInt( 8, p->M.pFans[Id].Required - p->M.pObjs[Id].Level ) : 9;
    Rsub_Neighbor_t * q;
    Hash = Gie_MixColor( Hash ^ Slack * 0x74174113u ) | 1;
    q = p->pNeighbors + ( Hash & ( p->nNeighborBins - 1 ) );
    if ( q->Hash != Hash )
    {
        Rsub_Early_t *a, *b;
        for ( a = q->Recipes; a; a = b )
        {
            b = a->Next;
            ABC_FREE( a );
            p->nEarlyItems--;
        }
        q->Recipes = NULL;
        q->nRecipes = 0;
        q->Hash = Hash;
        q->Count = q->Good = 0;
    }
    return q;
}

static inline int Rsub_Mffc( Rsub_Man_t * p, int Id, Rsub_Cut_t * pCut, int fMark )
{
    return Gie_Mffc( &p->M, Id, pCut->Leaves, pCut->nLeaves, fMark );
}

/**Function*************************************************************

  Synopsis    [Constructs one reconvergence-driven cut in reference order.]

  Description [Prefer expansions introducing fewer new leaves, breaking
  ties by decreasing level. Marks include the interior of the cut.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Rsub_Cut( Rsub_Man_t * p, int Root, Rsub_Cut_t * pCut )
{
    int i, Best, Cost, BestCost, Id, a, b;
    Gie_TruthNext( &p->M );
    pCut->nLeaves = 2;
    pCut->Leaves[0] = p->M.pObjs[Root].Fan[0] >> 1;
    pCut->Leaves[1] = p->M.pObjs[Root].Fan[1] >> 1;
    p->M.pObjs[Root].TruthMark = p->M.TruthMark;
    p->M.pObjs[pCut->Leaves[0]].TruthMark = p->M.TruthMark;
    p->M.pObjs[pCut->Leaves[1]].TruthMark = p->M.TruthMark;
    for ( ;; )
    {
        Best = -1;
        BestCost = 3;
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            Id = pCut->Leaves[i];
            if ( p->M.pObjs[Id].Type != GIE_AND ) continue;
            a = p->M.pObjs[Id].Fan[0] >> 1;
            b = p->M.pObjs[Id].Fan[1] >> 1;
            Cost = ( p->M.pObjs[a].TruthMark != p->M.TruthMark ) + ( p->M.pObjs[b].TruthMark != p->M.TruthMark );
            // Cut growth follows two fanins; it does not scan these fanouts.
            // Low caps lost quality in the wide-window experiments. Keep a
            // separate, generous limit from fanout-based divisor expansion.
            if ( Cost == 2 && p->M.pObjs[Id].Refs > RSUB_CUT_FANOUT_MAX ) continue;
            if ( Cost < BestCost ||
                 ( Cost == BestCost && p->M.pObjs[Id].Level > p->M.pObjs[pCut->Leaves[Best]].Level ) )
                Best = i, BestCost = Cost;
            if ( BestCost == 0 ) break;
        }
        if ( Best < 0 || pCut->nLeaves - 1 + BestCost > p->nCutMax ) break;
        Id = pCut->Leaves[Best];
        for ( i = Best + 1; i < pCut->nLeaves; i++ )
            pCut->Leaves[i - 1] = pCut->Leaves[i];
        pCut->nLeaves--;
        for ( i = 0; i < 2; i++ )
        {
            a = p->M.pObjs[Id].Fan[i] >> 1;
            if ( p->M.pObjs[a].TruthMark == p->M.TruthMark ) continue;
            p->M.pObjs[a].TruthMark = p->M.TruthMark;
            pCut->Leaves[pCut->nLeaves++] = a;
        }
    }
    assert( pCut->nLeaves <= p->nCutMax );
    p->nCuts++;
}

/**Function*************************************************************

  Synopsis    [Collects a bounded cone and fuses its one-word simulation.]

  Description [Every recursive entry consumes the window budget before descending.
  Recursion is therefore bounded by RSUB_DIV_MAX, even for a deep input AIG.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_Collect_rec( Rsub_Man_t * p, int Id, int Limit, int * Visited, int Small )
{
    Gie_Obj_t * Obj = p->M.pObjs + Id;
    int a, b, Slot;
    if ( Obj->TruthMark == p->M.TruthMark ) return 1;
    assert( Obj->Type == GIE_AND );
    Obj->TruthMark = p->M.TruthMark;
    if ( ++*Visited >= Limit ) return 0;
    a = Obj->Fan[0];
    b = Obj->Fan[1];
    if ( !Rsub_Collect_rec( p, a >> 1, Limit, Visited, Small ) ||
         !Rsub_Collect_rec( p, b >> 1, Limit, Visited, Small ) )
        return 0;
    Slot = Vec_IntSize( p->vNodes );
    Obj->Truth = (unsigned short) Slot;
    if ( Obj->Mark != p->M.Mark ) Vec_IntPush( p->vDivs, Slot );
    Vec_IntPush( p->vNodes, Id );
    if ( Small )
        p->pSims[Slot] = ( p->pSims[p->M.pObjs[a >> 1].Truth] ^ ( (word) 0 - ( a & 1 ) ) ) &
                         ( p->pSims[p->M.pObjs[b >> 1].Truth] ^ ( (word) 0 - ( b & 1 ) ) );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Seeds cut variables and collects the root fanin cone.]

  Description [The root cone is visited in topological order. Removable MFFC nodes
  get truth slots but are excluded from the external divisor list.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_Collect( Rsub_Man_t * p, int Root, Rsub_Cut_t * pCut )
{
    static const word Vars[6] = { ABC_CONST( 0xaaaaaaaaaaaaaaaa ), ABC_CONST( 0xcccccccccccccccc ),
                                  ABC_CONST( 0xf0f0f0f0f0f0f0f0 ), ABC_CONST( 0xff00ff00ff00ff00 ),
                                  ABC_CONST( 0xffff0000ffff0000 ), ABC_CONST( 0xffffffff00000000 ) };
    int i, Id, nVisited = pCut->nLeaves, Small = pCut->nLeaves <= 6;
    // Reserve nCutMax leaf slots, keeping the internal-node budget fixed.
    int Limit = RSUB_DIV_MAX - p->nCutMax + pCut->nLeaves;
    Vec_IntClear( p->vNodes );
    Vec_IntClear( p->vDivs );
    Gie_TruthNext( &p->M );
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        Id = pCut->Leaves[i];
        p->M.pObjs[Id].TruthMark = p->M.TruthMark;
        p->M.pObjs[Id].Truth = (unsigned short) i;
        Vec_IntPush( p->vNodes, Id );
        Vec_IntPush( p->vDivs, i );
        if ( Small ) p->pSims[i] = Vars[i];
    }
    if ( !Rsub_Collect_rec( p, Root, Limit, &nVisited, Small ) )
    {
        p->nLimited++;
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Extends a window only after its own cone fails to simplify.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Rsub_Expand( Rsub_Man_t * p, int Root, Rsub_Cut_t * pCut )
{
    int i, Id, Edge, a, b;
    // Use the same fixed internal-node budget as cone collection.
    int Limit = RSUB_DIV_MAX - p->nCutMax + pCut->nLeaves;
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    for ( i = 0; i < Vec_IntSize( p->vDivs ) && Vec_IntSize( p->vNodes ) < Limit; i++ )
    {
        Id = Vec_IntEntry( p->vNodes, Vec_IntEntry( p->vDivs, i ) );
        if ( p->M.pObjs[Id].Refs > 100 ) continue;
        for ( Edge = p->M.pFans[Id].Head; Edge; Edge = p->M.pFans[Edge >> 1].Next[Edge & 1] )
        {
            int Fan = Edge >> 1;
            Gie_Obj_t * pObj = p->M.pObjs + Fan;
            if ( pObj->Type != GIE_AND || pObj->Busy || pObj->TruthMark == p->M.TruthMark ) continue;
            // An unvisited simple node may have equal or constant fanins.
            // Leave its simplification to its own visit instead of promoting it.
            if ( Gie_Simplify( pObj->Fan[0], pObj->Fan[1] ) >= 0 ) continue;
            a = pObj->Fan[0] >> 1;
            b = pObj->Fan[1] >> 1;
            if ( a == Root || b == Root || p->M.pObjs[a].TruthMark != p->M.TruthMark ||
                 p->M.pObjs[b].TruthMark != p->M.TruthMark )
                continue;
            assert( p->M.pObjs[a].Mark != p->M.Mark && p->M.pObjs[b].Mark != p->M.Mark );
            pObj->Level = 1 + Abc_MaxInt( p->M.pObjs[a].Level, p->M.pObjs[b].Level );
            if ( pObj->Level > Required ) continue;
            pObj->TruthMark = p->M.TruthMark;
            pObj->Truth = (unsigned short) Vec_IntSize( p->vNodes );
            Vec_IntPush( p->vDivs, Vec_IntSize( p->vNodes ) );
            Vec_IntPush( p->vNodes, Fan );
            if ( pCut->nLeaves <= 6 )
                p->pSims[pObj->Truth] = ( p->pSims[p->M.pObjs[a].Truth] ^ ( (word) 0 - ( pObj->Fan[0] & 1 ) ) ) &
                                        ( p->pSims[p->M.pObjs[b].Truth] ^ ( (word) 0 - ( pObj->Fan[1] & 1 ) ) );
            if ( Vec_IntSize( p->vNodes ) == Limit ) break;
        }
    }
    p->nDivs += Vec_IntSize( p->vDivs );
}

/**Function*************************************************************

  Synopsis    [Evaluates exact truth tables at the actual cut width.]

  Description [Bit zero is the all-zero cut assignment. Functions remain
  unnormalized; edge phases are applied when evaluating a candidate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Rsub_Simulate( Rsub_Man_t * p, Rsub_Cut_t * pCut, int Start )
{
    static const word Vars[6] = { ABC_CONST( 0xaaaaaaaaaaaaaaaa ), ABC_CONST( 0xcccccccccccccccc ),
                                  ABC_CONST( 0xf0f0f0f0f0f0f0f0 ), ABC_CONST( 0xff00ff00ff00ff00 ),
                                  ABC_CONST( 0xffff0000ffff0000 ), ABC_CONST( 0xffffffff00000000 ) };
    int i, w, Id, a, b;
    word *pOut, *pIn0, *pIn1, Phase0, Phase1;
    p->nWords = pCut->nLeaves <= 6 ? 1 : 1 << ( pCut->nLeaves - 6 );
    if ( Start == 0 )
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            pOut = p->pSims + i * p->nWords;
            if ( i < 6 )
                for ( w = 0; w < p->nWords; w++ )
                    pOut[w] = Vars[i];
            else
                for ( w = 0; w < p->nWords; w++ )
                    pOut[w] = (word) 0 - ( ( w >> ( i - 6 ) ) & 1 );
        }
    for ( i = Abc_MaxInt( pCut->nLeaves, Start ); i < Vec_IntSize( p->vNodes ); i++ )
    {
        Id = Vec_IntEntry( p->vNodes, i );
        a = p->M.pObjs[Id].Fan[0];
        b = p->M.pObjs[Id].Fan[1];
        assert( p->M.pObjs[a >> 1].Truth < i && p->M.pObjs[b >> 1].Truth < i );
        pIn0 = p->pSims + p->M.pObjs[a >> 1].Truth * p->nWords;
        pIn1 = p->pSims + p->M.pObjs[b >> 1].Truth * p->nWords;
        pOut = p->pSims + i * p->nWords;
        Phase0 = (word) 0 - ( a & 1 );
        Phase1 = (word) 0 - ( b & 1 );
        for ( w = 0; w < p->nWords; w++ )
            pOut[w] = ( pIn0[w] ^ Phase0 ) & ( pIn1[w] ^ Phase1 );
    }
}

static inline word * Rsub_Truth( Rsub_Man_t * p, int Lit )
{
    return p->pSims + ( Lit >> 1 ) * p->nWords;
}

/**Function*************************************************************

  Synopsis    [Searches constant, wire, OR, and AND replacements.]

  Description [Normalized candidates use the same containment priority
  as resub. The result is an AND over at most two divisor literals.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_Search( Rsub_Man_t * p, int Root, Rsub_Cut_t * pCut, int * pA, int * pB, int fOnlyZero )
{
    int Pos[RSUB_DIV_MAX], Neg[RSUB_DIV_MAX], nPos = 0, nNeg = 0;
    int i, k, w, Slot, Lit, Id, OutPhase, Phase, a, b;
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    word * pRoot = p->pSims + p->M.pObjs[Root].Truth * p->nWords;
    word *pData, *pData1, OutMask, Mask, Mask1;
    OutPhase = pRoot[0] & 1;
    OutMask = (word) 0 - OutPhase;
    if ( pCut->Saved < p->nMinSaved ) return -1;
    for ( w = 0; w < p->nWords; w++ )
        if ( pRoot[w] ^ OutMask ) break;
    if ( w == p->nWords )
    {
        *pA = *pB = OutPhase;
        p->nConst++;
        return 0;
    }
    Vec_IntForEachEntry ( p->vDivs, Slot, i )
    {
        Id = Vec_IntEntry( p->vNodes, Slot );
        pData = p->pSims + Slot * p->nWords;
        Phase = ( pData[0] & 1 ) ^ OutPhase;
        Mask = (word) 0 - Phase;
        for ( w = 0; w < p->nWords; w++ )
            if ( ( pData[w] ^ Mask ) != pRoot[w] ) break;
        if ( w == p->nWords && p->M.pObjs[Id].Level <= Required )
        {
            *pA = *pB = 2 * Id + Phase;
            p->nEqual++;
            return 0;
        }
    }
    if ( fOnlyZero || p->nSteps == 0 || pCut->Saved <= p->nMinSaved ) return -1;
    Vec_IntForEachEntry ( p->vDivs, Slot, i )
    {
        Id = Vec_IntEntry( p->vNodes, Slot );
        if ( p->M.pObjs[Id].Level >= Required ) continue;
        pData = p->pSims + Slot * p->nWords;
        Phase = pData[0] & 1;
        Mask = (word) 0 - Phase;
        Lit = 2 * Slot + Phase;
        for ( w = 0; w < p->nWords; w++ )
            if ( ( pData[w] ^ Mask ) & ~( pRoot[w] ^ OutMask ) ) break;
        if ( w == p->nWords )
        {
            Pos[nPos++] = Lit;
            continue;
        }
        // Both normalized functions are zero at bit zero, so complemented
        // positive containment is impossible when every assignment is care.
        for ( w = 0; w < p->nWords; w++ )
            if ( ~( pData[w] ^ Mask ) & ( pRoot[w] ^ OutMask ) ) break;
        if ( w == p->nWords )
        {
            Neg[nNeg++] = Lit;
            continue;
        }
        for ( w = 0; w < p->nWords; w++ )
            if ( ( pData[w] ^ Mask ) & ( pRoot[w] ^ OutMask ) ) break;
        if ( w == p->nWords ) Neg[nNeg++] = Lit ^ 1;
    }
    for ( i = 0; i < nPos; i++ )
    {
        pData = Rsub_Truth( p, Pos[i] );
        Mask = (word) 0 - ( Pos[i] & 1 );
        for ( k = i + 1; k < nPos; k++ )
        {
            pData1 = Rsub_Truth( p, Pos[k] );
            Mask1 = (word) 0 - ( Pos[k] & 1 );
            for ( w = 0; w < p->nWords; w++ )
                if ( ( ( pData[w] ^ Mask ) | ( pData1[w] ^ Mask1 ) ) != ( pRoot[w] ^ OutMask ) ) break;
            if ( w != p->nWords ) continue;
            a = Pos[i];
            b = Pos[k];
            *pA = 2 * Vec_IntEntry( p->vNodes, a >> 1 ) + ( ( a & 1 ) ^ 1 );
            *pB = 2 * Vec_IntEntry( p->vNodes, b >> 1 ) + ( ( b & 1 ) ^ 1 );
            p->nPair++;
            return OutPhase ^ 1;
        }
    }
    for ( i = 0; i < nNeg; i++ )
    {
        pData = Rsub_Truth( p, Neg[i] );
        Mask = (word) 0 - ( Neg[i] & 1 );
        for ( k = i + 1; k < nNeg; k++ )
        {
            pData1 = Rsub_Truth( p, Neg[k] );
            Mask1 = (word) 0 - ( Neg[k] & 1 );
            for ( w = 0; w < p->nWords; w++ )
                if ( ( ( pData[w] ^ Mask ) & ( pData1[w] ^ Mask1 ) ) != ( pRoot[w] ^ OutMask ) ) break;
            if ( w != p->nWords ) continue;
            a = Neg[i];
            b = Neg[k];
            *pA = 2 * Vec_IntEntry( p->vNodes, a >> 1 ) + ( a & 1 );
            *pB = 2 * Vec_IntEntry( p->vNodes, b >> 1 ) + ( b & 1 );
            p->nPair++;
            return OutPhase;
        }
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Releases a bounded cache of exact local search results.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Rsub_CacheClear( Rsub_Man_t * p )
{
    Rsub_Cache_t *pEntry, *pNext;
    int i;
    if ( !p->pCache ) return;
    for ( i = 0; i < p->nCacheBins; i++ )
    {
        for ( pEntry = p->pCache[i]; pEntry; pEntry = pNext )
        {
            pNext = pEntry->pNext;
            ABC_FREE( pEntry );
        }
        p->pCache[i] = NULL;
    }
    p->nCache = 0;
}

/**Function*************************************************************

  Synopsis    [Rejects impossible wide-window searches with 64 assignments.]

  Description [Every exact replacement must also match these fixed assignments.
  Positive and negative containment are considered independently because
  sampling can introduce false containments. A positive result still needs
  the full truth-table proof; a negative result safely avoids that work.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_LocalPossible( Rsub_Man_t * p, int Root, Rsub_Cut_t * Cut, int OnlyZero )
{
    static const word Vars[16] = {
        ABC_CONST( 0xaaaaaaaaaaaaaaaa ), ABC_CONST( 0xcccccccccccccccc ), ABC_CONST( 0xf0f0f0f0f0f0f0f0 ),
        ABC_CONST( 0xff00ff00ff00ff00 ), ABC_CONST( 0xffff0000ffff0000 ), ABC_CONST( 0xffffffff00000000 ),
        ABC_CONST( 0x839b2f7e6ca014d8 ), ABC_CONST( 0x7d542a98c1f09be6 ), ABC_CONST( 0xd31b05c7fa946e28 ),
        ABC_CONST( 0x68cfb3914ae572d0 ), ABC_CONST( 0xa74591ef028c6db2 ), ABC_CONST( 0x5e1cae6489d30fb6 ),
        ABC_CONST( 0x0a3fd964c712e58a ), ABC_CONST( 0xe438ba570c2d196e ), ABC_CONST( 0x425c9af68e713bd0 ),
        ABC_CONST( 0x918ef5c270bda436 ) };
    word Data[RSUB_DIV_MAX], Pos[RSUB_DIV_MAX], Neg[RSUB_DIV_MAX], R, D;
    int i, j, Id, a, b, nPos = 0, nNeg = 0, Slot, Req = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    if ( Cut->Saved < p->nMinSaved ) return 0;
    for ( i = 0; i < Cut->nLeaves; i++ )
        Data[i] = Vars[i];
    for ( i = Cut->nLeaves; i < Vec_IntSize( p->vNodes ); i++ )
    {
        Id = Vec_IntEntry( p->vNodes, i );
        a = p->M.pObjs[Id].Fan[0];
        b = p->M.pObjs[Id].Fan[1];
        Data[i] = ( Data[p->M.pObjs[a >> 1].Truth] ^ ( (word) 0 - ( a & 1 ) ) ) &
                  ( Data[p->M.pObjs[b >> 1].Truth] ^ ( (word) 0 - ( b & 1 ) ) );
    }
    R = Data[p->M.pObjs[Root].Truth];
    R ^= (word) 0 - ( R & 1 );
    if ( !R ) return 1;
    Vec_IntForEachEntry ( p->vDivs, Slot, i )
    {
        Id = Vec_IntEntry( p->vNodes, Slot );
        D = Data[Slot];
        D ^= (word) 0 - ( D & 1 );
        if ( D == R && p->M.pObjs[Id].Level <= Req ) return 1;
        if ( OnlyZero || !p->nSteps || Cut->Saved <= p->nMinSaved || p->M.pObjs[Id].Level >= Req ) continue;
        if ( !( D & ~R ) ) Pos[nPos++] = D;
        if ( !( R & ~D ) )
            Neg[nNeg++] = D;
        else if ( !( R & D ) )
            Neg[nNeg++] = ~D;
    }
    for ( i = 0; i < nPos; i++ )
        for ( j = i + 1; j < nPos; j++ )
            if ( ( Pos[i] | Pos[j] ) == R ) return 1;
    for ( i = 0; i < nNeg; i++ )
        for ( j = i + 1; j < nNeg; j++ )
            if ( ( Neg[i] & Neg[j] ) == R ) return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Reuses searches for windows with identical local programs.]

  Description [The key records every edge, divisor, and level eligibility.
  Actual object identifiers are absent. Hashes only select a bucket; the
  full key must match before a proof or failed search can be reused.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_SearchCached( Rsub_Man_t * p, int Root, Rsub_Cut_t * pCut, int * pA, int * pB, int fOnlyZero,
                              int * pnSimulated )
{
    unsigned Code[4 + 3 * RSUB_DIV_MAX], Hash = 0x1234567;
    int nCode = 4, i, Id, Slot, a, b, Phase;
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    Rsub_Cache_t * pEntry;
    abctime Clock;
    // A single-word truth is cheaper to evaluate than to encode and hash.
    // Wide windows retain the exact program cache; small designs allocate
    // its buckets only if they actually encounter one of these windows.
    if ( pCut->nLeaves <= 6 )
    {
        Clock = p->fVerbose ? Abc_Clock() : 0;
        p->nWords = 1;
        *pnSimulated = Vec_IntSize( p->vNodes );
        if ( p->fVerbose ) p->timeSim += Abc_Clock() - Clock;
        return Rsub_Search( p, Root, pCut, pA, pB, fOnlyZero );
    }
    if ( !p->pCache ) p->pCache = ABC_CALLOC( Rsub_Cache_t *, p->nCacheBins );
    Code[0] = pCut->nLeaves;
    Code[1] = Vec_IntSize( p->vNodes ) | ( p->M.pObjs[Root].Truth << 16 );
    Code[2] = Vec_IntSize( p->vDivs ) | ( fOnlyZero << 16 ) | ( ( p->nSteps && pCut->Saved > p->nMinSaved ) << 17 ) |
              ( ( pCut->Saved >= p->nMinSaved ) << 18 );
    Code[3] = 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
        if ( !pCut->Leaves[i] ) Code[3] |= 1u << i;
    for ( i = pCut->nLeaves; i < Vec_IntSize( p->vNodes ); i++ )
    {
        Id = Vec_IntEntry( p->vNodes, i );
        a = p->M.pObjs[Id].Fan[0];
        b = p->M.pObjs[Id].Fan[1];
        a = 2 * p->M.pObjs[a >> 1].Truth + ( a & 1 );
        b = 2 * p->M.pObjs[b >> 1].Truth + ( b & 1 );
        Code[nCode++] = a | ( b << 9 );
    }
    Vec_IntForEachEntry ( p->vDivs, Slot, i )
    {
        Id = Vec_IntEntry( p->vNodes, Slot );
        Code[nCode++] = 4 * Slot + ( p->M.pObjs[Id].Level <= Required ) + 2 * ( p->M.pObjs[Id].Level < Required );
    }
    for ( i = 0; i < nCode; i++ )
        Hash = ( Hash * 12582917u ) ^ Code[i];
    Hash ^= Hash >> 16;
    for ( pEntry = p->pCache[Hash & ( p->nCacheBins - 1 )]; pEntry; pEntry = pEntry->pNext )
        if ( pEntry->Hash == Hash && pEntry->nCode == nCode &&
             !memcmp( pEntry->Code, Code, sizeof( unsigned ) * nCode ) )
        {
            p->nCacheHits++;
            if ( pEntry->Phase < 0 ) return -1;
            a = pEntry->A;
            b = pEntry->B;
            *pA = a < 2 ? a : 2 * Vec_IntEntry( p->vNodes, ( a - 2 ) >> 1 ) + ( a & 1 );
            *pB = b < 2 ? b : 2 * Vec_IntEntry( p->vNodes, ( b - 2 ) >> 1 ) + ( b & 1 );
            if ( a != b )
                p->nPair++;
            else if ( a < 2 )
                p->nConst++;
            else
                p->nEqual++;
            return pEntry->Phase;
        }
    p->nCacheMisses++;
    Phase = -1;
    if ( Rsub_LocalPossible( p, Root, pCut, fOnlyZero ) )
    {
        Clock = p->fVerbose ? Abc_Clock() : 0;
        Rsub_Simulate( p, pCut, *pnSimulated );
        *pnSimulated = Vec_IntSize( p->vNodes );
        if ( p->fVerbose ) p->timeSim += Abc_Clock() - Clock;
        Phase = Rsub_Search( p, Root, pCut, pA, pB, fOnlyZero );
    }
    if ( p->nCache == RSUB_CACHE_LIMIT ) Rsub_CacheClear( p );
    pEntry = (Rsub_Cache_t *) ABC_ALLOC( char, sizeof( Rsub_Cache_t ) + sizeof( unsigned ) * ( nCode - 1 ) );
    pEntry->Hash = Hash;
    pEntry->nCode = nCode;
    pEntry->Phase = Phase;
    pEntry->A = pEntry->B = 0;
    if ( Phase >= 0 )
    {
        a = *pA;
        b = *pB;
        pEntry->A = a < 2 ? a : 2 + 2 * p->M.pObjs[a >> 1].Truth + ( a & 1 );
        pEntry->B = b < 2 ? b : 2 + 2 * p->M.pObjs[b >> 1].Truth + ( b & 1 );
    }
    memcpy( pEntry->Code, Code, sizeof( unsigned ) * nCode );
    pEntry->pNext = p->pCache[Hash & ( p->nCacheBins - 1 )];
    p->pCache[Hash & ( p->nCacheBins - 1 )] = pEntry;
    p->nCache++;
    return Phase;
}

/**Function*************************************************************

  Synopsis    [Recognizes profitable two- and three-gate resubstitutions.]

  Description [The guards establish removability before trying absorption, constants,
  associative sharing, and a complemented multiplexer implementation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_FastPlan( Rsub_Man_t * p, int Root, int * pA, int * pB )
{
    int x = p->M.pObjs[Root].Fan[0], y = p->M.pObjs[Root].Fan[1], a, b, c, d, Child, Outer, k, Pair, Last, Lit, Level;
    int Sel, Then, Else, P, Q;
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    int r0 = p->M.pObjs[x >> 1].Type == GIE_AND && p->M.pObjs[x >> 1].Refs == 1;
    int r1 = p->M.pObjs[y >> 1].Type == GIE_AND && p->M.pObjs[y >> 1].Refs == 1;
    if ( r0 != r1 )
    {
        Child = r0 ? x : y;
        Outer = r0 ? y : x;
        a = p->M.pObjs[Child >> 1].Fan[0];
        b = p->M.pObjs[Child >> 1].Fan[1];
        for ( k = 0; k < 2; k++ )
        {
            int Var = ( k ? b : a ) >> 1;
            if ( p->M.pObjs[Var].Type == GIE_AND && p->M.pObjs[Var].Refs <= 1 + ( Var == ( Outer >> 1 ) ) ) return -1;
        }
        if ( Child & 1 )
        {
            if ( Outer == ( a ^ 1 ) || Outer == ( b ^ 1 ) )
            {
                *pA = *pB = Outer;
                return 0;
            }
            if ( Outer != a && Outer != b ) return -1;
            *pA = Outer == a ? b ^ 1 : a ^ 1;
            *pB = Outer;
            return 0;
        }
        if ( Outer == a || Outer == b )
        {
            *pA = *pB = Child;
            return 0;
        }
        if ( Outer == ( a ^ 1 ) || Outer == ( b ^ 1 ) )
        {
            *pA = *pB = 0;
            return 0;
        }
        for ( k = 0; k < 2; k++ )
        {
            Pair = Gie_Lookup( &p->M, Outer, k ? b : a, Root );
            Last = k ? a : b;
            if ( Pair < 0 || ( Pair >> 1 ) == ( Child >> 1 ) ) continue;
            Lit = Gie_Lookup( &p->M, Pair, Last, Root );
            Level = Lit >= 0 ? p->M.pObjs[Lit >> 1].Level
                             : 1 + Abc_MaxInt( p->M.pObjs[Pair >> 1].Level, p->M.pObjs[Last >> 1].Level );
            if ( Level > Required ) continue;
            if ( Lit >= 0 )
                *pA = *pB = Lit;
            else
            {
                *pA = Pair;
                *pB = Last;
            }
            return 0;
        }
        return -1;
    }
    if ( !r0 || !( x & 1 ) || !( y & 1 ) ) return -1;
    a = p->M.pObjs[x >> 1].Fan[0];
    b = p->M.pObjs[x >> 1].Fan[1];
    c = p->M.pObjs[y >> 1].Fan[0];
    d = p->M.pObjs[y >> 1].Fan[1];
    if ( a == ( c ^ 1 ) )
        Sel = a, Then = b, Else = d;
    else if ( a == ( d ^ 1 ) )
        Sel = a, Then = b, Else = c;
    else if ( b == ( c ^ 1 ) )
        Sel = b, Then = a, Else = d;
    else if ( b == ( d ^ 1 ) )
        Sel = b, Then = a, Else = c;
    else
        return -1;
    if ( p->M.pObjs[Sel >> 1].Type == GIE_AND && p->M.pObjs[Sel >> 1].Refs <= 2 ) return -1;
    if ( p->M.pObjs[Then >> 1].Type == GIE_AND && p->M.pObjs[Then >> 1].Refs <= 1 + ( ( Then >> 1 ) == ( Else >> 1 ) ) )
        return -1;
    if ( p->M.pObjs[Else >> 1].Type == GIE_AND && p->M.pObjs[Else >> 1].Refs <= 1 + ( ( Then >> 1 ) == ( Else >> 1 ) ) )
        return -1;
    if ( Then == Else )
    {
        *pA = *pB = Then ^ 1;
        return 0;
    }
    P = Gie_Lookup( &p->M, Sel, Then ^ 1, Root );
    Q = Gie_Lookup( &p->M, Sel ^ 1, Else ^ 1, Root );
    if ( P < 0 || Q < 0 ) return -1;
    if ( 1 + Abc_MaxInt( p->M.pObjs[P >> 1].Level, p->M.pObjs[Q >> 1].Level ) > Required ) return -1;
    *pA = P ^ 1;
    *pB = Q ^ 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Matches the complete root pattern of a previously proved recipe.]

  Description [Shared abstract variables must bind consistently. Try both fanin
  orders, undoing every new binding before a retry. A work budget bounds
  ambiguous matches; failure leaves the ordinary search policy unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_EarlyMatch_rec( Rsub_Man_t * p, Rsub_Early_t * r, Rsub_Match_t * Task, int * Map, int * Undo,
                                int * nUndo, int * Budget )
{
    Rsub_Match_t Children[2];
    int Slot, Id, a, b, x, y, Saved, Try;
    for ( ; Task; Task = Task->Next )
    {
        Slot = Task->Slot;
        Id = Task->Id;
        if ( Map[Slot] >= 0 )
        {
            if ( Map[Slot] != 2 * Id ) return 0;
            continue;
        }
        if ( --*Budget < 0 ) return 0;
        Map[Slot] = 2 * Id;
        Undo[( *nUndo )++] = Slot;
        if ( Slot < r->nLeaves )
        {
            if ( ( r->ZeroMask & ( 1u << Slot ) ) && Id ) return 0;
            continue;
        }
        if ( p->M.pObjs[Id].Type != GIE_AND ) return 0;
        a = r->Ops[2 * Slot];
        b = r->Ops[2 * Slot + 1];
        x = p->M.pObjs[Id].Fan[0];
        y = p->M.pObjs[Id].Fan[1];
        Saved = *nUndo;
        Children[0].Slot = a >> 1;
        Children[1].Slot = b >> 1;
        Children[0].Next = Children + 1;
        // Match the remaining siblings before committing this orientation.
        // A later shared-variable conflict must retry earlier choices too.
        Children[1].Next = Task->Next;
        for ( Try = 0; Try < 2; Try++ )
        {
            Children[0].Id = x >> 1;
            Children[1].Id = y >> 1;
            if ( ( a & 1 ) == ( x & 1 ) && ( b & 1 ) == ( y & 1 ) &&
                 Rsub_EarlyMatch_rec( p, r, Children, Map, Undo, nUndo, Budget ) )
                return 1;
            while ( *nUndo > Saved )
                Map[Undo[--*nUndo]] = -1;
            ABC_SWAP( int, x, y );
        }
        return 0;
    }
    return 1;
}

static int Rsub_EarlyMatch( Rsub_Man_t * p, Rsub_Early_t * r, int Slot, int Id, int * Map, int * Undo, int * nUndo,
                            int * Budget )
{
    Rsub_Match_t Task;
    Task.Slot = Slot;
    Task.Id = Id;
    Task.Next = NULL;
    return Rsub_EarlyMatch_rec( p, r, &Task, Map, Undo, nUndo, Budget );
}

/**Function*************************************************************

  Synopsis    [Locates a recipe divisor without constructing its whole window.]

  Description [The ready-node hash is tried first. A bounded fanout scan also finds
  unvisited divisors with an unfinished fanin; these are not yet hashed.
  Busy roots are excluded to avoid dependency cycles.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_EarlyLookup( Rsub_Man_t * p, int a, int b )
{
    int Lit = Gie_Lookup( &p->M, a, b, p->M.iRoot ), x = a >> 1, y = b >> 1, Edge, Id;
    if ( Lit >= 0 ) return Lit;
    if ( p->M.pObjs[x].Handled && p->M.pObjs[y].Handled ) return -1;
    if ( p->M.pObjs[x].Refs > p->M.pObjs[y].Refs ) ABC_SWAP( int, x, y );
    if ( p->M.pObjs[x].Refs > 100 ) return -1;
    for ( Edge = p->M.pFans[x].Head; Edge; Edge = p->M.pFans[Edge >> 1].Next[Edge & 1] )
    {
        Id = Edge >> 1;
        if ( p->M.pObjs[Id].Type != GIE_AND || p->M.pObjs[Id].Busy ) continue;
        if ( ( p->M.pObjs[Id].Fan[0] == a && p->M.pObjs[Id].Fan[1] == b ) ||
             ( p->M.pObjs[Id].Fan[0] == b && p->M.pObjs[Id].Fan[1] == a ) )
        {
            p->M.pObjs[Id].Level = 1 + Abc_MaxInt( p->M.pObjs[a >> 1].Level, p->M.pObjs[b >> 1].Level );
            return 2 * Id;
        }
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Replays a proved recipe after exact structural matching.]

  Description [The neighborhood hash only selects candidates. Each root and divisor
  program is checked against the current graph, followed by current level
  and MFFC tests. Reusing a proof does not reuse stale cost information.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Rsub_EarlyTry( Rsub_Man_t * p, Rsub_Neighbor_t * q, int Root, int * A, int * B )
{
    int Map[RSUB_DIV_MAX], Undo[RSUB_DIV_MAX], nUndo, Budget;
    int i, a, b, Lit, Cost, Req = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    Rsub_Cut_t Cut;
    Rsub_Early_t * r;
    for ( r = q->Recipes; r; r = r->Next )
    {
        memset( Map, 0xFF, sizeof( int ) * r->nNodes );
        nUndo = 0;
        Budget = RSUB_RECIPE_MATCH_MAX;
        if ( !Rsub_EarlyMatch( p, r, r->Root, Root, Map, Undo, &nUndo, &Budget ) ) continue;
        for ( i = r->Root + 1; i < r->nNodes; i++ )
            if ( r->Used[i] )
            {
                a = r->Ops[2 * i];
                b = r->Ops[2 * i + 1];
                assert( Map[a >> 1] >= 0 && Map[b >> 1] >= 0 );
                Lit = Rsub_EarlyLookup( p, Map[a >> 1] ^ ( a & 1 ), Map[b >> 1] ^ ( b & 1 ) );
                if ( Lit < 0 ) break;
                Map[i] = Lit;
            }
        if ( i < r->nNodes ) continue;
        a = r->A < 0 ? -r->A - 1 : Map[r->A >> 1] ^ ( r->A & 1 );
        b = r->B < 0 ? -r->B - 1 : Map[r->B >> 1] ^ ( r->B & 1 );
        Lit = Gie_Lookup( &p->M, a, b, Root );
        Cost = Lit < 0;
        if ( Cost && !p->nSteps ) continue;
        if ( Cost )
        {
            if ( 1 + Abc_MaxInt( p->M.pObjs[a >> 1].Level, p->M.pObjs[b >> 1].Level ) > Req ) continue;
            Cut.nLeaves = 2;
            Cut.Leaves[0] = a >> 1;
            Cut.Leaves[1] = b >> 1;
        }
        else
        {
            if ( p->M.pObjs[Lit >> 1].Level > Req ) continue;
            Cut.nLeaves = 1;
            Cut.Leaves[0] = Lit >> 1;
        }
        if ( Rsub_Mffc( p, Root, &Cut, 0 ) < Cost + p->nMinSaved ) continue;
        if ( Cost )
        {
            *A = a;
            *B = b;
        }
        else
            *A = *B = Lit;
        p->nEarlyHits++;
        return r->Phase;
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Records a successful local proof in abstract cut coordinates.]

  Description [Only the divisor program used by the replacement is replayed.
  Constants retain their bindings, and both per-key and total recipe counts
  are bounded. The root program itself is matched in full.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Rsub_EarlySave( Rsub_Man_t * p, Rsub_Neighbor_t * q, Rsub_Cut_t * Cut, int Root, int A, int B, int Phase )
{
    Rsub_Early_t r, *x;
    int i, a, b, Id;
    if ( q->nRecipes == RSUB_RECIPE_PER_KEY || p->nEarlyItems == RSUB_RECIPE_LIMIT ) return;
    memset( &r, 0, sizeof( r ) );
    r.nLeaves = Cut->nLeaves;
    r.nNodes = Vec_IntSize( p->vNodes );
    r.Root = p->M.pObjs[Root].Truth;
    if ( r.Root - r.nLeaves > RSUB_RECIPE_ROOT_MAX ) return;
    r.A = A < 2 ? -A - 1 : 2 * p->M.pObjs[A >> 1].Truth + ( A & 1 );
    r.B = B < 2 ? -B - 1 : 2 * p->M.pObjs[B >> 1].Truth + ( B & 1 );
    r.Phase = Phase;
    if ( r.A >= 0 ) r.Used[r.A >> 1] = 1;
    if ( r.B >= 0 ) r.Used[r.B >> 1] = 1;
    for ( i = 0; i < Cut->nLeaves; i++ )
        if ( !Cut->Leaves[i] ) r.ZeroMask |= 1u << i;
    for ( i = r.nNodes - 1; i >= r.nLeaves; i-- )
    {
        Id = Vec_IntEntry( p->vNodes, i );
        a = p->M.pObjs[Id].Fan[0];
        b = p->M.pObjs[Id].Fan[1];
        r.Ops[2 * i] = (unsigned short) ( 2 * p->M.pObjs[a >> 1].Truth + ( a & 1 ) );
        r.Ops[2 * i + 1] = (unsigned short) ( 2 * p->M.pObjs[b >> 1].Truth + ( b & 1 ) );
        if ( r.Used[i] ) r.Used[r.Ops[2 * i] >> 1] = r.Used[r.Ops[2 * i + 1] >> 1] = 1;
    }
    for ( x = q->Recipes; x; x = x->Next )
        if ( x->nNodes == r.nNodes && x->nLeaves == r.nLeaves && x->Root == r.Root && x->A == r.A && x->B == r.B &&
             x->Phase == r.Phase && x->ZeroMask == r.ZeroMask &&
             !memcmp( x->Ops, r.Ops, sizeof( unsigned short ) * 2 * r.nNodes ) )
            return;
    x = ABC_ALLOC( Rsub_Early_t, 1 );
    *x = r;
    x->Next = q->Recipes;
    q->Recipes = x;
    q->nRecipes++;
    p->nEarlyItems++;
}

/**Function*************************************************************

  Synopsis    [Marks nodes whose function may equal another existing node.]

  Description [A deterministic simulation is only a rejection filter.
  New one-gate replacements have the function of an original root, so
  they cannot introduce an equality absent from the original signatures.
  Hash collisions retain work and never justify a replacement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Rsub_GlobalFilter( Rsub_Man_t * p )
{
    word * pSims = ABC_CALLOC( word, p->M.nObjs );
    unsigned Rand = 0x31415927, Key;
    word Sig;
    int i, k, a, b;
    for ( i = 1; i < p->M.nObjs; i++ )
    {
        Gie_Obj_t * pObj = p->M.pObjs + i;
        if ( pObj->Type == GIE_CI )
        {
            Rand ^= Rand << 13;
            Rand ^= Rand >> 17;
            Rand ^= Rand << 5;
            Sig = (word) Rand << 32;
            Rand ^= Rand << 13;
            Rand ^= Rand >> 17;
            Rand ^= Rand << 5;
            pSims[i] = Sig | Rand;
        }
        else if ( pObj->Type == GIE_AND )
        {
            a = pObj->Fan[0];
            b = pObj->Fan[1];
            pSims[i] = ( pSims[a >> 1] ^ ( (word) 0 - ( a & 1 ) ) ) & ( pSims[b >> 1] ^ ( (word) 0 - ( b & 1 ) ) );
        }
        else
            continue;
        Sig = pSims[i] ^ ( (word) 0 - ( pSims[i] & 1 ) );
        if ( !Sig )
        {
            pObj->CanEqual = 1;
            continue;
        }
        Key = (unsigned) ( ( Sig * ABC_CONST( 0x9e3779b97f4a7c15 ) ) >> 32 ) & p->M.nHashMask;
        for ( k = p->M.pHash[Key]; k; k = p->M.pObjs[k].Hash )
            if ( Sig == ( pSims[k] ^ ( (word) 0 - ( pSims[k] & 1 ) ) ) ) break;
        if ( k )
            pObj->CanEqual = p->M.pObjs[k].CanEqual = 1;
        else
        {
            pObj->Hash = p->M.pHash[Key];
            p->M.pHash[Key] = i;
        }
    }
    ABC_FREE( pSims );
    memset( p->M.pHash, 0, sizeof( int ) * ( p->M.nHashMask + 1 ) );
    for ( i = 1; i < p->M.nObjs; i++ )
    {
        p->M.pObjs[i].Hash = 0;
        Gie_Ready( &p->M, i );
    }
}

/**Function*************************************************************

  Synopsis    [Initializes the resubstitution pass and its shared mutable graph.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Rsub_Man_t * Rsub_ManStart( Gia_Man_t * pGia, int fKeepLevel, Vec_Int_t * vCiLevels )
{
    Rsub_Man_t * p = ABC_CALLOC( Rsub_Man_t, 1 );
    Gie_ManStart( &p->M, pGia, fKeepLevel, GIE_HASH_DEFER, vCiLevels );
    p->vNodes = Vec_IntAlloc( RSUB_DIV_MAX );
    p->vDivs = Vec_IntAlloc( RSUB_DIV_MAX );
    p->vTodo = Vec_IntAlloc( 256 );
    Rsub_GlobalFilter( p );
    return p;
}

/**Function*************************************************************

  Synopsis    [Performs one resubstitution pass and returns a new GIA.]

  Description [The default search allows one new AND per replacement.
  A reused unvisited divisor is optimized before the pending root retries.
  Busy roots cannot be divisors, so dependencies never form a cycle.
  Only finished nodes feed accepted replacements; their levels are exact.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Rsub_ManPerform( Gia_Man_t * pGia, int nCutMax, int nSteps, int nMinSaved, int fKeepLevel, int fVerbose )
{
    Rsub_Man_t * p;
    Gia_Man_t * pNew;
    Vec_Int_t * vCiLevels;
    Rsub_Cut_t Cut;
    Rsub_Neighbor_t * Neighbor;
    int Id, Next, Lit, Phase, a, b, OldAnds, nStart;
    abctime Start = Abc_Clock(), Setup, Export, Clock = 0;
    if ( pGia == NULL || Gia_ManHasChoices( pGia ) || pGia->pMuxes || Gia_ManXorNum( pGia ) || Gia_ManBufNum( pGia ) )
        return NULL;
    if ( nCutMax < 4 || nCutMax > RSUB_LEAF_MAX || nSteps < 0 || nSteps > 1 || nMinSaved < 1 ) return NULL;
    if ( Gia_ManIsSeqWithBoxes( pGia ) && !Gia_ManIsNormalized( pGia ) ) return NULL;
    if ( Gia_ManObjNum( pGia ) > Gie_ObjectLimit() / 2 ) return NULL;
    vCiLevels = Gia_ManBoxNum( pGia ) ? Gie_BoxCiLevels( pGia ) : NULL;
    p = Rsub_ManStart( pGia, fKeepLevel, vCiLevels );
    Vec_IntFreeP( &vCiLevels );
    p->nCutMax = nCutMax;
    p->nSteps = nSteps;
    p->nMinSaved = nMinSaved;
    p->fVerbose = fVerbose;
    p->nCacheBins = 16;
    while ( p->nCacheBins < Gia_ManAndNum( pGia ) && p->nCacheBins < RSUB_CACHE_BINS )
        p->nCacheBins *= 2;
    p->pSims = ABC_ALLOC( word, RSUB_DIV_MAX * ( nCutMax <= 6 ? 1 : 1 << ( nCutMax - 6 ) ) );
    p->pNeighborhood = Gie_Neighborhoods( &p->M, p->M.nOrig, RSUB_NEIGHBOR_ROUNDS );
    p->nNeighborBins = 16;
    while ( p->nNeighborBins < p->M.nOrig && p->nNeighborBins < RSUB_NEIGHBOR_BINS )
        p->nNeighborBins *= 2;
    p->pNeighbors = ABC_CALLOC( Rsub_Neighbor_t, p->nNeighborBins );
    Setup = Abc_Clock() - Start;
    for ( Next = 1; Next < p->M.nOrig; Next++ )
    {
        if ( p->M.pObjs[Next].Type != GIE_AND || p->M.pObjs[Next].Handled ) continue;
        Vec_IntPush( p->vTodo, Next );
        while ( Vec_IntSize( p->vTodo ) )
        {
            Id = Vec_IntEntryLast( p->vTodo );
            if ( p->M.pObjs[Id].Handled ) goto finish;
            p->M.pObjs[Id].Busy = 1;
            a = p->M.pObjs[Id].Fan[0] >> 1;
            b = p->M.pObjs[Id].Fan[1] >> 1;
            assert( !p->M.pObjs[a].Busy && !p->M.pObjs[b].Busy );
            if ( !p->M.pObjs[a].Handled )
            {
                Vec_IntPush( p->vTodo, a );
                continue;
            }
            if ( !p->M.pObjs[b].Handled )
            {
                Vec_IntPush( p->vTodo, b );
                continue;
            }
            assert( p->M.pObjs[a].Handled && p->M.pObjs[b].Handled );
            Gie_Ready( &p->M, Id );
            Lit = Gie_Simplify( p->M.pObjs[Id].Fan[0], p->M.pObjs[Id].Fan[1] );
            if ( Lit < 0 && p->M.pObjs[Id].Duplicate )
                Lit = Gie_Lookup( &p->M, p->M.pObjs[Id].Fan[0], p->M.pObjs[Id].Fan[1], Id );
            if ( Lit >= 0 )
            {
                if ( !p->M.pObjs[Lit >> 1].Handled )
                {
                    Vec_IntPush( p->vTodo, Lit >> 1 );
                    continue;
                }
                Gie_Finish( &p->M, Lit >> 1 );
                Gie_Replace( &p->M, Id, Lit );
                p->nMerged++;
                continue;
            }
            if ( p->M.pObjs[Id].Refs > 1000 ) goto finish;
            if ( !p->M.pObjs[Id].CanEqual &&
                 ( nSteps == 0 || ( ( p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].Type != GIE_AND ||
                                      p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].Refs > 1 ) &&
                                    ( p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].Type != GIE_AND ||
                                      p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].Refs > 1 ) ) ) )
            {
                p->nSkipped++;
                goto finish;
            }
            p->M.iRoot = Id;
            if ( fVerbose ) Clock = Abc_Clock();
            if ( nSteps && nMinSaved == 1 )
            {
                Phase = Rsub_FastPlan( p, Id, &a, &b );
                if ( Phase >= 0 ) goto early_build;
            }
            Neighbor = Rsub_NeighborFind( p, Id );
            Phase = Rsub_EarlyTry( p, Neighbor, Id, &a, &b );
            if ( Phase >= 0 ) goto early_build;
            // A bounded effort heuristic for recurring neighborhoods. A hash
            // match is not proof that no improvement exists. Successful
            // recipes still require an exact match and a fresh gain check.
            if ( !Neighbor->Good && Neighbor->Count >= RSUB_NEIGHBOR_TRIES )
            {
                p->nNeighborSkips++;
                goto finish;
            }
            Neighbor->Count++;
            p->M.iRoot = Id;
            if ( fVerbose ) Clock = Abc_Clock();
            Rsub_Cut( p, Id, &Cut );
            Cut.Saved = Rsub_Mffc( p, Id, &Cut, 1 );
            if ( fVerbose )
            {
                p->timeCuts += Abc_Clock() - Clock;
                Clock = Abc_Clock();
            }
            if ( !p->M.pObjs[Id].CanEqual && Cut.Saved <= nMinSaved )
            {
                p->nSkipped++;
                goto finish;
            }
            if ( !Rsub_Collect( p, Id, &Cut ) ) goto finish;
            if ( fVerbose )
            {
                p->timeDivs += Abc_Clock() - Clock;
                Clock = Abc_Clock();
            }
            nStart = 0;
            Phase = Rsub_SearchCached( p, Id, &Cut, &a, &b, 1, &nStart );
            if ( fVerbose )
            {
                p->timeSearch += Abc_Clock() - Clock;
                Clock = Abc_Clock();
            }
            if ( Phase >= 0 ) goto build;
            Rsub_Expand( p, Id, &Cut );
            if ( fVerbose )
            {
                p->timeDivs += Abc_Clock() - Clock;
                Clock = Abc_Clock();
            }
            Phase = Rsub_SearchCached( p, Id, &Cut, &a, &b, 0, &nStart );
            if ( fVerbose )
            {
                p->timeSearch += Abc_Clock() - Clock;
                Clock = Abc_Clock();
            }
            if ( Phase < 0 ) goto finish;
        build:
            Neighbor->Good = 1;
            Rsub_EarlySave( p, Neighbor, &Cut, Id, a, b, Phase );
        early_build:
            if ( !p->M.pObjs[a >> 1].Handled )
            {
                Vec_IntPush( p->vTodo, a >> 1 );
                continue;
            }
            if ( !p->M.pObjs[b >> 1].Handled )
            {
                Vec_IntPush( p->vTodo, b >> 1 );
                continue;
            }
            OldAnds = p->M.nAnds;
            Lit = Gie_And( &p->M, a, b );
            if ( Lit < 0 ) goto finish;
            Gie_Replace( &p->M, Id, Lit ^ Phase );
            assert( p->M.nAnds < OldAnds );
            p->nRewritten++;
            if ( fVerbose ) p->timeUpdate += Abc_Clock() - Clock;
        finish:
            Gie_Finish( &p->M, Id );
            p->M.pObjs[Id].Busy = 0;
            Vec_IntPop( p->vTodo );
        }
    }
    Export = Abc_Clock();
    pNew = Gie_ManExport( &p->M, pGia );
    Export = Abc_Clock() - Export;
    if ( fVerbose )
    {
        Abc_Print( 1, "&resub2: ANDs %d -> %d. Rewrites %d. Merges %d. Candidates: constant %d, wire %d, pair %d.\n",
                   Gia_ManAndNum( pGia ), Gia_ManAndNum( pNew ), p->nRewritten, p->nMerged, p->nConst, p->nEqual,
                   p->nPair );
        Abc_Print( 1, "&resub2: early hits %d skips %d\n", p->nEarlyHits, p->nNeighborSkips );
        Abc_Print( 1, "&resub2: cache hits %.0f  misses %.0f.\n", p->nCacheHits, p->nCacheMisses );
        Abc_Print( 1, "&resub2: cuts %.0f  divisors %.0f  limited %d  filtered %d.\n", p->nCuts, p->nDivs, p->nLimited,
                   p->nSkipped );
        Abc_Print( 1,
                   "&resub2: import %.6f  cut/MFFC %.6f  divisors %.6f  truth %.6f  search %.6f  update %.6f  export "
                   "%.6f  total %.6f sec\n",
                   (double) Setup / CLOCKS_PER_SEC, (double) p->timeCuts / CLOCKS_PER_SEC,
                   (double) p->timeDivs / CLOCKS_PER_SEC, (double) p->timeSim / CLOCKS_PER_SEC,
                   (double) ( p->timeSearch - p->timeSim ) / CLOCKS_PER_SEC, (double) p->timeUpdate / CLOCKS_PER_SEC,
                   (double) Export / CLOCKS_PER_SEC, (double) ( Abc_Clock() - Start ) / CLOCKS_PER_SEC );
    }
    for ( Id = 0; Id < p->nNeighborBins; Id++ )
    {
        Rsub_Early_t *pRecipe, *pNext;
        for ( pRecipe = p->pNeighbors[Id].Recipes; pRecipe; pRecipe = pNext )
        {
            pNext = pRecipe->Next;
            ABC_FREE( pRecipe );
        }
    }
    ABC_FREE( p->pNeighborhood );
    ABC_FREE( p->pNeighbors );
    Rsub_CacheClear( p );
    ABC_FREE( p->pCache );
    ABC_FREE( p->pSims );
    Vec_IntFree( p->vNodes );
    Vec_IntFree( p->vDivs );
    Vec_IntFree( p->vTodo );
    Gie_ManStop( &p->M );
    ABC_FREE( p );
    return pNew;
}

ABC_NAMESPACE_IMPL_END
