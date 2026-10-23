/**CFile****************************************************************

  FileName    [giaDrf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cached DAG-aware AIG refactoring.]

  Synopsis    [Cached refactoring over the shared mutable AIG.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDrf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "giaDrf.h"
#include "opt/drw/drwInt.h"

ABC_NAMESPACE_IMPL_START

static inline int Drf_Mffc( Drf_Man_t * p, int Root, Drf_Cut_t * pCut, int fMark )
{
    return Gie_Mffc( &p->M, Root, pCut->Leaves, pCut->nLeaves, fMark );
}

static Drf_Entry_t * Drf_Factor( Drf_Man_t * p, Drf_Cut_t * pCut );

/**Function*************************************************************

  Synopsis    [Collects a depth-bounded MFFC and its ordered boundary.]

  Description [Reference changes are recorded once and restored by replay.
  The boundary walk follows the original left-to-right fanin order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drf_Boundary( Drf_Man_t * p, int Root, Drf_Cut_t * pCut )
{
    int Id, Var, i, k, MinLevel = Abc_MaxInt( 0, p->M.pObjs[Root].Level - 10 );
    p->nCuts++;
    pCut->fAssoc = 0;
    Vec_IntClear( p->vNodes );
    Vec_IntClear( p->M.vStack );
    Vec_IntPush( p->M.vStack, Root );
    Gie_MarkNext( &p->M );
    while ( Vec_IntSize( p->M.vStack ) )
    {
        Id = Vec_IntPop( p->M.vStack );
        Vec_IntPush( p->vNodes, Id );
        p->M.pObjs[Id].Mark = p->M.Mark;
        for ( k = 0; k < 2; k++ )
        {
            Var = p->M.pObjs[Id].Fan[k] >> 1;
            if ( p->M.pObjs[Var].Type != GIE_AND ) continue;
            assert( p->M.pObjs[Var].Refs > 0 );
            if ( --p->M.pObjs[Var].Refs == 0 && p->M.pObjs[Var].Level > MinLevel )
            {
                if ( !( p->M.pObjs[Id].Fan[k] & 1 ) ) pCut->fAssoc = 1;
                Vec_IntPush( p->M.vStack, Var );
            }
        }
    }
    pCut->Saved = Vec_IntSize( p->vNodes );
    pCut->nLeaves = 0;
    if ( pCut->Saved > 1 )
    {
        Gie_TruthNext( &p->M );
        Vec_IntPush( p->M.vStack, Root );
        while ( Vec_IntSize( p->M.vStack ) )
        {
            Id = Vec_IntPop( p->M.vStack );
            if ( !Id ) continue;
            if ( p->M.pObjs[Id].TruthMark == p->M.TruthMark ) continue;
            p->M.pObjs[Id].TruthMark = p->M.TruthMark;
            if ( Id != Root &&
                 ( p->M.pObjs[Id].Type != GIE_AND || p->M.pObjs[Id].Refs || p->M.pObjs[Id].Level <= MinLevel ) )
            {
                if ( pCut->nLeaves == DRF_LEAF_MAX )
                {
                    pCut->nLeaves++;
                    break;
                }
                pCut->Leaves[pCut->nLeaves++] = Id;
                continue;
            }
            Vec_IntPush( p->M.vStack, p->M.pObjs[Id].Fan[1] >> 1 );
            Vec_IntPush( p->M.vStack, p->M.pObjs[Id].Fan[0] >> 1 );
        }
    }
    Vec_IntForEachEntry ( p->vNodes, Id, i )
        for ( k = 0; k < 2; k++ )
        {
            Var = p->M.pObjs[Id].Fan[k] >> 1;
            if ( p->M.pObjs[Var].Type == GIE_AND ) p->M.pObjs[Var].Refs++;
        }
    Vec_IntClear( p->M.vStack );
    return pCut->Saved > 1;
}

/**Function*************************************************************

  Synopsis    [Finds a reconvergence-driven cut when the MFFC is too wide.]

  Description [An expansion prefers the fewest new boundary nodes, then
  the largest level. Shared predecessors already in the cone are free.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drf_ReconvCut( Drf_Man_t * p, int Root, Drf_Cut_t * pCut )
{
    int i, k, Id, Var, Cost, Best, BestCost;
    Gie_TruthNext( &p->M );
    p->M.pObjs[0].TruthMark = p->M.TruthMark;
    p->M.pObjs[Root].TruthMark = p->M.TruthMark;
    pCut->nLeaves = 0;
    for ( k = 0; k < 2; k++ )
    {
        Var = p->M.pObjs[Root].Fan[k] >> 1;
        if ( p->M.pObjs[Var].TruthMark == p->M.TruthMark ) continue;
        pCut->Leaves[pCut->nLeaves++] = Var;
        p->M.pObjs[Var].TruthMark = p->M.TruthMark;
    }
    for ( ;; )
    {
        Best = -1;
        BestCost = 100;
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            Id = pCut->Leaves[i];
            if ( p->M.pObjs[Id].Type != GIE_AND ) continue;
            Cost = ( p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].TruthMark != p->M.TruthMark ) +
                   ( p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].TruthMark != p->M.TruthMark );
            if ( Cost == 2 && p->M.pObjs[Id].Refs > 50 ) continue;
            if ( Cost < BestCost ||
                 ( Cost == BestCost && p->M.pObjs[Id].Level > p->M.pObjs[pCut->Leaves[Best]].Level ) )
                Best = i, BestCost = Cost;
            if ( BestCost == 0 ) break;
        }
        if ( Best < 0 || pCut->nLeaves - 1 + BestCost > DRF_LEAF_MAX ) break;
        Id = pCut->Leaves[Best];
        for ( i = Best + 1; i < pCut->nLeaves; i++ )
            pCut->Leaves[i - 1] = pCut->Leaves[i];
        pCut->nLeaves--;
        for ( k = 0; k < 2; k++ )
        {
            Var = p->M.pObjs[Id].Fan[k] >> 1;
            if ( p->M.pObjs[Var].TruthMark == p->M.TruthMark ) continue;
            pCut->Leaves[pCut->nLeaves++] = Var;
            p->M.pObjs[Var].TruthMark = p->M.TruthMark;
        }
    }
    pCut->Saved = Drf_Mffc( p, Root, pCut, 1 );
}

/**Function*************************************************************

  Synopsis    [Computes a cut truth table in reusable, stamped storage.]

  Description [Indices survive vector growth. The explicit DFS stack
  avoids recursion on deep reconvergent cones. Words use Kit's layout.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned * Drf_Truth( Drf_Man_t * p, int Root, Drf_Cut_t * pCut )
{
    static const unsigned Elem[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    int Words = Kit_TruthWordNum( pCut->nLeaves ), i, w, Id, a, b, Index;
    unsigned *pTruth, *p0, *p1, Phase0, Phase1;
    Gie_TruthNext( &p->M );
    Vec_IntFill( p->vTruth, ( pCut->nLeaves + 1 ) * Words, 0 );
    p->M.pObjs[0].TruthMark = p->M.TruthMark;
    p->M.pObjs[0].Truth = 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        Id = pCut->Leaves[i];
        p->M.pObjs[Id].TruthMark = p->M.TruthMark;
        p->M.pObjs[Id].Truth = (unsigned short) ( i + 1 );
        pTruth = (unsigned *) Vec_IntArray( p->vTruth ) + ( i + 1 ) * Words;
        for ( w = 0; w < Words; w++ )
            pTruth[w] = i < 5 ? Elem[i] : ( w >> ( i - 5 ) ) & 1 ? ~0u : 0;
    }
    if ( pCut->fFull )
    {
        // Dereferencing visits each gate after all its MFFC fanouts. The
        // reverse list is already a truth-evaluation program for this cut.
        int Count = Vec_IntSize( p->vNodes );
        if ( Count + pCut->nLeaves + 1 >= 65535 )
        {
            p->nLimited++;
            return NULL;
        }
        Vec_IntFillExtra( p->vTruth, ( Count + pCut->nLeaves + 1 ) * Words, 0 );
        for ( i = Count - 1, Index = pCut->nLeaves + 1; i >= 0; i--, Index++ )
        {
            Id = Vec_IntEntry( p->vNodes, i );
            a = p->M.pObjs[Id].Fan[0];
            b = p->M.pObjs[Id].Fan[1];
            assert( p->M.pObjs[a >> 1].TruthMark == p->M.TruthMark && p->M.pObjs[b >> 1].TruthMark == p->M.TruthMark );
            pTruth = (unsigned *) Vec_IntArray( p->vTruth ) + Index * Words;
            p0 = (unsigned *) Vec_IntArray( p->vTruth ) + p->M.pObjs[a >> 1].Truth * Words;
            p1 = (unsigned *) Vec_IntArray( p->vTruth ) + p->M.pObjs[b >> 1].Truth * Words;
            Phase0 = ( a & 1 ) ? ~0u : 0;
            Phase1 = ( b & 1 ) ? ~0u : 0;
            for ( w = 0; w < Words; w++ )
                pTruth[w] = ( p0[w] ^ Phase0 ) & ( p1[w] ^ Phase1 );
            p->M.pObjs[Id].Truth = (unsigned short) Index;
            p->M.pObjs[Id].TruthMark = p->M.TruthMark;
        }
        return (unsigned *) Vec_IntArray( p->vTruth ) + p->M.pObjs[Root].Truth * Words;
    }
    Vec_IntClear( p->M.vStack );
    Vec_IntPush( p->M.vStack, Root );
    while ( Vec_IntSize( p->M.vStack ) )
    {
        Id = Vec_IntEntryLast( p->M.vStack );
        if ( p->M.pObjs[Id].TruthMark == p->M.TruthMark )
        {
            Vec_IntPop( p->M.vStack );
            continue;
        }
        assert( p->M.pObjs[Id].Type == GIE_AND );
        a = p->M.pObjs[Id].Fan[0];
        b = p->M.pObjs[Id].Fan[1];
        if ( p->M.pObjs[a >> 1].TruthMark != p->M.TruthMark )
        {
            Vec_IntPush( p->M.vStack, a >> 1 );
            continue;
        }
        if ( p->M.pObjs[b >> 1].TruthMark != p->M.TruthMark )
        {
            Vec_IntPush( p->M.vStack, b >> 1 );
            continue;
        }
        Index = Vec_IntSize( p->vTruth ) / Words;
        if ( Index >= 65535 )
        {
            Vec_IntClear( p->M.vStack );
            p->nLimited++;
            return NULL;
        }
        Vec_IntFillExtra( p->vTruth, ( Index + 1 ) * Words, 0 );
        pTruth = (unsigned *) Vec_IntArray( p->vTruth ) + Index * Words;
        p0 = (unsigned *) Vec_IntArray( p->vTruth ) + p->M.pObjs[a >> 1].Truth * Words;
        p1 = (unsigned *) Vec_IntArray( p->vTruth ) + p->M.pObjs[b >> 1].Truth * Words;
        Phase0 = ( a & 1 ) ? ~0u : 0;
        Phase1 = ( b & 1 ) ? ~0u : 0;
        for ( w = 0; w < Words; w++ )
            pTruth[w] = ( p0[w] ^ Phase0 ) & ( p1[w] ^ Phase1 );
        p->M.pObjs[Id].Truth = (unsigned short) Index;
        p->M.pObjs[Id].TruthMark = p->M.TruthMark;
        Vec_IntPop( p->M.vStack );
    }
    return (unsigned *) Vec_IntArray( p->vTruth ) + p->M.pObjs[Root].Truth * Words;
}

/**Function*************************************************************

  Synopsis    [Clears both caches between node evaluations.]

  Description [Shape entries reference factor entries, so their lifetimes
  must end together. No selected cut may be live across this call.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drf_CacheClear( Drf_Man_t * p )
{
    int i, j;
    if ( p->pShapes )
        for ( i = 0; i < DRF_CACHE_BINS; i++ )
        {
            Drf_Shape_t *pShape = p->pShapes[i], *pNext;
            while ( pShape )
            {
                pNext = pShape->pNext;
                ABC_FREE( pShape );
                pShape = pNext;
            }
            p->pShapes[i] = NULL;
        }
    for ( i = 0; i < DRF_CACHE_BINS; i++ )
    {
        Drf_Entry_t *pEntry = p->pCache[i], *pNext;
        while ( pEntry )
        {
            pNext = pEntry->pNext;
            for ( j = 0; j < pEntry->nGraphs; j++ )
                Kit_GraphFree( pEntry->pGraphs[j] );
            ABC_FREE( pEntry->pTruth );
            ABC_FREE( pEntry->pPairs );
            ABC_FREE( pEntry );
            pEntry = pNext;
        }
        p->pCache[i] = NULL;
    }
    p->nCache = p->nShapes = 0;
}

/**Function*************************************************************

  Synopsis    [Computes cut truth with optional exact cone-program caching.]

  Description [The program is cheaper than a wide truth table. Its
  variables are cut positions, so entries contain no network object IDs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Drf_Entry_t * Drf_Shape( Drf_Man_t * p, int Root, Drf_Cut_t * pCut )
{
    Drf_Shape_t * pShape;
    unsigned Code[256], Hash = pCut->nLeaves;
    int i, Id, a, b, nNodes = Vec_IntSize( p->vNodes );
    if ( !pCut->fFull || pCut->nLeaves < 8 || nNodes > 256 )
    {
        pCut->pTruth = Drf_Truth( p, Root, pCut );
        return NULL;
    }
    Gie_TruthNext( &p->M );
    p->M.pObjs[0].Truth = 0;
    p->M.pObjs[0].TruthMark = p->M.TruthMark;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        p->M.pObjs[pCut->Leaves[i]].Truth = (unsigned short) ( i + 1 );
        p->M.pObjs[pCut->Leaves[i]].TruthMark = p->M.TruthMark;
    }
    for ( i = 0; i < nNodes; i++ )
    {
        Id = Vec_IntEntry( p->vNodes, nNodes - 1 - i );
        a = p->M.pObjs[Id].Fan[0];
        b = p->M.pObjs[Id].Fan[1];
        assert( p->M.pObjs[a >> 1].TruthMark == p->M.TruthMark && p->M.pObjs[b >> 1].TruthMark == p->M.TruthMark );
        a = 2 * p->M.pObjs[a >> 1].Truth + ( a & 1 );
        b = 2 * p->M.pObjs[b >> 1].Truth + ( b & 1 );
        Code[i] = ( (unsigned) a << 16 ) | (unsigned) b;
        Hash = ( Hash ^ Code[i] ) * 16777619u;
        p->M.pObjs[Id].Truth = (unsigned short) ( pCut->nLeaves + 1 + i );
        p->M.pObjs[Id].TruthMark = p->M.TruthMark;
    }
    if ( !p->pShapes ) p->pShapes = ABC_CALLOC( Drf_Shape_t *, DRF_CACHE_BINS );
    for ( pShape = p->pShapes[Hash & ( DRF_CACHE_BINS - 1 )]; pShape; pShape = pShape->pNext )
        if ( pShape->Hash == Hash && pShape->nNodes == nNodes && pShape->nLeaves == pCut->nLeaves &&
             !memcmp( pShape->Code, Code, nNodes * sizeof( unsigned ) ) )
        {
            p->nShapeHits++;
            pCut->pTruth = pShape->pEntry->pTruth;
            return pShape->pEntry;
        }
    pCut->pTruth = Drf_Truth( p, Root, pCut );
    if ( !pCut->pTruth ) return NULL;
    pShape = (Drf_Shape_t *) ABC_ALLOC( char, sizeof( Drf_Shape_t ) + ( nNodes - 1 ) * sizeof( unsigned ) );
    pShape->pEntry = Drf_Factor( p, pCut );
    pShape->Hash = Hash;
    pShape->nNodes = nNodes;
    pShape->nLeaves = pCut->nLeaves;
    memcpy( pShape->Code, Code, nNodes * sizeof( unsigned ) );
    pShape->pNext = p->pShapes[Hash & ( DRF_CACHE_BINS - 1 )];
    p->pShapes[Hash & ( DRF_CACHE_BINS - 1 )] = pShape;
    p->nShapes++;
    pCut->pTruth = pShape->pEntry->pTruth;
    return pShape->pEntry;
}

/**Function*************************************************************

  Synopsis    [Exposes dependent boundary leaves without widening the cut.]

  Description [Replacing a shared leaf by fanins already on the boundary
  removes a false independence assumption. The scan is bounded by work.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Drf_ExtendCut( Drf_Man_t * p, int Root, Drf_Cut_t * pCut )
{
    int i, k, Id, a, b, Changed = 0, nSteps = 0;
    // Standalone refactoring focuses on shrinking into the four-input
    // library. Orchestration can also expose dependencies in wider cuts.
    if ( pCut->nLeaves > p->nExpandLimit ) return;
    for ( i = 0; i < pCut->nLeaves; i++ )
        p->M.pObjs[pCut->Leaves[i]].Inside = 1;
    for ( i = 0; i < pCut->nLeaves && nSteps < 32; i++ )
    {
        Id = pCut->Leaves[i];
        if ( p->M.pObjs[Id].Type != GIE_AND ) continue;
        a = p->M.pObjs[Id].Fan[0] >> 1;
        b = p->M.pObjs[Id].Fan[1] >> 1;
        if ( !p->M.pObjs[a].Inside && !p->M.pObjs[b].Inside ) continue;
        p->M.pObjs[Id].Inside = 0;
        for ( k = i + 1; k < pCut->nLeaves; k++ )
            pCut->Leaves[k - 1] = pCut->Leaves[k];
        pCut->nLeaves--;
        if ( a && !p->M.pObjs[a].Inside )
        {
            pCut->Leaves[pCut->nLeaves++] = a;
            p->M.pObjs[a].Inside = 1;
        }
        if ( b && !p->M.pObjs[b].Inside )
        {
            pCut->Leaves[pCut->nLeaves++] = b;
            p->M.pObjs[b].Inside = 1;
        }
        nSteps++;
        Changed = 1;
        i = -1;
    }
    for ( i = 0; i < pCut->nLeaves; i++ )
        p->M.pObjs[pCut->Leaves[i]].Inside = 0;
    if ( !Changed ) return;
    pCut->fFull = 0;
    pCut->Saved = Drf_Mffc( p, Root, pCut, 1 );
}

/**Function*************************************************************

  Synopsis    [Selects one refactoring cut and evaluates its truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Drf_SelectCut( Drf_Man_t * p, int Root, Drf_Cut_t * pCut )
{
    // One cut can add one shape and one factor entry. Reclaim both
    // caches before selection, while no cut holds a pointer into them.
    if ( p->nCache + p->nShapes >= DRF_CACHE_LIMIT - 1 )
    {
        Drf_CacheClear( p );
        p->nCacheClears++;
    }
    if ( !Drf_Boundary( p, Root, pCut ) ) return 0;
    pCut->fFull = pCut->nLeaves <= DRF_LEAF_MAX;
    if ( !pCut->fFull ) Drf_ReconvCut( p, Root, pCut );
    Drf_ExtendCut( p, Root, pCut );
    if ( pCut->Saved < 2 ) return 0;
    // A read-once tree without an associative internal edge has a unique
    // factored form. Neither ISOP polarity can improve its structure.
    if ( pCut->fFull && !pCut->fAssoc && pCut->nLeaves >= 5 && pCut->nLeaves == pCut->Saved + 1 ) return 0;
    pCut->pEntry = Drf_Shape( p, Root, pCut );
    return pCut->pTruth != NULL;
}

/**Function*************************************************************

  Synopsis    [Compacts one immutable library root into a factored program.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drf_LibGraph_rec( const Drw_LibClass_t * pClass, Kit_Graph_t * pGraph, int * pMap, int Id )
{
    int a, b, Lit0, Lit1;
    if ( pMap[Id] >= 0 ) return pMap[Id];
    // A library structure may use an input outside this cut's support.
    if ( Id < 4 ) return -1;
    a = Drw_LibNodes[pClass->iNodes + Id - 4][0];
    b = Drw_LibNodes[pClass->iNodes + Id - 4][1];
    Lit0 = Drf_LibGraph_rec( pClass, pGraph, pMap, a >> 1 );
    if ( Lit0 < 0 ) return -1;
    Lit1 = Drf_LibGraph_rec( pClass, pGraph, pMap, b >> 1 );
    if ( Lit1 < 0 ) return -1;
    return pMap[Id] = Kit_EdgeToInt(
               Kit_GraphAddNodeAnd( pGraph, Kit_IntToEdge( Lit0 ^ ( a & 1 ) ), Kit_IntToEdge( Lit1 ^ ( b & 1 ) ) ) );
}

/**Function*************************************************************

  Synopsis    [Caches small-library programs and factored covers by truth.]

  Description [The cache is local to the call. A hash match is
  always followed by full equality; cache entries contain no graph IDs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Drf_Entry_t * Drf_Factor( Drf_Man_t * p, Drf_Cut_t * pCut )
{
    Drf_Entry_t * pEntry;
    unsigned Hash = (unsigned) pCut->nLeaves, Temp[1 << ( DRF_LEAF_MAX - 5 )];
    int Words = Kit_TruthWordNum( pCut->nLeaves ), w, Phase, i, k, Size = 0;
    for ( w = 0; w < Words; w++ )
        Hash = ( Hash ^ pCut->pTruth[w] ) * 16777619u;
    for ( pEntry = p->pCache[Hash & ( DRF_CACHE_BINS - 1 )]; pEntry; pEntry = pEntry->pNext )
        if ( pEntry->Hash == Hash && pEntry->nLeaves == pCut->nLeaves &&
             !memcmp( pEntry->pTruth, pCut->pTruth, sizeof( unsigned ) * Words ) )
        {
            p->nHits++;
            return pEntry;
        }
    pEntry = ABC_CALLOC( Drf_Entry_t, 1 );
    pEntry->Hash = Hash;
    pEntry->nLeaves = pCut->nLeaves;
    pEntry->pTruth = ABC_ALLOC( unsigned, Words );
    memcpy( pEntry->pTruth, pCut->pTruth, sizeof( unsigned ) * Words );
    if ( pCut->nLeaves <= 4 && ( Drw_Transforms[pCut->pTruth[0] & 65535] & 255 ) )
    {
        unsigned Transform = Drw_Transforms[pCut->pTruth[0] & 65535];
        const Drw_LibClass_t * pClass = Drw_Classes + ( Transform & 255 );
        int nRoots = 0, Roots[DRF_GRAPH_LIMIT + 1], Map[256], j, r;
        // Keep the smallest alternatives, with library order breaking ties.
        for ( r = 0; r < pClass->nRoots; r++ )
        {
            int RootSize = Drw_LibSizes[pClass->iRoots + r];
            j = nRoots;
            while ( j > 0 && Drw_LibSizes[pClass->iRoots + Roots[j - 1]] > RootSize )
            {
                Roots[j] = Roots[j - 1];
                j--;
            }
            Roots[j] = r;
            if ( nRoots < DRF_GRAPH_LIMIT ) nRoots++;
        }
        for ( Phase = 0; Phase < nRoots; Phase++ )
        {
            Kit_Graph_t * pGraph = Kit_GraphCreate( pCut->nLeaves );
            int Root = Drw_LibRoots[pClass->iRoots + Roots[Phase]], Lit;
            memset( Map, 0xFF, sizeof( Map ) );
            for ( j = 0; j < 4; j++ )
            {
                int Pos = ( Transform >> ( 13 + 2 * j ) ) & 3;
                if ( Pos < pCut->nLeaves ) Map[j] = 2 * Pos + ( ( Transform >> ( 8 + j ) ) & 1 );
            }
            Lit = Drf_LibGraph_rec( pClass, pGraph, Map, Root >> 1 );
            if ( Lit < 0 )
            {
                Kit_GraphFree( pGraph );
                continue;
            }
            Lit ^= ( Root & 1 ) ^ ( ( Transform >> 12 ) & 1 );
            Kit_GraphSetRoot( pGraph, Kit_IntToEdge( Lit ) );
            pEntry->pGraphs[pEntry->nGraphs++] = pGraph;
        }
    }
    else
        for ( Phase = 0; Phase < 2; Phase++ )
        {
            for ( w = 0; w < Words; w++ )
                Temp[w] = pCut->pTruth[w] ^ ( Phase ? ~0u : 0 );
            // Match Kit_TruthToGraph's bound on the factoring scratch space.
            if ( Kit_TruthIsop( Temp, pCut->nLeaves, p->vMemory, 0 ) >= 0 &&
                 Vec_IntSize( p->vMemory ) <= DRF_COVER_LIMIT )
                pEntry->pGraphs[pEntry->nGraphs++] = Kit_SopFactor( p->vMemory, Phase, pCut->nLeaves, p->vMemory );
        }
    if ( pCut->nLeaves >= 5 && pCut->nLeaves <= 6 )
    {
        unsigned Reverse[2];
        char Perm[6];
        int v;
        Kit_Node_t * pNode;
        Kit_Graph_t * pGraph;
        for ( Phase = 0; Phase < 2; Phase++ )
        {
            for ( v = 0; v < pCut->nLeaves; v++ )
                Perm[v] = (char) ( pCut->nLeaves - 1 - v );
            for ( w = 0; w < Words; w++ )
                Temp[w] = pCut->pTruth[w] ^ ( Phase ? ~0u : 0 );
            Kit_TruthPermute( Reverse, Temp, pCut->nLeaves, Perm, 0 );
            if ( Kit_TruthIsop( Reverse, pCut->nLeaves, p->vMemory, 0 ) < 0 ||
                 Vec_IntSize( p->vMemory ) > DRF_COVER_LIMIT )
                continue;
            pGraph = Kit_SopFactor( p->vMemory, Phase, pCut->nLeaves, p->vMemory );
            Kit_GraphForEachNode ( pGraph, pNode, v )
            {
                if ( pNode->eEdge0.Node < (unsigned) pGraph->nLeaves )
                    pNode->eEdge0.Node = pGraph->nLeaves - 1 - pNode->eEdge0.Node;
                if ( pNode->eEdge1.Node < (unsigned) pGraph->nLeaves )
                    pNode->eEdge1.Node = pGraph->nLeaves - 1 - pNode->eEdge1.Node;
            }
            if ( pGraph->eRoot.Node < (unsigned) pGraph->nLeaves )
                pGraph->eRoot.Node = pGraph->nLeaves - 1 - pGraph->eRoot.Node;
            pEntry->pGraphs[pEntry->nGraphs++] = pGraph;
        }
    }
    for ( i = 1; i < pEntry->nGraphs; i++ )
    {
        Kit_Graph_t * pGraph = pEntry->pGraphs[i];
        k = i;
        while ( k > 0 && Kit_GraphNodeNum( pEntry->pGraphs[k - 1] ) > Kit_GraphNodeNum( pGraph ) )
        {
            pEntry->pGraphs[k] = pEntry->pGraphs[k - 1];
            k--;
        }
        pEntry->pGraphs[k] = pGraph;
    }
    pEntry->MinSize = ABC_INFINITY;
    for ( Phase = 0; Phase < pEntry->nGraphs; Phase++ )
        if ( pEntry->pGraphs[Phase] ) Size += Kit_GraphNodeNum( pEntry->pGraphs[Phase] );
    pEntry->pPairs = ABC_ALLOC( int, 2 * Abc_MaxInt( 1, Size ) );
    for ( Phase = 0; Phase < pEntry->nGraphs; Phase++ )
    {
        Kit_Graph_t * pGraph = pEntry->pGraphs[Phase];
        Kit_Node_t * pNode;
        if ( !pGraph ) continue;
        pEntry->MinSize = Abc_MinInt( pEntry->MinSize, Kit_GraphNodeNum( pGraph ) );
        Kit_GraphForEachNode ( pGraph, pNode, i )
        {
            int a, b;
            if ( pNode->eEdge0.Node >= (unsigned) pGraph->nLeaves || pNode->eEdge1.Node >= (unsigned) pGraph->nLeaves )
                continue;
            a = Kit_EdgeToInt( pNode->eEdge0 );
            b = Kit_EdgeToInt( pNode->eEdge1 );
            if ( a > b ) ABC_SWAP( int, a, b );
            for ( k = 0; k < pEntry->nPairs; k++ )
                if ( pEntry->pPairs[2 * k] == a && pEntry->pPairs[2 * k + 1] == b ) break;
            if ( pCut->nLeaves <= 4 )
            {
                assert( k < 64 );
                pEntry->PairMask[Phase] |= (word) 1 << k;
            }
            if ( k < pEntry->nPairs ) continue;
            pEntry->pPairs[2 * k] = a;
            pEntry->pPairs[2 * k + 1] = b;
            pEntry->nPairs++;
        }
    }
    pEntry->pNext = p->pCache[Hash & ( DRF_CACHE_BINS - 1 )];
    p->pCache[Hash & ( DRF_CACHE_BINS - 1 )] = pEntry;
    p->nCache++;
    return pEntry;
}

/**Function*************************************************************

  Synopsis    [Counts new gates and exact levels of one candidate graph.]

  Description [Levels are derived from the finished cut leaves, including
  when the hash finds an unvisited gate. Reusing the current root, including
  as an internal gate, is rejected.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Drf_TryGraph( Drf_Man_t * p, int Root, Drf_Cut_t * pCut, Kit_Graph_t * pGraph, int * pLevel, int BestCost )
{
    int i, a, b, Lit, Level, Added = 0, Limit = Abc_MinInt( pCut->Saved - 1, BestCost );
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    Kit_Node_t * pNode;
    if ( Kit_GraphIsConst( pGraph ) )
    {
        *pLevel = 0;
        return 0;
    }
    Vec_IntFillExtra( p->vLits, pGraph->nSize, 0 );
    Vec_IntFillExtra( p->vLevels, pGraph->nSize, 0 );
    for ( i = 0; i < pGraph->nLeaves; i++ )
    {
        Vec_IntWriteEntry( p->vLits, i, 2 * pCut->Leaves[i] );
        Vec_IntWriteEntry( p->vLevels, i, p->M.pObjs[pCut->Leaves[i]].Level );
    }
    Kit_GraphForEachNode ( pGraph, pNode, i )
    {
        a = Vec_IntEntry( p->vLits, pNode->eEdge0.Node );
        b = Vec_IntEntry( p->vLits, pNode->eEdge1.Node );
        Lit = a < 0 || b < 0 ? -1 : Gie_Lookup( &p->M, a ^ pNode->eEdge0.fCompl, b ^ pNode->eEdge1.fCompl, -1 );
        if ( Lit >= 0 && ( Lit >> 1 ) == Root ) return -1;
        if ( Lit < 0 || p->M.pObjs[Lit >> 1].Mark == p->M.Mark )
            if ( ++Added > Limit ) return -1;
        Level = 1 + Abc_MaxInt( Vec_IntEntry( p->vLevels, pNode->eEdge0.Node ),
                                Vec_IntEntry( p->vLevels, pNode->eEdge1.Node ) );
        if ( Lit >= 0 )
        {
            if ( Gie_Simplify( a ^ pNode->eEdge0.fCompl, b ^ pNode->eEdge1.fCompl ) >= 0 )
                Level = Gie_AndLevel( a ^ pNode->eEdge0.fCompl, b ^ pNode->eEdge1.fCompl,
                                      Vec_IntEntry( p->vLevels, pNode->eEdge0.Node ),
                                      Vec_IntEntry( p->vLevels, pNode->eEdge1.Node ) );
            else
                p->M.pObjs[Lit >> 1].Level = Level;
        }
        if ( Level > Required ) return -1;
        Vec_IntWriteEntry( p->vLits, i, Lit );
        Vec_IntWriteEntry( p->vLevels, i, Level );
    }
    *pLevel = Vec_IntEntry( p->vLevels, pGraph->eRoot.Node );
    return *pLevel <= Required ? Added : -1;
}

/**Function*************************************************************

  Synopsis    [Builds the best positive-gain, level-feasible factorization.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Drf_Evaluate( Drf_Man_t * p, int Id, Drf_Cut_t * pCut )
{
    Drf_Entry_t * pEntry;
    Kit_Graph_t * pBest = NULL;
    int i, a, b, Lit, Cost, Level, BestCost = pCut->Saved, BestLevel = ABC_INFINITY;
    word Shared = 0;
    p->M.iRoot = Id;
    p->FactorLit = -1;
    p->FactorLevel = 0;
    if ( Kit_TruthIsConst0( pCut->pTruth, pCut->nLeaves ) )
    {
        p->FactorLit = 0;
        return 0;
    }
    if ( Kit_TruthIsConst1( pCut->pTruth, pCut->nLeaves ) )
    {
        p->FactorLit = 1;
        return 0;
    }
    pEntry = pCut->pEntry ? pCut->pEntry : Drf_Factor( p, pCut );
    // Without intrinsic gain, some bottom-level gate must be shared
    // outside the removable cone before either graph can improve it.
    if ( pEntry->MinSize >= pCut->Saved )
    {
        for ( i = 0; i < pEntry->nPairs; i++ )
        {
            a = pEntry->pPairs[2 * i];
            b = pEntry->pPairs[2 * i + 1];
            Lit = Gie_Lookup( &p->M, 2 * pCut->Leaves[a >> 1] ^ ( a & 1 ), 2 * pCut->Leaves[b >> 1] ^ ( b & 1 ), -1 );
            if ( Lit < 0 || p->M.pObjs[Lit >> 1].Mark == p->M.Mark ) continue;
            if ( pCut->nLeaves > 4 )
            {
                Shared = 1;
                break;
            }
            Shared |= (word) 1 << i;
        }
        if ( !Shared ) return -1;
    }
    for ( i = 0; i < pEntry->nGraphs; i++ )
    {
        if ( !pEntry->pGraphs[i] ) continue;
        if ( pEntry->MinSize >= pCut->Saved && pCut->nLeaves <= 4 && !( Shared & pEntry->PairMask[i] ) ) continue;
        Cost = Drf_TryGraph( p, Id, pCut, pEntry->pGraphs[i], &Level, BestCost );
        if ( Cost < 0 || ( Cost == BestCost && Level >= BestLevel ) ) continue;
        BestCost = Cost;
        BestLevel = Level;
        pBest = pEntry->pGraphs[i];
    }
    if ( !pBest ) return -1;
    p->pFactorGraph = pBest;
    p->FactorLevel = BestLevel;
    return BestCost;
}

/**Function*************************************************************

  Synopsis    [Builds the selected factorization after its gain was checked.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Drf_BuildFactor( Drf_Man_t * p, Drf_Cut_t * pCut )
{
    Kit_Graph_t * pBest = p->pFactorGraph;
    Kit_Node_t * pNode;
    int i, a, b, Lit;
    if ( p->FactorLit >= 0 ) return p->FactorLit;
    if ( Kit_GraphIsConst( pBest ) ) return Kit_GraphIsConst1( pBest );
    for ( i = 0; i < pBest->nLeaves; i++ )
        Vec_IntWriteEntry( p->vLits, i, 2 * pCut->Leaves[i] );
    Kit_GraphForEachNode ( pBest, pNode, i )
    {
        a = Vec_IntEntry( p->vLits, pNode->eEdge0.Node ) ^ pNode->eEdge0.fCompl;
        b = Vec_IntEntry( p->vLits, pNode->eEdge1.Node ) ^ pNode->eEdge1.fCompl;
        Lit = Gie_And( &p->M, a, b );
        if ( Lit < 0 ) return -1;
        Vec_IntWriteEntry( p->vLits, i, Lit );
    }
    return Vec_IntEntry( p->vLits, pBest->eRoot.Node ) ^ pBest->eRoot.fCompl;
}

/**Function*************************************************************

  Synopsis    [Initializes one factoring context and its mutable graph.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Drf_ManInit( Drf_Man_t * p, Gia_Man_t * pGia, int fKeepLevel, int HashMode, Vec_Int_t * vCiLevels )
{
    Gie_ManStart( &p->M, pGia, fKeepLevel, HashMode, vCiLevels );
    p->nExpandLimit = 5;
    p->vNodes = Vec_IntAlloc( 1024 );
    p->vTruth = Vec_IntAlloc( 4096 );
    p->vMemory = Vec_IntAlloc( 1 << 16 );
    p->vLits = Vec_IntAlloc( 256 );
    p->vLevels = Vec_IntAlloc( 256 );
    p->pCache = ABC_CALLOC( Drf_Entry_t *, DRF_CACHE_BINS );
}

/**Function*************************************************************

  Synopsis    [Releases a factoring context and its mutable graph.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Drf_ManRelease( Drf_Man_t * p )
{
    Drf_CacheClear( p );
    ABC_FREE( p->pCache );
    ABC_FREE( p->pShapes );
    Vec_IntFree( p->vNodes );
    Vec_IntFree( p->vTruth );
    Vec_IntFree( p->vMemory );
    Vec_IntFree( p->vLits );
    Vec_IntFree( p->vLevels );
    Gie_ManStop( &p->M );
}

/**Function*************************************************************

  Synopsis    [Performs one refactoring pass and returns a new GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Drf_ManRefactor( Gia_Man_t * pGia, int fKeepLevel, int fVerbose )
{
    Drf_Man_t * p;
    Gia_Man_t * pNew;
    Vec_Int_t * vCiLevels;
    Drf_Cut_t Cut;
    int Id, Lit, NewStart, OldAnds, Done;
    abctime Start = Abc_Clock(), Setup, Export, Clock;
    if ( pGia == NULL || Gia_ManHasChoices( pGia ) || Gia_ManMuxNum( pGia ) || Gia_ManXorNum( pGia ) || Gia_ManBufNum( pGia ) )
        return NULL;
    // Internal sequential box views use a different CI order. Require
    // the standard normalized interface when explicit registers coexist.
    if ( Gia_ManIsSeqWithBoxes( pGia ) && !Gia_ManIsNormalized( pGia ) ) return NULL;
    if ( Gia_ManObjNum( pGia ) > Gie_ObjectLimit() / 2 ) return NULL;
    vCiLevels = Gia_ManBoxNum( pGia ) ? Gie_BoxCiLevels( pGia ) : NULL;
    p = ABC_CALLOC( Drf_Man_t, 1 );
    Drf_ManInit( p, pGia, fKeepLevel, GIE_HASH_READY, vCiLevels );
    Vec_IntFreeP( &vCiLevels );
    Setup = Abc_Clock() - Start;
    // Reused ready nodes finish early. All remaining original nodes retain
    // their topological visit order; each is considered at most once.
    for ( Id = 1; Id < p->M.nOrig; Id++ )
    {
        if ( p->M.pObjs[Id].Type != GIE_AND || p->M.pObjs[Id].Handled ) continue;
        assert( !p->M.pObjs[Id].Handled && p->M.pObjs[Id].Type == GIE_AND );
        assert( p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].Handled );
        assert( p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].Handled );
        // Hashed ready nodes already have their exact level.
        if ( !p->M.pObjs[Id].Hashed )
            p->M.pObjs[Id].Level = 1 + Abc_MaxInt( p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].Level,
                                                   p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].Level );
        Lit = Gie_Simplify( p->M.pObjs[Id].Fan[0], p->M.pObjs[Id].Fan[1] );
        if ( Lit < 0 && ( !p->M.pObjs[Id].Hashed || p->M.pObjs[Id].Duplicate ) )
            Lit = Gie_Lookup( &p->M, p->M.pObjs[Id].Fan[0], p->M.pObjs[Id].Fan[1], Id );
        if ( Lit >= 0 )
        {
            Gie_Finish( &p->M, Lit >> 1 );
            Gie_Replace( &p->M, Id, Lit );
            p->nMerged++;
            continue;
        }
        if ( !p->M.pObjs[Id].Hashed ) Gie_HashInsert( &p->M, Id );
        // If neither fanin is removable, the immediate cut already attains
        // the maximum possible MFFC of one node. It cannot give a gain.
        if ( ( p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].Type != GIE_AND ||
               p->M.pObjs[p->M.pObjs[Id].Fan[0] >> 1].Refs > 1 ) &&
             ( p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].Type != GIE_AND ||
               p->M.pObjs[p->M.pObjs[Id].Fan[1] >> 1].Refs > 1 ) )
            goto finish;
        Clock = fVerbose ? Abc_Clock() : 0;
        NewStart = p->M.nObjs;
        OldAnds = p->M.nAnds;
        Lit = Drf_TwoGate( p, Id, &Done );
        if ( !Done ) Lit = Drf_ThreeGate( p, Id, &Done );
        if ( !Done )
        {
            if ( !Drf_SelectCut( p, Id, &Cut ) ) goto finish;
            if ( fVerbose ) p->timeCuts += Abc_Clock() - Clock;
            Clock = fVerbose ? Abc_Clock() : 0;
            Lit = Drf_Evaluate( p, Id, &Cut );
            if ( Lit >= 0 ) Lit = Drf_BuildFactor( p, &Cut );
        }
        if ( fVerbose ) p->timeEval += Abc_Clock() - Clock;
        if ( Lit < 0 && NewStart == p->M.nObjs ) goto finish;
        Clock = fVerbose ? Abc_Clock() : 0;
        if ( Lit >= 0 ) Gie_Replace( &p->M, Id, Lit );
        // Dependent cut leaves can make library nodes coincide. Remove
        // any construction debris, also when a build rejected self-reuse.
        Gie_DeleteSince( &p->M, NewStart );
        if ( fVerbose ) p->timeUpdate += Abc_Clock() - Clock;
        assert( Lit < 0 || p->M.nAnds < OldAnds );
        p->nRewritten += Lit >= 0;
    finish:
        Gie_Finish( &p->M, Id );
    }
    Export = Abc_Clock();
    pNew = Gie_ManExport( &p->M, pGia );
    assert( p->M.nAnds == Gia_ManAndNum( pNew ) );
    Export = Abc_Clock() - Export;
    if ( fVerbose )
    {
        Abc_Print( 1, "&drf: ANDs %d -> %d. Rewrites = %d. Merges = %d. Cuts = %.0f. Limited = %d.\n",
                   Gia_ManAndNum( pGia ), Gia_ManAndNum( pNew ), p->nRewritten, p->nMerged, p->nCuts, p->nLimited );
        Abc_Print( 1, "&drf: shape-cache hits %d  resident %d.\n", p->nShapeHits, p->nShapes );
        Abc_Print( 1, "&drf: factor-cache hits %d  resident %d. Clears = %d.\n", p->nHits, p->nCache, p->nCacheClears );
        Abc_Print( 1, "&drf: import %.6f  cuts %.6f  evaluate %.6f  update %.6f  export %.6f  total %.6f sec\n",
                   (double) Setup / CLOCKS_PER_SEC, (double) p->timeCuts / CLOCKS_PER_SEC,
                   (double) p->timeEval / CLOCKS_PER_SEC, (double) p->timeUpdate / CLOCKS_PER_SEC,
                   (double) Export / CLOCKS_PER_SEC, (double) ( Abc_Clock() - Start ) / CLOCKS_PER_SEC );
    }
    Drf_ManRelease( p );
    ABC_FREE( p );
    return pNew;
}

ABC_NAMESPACE_IMPL_END
