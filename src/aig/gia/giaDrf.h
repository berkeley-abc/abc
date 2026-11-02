/**CFile****************************************************************

  FileName    [giaDrf.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cached DAG-aware AIG refactoring.]

  Synopsis    [Internal refactoring pass over the shared mutable AIG.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaDrf.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__aig__gia__giaDrf_h
#define ABC__aig__gia__giaDrf_h

#include "gia.h"
#include "giaEdit.h"
#include "bool/kit/kit.h"

ABC_NAMESPACE_HEADER_START

enum
{
    DRF_LEAF_MAX = 12,
    DRF_CACHE_BINS = 65536,
    DRF_GRAPH_LIMIT = 8
};
enum
{
    DRF_CACHE_LIMIT = 16384,
    DRF_COVER_LIMIT = 1 << 16
};
typedef struct Drf_Cut_t_ Drf_Cut_t;
typedef struct Drf_Man_t_ Drf_Man_t;
typedef struct Drf_Entry_t_ Drf_Entry_t;
typedef struct Drf_Shape_t_ Drf_Shape_t;

struct Drf_Cut_t_
{
    int Leaves[DRF_LEAF_MAX];
    int nLeaves;
    int Saved;
    int fFull;
    int fAssoc;
    unsigned * pTruth;
    Drf_Entry_t * pEntry;
};

struct Drf_Entry_t_
{
    Drf_Entry_t * pNext;
    unsigned Hash;
    int nLeaves;
    unsigned * pTruth;
    Kit_Graph_t * pGraphs[DRF_GRAPH_LIMIT];
    int nGraphs;
    word PairMask[DRF_GRAPH_LIMIT];
    int MinSize;
    int nPairs;
    int * pPairs;
};

struct Drf_Shape_t_
{
    Drf_Shape_t * pNext;
    Drf_Entry_t * pEntry;
    unsigned Hash;
    int nNodes, nLeaves;
    unsigned Code[1];
};

struct Drf_Man_t_
{
    Gie_Man_t M;
    Vec_Int_t *vNodes, *vTruth, *vMemory, *vLits, *vLevels;
    Drf_Entry_t ** pCache;
    Drf_Shape_t ** pShapes;
    Kit_Graph_t * pFactorGraph;
    int FactorLit, FactorLevel;
    int nExpandLimit;
    int nShapeHits, nShapes, nCache, nHits, nCacheClears;
    int nLimited, nRewritten, nMerged;
    double nCuts;
    abctime timeCuts, timeEval, timeUpdate;
};

extern void Drf_ManInit( Drf_Man_t * p, Gia_Man_t * pGia, int fKeepLevel, int HashMode, Vec_Int_t * vCiLevels );
extern void Drf_ManRelease( Drf_Man_t * p );
extern int Drf_SelectCut( Drf_Man_t * p, int Root, Drf_Cut_t * pCut );
extern int Drf_Evaluate( Drf_Man_t * p, int Root, Drf_Cut_t * pCut );
extern int Drf_BuildFactor( Drf_Man_t * p, Drf_Cut_t * pCut );

/**Function*************************************************************

  Synopsis    [Handles two-gate MFFCs without constructing a cut or truth.]

  Description [A three-literal conjunction can improve only by reusing
  another pair. A complemented inner AND has a unique two-gate form,
  apart from absorption when the outer literal is also an inner input.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Drf_TwoGate( Drf_Man_t * p, int Root, int * pDone )
{
    int k, Child, Outer, a, b, Lit, Level, Cost, Best = -1, BestPair = -1;
    int BestCost = 2, BestLevel = ABC_INFINITY, Pair[2], Last[2];
    int MinLevel = Abc_MaxInt( 0, p->M.pObjs[Root].Level - 10 );
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    int x = p->M.pObjs[Root].Fan[0], y = p->M.pObjs[Root].Fan[1];
    int r0 = p->M.pObjs[x >> 1].Type == GIE_AND && p->M.pObjs[x >> 1].Refs == 1 && p->M.pObjs[x >> 1].Level > MinLevel;
    int r1 = p->M.pObjs[y >> 1].Type == GIE_AND && p->M.pObjs[y >> 1].Refs == 1 && p->M.pObjs[y >> 1].Level > MinLevel;
    *pDone = 0;
    if ( r0 == r1 ) return -1;
    Child = r0 ? x : y;
    Outer = r0 ? y : x;
    a = p->M.pObjs[Child >> 1].Fan[0];
    b = p->M.pObjs[Child >> 1].Fan[1];
    for ( k = 0; k < 2; k++ )
    {
        int Var = ( k ? b : a ) >> 1;
        if ( p->M.pObjs[Var].Type == GIE_AND && p->M.pObjs[Var].Level > MinLevel &&
             p->M.pObjs[Var].Refs <= 1 + ( Var == ( Outer >> 1 ) ) )
            return -1;
    }
    *pDone = 1;
    p->M.iRoot = Root;
    if ( Child & 1 )
    {
        if ( Outer == ( a ^ 1 ) || Outer == ( b ^ 1 ) ) return Outer;
        if ( Outer != a && Outer != b ) return -1;
        a = Outer == a ? ( b ^ 1 ) : ( a ^ 1 );
        b = Outer;
        Level = Gie_AndLevel( a, b, p->M.pObjs[a >> 1].Level, p->M.pObjs[b >> 1].Level );
        return Level > Required ? -1 : Gie_And( &p->M, a, b );
    }
    if ( Outer == a || Outer == b ) return Child;
    if ( Outer == ( a ^ 1 ) || Outer == ( b ^ 1 ) ) return 0;
    Pair[0] = Gie_Lookup( &p->M, Outer, a, Root );
    Pair[1] = Gie_Lookup( &p->M, Outer, b, Root );
    Last[0] = b;
    Last[1] = a;
    if ( Pair[0] >= 0 && Pair[0] > 1 )
        p->M.pObjs[Pair[0] >> 1].Level =
            Gie_AndLevel( Outer, a, p->M.pObjs[Outer >> 1].Level, p->M.pObjs[a >> 1].Level );
    if ( Pair[1] >= 0 && Pair[1] > 1 )
        p->M.pObjs[Pair[1] >> 1].Level =
            Gie_AndLevel( Outer, b, p->M.pObjs[Outer >> 1].Level, p->M.pObjs[b >> 1].Level );
    for ( k = 0; k < 2; k++ )
    {
        if ( Pair[k] < 0 || ( Pair[k] >> 1 ) == ( Child >> 1 ) ) continue;
        Lit = Gie_Lookup( &p->M, Pair[k], Last[k], Root );
        Cost = Lit < 0;
        Level = Gie_AndLevel( Pair[k], Last[k], p->M.pObjs[Pair[k] >> 1].Level, p->M.pObjs[Last[k] >> 1].Level );
        if ( Level > Required || Cost > BestCost || ( Cost == BestCost && Level >= BestLevel ) ) continue;
        Best = Lit;
        BestPair = k;
        BestCost = Cost;
        BestLevel = Level;
    }
    if ( BestPair < 0 ) return -1;
    if ( Best >= 0 )
    {
        Gie_Finish( &p->M, Best >> 1 );
        return Best;
    }
    Gie_Finish( &p->M, Pair[BestPair] >> 1 );
    return Gie_And( &p->M, Pair[BestPair], Last[BestPair] );
}

/**Function*************************************************************

  Synopsis    [Checks the two polarities of an isolated MUX or XOR cone.]

  Description [Both forms have three gates. Replacing the products by
  their duals is useful only if at least one dual product already exists.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Drf_ThreeGate( Drf_Man_t * p, int Root, int * pDone )
{
    int x = p->M.pObjs[Root].Fan[0], y = p->M.pObjs[Root].Fan[1];
    int a, b, c, d, Sel, Then, Else, P, Q, Lit, Level0, Level1, Level;
    int Required = p->M.fKeepLevel ? p->M.pFans[Root].Required : ABC_INFINITY;
    *pDone = 0;
    if ( !( x & 1 ) || !( y & 1 ) || p->M.pObjs[x >> 1].Type != GIE_AND || p->M.pObjs[y >> 1].Type != GIE_AND ||
         p->M.pObjs[x >> 1].Refs != 1 || p->M.pObjs[y >> 1].Refs != 1 )
        return -1;
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
    *pDone = 1;
    p->M.iRoot = Root;
    if ( Then == Else ) return Then ^ 1;
    P = Gie_Lookup( &p->M, Sel, Then ^ 1, Root );
    Q = Gie_Lookup( &p->M, Sel ^ 1, Else ^ 1, Root );
    if ( P < 0 && Q < 0 ) return -1;
    Level0 = Gie_AndLevel( Sel, Then ^ 1, p->M.pObjs[Sel >> 1].Level, p->M.pObjs[Then >> 1].Level );
    Level1 = Gie_AndLevel( Sel ^ 1, Else ^ 1, p->M.pObjs[Sel >> 1].Level, p->M.pObjs[Else >> 1].Level );
    Level = P >= 0 && Q >= 0 ? Gie_AndLevel( P ^ 1, Q ^ 1, Level0, Level1 ) : 1 + Abc_MaxInt( Level0, Level1 );
    if ( Level > Required ) return -1;
    P = Gie_And( &p->M, Sel, Then ^ 1 );
    if ( P < 0 ) return -1;
    Q = Gie_And( &p->M, Sel ^ 1, Else ^ 1 );
    if ( Q < 0 ) return -1;
    Lit = Gie_And( &p->M, P ^ 1, Q ^ 1 );
    return Lit < 0 ? -1 : Lit ^ 1;
}

ABC_NAMESPACE_HEADER_END

#endif
