/**CFile****************************************************************

  FileName    [giaIf2.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact truth-aware LUT mapping.]

  Synopsis    [Priority-cut mapping directly on a GIA.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaIf2.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "bool/kit/kit.h"
#include "misc/tim/tim.h"
#include "misc/util/utilTruth.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define IF2_LEAF_MAX  6
#define IF2_CUT_MAX  32
#define IF2_INFINITY ((float)1.0e20)
#define IF2_EPSILON  ((float)0.005)

typedef struct If2_Cut_t_ If2_Cut_t;
struct If2_Cut_t_
{
    word            Truth;
    word            Sign;
    int             Leaves[IF2_LEAF_MAX];
    float           Delay;
    float           Flow;
    float           Edge;
    int             nLeaves;
};

typedef struct If2_Man_t_ If2_Man_t;
struct If2_Man_t_
{
    Gia_Man_t *     pGia;
    If2_Par_t *     pPars;
    Tim_Man_t *     pTim;
    If2_Cut_t *     pCuts;
    If2_Cut_t *     pBest;
    unsigned char * pCounts;
    int *           pRefs;
    int *           pOrigRefs;
    word *          pLocalMask;
    float *         pEstRefs;
    float *         pChoiceRefs;
    float *         pInvRefs;
    float *         pRequired;
    float *         pCoRequired;
    Vec_Int_t *     vStack;
    Vec_Int_t *     vUndo;
    int             fChoices;
    int             fTruth;
    unsigned char * pAreaSeen;
    Vec_Int_t *     vAreaNodes;
    word            AreaMasks[128];
    int             AreaCounts[128], AreaEdges[128], AreaHash[256], nAreaGroups;
    int *           pBankLeaves;
    word *          pBankMasks;
    unsigned char * pBankSize;
    unsigned char * pSkip;
    int *           pGroupOffset;
    Vec_Int_t *     vGroupInputs;
    int *           pLevelStamp;
    int *           pFlowIndex;
    int             Limit;
    int             fExact;
    int             Mode;
    int             Round;
    float           Target;
    double          nPairs;
    double          nMerged;
    double          nMinimized;
    double          nTrials;
    double          nRefVisits;
};

extern int Kit_GraphToGia( Gia_Man_t * pMan, Kit_Graph_t * pGraph, Vec_Int_t * vLeaves, int fHash );

#if defined(__GNUC__) || defined(__clang__)
#define IF2_INLINE static inline __attribute__((always_inline))
#elif defined(_MSC_VER)
#define IF2_INLINE static __forceinline
#else
#define IF2_INLINE static inline
#endif

static inline If2_Cut_t * If2_ObjCuts( If2_Man_t * p, int Id )
{
    return p->pCuts + (size_t)Id * p->pPars->nCutsMax;
}
static inline If2_Cut_t * If2_ObjBest( If2_Man_t * p, int Id )
{
    return p->pBest + Id;
}
static inline int If2_ObjIsNode( If2_Man_t * p, int Id )
{
    return Gia_ObjIsAnd( Gia_ManObj(p->pGia, Id) );
}
static inline word If2_LeafSign( int Id )
{
    return ((word)1) << (Id & 63);
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a terminal or unit cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_CutUnit( If2_Cut_t * pCut, int Id )
{
    memset( pCut, 0, sizeof(If2_Cut_t) );
    if ( Id == 0 ) return;
    pCut->Truth = ABC_CONST(0xAAAAAAAAAAAAAAAA);
    pCut->Leaves[0] = Id;
    pCut->nLeaves = 1;
    pCut->Sign = If2_LeafSign( Id );
}

/**Function*************************************************************

  Synopsis    [Aligns a six-variable truth table with a merged support.]

  Description [The mask gives the destination positions of the ordered input variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If2_Stretch( word t, unsigned Mask )
{
    switch ( Mask )
    {
    case 0: return t;
    case 1: return t;
    case 2: t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 3: return t;
    case 4: t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 5: t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 6: t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 7: return t;
    case 8: t = Abc_Tt6SwapVars(t, 0, 3); return t;
    case 9: t = Abc_Tt6SwapVars(t, 1, 3); return t;
    case 10: t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 11: t = Abc_Tt6SwapVars(t, 2, 3); return t;
    case 12: t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 13: t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 14: t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 15: return t;
    case 16: t = Abc_Tt6SwapVars(t, 0, 4); return t;
    case 17: t = Abc_Tt6SwapVars(t, 1, 4); return t;
    case 18: t = Abc_Tt6SwapVars(t, 1, 4); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 19: t = Abc_Tt6SwapVars(t, 2, 4); return t;
    case 20: t = Abc_Tt6SwapVars(t, 1, 4); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 21: t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 22: t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 23: t = Abc_Tt6SwapVars(t, 3, 4); return t;
    case 24: t = Abc_Tt6SwapVars(t, 1, 4); t = Abc_Tt6SwapVars(t, 0, 3); return t;
    case 25: t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 3); return t;
    case 26: t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 27: t = Abc_Tt6SwapVars(t, 3, 4); t = Abc_Tt6SwapVars(t, 2, 3); return t;
    case 28: t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 29: t = Abc_Tt6SwapVars(t, 3, 4); t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 30: t = Abc_Tt6SwapVars(t, 3, 4); t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 31: return t;
    case 32: t = Abc_Tt6SwapVars(t, 0, 5); return t;
    case 33: t = Abc_Tt6SwapVars(t, 1, 5); return t;
    case 34: t = Abc_Tt6SwapVars(t, 1, 5); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 35: t = Abc_Tt6SwapVars(t, 2, 5); return t;
    case 36: t = Abc_Tt6SwapVars(t, 1, 5); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 37: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 38: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 39: t = Abc_Tt6SwapVars(t, 3, 5); return t;
    case 40: t = Abc_Tt6SwapVars(t, 1, 5); t = Abc_Tt6SwapVars(t, 0, 3); return t;
    case 41: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 3); return t;
    case 42: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 43: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 3); return t;
    case 44: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 45: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 46: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 47: t = Abc_Tt6SwapVars(t, 4, 5); return t;
    case 48: t = Abc_Tt6SwapVars(t, 1, 5); t = Abc_Tt6SwapVars(t, 0, 4); return t;
    case 49: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 4); return t;
    case 50: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 4); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 51: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 4); return t;
    case 52: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 4); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 53: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 54: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 55: t = Abc_Tt6SwapVars(t, 4, 5); t = Abc_Tt6SwapVars(t, 3, 4); return t;
    case 56: t = Abc_Tt6SwapVars(t, 2, 5); t = Abc_Tt6SwapVars(t, 1, 4); t = Abc_Tt6SwapVars(t, 0, 3); return t;
    case 57: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 3); return t;
    case 58: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 59: t = Abc_Tt6SwapVars(t, 4, 5); t = Abc_Tt6SwapVars(t, 3, 4); t = Abc_Tt6SwapVars(t, 2, 3); return t;
    case 60: t = Abc_Tt6SwapVars(t, 3, 5); t = Abc_Tt6SwapVars(t, 2, 4); t = Abc_Tt6SwapVars(t, 1, 3); t = Abc_Tt6SwapVars(t, 0, 2); return t;
    case 61: t = Abc_Tt6SwapVars(t, 4, 5); t = Abc_Tt6SwapVars(t, 3, 4); t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); return t;
    case 62: t = Abc_Tt6SwapVars(t, 4, 5); t = Abc_Tt6SwapVars(t, 3, 4); t = Abc_Tt6SwapVars(t, 2, 3); t = Abc_Tt6SwapVars(t, 1, 2); t = Abc_Tt6SwapVars(t, 0, 1); return t;
    case 63: return t;
    }
    assert(0);
    return t;
}

/**Function*************************************************************

  Synopsis    [Counts bits using portable unsigned arithmetic.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If2_BitCount( word Bits )
{
    Bits -= ( Bits >> 1 ) & ABC_CONST( 0x5555555555555555 );
    Bits = ( Bits & ABC_CONST( 0x3333333333333333 ) ) + ( ( Bits >> 2 ) & ABC_CONST( 0x3333333333333333 ) );
    Bits = ( Bits + ( Bits >> 4 ) ) & ABC_CONST( 0x0F0F0F0F0F0F0F0F );
    return (int)( ( Bits * ABC_CONST( 0x0101010101010101 ) ) >> 56 );
}

IF2_INLINE int If2_CutMerge( If2_Man_t * p, If2_Cut_t * p0, If2_Cut_t * p1, If2_Cut_t * pRes )
{
    int i = 0, k = 0, n = 0, Id;
    unsigned m0 = 0, m1 = 0, mSmall = 0;
    if ( If2_BitCount(p0->Sign | p1->Sign) > p->pPars->nLutSize ) return 0;
    if ( p0->nLeaves == p->pPars->nLutSize || p1->nLeaves == p->pPars->nLutSize )
    {
        If2_Cut_t * pBig = p0->nLeaves >= p1->nLeaves ? p0 : p1;
        If2_Cut_t * pSmall = pBig == p0 ? p1 : p0;
        if ( (pBig->Sign & pSmall->Sign) != pSmall->Sign ) return 0;
        for ( i = k = 0; i < pBig->nLeaves && k < pSmall->nLeaves; i++ )
        {
            if ( pBig->Leaves[i] > pSmall->Leaves[k] ) return 0;
            if ( pBig->Leaves[i] == pSmall->Leaves[k] ) { k++; mSmall |= 1u << i; }
        }
        if ( k != pSmall->nLeaves ) return 0;
        memcpy(pRes->Leaves, pBig->Leaves, sizeof(int)*pBig->nLeaves);
        pRes->nLeaves = pBig->nLeaves;
        pRes->Sign = pBig->Sign;
        pRes->Truth = pBig == p0 ? ((1u << pBig->nLeaves)-1) | (mSmall << 6) : mSmall | (((1u << pBig->nLeaves)-1) << 6);
        p->nMerged++;
        return 1;
    }
    while ( i < p0->nLeaves || k < p1->nLeaves )
    {
        if ( k == p1->nLeaves || (i < p0->nLeaves && p0->Leaves[i] < p1->Leaves[k]) )
            { Id = p0->Leaves[i++]; m0 |= 1u << n; }
        else if ( i == p0->nLeaves || p1->Leaves[k] < p0->Leaves[i] )
            { Id = p1->Leaves[k++]; m1 |= 1u << n; }
        else
            { Id = p0->Leaves[i++]; k++; m0 |= 1u << n; m1 |= 1u << n; }
        if ( n == p->pPars->nLutSize ) return 0;
        pRes->Leaves[n++] = Id;
    }
    p->nMerged++;
    pRes->nLeaves = n;
    pRes->Sign = p0->Sign | p1->Sign;
    pRes->Truth = m0 | (m1 << 6);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Composes and optionally minimizes a merged truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_CutTruth( If2_Man_t * p, If2_Cut_t * p0, If2_Cut_t * p1, If2_Cut_t * pRes, int c0, int c1, int fXor )
{
    int i, n = pRes->nLeaves, nOld = n;
    word t0 = c0 ? ~p0->Truth : p0->Truth;
    word t1 = c1 ? ~p1->Truth : p1->Truth;
    if ( !p->fTruth ) { pRes->Truth = 0; return; }
    t0 = If2_Stretch(t0, (unsigned)pRes->Truth & 63);
    t1 = If2_Stretch(t1, (unsigned)(pRes->Truth >> 6));
    pRes->Truth = fXor ? t0 ^ t1 : t0 & t1;
    if ( p->pPars->fCutMin && (n < p0->nLeaves + p1->nLeaves || !p0->nLeaves || !p1->nLeaves) )
    {
        word Truth = pRes->Truth;
        int Leaves[IF2_LEAF_MAX], nMin;
        memcpy( Leaves, pRes->Leaves, sizeof(int) * n );
        nMin = Abc_Tt6MinBase( &Truth, Leaves, n );
        // Collapsing to an alias or constant can discard useful cut alternatives.
        if ( nMin >= 2 )
        {
            n = nMin;
            pRes->Truth = Truth;
            memcpy( pRes->Leaves, Leaves, sizeof(int) * n );
        }
    }
    if ( n == nOld ) return;
    p->nMinimized++;
    pRes->nLeaves = n;
    pRes->Sign = 0;
    for ( i = 0; i < n; i++ ) pRes->Sign |= If2_LeafSign( pRes->Leaves[i] );
    return;
}

/**Function*************************************************************

  Synopsis    [References a cut and counts its newly used mapped cone.]

  Description [Trials restore increments with an undo list instead of a second cone traversal.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_CutRef( If2_Man_t * p, If2_Cut_t * pCut, int fTrial, float * pArea, float * pEdge )
{
    int i, Id;
    float Area = (float)(pCut->nLeaves > 1);
    float Edge = pCut->nLeaves > 1 ? (float)pCut->nLeaves : 0;
    Vec_IntClear(p->vStack);
    Vec_IntClear(p->vUndo);
    for ( ; ; )
    {
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            Id = pCut->Leaves[i];
            if ( fTrial ) Vec_IntPush(p->vUndo, Id);
            p->nRefVisits++;
            if ( p->pRefs[Id]++ || !If2_ObjIsNode(p, Id) ) continue;
            Vec_IntPush(p->vStack, Id);
        }
        if ( !Vec_IntSize(p->vStack) ) break;
        pCut = If2_ObjBest(p, Vec_IntPop(p->vStack));
        Area += pCut->nLeaves > 1;
        Edge += pCut->nLeaves > 1 ? pCut->nLeaves : 0;
    }
    if ( fTrial ) Vec_IntForEachEntry(p->vUndo, Id, i) p->pRefs[Id]--;
    *pArea = Area;
    *pEdge = Edge;
}

/**Function*************************************************************

  Synopsis    [Removes the selected cut before evaluating replacements.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_CutDeref( If2_Man_t * p, If2_Cut_t * pCut )
{
    int i, Id;
    Vec_IntClear(p->vStack);
    for ( ; ; )
    {
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            Id = pCut->Leaves[i];
            assert(p->pRefs[Id] > 0);
            if ( --p->pRefs[Id] || !If2_ObjIsNode(p, Id) ) continue;
            Vec_IntPush(p->vStack, Id);
        }
        if ( !Vec_IntSize(p->vStack) ) break;
        pCut = If2_ObjBest(p, Vec_IntPop(p->vStack));
    }
}

/**Function*************************************************************

  Synopsis    [Computes delay, area and edge costs of a candidate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void If2_CutScore( If2_Man_t * p, If2_Cut_t * pCut )
{
    int i, Id;
    float Div, Delay = 0, Flow = (float)(pCut->nLeaves > 1);
    float Edge = pCut->nLeaves > 1 ? (float)pCut->nLeaves : 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        If2_Cut_t * pLeaf;
        Id = pCut->Leaves[i];
        pLeaf = If2_ObjBest( p, Id );
        Delay = Abc_MaxFloat( Delay, pLeaf->Delay );
        if ( p->fExact ) continue;
        Div = p->Mode == 2 ? (p->pRefs[Id] ? 0 : 1) : (p->pRefs[Id] ? p->pInvRefs[Id] : 1);
        Flow += pLeaf->Flow * Div;
        Edge += pLeaf->Edge * Div;
    }
    pCut->Delay = Delay + (float)(pCut->nLeaves > 1);
    if ( p->fExact )
    {
        If2_CutRef( p, pCut, 1, &Flow, &Edge );
        p->nTrials++;
    }
    pCut->Flow = Abc_MinFloat( Flow, IF2_INFINITY );
    pCut->Edge = Abc_MinFloat( Edge, IF2_INFINITY );
}

/**Function*************************************************************

  Synopsis    [Tests sorted support containment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If2_CutContains( If2_Man_t * p, If2_Cut_t * pLarge, If2_Cut_t * pSmall )
{
    int i = 0, k = 0;
    if ( pLarge->nLeaves == pSmall->nLeaves )
        return pLarge->Sign == pSmall->Sign && !memcmp(pLarge->Leaves, pSmall->Leaves, sizeof(int)*pSmall->nLeaves);
    // Choice cones can expose useful larger supports. Retain these in the
    // bounded priority bank and eliminate only identical supports.
    if ( p->fChoices ) return 0;
    if ( pLarge->nLeaves < pSmall->nLeaves || (pLarge->Sign & pSmall->Sign) != pSmall->Sign ) return 0;
    while ( i < pLarge->nLeaves && k < pSmall->nLeaves )
    {
        if ( pLarge->Leaves[i] > pSmall->Leaves[k] ) return 0;
        if ( pLarge->Leaves[i] == pSmall->Leaves[k] ) k++;
        i++;
    }
    return k == pSmall->nLeaves;
}

/**Function*************************************************************

  Synopsis    [Orders candidates with deterministic support tie breaking.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If2_CutLess( If2_Cut_t * p0, If2_Cut_t * p1, int Mode, float Required )
{
    int i, Late0 = p0->Delay > Required + IF2_EPSILON;
    int Late1 = p1->Delay > Required + IF2_EPSILON;
    if ( Late0 != Late1 ) return Late0 < Late1;
    if ( !Mode || Mode == 3 || Late0 )
    {
        if ( p0->Delay < p1->Delay - IF2_EPSILON ) return 1;
        if ( p0->Delay > p1->Delay + IF2_EPSILON ) return 0;
        if ( Mode != 3 && p0->nLeaves != p1->nLeaves ) return p0->nLeaves < p1->nLeaves;
    }
    if ( p0->Flow < p1->Flow - IF2_EPSILON ) return 1;
    if ( p0->Flow > p1->Flow + IF2_EPSILON ) return 0;
    if ( p0->Edge < p1->Edge - IF2_EPSILON ) return 1;
    if ( p0->Edge > p1->Edge + IF2_EPSILON ) return 0;
    if ( p0->Delay < p1->Delay - IF2_EPSILON ) return 1;
    if ( p0->Delay > p1->Delay + IF2_EPSILON ) return 0;
    if ( p0->nLeaves != p1->nLeaves ) return p0->nLeaves < p1->nLeaves;
    for ( i = 0; i < p0->nLeaves; i++ )
        if ( p0->Leaves[i] != p1->Leaves[i] ) return p0->Leaves[i] < p1->Leaves[i];
    return p0->Truth < p1->Truth;
}

/**Function*************************************************************

  Synopsis    [Keeps a priority bank and a separate timing alternative.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If2_CutInsert( If2_Man_t * p, If2_Cut_t * pSet, int nCuts, If2_Cut_t * pCut, If2_Cut_t * pFast, float Required, int fChecked )
{
    int i, k;
    if ( !fChecked )
        for ( i = 0; i < nCuts; i++ )
            if ( If2_CutContains(p, pCut, pSet + i) ) return nCuts;
    If2_CutScore( p, pCut );
    if ( (p->Mode == 1 || p->Mode == 2) && p->pPars->fDiverse && p->pPars->nCutsMax > 1 &&
         (pFast->nLeaves < 0 || If2_CutLess(pCut, pFast, 0, IF2_INFINITY)) )
        *pFast = *pCut;
    if ( !p->fChoices && pCut->nLeaves < p->pPars->nLutSize )
    {
        for ( i = k = 0; i < nCuts; i++ )
            if ( pSet[i].nLeaves <= pCut->nLeaves || !If2_CutContains(p, pSet+i, pCut) )
            {
                if ( k != i ) pSet[k] = pSet[i];
                k++;
            }
        nCuts = k;
    }
    for ( i = 0; i < nCuts; i++ )
        if ( If2_CutLess(pCut, pSet + i, p->Mode == 3 ? 3 : (p->Mode || p->pPars->fArea), p->Mode == 3 ? IF2_INFINITY : Required) ) break;
    if ( i == p->pPars->nCutsMax ) return nCuts;
    nCuts = Abc_MinInt( nCuts + 1, p->pPars->nCutsMax );
    for ( k = nCuts - 1; k > i; k-- ) pSet[k] = pSet[k-1];
    pSet[i] = *pCut;
    return nCuts;
}

/**Function*************************************************************

  Synopsis    [Maps a node with truth tables or a larger cut bank.]

  Description [Choice cuts are imported from earlier equivalent nodes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ObjMap( If2_Man_t * p, int Id )
{
    If2_Cut_t Set[IF2_CUT_MAX], Cut, Fast, Unit0, Unit1, Winner;
    If2_Cut_t * p0, * p1, * pOld = If2_ObjBest(p, Id);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int Id0 = Gia_ObjFaninId0(pObj, Id), Id1 = Gia_ObjFaninId1(pObj, Id);
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], nCuts = 0;
    int nBefore;
    int i, k, m, Sibl = Gia_ObjSibl(p->pGia, Id), fReferenced = p->pRefs[Id] > 0;
    float Area, Edge, Required = p->pPars->fArea ? IF2_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && fReferenced;
    Fast.nLeaves = -1;
    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutDeref( p, pOld );
    if ( p->Round && p->Mode != 3 )
    {
        Cut = *pOld;
        nCuts = If2_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
    }
    if ( Sibl )
    {
        int fCompl = Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pGia, Sibl));
        assert( Sibl < Id );
        for ( i = 0; i < p->pCounts[Sibl]; i++ )
        {
            Cut = If2_ObjCuts(p, Sibl)[i];
            if ( fCompl ) Cut.Truth = ~Cut.Truth;
            nCuts = If2_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
        }
    }
    If2_CutUnit( &Unit0, Id0 );
    If2_CutUnit( &Unit1, Id1 );
    n0 += If2_ObjBest(p, Id0)->nLeaves > 1;
    n1 += If2_ObjBest(p, Id1)->nLeaves > 1;
    for ( i = 0; i < n0; i++ )
    for ( k = 0; k < n1; k++ )
    {
        p0 = i < p->pCounts[Id0] ? If2_ObjCuts(p, Id0) + i : &Unit0;
        p1 = k < p->pCounts[Id1] ? If2_ObjCuts(p, Id1) + k : &Unit1;
        p->nPairs++;
        if ( !If2_CutMerge(p, p0, p1, &Cut) ) continue;
        for ( m = 0; m < nCuts; m++ )
            if ( If2_CutContains(p, &Cut, Set + m) ) break;
        if ( m < nCuts ) continue;
        nBefore = Cut.nLeaves;
        If2_CutTruth( p, p0, p1, &Cut, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), Gia_ObjIsXor(pObj) );
        nCuts = If2_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, nBefore == Cut.nLeaves );
    }
    assert( nCuts > 0 );
    if ( p->pPars->fDiverse && (p->Mode == 1 || p->Mode == 2) && p->pPars->nCutsMax > 1 && Fast.Delay < Set[0].Delay - IF2_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ )
            if ( Set[i].Delay <= Fast.Delay + IF2_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt( nCuts, p->pPars->nCutsMax - 1 );
            Set[i] = Fast;
            nCuts = Abc_MaxInt( nCuts, i + 1 );
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required + IF2_EPSILON )
    {
        Winner = *pOld;
        If2_CutScore(p, &Winner);
    }
    memcpy(If2_ObjCuts(p, Id), Set, sizeof(If2_Cut_t)*nCuts);
    *pOld = Winner;
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutRef( p, pOld, 0, &Area, &Edge );
}

/**Function*************************************************************

  Synopsis    [Enumerates truth-aware cuts of a three-input MUX.]

  Description [The data inputs are merged before adding the control support.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ObjMapMux( If2_Man_t * p, int Id )
{
    If2_Cut_t Set[IF2_CUT_MAX], Cut, Fast, Unit0, Unit1, Unit2, Pair, Winner;
    If2_Cut_t *p0, *p1, *p2, *pOld = If2_ObjBest( p, Id );
    Gia_Obj_t * pObj = Gia_ManObj( p->pGia, Id );
    int Id0 = Gia_ObjFaninId0( pObj, Id ), Id1 = Gia_ObjFaninId1( pObj, Id );
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], nCuts = 0;
    int Id2 = Gia_ObjFaninId2( p->pGia, Id ), n2 = p->pCounts[Id2], j;
    int nBefore;
    word t0, t1, t2;
    int i, k, m, Sibl = Gia_ObjSibl( p->pGia, Id ), fReferenced = p->pRefs[Id] > 0;
    float Area, Edge, Required = p->pPars->fArea ? IF2_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && fReferenced;
    Fast.nLeaves = -1;
    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutDeref( p, pOld );
    if ( p->Round && p->Mode != 3 )
    {
        Cut = *pOld;
        nCuts = If2_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
    }
    if ( Sibl )
    {
        int fCompl = Gia_ObjPhase( pObj ) ^ Gia_ObjPhase( Gia_ManObj( p->pGia, Sibl ) );
        assert( Sibl < Id );
        for ( i = 0; i < p->pCounts[Sibl]; i++ )
        {
            Cut = If2_ObjCuts( p, Sibl )[i];
            if ( fCompl ) Cut.Truth = ~Cut.Truth;
            nCuts = If2_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
        }
    }
    If2_CutUnit( &Unit0, Id0 );
    If2_CutUnit( &Unit1, Id1 );
    If2_CutUnit( &Unit2, Id2 );
    n2 += If2_ObjBest( p, Id2 )->nLeaves > 1;
    n0 += If2_ObjBest( p, Id0 )->nLeaves > 1;
    n1 += If2_ObjBest( p, Id1 )->nLeaves > 1;
    for ( i = 0; i < n0; i++ )
        for ( k = 0; k < n1; k++ )
        {
            p0 = i < p->pCounts[Id0] ? If2_ObjCuts( p, Id0 ) + i : &Unit0;
            p1 = k < p->pCounts[Id1] ? If2_ObjCuts( p, Id1 ) + k : &Unit1;
            if ( !If2_CutMerge( p, p0, p1, &Pair ) ) continue;
            for ( j = 0; j < n2; j++ )
            {
                p2 = j < p->pCounts[Id2] ? If2_ObjCuts( p, Id2 ) + j : &Unit2;
                p->nPairs++;
                if ( !If2_CutMerge( p, &Pair, p2, &Cut ) ) continue;
                for ( m = 0; m < nCuts; m++ )
                    if ( If2_CutContains(p,  &Cut, Set + m ) ) break;
                if ( m < nCuts ) continue;
                t0 = If2_Stretch( Gia_ObjFaninC0( pObj ) ? ~p0->Truth : p0->Truth, (unsigned)Pair.Truth & 63 );
                t1 = If2_Stretch( Gia_ObjFaninC1( pObj ) ? ~p1->Truth : p1->Truth, (unsigned)( Pair.Truth >> 6 ) );
                t0 = If2_Stretch( t0, (unsigned)Cut.Truth & 63 );
                t1 = If2_Stretch( t1, (unsigned)Cut.Truth & 63 );
                t2 = If2_Stretch( Gia_ObjFaninC2( p->pGia, pObj ) ? ~p2->Truth : p2->Truth, (unsigned)( Cut.Truth >> 6 ) );
                Cut.Truth = ( t2 & t1 ) | ( ~t2 & t0 );
                nBefore = Cut.nLeaves;
                if ( p->pPars->fCutMin )
                {
                    int Leaves[6], n;
                    word Truth = Cut.Truth;
                    memcpy( Leaves, Cut.Leaves, sizeof( int ) * Cut.nLeaves );
                    n = Abc_Tt6MinBase( &Truth, Leaves, Cut.nLeaves );
                    if ( n >= 2 && n < Cut.nLeaves )
                    {
                        Cut.Truth = Truth;
                        Cut.nLeaves = n;
                        Cut.Sign = 0;
                        memcpy( Cut.Leaves, Leaves, sizeof( int ) * n );
                        for ( m = 0; m < n; m++ ) Cut.Sign |= If2_LeafSign( Leaves[m] );
                        p->nMinimized++;
                    }
                }
                nCuts = If2_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, nBefore == Cut.nLeaves );
            }
        }
    assert( nCuts > 0 );
    if ( p->pPars->fDiverse && ( p->Mode == 1 || p->Mode == 2 ) && p->pPars->nCutsMax > 1 &&
         Fast.Delay < Set[0].Delay - IF2_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ )
            if ( Set[i].Delay <= Fast.Delay + IF2_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt( nCuts, p->pPars->nCutsMax - 1 );
            Set[i] = Fast;
            nCuts = Abc_MaxInt( nCuts, i + 1 );
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required + IF2_EPSILON )
    {
        Winner = *pOld;
        If2_CutScore( p, &Winner );
    }
    memcpy( If2_ObjCuts( p, Id ), Set, sizeof( If2_Cut_t ) * nCuts );
    *pOld = Winner;
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutRef( p, pOld, 0, &Area, &Edge );
}

/**Function*************************************************************

  Synopsis    [Keeps feasible output constraints and tightens them after seeding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float If2_CoRequired( If2_Man_t * p, int iCo, float Delay )
{
    float Required = p->Target;
    if ( p->pGia->vCoReqs ) Required = (float)Vec_IntEntry(p->pGia->vCoReqs, iCo);
    else if ( p->pGia->vOutReqs ) Required = Vec_FltSize(p->pGia->vOutReqs) ? Vec_FltEntry(p->pGia->vOutReqs, iCo) : p->pGia->DefOutReqs;
    if ( p->pPars->fArea ) return IF2_INFINITY;
    // Freeze feasible bounds, then keep any improvement found by the seed round.
    // Clamp the update so explicit output constraints can never gain slack.
    if ( p->Round == 0 ) p->pCoRequired[iCo] = Abc_MaxFloat( Required, Delay );
    else if ( p->Mode == 3 ) p->pCoRequired[iCo] = Abc_MinFloat( p->pCoRequired[iCo], Abc_MaxFloat(Required, Delay) );
    return p->pCoRequired[iCo];
}

/**Function*************************************************************

  Synopsis    [Extracts the cover and propagates required times.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ManRequired( If2_Man_t * p )
{
    Gia_Obj_t * pObj;
    If2_Cut_t * pCut;
    int i, k, Id, nObjs = Gia_ManObjNum(p->pGia);
    float Delay = 0, Required, LeafReq;
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachCo( p->pGia, pObj, i )
        Delay = Abc_MaxFloat( Delay, If2_ObjBest(p, Gia_ObjFaninId0p(p->pGia, pObj))->Delay );
    p->pPars->Delay = Delay;
    // Area recovery must not spend a depth improvement found during seeding.
    if ( p->Round == 0 )
        p->Target = Abc_MaxFloat( Delay, p->pPars->DelayTarget );
    else if ( p->Mode == 3 )
        p->Target = Abc_MinFloat( p->Target, Abc_MaxFloat(Delay, p->pPars->DelayTarget) );
    memset( p->pRefs, 0, sizeof(int) * nObjs );
    for ( i = 0; i < nObjs; i++ ) p->pRequired[i] = IF2_INFINITY;
    if ( p->pTim )
    {
        Tim_ManIncrementTravId( p->pTim );
        Tim_ManInitPoRequiredAll( p->pTim, p->pPars->fArea ? IF2_INFINITY : p->Target );
    }
    Gia_ManForEachObjReverse1( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) )
        {
            Id = Gia_ObjFaninId0(pObj, i);
            Required = p->pTim ? Tim_ManGetCoRequired(p->pTim, Gia_ObjCioId(pObj)) : If2_CoRequired(p, Gia_ObjCioId(pObj), If2_ObjBest(p, Id)->Delay);
            p->pRequired[Id] = Abc_MinFloat( p->pRequired[Id], Required );
            p->pRefs[Id]++;
        }
        else if ( Gia_ObjIsCi(pObj) )
        {
            if ( p->pTim ) Tim_ManSetCiRequired( p->pTim, Gia_ObjCioId(pObj), p->pRequired[i] );
        }
        else if ( p->pRefs[i] )
        {
            pCut = If2_ObjBest( p, i );
            p->pPars->Area += pCut->nLeaves > 1;
            p->pPars->Edge += pCut->nLeaves > 1 ? pCut->nLeaves : 0;
            LeafReq = p->pRequired[i] - (float)(pCut->nLeaves > 1);
            for ( k = 0; k < pCut->nLeaves; k++ )
            {
                Id = pCut->Leaves[k];
                assert( Id < i );
                p->pRefs[Id]++;
                p->pRequired[Id] = Abc_MinFloat( p->pRequired[Id], LeafReq );
            }
        }
    }
    for ( i = 0; i < nObjs; i++ )
    {
        p->pEstRefs[i] = (p->pEstRefs[i] + 2 * (float)Abc_MaxInt(1, p->pRefs[i])) / 3;
        p->pInvRefs[i] = 1.0f / p->pEstRefs[i];
    }
}

/**Function*************************************************************

  Synopsis    [Shares exact-area reference work among candidate cuts.]

  Description [Each newly referenced LUT is labeled by the palette leaves that reach it.
  Its area is charged once when a candidate intersects this label.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_AreaCache( If2_Man_t * p, int * Palette, int nPalette )
{
    If2_Cut_t * Cut;
    word Mask;
    int i, k, Id, Leaf, Bin, Group, nGroups = 0;
    p->nAreaGroups = 0;
    Vec_IntClear(p->vAreaNodes);
    Vec_IntClear(p->vStack);
    for ( i = 0; i < nPalette; i++ )
    {
        Id = Palette[i];
        if ( p->pRefs[Id] || !If2_ObjIsNode(p, Id) ) continue;
        p->pLocalMask[Id] |= ((word)1) << i;
        Vec_IntPush(p->vStack, Id);
    }
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntPop(p->vStack);
        if ( Id < 0 ) { Vec_IntPush(p->vAreaNodes, -Id); continue; }
        if ( p->pAreaSeen[Id] ) continue;
        p->pAreaSeen[Id] = 1;
        Vec_IntPush(p->vStack, -Id);
        Cut = If2_ObjBest(p, Id);
        for ( k = 0; k < Cut->nLeaves; k++ )
        {
            Leaf = Cut->Leaves[k];
            if ( !p->pRefs[Leaf] && If2_ObjIsNode(p, Leaf) && !p->pAreaSeen[Leaf] ) Vec_IntPush(p->vStack, Leaf);
        }
    }
    memset(p->AreaHash, -1, sizeof(p->AreaHash));
    for ( i = Vec_IntSize(p->vAreaNodes)-1; i >= 0; i-- )
    {
        Id = Vec_IntEntry(p->vAreaNodes, i);
        Mask = p->pLocalMask[Id];
        assert(Mask != 0);
        Cut = If2_ObjBest(p, Id);
        for ( k = 0; k < Cut->nLeaves; k++ )
        {
            Leaf = Cut->Leaves[k];
            if ( p->pAreaSeen[Leaf] ) p->pLocalMask[Leaf] |= Mask;
        }
        if ( Cut->nLeaves < 2 || nGroups == 128 ) continue;
        Bin = (int)((Mask * ABC_CONST(0x9e3779b97f4a7c15)) >> 56);
        for ( ; p->AreaHash[Bin] >= 0 && p->AreaMasks[p->AreaHash[Bin]] != Mask; Bin = (Bin+1)&255 ) {}
        Group = p->AreaHash[Bin];
        if ( Group < 0 )
        {
            Group = p->AreaHash[Bin] = nGroups++;
            p->AreaMasks[Group] = Mask;
            p->AreaCounts[Group] = p->AreaEdges[Group] = 0;
        }
        p->AreaCounts[Group]++;
        p->AreaEdges[Group] += Cut->nLeaves;
    }
    Vec_IntForEachEntry(p->vAreaNodes, Id, i)
    {
        p->pAreaSeen[Id] = 0;
        p->pLocalMask[Id] = 0;
    }
    p->nAreaGroups = nGroups == 128 ? -1 : nGroups;
}

typedef struct If2_BCut_t_ If2_BCut_t;
struct If2_BCut_t_
{
    word Mask;
    float Delay, Flow, Edge;
    int Size;
};

static inline int If2_FirstBit( word Bits )
{
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_ctzll(Bits);
#else
    static const unsigned char First[64] = { 0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6 };
    return First[((Bits & (~Bits+1)) * ABC_CONST(0x03f79d71b4cb0a89)) >> 58];
#endif
}

/**Function*************************************************************

  Synopsis    [Materializes the selected support from its palette mask.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void If2_BitUnpack( If2_Cut_t * Cut, If2_BCut_t * B, int * Palette )
{
    word Bits;
    int n = 0;
    Cut->Truth = Cut->Sign = 0;
    Cut->Delay = B->Delay; Cut->Flow = B->Flow; Cut->Edge = B->Edge;
    Cut->nLeaves = B->Size;
    for ( Bits = B->Mask; Bits; Bits &= Bits-1 )
    {
        Cut->Leaves[n] = Palette[If2_FirstBit(Bits)];
        Cut->Sign |= If2_LeafSign(Cut->Leaves[n++]);
    }
    assert(n == B->Size);
}

/**Function*************************************************************

  Synopsis    [Compares compact cuts without materializing their supports.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If2_BitLess( If2_BCut_t * A, If2_BCut_t * B, int Mode, float Required )
{
    int LateA = A->Delay > Required+IF2_EPSILON, LateB = B->Delay > Required+IF2_EPSILON;
    word Diff;
    if ( LateA != LateB ) return LateA < LateB;
    if ( !Mode || Mode == 3 || LateA )
    {
        if ( A->Delay < B->Delay-IF2_EPSILON ) return 1;
        if ( A->Delay > B->Delay+IF2_EPSILON ) return 0;
        if ( Mode != 3 && A->Size != B->Size ) return A->Size < B->Size;
    }
    if ( A->Flow < B->Flow-IF2_EPSILON ) return 1;
    if ( A->Flow > B->Flow+IF2_EPSILON ) return 0;
    if ( A->Edge < B->Edge-IF2_EPSILON ) return 1;
    if ( A->Edge > B->Edge+IF2_EPSILON ) return 0;
    if ( A->Delay < B->Delay-IF2_EPSILON ) return 1;
    if ( A->Delay > B->Delay+IF2_EPSILON ) return 0;
    if ( A->Size != B->Size ) return A->Size < B->Size;
    Diff = A->Mask ^ B->Mask;
    return !!(A->Mask & (Diff & (~Diff+1)));
}



/**Function*************************************************************

  Synopsis    [Scores a compact cut, using shared exact-area dependencies.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
IF2_INLINE void If2_BitScore( If2_Man_t * p, If2_BCut_t * Cut, int * Palette, float Costs[64][3] )
{
    word Bits;
    int i;
    float Delay = 0, Flow = (float)(Cut->Size > 1), Edge = Cut->Size > 1 ? (float)Cut->Size : 0;
    for ( Bits = Cut->Mask; Bits; Bits &= Bits-1 )
    {
        i = If2_FirstBit(Bits);
        Delay = Abc_MaxFloat(Delay, Costs[i][0]);
        Flow += Costs[i][1]; Edge += Costs[i][2];
    }
    Cut->Delay = Delay + (Cut->Size > 1);
    if ( p->fExact && p->nAreaGroups >= 0 )
    {
        for ( i = 0; i < p->nAreaGroups; i++ )
            if ( p->AreaMasks[i] & Cut->Mask ) { Flow += p->AreaCounts[i]; Edge += p->AreaEdges[i]; }
    }
    else if ( p->fExact )
    {
        If2_Cut_t Temp;
        If2_BitUnpack(&Temp, Cut, Palette);
        If2_CutRef(p, &Temp, 1, &Flow, &Edge);
        p->nTrials++;
    }
    Cut->Flow = Abc_MinFloat(Flow, IF2_INFINITY);
    Cut->Edge = Abc_MinFloat(Edge, IF2_INFINITY);
}

/**Function*************************************************************

  Synopsis    [Retains compact priority cuts and a timing alternative.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
IF2_INLINE int If2_BitKeep( If2_Man_t * p, If2_BCut_t * Set, int nCuts, If2_BCut_t * Cut, If2_BCut_t * Fast, float Required )
{
    int i, k;
    if ( (p->Mode == 1 || p->Mode == 2) && p->pPars->fDiverse && p->Limit > 1 &&
        (Fast->Size < 0 || If2_BitLess(Cut, Fast, 0, IF2_INFINITY)) ) *Fast = *Cut;
    for ( i = k = 0; i < nCuts; i++ )
        if ( (Cut->Mask & Set[i].Mask) != Cut->Mask )
        {
            if ( k != i ) Set[k] = Set[i];
            k++;
        }
    nCuts = k;
    for ( i = 0; i < nCuts; i++ )
        if ( If2_BitLess(Cut, Set+i, p->Mode == 3 ? 3 : (p->Mode || p->pPars->fArea), p->Mode == 3 ? IF2_INFINITY : Required) ) break;
    if ( i == p->Limit ) return nCuts;
    nCuts = Abc_MinInt(nCuts+1, p->Limit);
    for ( k = nCuts-1; k > i; k-- ) Set[k] = Set[k-1];
    Set[i] = *Cut;
    return nCuts;
}

/**Function*************************************************************

  Synopsis    [Merges two compact cut banks over one sorted leaf palette.]

  Description [Palette positions are exact local bit indices, not hash signatures.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ObjMapBits( If2_Man_t * p, int Id )
{
    If2_BCut_t Set[4], Cut, Fast, Winner;
    If2_Cut_t * pOld = If2_ObjBest(p, Id);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int Id0 = Gia_ObjFaninId0(pObj, Id), Id1 = Gia_ObjFaninId1(pObj, Id);
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], nCuts = 0;
    word Masks[11], Mask;
    int Palette[64], nPalette = 0, i, j, k, n, Leaf, fReferenced = p->pRefs[Id] > 0;
    float Costs[64][3], Div, Area, Edge, Required = p->pPars->fArea ? IF2_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && fReferenced;
    Fast.Size = -1;
    {
        int * Pal0 = p->pBankLeaves + (size_t)Id0*p->pPars->nCutsMax*6;
        int * Pal1 = p->pBankLeaves + (size_t)Id1*p->pPars->nCutsMax*6;
        word * Bank0 = p->pBankMasks + (size_t)Id0*p->pPars->nCutsMax;
        word * Bank1 = p->pBankMasks + (size_t)Id1*p->pPars->nCutsMax;
        word Expand0[25], Expand1[25], Bit, Bits;
        int nPal0 = p->pBankSize[Id0], nPal1 = p->pBankSize[Id1];
        int nOld = p->Round ? pOld->nLeaves : 0;
        int a = 0, b = 0, o = 0, A, B, O, Add0 = If2_ObjBest(p, Id0)->nLeaves > 1, Add1 = If2_ObjBest(p, Id1)->nLeaves > 1;
        Masks[n0+n1+Add0+Add1] = 0;
        while ( a < nPal0+Add0 || b < nPal1+Add1 || o < nOld )
        {
            A = a < nPal0 ? Pal0[a] : (a == nPal0 && Add0 ? Id0 : INT_MAX);
            B = b < nPal1 ? Pal1[b] : (b == nPal1 && Add1 ? Id1 : INT_MAX);
            O = o < nOld ? pOld->Leaves[o] : INT_MAX;
            Leaf = Abc_MinInt(A, Abc_MinInt(B, O));
            assert(nPalette < 64);
            Bit = ((word)1) << nPalette;
            Palette[nPalette++] = Leaf;
            if ( A == Leaf ) Expand0[a++] = Bit;
            if ( B == Leaf ) Expand1[b++] = Bit;
            if ( O == Leaf ) { Masks[n0+n1+Add0+Add1] |= Bit; o++; }
        }
        for ( i = 0; i < n0; i++ )
        {
            Masks[i] = 0;
            for ( Bits = Bank0[i]; Bits; Bits &= Bits-1 ) Masks[i] |= Expand0[If2_FirstBit(Bits)];
        }
        if ( Add0 ) Masks[n0++] = Expand0[nPal0];
        for ( i = 0; i < n1; i++ )
        {
            Masks[n0+i] = 0;
            for ( Bits = Bank1[i]; Bits; Bits &= Bits-1 ) Masks[n0+i] |= Expand1[If2_FirstBit(Bits)];
        }
        if ( Add1 ) Masks[n0+n1++] = Expand1[nPal1];
    }

    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutDeref(p, pOld);
    for ( i = 0; i < nPalette; i++ )
    {
        Leaf = Palette[i];
        Div = p->Mode == 2 ? (p->pRefs[Leaf] ? 0 : 1) : (p->pRefs[Leaf] ? p->pInvRefs[Leaf] : 1);
        Costs[i][0] = If2_ObjBest(p, Leaf)->Delay;
        Costs[i][1] = p->fExact ? 0 : If2_ObjBest(p, Leaf)->Flow * Div;
        Costs[i][2] = p->fExact ? 0 : If2_ObjBest(p, Leaf)->Edge * Div;
    }
    if ( p->fExact ) If2_AreaCache(p, Palette, nPalette);
    if ( p->Round && p->Mode != 3 )
    {
        Cut.Mask = Masks[n0+n1]; Cut.Size = pOld->nLeaves;
        If2_BitScore(p, &Cut, Palette, Costs);
        nCuts = If2_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
    }
    for ( i = 0; i < n0; i++ )
    for ( k = 0; k < n1; k++ )
    {
        p->nPairs++;
        Mask = Masks[i] | Masks[n0+k];
        n = If2_BitCount(Mask);
        if ( n > p->pPars->nLutSize ) continue;
        p->nMerged++;
        for ( j = 0; j < nCuts; j++ ) if ( (Mask & Set[j].Mask) == Set[j].Mask ) break;
        if ( j < nCuts ) continue;
        Cut.Mask = Mask; Cut.Size = n;
        If2_BitScore(p, &Cut, Palette, Costs);
        nCuts = If2_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
    }
    assert(nCuts > 0);
    if ( p->pPars->fDiverse && (p->Mode == 1 || p->Mode == 2) && p->Limit > 1 && Fast.Delay < Set[0].Delay-IF2_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ ) if ( Set[i].Delay <= Fast.Delay+IF2_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt(nCuts, p->Limit-1); Set[i] = Fast; nCuts = Abc_MaxInt(nCuts, i+1);
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required+IF2_EPSILON )
    {
        Winner.Mask = Masks[n0+n1]; Winner.Size = pOld->nLeaves;
        If2_BitScore(p, &Winner, Palette, Costs);
    }
    {
        int * SavedLeaves = p->pBankLeaves + (size_t)Id*p->pPars->nCutsMax*6;
        word * SavedMasks = p->pBankMasks + (size_t)Id*p->pPars->nCutsMax;
        word Used = 0, Bits, Expand[64];
        int Count = 0;
        for ( i = 0; i < nCuts; i++ ) Used |= Set[i].Mask;
        for ( Bits = Used; Bits; Bits &= Bits-1 )
        {
            j = If2_FirstBit(Bits);
            Expand[j] = ((word)1) << Count;
            SavedLeaves[Count++] = Palette[j];
        }
        p->pBankSize[Id] = (unsigned char)Count;
        for ( i = 0; i < nCuts; i++ )
        {
            SavedMasks[i] = 0;
            for ( Bits = Set[i].Mask; Bits; Bits &= Bits-1 ) SavedMasks[i] |= Expand[If2_FirstBit(Bits)];
        }
    }

    If2_BitUnpack(pOld, &Winner, Palette);
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutRef(p, pOld, 0, &Area, &Edge);
}

/**Function*************************************************************

  Synopsis    [Maps a protected three-input fanout-free group.]

  Description [The initial mapped boundaries remain available; only unused interiors
  are hidden from later rounds.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ObjMapGroup( If2_Man_t * p, int Id )
{
    If2_BCut_t Set[4], Cut, Fast, Winner;
    If2_Cut_t * pOld = If2_ObjBest(p, Id);
    int * Inputs = Vec_IntEntryP(p->vGroupInputs, p->pGroupOffset[Id]);
    int Id0 = Inputs[0], Id1 = Inputs[1], Id2 = Inputs[2];
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], n2 = p->pCounts[Id2], nCuts = 0;
    word Masks[16], Mask, Pair;
    int Palette[64], nPalette = 0, i, j, k, c, n, Leaf, fReferenced = p->pRefs[Id] > 0;
    float Costs[64][3], Div, Area, Edge, Required = p->pPars->fArea ? IF2_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && fReferenced;
    Fast.Size = -1;
    {
        int Pos[4] = {0,0,0,0}, Count[4], Next[4], q, Total = 0;
        int * Pals[4];
        word Expand[3][19], Bits, Bit;
        for ( q = 0; q < 3; q++ )
        {
            Pals[q] = p->pBankLeaves + (size_t)Inputs[q]*p->pPars->nCutsMax*6;
            Count[q] = p->pBankSize[Inputs[q]]+(If2_ObjBest(p, Inputs[q])->nLeaves > 1);
            Total += p->pCounts[Inputs[q]]+(If2_ObjBest(p, Inputs[q])->nLeaves > 1);
        }
        Pals[3] = pOld->Leaves; Count[3] = p->Round ? pOld->nLeaves : 0;
        Masks[Total] = 0;
        for ( ; ; )
        {
            Leaf = INT_MAX;
            for ( q = 0; q < 4; q++ )
            {
                Next[q] = Pos[q] == Count[q] ? INT_MAX : (q < 3 && Pos[q] == p->pBankSize[Inputs[q]] ? Inputs[q] : Pals[q][Pos[q]]);
                Leaf = Abc_MinInt(Leaf, Next[q]);
            }
            if ( Leaf == INT_MAX ) break;
            assert(nPalette < 64);
            Bit = ((word)1) << nPalette; Palette[nPalette++] = Leaf;
            for ( q = 0; q < 4; q++ ) if ( Next[q] == Leaf )
            {
                if ( q < 3 ) Expand[q][Pos[q]] = Bit;
                else Masks[Total] |= Bit;
                Pos[q]++;
            }
        }
        Total = 0;
        for ( q = 0; q < 3; q++ )
        {
            word * Bank = p->pBankMasks + (size_t)Inputs[q]*p->pPars->nCutsMax;
            for ( i = 0; i < p->pCounts[Inputs[q]]; i++ )
            {
                Masks[Total] = 0;
                for ( Bits = Bank[i]; Bits; Bits &= Bits-1 ) Masks[Total] |= Expand[q][If2_FirstBit(Bits)];
                Total++;
            }
            if ( If2_ObjBest(p, Inputs[q])->nLeaves > 1 ) Masks[Total++] = Expand[q][Count[q]-1];
        }
        n0 += If2_ObjBest(p, Id0)->nLeaves > 1;
        n1 += If2_ObjBest(p, Id1)->nLeaves > 1;
        n2 += If2_ObjBest(p, Id2)->nLeaves > 1;
    }

    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutDeref(p, pOld);
    for ( i = 0; i < nPalette; i++ )
    {
        Leaf = Palette[i];
        Div = p->Mode == 2 ? (p->pRefs[Leaf] ? 0 : 1) : (p->pRefs[Leaf] ? p->pInvRefs[Leaf] : 1);
        Costs[i][0] = If2_ObjBest(p, Leaf)->Delay;
        Costs[i][1] = p->fExact ? 0 : If2_ObjBest(p, Leaf)->Flow * Div;
        Costs[i][2] = p->fExact ? 0 : If2_ObjBest(p, Leaf)->Edge * Div;
    }
    if ( p->fExact ) If2_AreaCache(p, Palette, nPalette);
    if ( p->Round && p->Mode != 3 )
    {
        Cut.Mask = Masks[n0+n1+n2]; Cut.Size = pOld->nLeaves;
        If2_BitScore(p, &Cut, Palette, Costs);
        nCuts = If2_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
    }
    for ( i = 0; i < n0; i++ )
    for ( k = 0; k < n1; k++ )
    {
        Pair = Masks[i] | Masks[n0+k];
        if ( If2_BitCount(Pair) > p->pPars->nLutSize ) continue;
        for ( c = 0; c < n2; c++ )
        {
            p->nPairs++;
            Mask = Pair | Masks[n0+n1+c];
            n = If2_BitCount(Mask);
            if ( n > p->pPars->nLutSize ) continue;
            p->nMerged++;
            for ( j = 0; j < nCuts; j++ ) if ( (Mask & Set[j].Mask) == Set[j].Mask ) break;
            if ( j < nCuts ) continue;
            Cut.Mask = Mask; Cut.Size = n;
            If2_BitScore(p, &Cut, Palette, Costs);
            nCuts = If2_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
        }
    }
    assert(nCuts > 0);
    if ( p->pPars->fDiverse && (p->Mode == 1 || p->Mode == 2) && p->Limit > 1 && Fast.Delay < Set[0].Delay-IF2_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ ) if ( Set[i].Delay <= Fast.Delay+IF2_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt(nCuts, p->Limit-1); Set[i] = Fast; nCuts = Abc_MaxInt(nCuts, i+1);
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required+IF2_EPSILON )
    {
        Winner.Mask = Masks[n0+n1+n2]; Winner.Size = pOld->nLeaves;
        If2_BitScore(p, &Winner, Palette, Costs);
    }
    {
        int * SavedLeaves = p->pBankLeaves + (size_t)Id*p->pPars->nCutsMax*6;
        word * SavedMasks = p->pBankMasks + (size_t)Id*p->pPars->nCutsMax;
        word Used = 0, Bits, Expand[64];
        int Count = 0;
        for ( i = 0; i < nCuts; i++ ) Used |= Set[i].Mask;
        for ( Bits = Used; Bits; Bits &= Bits-1 )
        {
            j = If2_FirstBit(Bits);
            Expand[j] = ((word)1) << Count;
            SavedLeaves[Count++] = Palette[j];
        }
        p->pBankSize[Id] = (unsigned char)Count;
        for ( i = 0; i < nCuts; i++ )
        {
            SavedMasks[i] = 0;
            for ( Bits = Set[i].Mask; Bits; Bits &= Bits-1 ) SavedMasks[i] |= Expand[If2_FirstBit(Bits)];
        }
    }

    If2_BitUnpack(pOld, &Winner, Palette);
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If2_CutRef(p, pOld, 0, &Area, &Edge);
}

/**Function*************************************************************

  Synopsis    [Groups fanout-free cones after the first delay mapping.]

  Description [Groups have at most three distinct inputs and never hide a selected
  mapping boundary. The original AIG is retained for export.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ManGroup( If2_Man_t * p )
{
    Gia_Obj_t * Obj, * Node;
    int Root, Id, i, k, Good, nNodes, nLeaves, nStack, nGroups = 0;
    int Stack[64], Nodes[32], Leaves[3];
    if ( p->fTruth || p->pTim || Gia_ManBufNum(p->pGia) || p->pPars->nCutsMax > 3 || p->pPars->nLutSize < 3 ) return;
    Gia_ManForEachObjReverse1(p->pGia, Obj, Root)
    {
        if ( !Gia_ObjIsAnd(Obj) || p->pSkip[Root] ) continue;
        nNodes = nLeaves = 0; nStack = Good = 1; Stack[0] = Root;
        while ( nStack )
        {
            Id = Stack[--nStack];
            if ( !Id ) continue;
            Node = Gia_ManObj(p->pGia, Id);
            if ( Gia_ObjIsAnd(Node) && !p->pSkip[Id] && (Id == Root || (p->pOrigRefs[Id] == 1 && !p->pRefs[Id])) )
            {
                if ( nNodes == 32 ) { Good = 0; break; }
                Nodes[nNodes++] = Id;
                Stack[nStack++] = Gia_ObjFaninId0(Node, Id);
                Stack[nStack++] = Gia_ObjFaninId1(Node, Id);
            }
            else
            {
                for ( i = 0; i < nLeaves; i++ ) if ( Leaves[i] == Id ) break;
                if ( i < nLeaves ) continue;
                if ( nLeaves == 3 ) { Good = 0; break; }
                Leaves[nLeaves++] = Id;
            }
        }
        if ( !Good || nNodes < 2 ) continue;
        p->pGroupOffset[Root] = Vec_IntSize(p->vGroupInputs);
        for ( i = 0; i < 3; i++ ) Vec_IntPush(p->vGroupInputs, i < nLeaves ? Leaves[i] : 0);
        for ( i = 1; i < nNodes; i++ ) { assert(!p->pRefs[Nodes[i]]); p->pSkip[Nodes[i]] = 1; }
        nGroups++;
    }
    memset(p->pOrigRefs, 0, sizeof(int)*Gia_ManObjNum(p->pGia));
    Gia_ManForEachObj1(p->pGia, Obj, Id)
    {
        if ( Gia_ObjIsCi(Obj) || p->pSkip[Id] ) continue;
        if ( p->pGroupOffset[Id] )
            for ( k = 0; k < 3; k++ ) p->pOrigRefs[Vec_IntEntry(p->vGroupInputs, p->pGroupOffset[Id]+k)]++;
        else
        {
            p->pOrigRefs[Gia_ObjFaninId0(Obj, Id)]++;
            if ( Gia_ObjIsAnd(Obj) ) p->pOrigRefs[Gia_ObjFaninId1(Obj, Id)]++;
        }
    }
    if ( p->pPars->fVerbose ) Abc_Print(1, "If2 three-input groups = %d\n", nGroups);
}

/**Function*************************************************************

  Synopsis    [Evaluates a repaired structural cut inside its bounded window.]

  Description [The window is already in postorder. Boundary nodes outside the cut
  remain unknown; the cut must separate them from its root.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If2_LevelCutTruth( If2_Man_t * p, int Root, If2_Cut_t * pCut, int * Nodes, int nNodes )
{
    static const word Vars[6] = { ABC_CONST( 0xAAAAAAAAAAAAAAAA ), ABC_CONST( 0xCCCCCCCCCCCCCCCC ),
                                  ABC_CONST( 0xF0F0F0F0F0F0F0F0 ), ABC_CONST( 0xFF00FF00FF00FF00 ),
                                  ABC_CONST( 0xFFFF0000FFFF0000 ), ABC_CONST( 0xFFFFFFFF00000000 ) };
    word Values[64], Known = 0, t0, t1, t2;
    Gia_Obj_t * Obj;
    int i, k, Id, Id0, Id1, Id2;
    assert( nNodes > 0 && nNodes <= 64 && Nodes[nNodes - 1] == Root );
    for ( i = 0; i < nNodes; i++ ) p->pFlowIndex[Nodes[i]] = i;
    for ( i = 0; i < nNodes; i++ )
    {
        Id = Nodes[i];
        for ( k = 0; k < pCut->nLeaves; k++ )
            if ( Id == pCut->Leaves[k] ) break;
        if ( k < pCut->nLeaves )
        {
            Values[i] = Vars[k];
            Known |= ( (word)1 ) << i;
            continue;
        }
        Obj = Gia_ManObj( p->pGia, Id );
        if ( !Gia_ObjIsAnd( Obj ) ) continue;
        Id0 = Gia_ObjFaninId0( Obj, Id );
        Id1 = Gia_ObjFaninId1( Obj, Id );
        t0 = t1 = 0;
        if ( Id0 )
        {
            if ( p->pLevelStamp[Id0] != Root ) continue;
            k = p->pFlowIndex[Id0];
            if ( !( Known & ( ( (word)1 ) << k ) ) ) continue;
            t0 = Values[k];
        }
        if ( Id1 )
        {
            if ( p->pLevelStamp[Id1] != Root ) continue;
            k = p->pFlowIndex[Id1];
            if ( !( Known & ( ( (word)1 ) << k ) ) ) continue;
            t1 = Values[k];
        }
        if ( Gia_ObjFaninC0( Obj ) ) t0 = ~t0;
        if ( Gia_ObjFaninC1( Obj ) ) t1 = ~t1;
        if ( Gia_ObjIsMux( p->pGia, Obj ) )
        {
            Id2 = Gia_ObjFaninId2( p->pGia, Id );
            t2 = 0;
            if ( Id2 )
            {
                if ( p->pLevelStamp[Id2] != Root ) continue;
                k = p->pFlowIndex[Id2];
                if ( !( Known & ( ( (word)1 ) << k ) ) ) continue;
                t2 = Values[k];
            }
            if ( Gia_ObjFaninC2( p->pGia, Obj ) ) t2 = ~t2;
            Values[i] = ( t2 & t1 ) | ( ~t2 & t0 );
        }
        else
            Values[i] = Gia_ObjIsXor( Obj ) ? t0 ^ t1 : t0 & t1;
        Known |= ( (word)1 ) << i;
    }
    if ( !( Known & ( ( (word)1 ) << ( nNodes - 1 ) ) ) ) return 0;
    pCut->Truth = Values[nNodes - 1];
    return 1;
}

/**Function*************************************************************

  Synopsis    [Repairs a missed timing bound using a small minimum cut.]

  Description [Nodes at the latest fanin level are contracted into the source.
  Lower-level nodes have unit vertex capacity. Boundary nodes use one vertex
  with a unit edge to the sink, leaving more room in the one-word graph.
  Search stops above K flow or the bounded window size; this does not guarantee
  global depth optimality. Repaired truth cuts are evaluated in the same window.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_TryLevelCut( If2_Man_t * p, int Root )
{
    Gia_Obj_t *Obj = Gia_ManObj( p->pGia, Root ), *Node;
    If2_Cut_t Cut, Old[4], *Best = If2_ObjBest( p, Root );
    word Adj[64], Fixed[64], Seen, Queue, Bits, Mask;
    int Parent[64], Nodes[64], Id, Id0, Id1, Id2, i, j, k, nNodes = 0, nVerts = 2, Flow = 0, u, v;
    int nCuts, nPalette, Leaf, nNew;
    int * Palette = p->pBankLeaves ? p->pBankLeaves + (size_t)Root * p->pPars->nCutsMax * 6 : NULL;
    word * Masks = p->pBankMasks ? p->pBankMasks + (size_t)Root * p->pPars->nCutsMax : NULL;
    float Bound = Abc_MaxFloat( If2_ObjBest( p, Gia_ObjFaninId0( Obj, Root ) )->Delay,
                                If2_ObjBest( p, Gia_ObjFaninId1( Obj, Root ) )->Delay );
    if ( Gia_ObjIsMux( p->pGia, Obj ) )
        Bound = Abc_MaxFloat( Bound, If2_ObjBest( p, Gia_ObjFaninId2( p->pGia, Root ) )->Delay );
    if ( Bound < 1 || Best->Delay <= Bound + IF2_EPSILON ) return;
    memset( Adj, 0, sizeof( Adj ) );
    memset( Fixed, 0, sizeof( Fixed ) );
    Vec_IntClear( p->vStack );
    Vec_IntPush( p->vStack, Root );
    while ( Vec_IntSize( p->vStack ) )
    {
        Id = Vec_IntEntryLast( p->vStack );
        if ( p->pLevelStamp[Id] == Root )
        {
            Vec_IntPop( p->vStack );
            continue;
        }
        Node = Gia_ManObj( p->pGia, Id );
        if ( Gia_ObjIsAnd( Node ) && ( Id == Root || If2_ObjBest( p, Id )->Delay >= Bound - 1 - IF2_EPSILON ) )
        {
            Id0 = Gia_ObjFaninId0( Node, Id );
            Id1 = Gia_ObjFaninId1( Node, Id );
            if ( Id0 && p->pLevelStamp[Id0] != Root )
            {
                Vec_IntPush( p->vStack, Id0 );
                continue;
            }
            if ( Id1 && p->pLevelStamp[Id1] != Root )
            {
                Vec_IntPush( p->vStack, Id1 );
                continue;
            }
            Id2 = Gia_ObjFaninId2( p->pGia, Id );
            if ( Id2 > 0 && p->pLevelStamp[Id2] != Root )
            {
                Vec_IntPush( p->vStack, Id2 );
                continue;
            }
        }
        if ( nNodes == 64 ) return;
        p->pLevelStamp[Id] = Root;
        Nodes[nNodes++] = Id;
        if ( If2_ObjBest( p, Id )->Delay < Bound - IF2_EPSILON )
        {
            nNew = !Gia_ObjIsAnd( Node ) || If2_ObjBest( p, Id )->Delay < Bound - 1 - IF2_EPSILON ? 1 : 2;
            if ( nVerts + nNew > 64 ) return;
            p->pFlowIndex[Id] = nVerts;
            nVerts += nNew;
        }
        else
            p->pFlowIndex[Id] = 0;
        Vec_IntPop( p->vStack );
    }
    for ( i = 0; i < nNodes; i++ )
    {
        Id = Nodes[i];
        Node = Gia_ManObj( p->pGia, Id );
        u = p->pFlowIndex[Id];
        if ( !Gia_ObjIsAnd( Node ) || If2_ObjBest( p, Id )->Delay < Bound - 1 - IF2_EPSILON )
            Adj[u] = 2; // Boundary node's unit-capacity edge to the sink.
        else
        {
            if ( u ) Adj[u] = ( (word)1 ) << ( u + 1 );
            Id0 = Gia_ObjFaninId0( Node, Id );
            Id1 = Gia_ObjFaninId1( Node, Id );
            if ( Id0 && p->pFlowIndex[Id0] ) Fixed[u ? u + 1 : 0] |= ( (word)1 ) << p->pFlowIndex[Id0];
            if ( Id1 && p->pFlowIndex[Id1] ) Fixed[u ? u + 1 : 0] |= ( (word)1 ) << p->pFlowIndex[Id1];
            Id2 = Gia_ObjFaninId2( p->pGia, Id );
            if ( Id2 > 0 && p->pFlowIndex[Id2] ) Fixed[u ? u + 1 : 0] |= ( (word)1 ) << p->pFlowIndex[Id2];
        }
    }
    for ( i = 0; i < nVerts; i++ ) Adj[i] |= Fixed[i];
    for ( ;; )
    {
        Seen = Queue = 1;
        while ( Queue && !( Seen & 2 ) )
        {
            u = If2_FirstBit( Queue );
            Queue &= Queue - 1;
            Bits = Adj[u] & ~Seen;
            Seen |= Bits;
            Queue |= Bits;
            for ( ; Bits; Bits &= Bits - 1 ) Parent[If2_FirstBit( Bits )] = u;
        }
        if ( !( Seen & 2 ) ) break;
        if ( ++Flow > p->pPars->nLutSize ) return;
        for ( v = 1; v; v = u )
        {
            u = Parent[v];
            if ( !( Fixed[u] & ( ( (word)1 ) << v ) ) ) Adj[u] &= ~( ( (word)1 ) << v );
            Adj[v] |= ( (word)1 ) << u;
        }
    }
    memset( &Cut, 0, sizeof( Cut ) );
    for ( i = 0; i < nNodes; i++ )
    {
        Id = Nodes[i];
        u = p->pFlowIndex[Id];
        Node = Gia_ManObj( p->pGia, Id );
        v = !Gia_ObjIsAnd( Node ) || If2_ObjBest( p, Id )->Delay < Bound - 1 - IF2_EPSILON ? 1 : u + 1;
        if ( !u || !( Seen & ( ( (word)1 ) << u ) ) || ( Seen & ( ( (word)1 ) << v ) ) ) continue;
        assert( Cut.nLeaves < p->pPars->nLutSize );
        for ( j = Cut.nLeaves++; j && Cut.Leaves[j - 1] > Id; j-- ) Cut.Leaves[j] = Cut.Leaves[j - 1];
        Cut.Leaves[j] = Id;
        Cut.Sign |= If2_LeafSign( Id );
    }
    assert( Cut.nLeaves == Flow );
    If2_CutScore( p, &Cut );
    assert( Cut.Delay <= Bound + IF2_EPSILON );
    if ( p->fTruth )
    {
        If2_Cut_t * Cuts = If2_ObjCuts( p, Root );
        if ( !If2_LevelCutTruth( p, Root, &Cut, Nodes, nNodes ) ) return;
        nCuts = Abc_MinInt( p->pCounts[Root], p->pPars->nCutsMax - 1 );
        memmove( Cuts + 1, Cuts, sizeof( If2_Cut_t ) * nCuts );
        Cuts[0] = *Best = Cut;
        p->pCounts[Root] = (unsigned char)( nCuts + 1 );
        return;
    }
    nCuts = Abc_MinInt( p->pCounts[Root], p->Limit - 1 );
    for ( i = 0; i < nCuts; i++ )
    {
        Old[i].nLeaves = 0;
        for ( Bits = Masks[i]; Bits; Bits &= Bits - 1 ) Old[i].Leaves[Old[i].nLeaves++] = Palette[If2_FirstBit( Bits )];
    }
    *Best = Cut;
    nPalette = 0;
    for ( i = 0; i <= nCuts; i++ )
    {
        If2_Cut_t * C = i ? Old + i - 1 : &Cut;
        for ( j = 0; j < C->nLeaves; j++ )
        {
            Leaf = C->Leaves[j];
            for ( k = 0; k < nPalette && Palette[k] < Leaf; k++ )
            {
            }
            if ( k < nPalette && Palette[k] == Leaf ) continue;
            memmove( Palette + k + 1, Palette + k, sizeof( int ) * ( nPalette - k ) );
            Palette[k] = Leaf;
            nPalette++;
        }
    }
    for ( i = 0; i <= nCuts; i++ )
    {
        If2_Cut_t * C = i ? Old + i - 1 : &Cut;
        Mask = 0;
        for ( j = k = 0; j < C->nLeaves; j++ )
        {
            while ( Palette[k] != C->Leaves[j] ) k++;
            Mask |= ( (word)1 ) << k;
        }
        Masks[i] = Mask;
    }
    p->pCounts[Root] = (unsigned char)( nCuts + 1 );
    p->pBankSize[Root] = (unsigned char)nPalette;
}

/**Function*************************************************************

  Synopsis    [Recovers area from outputs toward the inputs.]

  Description [Only referenced roots need a new exact-area search. Selected cuts tighten
  their leaf requirements before those leaves are visited. Refresh all arrivals
  afterward, including inactive cuts needed by a later recovery round.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ReverseArea( If2_Man_t * p )
{
    Gia_Obj_t * Obj;
    If2_Cut_t * Cut;
    int i, j, Id, Count = 0;
    float Bound, Delay;
    Gia_ManForEachAndReverse ( p->pGia, Obj, i )
    {
        if ( !p->pRefs[i] ) continue;
        if ( Gia_ObjIsMuxId( p->pGia, i ) )
            If2_ObjMapMux( p, i );
        else
            If2_ObjMap( p, i );
        Count++;
        Cut = If2_ObjBest( p, i );
        Bound = p->pRequired[i] - (float)( Cut->nLeaves > 1 );
        for ( j = 0; j < Cut->nLeaves; j++ )
        {
            Id = Cut->Leaves[j];
            assert( Id < i );
            p->pRequired[Id] = Abc_MinFloat( p->pRequired[Id], Bound );
        }
    }
    // Lower nodes may use available slack. Recompute exact arrivals once.
    Gia_ManForEachAnd ( p->pGia, Obj, i )
    {
        Cut = If2_ObjBest( p, i );
        Delay = 0;
        for ( j = 0; j < Cut->nLeaves; j++ ) Delay = Abc_MaxFloat( Delay, If2_ObjBest( p, Cut->Leaves[j] )->Delay );
        Cut->Delay = Delay + (float)( Cut->nLeaves > 1 );
        assert( !p->pRefs[i] || p->pPars->fArea || Cut->Delay <= p->pRequired[i] + IF2_EPSILON );
    }
    if ( p->pPars->fVerbose ) Abc_Print( 1, "If2 reverse area: %d selected nodes\n", Count );
}

/**Function*************************************************************

  Synopsis    [Performs one delay, seed, flow or exact-area round.]

  Description [Choice graphs use reverse exact-area recovery when timing boxes permit it.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ManRound( If2_Man_t * p, int Mode )
{
    Gia_Obj_t * pObj;
    int i, Id, iCi;
    abctime clk = Abc_Clock();
    p->Mode = Mode;
    p->Limit =
        ( Mode == 1 || ( Mode == 3 && p->pPars->nLutSize <= 4 ) ) ? p->pPars->nCutsMax : Abc_MinInt( 2, p->pPars->nCutsMax );
    if ( Mode == 3 )
    {
        memcpy( p->pRefs, p->pOrigRefs, sizeof( int ) * Gia_ManObjNum( p->pGia ) );
        for ( i = 0; i < Gia_ManObjNum( p->pGia ); i++ )
        {
            p->pEstRefs[i] = p->pChoiceRefs ? Abc_MaxFloat( 1.0f, p->pChoiceRefs[i] ) : (float)Abc_MaxInt( 1, p->pRefs[i] );
            p->pInvRefs[i] = 1.0f / p->pEstRefs[i];
        }
    }
    if ( p->pTim ) Tim_ManIncrementTravId( p->pTim );
    if ( Mode == 2 && Gia_ManHasChoices( p->pGia ) && !p->pTim && !Gia_ManBufNum( p->pGia ) )
        If2_ReverseArea( p );
    else
        Gia_ManForEachObj1 ( p->pGia, pObj, i )
        {
            if ( Gia_ObjIsCi( pObj ) )
            {
                iCi = Gia_ObjCioId( pObj );
                if ( p->pTim ) If2_ObjBest( p, i )->Delay = Tim_ManGetCiArrival( p->pTim, iCi );
            }
            else if ( Gia_ObjIsCo( pObj ) )
            {
                if ( p->pTim )
                    Tim_ManSetCoArrival( p->pTim, Gia_ObjCioId( pObj ),
                                         If2_ObjBest( p, Gia_ObjFaninId0( pObj, i ) )->Delay );
            }
            else if ( !p->pGia->fGiaSimple && Gia_ObjIsBuf( pObj ) )
            {
                p->fExact = 0;
                Id = Gia_ObjFaninId0( pObj, i );
                If2_CutUnit( If2_ObjBest( p, i ), Id );
                if ( Gia_ObjFaninC0( pObj ) ) If2_ObjBest( p, i )->Truth = ~If2_ObjBest( p, i )->Truth;
                If2_CutScore( p, If2_ObjBest( p, i ) );
                p->pCounts[i] = 1;
                if ( p->pCuts )
                    *If2_ObjCuts( p, i ) = *If2_ObjBest( p, i );
                else
                {
                    p->pBankSize[i] = (unsigned char)( Id > 0 );
                    p->pBankLeaves[(size_t)i * p->pPars->nCutsMax * 6] = Id;
                    p->pBankMasks[(size_t)i * p->pPars->nCutsMax] = Id > 0;
                }
            }
            else if ( p->pSkip[i] )
            {
                assert( p->pRefs[i] == 0 );
            }
            else if ( Gia_ObjIsMuxId( p->pGia, i ) )
                If2_ObjMapMux( p, i );
            else if ( p->pGroupOffset[i] )
                If2_ObjMapGroup( p, i );
            else if ( !p->fTruth && p->pPars->nCutsMax <= 4 )
                If2_ObjMapBits( p, i );
            else
                If2_ObjMap( p, i );
            if ( Mode == 0 && !p->pPars->fArea && !p->pTim && !p->pGia->vInArrs && !p->pGia->vCiArrs && !Gia_ManBufNum( p->pGia ) &&
                 p->pPars->nCutsMax <= 4 && Gia_ObjIsAnd( pObj ) )
                If2_TryLevelCut( p, i );
        }
    If2_ManRequired( p );
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "If2 %s %d: LUT = %d  Edge = %d  Delay = %.2f  Time = %.3f sec\n",
                   Mode == 2 ? "area" : ( Mode == 3 ? "seed" : ( Mode ? "flow" : "delay" ) ), p->Round, p->pPars->Area,
                   p->pPars->Edge, p->pPars->Delay, 1.0 * ( Abc_Clock() - clk ) / CLOCKS_PER_SEC );
    p->Round++;
}

/**Function*************************************************************

  Synopsis    [Computes selected functions when structural export is unavailable.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ManSelectedTruth( If2_Man_t * p )
{
    static const word Vars[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    word * pTruth = ABC_ALLOC( word, Gia_ManObjNum(p->pGia) );
    int * pStamp = ABC_CALLOC( int, Gia_ManObjNum(p->pGia) );
    Gia_Obj_t * pObj;
    int i, k, Id, Id0, Id1;
    pTruth[0] = 0;
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        If2_Cut_t * pCut;
        if ( !p->pRefs[i] ) continue;
        pCut = If2_ObjBest(p, i);
        pStamp[0] = i;
        for ( k = 0; k < pCut->nLeaves; k++ )
        {
            Id = pCut->Leaves[k];
            pStamp[Id] = i;
            pTruth[Id] = Vars[k];
        }
        Vec_IntClear(p->vStack);
        Vec_IntPush(p->vStack, i);
        while ( Vec_IntSize(p->vStack) )
        {
            Id = Vec_IntEntryLast(p->vStack);
            if ( pStamp[Id] == i ) { Vec_IntPop(p->vStack); continue; }
            pObj = Gia_ManObj(p->pGia, Id);
            assert( Gia_ObjIsAnd(pObj) );
            Id0 = Gia_ObjFaninId0(pObj, Id);
            Id1 = Gia_ObjFaninId1(pObj, Id);
            if ( pStamp[Id0] != i ) { Vec_IntPush(p->vStack, Id0); continue; }
            if ( pStamp[Id1] != i ) { Vec_IntPush(p->vStack, Id1); continue; }
            {
                word t0 = Gia_ObjFaninC0(pObj) ? ~pTruth[Id0] : pTruth[Id0];
                word t1 = Gia_ObjFaninC1(pObj) ? ~pTruth[Id1] : pTruth[Id1];
                pTruth[Id] = (!p->pGia->fGiaSimple && Gia_ObjIsBuf(pObj)) ? t0 : Gia_ObjIsXor(pObj) ? t0 ^ t1 : t0 & t1;
            }
            pStamp[Id] = i;
            Vec_IntPop(p->vStack);
        }
        pCut->Truth = pTruth[i];
    }
    ABC_FREE(pTruth);
    ABC_FREE(pStamp);
}

/**Function*************************************************************

  Synopsis    [Restores CI and CO vector order after structural duplication.]

  Description [Object order need not match interface order, even for normalized GIAs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ManOrderInterface( Gia_Man_t * pNew, Gia_Man_t * pOld )
{
    Gia_Obj_t * Obj;
    int i, Id;
    Gia_ManForEachCi(pOld, Obj, i)
    {
        Id = Abc_Lit2Var(Obj->Value);
        Vec_IntWriteEntry(pNew->vCis, i, Id);
        Gia_ObjSetCioId(Gia_ManObj(pNew, Id), i);
    }
    Gia_ManForEachCo(pOld, Obj, i)
    {
        Id = Abc_Lit2Var(Obj->Value);
        Vec_IntWriteEntry(pNew->vCos, i, Id);
        Gia_ObjSetCioId(Gia_ManObj(pNew, Id), i);
    }
}

/**Function*************************************************************

  Synopsis    [Attaches selected structural cuts to an AIG copy.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If2_ManExportStructural( If2_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vMap;
    int i, k;
    if ( Gia_ManBufNum(p->pGia) ) return NULL;
    Gia_ManForEachAnd(p->pGia, pObj, i)
        if ( p->pRefs[i] && If2_ObjBest(p, i)->nLeaves < 2 ) return NULL;
    if ( Gia_ManXorNum(p->pGia) || p->pGia->fGiaSimple )
    {
        pNew = Gia_ManStart(Gia_ManObjNum(p->pGia)+2*Gia_ManXorNum(p->pGia));
        pNew->fGiaSimple = p->pGia->fGiaSimple;
        pNew->pName = Abc_UtilStrsav(p->pGia->pName);
        pNew->pSpec = Abc_UtilStrsav(p->pGia->pSpec);
        Gia_ManConst0(p->pGia)->Value = 0;
        Gia_ManForEachObj1(p->pGia, pObj, i)
            if ( Gia_ObjIsCi(pObj) ) pObj->Value = Gia_ManAppendCi(pNew);
            else if ( Gia_ObjIsCo(pObj) ) pObj->Value = Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj));
            else if ( Gia_ObjIsXor(pObj) ) pObj->Value = Gia_ManAppendXor(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
            else pObj->Value = Gia_ManAppendAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
        Gia_ManSetRegNum(pNew, Gia_ManRegNum(p->pGia));
    }
    else pNew = Gia_ManDup(p->pGia);
    If2_ManOrderInterface(pNew, p->pGia);
    Vec_IntFreeP(&pNew->vMapping);
    vMap = Vec_IntAlloc(Gia_ManObjNum(pNew) + (int)p->pPars->Edge + 2*(int)p->pPars->Area);
    Vec_IntFill(vMap, Gia_ManObjNum(pNew), 0);
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        If2_Cut_t * pCut = If2_ObjBest(p, i);
        if ( !p->pRefs[i] ) continue;
        Vec_IntWriteEntry(vMap, Abc_Lit2Var(pObj->Value), Vec_IntSize(vMap));
        Vec_IntPush(vMap, pCut->nLeaves);
        for ( k = 0; k < pCut->nLeaves; k++ ) Vec_IntPush(vMap, Abc_Lit2Var(Gia_ManObj(p->pGia, pCut->Leaves[k])->Value));
        Vec_IntPush(vMap, Abc_Lit2Var(pObj->Value));
    }
    pNew->vMapping = vMap;
    pNew->MappedArea = p->pPars->Area;
    pNew->MappedDelay = (int)p->pPars->Delay;
    Gia_ManMappingVerify(pNew);
    return pNew;
}

enum { IF2_RECIPE_BINS = 4096, IF2_RECIPE_LIMIT = IF2_RECIPE_BINS / 2 };

typedef struct If2_Recipe_t_ If2_Recipe_t;
struct If2_Recipe_t_
{
    word            Truth;
    Kit_Graph_t *   pGraph;
    int             nLeaves;
};

/**Function*************************************************************

  Synopsis    [Releases the bounded cache of factored LUT functions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_RecipeClear( If2_Recipe_t * pRecipes )
{
    int i;
    for ( i = 0; i < IF2_RECIPE_BINS; i++ )
        if ( pRecipes[i].pGraph ) Kit_GraphFree( pRecipes[i].pGraph );
    memset( pRecipes, 0, sizeof(If2_Recipe_t) * IF2_RECIPE_BINS );
}

/**Function*************************************************************

  Synopsis    [Reuses the same deterministic factorization for identical LUTs.]

  Description [The cache belongs to one export. Graph realization overwrites all
  leaf and internal literals, so cached graphs never retain input-specific state.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Kit_Graph_t * If2_RecipeFind( If2_Recipe_t * pRecipes, int * pnRecipes, word Truth, int nLeaves, Vec_Int_t * vCover )
{
    unsigned Words[2];
    int Home = (int)(((Truth ^ (Truth >> 32)) * ABC_CONST(0x9e3779b97f4a7c15) + nLeaves) & (IF2_RECIPE_BINS - 1));
    int Bin = Home;
    while ( pRecipes[Bin].pGraph )
    {
        if ( pRecipes[Bin].Truth == Truth && pRecipes[Bin].nLeaves == nLeaves )
            return pRecipes[Bin].pGraph;
        Bin = (Bin + 1) & (IF2_RECIPE_BINS - 1);
    }
    if ( *pnRecipes == IF2_RECIPE_LIMIT )
    {
        If2_RecipeClear( pRecipes );
        *pnRecipes = 0;
        Bin = Home;
    }
    Words[0] = (unsigned)Truth;
    Words[1] = (unsigned)(Truth >> 32);
    pRecipes[Bin].Truth = Truth;
    pRecipes[Bin].nLeaves = nLeaves;
    pRecipes[Bin].pGraph = Kit_TruthToGraph( Words, nLeaves, vCover );
    *pnRecipes += pRecipes[Bin].pGraph != NULL;
    return pRecipes[Bin].pGraph;
}

/**Function*************************************************************

  Synopsis    [Realizes selected functional cuts and attaches LUT mapping.]

  Description [Minimized supports and choice cuts need not be structural cuts of the
  input AIG. Their truth tables define the resulting logic.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If2_ManExport( If2_Man_t * p )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vCopies = Vec_IntStartFull( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vOffsets = Vec_IntAlloc( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vMapping = Vec_IntStart( 1 );
    Vec_Int_t * vLeaves = Vec_IntAlloc( IF2_LEAF_MAX );
    Vec_Int_t * vCover = Vec_IntAlloc( 1024 );
    Gia_Obj_t * pObj;
    If2_Cut_t * pCut;
    If2_Recipe_t * pRecipes = ABC_CALLOC( If2_Recipe_t, IF2_RECIPE_BINS );
    Kit_Graph_t * pGraph;
    int i, k, Lit, LeafLit, Root, nRecipes = 0;
    pNew->pName = Abc_UtilStrsav( p->pGia->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pGia->pSpec );
    Vec_IntWriteEntry( vCopies, 0, 0 );
    Gia_ManForEachObj1( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            Vec_IntWriteEntry( vCopies, i, pObj->Value = Gia_ManAppendCi(pNew) );
        else if ( Gia_ObjIsCo(pObj) )
        {
            Lit = Vec_IntEntry( vCopies, Gia_ObjFaninId0(pObj, i) );
            assert( Lit >= 0 );
            pObj->Value = Gia_ManAppendCo( pNew, Abc_LitNotCond(Lit, Gia_ObjFaninC0(pObj)) );
        }
        else if ( p->pRefs[i] )
        {
            pCut = If2_ObjBest( p, i );
            if ( pCut->nLeaves == 0 )
                Lit = (int)(pCut->Truth & 1);
            else if ( pCut->nLeaves == 1 && (pCut->Truth == ABC_CONST(0xAAAAAAAAAAAAAAAA) || pCut->Truth == ABC_CONST(0x5555555555555555)) )
                Lit = Abc_LitNotCond( Vec_IntEntry(vCopies, pCut->Leaves[0]), (int)(pCut->Truth & 1) );
            else
            {
                Vec_IntClear( vLeaves );
                for ( k = 0; k < pCut->nLeaves; k++ )
                {
                    LeafLit = Vec_IntEntry( vCopies, pCut->Leaves[k] );
                    assert( LeafLit >= 0 );
                    Vec_IntPush( vLeaves, LeafLit );
                }
                pGraph = If2_RecipeFind( pRecipes, &nRecipes, pCut->Truth, pCut->nLeaves, vCover );
                if ( pGraph == NULL )
                {
                    Abc_Print( -1, "&if2: factoring a selected LUT failed.\n" );
                    Gia_ManStop( pNew );
                    pNew = NULL;
                    Vec_IntFree( vOffsets );
                    goto cleanup;
                }
                Lit = Kit_GraphToGia( pNew, pGraph, vLeaves, 0 );
                Root = Abc_Lit2Var( Lit );
                if ( Root && Gia_ObjIsAnd(Gia_ManObj(pNew, Root)) )
                {
                    for ( k = 0; k < Vec_IntSize(vLeaves); k++ )
                        if ( Root == Abc_Lit2Var(Vec_IntEntry(vLeaves, k)) ) break;
                    if ( k == Vec_IntSize(vLeaves) )
                    {
                        Vec_IntSetEntry( vOffsets, Root, Vec_IntSize(vMapping) );
                        Vec_IntPush( vMapping, pCut->nLeaves );
                        for ( k = 0; k < pCut->nLeaves; k++ )
                            Vec_IntPush( vMapping, Abc_Lit2Var(Vec_IntEntry(vLeaves, k)) );
                        Vec_IntPush( vMapping, Root );
                    }
                }
            }
            Vec_IntWriteEntry( vCopies, i, Lit );
        }
    }
    If2_ManOrderInterface(pNew, p->pGia);
    Vec_IntFillExtra( vOffsets, Gia_ManObjNum(pNew), 0 );
    Vec_IntForEachEntry( vOffsets, Root, i )
        if ( Root ) Vec_IntAddToEntry( vOffsets, i, Gia_ManObjNum(pNew) );
    Vec_IntAppend( vOffsets, vMapping );
    pNew->vMapping = vOffsets;
    pNew->MappedArea = p->pPars->Area;
    pNew->MappedDelay = (int)p->pPars->Delay;
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p->pGia) );
cleanup:
    If2_RecipeClear( pRecipes );
    ABC_FREE( pRecipes );
    Vec_IntFree( vCopies );
    Vec_IntFree( vMapping );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vCover );
    if ( pNew ) Gia_ManMappingVerify( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Substitutes one LUT function into a selected cut.]

  Description [The merged support must fit the LUT bound. Cofactor composition preserves
  the root function and permits final support minimization.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If2_ComposeLeaf( If2_Man_t * p, If2_Cut_t * Root, int Pos, If2_Cut_t * Child, If2_Cut_t * Res )
{
    If2_Cut_t Base = *Root;
    word Zero = Abc_Tt6Cofactor0( Root->Truth, Pos ), One = Abc_Tt6Cofactor1( Root->Truth, Pos ), Select;
    unsigned M0, M1;
    int j;
    Base.nLeaves--;
    Base.Sign = 0;
    for ( j = Pos; j < Base.nLeaves; j++ ) Base.Leaves[j] = Base.Leaves[j + 1];
    for ( j = 0; j < Base.nLeaves; j++ ) Base.Sign |= If2_LeafSign( Base.Leaves[j] );
    if ( !If2_CutMerge( p, &Base, Child, Res ) ) return 0;
    for ( j = Pos; j < 5; j++ )
    {
        Zero = Abc_Tt6SwapVars( Zero, j, j + 1 );
        One = Abc_Tt6SwapVars( One, j, j + 1 );
    }
    M0 = (unsigned)Res->Truth & 63;
    M1 = (unsigned)( Res->Truth >> 6 );
    Zero = If2_Stretch( Zero, M0 );
    One = If2_Stretch( One, M0 );
    Select = If2_Stretch( Child->Truth, M1 );
    Res->Truth = ( Zero & ~Select ) | ( One & Select );
    Res->nLeaves = Abc_Tt6MinBase( &Res->Truth, Res->Leaves, Res->nLeaves );
    // Keep referenced LUT roots distinct from their leaves and the constant.
    if ( Res->nLeaves < 2 ) return 0;
    Res->Sign = 0;
    for ( j = 0; j < Res->nLeaves; j++ ) Res->Sign |= If2_LeafSign( Res->Leaves[j] );
    return 1;
}
/**Function*************************************************************

  Synopsis    [Removes redundant LUT boundaries after exact-area recovery.]

  Description [Accept strictly smaller area, or equal area with lower delay. Each root
  has a fixed iteration bound, and no accepted cut increases its arrival.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_InlineCover( If2_Man_t * p )
{
    Gia_Obj_t * Obj;
    If2_Cut_t Old, Best, Cut, *Child, *Current;
    int Id, i, k, Iter, Count = 0, Trials = 0;
    float Area, Edge;
    if ( !p->fTruth || !Gia_ManHasChoices( p->pGia ) || p->pTim ) return;
    p->Mode = 2;
    Gia_ManForEachAnd ( p->pGia, Obj, Id )
    {
        if ( !p->pRefs[Id] ) continue;
        Current = If2_ObjBest( p, Id );
        for ( Iter = 0; Iter < 4; Iter++ )
        {
            Old = *Current;
            If2_CutDeref( p, &Old );
            p->fExact = 1;
            Best = Old;
            If2_CutScore( p, &Best );
            for ( i = 0; i < Old.nLeaves; i++ )
            {
                int Leaf = Old.Leaves[i];
                if ( !If2_ObjIsNode( p, Leaf ) ) continue;
                for ( k = 0; k < p->pPars->nCutsMax + 1; k++ )
                {
                    if ( k && k > p->pCounts[Leaf] ) break;
                    Child = k ? If2_ObjCuts( p, Leaf ) + k - 1 : If2_ObjBest( p, Leaf );
                    if ( !If2_ComposeLeaf( p, &Old, i, Child, &Cut ) ) continue;
                    Trials++;
                    If2_CutScore( p, &Cut );
                    if ( Cut.Delay > Old.Delay + IF2_EPSILON ) continue;
                    if ( Cut.Flow < Best.Flow - IF2_EPSILON ||
                         ( Cut.Flow == Best.Flow && Cut.Delay < Best.Delay - IF2_EPSILON ) )
                        Best = Cut;
                }
            }
            *Current = Best;
            If2_CutRef( p, Current, 0, &Area, &Edge );
            if ( Current->nLeaves == Old.nLeaves && !memcmp( Current->Leaves, Old.Leaves, Old.nLeaves * sizeof( int ) ) )
                break;
            Count++;
        }
    }
    If2_ManRequired( p );
    if ( p->pPars->fVerbose ) Abc_Print( 1, "If2 cover composition: %d accepted, %d trials\n", Count, Trials );
}

/**Function*************************************************************

  Synopsis    [Maps a topologically ordered GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If2_ManPerformMappingCore( Gia_Man_t * pGia, If2_Par_t * pPars )
{
    If2_Man_t Man, *p = &Man;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, k, nObjs = Gia_ManObjNum( pGia );
    abctime clk = Abc_Clock(), clkExport;
    // Box ordering can create a fresh GIA without the original choice phases.
    if ( Gia_ManHasChoices( pGia ) ) Gia_ManSetPhase( pGia );
    memset( p, 0, sizeof( If2_Man_t ) );
    p->pGia = pGia;
    p->pPars = pPars;
    p->fChoices = Gia_ManHasChoices( pGia );
    p->fTruth = pPars->fCutMin || Gia_ManHasChoices( pGia ) || Gia_ManMuxNum( pGia );
    p->pTim = pGia->pManTime ? Tim_ManDup( (Tim_Man_t *)pGia->pManTime, 0 ) : NULL;
    p->pCuts = p->fTruth || pPars->nCutsMax > 4 ? ABC_ALLOC( If2_Cut_t, (size_t)nObjs * pPars->nCutsMax ) : NULL;
    p->pBest = ABC_ALLOC( If2_Cut_t, nObjs );
    p->pCounts = ABC_CALLOC( unsigned char, nObjs );
    p->pLocalMask = p->pCuts ? NULL : ABC_CALLOC( word, nObjs );
    p->pAreaSeen = p->pCuts ? NULL : ABC_CALLOC( unsigned char, nObjs );
    p->pLevelStamp = ABC_CALLOC( int, nObjs );
    p->pFlowIndex = ABC_ALLOC( int, nObjs );
    p->pSkip = ABC_CALLOC( unsigned char, nObjs );
    p->pGroupOffset = ABC_CALLOC( int, nObjs );
    p->vGroupInputs = Vec_IntStart( 1 );
    p->pBankLeaves = p->pCuts ? NULL : ABC_ALLOC( int, (size_t)nObjs * pPars->nCutsMax * 6 );
    p->pBankMasks = p->pCuts ? NULL : ABC_ALLOC( word, (size_t)nObjs * pPars->nCutsMax );
    p->pBankSize = p->pCuts ? NULL : ABC_CALLOC( unsigned char, nObjs );
    p->vAreaNodes = Vec_IntAlloc( 128 );
    p->pRefs = ABC_CALLOC( int, nObjs );
    p->pEstRefs = ABC_ALLOC( float, nObjs );
    p->pInvRefs = ABC_ALLOC( float, nObjs );
    p->pRequired = ABC_ALLOC( float, nObjs );
    p->pCoRequired = ABC_ALLOC( float, Gia_ManCoNum( pGia ) );
    p->vStack = Vec_IntAlloc( 128 );
    p->vUndo = Vec_IntAlloc( 128 );
    for ( i = 0; i < nObjs; i++ ) p->pRequired[i] = IF2_INFINITY;
    If2_CutUnit( If2_ObjBest( p, 0 ), 0 );
    p->pCounts[0] = 1;
    if ( p->pCuts )
        *If2_ObjCuts( p, 0 ) = *If2_ObjBest( p, 0 );
    else
        p->pBankMasks[0] = 0;
    Gia_ManForEachCi ( pGia, pObj, i )
    {
        k = Gia_ObjId( pGia, pObj );
        If2_CutUnit( If2_ObjBest( p, k ), k );
        p->pCounts[k] = 1;
        if ( p->pCuts )
            *If2_ObjCuts( p, k ) = *If2_ObjBest( p, k );
        else
        {
            p->pBankSize[k] = 1;
            p->pBankLeaves[(size_t)k * pPars->nCutsMax * 6] = k;
            p->pBankMasks[(size_t)k * pPars->nCutsMax] = 1;
        }
        if ( pGia->vCiArrs )
            If2_ObjBest( p, k )->Delay = (float)Vec_IntEntry( pGia->vCiArrs, i );
        else if ( pGia->vInArrs )
            If2_ObjBest( p, k )->Delay = Vec_FltSize( pGia->vInArrs ) ? Vec_FltEntry( pGia->vInArrs, i ) : pGia->DefInArrs;
    }
    Gia_ManForEachObj1 ( pGia, pObj, i )
        if ( !Gia_ObjIsCi( pObj ) )
        {
            if ( Gia_ObjIsMux( pGia, pObj ) ) p->pRefs[Gia_ObjFaninId2( pGia, i )]++;
            p->pRefs[Gia_ObjFaninId0( pObj, i )]++;
            if ( Gia_ObjIsAnd( pObj ) && ( pGia->fGiaSimple || !Gia_ObjIsBuf( pObj ) ) )
                p->pRefs[Gia_ObjFaninId1( pObj, i )]++;
        }
    if ( Gia_ManHasChoices( pGia ) ) p->pChoiceRefs = Gia_ManChoiceRefs( pGia );
    for ( i = 0; i < nObjs; i++ )
    {
        p->pEstRefs[i] = p->pChoiceRefs ? Abc_MaxFloat( 1.0f, p->pChoiceRefs[i] ) : (float)Abc_MaxInt( 1, p->pRefs[i] );
        p->pInvRefs[i] = 1.0f / p->pEstRefs[i];
    }
    p->pOrigRefs = ABC_ALLOC( int, nObjs );
    memcpy( p->pOrigRefs, p->pRefs, sizeof( int ) * nObjs );
    If2_ManRound( p, 0 );
    If2_ManGroup( p );
    If2_ManRound( p, 3 );
    ABC_FREE( p->pChoiceRefs );
    for ( i = 0; i < pPars->nFlowIters; i++ ) If2_ManRound( p, 1 );
    for ( i = 0; i < pPars->nAreaIters; i++ ) If2_ManRound( p, 2 );
    if ( pPars->nAreaIters > 0 ) If2_InlineCover( p );
    clkExport = Abc_Clock();
    pNew = p->fTruth ? NULL : If2_ManExportStructural( p );
    if ( pNew == NULL )
    {
        if ( !p->fTruth ) If2_ManSelectedTruth( p );
        pNew = If2_ManExport( p );
    }
    if ( pPars->fVerbose )
        Abc_Print( 1,
                   "If2: pairs = %.0f  merges = %.0f  minimized = %.0f  trials = %.0f  ref visits = %.0f\nIf2: cut memory = "
                   "%.2f MB  mapping = %.3f sec  export = %.3f sec  total = %.3f sec\n",
                   p->nPairs, p->nMerged, p->nMinimized, p->nTrials, p->nRefVisits,
                   (double)nObjs *
                       ( sizeof( If2_Cut_t ) +
                         pPars->nCutsMax * ( 6 * sizeof( int ) + sizeof( word ) + ( p->pCuts ? sizeof( If2_Cut_t ) : 0 ) ) +
                         2 * sizeof( unsigned char ) ) /
                       ( 1 << 20 ),
                   1.0 * ( clkExport - clk ) / CLOCKS_PER_SEC, 1.0 * ( Abc_Clock() - clkExport ) / CLOCKS_PER_SEC,
                   1.0 * ( Abc_Clock() - clk ) / CLOCKS_PER_SEC );
    if ( p->pTim ) Tim_ManStop( p->pTim );
    ABC_FREE( p->pCuts );
    ABC_FREE( p->pBest );
    ABC_FREE( p->pCounts );
    ABC_FREE( p->pLocalMask );
    ABC_FREE( p->pAreaSeen );
    ABC_FREE( p->pLevelStamp );
    ABC_FREE( p->pFlowIndex );
    ABC_FREE( p->pSkip );
    ABC_FREE( p->pGroupOffset );
    Vec_IntFree( p->vGroupInputs );
    ABC_FREE( p->pBankLeaves );
    ABC_FREE( p->pBankMasks );
    ABC_FREE( p->pBankSize );
    Vec_IntFree( p->vAreaNodes );
    ABC_FREE( p->pRefs );
    ABC_FREE( p->pOrigRefs );
    ABC_FREE( p->pChoiceRefs );
    ABC_FREE( p->pEstRefs );
    ABC_FREE( p->pInvRefs );
    ABC_FREE( p->pRequired );
    ABC_FREE( p->pCoRequired );
    Vec_IntFree( p->vStack );
    Vec_IntFree( p->vUndo );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Recognizes XORs and protected choice MUXes before mapping.]

  Description [Sibling edges are part of reachability. MUX interiors must be
  private and have no choices; shared XOR products remain available when used
  elsewhere. Ordinary inputs retain XOR-only recognition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If2_ManCoarsen( Gia_Man_t * p, int fMux )
{
    Gia_Man_t * New;
    Gia_Obj_t *Obj, *Fan0, *Fan1, *FanC;
    unsigned char * Needed = ABC_CALLOC( unsigned char, Gia_ManObjNum( p ) );
    int i, nObjs = 1 + Gia_ManCiNum( p ) + Gia_ManCoNum( p ), Lit0, Lit1, fPlain;
    int * Refs = fMux ? ABC_CALLOC( int, Gia_ManObjNum( p ) ) : NULL;
    if ( fMux )
        Gia_ManForEachObj1 ( p, Obj, i )
            if ( !Gia_ObjIsCi( Obj ) )
            {
                Refs[Gia_ObjFaninId0( Obj, i )]++;
                if ( Gia_ObjIsAnd( Obj ) ) Refs[Gia_ObjFaninId1( Obj, i )]++;
            }
    Gia_ManForEachObjReverse1 ( p, Obj, i )
    {
        if ( Gia_ObjIsCo( Obj ) )
            Needed[Gia_ObjFaninId0( Obj, i )] = 1;
        else if ( Gia_ObjIsAnd( Obj ) && Needed[i] )
        {
            if ( Gia_ObjSibl( p, i ) ) Needed[Gia_ObjSibl( p, i )] = 1;
            fPlain = !Gia_ObjIsXor(Obj) && !Gia_ObjIsXor(Gia_ObjFanin0(Obj)) && !Gia_ObjIsXor(Gia_ObjFanin1(Obj));
            if ( fPlain && ( !Gia_ObjSibl( p, Gia_ObjFaninId0( Obj, i ) ) && !Gia_ObjSibl( p, Gia_ObjFaninId1( Obj, i ) ) ) &&
                 Gia_ObjRecognizeExor( Obj, &Fan0, &Fan1 ) )
            {
                Needed[i] |= 2;
                Needed[Gia_ObjId( p, Gia_Regular( Fan0 ) )] = 1;
                Needed[Gia_ObjId( p, Gia_Regular( Fan1 ) )] = 1;
            }
            else if ( fPlain && fMux && Refs[Gia_ObjFaninId0( Obj, i )] == 1 && Refs[Gia_ObjFaninId1( Obj, i )] == 1 &&
                      !Gia_ObjSibl( p, Gia_ObjFaninId0( Obj, i ) ) && !Gia_ObjSibl( p, Gia_ObjFaninId1( Obj, i ) ) &&
                      Gia_ObjIsMuxType( Obj ) )
            {
                FanC = Gia_ObjRecognizeMux( Obj, &Fan1, &Fan0 );
                if ( Gia_Regular( FanC ) != Gia_Regular( Fan0 ) && Gia_Regular( FanC ) != Gia_Regular( Fan1 ) &&
                     Gia_Regular( Fan0 ) != Gia_Regular( Fan1 ) )
                {
                    Needed[i] |= 4;
                    Needed[Gia_ObjId( p, Gia_Regular( FanC ) )] = 1;
                    Needed[Gia_ObjId( p, Gia_Regular( Fan0 ) )] = 1;
                    Needed[Gia_ObjId( p, Gia_Regular( Fan1 ) )] = 1;
                }
                else
                {
                    Needed[Gia_ObjFaninId0( Obj, i )] = 1;
                    Needed[Gia_ObjFaninId1( Obj, i )] = 1;
                }
            }
            else
            {
                Needed[Gia_ObjFaninId0( Obj, i )] = 1;
                Needed[Gia_ObjFaninId1( Obj, i )] = 1;
            }
            nObjs++;
        }
    }
    New = Gia_ManStart( nObjs );
    New->pMuxes = ABC_CALLOC( unsigned, New->nObjsAlloc );
    if ( Gia_ManHasChoices( p ) ) New->pSibls = ABC_CALLOC( int, New->nObjsAlloc );
    New->pName = Abc_UtilStrsav( p->pName );
    New->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0( p )->Value = 0;
    Gia_ManForEachObj1 ( p, Obj, i )
    {
        if ( Gia_ObjIsCi( Obj ) )
            Obj->Value = Gia_ManAppendCi( New );
        else if ( Gia_ObjIsCo( Obj ) )
            Obj->Value = Gia_ManAppendCo( New, Gia_ObjFanin0Copy( Obj ) );
        else if ( !Needed[i] )
            continue;
        else if ( Gia_ObjIsXor(Obj) )
        {
            Lit0 = Gia_ObjFanin0Copy(Obj);
            Lit1 = Gia_ObjFanin1Copy(Obj);
            Obj->Value = Gia_ManAppendXorReal(New,Abc_LitRegular(Lit0),Abc_LitRegular(Lit1)) ^ ((Lit0 ^ Lit1) & 1);
        }
        else if ( Needed[i] & 2 )
        {
            Gia_ObjRecognizeExor( Obj, &Fan0, &Fan1 );
            Lit0 = Gia_Regular( Fan0 )->Value ^ Gia_IsComplement( Fan0 );
            Lit1 = Gia_Regular( Fan1 )->Value ^ Gia_IsComplement( Fan1 );
            Obj->Value = Gia_ManAppendXorReal( New, Lit0, Lit1 );
        }
        else if ( Needed[i] & 4 )
        {
            FanC = Gia_ObjRecognizeMux( Obj, &Fan1, &Fan0 );
            Obj->Value = Gia_ManAppendMuxReal( New, Gia_Regular( FanC )->Value ^ Gia_IsComplement( FanC ),
                                               Gia_Regular( Fan1 )->Value ^ Gia_IsComplement( Fan1 ),
                                               Gia_Regular( Fan0 )->Value ^ Gia_IsComplement( Fan0 ) );
        }
        else
            Obj->Value = Gia_ManAppendAnd( New, Gia_ObjFanin0Copy( Obj ), Gia_ObjFanin1Copy( Obj ) );
        if ( Gia_ObjIsAnd( Obj ) && Gia_ObjSibl( p, i ) )
        {
            int Sibl = Gia_ManObj( p, Gia_ObjSibl( p, i ) )->Value >> 1;
            assert( Sibl > 0 && Sibl < (int)( Obj->Value >> 1 ) );
            New->pSibls[Obj->Value >> 1] = Sibl;
        }
    }
    assert( Gia_ManObjNum( New ) == nObjs );
    Gia_ManSetRegNum( New, Gia_ManRegNum( p ) );
    If2_ManOrderInterface( New, p );
    ABC_FREE( Refs );
    ABC_FREE( Needed );
    return New;
}

/**Function*************************************************************

  Synopsis    [Uses temporary XOR recognition when metadata permits it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If2_ManPerformMappingInt( Gia_Man_t * pGia, If2_Par_t * pPars )
{
    Gia_Man_t * pCls, * pNew;
    if ( pGia->fGiaSimple || pGia->pManTime || pGia->vCiArrs || pGia->vInArrs || pGia->vCoReqs || pGia->vOutReqs || Gia_ManBufNum(pGia) )
        return If2_ManPerformMappingCore(pGia, pPars);
    pCls = If2_ManCoarsen(pGia, Gia_ManHasChoices(pGia) && pPars->nLutSize >= 3);
    pNew = If2_ManPerformMappingCore(pCls, pPars);
    Gia_ManStop(pCls);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Sets default LUT size, cut budget and recovery rounds.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void If2_ManSetDefaultPars( If2_Par_t * pPars )
{
    memset( pPars, 0, sizeof(If2_Par_t) );
    pPars->nLutSize = 6;
    pPars->nCutsMax = 3;
    pPars->nFlowIters = 1;
    pPars->nAreaIters = 1;
    pPars->fCutMin = 0;
    pPars->fDiverse = 1;
    pPars->DelayTarget = -1;
}

/**Function*************************************************************

  Synopsis    [Folds buffers and degenerate ANDs before box ordering.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If2_ManFoldBuffers( Gia_Man_t * p )
{
    Gia_Man_t * New = Gia_ManStart(Gia_ManObjNum(p));
    Gia_Obj_t * Obj;
    int i, a, b;
    New->pName = Abc_UtilStrsav(p->pName);
    New->pSpec = Abc_UtilStrsav(p->pSpec);
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachObj1(p, Obj, i)
        if ( Gia_ObjIsCi(Obj) ) Obj->Value = Gia_ManAppendCi(New);
        else if ( Gia_ObjIsCo(Obj) ) Obj->Value = Gia_ManAppendCo(New, Gia_ObjFanin0Copy(Obj));
        else if ( !p->fGiaSimple && Gia_ObjIsBuf(Obj) ) Obj->Value = Gia_ObjFanin0Copy(Obj);
        else
        {
            a = Gia_ObjFanin0Copy(Obj); b = Gia_ObjFanin1Copy(Obj);
            Obj->Value = !a || !b || a == (b^1) ? 0 : a == 1 || a == b ? b : b == 1 ? a : Gia_ManAppendAnd(New, a, b);
        }
    If2_ManOrderInterface(New, p);
    Gia_ManSetRegNum(New, Gia_ManRegNum(p));
    return New;
}

/**Function*************************************************************

  Synopsis    [Transfers timing and preserves interface metadata.]

  Description [Internal node names are left on the old GIA because its IDs change.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If2_ManTransferMetadata( Gia_Man_t * pNew, Gia_Man_t * pOld )
{
    Vec_Ptr_t * Names = pOld->vNamesNode;
    pNew->nConstrs = pOld->nConstrs;
    // Internal node IDs change during mapping; only interface names transfer.
    pOld->vNamesNode = NULL;
    Gia_ManTransferTiming(pNew, pOld);
    pOld->vNamesNode = Names;
    if ( !pNew->vRegInits && pOld->vRegInits ) pNew->vRegInits = (Vec_IntSize(pOld->vRegInits) ? Vec_IntDup(pOld->vRegInits) : Vec_IntAlloc(0));
    if ( !pNew->vRegClasses && pOld->vRegClasses ) pNew->vRegClasses = (Vec_IntSize(pOld->vRegClasses) ? Vec_IntDup(pOld->vRegClasses) : Vec_IntAlloc(0));
    if ( !pNew->vFlopClasses && pOld->vFlopClasses ) pNew->vFlopClasses = (Vec_IntSize(pOld->vFlopClasses) ? Vec_IntDup(pOld->vFlopClasses) : Vec_IntAlloc(0));
    if ( !pNew->vUserPiIds && pOld->vUserPiIds ) pNew->vUserPiIds = (Vec_IntSize(pOld->vUserPiIds) ? Vec_IntDup(pOld->vUserPiIds) : Vec_IntAlloc(0));
    if ( !pNew->vUserPoIds && pOld->vUserPoIds ) pNew->vUserPoIds = (Vec_IntSize(pOld->vUserPoIds) ? Vec_IntDup(pOld->vUserPoIds) : Vec_IntAlloc(0));
    if ( !pNew->vUserFfIds && pOld->vUserFfIds ) pNew->vUserFfIds = (Vec_IntSize(pOld->vUserFfIds) ? Vec_IntDup(pOld->vUserFfIds) : Vec_IntAlloc(0));
}

/**Function*************************************************************

  Synopsis    [Maps a GIA and restores normalized box order.]

  Description [Explicit registers precede box outputs in the timing manager but follow
  them in normalized GIA order. Convert both directions around mapping.]

  SideEffects [Transfers timing and interface names on success. Uses the
  input object Value and phase fields as temporary workspace.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * If2_ManPerformMapping( Gia_Man_t * pGia, If2_Par_t * pPars )
{
    Gia_Man_t * pNew, * pTemp, * pOrder;
    Gia_Obj_t * pObj;
    int i;
    if ( pGia == NULL || pPars == NULL || pPars->nLutSize < 2 || pPars->nLutSize > IF2_LEAF_MAX || pPars->nCutsMax < 1 || pPars->nCutsMax > IF2_CUT_MAX || pPars->nFlowIters < 0 || pPars->nAreaIters < 0 ) return NULL;
    if ( (size_t)Gia_ManObjNum(pGia) > ((size_t)-1) / sizeof(If2_Cut_t) / pPars->nCutsMax ) return NULL;
    if ( Gia_ManMuxNum(pGia) )
    {
        Abc_Print( -1, "&if2 currently requires an AIG without explicit MUX nodes.\n" );
        return NULL;
    }
    Gia_ManForEachAnd( pGia, pObj, i )
        if ( Gia_ObjSibl(pGia, i) >= i ) return NULL;
    if ( pGia->pManTime && Tim_ManBoxNum((Tim_Man_t *)pGia->pManTime) && (Gia_ManBufNum(pGia) || pGia->fGiaSimple) )
    {
        if ( Gia_ManHasChoices(pGia) )
        {
            Abc_Print(-1, "&if2 does not support boxed choices with buffers or simple gates.\n");
            return NULL;
        }
        pTemp = If2_ManFoldBuffers(pGia);
        If2_ManTransferMetadata(pTemp, pGia);
        pNew = If2_ManPerformMapping(pTemp, pPars);
        if ( pNew == NULL ) If2_ManTransferMetadata(pGia, pTemp);
        Gia_ManStop(pTemp);
        return pNew;
    }
    if ( pGia->pManTime && Tim_ManBoxNum((Tim_Man_t *)pGia->pManTime) && Gia_ManIsNormalized(pGia) )
    {
        pOrder = pGia;
        if ( Gia_ManRegNum(pGia) )
        {
            pOrder = Gia_ManDupUnshuffleInputs(pGia);
            If2_ManTransferMetadata(pOrder, pGia);
        }
        pTemp = Gia_ManDupUnnormalize(pOrder);
        if ( pTemp == NULL )
        {
            if ( pOrder != pGia ) { If2_ManTransferMetadata(pGia, pOrder); Gia_ManStop(pOrder); }
            return NULL;
        }
        If2_ManTransferMetadata(pTemp, pOrder);
        if ( pOrder != pGia ) Gia_ManStop(pOrder);
        pNew = If2_ManPerformMappingInt( pTemp, pPars );
        if ( pNew == NULL )
        {
            If2_ManTransferMetadata(pGia, pTemp);
            Gia_ManStop(pTemp);
            return NULL;
        }
        If2_ManTransferMetadata( pNew, pTemp );
        Gia_ManStop( pTemp );
        pTemp = pNew;
        pNew = Gia_ManDupNormalize( pTemp, 0 );
        Gia_ManTransferMapping( pNew, pTemp );
        If2_ManTransferMetadata( pNew, pTemp );
        Gia_ManStop( pTemp );
    }
    else
    {
        pNew = If2_ManPerformMappingInt( pGia, pPars );
        if ( pNew == NULL ) return NULL;
        If2_ManTransferMetadata( pNew, pGia );
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
