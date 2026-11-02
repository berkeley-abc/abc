/**CFile****************************************************************

  FileName    [giaIf3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Area-oriented truth-aware LUT mapping.]

  Synopsis    [Delay-constrained LUT area recovery directly on a GIA.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaIf3.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "bool/kit/kit.h"
#include "misc/tim/tim.h"
#include "misc/util/utilTruth.h"
#include "map/if/acd/ac_wrapper.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define IF3_LEAF_MAX  6
#define IF3_CUT_MAX  32
#define IF3_INFINITY ((float)1.0e20)
#define IF3_EPSILON  ((float)0.005)

typedef struct If3_Cut_t_ If3_Cut_t;
struct If3_Cut_t_
{
    word            Truth;
    word            Sign;
    int             Leaves[IF3_LEAF_MAX];
    float           Delay;
    float           Flow;
    float           Edge;
    int             nLeaves;
};

typedef struct If3_Man_t_ If3_Man_t;
struct If3_Man_t_
{
    Gia_Man_t *     pGia;
    If3_Par_t *     pPars;
    Tim_Man_t *     pTim;
    If3_Cut_t *     pCuts;
    If3_Cut_t *     pBest;
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
    int             fCausal;
    int             fReuseCuts;
    int             fCachedArea;
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
#define IF3_INLINE static inline __attribute__((always_inline))
#elif defined(_MSC_VER)
#define IF3_INLINE static __forceinline
#else
#define IF3_INLINE static inline
#endif

/**Function*************************************************************

  Synopsis    [Returns the retained cut bank of an AIG object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline If3_Cut_t * If3_ObjCuts( If3_Man_t * p, int Id )
{
    return p->pCuts + (size_t)Id * p->pPars->nCutsMax;
}

/**Function*************************************************************

  Synopsis    [Returns the selected cut of an AIG object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline If3_Cut_t * If3_ObjBest( If3_Man_t * p, int Id )
{
    return p->pBest + Id;
}

/**Function*************************************************************

  Synopsis    [Checks whether an AIG object is a mapping node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If3_ObjIsNode( If3_Man_t * p, int Id )
{
    return Gia_ObjIsAnd( Gia_ManObj(p->pGia, Id) );
}

/**Function*************************************************************

  Synopsis    [Computes the signature bit of a cut leaf.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word If3_LeafSign( int Id )
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
static void If3_CutUnit( If3_Cut_t * pCut, int Id )
{
    memset( pCut, 0, sizeof(If3_Cut_t) );
    if ( Id == 0 ) return;
    pCut->Truth = ABC_CONST(0xAAAAAAAAAAAAAAAA);
    pCut->Leaves[0] = Id;
    pCut->nLeaves = 1;
    pCut->Sign = If3_LeafSign( Id );
}

/**Function*************************************************************

  Synopsis    [Aligns a six-variable truth table with a merged support.]

  Description [The mask gives the destination positions of the ordered input variables.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If3_Stretch( word t, unsigned Mask )
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
static inline int If3_BitCount( word Bits )
{
    Bits -= ( Bits >> 1 ) & ABC_CONST( 0x5555555555555555 );
    Bits = ( Bits & ABC_CONST( 0x3333333333333333 ) ) + ( ( Bits >> 2 ) & ABC_CONST( 0x3333333333333333 ) );
    Bits = ( Bits + ( Bits >> 4 ) ) & ABC_CONST( 0x0F0F0F0F0F0F0F0F );
    return (int)( ( Bits * ABC_CONST( 0x0101010101010101 ) ) >> 56 );
}

/**Function*************************************************************

  Synopsis    [Merges sorted cut supports within the LUT input limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
IF3_INLINE int If3_CutMerge( If3_Man_t * p, If3_Cut_t * p0, If3_Cut_t * p1, If3_Cut_t * pRes )
{
    int i = 0, k = 0, n = 0, Id;
    unsigned m0 = 0, m1 = 0, mSmall = 0;
    if ( If3_BitCount(p0->Sign | p1->Sign) > p->pPars->nLutSize ) return 0;
    if ( p0->nLeaves == p->pPars->nLutSize || p1->nLeaves == p->pPars->nLutSize )
    {
        If3_Cut_t * pBig = p0->nLeaves >= p1->nLeaves ? p0 : p1;
        If3_Cut_t * pSmall = pBig == p0 ? p1 : p0;
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
static void If3_CutTruth( If3_Man_t * p, If3_Cut_t * p0, If3_Cut_t * p1, If3_Cut_t * pRes, int c0, int c1, int fXor )
{
    int i, n = pRes->nLeaves, nOld = n;
    word t0 = c0 ? ~p0->Truth : p0->Truth;
    word t1 = c1 ? ~p1->Truth : p1->Truth;
    if ( !p->fTruth ) { pRes->Truth = 0; return; }
    t0 = If3_Stretch(t0, (unsigned)pRes->Truth & 63);
    t1 = If3_Stretch(t1, (unsigned)(pRes->Truth >> 6));
    pRes->Truth = fXor ? t0 ^ t1 : t0 & t1;
    if ( p->pPars->fCutMin && (n < p0->nLeaves + p1->nLeaves || !p0->nLeaves || !p1->nLeaves) )
    {
        word Truth = pRes->Truth;
        int Leaves[IF3_LEAF_MAX], nMin;
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
    for ( i = 0; i < n; i++ ) pRes->Sign |= If3_LeafSign( pRes->Leaves[i] );
    return;
}

/**Function*************************************************************

  Synopsis    [References a cut and counts its newly used mapped cone.]

  Description [Trials restore increments with an undo list instead of a second cone traversal.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_CutRef( If3_Man_t * p, If3_Cut_t * pCut, int fTrial, float * pArea, float * pEdge )
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
            if ( p->pRefs[Id]++ || !If3_ObjIsNode(p, Id) ) continue;
            Vec_IntPush(p->vStack, Id);
        }
        if ( !Vec_IntSize(p->vStack) ) break;
        pCut = If3_ObjBest(p, Vec_IntPop(p->vStack));
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
static void If3_CutDeref( If3_Man_t * p, If3_Cut_t * pCut )
{
    int i, Id;
    Vec_IntClear(p->vStack);
    for ( ; ; )
    {
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            Id = pCut->Leaves[i];
            assert(p->pRefs[Id] > 0);
            if ( --p->pRefs[Id] || !If3_ObjIsNode(p, Id) ) continue;
            Vec_IntPush(p->vStack, Id);
        }
        if ( !Vec_IntSize(p->vStack) ) break;
        pCut = If3_ObjBest(p, Vec_IntPop(p->vStack));
    }
}

/**Function*************************************************************

  Synopsis    [Computes delay, area and edge costs of a candidate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void If3_CutScore( If3_Man_t * p, If3_Cut_t * pCut )
{
    int i, Id;
    float Div, Delay = 0, Flow = (float)(pCut->nLeaves > 1);
    float Edge = pCut->nLeaves > 1 ? (float)pCut->nLeaves : 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
    {
        If3_Cut_t * pLeaf;
        Id = pCut->Leaves[i];
        pLeaf = If3_ObjBest( p, Id );
        Delay = Abc_MaxFloat( Delay, pLeaf->Delay );
        if ( p->fExact ) continue;
        Div = p->Mode == 2 ? (p->pRefs[Id] ? 0 : 1) : (p->pRefs[Id] ? p->pInvRefs[Id] : 1);
        Flow += pLeaf->Flow * Div;
        Edge += pLeaf->Edge * Div;
    }
    pCut->Delay = Delay + (float)(pCut->nLeaves > 1);
    if ( p->fExact && p->fCachedArea )
    {
        word Mask = 0;
        for ( i = 0; i < pCut->nLeaves; i++ )
        {
            Id = pCut->Leaves[i];
            if ( !p->pRefs[Id] && If3_ObjIsNode(p, Id) ) Mask |= ((word)1) << p->pFlowIndex[Id];
        }
        for ( i = 0; i < p->nAreaGroups; i++ )
            if ( p->AreaMasks[i] & Mask ) { Flow += p->AreaCounts[i]; Edge += p->AreaEdges[i]; }
    }
    else if ( p->fExact )
    {
        If3_CutRef( p, pCut, 1, &Flow, &Edge );
        p->nTrials++;
    }
    pCut->Flow = Abc_MinFloat( Flow, IF3_INFINITY );
    pCut->Edge = Abc_MinFloat( Edge, IF3_INFINITY );
}

/**Function*************************************************************

  Synopsis    [Tests sorted support containment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If3_CutContains( If3_Man_t * p, If3_Cut_t * pLarge, If3_Cut_t * pSmall )
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
static inline int If3_CutLess( If3_Cut_t * p0, If3_Cut_t * p1, int Mode, float Required )
{
    int i, Late0 = p0->Delay > Required + IF3_EPSILON;
    int Late1 = p1->Delay > Required + IF3_EPSILON;
    if ( Late0 != Late1 ) return Late0 < Late1;
    if ( !Mode || Mode == 3 || Late0 )
    {
        if ( p0->Delay < p1->Delay - IF3_EPSILON ) return 1;
        if ( p0->Delay > p1->Delay + IF3_EPSILON ) return 0;
        if ( Mode != 3 && p0->nLeaves != p1->nLeaves ) return p0->nLeaves < p1->nLeaves;
    }
    if ( p0->Flow < p1->Flow - IF3_EPSILON ) return 1;
    if ( p0->Flow > p1->Flow + IF3_EPSILON ) return 0;
    if ( p0->Edge < p1->Edge - IF3_EPSILON ) return 1;
    if ( p0->Edge > p1->Edge + IF3_EPSILON ) return 0;
    if ( p0->Delay < p1->Delay - IF3_EPSILON ) return 1;
    if ( p0->Delay > p1->Delay + IF3_EPSILON ) return 0;
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
static inline int If3_CutInsert( If3_Man_t * p, If3_Cut_t * pSet, int nCuts, If3_Cut_t * pCut, If3_Cut_t * pFast, float Required, int fChecked )
{
    int i, k;
    if ( !fChecked )
        for ( i = 0; i < nCuts; i++ )
            if ( If3_CutContains(p, pCut, pSet + i) ) return nCuts;
    If3_CutScore( p, pCut );
    if ( (p->Mode == 1 || p->Mode == 2) && p->pPars->fDiverse && p->pPars->nCutsMax > 1 &&
         (pFast->nLeaves < 0 || If3_CutLess(pCut, pFast, 0, IF3_INFINITY)) )
        *pFast = *pCut;
    if ( !p->fChoices && pCut->nLeaves < p->pPars->nLutSize )
    {
        for ( i = k = 0; i < nCuts; i++ )
            if ( pSet[i].nLeaves <= pCut->nLeaves || !If3_CutContains(p, pSet+i, pCut) )
            {
                if ( k != i ) pSet[k] = pSet[i];
                k++;
            }
        nCuts = k;
    }
    for ( i = 0; i < nCuts; i++ )
        if ( If3_CutLess(pCut, pSet + i, p->Mode == 3 ? 3 : (p->Mode || p->pPars->fArea), p->Mode == 3 ? IF3_INFINITY : Required) ) break;
    if ( i == p->pPars->nCutsMax ) return nCuts;
    nCuts = Abc_MinInt( nCuts + 1, p->pPars->nCutsMax );
    for ( k = nCuts - 1; k > i; k-- ) pSet[k] = pSet[k-1];
    pSet[i] = *pCut;
    return nCuts;
}

static void If3_PrepareCache( If3_Man_t * p, int Root );

/**Function*************************************************************

  Synopsis    [Maps a node with truth tables or a larger cut bank.]

  Description [Choice cuts are imported from earlier equivalent nodes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ObjMap( If3_Man_t * p, int Id )
{
    If3_Cut_t Set[IF3_CUT_MAX], Cut, Fast, Unit0, Unit1, Winner;
    If3_Cut_t * p0, * p1, * pOld = If3_ObjBest(p, Id);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int Id0 = Gia_ObjFaninId0(pObj, Id), Id1 = Gia_ObjFaninId1(pObj, Id);
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], nCuts = 0;
    int nBefore;
    int i, k, m, Sibl = Gia_ObjSibl(p->pGia, Id), fReferenced = p->pRefs[Id] > 0;
    float Area, Edge, Required = p->pPars->fArea ? IF3_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && (fReferenced || p->fCausal);
    Fast.nLeaves = -1;
    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutDeref( p, pOld );
    If3_PrepareCache(p, Id);
    if ( p->Round && p->Mode != 3 )
    {
        Cut = *pOld;
        nCuts = If3_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
    }
    if ( Sibl )
    {
        int fCompl = Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p->pGia, Sibl));
        assert( Sibl < Id );
        for ( i = 0; i < p->pCounts[Sibl]; i++ )
        {
            Cut = If3_ObjCuts(p, Sibl)[i];
            if ( fCompl ) Cut.Truth = ~Cut.Truth;
            nCuts = If3_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
        }
    }
    if ( p->fReuseCuts )
    {
        for ( i = 0; i < p->pCounts[Id]; i++ )
        {
            Cut = If3_ObjCuts(p, Id)[i];
            nCuts = If3_CutInsert(p, Set, nCuts, &Cut, &Fast, Required, 0);
        }
        goto select_cut;
    }
    If3_CutUnit( &Unit0, Id0 );
    If3_CutUnit( &Unit1, Id1 );
    n0 += If3_ObjBest(p, Id0)->nLeaves > 1;
    n1 += If3_ObjBest(p, Id1)->nLeaves > 1;
    for ( i = 0; i < n0; i++ )
    for ( k = 0; k < n1; k++ )
    {
        p0 = i < p->pCounts[Id0] ? If3_ObjCuts(p, Id0) + i : &Unit0;
        p1 = k < p->pCounts[Id1] ? If3_ObjCuts(p, Id1) + k : &Unit1;
        p->nPairs++;
        if ( !If3_CutMerge(p, p0, p1, &Cut) ) continue;
        for ( m = 0; m < nCuts; m++ )
            if ( If3_CutContains(p, &Cut, Set + m) ) break;
        if ( m < nCuts ) continue;
        nBefore = Cut.nLeaves;
        If3_CutTruth( p, p0, p1, &Cut, Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), Gia_ObjIsXor(pObj) );
        nCuts = If3_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, nBefore == Cut.nLeaves );
    }
select_cut:
    assert( nCuts > 0 );
    if ( p->pPars->fDiverse && (p->Mode == 1 || p->Mode == 2) && p->pPars->nCutsMax > 1 && Fast.Delay < Set[0].Delay - IF3_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ )
            if ( Set[i].Delay <= Fast.Delay + IF3_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt( nCuts, p->pPars->nCutsMax - 1 );
            Set[i] = Fast;
            nCuts = Abc_MaxInt( nCuts, i + 1 );
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required + IF3_EPSILON )
    {
        Winner = *pOld;
        If3_CutScore(p, &Winner);
    }
    memcpy(If3_ObjCuts(p, Id), Set, sizeof(If3_Cut_t)*nCuts);
    *pOld = Winner;
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutRef( p, pOld, 0, &Area, &Edge );
}

/**Function*************************************************************

  Synopsis    [Enumerates truth-aware cuts of a three-input MUX.]

  Description [The data inputs are merged before adding the control support.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ObjMapMux( If3_Man_t * p, int Id )
{
    If3_Cut_t Set[IF3_CUT_MAX], Cut, Fast, Unit0, Unit1, Unit2, Pair, Winner;
    If3_Cut_t *p0, *p1, *p2, *pOld = If3_ObjBest( p, Id );
    Gia_Obj_t * pObj = Gia_ManObj( p->pGia, Id );
    int Id0 = Gia_ObjFaninId0( pObj, Id ), Id1 = Gia_ObjFaninId1( pObj, Id );
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], nCuts = 0;
    int Id2 = Gia_ObjFaninId2( p->pGia, Id ), n2 = p->pCounts[Id2], j;
    int nBefore;
    word t0, t1, t2;
    int i, k, m, Sibl = Gia_ObjSibl( p->pGia, Id ), fReferenced = p->pRefs[Id] > 0;
    float Area, Edge, Required = p->pPars->fArea ? IF3_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && (fReferenced || p->fCausal);
    Fast.nLeaves = -1;
    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutDeref( p, pOld );
    If3_PrepareCache(p, Id);
    if ( p->Round && p->Mode != 3 )
    {
        Cut = *pOld;
        nCuts = If3_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
    }
    if ( Sibl )
    {
        int fCompl = Gia_ObjPhase( pObj ) ^ Gia_ObjPhase( Gia_ManObj( p->pGia, Sibl ) );
        assert( Sibl < Id );
        for ( i = 0; i < p->pCounts[Sibl]; i++ )
        {
            Cut = If3_ObjCuts( p, Sibl )[i];
            if ( fCompl ) Cut.Truth = ~Cut.Truth;
            nCuts = If3_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, 0 );
        }
    }
    if ( p->fReuseCuts )
    {
        for ( i = 0; i < p->pCounts[Id]; i++ )
        {
            Cut = If3_ObjCuts(p, Id)[i];
            nCuts = If3_CutInsert(p, Set, nCuts, &Cut, &Fast, Required, 0);
        }
        goto select_cut;
    }
    If3_CutUnit( &Unit0, Id0 );
    If3_CutUnit( &Unit1, Id1 );
    If3_CutUnit( &Unit2, Id2 );
    n2 += If3_ObjBest( p, Id2 )->nLeaves > 1;
    n0 += If3_ObjBest( p, Id0 )->nLeaves > 1;
    n1 += If3_ObjBest( p, Id1 )->nLeaves > 1;
    for ( i = 0; i < n0; i++ )
        for ( k = 0; k < n1; k++ )
        {
            p0 = i < p->pCounts[Id0] ? If3_ObjCuts( p, Id0 ) + i : &Unit0;
            p1 = k < p->pCounts[Id1] ? If3_ObjCuts( p, Id1 ) + k : &Unit1;
            if ( !If3_CutMerge( p, p0, p1, &Pair ) ) continue;
            for ( j = 0; j < n2; j++ )
            {
                p2 = j < p->pCounts[Id2] ? If3_ObjCuts( p, Id2 ) + j : &Unit2;
                p->nPairs++;
                if ( !If3_CutMerge( p, &Pair, p2, &Cut ) ) continue;
                for ( m = 0; m < nCuts; m++ )
                    if ( If3_CutContains(p,  &Cut, Set + m ) ) break;
                if ( m < nCuts ) continue;
                t0 = If3_Stretch( Gia_ObjFaninC0( pObj ) ? ~p0->Truth : p0->Truth, (unsigned)Pair.Truth & 63 );
                t1 = If3_Stretch( Gia_ObjFaninC1( pObj ) ? ~p1->Truth : p1->Truth, (unsigned)( Pair.Truth >> 6 ) );
                t0 = If3_Stretch( t0, (unsigned)Cut.Truth & 63 );
                t1 = If3_Stretch( t1, (unsigned)Cut.Truth & 63 );
                t2 = If3_Stretch( Gia_ObjFaninC2( p->pGia, pObj ) ? ~p2->Truth : p2->Truth, (unsigned)( Cut.Truth >> 6 ) );
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
                        for ( m = 0; m < n; m++ ) Cut.Sign |= If3_LeafSign( Leaves[m] );
                        p->nMinimized++;
                    }
                }
                nCuts = If3_CutInsert( p, Set, nCuts, &Cut, &Fast, Required, nBefore == Cut.nLeaves );
            }
        }
select_cut:
    assert( nCuts > 0 );
    if ( p->pPars->fDiverse && ( p->Mode == 1 || p->Mode == 2 ) && p->pPars->nCutsMax > 1 &&
         Fast.Delay < Set[0].Delay - IF3_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ )
            if ( Set[i].Delay <= Fast.Delay + IF3_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt( nCuts, p->pPars->nCutsMax - 1 );
            Set[i] = Fast;
            nCuts = Abc_MaxInt( nCuts, i + 1 );
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required + IF3_EPSILON )
    {
        Winner = *pOld;
        If3_CutScore( p, &Winner );
    }
    memcpy( If3_ObjCuts( p, Id ), Set, sizeof( If3_Cut_t ) * nCuts );
    *pOld = Winner;
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutRef( p, pOld, 0, &Area, &Edge );
}

/**Function*************************************************************

  Synopsis    [Keeps feasible output constraints and tightens them after seeding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float If3_CoRequired( If3_Man_t * p, int iCo, float Delay )
{
    float Required = p->Target;
    if ( p->pGia->vCoReqs ) Required = (float)Vec_IntEntry(p->pGia->vCoReqs, iCo);
    else if ( p->pGia->vOutReqs ) Required = Vec_FltSize(p->pGia->vOutReqs) ? Vec_FltEntry(p->pGia->vOutReqs, iCo) : p->pGia->DefOutReqs;
    if ( p->pPars->fArea ) return IF3_INFINITY;
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
static void If3_ManRequired( If3_Man_t * p )
{
    Gia_Obj_t * pObj;
    If3_Cut_t * pCut;
    int i, k, Id, nObjs = Gia_ManObjNum(p->pGia);
    float Delay = 0, Required, LeafReq;
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachCo( p->pGia, pObj, i )
        Delay = Abc_MaxFloat( Delay, If3_ObjBest(p, Gia_ObjFaninId0p(p->pGia, pObj))->Delay );
    p->pPars->Delay = Delay;
    // Area recovery must not spend a depth improvement found during seeding.
    if ( p->Round == 0 )
        p->Target = Abc_MaxFloat( Delay, p->pPars->DelayTarget );
    else if ( p->Mode == 3 )
        p->Target = Abc_MinFloat( p->Target, Abc_MaxFloat(Delay, p->pPars->DelayTarget) );
    memset( p->pRefs, 0, sizeof(int) * nObjs );
    for ( i = 0; i < nObjs; i++ ) p->pRequired[i] = IF3_INFINITY;
    if ( p->pTim )
    {
        Tim_ManIncrementTravId( p->pTim );
        Tim_ManInitPoRequiredAll( p->pTim, p->pPars->fArea ? IF3_INFINITY : p->Target );
    }
    Gia_ManForEachObjReverse1( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) )
        {
            Id = Gia_ObjFaninId0(pObj, i);
            Required = p->pTim ? Tim_ManGetCoRequired(p->pTim, Gia_ObjCioId(pObj)) : If3_CoRequired(p, Gia_ObjCioId(pObj), If3_ObjBest(p, Id)->Delay);
            p->pRequired[Id] = Abc_MinFloat( p->pRequired[Id], Required );
            p->pRefs[Id]++;
        }
        else if ( Gia_ObjIsCi(pObj) )
        {
            if ( p->pTim ) Tim_ManSetCiRequired( p->pTim, Gia_ObjCioId(pObj), p->pRequired[i] );
        }
        else if ( p->pRefs[i] )
        {
            pCut = If3_ObjBest( p, i );
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
static void If3_AreaCache( If3_Man_t * p, int * Palette, int nPalette )
{
    If3_Cut_t * Cut;
    word Mask;
    int i, k, Id, Leaf, Bin, Group, nGroups = 0;
    p->nAreaGroups = 0;
    Vec_IntClear(p->vAreaNodes);
    Vec_IntClear(p->vStack);
    for ( i = 0; i < nPalette; i++ )
    {
        Id = Palette[i];
        if ( p->pRefs[Id] || !If3_ObjIsNode(p, Id) ) continue;
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
        Cut = If3_ObjBest(p, Id);
        for ( k = 0; k < Cut->nLeaves; k++ )
        {
            Leaf = Cut->Leaves[k];
            if ( !p->pRefs[Leaf] && If3_ObjIsNode(p, Leaf) && !p->pAreaSeen[Leaf] ) Vec_IntPush(p->vStack, Leaf);
        }
    }
    memset(p->AreaHash, -1, sizeof(p->AreaHash));
    for ( i = Vec_IntSize(p->vAreaNodes)-1; i >= 0; i-- )
    {
        Id = Vec_IntEntry(p->vAreaNodes, i);
        Mask = p->pLocalMask[Id];
        assert(Mask != 0);
        Cut = If3_ObjBest(p, Id);
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

/**Function*************************************************************

  Synopsis    [Collects a distinct unreferenced leaf for area caching.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_CacheLeaf( If3_Man_t * p, int Id, int * Palette, int * pSize )
{
    if ( p->pRefs[Id] || !If3_ObjIsNode(p, Id) || p->pAreaSeen[Id] ) return 1;
    if ( *pSize == 64 ) return 0;
    Palette[(*pSize)++] = Id;
    p->pAreaSeen[Id] = 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Prepares shared exact-area costs for a node's candidate cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PrepareCache( If3_Man_t * p, int Root )
{
    int Palette[64], Roots[4], nPalette = 0, nRoots = 0, i, j, k, Id;
    Gia_Obj_t * Obj = Gia_ManObj(p->pGia, Root);
    If3_Cut_t * Cut = If3_ObjBest(p, Root);
    p->fCachedArea = 0;
    if ( !p->fExact ) return;
    for ( i = 0; i < Cut->nLeaves; i++ )
        if ( !If3_CacheLeaf(p, Cut->Leaves[i], Palette, &nPalette) ) goto overflow;
    if ( p->fReuseCuts ) Roots[nRoots++] = Root;
    else
    {
        Roots[nRoots++] = Gia_ObjFaninId0(Obj, Root);
        Roots[nRoots++] = Gia_ObjFaninId1(Obj, Root);
        if ( Gia_ObjIsMux(p->pGia, Obj) ) Roots[nRoots++] = Gia_ObjFaninId2(p->pGia, Root);
    }
    if ( Gia_ObjSibl(p->pGia, Root) ) Roots[nRoots++] = Gia_ObjSibl(p->pGia, Root);
    for ( i = 0; i < nRoots; i++ )
    {
        Id = Roots[i];
        if ( !p->fReuseCuts && !If3_CacheLeaf(p, Id, Palette, &nPalette) ) goto overflow;
        for ( j = 0; j < p->pCounts[Id]; j++ )
        {
            Cut = If3_ObjCuts(p, Id) + j;
            for ( k = 0; k < Cut->nLeaves; k++ )
                if ( !If3_CacheLeaf(p, Cut->Leaves[k], Palette, &nPalette) ) goto overflow;
        }
    }
    for ( i = 0; i < nPalette; i++ ) p->pAreaSeen[Palette[i]] = 0;
    If3_AreaCache(p, Palette, nPalette);
    if ( p->nAreaGroups < 0 ) return;
    for ( i = 0; i < nPalette; i++ ) p->pFlowIndex[Palette[i]] = i;
    p->fCachedArea = 1;
    return;
overflow:
    for ( i = 0; i < nPalette; i++ ) p->pAreaSeen[Palette[i]] = 0;
}

typedef struct If3_BCut_t_ If3_BCut_t;
struct If3_BCut_t_
{
    word Mask;
    float Delay, Flow, Edge;
    int Size;
};

/**Function*************************************************************

  Synopsis    [Returns the least significant set bit of a nonzero word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If3_FirstBit( word Bits )
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
static inline void If3_BitUnpack( If3_Cut_t * Cut, If3_BCut_t * B, int * Palette )
{
    word Bits;
    int n = 0;
    Cut->Truth = Cut->Sign = 0;
    Cut->Delay = B->Delay; Cut->Flow = B->Flow; Cut->Edge = B->Edge;
    Cut->nLeaves = B->Size;
    for ( Bits = B->Mask; Bits; Bits &= Bits-1 )
    {
        Cut->Leaves[n] = Palette[If3_FirstBit(Bits)];
        Cut->Sign |= If3_LeafSign(Cut->Leaves[n++]);
    }
    assert(n == B->Size);
}

/**Function*************************************************************

  Synopsis    [Compares compact cuts without materializing their supports.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If3_BitLess( If3_BCut_t * A, If3_BCut_t * B, int Mode, float Required )
{
    int LateA = A->Delay > Required+IF3_EPSILON, LateB = B->Delay > Required+IF3_EPSILON;
    word Diff;
    if ( LateA != LateB ) return LateA < LateB;
    if ( !Mode || Mode == 3 || LateA )
    {
        if ( A->Delay < B->Delay-IF3_EPSILON ) return 1;
        if ( A->Delay > B->Delay+IF3_EPSILON ) return 0;
        if ( Mode != 3 && A->Size != B->Size ) return A->Size < B->Size;
    }
    if ( A->Flow < B->Flow-IF3_EPSILON ) return 1;
    if ( A->Flow > B->Flow+IF3_EPSILON ) return 0;
    if ( A->Edge < B->Edge-IF3_EPSILON ) return 1;
    if ( A->Edge > B->Edge+IF3_EPSILON ) return 0;
    if ( A->Delay < B->Delay-IF3_EPSILON ) return 1;
    if ( A->Delay > B->Delay+IF3_EPSILON ) return 0;
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
IF3_INLINE void If3_BitScore( If3_Man_t * p, If3_BCut_t * Cut, int * Palette, float Costs[64][3] )
{
    word Bits;
    int i;
    float Delay = 0, Flow = (float)(Cut->Size > 1), Edge = Cut->Size > 1 ? (float)Cut->Size : 0;
    for ( Bits = Cut->Mask; Bits; Bits &= Bits-1 )
    {
        i = If3_FirstBit(Bits);
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
        If3_Cut_t Temp;
        If3_BitUnpack(&Temp, Cut, Palette);
        If3_CutRef(p, &Temp, 1, &Flow, &Edge);
        p->nTrials++;
    }
    Cut->Flow = Abc_MinFloat(Flow, IF3_INFINITY);
    Cut->Edge = Abc_MinFloat(Edge, IF3_INFINITY);
}

/**Function*************************************************************

  Synopsis    [Retains compact priority cuts and a timing alternative.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
IF3_INLINE int If3_BitKeep( If3_Man_t * p, If3_BCut_t * Set, int nCuts, If3_BCut_t * Cut, If3_BCut_t * Fast, float Required )
{
    int i, k;
    if ( (p->Mode == 1 || p->Mode == 2) && p->pPars->fDiverse && p->Limit > 1 &&
        (Fast->Size < 0 || If3_BitLess(Cut, Fast, 0, IF3_INFINITY)) ) *Fast = *Cut;
    for ( i = k = 0; i < nCuts; i++ )
        if ( (Cut->Mask & Set[i].Mask) != Cut->Mask )
        {
            if ( k != i ) Set[k] = Set[i];
            k++;
        }
    nCuts = k;
    for ( i = 0; i < nCuts; i++ )
        if ( If3_BitLess(Cut, Set+i, p->Mode == 3 ? 3 : (p->Mode || p->pPars->fArea), p->Mode == 3 ? IF3_INFINITY : Required) ) break;
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
static void If3_ObjMapBits( If3_Man_t * p, int Id )
{
    If3_BCut_t Set[4], Cut, Fast, Winner;
    If3_Cut_t * pOld = If3_ObjBest(p, Id);
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int Id0 = Gia_ObjFaninId0(pObj, Id), Id1 = Gia_ObjFaninId1(pObj, Id);
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], nCuts = 0;
    word Masks[11], Mask;
    int Palette[64], nPalette = 0, i, j, k, n, Leaf, fReferenced = p->pRefs[Id] > 0;
    float Costs[64][3], Div, Area, Edge, Required = p->pPars->fArea ? IF3_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && (fReferenced || p->fCausal);
    Fast.Size = -1;
    {
        int * Pal0 = p->pBankLeaves + (size_t)Id0*p->pPars->nCutsMax*6;
        int * Pal1 = p->pBankLeaves + (size_t)Id1*p->pPars->nCutsMax*6;
        word * Bank0 = p->pBankMasks + (size_t)Id0*p->pPars->nCutsMax;
        word * Bank1 = p->pBankMasks + (size_t)Id1*p->pPars->nCutsMax;
        word Expand0[25], Expand1[25], Bit, Bits;
        int nPal0 = p->pBankSize[Id0], nPal1 = p->pBankSize[Id1];
        int nOld = p->Round ? pOld->nLeaves : 0;
        int a = 0, b = 0, o = 0, A, B, O, Add0 = If3_ObjBest(p, Id0)->nLeaves > 1, Add1 = If3_ObjBest(p, Id1)->nLeaves > 1;
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
            for ( Bits = Bank0[i]; Bits; Bits &= Bits-1 ) Masks[i] |= Expand0[If3_FirstBit(Bits)];
        }
        if ( Add0 ) Masks[n0++] = Expand0[nPal0];
        for ( i = 0; i < n1; i++ )
        {
            Masks[n0+i] = 0;
            for ( Bits = Bank1[i]; Bits; Bits &= Bits-1 ) Masks[n0+i] |= Expand1[If3_FirstBit(Bits)];
        }
        if ( Add1 ) Masks[n0+n1++] = Expand1[nPal1];
    }

    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutDeref(p, pOld);
    for ( i = 0; i < nPalette; i++ )
    {
        Leaf = Palette[i];
        Div = p->Mode == 2 ? (p->pRefs[Leaf] ? 0 : 1) : (p->pRefs[Leaf] ? p->pInvRefs[Leaf] : 1);
        Costs[i][0] = If3_ObjBest(p, Leaf)->Delay;
        Costs[i][1] = p->fExact ? 0 : If3_ObjBest(p, Leaf)->Flow * Div;
        Costs[i][2] = p->fExact ? 0 : If3_ObjBest(p, Leaf)->Edge * Div;
    }
    if ( p->fExact ) If3_AreaCache(p, Palette, nPalette);
    if ( p->Round && p->Mode != 3 )
    {
        Cut.Mask = Masks[n0+n1]; Cut.Size = pOld->nLeaves;
        If3_BitScore(p, &Cut, Palette, Costs);
        nCuts = If3_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
    }
    for ( i = 0; i < n0; i++ )
    for ( k = 0; k < n1; k++ )
    {
        p->nPairs++;
        Mask = Masks[i] | Masks[n0+k];
        n = If3_BitCount(Mask);
        if ( n > p->pPars->nLutSize ) continue;
        p->nMerged++;
        for ( j = 0; j < nCuts; j++ ) if ( (Mask & Set[j].Mask) == Set[j].Mask ) break;
        if ( j < nCuts ) continue;
        Cut.Mask = Mask; Cut.Size = n;
        If3_BitScore(p, &Cut, Palette, Costs);
        nCuts = If3_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
    }
    assert(nCuts > 0);
    if ( p->pPars->fDiverse && (p->Mode == 1 || p->Mode == 2) && p->Limit > 1 && Fast.Delay < Set[0].Delay-IF3_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ ) if ( Set[i].Delay <= Fast.Delay+IF3_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt(nCuts, p->Limit-1); Set[i] = Fast; nCuts = Abc_MaxInt(nCuts, i+1);
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required+IF3_EPSILON )
    {
        Winner.Mask = Masks[n0+n1]; Winner.Size = pOld->nLeaves;
        If3_BitScore(p, &Winner, Palette, Costs);
    }
    {
        int * SavedLeaves = p->pBankLeaves + (size_t)Id*p->pPars->nCutsMax*6;
        word * SavedMasks = p->pBankMasks + (size_t)Id*p->pPars->nCutsMax;
        word Used = 0, Bits, Expand[64];
        int Count = 0;
        for ( i = 0; i < nCuts; i++ ) Used |= Set[i].Mask;
        for ( Bits = Used; Bits; Bits &= Bits-1 )
        {
            j = If3_FirstBit(Bits);
            Expand[j] = ((word)1) << Count;
            SavedLeaves[Count++] = Palette[j];
        }
        p->pBankSize[Id] = (unsigned char)Count;
        for ( i = 0; i < nCuts; i++ )
        {
            SavedMasks[i] = 0;
            for ( Bits = Set[i].Mask; Bits; Bits &= Bits-1 ) SavedMasks[i] |= Expand[If3_FirstBit(Bits)];
        }
    }

    If3_BitUnpack(pOld, &Winner, Palette);
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutRef(p, pOld, 0, &Area, &Edge);
}

/**Function*************************************************************

  Synopsis    [Maps a protected three-input fanout-free group.]

  Description [The initial mapped boundaries remain available; only unused interiors
  are hidden from later rounds.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ObjMapGroup( If3_Man_t * p, int Id )
{
    If3_BCut_t Set[4], Cut, Fast, Winner;
    If3_Cut_t * pOld = If3_ObjBest(p, Id);
    int * Inputs = Vec_IntEntryP(p->vGroupInputs, p->pGroupOffset[Id]);
    int Id0 = Inputs[0], Id1 = Inputs[1], Id2 = Inputs[2];
    int n0 = p->pCounts[Id0], n1 = p->pCounts[Id1], n2 = p->pCounts[Id2], nCuts = 0;
    word Masks[16], Mask, Pair;
    int Palette[64], nPalette = 0, i, j, k, c, n, Leaf, fReferenced = p->pRefs[Id] > 0;
    float Costs[64][3], Div, Area, Edge, Required = p->pPars->fArea ? IF3_INFINITY : p->pRequired[Id];
    p->fExact = p->Mode == 2 && (fReferenced || p->fCausal);
    Fast.Size = -1;
    {
        int Pos[4] = {0,0,0,0}, Count[4], Next[4], q, Total = 0;
        int * Pals[4];
        word Expand[3][19], Bits, Bit;
        for ( q = 0; q < 3; q++ )
        {
            Pals[q] = p->pBankLeaves + (size_t)Inputs[q]*p->pPars->nCutsMax*6;
            Count[q] = p->pBankSize[Inputs[q]]+(If3_ObjBest(p, Inputs[q])->nLeaves > 1);
            Total += p->pCounts[Inputs[q]]+(If3_ObjBest(p, Inputs[q])->nLeaves > 1);
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
                for ( Bits = Bank[i]; Bits; Bits &= Bits-1 ) Masks[Total] |= Expand[q][If3_FirstBit(Bits)];
                Total++;
            }
            if ( If3_ObjBest(p, Inputs[q])->nLeaves > 1 ) Masks[Total++] = Expand[q][Count[q]-1];
        }
        n0 += If3_ObjBest(p, Id0)->nLeaves > 1;
        n1 += If3_ObjBest(p, Id1)->nLeaves > 1;
        n2 += If3_ObjBest(p, Id2)->nLeaves > 1;
    }

    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutDeref(p, pOld);
    for ( i = 0; i < nPalette; i++ )
    {
        Leaf = Palette[i];
        Div = p->Mode == 2 ? (p->pRefs[Leaf] ? 0 : 1) : (p->pRefs[Leaf] ? p->pInvRefs[Leaf] : 1);
        Costs[i][0] = If3_ObjBest(p, Leaf)->Delay;
        Costs[i][1] = p->fExact ? 0 : If3_ObjBest(p, Leaf)->Flow * Div;
        Costs[i][2] = p->fExact ? 0 : If3_ObjBest(p, Leaf)->Edge * Div;
    }
    if ( p->fExact ) If3_AreaCache(p, Palette, nPalette);
    if ( p->Round && p->Mode != 3 )
    {
        Cut.Mask = Masks[n0+n1+n2]; Cut.Size = pOld->nLeaves;
        If3_BitScore(p, &Cut, Palette, Costs);
        nCuts = If3_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
    }
    for ( i = 0; i < n0; i++ )
    for ( k = 0; k < n1; k++ )
    {
        Pair = Masks[i] | Masks[n0+k];
        if ( If3_BitCount(Pair) > p->pPars->nLutSize ) continue;
        for ( c = 0; c < n2; c++ )
        {
            p->nPairs++;
            Mask = Pair | Masks[n0+n1+c];
            n = If3_BitCount(Mask);
            if ( n > p->pPars->nLutSize ) continue;
            p->nMerged++;
            for ( j = 0; j < nCuts; j++ ) if ( (Mask & Set[j].Mask) == Set[j].Mask ) break;
            if ( j < nCuts ) continue;
            Cut.Mask = Mask; Cut.Size = n;
            If3_BitScore(p, &Cut, Palette, Costs);
            nCuts = If3_BitKeep(p, Set, nCuts, &Cut, &Fast, Required);
        }
    }
    assert(nCuts > 0);
    if ( p->pPars->fDiverse && (p->Mode == 1 || p->Mode == 2) && p->Limit > 1 && Fast.Delay < Set[0].Delay-IF3_EPSILON )
    {
        for ( i = 0; i < nCuts; i++ ) if ( Set[i].Delay <= Fast.Delay+IF3_EPSILON ) break;
        if ( i == nCuts )
        {
            i = Abc_MinInt(nCuts, p->Limit-1); Set[i] = Fast; nCuts = Abc_MaxInt(nCuts, i+1);
        }
    }
    Winner = Set[0];
    if ( p->Mode == 3 && Set[0].Delay > Required+IF3_EPSILON )
    {
        Winner.Mask = Masks[n0+n1+n2]; Winner.Size = pOld->nLeaves;
        If3_BitScore(p, &Winner, Palette, Costs);
    }
    {
        int * SavedLeaves = p->pBankLeaves + (size_t)Id*p->pPars->nCutsMax*6;
        word * SavedMasks = p->pBankMasks + (size_t)Id*p->pPars->nCutsMax;
        word Used = 0, Bits, Expand[64];
        int Count = 0;
        for ( i = 0; i < nCuts; i++ ) Used |= Set[i].Mask;
        for ( Bits = Used; Bits; Bits &= Bits-1 )
        {
            j = If3_FirstBit(Bits);
            Expand[j] = ((word)1) << Count;
            SavedLeaves[Count++] = Palette[j];
        }
        p->pBankSize[Id] = (unsigned char)Count;
        for ( i = 0; i < nCuts; i++ )
        {
            SavedMasks[i] = 0;
            for ( Bits = Set[i].Mask; Bits; Bits &= Bits-1 ) SavedMasks[i] |= Expand[If3_FirstBit(Bits)];
        }
    }

    If3_BitUnpack(pOld, &Winner, Palette);
    p->pCounts[Id] = (unsigned char)nCuts;
    if ( p->Round && p->Mode != 3 && fReferenced ) If3_CutRef(p, pOld, 0, &Area, &Edge);
}

/**Function*************************************************************

  Synopsis    [Groups fanout-free cones after the first delay mapping.]

  Description [Groups have at most three distinct inputs and never hide a selected
  mapping boundary. The original AIG is retained for export.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ManGroup( If3_Man_t * p )
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
    if ( p->pPars->fVerbose ) Abc_Print(1, "If3 three-input groups = %d\n", nGroups);
}

/**Function*************************************************************

  Synopsis    [Evaluates a repaired structural cut inside its bounded window.]

  Description [The window is already in postorder. Boundary nodes outside the cut
  remain unknown; the cut must separate them from its root.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_LevelCutTruth( If3_Man_t * p, int Root, If3_Cut_t * pCut, int * Nodes, int nNodes )
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
static void If3_TryLevelCut( If3_Man_t * p, int Root )
{
    Gia_Obj_t *Obj = Gia_ManObj( p->pGia, Root ), *Node;
    If3_Cut_t Cut, Old[4], *Best = If3_ObjBest( p, Root );
    word Adj[64], Fixed[64], Seen, Queue, Bits, Mask;
    int Parent[64], Nodes[64], Id, Id0, Id1, Id2, i, j, k, nNodes = 0, nVerts = 2, Flow = 0, u, v;
    int nCuts, nPalette, Leaf, nNew;
    int * Palette = p->pBankLeaves ? p->pBankLeaves + (size_t)Root * p->pPars->nCutsMax * 6 : NULL;
    word * Masks = p->pBankMasks ? p->pBankMasks + (size_t)Root * p->pPars->nCutsMax : NULL;
    float Bound = Abc_MaxFloat( If3_ObjBest( p, Gia_ObjFaninId0( Obj, Root ) )->Delay,
                                If3_ObjBest( p, Gia_ObjFaninId1( Obj, Root ) )->Delay );
    if ( Gia_ObjIsMux( p->pGia, Obj ) )
        Bound = Abc_MaxFloat( Bound, If3_ObjBest( p, Gia_ObjFaninId2( p->pGia, Root ) )->Delay );
    if ( Bound < 1 || Best->Delay <= Bound + IF3_EPSILON ) return;
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
        if ( Gia_ObjIsAnd( Node ) && ( Id == Root || If3_ObjBest( p, Id )->Delay >= Bound - 1 - IF3_EPSILON ) )
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
        if ( If3_ObjBest( p, Id )->Delay < Bound - IF3_EPSILON )
        {
            nNew = !Gia_ObjIsAnd( Node ) || If3_ObjBest( p, Id )->Delay < Bound - 1 - IF3_EPSILON ? 1 : 2;
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
        if ( !Gia_ObjIsAnd( Node ) || If3_ObjBest( p, Id )->Delay < Bound - 1 - IF3_EPSILON )
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
            u = If3_FirstBit( Queue );
            Queue &= Queue - 1;
            Bits = Adj[u] & ~Seen;
            Seen |= Bits;
            Queue |= Bits;
            for ( ; Bits; Bits &= Bits - 1 ) Parent[If3_FirstBit( Bits )] = u;
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
        v = !Gia_ObjIsAnd( Node ) || If3_ObjBest( p, Id )->Delay < Bound - 1 - IF3_EPSILON ? 1 : u + 1;
        if ( !u || !( Seen & ( ( (word)1 ) << u ) ) || ( Seen & ( ( (word)1 ) << v ) ) ) continue;
        assert( Cut.nLeaves < p->pPars->nLutSize );
        for ( j = Cut.nLeaves++; j && Cut.Leaves[j - 1] > Id; j-- ) Cut.Leaves[j] = Cut.Leaves[j - 1];
        Cut.Leaves[j] = Id;
        Cut.Sign |= If3_LeafSign( Id );
    }
    assert( Cut.nLeaves == Flow );
    p->fCachedArea = 0;
    If3_CutScore( p, &Cut );
    assert( Cut.Delay <= Bound + IF3_EPSILON );
    if ( p->pCuts )
    {
        If3_Cut_t * Cuts = If3_ObjCuts( p, Root );
        if ( p->fTruth && !If3_LevelCutTruth( p, Root, &Cut, Nodes, nNodes ) ) return;
        nCuts = Abc_MinInt( p->pCounts[Root], p->pPars->nCutsMax - 1 );
        memmove( Cuts + 1, Cuts, sizeof( If3_Cut_t ) * nCuts );
        Cuts[0] = *Best = Cut;
        p->pCounts[Root] = (unsigned char)( nCuts + 1 );
        return;
    }
    nCuts = Abc_MinInt( p->pCounts[Root], p->Limit - 1 );
    for ( i = 0; i < nCuts; i++ )
    {
        Old[i].nLeaves = 0;
        for ( Bits = Masks[i]; Bits; Bits &= Bits - 1 ) Old[i].Leaves[Old[i].nLeaves++] = Palette[If3_FirstBit( Bits )];
    }
    *Best = Cut;
    nPalette = 0;
    for ( i = 0; i <= nCuts; i++ )
    {
        If3_Cut_t * C = i ? Old + i - 1 : &Cut;
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
        If3_Cut_t * C = i ? Old + i - 1 : &Cut;
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
static void If3_ReverseArea( If3_Man_t * p )
{
    Gia_Obj_t * Obj;
    If3_Cut_t * Cut;
    int i, j, Id, Count = 0;
    float Bound, Delay;
    Gia_ManForEachAndReverse ( p->pGia, Obj, i )
    {
        if ( !p->pRefs[i] ) continue;
        if ( Gia_ObjIsMuxId( p->pGia, i ) )
            If3_ObjMapMux( p, i );
        else if ( p->pGroupOffset[i] )
            If3_ObjMapGroup( p, i );
        else if ( !p->pCuts )
            If3_ObjMapBits( p, i );
        else
            If3_ObjMap( p, i );
        Count++;
        Cut = If3_ObjBest( p, i );
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
        Cut = If3_ObjBest( p, i );
        Delay = 0;
        for ( j = 0; j < Cut->nLeaves; j++ ) Delay = Abc_MaxFloat( Delay, If3_ObjBest( p, Cut->Leaves[j] )->Delay );
        Cut->Delay = Delay + (float)( Cut->nLeaves > 1 );
        assert( !p->pRefs[i] || p->pPars->fArea || Cut->Delay <= p->pRequired[i] + IF3_EPSILON );
    }
    if ( p->pPars->fVerbose ) Abc_Print( 1, "If3 reverse area: %d selected nodes\n", Count );
}

/**Function*************************************************************

  Synopsis    [Performs one delay, seed, flow or exact-area round.]

  Description [Choice graphs use reverse exact-area recovery when timing boxes permit it.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ManRound( If3_Man_t * p, int Mode )
{
    Gia_Obj_t * pObj;
    int i, Id, iCi;
    abctime clk = Abc_Clock();
    p->Mode = Mode;
    p->fReuseCuts = p->pCuts && p->Round >= 3;
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
    if ( Mode == 2 && (p->pPars->fReverse || Gia_ManHasChoices(p->pGia)) && !p->pTim && !Gia_ManBufNum(p->pGia) )
        If3_ReverseArea( p );
    else
        Gia_ManForEachObj1 ( p->pGia, pObj, i )
        {
            if ( Gia_ObjIsCi( pObj ) )
            {
                iCi = Gia_ObjCioId( pObj );
                if ( p->pTim ) If3_ObjBest( p, i )->Delay = Tim_ManGetCiArrival( p->pTim, iCi );
            }
            else if ( Gia_ObjIsCo( pObj ) )
            {
                if ( p->pTim )
                    Tim_ManSetCoArrival( p->pTim, Gia_ObjCioId( pObj ),
                                         If3_ObjBest( p, Gia_ObjFaninId0( pObj, i ) )->Delay );
            }
            else if ( !p->pGia->fGiaSimple && Gia_ObjIsBuf( pObj ) )
            {
                p->fExact = 0;
                Id = Gia_ObjFaninId0( pObj, i );
                If3_CutUnit( If3_ObjBest( p, i ), Id );
                if ( Gia_ObjFaninC0( pObj ) ) If3_ObjBest( p, i )->Truth = ~If3_ObjBest( p, i )->Truth;
                If3_CutScore( p, If3_ObjBest( p, i ) );
                p->pCounts[i] = 1;
                if ( p->pCuts )
                    *If3_ObjCuts( p, i ) = *If3_ObjBest( p, i );
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
                If3_ObjMapMux( p, i );
            else if ( p->pGroupOffset[i] )
                If3_ObjMapGroup( p, i );
            else if ( !p->fTruth && p->pPars->nCutsMax <= 4 )
                If3_ObjMapBits( p, i );
            else
                If3_ObjMap( p, i );
            if ( Mode == 0 && !p->pPars->fArea && !p->pTim && !p->pGia->vInArrs && !p->pGia->vCiArrs && !Gia_ManBufNum( p->pGia ) &&
                 Gia_ObjIsAnd( pObj ) )
                If3_TryLevelCut( p, i );
        }
    If3_ManRequired( p );
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "If3 %s %d: LUT = %d  Edge = %d  Delay = %.2f  Time = %.3f sec\n",
                   Mode == 2 ? "area" : ( Mode == 3 ? "seed" : ( Mode ? "flow" : "delay" ) ), p->Round, p->pPars->Area,
                   p->pPars->Edge, p->pPars->Delay, 1.0 * ( Abc_Clock() - clk ) / CLOCKS_PER_SEC );
    p->Round++;
}

/**Function*************************************************************

  Synopsis    [Rebuilds sharing costs using causal reference placeholders.]

  Description [Each formerly used LUT has one temporary reference. Its
  earliest old consumer retires that reference before choosing a cut.
  Later consumers therefore share only logic retained by already processed
  nodes. The final cover is rebuilt from the outputs, and the caller retains
  the best feasible incumbent.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_CausalRound( If3_Man_t * p )
{
    Gia_Obj_t * Obj;
    If3_Cut_t * Cut;
    int i, k, Leaf, nObjs = Gia_ManObjNum(p->pGia);
    int * Heads, * Next;
    unsigned char * Used;
    float Area, Edge;
    abctime clk = Abc_Clock();
    if ( p->pTim || Gia_ManBufNum(p->pGia) ) return;
    Heads = ABC_CALLOC( int, nObjs );
    Next = ABC_ALLOC( int, nObjs );
    Used = ABC_ALLOC( unsigned char, nObjs );
    for ( i = 0; i < nObjs; i++ )
    {
        Next[i] = -1;
        Used[i] = (unsigned char)(p->pRefs[i] > 0);
    }
    Gia_ManForEachAnd( p->pGia, Obj, i )
    {
        if ( !Used[i] ) continue;
        Cut = If3_ObjBest(p, i);
        for ( k = 0; k < Cut->nLeaves; k++ )
        {
            Leaf = Cut->Leaves[k];
            if ( !If3_ObjIsNode(p, Leaf) || Next[Leaf] >= 0 ) continue;
            assert( Used[Leaf] && Leaf < i );
            Next[Leaf] = Heads[i];
            Heads[i] = Leaf;
        }
    }
    memset( p->pRefs, 0, sizeof(int) * nObjs );
    p->Mode = 2;
    p->Limit = p->pPars->nCutsMax;
    p->fCausal = 1;
    p->fReuseCuts = p->pCuts != NULL;
    Gia_ManForEachAnd( p->pGia, Obj, i )
    {
        if ( p->pSkip[i] ) continue;
        assert( p->pRefs[i] == 0 );
        for ( Leaf = Heads[i]; Leaf; Leaf = Next[Leaf] )
        {
            assert( p->pRefs[Leaf] > 0 );
            if ( --p->pRefs[Leaf] == 0 ) If3_CutDeref(p, If3_ObjBest(p, Leaf));
        }
        if ( Gia_ObjIsMuxId(p->pGia, i) ) If3_ObjMapMux(p, i);
        else if ( p->pGroupOffset[i] ) If3_ObjMapGroup(p, i);
        else if ( !p->pCuts ) If3_ObjMapBits(p, i);
        else If3_ObjMap(p, i);
        if ( Used[i] )
        {
            p->pRefs[i]++;
            If3_CutRef(p, If3_ObjBest(p, i), 0, &Area, &Edge);
        }
    }
    p->fCausal = 0;
    If3_ManRequired(p);
    if ( p->pPars->fVerbose )
        Abc_Print(1, "If3 causal %d: LUT = %d  Edge = %d  Delay = %.2f  Time = %.3f sec\n",
                  p->Round, p->pPars->Area, p->pPars->Edge, p->pPars->Delay,
                  1.0 * (Abc_Clock() - clk) / CLOCKS_PER_SEC);
    p->Round++;
    ABC_FREE( Heads );
    ABC_FREE( Next );
    ABC_FREE( Used );
}

/**Function*************************************************************

  Synopsis    [Keeps a feasible incumbent while recovery explores alternatives.]

  Description [Every cut belongs to the same fixed AIG. Saving the selected
  cuts suffices; mapped references and requirements are rebuilt on restore.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_SaveCover( If3_Man_t * p, If3_Cut_t * Saved, int * pArea, float * pDelay )
{
    if ( Saved == NULL ) return;
    if ( p->pPars->Area > *pArea || (p->pPars->Area == *pArea && p->pPars->Delay >= *pDelay) ) return;
    memcpy( Saved, p->pBest, sizeof(If3_Cut_t) * Gia_ManObjNum(p->pGia) );
    *pArea = p->pPars->Area;
    *pDelay = p->pPars->Delay;
}

/**Function*************************************************************

  Synopsis    [Computes selected functions when structural export is unavailable.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ManSelectedTruth( If3_Man_t * p )
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
        If3_Cut_t * pCut;
        if ( !p->pRefs[i] ) continue;
        pCut = If3_ObjBest(p, i);
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
static void If3_ManOrderInterface( Gia_Man_t * pNew, Gia_Man_t * pOld )
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
static Gia_Man_t * If3_ManExportStructural( If3_Man_t * p )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    Vec_Int_t * vMap;
    int i, k;
    if ( Gia_ManBufNum(p->pGia) ) return NULL;
    Gia_ManForEachAnd(p->pGia, pObj, i)
        if ( p->pRefs[i] && If3_ObjBest(p, i)->nLeaves < 2 ) return NULL;
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
    If3_ManOrderInterface(pNew, p->pGia);
    Vec_IntFreeP(&pNew->vMapping);
    vMap = Vec_IntAlloc(Gia_ManObjNum(pNew) + (int)p->pPars->Edge + 2*(int)p->pPars->Area);
    Vec_IntFill(vMap, Gia_ManObjNum(pNew), 0);
    Gia_ManForEachAnd(p->pGia, pObj, i)
    {
        If3_Cut_t * pCut = If3_ObjBest(p, i);
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

enum { IF3_RECIPE_BINS = 4096, IF3_RECIPE_LIMIT = IF3_RECIPE_BINS / 2 };

typedef struct If3_Recipe_t_ If3_Recipe_t;
struct If3_Recipe_t_
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
static void If3_RecipeClear( If3_Recipe_t * pRecipes )
{
    int i;
    for ( i = 0; i < IF3_RECIPE_BINS; i++ )
        if ( pRecipes[i].pGraph ) Kit_GraphFree( pRecipes[i].pGraph );
    memset( pRecipes, 0, sizeof(If3_Recipe_t) * IF3_RECIPE_BINS );
}

/**Function*************************************************************

  Synopsis    [Reuses the same deterministic factorization for identical LUTs.]

  Description [The cache belongs to one export. Graph realization overwrites all
  leaf and internal literals, so cached graphs never retain input-specific state.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Kit_Graph_t * If3_RecipeFind( If3_Recipe_t * pRecipes, int * pnRecipes, word Truth, int nLeaves, Vec_Int_t * vCover )
{
    unsigned Words[2];
    word Hash = Truth + ABC_CONST(0x9e3779b97f4a7c15) * (nLeaves + 1);
    int Home, Bin;
    // Stretched truth tables have equal halves. Mix before folding so
    // functions of fewer than six variables do not share one hash bucket.
    Hash = (Hash ^ (Hash >> 30)) * ABC_CONST(0xbf58476d1ce4e5b9);
    Hash = (Hash ^ (Hash >> 27)) * ABC_CONST(0x94d049bb133111eb);
    Home = (int)((Hash ^ (Hash >> 31)) & (IF3_RECIPE_BINS - 1));
    Bin = Home;
    while ( pRecipes[Bin].pGraph )
    {
        if ( pRecipes[Bin].Truth == Truth && pRecipes[Bin].nLeaves == nLeaves )
            return pRecipes[Bin].pGraph;
        Bin = (Bin + 1) & (IF3_RECIPE_BINS - 1);
    }
    if ( *pnRecipes == IF3_RECIPE_LIMIT )
    {
        If3_RecipeClear( pRecipes );
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
static Gia_Man_t * If3_ManExport( If3_Man_t * p )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vCopies = Vec_IntStartFull( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vOffsets = Vec_IntAlloc( Gia_ManObjNum(p->pGia) );
    Vec_Int_t * vMapping = Vec_IntStart( 1 );
    Vec_Int_t * vLeaves = Vec_IntAlloc( IF3_LEAF_MAX );
    Vec_Int_t * vCover = Vec_IntAlloc( 1024 );
    Gia_Obj_t * pObj;
    If3_Cut_t * pCut;
    If3_Recipe_t * pRecipes = ABC_CALLOC( If3_Recipe_t, IF3_RECIPE_BINS );
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
            pCut = If3_ObjBest( p, i );
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
                pGraph = If3_RecipeFind( pRecipes, &nRecipes, pCut->Truth, pCut->nLeaves, vCover );
                if ( pGraph == NULL )
                {
                    Abc_Print( -1, "&if3: factoring a selected LUT failed.\n" );
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
    If3_ManOrderInterface(pNew, p->pGia);
    Vec_IntFillExtra( vOffsets, Gia_ManObjNum(pNew), 0 );
    Vec_IntForEachEntry( vOffsets, Root, i )
        if ( Root ) Vec_IntAddToEntry( vOffsets, i, Gia_ManObjNum(pNew) );
    Vec_IntAppend( vOffsets, vMapping );
    pNew->vMapping = vOffsets;
    pNew->MappedArea = p->pPars->Area;
    pNew->MappedDelay = (int)p->pPars->Delay;
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p->pGia) );
cleanup:
    If3_RecipeClear( pRecipes );
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
static int If3_ComposeLeaf( If3_Man_t * p, If3_Cut_t * Root, int Pos, If3_Cut_t * Child, If3_Cut_t * Res )
{
    If3_Cut_t Base = *Root;
    word Zero = Abc_Tt6Cofactor0( Root->Truth, Pos ), One = Abc_Tt6Cofactor1( Root->Truth, Pos ), Select;
    unsigned M0, M1;
    int j;
    Base.nLeaves--;
    Base.Sign = 0;
    for ( j = Pos; j < Base.nLeaves; j++ ) Base.Leaves[j] = Base.Leaves[j + 1];
    for ( j = 0; j < Base.nLeaves; j++ ) Base.Sign |= If3_LeafSign( Base.Leaves[j] );
    if ( !If3_CutMerge( p, &Base, Child, Res ) ) return 0;
    for ( j = Pos; j < 5; j++ )
    {
        Zero = Abc_Tt6SwapVars( Zero, j, j + 1 );
        One = Abc_Tt6SwapVars( One, j, j + 1 );
    }
    M0 = (unsigned)Res->Truth & 63;
    M1 = (unsigned)( Res->Truth >> 6 );
    Zero = If3_Stretch( Zero, M0 );
    One = If3_Stretch( One, M0 );
    Select = If3_Stretch( Child->Truth, M1 );
    Res->Truth = ( Zero & ~Select ) | ( One & Select );
    Res->nLeaves = Abc_Tt6MinBase( &Res->Truth, Res->Leaves, Res->nLeaves );
    // Keep referenced LUT roots distinct from their leaves and the constant.
    if ( Res->nLeaves < 2 ) return 0;
    Res->Sign = 0;
    for ( j = 0; j < Res->nLeaves; j++ ) Res->Sign |= If3_LeafSign( Res->Leaves[j] );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Expands one selected LUT boundary without changing the AIG.]

  Description [Structural cuts compose by support union. Truth cuts additionally
  compose the functions, since minimized supports need not be structural cuts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_ExpandSelected( If3_Man_t * p, If3_Cut_t * Root, int Pos, If3_Cut_t * Child, If3_Cut_t * Res )
{
    If3_Cut_t Base;
    int j;
    if ( p->fTruth )
    {
        if ( !If3_ComposeLeaf(p, Root, Pos, Child, Res) ) return 0;
    }
    else
    {
        Base = *Root;
        Base.nLeaves--;
        Base.Sign = 0;
        for ( j = Pos; j < Base.nLeaves; j++ ) Base.Leaves[j] = Base.Leaves[j+1];
        for ( j = 0; j < Base.nLeaves; j++ ) Base.Sign |= If3_LeafSign(Base.Leaves[j]);
        if ( !If3_CutMerge(p, &Base, Child, Res) || Res->nLeaves < 2 ) return 0;
        Res->Truth = 0;
    }
    Res->Delay = 0;
    for ( j = 0; j < Res->nLeaves; j++ )
        Res->Delay = Abc_MaxFloat(Res->Delay, If3_ObjBest(p, Res->Leaves[j])->Delay);
    Res->Delay += 1;
    Res->Flow = 0;
    Res->Edge = (float)Res->nLeaves;
    return Res->Delay <= Root->Delay + IF3_EPSILON;
}

/**Function*************************************************************

  Synopsis    [Eliminates a shared LUT from all of its consumers together.]

  Description [Every replacement uses only leaves already present in the
  selected cover, so no new LUT can become live. Replacing the consumers
  atomically removes at least their common LUT. Snapshot fanout lists are
  checked against current references; newly added consumers defer a trial
  until the next pass. Output references prevent removal of output drivers.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_AbsorbShared( If3_Man_t * p )
{
    enum { IF3_ABSORB_FANOUTS = 32 };
    If3_Cut_t Cuts[IF3_ABSORB_FANOUTS], * Cut;
    Gia_Obj_t * Obj;
    int Fans[IF3_ABSORB_FANOUTS], * Starts, * Ends, * Edges;
    int i, k, j, Leaf, Root, nFans, nEdges = 0, Count = 0;
    int nObjs = Gia_ManObjNum(p->pGia), AreaBefore = p->pPars->Area;
    float Area, Edge, Delay;
    abctime clk = Abc_Clock();
    if ( p->pTim || Gia_ManBufNum(p->pGia) ) return 0;
    Gia_ManForEachAnd(p->pGia, Obj, i)
    {
        if ( p->pRefs[i] > INT_MAX - nEdges ) return 0;
        nEdges += p->pRefs[i];
    }
    Starts = ABC_ALLOC( int, nObjs );
    Ends = ABC_ALLOC( int, nObjs );
    Edges = ABC_ALLOC( int, nEdges );
    nEdges = 0;
    Gia_ManForEachObj(p->pGia, Obj, i)
    {
        Starts[i] = Ends[i] = nEdges;
        if ( Gia_ObjIsAnd(Obj) ) nEdges += p->pRefs[i];
    }
    Gia_ManForEachAnd(p->pGia, Obj, i)
    {
        if ( !p->pRefs[i] ) continue;
        Cut = If3_ObjBest(p, i);
        for ( k = 0; k < Cut->nLeaves; k++ )
        {
            Leaf = Cut->Leaves[k];
            if ( If3_ObjIsNode(p, Leaf) ) Edges[Ends[Leaf]++] = i;
        }
    }
    Gia_ManForEachAnd(p->pGia, Obj, i)
    {
        if ( !p->pRefs[i] || p->pRefs[i] > IF3_ABSORB_FANOUTS ) continue;
        nFans = 0;
        for ( j = Starts[i]; j < Ends[i]; j++ )
        {
            Root = Edges[j];
            if ( !p->pRefs[Root] ) continue;
            Cut = If3_ObjBest(p, Root);
            for ( k = 0; k < Cut->nLeaves && Cut->Leaves[k] != i; k++ ) {}
            if ( k == Cut->nLeaves ) continue;
            if ( !If3_ExpandSelected(p, Cut, k, If3_ObjBest(p, i), Cuts + nFans) ) break;
            Fans[nFans++] = Root;
        }
        if ( j != Ends[i] || nFans != p->pRefs[i] ) continue;
        // Pin consumer roots: one consumer may itself feed another, and its
        // old cut must not be recursively dereferenced a second time.
        for ( k = 0; k < nFans; k++ ) p->pRefs[Fans[k]]++;
        for ( k = 0; k < nFans; k++ ) If3_CutDeref(p, If3_ObjBest(p, Fans[k]));
        for ( k = 0; k < nFans; k++ )
        {
            *If3_ObjBest(p, Fans[k]) = Cuts[k];
            If3_CutRef(p, Cuts+k, 0, &Area, &Edge);
        }
        for ( k = 0; k < nFans; k++ )
            if ( --p->pRefs[Fans[k]] == 0 ) If3_CutDeref(p, If3_ObjBest(p, Fans[k]));
        assert( p->pRefs[i] == 0 );
        Count++;
    }
    // Absorption never raises an arrival; refresh exact values for export.
    Gia_ManForEachAnd(p->pGia, Obj, i)
    {
        if ( p->pSkip[i] ) continue;
        Cut = If3_ObjBest(p, i);
        Delay = 0;
        for ( k = 0; k < Cut->nLeaves; k++ )
            Delay = Abc_MaxFloat(Delay, If3_ObjBest(p, Cut->Leaves[k])->Delay);
        Cut->Delay = Delay + (float)(Cut->nLeaves > 1);
    }
    If3_ManRequired(p);
    assert( p->pPars->Area <= AreaBefore - Count );
    if ( p->pPars->fVerbose )
        Abc_Print(1, "If3 shared absorption: %d removed  LUT = %d  Delay = %.2f  Time = %.3f sec\n",
                  Count, p->pPars->Area, p->pPars->Delay, 1.0 * (Abc_Clock() - clk) / CLOCKS_PER_SEC);
    ABC_FREE( Starts );
    ABC_FREE( Ends );
    ABC_FREE( Edges );
    return Count;
}

/**Function*************************************************************

  Synopsis    [Removes redundant LUT boundaries after exact-area recovery.]

  Description [Accept strictly smaller area, or equal area with lower delay. Each root
  has a fixed iteration bound, and no accepted cut increases its arrival.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_InlineCover( If3_Man_t * p )
{
    Gia_Obj_t * Obj;
    If3_Cut_t Old, Best, Cut, *Child, *Current;
    int Id, i, k, Iter, Count = 0, Trials = 0;
    float Area, Edge;
    if ( !p->fTruth || !Gia_ManHasChoices( p->pGia ) || p->pTim ) return;
    p->Mode = 2;
    Gia_ManForEachAnd ( p->pGia, Obj, Id )
    {
        if ( !p->pRefs[Id] ) continue;
        Current = If3_ObjBest( p, Id );
        for ( Iter = 0; Iter < 4; Iter++ )
        {
            Old = *Current;
            If3_CutDeref( p, &Old );
            p->fExact = 1;
            Best = Old;
            If3_CutScore( p, &Best );
            for ( i = 0; i < Old.nLeaves; i++ )
            {
                int Leaf = Old.Leaves[i];
                if ( !If3_ObjIsNode( p, Leaf ) ) continue;
                for ( k = 0; k < p->pPars->nCutsMax + 1; k++ )
                {
                    if ( k && k > p->pCounts[Leaf] ) break;
                    Child = k ? If3_ObjCuts( p, Leaf ) + k - 1 : If3_ObjBest( p, Leaf );
                    if ( !If3_ComposeLeaf( p, &Old, i, Child, &Cut ) ) continue;
                    Trials++;
                    If3_CutScore( p, &Cut );
                    if ( Cut.Delay > Old.Delay + IF3_EPSILON ) continue;
                    if ( Cut.Flow < Best.Flow - IF3_EPSILON ||
                         ( Cut.Flow == Best.Flow && Cut.Delay < Best.Delay - IF3_EPSILON ) )
                        Best = Cut;
                }
            }
            *Current = Best;
            If3_CutRef( p, Current, 0, &Area, &Edge );
            if ( Current->nLeaves == Old.nLeaves && !memcmp( Current->Leaves, Old.Leaves, Old.nLeaves * sizeof( int ) ) )
                break;
            Count++;
        }
    }
    If3_ManRequired( p );
    if ( p->pPars->fVerbose ) Abc_Print( 1, "If3 cover composition: %d accepted, %d trials\n", Count, Trials );
}

enum { IF3_PACK_NODES = 8, IF3_PACK_VARS = 11, IF3_PACK_WORDS = 32,
       IF3_PACK_BINS = 16384, IF3_PACK_LIMIT = IF3_PACK_BINS / 2 };

typedef struct If3_Lut_t_ If3_Lut_t;
struct If3_Lut_t_
{
    word Truth;
    int Fans[6];
    int nFans, Refs, Level, Required, Next, Dead;
};

typedef struct If3_PackEntry_t_ If3_PackEntry_t;
struct If3_PackEntry_t_
{
    word Truth[IF3_PACK_WORDS];
    unsigned char Dec[128];
    unsigned short Late;
    unsigned char nVars, Used;
};

typedef struct If3_Pack_t_ If3_Pack_t;
struct If3_Pack_t_
{
    If3_Lut_t * Luts;
    If3_PackEntry_t * Cache;
    If3_Recipe_t * Recipes;
    Vec_Int_t * Order, * Cover, * Release;
    Vec_Wrd_t * Scratch;
    int nObjs, nCap, nCis, nLuts, nRecipes, nCache, K;
    int Trials, Hits, Changes, Saved, Shared;
    int * HashBins, * Aliases;
    int nHashBins, ResubHits;
    int * FanHeads, * Slots;
    unsigned * Seen, Stamp;
    Vec_Int_t * FanEdges;
    // Elementary tables are initialized once and only read by local programs.
    word Vars[IF3_PACK_VARS][IF3_PACK_WORDS], Zero[IF3_PACK_WORDS];
};

/**Function*************************************************************

  Synopsis    [Finds a node in a bounded local list.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackHas( int * A, int N, int Value )
{
    int i;
    for ( i = 0; i < N; i++ ) if ( A[i] == Value ) return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Expands a mapped cone without crossing shared nodes.]

  Description [Every expanded node has all live fanouts in the window.
  The boundary order is structural, not global object ID.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackExpand( If3_Pack_t * p, int * Nodes, int * pnNodes,
                           int * Leaves, int * pnLeaves )
{
    int Test[IF3_PACK_VARS+6], Best[IF3_PACK_VARS], BestSize = 100, BestPos = -1;
    int i, j, k, Id, Count, N, Leaf, Total;
    If3_Lut_t * Lut;
    for ( i = 0; i < *pnLeaves; i++ )
    {
        Id = Leaves[i];
        if ( Id <= p->nCis || !p->Luts[Id].Refs || If3_PackHas(Nodes, *pnNodes, Id) >= 0 ) continue;
        Count = 0;
        for ( j = 0; j < *pnNodes; j++ )
            for ( k = 0; k < p->Luts[Nodes[j]].nFans; k++ )
                Count += p->Luts[Nodes[j]].Fans[k] == Id;
        if ( Count != p->Luts[Id].Refs ) continue;
        for ( j = N = 0; j < *pnLeaves; j++ )
            if ( Leaves[j] != Id && If3_PackHas(Test, N, Leaves[j]) < 0 ) Test[N++] = Leaves[j];
        Lut = p->Luts + Id;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            Leaf = Lut->Fans[j];
            if ( If3_PackHas(Nodes, *pnNodes, Leaf) >= 0 || If3_PackHas(Test, N, Leaf) >= 0 ) continue;
            Test[N++] = Leaf;
        }
        Total = N;
        if ( Total > IF3_PACK_VARS || Total >= BestSize ) continue;
        BestSize = Total;
        BestPos = i;
        memcpy(Best, Test, sizeof(int)*N);
    }
    if ( BestPos < 0 ) return 0;
    Nodes[(*pnNodes)++] = Leaves[BestPos];
    *pnLeaves = BestSize;
    memcpy(Leaves, Best, sizeof(int)*BestSize);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns an elementary truth-table word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If3_PackVariable( int Var, int Word )
{
    static const word Vars[6] = { ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000) };
    return Var < 6 ? Vars[Var] : ((Word >> (Var-6)) & 1) ? ~(word)0 : 0;
}

/**Function*************************************************************

  Synopsis    [Evaluates a factored LUT on one word of assignments.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If3_PackEval( If3_Pack_t * p, word Truth, int nFans, word * Values )
{
    Kit_Graph_t * Graph = If3_RecipeFind(p->Recipes, &p->nRecipes, Truth, nFans, p->Cover);
    Kit_Node_t * Node;
    word * Data, a, b;
    int i;
    assert(Graph != NULL);
    if ( Kit_GraphIsConst(Graph) ) return Kit_GraphIsConst1(Graph) ? ~(word)0 : 0;
    Vec_WrdGrow(p->Scratch, Graph->nSize);
    Data = Vec_WrdArray(p->Scratch);
    for ( i = 0; i < nFans; i++ ) Data[i] = Values[i];
    Kit_GraphForEachNode(Graph, Node, i)
    {
        a = Data[Node->eEdge0.Node];
        b = Data[Node->eEdge1.Node];
        Data[i] = (Node->eEdge0.fCompl ? ~a : a) & (Node->eEdge1.fCompl ? ~b : b);
    }
    a = Data[Graph->eRoot.Node];
    return Graph->eRoot.fCompl ? ~a : a;
}

/**Function*************************************************************

  Synopsis    [Evaluates a small truth table without constructing a recipe.]

  Description [The lowest variable selects one of four elementary words.
  Shannon composition merges the remaining pairs in place. Transient care
  derivatives therefore do not displace cached recipes for mapped LUTs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If3_PackEvalDirect( word Truth, int nFans, word * Inputs )
{
    word Work[32], Base[4];
    int i, v, n;
    if ( Truth == 0 || Truth == ~(word)0 ) return Truth;
    assert(nFans > 0 && nFans <= 6);
    Base[0] = 0;
    Base[1] = ~Inputs[0];
    Base[2] = Inputs[0];
    Base[3] = ~(word)0;
    n = 1 << (nFans-1);
    for ( i = 0; i < n; i++ ) Work[i] = Base[(Truth >> (2*i)) & 3];
    for ( v = 1; v < nFans; v++ )
    {
        n >>= 1;
        for ( i = 0; i < n; i++ )
            Work[i] = Work[2*i] ^ ((Work[2*i] ^ Work[2*i+1]) & Inputs[v]);
    }
    return Work[0];
}

/**Function*************************************************************

  Synopsis    [Evaluates a factored LUT across all local assignments.]

  Description [Bindings, recipe lookup, and edge polarities are resolved
  once per LUT rather than once per truth-table word.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackEvalWords( If3_Pack_t * p, word Truth, int nFans, word ** Inputs, int nWords, word * Output )
{
    Kit_Graph_t * Graph = If3_RecipeFind(p->Recipes, &p->nRecipes, Truth, nFans, p->Cover);
    Kit_Node_t * Node;
    word * Data, * a, * b, * c, x, y;
    int i, w;
    assert(Graph != NULL);
    if ( Kit_GraphIsConst(Graph) )
    {
        x = Kit_GraphIsConst1(Graph) ? ~(word)0 : 0;
        for ( w = 0; w < nWords; w++ ) Output[w] = x;
        return;
    }
    Vec_WrdGrow(p->Scratch, Graph->nSize*nWords);
    Data = Vec_WrdArray(p->Scratch);
    for ( i = 0; i < nFans; i++ ) memcpy(Data+i*nWords, Inputs[i], sizeof(word)*nWords);
    Kit_GraphForEachNode(Graph, Node, i)
    {
        a = Data+Node->eEdge0.Node*nWords;
        b = Data+Node->eEdge1.Node*nWords;
        c = Data+i*nWords;
        x = Node->eEdge0.fCompl ? ~(word)0 : 0;
        y = Node->eEdge1.fCompl ? ~(word)0 : 0;
        for ( w = 0; w < nWords; w++ ) c[w] = (a[w]^x) & (b[w]^y);
    }
    a = Data+Graph->eRoot.Node*nWords;
    x = Graph->eRoot.fCompl ? ~(word)0 : 0;
    for ( w = 0; w < nWords; w++ ) Output[w] = a[w]^x;
}

/**Function*************************************************************

  Synopsis    [Computes the complete function of a bounded LUT cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackTruth( If3_Pack_t * p, int * Nodes, int nNodes, int * Leaves, int nLeaves, word * Truth )
{
    word Values[IF3_PACK_NODES][IF3_PACK_WORDS], * Inputs[6];
    unsigned Done = 0;
    int Pass, i, k, Pos, nWords = Abc_TtWordNum(nLeaves);
    If3_Lut_t * Lut;
    assert(nNodes > 0 && nNodes <= IF3_PACK_NODES);
    for ( Pass = 0; Pass < nNodes; Pass++ )
        for ( i = 0; i < nNodes; i++ )
        {
            if ( Done & (1u<<i) ) continue;
            Lut = p->Luts+Nodes[i];
            for ( k = 0; k < Lut->nFans; k++ )
            {
                Pos = If3_PackHas(Nodes, nNodes, Lut->Fans[k]);
                if ( Pos >= 0 )
                {
                    if ( !(Done & (1u<<Pos)) ) break;
                    Inputs[k] = Values[Pos];
                }
                else
                {
                    Pos = If3_PackHas(Leaves, nLeaves, Lut->Fans[k]);
                    assert(Pos >= 0);
                    Inputs[k] = p->Vars[Pos];
                }
            }
            if ( k < Lut->nFans ) continue;
            If3_PackEvalWords(p, Lut->Truth, Lut->nFans, Inputs, nWords, Values[i]);
            Done |= 1u<<i;
        }
    assert(Done == (1u<<nNodes)-1);
    memcpy(Truth, Values[0], sizeof(word)*nWords);
    return nWords;
}

/**Function*************************************************************

  Synopsis    [Caches delay-aware decomposition of complete functions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static If3_PackEntry_t * If3_PackDecompose( If3_Pack_t * p, word * Truth, int nVars, unsigned Late )
{
    If3_PackEntry_t * Entry;
    word Hash = nVars + 257u * Late;
    unsigned Profile = Late;
    int w, nWords = Abc_TtWordNum(nVars), Bin;
    p->Trials++;
    for ( w = 0; w < nWords; w++ ) Hash = (Hash ^ Truth[w]) * ABC_CONST(0x9e3779b97f4a7c15);
    Bin = (int)((Hash ^ (Hash >> 32)) & (IF3_PACK_BINS-1));
    while ( p->Cache[Bin].Used )
    {
        Entry = p->Cache + Bin;
        if ( Entry->nVars == nVars && Entry->Late == Late && !memcmp(Entry->Truth, Truth, sizeof(word)*nWords) )
        {
            p->Hits++;
            return Entry;
        }
        Bin = (Bin+1) & (IF3_PACK_BINS-1);
    }
    if ( p->nCache == IF3_PACK_LIMIT )
    {
        memset(p->Cache, 0, sizeof(If3_PackEntry_t)*IF3_PACK_BINS);
        p->nCache = 0;
        Bin = (int)((Hash ^ (Hash >> 32)) & (IF3_PACK_BINS-1));
    }
    Entry = p->Cache + Bin;
    Entry->Used = 1;
    Entry->nVars = (unsigned char)nVars;
    Entry->Late = (unsigned short)Late;
    memcpy(Entry->Truth, Truth, sizeof(word)*nWords);
    memset(Entry->Dec, 0, sizeof(Entry->Dec));
    p->nCache++;
    // Prefer a two-LUT decomposition before the general multi-LUT search.
    // The specialized routine requires more than four input variables.
    if ( nVars <= 4 || nVars >= 2*p->K || acd2_decompose(Truth, nVars, p->K, &Profile, Entry->Dec) < 0 )
    {
        Profile = Late;
        if ( acd_decompose(Truth, nVars, p->K, &Profile, Entry->Dec) < 0 ) Entry->Dec[1] = 0;
    }
    return Entry;
}

/**Function*************************************************************

  Synopsis    [Hashes a LUT function and its ordered inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned If3_PackHash( If3_Lut_t * Lut )
{
    word Truth = (Lut->Truth & 1) ? ~Lut->Truth : Lut->Truth;
    unsigned Hash = (unsigned)(Truth ^ (Truth >> 32)) + 127u*Lut->nFans;
    int i;
    for ( i = 0; i < Lut->nFans; i++ ) Hash = (Hash ^ (unsigned)Lut->Fans[i])*12582917u;
    return Hash;
}

/**Function*************************************************************

  Synopsis    [Orders LUT inputs while permuting the truth table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackSort( If3_Lut_t * Lut )
{
    int i, j, Temp;
    for ( i = 1; i < Lut->nFans; i++ )
        for ( j = i; j > 0 && Lut->Fans[j-1] > Lut->Fans[j]; j-- )
        {
            Temp = Lut->Fans[j-1];
            Lut->Fans[j-1] = Lut->Fans[j];
            Lut->Fans[j] = Temp;
            Lut->Truth = Abc_Tt6SwapVars(Lut->Truth, j-1, j);
        }
}

/**Function*************************************************************

  Synopsis    [Finds an equivalent completed LUT outside the replaced cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackLookup( If3_Pack_t * p, If3_Lut_t * Lut, int * Nodes, int nNodes )
{
    If3_Lut_t * Test;
    int Id, Phase;
    unsigned Hash = If3_PackHash(Lut) & (p->nHashBins-1);
    for ( Id = p->HashBins[Hash]; Id; Id = p->Luts[Id].Next )
    {
        Test = p->Luts+Id;
        if ( !Test->Refs || Test->nFans != Lut->nFans || If3_PackHas(Nodes, nNodes, Id) >= 0 ) continue;
        Phase = (int)((Test->Truth ^ Lut->Truth) & 1);
        if ( Test->Truth != (Phase ? ~Lut->Truth : Lut->Truth) || memcmp(Test->Fans, Lut->Fans, sizeof(int)*Lut->nFans) ) continue;
        return Abc_Var2Lit(Id, Phase);
    }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Registers a completed LUT for sharing and divisor discovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackFinish( If3_Pack_t * p, int Id )
{
    If3_Lut_t * Lut = p->Luts+Id;
    unsigned Hash;
    if ( Lut->nFans < 2 ) return;
    If3_PackSort(Lut);
    Hash = If3_PackHash(Lut) & (p->nHashBins-1);
    Lut->Next = p->HashBins[Hash];
    p->HashBins[Hash] = Id;
    {
        int j, Fan, Offset;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            Fan = Lut->Fans[j];
            Offset = Vec_IntSize(p->FanEdges);
            Vec_IntPushTwo(p->FanEdges, Id, p->FanHeads[Fan]);
            p->FanHeads[Fan] = Offset;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Removes constant, duplicate, and vacuous LUT inputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackSimplify( If3_Lut_t * Lut )
{
    word Zero, One, Select;
    int i, j;
    for ( i = 0; i < Lut->nFans; i++ )
    {
        if ( Lut->Fans[i] == 0 ) Lut->Truth = Abc_Tt6Cofactor0(Lut->Truth, i);
        for ( j = 0; j < i; j++ )
            if ( Lut->Fans[j] == Lut->Fans[i] )
            {
                Zero = Abc_Tt6Cofactor0(Lut->Truth, i);
                One = Abc_Tt6Cofactor1(Lut->Truth, i);
                Select = If3_PackVariable(j, 0);
                Lut->Truth = (Zero & ~Select) | (One & Select);
                break;
            }
    }
    Lut->nFans = Abc_Tt6MinBase(&Lut->Truth, Lut->Fans, Lut->nFans);
    return Lut->nFans >= 2;
}

/**Function*************************************************************

  Synopsis    [Reuses existing LUTs in a proposed decomposition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackShare( If3_Pack_t * p, If3_Lut_t * Proposed, int nNew, int * Nodes, int nNodes )
{
    If3_Lut_t Lut;
    int Remap[8], i, j, Id, Lit, N = 0;
    for ( i = 0; i < nNew; i++ )
    {
        Lut = Proposed[i];
        for ( j = 0; j < Lut.nFans; j++ )
        {
            Id = Lut.Fans[j];
            if ( Id < p->nObjs ) continue;
            assert(Id-p->nObjs < i);
            Lit = Remap[Id-p->nObjs];
            Lut.Fans[j] = Abc_Lit2Var(Lit);
            if ( Abc_LitIsCompl(Lit) ) Lut.Truth = Abc_Tt6Flip(Lut.Truth, j);
        }
        if ( !If3_PackSimplify(&Lut) ) return -1;
        If3_PackSort(&Lut);
        if ( i < nNew-1 && (Lit = If3_PackLookup(p, &Lut, Nodes, nNodes)) >= 0 )
        {
            Remap[i] = Lit;
            p->Shared++;
            continue;
        }
        Lut.Level = 0;
        for ( j = 0; j < Lut.nFans; j++ )
        {
            Id = Lut.Fans[j];
            Lut.Level = Abc_MaxInt(Lut.Level, Id < p->nObjs ? p->Luts[Id].Level : Proposed[Id-p->nObjs].Level);
        }
        Lut.Level++;
        Remap[i] = Abc_Var2Lit(p->nObjs+N, 0);
        Proposed[N++] = Lut;
    }
    return N;
}

typedef struct If3_PackPlan_t_ If3_PackPlan_t;
struct If3_PackPlan_t_
{
    If3_Lut_t Proposed[8];
    int Nodes[IF3_PACK_NODES];
    int nNodes, nNew;
};

/**Function*************************************************************

  Synopsis    [Proves a one-divisor substitution over every boundary assignment.]

  Description [A divisor is usable when each tuple of its value and the
  selected free variables determines the root. Complete enumeration of
  the boundary assignments provides an exact local functional proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackDivisor( If3_Pack_t * p, int Root, int Div, word * RootTruth, word * DivTruth,
                            unsigned Support, int * Nodes, int nNodes, int * Leaves, int nVars,
                            If3_PackPlan_t * Best )
{
    word R[32], G[32], Inputs[6], Truth, a, b, Mask, Check;
    If3_Lut_t Lut;
    unsigned Bound;
    int Order[11], Perm[11], nBound = nVars-(p->K-1), Words = Abc_TtWordNum(nVars);
    int i, j, k, N, Row, Shift, Bits, Index, Code, Tries = 0;
    if ( nBound < 1 || nBound > 6 || p->Luts[Div].Level+1 > p->Luts[Root].Required ) return 0;
    for ( Bound = Support; Bound; Bound = (Bound-1)&Support )
    {
        if ( Abc_TtCountOnes((word)Bound) != nBound ) continue;
        if ( ++Tries > 32 ) break;
        for ( i = N = 0; i < nVars; i++ ) if ( Bound & (1u<<i) ) Order[N++] = i;
        for ( i = 0; i < nVars; i++ ) if ( !(Bound & (1u<<i)) ) Order[N++] = i;
        memcpy(R, RootTruth, sizeof(word)*Words);
        memcpy(G, DivTruth, sizeof(word)*Words);
        for ( i = 0; i < nVars; i++ ) Perm[i] = i;
        for ( i = 0; i < nBound; i++ )
        {
            for ( j = i; Perm[j] != Order[i]; j++ ) {}
            if ( j == i ) continue;
            Abc_TtSwapVars(R, nVars, i, j);
            Abc_TtSwapVars(G, nVars, i, j);
            k = Perm[i]; Perm[i] = Perm[j]; Perm[j] = k;
        }
        // The unbound variables may have moved during these swaps.
        for ( i = nBound; i < nVars; i++ ) Order[i] = Perm[i];
        Bits = 1 << nBound;
        Mask = Bits == 64 ? ~(word)0 : (((word)1)<<Bits)-1;
        Truth = 0;
        for ( Row = 0; Row < (1 << (p->K-1)); Row++ )
        {
            Index = (Row*Bits) >> 6;
            Shift = (Row*Bits) & 63;
            a = (R[Index] >> Shift) & Mask;
            b = (G[Index] >> Shift) & Mask;
            if ( a == 0 ) Code = 0;
            else if ( a == Mask ) Code = 3;
            else if ( a == b ) Code = 2;
            else if ( a == (b ^ Mask) ) Code = 1;
            else break;
            Truth |= (word)Code << (2*Row);
        }
        if ( Row < (1 << (p->K-1)) ) continue;
        memset(&Lut, 0, sizeof(Lut));
        Lut.Truth = Abc_Tt6Stretch(Truth, p->K);
        Lut.Fans[0] = Div;
        Lut.Level = p->Luts[Div].Level;
        for ( i = nBound; i < nVars; i++ )
        {
            Lut.Fans[1+i-nBound] = Leaves[Order[i]];
            Lut.Level = Abc_MaxInt(Lut.Level, p->Luts[Leaves[Order[i]]].Level);
        }
        Lut.Level++;
        Lut.nFans = p->K;
        if ( Lut.Level > p->Luts[Root].Required ) continue;
        for ( i = 0; i < Words; i++ )
        {
            Inputs[0] = DivTruth[i];
            for ( j = nBound; j < nVars; j++ ) Inputs[1+j-nBound] = If3_PackVariable(Order[j], i);
            Check = If3_PackEval(p, Lut.Truth, Lut.nFans, Inputs);
            assert(Check == RootTruth[i]);
        }
        Lut.nFans = Abc_Tt6MinBase(&Lut.Truth, Lut.Fans, Lut.nFans);
        if ( Lut.nFans < 2 ) continue;
        if ( nNodes-1 < Best->nNodes-Best->nNew ||
             (nNodes-1 == Best->nNodes-Best->nNew && Best->nNew && Lut.Level >= Best->Proposed[Best->nNew-1].Level) ) continue;
        If3_PackSort(&Lut);
        Best->nNodes = nNodes;
        Best->nNew = 1;
        Best->Proposed[0] = Lut;
        memcpy(Best->Nodes, Nodes, sizeof(int)*nNodes);
        p->ResubHits++;
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Finds available functional divisors of a local cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackResub( If3_Pack_t * p, int Root, word * Truth, int * Nodes, int nNodes,
                           int * Leaves, int nLeaves, If3_PackPlan_t * Best )
{
    enum { IF3_PACK_DIVS = 40, IF3_PACK_EDGES = 512 };
    word Values[IF3_PACK_DIVS][32], * Inputs[6];
    unsigned Support[IF3_PACK_DIVS];
    int Ids[IF3_PACK_DIVS], Count = 0, nEdges = 0, Pos, Edge, Id, i, j, w, Known;
    int Words = Abc_TtWordNum(nLeaves);
    If3_Lut_t * Lut;
    if ( nLeaves <= p->K || nNodes-1 < Best->nNodes-Best->nNew ) return;
    if ( ++p->Stamp == 0 ) { memset(p->Seen, 0, sizeof(unsigned)*p->nCap); p->Stamp = 1; }
    for ( i = 0; i < nLeaves; i++ )
    {
        Id = Ids[Count++] = Leaves[i];
        p->Seen[Id] = p->Stamp;
        p->Slots[Id] = i;
        Support[i] = 1u << i;
        for ( w = 0; w < Words; w++ ) Values[i][w] = If3_PackVariable(i, w);
    }
    for ( Pos = 0; Pos < Count && Count < IF3_PACK_DIVS; Pos++ )
        for ( Edge = p->FanHeads[Ids[Pos]]; Edge && Count < IF3_PACK_DIVS; Edge = Vec_IntEntry(p->FanEdges, Edge+1) )
        {
            if ( ++nEdges > IF3_PACK_EDGES ) return;
            Id = Vec_IntEntry(p->FanEdges, Edge);
            Lut = p->Luts+Id;
            if ( !Lut->Refs || p->Seen[Id] == p->Stamp || If3_PackHas(Nodes, nNodes, Id) >= 0 ) continue;
            for ( j = 0; j < Lut->nFans; j++ ) if ( p->Seen[Lut->Fans[j]] != p->Stamp ) break;
            if ( j < Lut->nFans ) continue;
            Known = Count++;
            Ids[Known] = Id;
            p->Seen[Id] = p->Stamp;
            p->Slots[Id] = Known;
            Support[Known] = 0;
            for ( j = 0; j < Lut->nFans; j++ ) Support[Known] |= Support[p->Slots[Lut->Fans[j]]];
            for ( j = 0; j < Lut->nFans; j++ ) Inputs[j] = Values[p->Slots[Lut->Fans[j]]];
            If3_PackEvalWords(p, Lut->Truth, Lut->nFans, Inputs, Words, Values[Known]);
            If3_PackDivisor(p, Root, Id, Truth, Values[Known], Support[Known], Nodes, nNodes, Leaves, nLeaves, Best);
        }
}

/**Function*************************************************************

  Synopsis    [Selects a nonincreasing-area implementation of a complete function.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackTryTruth( If3_Pack_t * p, int Root, int * Nodes, int nNodes, int * Leaves, int nLeaves, word * Truth, If3_PackPlan_t * Best )
{
    word Check[8][IF3_PACK_WORDS], Inputs[6], Value;
    unsigned Late = 0;
    unsigned char * Dec;
    If3_PackEntry_t * Entry = NULL;
    If3_Lut_t Proposed[8], * Lut;
    int Ids[IF3_PACK_VARS+8], Req = p->Luts[Root].Required;
    int i, j, k, w, Pos, Bytes, nNew;
    nLeaves = Abc_TtMinBase(Truth, Leaves, nLeaves, nLeaves);
    if ( nLeaves < 2 ) return 0;
    for ( i = 0; i < nLeaves; i++ )
    {
        if ( p->Luts[Leaves[i]].Level > Req-1 ) return 0;
        if ( p->Luts[Leaves[i]].Level > Req-2 ) Late |= 1u << i;
    }
    If3_PackResub(p, Root, Truth, Nodes, nNodes, Leaves, nLeaves, Best);
    memset(Proposed, 0, sizeof(Proposed));
    if ( nLeaves <= p->K )
    {
        nNew = 1;
        Proposed[0].Truth = Truth[0];
        Proposed[0].nFans = nLeaves;
        memcpy(Proposed[0].Fans, Leaves, sizeof(int)*nLeaves);
    }
    else
    {
        Entry = If3_PackDecompose(p, Truth, nLeaves, Late);
        Dec = Entry->Dec;
        nNew = Dec[1];
        if ( !nNew || nNew > 3 ) return 0;
        memcpy(Ids, Leaves, sizeof(int)*nLeaves);
        for ( i = 0, Pos = 2; i < nNew; i++ )
        {
            Lut = Proposed + i;
            Lut->nFans = Dec[Pos++];
            assert(Lut->nFans >= 2 && Lut->nFans <= p->K);
            for ( j = 0; j < Lut->nFans; j++ )
            {
                k = Dec[Pos++];
                assert(k < nLeaves+i);
                Lut->Fans[j] = Ids[k];
            }
            Bytes = Lut->nFans <= 3 ? 1 : 1 << (Lut->nFans-3);
            Value = 0;
            for ( j = 0; j < Bytes; j++ ) Value |= (word)Dec[Pos++] << (8*j);
            if ( Lut->nFans < 6 ) Value &= (((word)1) << (1 << Lut->nFans))-1;
            for ( j = 1 << Lut->nFans; j < 64; j *= 2 ) Value |= Value << j;
            Lut->Truth = Value;
            Ids[nLeaves+i] = i == nNew-1 ? Root : p->nObjs+i;
        }
        assert(Pos == Dec[0]);
    }
    for ( i = 0; i < nNew; i++ )
    {
        Lut = Proposed + i;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            k = Lut->Fans[j];
            Lut->Level = Abc_MaxInt(Lut->Level, k < p->nObjs ? p->Luts[k].Level : Proposed[k-p->nObjs].Level);
        }
        Lut->Level++;
    }
    if ( Proposed[nNew-1].Level > Req ) return 0;
    // The cache key includes the complete function and input count. Once
    // independently verified, its symbolic decomposition is valid for every
    // subsequent renaming of the same distinct boundary leaves.
    if ( Entry && !(Entry->Used & 2) )
    {
        for ( i = 0; i < nNew; i++ )
            for ( w = 0; w < Abc_TtWordNum(nLeaves); w++ )
            {
                Lut = Proposed + i;
                for ( j = 0; j < Lut->nFans; j++ )
                {
                    k = Lut->Fans[j];
                    if ( k >= p->nObjs ) Inputs[j] = Check[k-p->nObjs][w];
                    else
                    {
                        Pos = If3_PackHas(Leaves, nLeaves, k);
                        assert(Pos >= 0);
                        Inputs[j] = If3_PackVariable(Pos, w);
                    }
                }
                Check[i][w] = If3_PackEval(p, Lut->Truth, Lut->nFans, Inputs);
            }
        if ( memcmp(Check[nNew-1], Truth, sizeof(word)*Abc_TtWordNum(nLeaves)) )
        {
            Entry->Dec[1] = 0;
            return 0;
        }
        Entry->Used |= 2;
    }
    // Count new LUTs after reuse: a larger decomposition may still save area.
    nNew = If3_PackShare(p, Proposed, nNew, Nodes, nNodes);
    if ( nNew < 1 || nNew > nNodes ) return 0;
    if ( nNew == nNodes )
    {
        int OldEdges = 0, NewEdges = 0;
        for ( i = 0; i < nNodes; i++ ) OldEdges += p->Luts[Nodes[i]].nFans;
        for ( i = 0; i < nNew; i++ ) NewEdges += Proposed[i].nFans;
        if ( NewEdges > OldEdges || (NewEdges == OldEdges && Proposed[nNew-1].Level >= p->Luts[Root].Level) ) return 0;
    }
    if ( Proposed[nNew-1].Level > Req ) return 0;
    if ( nNodes-nNew < Best->nNodes-Best->nNew ||
         (nNodes-nNew == Best->nNodes-Best->nNew && Best->nNew &&
          Proposed[nNew-1].Level >= Best->Proposed[Best->nNew-1].Level) ) return 0;
    Best->nNodes = nNodes;
    Best->nNew = nNew;
    memcpy(Best->Nodes, Nodes, sizeof(int)*nNodes);
    memcpy(Best->Proposed, Proposed, sizeof(If3_Lut_t)*nNew);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Constrains a window by exact functions among its boundary.]

  Description [Only relations whose complete fanin list is on the boundary
  are used. Other boundary signals remain independent, so the result is an
  overapproximation of all reachable assignments. No SAT calls are needed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackRelations( If3_Pack_t * p, int * Leaves, int nLeaves, word * Care )
{
    word Values[IF3_PACK_WORDS], * Inputs[6];
    unsigned Relations = 0;
    int i, j, w, Pos, Words = Abc_TtWordNum(nLeaves);
    If3_Lut_t * Lut;
    for ( i = 0; i < nLeaves; i++ )
    {
        if ( Leaves[i] == 0 ) { Relations |= 1u << i; continue; }
        if ( Leaves[i] <= p->nCis ) continue;
        Lut = p->Luts+Leaves[i];
        for ( j = 0; j < Lut->nFans; j++ )
            if ( Lut->Fans[j] && If3_PackHas(Leaves, nLeaves, Lut->Fans[j]) < 0 ) break;
        if ( j == Lut->nFans ) Relations |= 1u << i;
    }
    if ( !Relations ) return 0;
    for ( w = 0; w < Words; w++ ) Care[w] = ~(word)0;
    for ( i = 0; i < nLeaves; i++ )
        if ( Relations & (1u << i) )
        {
            if ( Leaves[i] == 0 )
            {
                for ( w = 0; w < Words; w++ ) Care[w] &= ~p->Vars[i][w];
                continue;
            }
            Lut = p->Luts+Leaves[i];
            for ( j = 0; j < Lut->nFans; j++ )
            {
                Pos = If3_PackHas(Leaves, nLeaves, Lut->Fans[j]);
                assert(Pos >= 0 || Lut->Fans[j] == 0);
                Inputs[j] = Lut->Fans[j] ? p->Vars[Pos] : p->Zero;
            }
            If3_PackEvalWords(p, Lut->Truth, Lut->nFans, Inputs, Words, Values);
            for ( w = 0; w < Words; w++ ) Care[w] &= ~(p->Vars[i][w] ^ Values[w]);
        }
    assert(!Abc_TtIsConst0(Care, Words));
    return !Abc_TtIsConst1(Care, Words);
}

/**Function*************************************************************

  Synopsis    [Tries complete and care-preserving window factorizations.]

  Description [A variable is removable when projecting it creates no
  on/off collision. Both completions preserve every reachable assignment.
  Boundary functions stay unchanged by the replacement. Skip extra trials
  when the incumbent already saves the maximum for this window.
  All accepted plans keep the delay bound.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackTry( If3_Pack_t * p, int Root, int * Nodes, int nNodes, int * Leaves, int nLeaves, If3_PackPlan_t * Best )
{
    word Truth[IF3_PACK_WORDS], Care[IF3_PACK_WORDS], Copy[IF3_PACK_WORDS];
    word On[IF3_PACK_WORDS], Off[IF3_PACK_WORDS];
    word On0[IF3_PACK_WORDS], On1[IF3_PACK_WORDS], Off0[IF3_PACK_WORDS], Off1[IF3_PACK_WORDS];
    int SavedLeaves[IF3_PACK_VARS], i, w, Words = Abc_TtWordNum(nLeaves), Result;
    memcpy(SavedLeaves, Leaves, sizeof(int)*nLeaves);
    If3_PackTruth(p, Nodes, nNodes, Leaves, nLeaves, Truth);
    memcpy(Copy, Truth, sizeof(word)*Words);
    Result = If3_PackTryTruth(p, Root, Nodes, nNodes, Leaves, nLeaves, Copy, Best);
    memcpy(Leaves, SavedLeaves, sizeof(int)*nLeaves);
    if ( Best->nNodes-Best->nNew >= nNodes-1 || !If3_PackRelations(p, Leaves, nLeaves, Care) ) return Result;
    for ( w = 0; w < Words; w++ ) { On[w] = Truth[w] & Care[w]; Off[w] = ~Truth[w] & Care[w]; }
    for ( i = nLeaves-1; i >= 0; i-- )
    {
        Abc_TtCofactor0p(On0, On, Words, i);
        Abc_TtCofactor1p(On1, On, Words, i);
        Abc_TtCofactor0p(Off0, Off, Words, i);
        Abc_TtCofactor1p(Off1, Off, Words, i);
        for ( w = 0; w < Words; w++ )
            if ( (On0[w] & Off1[w]) | (On1[w] & Off0[w]) ) break;
        if ( w < Words ) continue;
        for ( w = 0; w < Words; w++ ) { On[w] = On0[w] | On1[w]; Off[w] = Off0[w] | Off1[w]; }
    }
    assert(Abc_TtEqualCare(On, Truth, Care, 0, Words));
    if ( memcmp(On, Truth, sizeof(word)*Words) )
    {
        memcpy(Copy, On, sizeof(word)*Words);
        Result |= If3_PackTryTruth(p, Root, Nodes, nNodes, Leaves, nLeaves, Copy, Best);
        memcpy(Leaves, SavedLeaves, sizeof(int)*nLeaves);
    }
    if ( Best->nNodes-Best->nNew >= nNodes-1 ) return Result;
    for ( w = 0; w < Words; w++ ) Copy[w] = ~Off[w];
    assert(Abc_TtEqualCare(Copy, Truth, Care, 0, Words));
    if ( memcmp(Copy, Truth, sizeof(word)*Words) && memcmp(Copy, On, sizeof(word)*Words) )
        Result |= If3_PackTryTruth(p, Root, Nodes, nNodes, Leaves, nLeaves, Copy, Best);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Replaces a local cone and releases newly dangling logic.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackApply( If3_Pack_t * p, int Root, If3_PackPlan_t * Best )
{
    If3_Lut_t * Proposed = Best->Proposed, * Lut;
    int Boundary[IF3_PACK_NODES*6+8], nBoundary = 0;
    int i, j, k, Req = p->Luts[Root].Required;
    if ( p->nObjs + Best->nNew > p->nCap )
    {
        int OldCap = p->nCap;
        p->nCap = Abc_MaxInt(2*p->nCap, p->nObjs+Best->nNew);
        p->Luts = ABC_REALLOC(If3_Lut_t, p->Luts, p->nCap);
        p->FanHeads = ABC_REALLOC(int, p->FanHeads, p->nCap);
        p->Slots = ABC_REALLOC(int, p->Slots, p->nCap);
        p->Seen = ABC_REALLOC(unsigned, p->Seen, p->nCap);
        memset(p->FanHeads+OldCap, 0, sizeof(int)*(p->nCap-OldCap));
        memset(p->Seen+OldCap, 0, sizeof(unsigned)*(p->nCap-OldCap));
        memset(p->Luts+OldCap, 0, sizeof(If3_Lut_t)*(p->nCap-OldCap));
    }
    for ( i = 0; i < Best->nNodes; i++ )
    {
        Lut = p->Luts + Best->Nodes[i];
        for ( j = 0; j < Lut->nFans; j++ )
        {
            assert(p->Luts[Lut->Fans[j]].Refs > 0);
            p->Luts[Lut->Fans[j]].Refs--;
            if ( If3_PackHas(Best->Nodes, Best->nNodes, Lut->Fans[j]) < 0 ) Boundary[nBoundary++] = Lut->Fans[j];
        }
    }
    for ( i = 0; i < Best->nNodes; i++ ) p->Luts[Best->Nodes[i]].Dead = 1;
    for ( i = 1; i < Best->nNodes; i++ ) assert(p->Luts[Best->Nodes[i]].Refs == 0);
    for ( i = 0; i < Best->nNew; i++ )
    {
        k = i == Best->nNew-1 ? Root : p->nObjs++;
        Proposed[i].Refs = p->Luts[k].Refs;
        Proposed[i].Required = Req;
        Proposed[i].Dead = 0;
        p->Luts[k] = Proposed[i];
        if ( k != Root ) Boundary[nBoundary++] = k;
        for ( j = 0; j < Proposed[i].nFans; j++ ) p->Luts[Proposed[i].Fans[j]].Refs++;
        if ( k != Root ) { If3_PackFinish(p, k); Vec_IntPush(p->Order, k); }
    }
    // A minimized support can orphan additional boundary cones. Release
    // these immediately so reuse and subsequent windows see exact live costs.
    Vec_IntClear(p->Release);
    for ( i = 0; i < nBoundary; i++ ) Vec_IntPush(p->Release, Boundary[i]);
    while ( Vec_IntSize(p->Release) )
    {
        k = Vec_IntPop(p->Release);
        Lut = p->Luts+k;
        if ( k <= p->nCis || Lut->Refs || Lut->Dead ) continue;
        Lut->Dead = 1;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            assert(p->Luts[Lut->Fans[j]].Refs > 0);
            if ( --p->Luts[Lut->Fans[j]].Refs == 0 ) Vec_IntPush(p->Release, Lut->Fans[j]);
        }
    }
    p->Changes++;
    p->Saved += Best->nNodes-Best->nNew;
}

/**Function*************************************************************

  Synopsis    [Resolves aliases and merges identical LUT functions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackCanonical( If3_Man_t * m, If3_Pack_t * p, int * Map )
{
    If3_Lut_t * Lut;
    Gia_Obj_t * Obj;
    unsigned Hash;
    word Zero, One, Select;
    int Id, i, j, k, Lit, Removed = 0;
    memset(p->HashBins, 0, sizeof(int)*p->nHashBins);
    p->Aliases = ABC_ALLOC(int, p->nObjs);
    for ( i = 0; i < p->nObjs; i++ ) p->Aliases[i] = Abc_Var2Lit(i, 0);
    Vec_IntForEachEntry(p->Order, Id, i)
    {
        Lut = p->Luts+Id;
        if ( !Lut->Refs ) continue;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            Lit = p->Aliases[Lut->Fans[j]];
            Lut->Fans[j] = Abc_Lit2Var(Lit);
            if ( Lit == 0 ) Lut->Truth = Abc_Tt6Cofactor0(Lut->Truth, j);
            else if ( Lit == 1 ) Lut->Truth = Abc_Tt6Cofactor1(Lut->Truth, j);
            else if ( Abc_LitIsCompl(Lit) ) Lut->Truth = Abc_Tt6Flip(Lut->Truth, j);
        }
        for ( j = 1; j < Lut->nFans; j++ )
            for ( k = 0; k < j; k++ )
                if ( Lut->Fans[k] == Lut->Fans[j] )
                {
                    Zero = Abc_Tt6Cofactor0(Lut->Truth, j);
                    One = Abc_Tt6Cofactor1(Lut->Truth, j);
                    Select = If3_PackVariable(k, 0);
                    Lut->Truth = (Zero & ~Select) | (One & Select);
                    break;
                }
        Lut->nFans = Abc_Tt6MinBase(&Lut->Truth, Lut->Fans, Lut->nFans);
        if ( Lut->nFans == 0 )
            p->Aliases[Id] = (int)(Lut->Truth & 1);
        else if ( Lut->nFans == 1 )
            p->Aliases[Id] = Abc_Var2Lit(Lut->Fans[0], (int)(Lut->Truth & 1));
        else
        {
            If3_PackSort(Lut);
            Lit = If3_PackLookup(p, Lut, &Id, 1);
            if ( Lit >= 0 ) p->Aliases[Id] = Lit;
            else
            {
                Lut->Level = 0;
                for ( j = 0; j < Lut->nFans; j++ ) Lut->Level = Abc_MaxInt(Lut->Level, p->Luts[Lut->Fans[j]].Level);
                Lut->Level++;
                Hash = If3_PackHash(Lut) & (p->nHashBins-1);
                Lut->Next = p->HashBins[Hash];
                p->HashBins[Hash] = Id;
            }
        }
        Removed += p->Aliases[Id] != Abc_Var2Lit(Id, 0);
    }
    for ( Id = 0; Id < p->nObjs; Id++ ) p->Luts[Id].Refs = 0;
    Gia_ManForEachCo(m->pGia, Obj, i)
        p->Luts[Abc_Lit2Var(p->Aliases[Map[Gia_ObjFaninId0p(m->pGia, Obj)]])].Refs++;
    Vec_IntForEachEntryReverse(p->Order, Id, i)
        if ( p->Luts[Id].Refs )
            for ( j = 0; j < p->Luts[Id].nFans; j++ ) p->Luts[p->Luts[Id].Fans[j]].Refs++;
    if ( m->pPars->fVerbose ) Abc_Print(1, "If3 LUT canonical merges = %d\n", Removed);
}

/**Function*************************************************************

  Synopsis    [Exports a LUT network as a GIA with an attached mapping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If3_PackExport( If3_Man_t * m, If3_Pack_t * p, int * Map )
{
    Gia_Man_t * New = Gia_ManStart(Gia_ManObjNum(m->pGia));
    Vec_Int_t * Copies = Vec_IntStartFull(p->nObjs);
    Vec_Int_t * Mapping = Vec_IntStart(1), * Offsets = Vec_IntAlloc(p->nObjs);
    Vec_Int_t * Fans = Vec_IntAlloc(6);
    Gia_Obj_t * Obj;
    If3_Lut_t * Lut;
    Kit_Graph_t * Graph;
    int Id, i, j, Lit, Root, Area = 0, Edge = 0, Depth = 0;
    New->pName = Abc_UtilStrsav(m->pGia->pName);
    New->pSpec = Abc_UtilStrsav(m->pGia->pSpec);
    Vec_IntWriteEntry(Copies, 0, 0);
    Gia_ManForEachCi(m->pGia, Obj, i)
        Vec_IntWriteEntry(Copies, Map[Gia_ObjId(m->pGia, Obj)], Gia_ManAppendCi(New));
    Vec_IntForEachEntry(p->Order, Id, i)
    {
        Lut = p->Luts + Id;
        if ( !Lut->Refs ) continue;
        Vec_IntClear(Fans);
        for ( j = 0; j < Lut->nFans; j++ )
        {
            Lit = Vec_IntEntry(Copies, Lut->Fans[j]);
            assert(Lit >= 0);
            Vec_IntPush(Fans, Lit);
        }
        Graph = If3_RecipeFind(p->Recipes, &p->nRecipes, Lut->Truth, Lut->nFans, p->Cover);
        assert(Graph != NULL);
        Lit = Kit_GraphToGia(New, Graph, Fans, 0);
        Vec_IntWriteEntry(Copies, Id, Lit);
        Root = Abc_Lit2Var(Lit);
        if ( !Root || !Gia_ObjIsAnd(Gia_ManObj(New, Root)) ) continue;
        for ( j = 0; j < Lut->nFans; j++ ) if ( Root == Abc_Lit2Var(Vec_IntEntry(Fans, j)) ) break;
        if ( j < Lut->nFans ) continue;
        Vec_IntSetEntry(Offsets, Root, Vec_IntSize(Mapping));
        Vec_IntPush(Mapping, Lut->nFans);
        for ( j = 0; j < Lut->nFans; j++ ) Vec_IntPush(Mapping, Abc_Lit2Var(Vec_IntEntry(Fans, j)));
        Vec_IntPush(Mapping, Root);
        Area++;
        Edge += Lut->nFans;
    }
    Gia_ManForEachCo(m->pGia, Obj, i)
    {
        Id = Map[Gia_ObjFaninId0p(m->pGia, Obj)];
        Lit = p->Aliases[Id];
        Id = Abc_Lit2Var(Lit);
        Lit = Vec_IntEntry(Copies, Id) ^ Abc_LitIsCompl(Lit);
        assert(Lit >= 0);
        Gia_ManAppendCo(New, Abc_LitNotCond(Lit, Gia_ObjFaninC0(Obj)));
        Depth = Abc_MaxInt(Depth, p->Luts[Id].Level);
    }
    Vec_IntFillExtra(Offsets, Gia_ManObjNum(New), 0);
    Vec_IntForEachEntry(Offsets, Root, i) if ( Root ) Vec_IntAddToEntry(Offsets, i, Gia_ManObjNum(New));
    Vec_IntAppend(Offsets, Mapping);
    New->vMapping = Offsets;
    New->MappedArea = m->pPars->Area = Area;
    m->pPars->Edge = Edge;
    New->MappedDelay = Depth;
    m->pPars->Delay = (float)Depth;
    Gia_ManSetRegNum(New, Gia_ManRegNum(m->pGia));
    Gia_ManMappingVerify(New);
    Vec_IntFree(Copies);
    Vec_IntFree(Mapping);
    Vec_IntFree(Fans);
    return New;
}

/**Function*************************************************************

  Synopsis    [Computes reachable boundary assignments over a bounded LUT cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If3_PackCare( If3_Pack_t * p, int Root, int * Nodes, int nNodes )
{
    int Leaves[18], nLeaves = 0, i, j, w, Pos, Pass, Code, Words;
    word Values[8][32], * Inputs[6], * RootInputs[6];
    word Care = 0, Bits;
    unsigned Done = 0;
    If3_Lut_t * Lut = p->Luts+Root;
    for ( i = 0; i < Lut->nFans; i++ )
        if ( If3_PackHas(Nodes, nNodes, Lut->Fans[i]) < 0 ) Leaves[nLeaves++] = Lut->Fans[i];
    for ( i = 0; i < nNodes; i++ )
        for ( j = 0; j < p->Luts[Nodes[i]].nFans; j++ )
        {
            Pos = p->Luts[Nodes[i]].Fans[j];
            if ( If3_PackHas(Nodes, nNodes, Pos) >= 0 || If3_PackHas(Leaves, nLeaves, Pos) >= 0 ) continue;
            Leaves[nLeaves++] = Pos;
            if ( nLeaves > 11 ) return ~(word)0;
        }
    Words = Abc_TtWordNum(nLeaves);
    for ( Pass = 0; Pass < nNodes; Pass++ )
        for ( i = 0; i < nNodes; i++ )
        {
            if ( Done & (1u<<i) ) continue;
            Lut = p->Luts+Nodes[i];
            for ( j = 0; j < Lut->nFans; j++ )
            {
                Pos = If3_PackHas(Nodes, nNodes, Lut->Fans[j]);
                if ( Pos >= 0 )
                {
                    if ( !(Done & (1u<<Pos)) ) break;
                    Inputs[j] = Values[Pos];
                }
                else
                {
                    Pos = If3_PackHas(Leaves, nLeaves, Lut->Fans[j]);
                    assert(Pos >= 0);
                    Inputs[j] = (Leaves[Pos] ? p->Vars[Pos] : p->Zero);
                }
            }
            if ( j < Lut->nFans ) continue;
            If3_PackEvalWords(p, Lut->Truth, Lut->nFans, Inputs, Words, Values[i]);
            Done |= 1u<<i;
        }
    assert(Done == (1u<<nNodes)-1);
    Lut = p->Luts+Root;
    for ( i = 0; i < Lut->nFans; i++ )
    {
        Pos = If3_PackHas(Nodes, nNodes, Lut->Fans[i]);
        if ( Pos >= 0 ) RootInputs[i] = Values[Pos];
        else
        {
            Pos = If3_PackHas(Leaves, nLeaves, Lut->Fans[i]);
            assert(Pos >= 0);
            RootInputs[i] = (Leaves[Pos] ? p->Vars[Pos] : p->Zero);
        }
    }
    for ( Code = 0; Code < (1<<Lut->nFans); Code++ )
        for ( w = 0; w < Words; w++ )
        {
            Bits = ~(word)0;
            for ( i = 0; i < Lut->nFans && Bits; i++ )
                Bits &= (Code & (1<<i)) ? RootInputs[i][w] : ~RootInputs[i][w];
            if ( Bits ) { Care |= ((word)1)<<Code; break; }
        }
    return Abc_Tt6Stretch(Care, Lut->nFans);
}

/**Function*************************************************************

  Synopsis    [Collects a small fanin window for exact care computation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_PackCareWindow( If3_Pack_t * p, int Root, int * Nodes )
{
    int Leaves[17], Trial[17], BestLeaves[11], nLeaves, nNodes = 0;
    int i, j, Id, Best, BestSize, Size;
    If3_Lut_t * Lut = p->Luts+Root;
    nLeaves = Lut->nFans;
    memcpy(Leaves, Lut->Fans, sizeof(int)*nLeaves);
    while ( nNodes < 8 )
    {
        Best = -1;
        BestSize = 12;
        for ( i = 0; i < nLeaves; i++ )
        {
            Id = Leaves[i];
            if ( Id <= p->nCis ) continue;
            Size = 0;
            for ( j = 0; j < nLeaves; j++ ) if ( j != i ) Trial[Size++] = Leaves[j];
            Lut = p->Luts+Id;
            for ( j = 0; j < Lut->nFans; j++ )
                if ( If3_PackHas(Nodes, nNodes, Lut->Fans[j]) < 0 && If3_PackHas(Trial, Size, Lut->Fans[j]) < 0 )
                    Trial[Size++] = Lut->Fans[j];
            if ( Size > 11 || Size > BestSize ) continue;
            if ( Size == BestSize && p->Luts[Id].Level <= p->Luts[Leaves[Best]].Level ) continue;
            Best = i;
            BestSize = Size;
            memcpy(BestLeaves, Trial, sizeof(int)*Size);
        }
        if ( Best < 0 ) break;
        Nodes[nNodes++] = Leaves[Best];
        nLeaves = BestSize;
        memcpy(Leaves, BestLeaves, sizeof(int)*nLeaves);
    }
    return nNodes;
}

/**Function*************************************************************

  Synopsis    [Minimizes LUT supports using exact local care conditions.]

  Description [A root may change only where every immediate fanout is
  insensitive to it. Unrelated side inputs are existentially quantified
  when forming the care condition, overapproximating observability.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_PackOdc( If3_Pack_t * p, int fVerbose )
{
    enum { IF3_ODC_ALIAS_EDGES = 256 };
    If3_Lut_t * Root, * Fan, * Lut;
    word Care, Derivative, Values[6], On, Off, On0, On1, Off0, Off1, Truth;
    int Id, i, j, k, Edge, FanId, Pos, Count, Offset, OldFans[6], NewFans[6];
    int Nodes[8], nNodes, Alias, Candidate, CandidateEdge, Scanned;
    word CandidateTruth;
    int nOld, nNew, Changes = 0, Removed = 0, Collapsed = 0;
    abctime Start = Abc_Clock();
    memset(p->FanHeads, 0, sizeof(int)*p->nCap);
    Vec_IntShrink(p->FanEdges, 2);
    for ( Id = p->nCis+1; Id < p->nObjs; Id++ )
    {
        Lut = p->Luts+Id;
        if ( !Lut->Refs ) continue;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            k = Lut->Fans[j];
            Offset = Vec_IntSize(p->FanEdges);
            Vec_IntPushTwo(p->FanEdges, Id, p->FanHeads[k]);
            p->FanHeads[k] = Offset;
        }
    }
    for ( Id = p->nCis+1; Id < p->nObjs; Id++ )
    {
        Root = p->Luts+Id;
        if ( !Root->Refs || Root->Refs > 16 || Root->nFans < 2 ) continue;
        Care = 0;
        Count = 0;
        for ( Edge = p->FanHeads[Id]; Edge; Edge = Vec_IntEntry(p->FanEdges, Edge+1) )
        {
            FanId = Vec_IntEntry(p->FanEdges, Edge);
            Fan = p->Luts+FanId;
            if ( !Fan->Refs ) continue;
            Pos = If3_PackHas(Fan->Fans, Fan->nFans, Id);
            if ( Pos < 0 ) continue;
            Count++;
            Derivative = Abc_Tt6Cofactor0(Fan->Truth, Pos) ^ Abc_Tt6Cofactor1(Fan->Truth, Pos);
            for ( j = 0; j < Fan->nFans; j++ )
            {
                Pos = If3_PackHas(Root->Fans, Root->nFans, Fan->Fans[j]);
                if ( Pos < 0 )
                {
                    Derivative = Abc_Tt6Cofactor0(Derivative, j) | Abc_Tt6Cofactor1(Derivative, j);
                    Values[j] = 0;
                }
                else Values[j] = If3_PackVariable(Pos, 0);
            }
            Care |= If3_PackEvalDirect(Derivative, Fan->nFans, Values);
            if ( Care == ~(word)0 ) break;
        }
        // Any missing reference is an output reference, whose care is total.
        if ( Count != Root->Refs ) Care = ~(word)0;
        nNodes = If3_PackCareWindow(p, Id, Nodes);
        if ( nNodes ) Care &= If3_PackCare(p, Id, Nodes, nNodes);
        if ( Care == ~(word)0 ) continue;
        // Earlier live LUTs may replace this root when they agree on its care.
        // A new alias only adds a reference to an already processed object.
        // Bound candidate discovery, while keeping every care condition exact.
        Alias = -1;
        for ( i = 0; i < Root->nFans && Alias < 0; i++ )
            for ( CandidateEdge = p->FanHeads[Root->Fans[i]], Scanned = 0;
                  CandidateEdge && Scanned < IF3_ODC_ALIAS_EDGES;
                  CandidateEdge = Vec_IntEntry(p->FanEdges, CandidateEdge+1), Scanned++ )
            {
                Candidate = Vec_IntEntry(p->FanEdges, CandidateEdge);
                if ( Candidate >= Id || Candidate <= p->nCis ) continue;
                Fan = p->Luts+Candidate;
                if ( !Fan->Refs || Fan->nFans < 2 || Fan->Level > Root->Required ) continue;
                for ( j = 0; j < Fan->nFans; j++ )
                {
                    Pos = If3_PackHas(Root->Fans, Root->nFans, Fan->Fans[j]);
                    if ( Pos < 0 ) break;
                    Values[j] = If3_PackVariable(Pos, 0);
                }
                if ( j < Fan->nFans ) continue;
                CandidateTruth = If3_PackEval(p, Fan->Truth, Fan->nFans, Values);
                if ( !((CandidateTruth ^ Root->Truth)&Care) ) Alias = 2*Candidate;
                else if ( !((~CandidateTruth ^ Root->Truth)&Care) ) Alias = 2*Candidate+1;
                if ( Alias >= 0 ) break;
            }
        On = Root->Truth & Care;
        Off = ~Root->Truth & Care;
        for ( i = Root->nFans-1; i >= 0; i-- )
        {
            On0 = Abc_Tt6Cofactor0(On, i);
            On1 = Abc_Tt6Cofactor1(On, i);
            Off0 = Abc_Tt6Cofactor0(Off, i);
            Off1 = Abc_Tt6Cofactor1(Off, i);
            if ( (On0 & Off1) || (On1 & Off0) ) continue;
            On = On0 | On1;
            Off = Off0 | Off1;
        }
        Truth = On;
        assert(((Truth ^ Root->Truth) & Care) == 0);
        nOld = Root->nFans;
        memcpy(OldFans, Root->Fans, sizeof(int)*nOld);
        memcpy(NewFans, Root->Fans, sizeof(int)*nOld);
        nNew = Abc_Tt6MinBase(&Truth, NewFans, nOld);
        if ( Alias >= 0 )
        {
            nNew = 1;
            NewFans[0] = Alias>>1;
            Truth = If3_PackVariable(0, 0) ^ ((Alias&1) ? ~(word)0 : 0);
        }
        if ( nNew >= nOld ) continue;
        for ( i = 0; i < nOld; i++ )
        {
            assert(p->Luts[OldFans[i]].Refs > 0);
            p->Luts[OldFans[i]].Refs--;
        }
        for ( i = 0; i < nNew; i++ ) p->Luts[NewFans[i]].Refs++;
        Root->nFans = nNew;
        Root->Truth = Truth;
        memcpy(Root->Fans, NewFans, sizeof(int)*nNew);
        Root->Level = 0;
        for ( i = 0; i < nNew; i++ ) Root->Level = Abc_MaxInt(Root->Level, p->Luts[NewFans[i]].Level);
        Root->Level += nNew > 1;
        Changes++;
        Removed += nOld-nNew;
        Collapsed += nNew < 2;
        Vec_IntClear(p->Release);
        for ( i = 0; i < nOld; i++ ) Vec_IntPush(p->Release, OldFans[i]);
        while ( Vec_IntSize(p->Release) )
        {
            k = Vec_IntPop(p->Release);
            Lut = p->Luts+k;
            if ( k <= p->nCis || Lut->Refs || Lut->Dead ) continue;
            Lut->Dead = 1;
            for ( j = 0; j < Lut->nFans; j++ )
            {
                assert(p->Luts[Lut->Fans[j]].Refs > 0);
                if ( --p->Luts[Lut->Fans[j]].Refs == 0 ) Vec_IntPush(p->Release, Lut->Fans[j]);
            }
        }
    }
    if ( fVerbose ) Abc_Print(1, "If3 local ODCs: %d changed LUTs, %d removed inputs, %d aliases, %.3f sec\n",
                               Changes, Removed, Collapsed, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
}


/**Function*************************************************************

  Synopsis    [Refactors mapped LUT cones while preserving area and depth bounds.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If3_Pack( If3_Man_t * m )
{
    If3_Pack_t Man, * p = &Man;
    Gia_Obj_t * Obj;
    Gia_Man_t * New;
    If3_Lut_t * Lut;
    If3_Cut_t * Cut;
    int * Map = ABC_CALLOC(int, Gia_ManObjNum(m->pGia));
    int Nodes[IF3_PACK_NODES], Leaves[IF3_PACK_VARS], nNodes, nLeaves;
    Vec_Int_t * OldOrder;
    int i, j, Id, Original, Pass, Before, Target = (m->pPars->fArea || m->Target >= INT_MAX/4) ? INT_MAX/4 : (int)(m->Target + IF3_EPSILON);
    size_t Capacity = 1 + (size_t)Gia_ManCiNum(m->pGia) + 3*(size_t)m->pPars->Area;
    abctime clk = Abc_Clock();
    if ( Capacity > INT_MAX/8 || Capacity > ((size_t)-1)/sizeof(If3_Lut_t) )
    {
        ABC_FREE(Map);
        return NULL;
    }
    memset(p, 0, sizeof(*p));
    p->nCis = Gia_ManCiNum(m->pGia);
    p->nLuts = m->pPars->Area;
    p->nCap = (int)Capacity;
    p->Luts = ABC_CALLOC(If3_Lut_t, p->nCap);
    p->FanHeads = ABC_CALLOC(int, p->nCap);
    p->Slots = ABC_ALLOC(int, p->nCap);
    p->Seen = ABC_CALLOC(unsigned, p->nCap);
    p->FanEdges = Vec_IntStart(2);
    p->Cache = ABC_CALLOC(If3_PackEntry_t, IF3_PACK_BINS);
    p->Recipes = ABC_CALLOC(If3_Recipe_t, IF3_RECIPE_BINS);
    p->Order = Vec_IntAlloc(p->nLuts);
    p->Cover = Vec_IntAlloc(1024);
    p->Release = Vec_IntAlloc(64);
    p->Scratch = Vec_WrdAlloc(128);
    p->K = m->pPars->nLutSize;
    for ( i = 0; i < IF3_PACK_VARS; i++ )
        for ( j = 0; j < IF3_PACK_WORDS; j++ ) p->Vars[i][j] = If3_PackVariable(i, j);
    p->nHashBins = 1 << Abc_Base2Log(Abc_MaxInt(1024, 2*p->nLuts));
    p->HashBins = ABC_CALLOC(int, p->nHashBins);
    p->nObjs = 1;
    Gia_ManForEachCi(m->pGia, Obj, i) Map[Gia_ObjId(m->pGia, Obj)] = p->nObjs++;
    Gia_ManForEachAnd(m->pGia, Obj, i)
    {
        if ( !m->pRefs[i] ) continue;
        Id = Map[i] = p->nObjs++;
        Lut = p->Luts + Id;
        Cut = If3_ObjBest(m, i);
        Lut->Truth = Cut->Truth;
        Lut->nFans = Cut->nLeaves;
        Lut->Required = m->pPars->fArea ? INT_MAX/4 : Target;
        for ( j = 0; j < Lut->nFans; j++ )
        {
            Lut->Fans[j] = Map[Cut->Leaves[j]];
            assert(Cut->Leaves[j] == 0 || Lut->Fans[j] > 0);
            p->Luts[Lut->Fans[j]].Refs++;
            Lut->Level = Abc_MaxInt(Lut->Level, p->Luts[Lut->Fans[j]].Level);
        }
        Lut->Level += Lut->nFans > 1;
    }
    Original = p->nObjs;
    Gia_ManForEachCo(m->pGia, Obj, i) p->Luts[Map[Gia_ObjFaninId0p(m->pGia, Obj)]].Refs++;
    for ( Id = Original-1; Id > p->nCis; Id-- )
    {
        Lut = p->Luts + Id;
        for ( j = 0; j < Lut->nFans; j++ )
            if ( Lut->Fans[j] > p->nCis ) p->Luts[Lut->Fans[j]].Required = Abc_MinInt(p->Luts[Lut->Fans[j]].Required, Lut->Required-1);
    }
    for ( Id = p->nCis+1; Id < Original; Id++ ) Vec_IntPush(p->Order, Id);
    If3_PackOdc(p, m->pPars->fVerbose);
    for ( Pass = 0; Pass < 3; Pass++ )
    {
    memset(p->HashBins, 0, sizeof(int)*p->nHashBins);
    memset(p->FanHeads, 0, sizeof(int)*p->nCap);
    Vec_IntShrink(p->FanEdges, 2);
    Before = p->Changes;
    OldOrder = p->Order;
    p->Order = Vec_IntAlloc(Vec_IntSize(OldOrder));
    Vec_IntForEachEntry(OldOrder, Id, i)
    {
        If3_PackPlan_t Best;
        memset(&Best, 0, sizeof(Best));
        Lut = p->Luts + Id;
        if ( !Lut->Refs ) continue;
        Lut->Level = 0;
        for ( j = 0; j < Lut->nFans; j++ ) Lut->Level = Abc_MaxInt(Lut->Level, p->Luts[Lut->Fans[j]].Level);
        Lut->Level += Lut->nFans > 1;
        Nodes[0] = Id;
        nNodes = 1;
        nLeaves = 0;
        for ( j = 0; j < Lut->nFans; j++ )
            if ( If3_PackHas(Leaves, nLeaves, Lut->Fans[j]) < 0 ) Leaves[nLeaves++] = Lut->Fans[j];
        {
            int Bounds[IF3_PACK_NODES+1][IF3_PACK_VARS];
            int Sizes[IF3_PACK_NODES+1], N;
            while ( nNodes < IF3_PACK_NODES && If3_PackExpand(p, Nodes, &nNodes, Leaves, &nLeaves) )
            {
                Sizes[nNodes] = nLeaves;
                memcpy(Bounds[nNodes], Leaves, sizeof(int)*nLeaves);
            }
            for ( N = nNodes; N >= 2; N-- )
            {
                int Copy[IF3_PACK_VARS];
                if ( N-1 < Best.nNodes-Best.nNew ) continue;
                memcpy(Copy, Bounds[N], sizeof(int)*Sizes[N]);
                If3_PackTry(p, Id, Nodes, N, Copy, Sizes[N], &Best);
            }
        }
        if ( Best.nNew ) If3_PackApply(p, Id, &Best);
        If3_PackFinish(p, Id);
        Vec_IntPush(p->Order, Id);
    }
    Vec_IntFree(OldOrder);
    // Rebuild live references after support minimization has orphaned any
    // boundary cones. Order includes each retained or newly created LUT.
    for ( Id = 0; Id < p->nObjs; Id++ ) p->Luts[Id].Refs = 0;
    Gia_ManForEachCo(m->pGia, Obj, i) p->Luts[Map[Gia_ObjFaninId0p(m->pGia, Obj)]].Refs++;
    Vec_IntForEachEntryReverse(p->Order, Id, i)
        if ( p->Luts[Id].Refs )
            for ( j = 0; j < p->Luts[Id].nFans; j++ ) p->Luts[p->Luts[Id].Fans[j]].Refs++;
    for ( Id = p->nCis+1; Id < p->nObjs; Id++ ) p->Luts[Id].Required = Target;
    Vec_IntForEachEntryReverse(p->Order, Id, i)
        if ( p->Luts[Id].Refs )
            for ( j = 0; j < p->Luts[Id].nFans; j++ )
            {
                int Fan = p->Luts[Id].Fans[j];
                p->Luts[Fan].Required = Abc_MinInt(p->Luts[Fan].Required, p->Luts[Id].Required-1);
            }
    if ( Before == p->Changes ) break;
    }
    if ( m->pPars->fVerbose ) Abc_Print(1, "If3 LUT sharing hits = %d\n", p->Shared);
    if ( m->pPars->fVerbose ) Abc_Print(1, "If3 LUT resub hits = %d\n", p->ResubHits);
    If3_PackCanonical(m, p, Map);
    i = m->pPars->Area;
    New = If3_PackExport(m, p, Map);
    assert(m->pPars->Area <= i-p->Saved);
    if ( m->pPars->fVerbose )
        Abc_Print(1, "If3 LUT decomposition: %d trials, %d hits, %d replacements, %d saved, %.3f sec\n",
                  p->Trials, p->Hits, p->Changes, p->Saved, 1.0*(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    If3_RecipeClear(p->Recipes);
    ABC_FREE(p->Recipes);
    ABC_FREE(p->FanHeads);
    ABC_FREE(p->Slots);
    ABC_FREE(p->Seen);
    Vec_IntFree(p->FanEdges);
    ABC_FREE(p->Aliases);
    ABC_FREE(p->HashBins);
    ABC_FREE(p->Cache);
    ABC_FREE(p->Luts);
    ABC_FREE(Map);
    Vec_IntFree(p->Order);
    Vec_IntFree(p->Cover);
    Vec_IntFree(p->Release);
    Vec_WrdFree(p->Scratch);
    return New;
}

/**Function*************************************************************

  Synopsis    [Maps a topologically ordered GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If3_ManPerformMappingCore( Gia_Man_t * pGia, If3_Par_t * pPars )
{
    If3_Man_t Man, *p = &Man;
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, k, nObjs = Gia_ManObjNum( pGia );
    int SavedArea = INT_MAX;
    float SavedDelay = IF3_INFINITY;
    If3_Cut_t * Saved;
    abctime clk = Abc_Clock(), clkExport;
    // Box ordering can create a fresh GIA without the original choice phases.
    if ( Gia_ManHasChoices( pGia ) ) Gia_ManSetPhase( pGia );
    memset( p, 0, sizeof( If3_Man_t ) );
    p->pGia = pGia;
    p->pPars = pPars;
    p->fChoices = Gia_ManHasChoices( pGia );
    p->fTruth = pPars->fCutMin || Gia_ManHasChoices( pGia ) || Gia_ManMuxNum( pGia );
    p->pTim = pGia->pManTime ? Tim_ManDup( (Tim_Man_t *)pGia->pManTime, 0 ) : NULL;
    p->pCuts = p->fTruth || pPars->nCutsMax > 4 ? ABC_ALLOC( If3_Cut_t, (size_t)nObjs * pPars->nCutsMax ) : NULL;
    p->pBest = ABC_ALLOC( If3_Cut_t, nObjs );
    p->pCounts = ABC_CALLOC( unsigned char, nObjs );
    p->pLocalMask = ABC_CALLOC( word, nObjs );
    p->pAreaSeen = ABC_CALLOC( unsigned char, nObjs );
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
    for ( i = 0; i < nObjs; i++ ) p->pRequired[i] = IF3_INFINITY;
    If3_CutUnit( If3_ObjBest( p, 0 ), 0 );
    p->pCounts[0] = 1;
    if ( p->pCuts )
        *If3_ObjCuts( p, 0 ) = *If3_ObjBest( p, 0 );
    else
        p->pBankMasks[0] = 0;
    Gia_ManForEachCi ( pGia, pObj, i )
    {
        k = Gia_ObjId( pGia, pObj );
        If3_CutUnit( If3_ObjBest( p, k ), k );
        p->pCounts[k] = 1;
        if ( p->pCuts )
            *If3_ObjCuts( p, k ) = *If3_ObjBest( p, k );
        else
        {
            p->pBankSize[k] = 1;
            p->pBankLeaves[(size_t)k * pPars->nCutsMax * 6] = k;
            p->pBankMasks[(size_t)k * pPars->nCutsMax] = 1;
        }
        if ( pGia->vCiArrs )
            If3_ObjBest( p, k )->Delay = (float)Vec_IntEntry( pGia->vCiArrs, i );
        else if ( pGia->vInArrs )
            If3_ObjBest( p, k )->Delay = Vec_FltSize( pGia->vInArrs ) ? Vec_FltEntry( pGia->vInArrs, i ) : pGia->DefInArrs;
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
    If3_ManRound( p, 0 );
    If3_ManGroup( p );
    If3_ManRound( p, 3 );
    ABC_FREE( p->pChoiceRefs );
    // Box timing retains the original traversal; exploration currently uses
    // only the fixed, explicit arrival and required-time model.
    Saved = p->pTim ? NULL : ABC_ALLOC( If3_Cut_t, nObjs );
    If3_SaveCover(p, Saved, &SavedArea, &SavedDelay);
    for ( i = 0; i < pPars->nFlowIters; i++ )
    {
        If3_ManRound(p, 1);
        If3_SaveCover(p, Saved, &SavedArea, &SavedDelay);
    }
    for ( i = 0; i < pPars->nAreaIters; i++ )
    {
        If3_ManRound(p, 2);
        If3_SaveCover(p, Saved, &SavedArea, &SavedDelay);
    }
    for ( i = 0; i < pPars->nExploreIters; i++ )
    {
        If3_CausalRound(p);
        If3_SaveCover(p, Saved, &SavedArea, &SavedDelay);
        If3_ManRound(p, 2);
        If3_SaveCover(p, Saved, &SavedArea, &SavedDelay);
    }
    if ( Saved )
    {
        memcpy( p->pBest, Saved, sizeof(If3_Cut_t) * nObjs );
        If3_ManRequired(p);
        ABC_FREE( Saved );
    }
    p->fCachedArea = 0;
    if ( pPars->nAreaIters > 0 ) If3_InlineCover( p );
    if ( pPars->nAreaIters > 0 )
        for ( i = 0; i < 2; i++ )
            if ( !If3_AbsorbShared(p) ) break;
    clkExport = Abc_Clock();
    pNew = NULL;
    if ( pPars->fPack && !p->pTim && !Gia_ManBufNum(pGia) && !pGia->vCiArrs && !pGia->vInArrs &&
         !pGia->vCoReqs && !pGia->vOutReqs && pPars->nAreaIters > 0 )
    {
        if ( !p->fTruth ) If3_ManSelectedTruth(p);
        pNew = If3_Pack(p);
    }
    else pNew = p->fTruth ? NULL : If3_ManExportStructural(p);
    if ( pNew == NULL )
    {
        if ( !p->fTruth ) If3_ManSelectedTruth( p );
        pNew = If3_ManExport( p );
    }
    if ( pPars->fVerbose )
        Abc_Print( 1,
                   "If3: pairs = %.0f  merges = %.0f  minimized = %.0f  trials = %.0f  ref visits = %.0f\nIf3: cut memory = "
                   "%.2f MB  mapping = %.3f sec  export = %.3f sec  total = %.3f sec\n",
                   p->nPairs, p->nMerged, p->nMinimized, p->nTrials, p->nRefVisits,
                   (double)nObjs *
                       ( sizeof( If3_Cut_t ) +
                         pPars->nCutsMax * ( 6 * sizeof( int ) + sizeof( word ) + ( p->pCuts ? sizeof( If3_Cut_t ) : 0 ) ) +
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
static Gia_Man_t * If3_ManCoarsen( Gia_Man_t * p, int fMux )
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
    If3_ManOrderInterface( New, p );
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
static Gia_Man_t * If3_ManPerformMappingInt( Gia_Man_t * pGia, If3_Par_t * pPars )
{
    Gia_Man_t * pCls, * pNew;
    if ( pGia->fGiaSimple || pGia->pManTime || pGia->vCiArrs || pGia->vInArrs || pGia->vCoReqs || pGia->vOutReqs || Gia_ManBufNum(pGia) )
        return If3_ManPerformMappingCore(pGia, pPars);
    pCls = If3_ManCoarsen(pGia, Gia_ManHasChoices(pGia) && pPars->nLutSize >= 3);
    pNew = If3_ManPerformMappingCore(pCls, pPars);
    Gia_ManStop(pCls);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Sets default LUT size, cut budget and recovery rounds.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void If3_ManSetDefaultPars( If3_Par_t * pPars )
{
    memset( pPars, 0, sizeof(If3_Par_t) );
    pPars->nLutSize = 6;
    pPars->nCutsMax = 8;
    pPars->nFlowIters = 2;
    pPars->nAreaIters = 1;
    pPars->nExploreIters = 0;
    pPars->fReverse = 1;
    pPars->fCutMin = 1;
    pPars->fSynthesis = 1;
    pPars->fPack = 1;
    pPars->fDiverse = 1;
    pPars->DelayTarget = -1;
}

/**Function*************************************************************

  Synopsis    [Folds buffers and degenerate ANDs before box ordering.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If3_ManFoldBuffers( Gia_Man_t * p )
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
    If3_ManOrderInterface(New, p);
    Gia_ManSetRegNum(New, Gia_ManRegNum(p));
    return New;
}

/**Function*************************************************************

  Synopsis    [Transfers timing and preserves interface metadata.]

  Description [Internal node names are left on the old GIA because its IDs change.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ManTransferMetadata( Gia_Man_t * pNew, Gia_Man_t * pOld )
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
static Gia_Man_t * If3_ManPerformMappingBase( Gia_Man_t * pGia, If3_Par_t * pPars )
{
    Gia_Man_t * pNew, * pTemp, * pOrder;
    Gia_Obj_t * pObj;
    int i;
    if ( pGia == NULL || pPars == NULL || pPars->nLutSize < 2 || pPars->nLutSize > IF3_LEAF_MAX || pPars->nCutsMax < 1 || pPars->nCutsMax > IF3_CUT_MAX || pPars->nFlowIters < 0 || pPars->nAreaIters < 0 || pPars->nExploreIters < 0 ) return NULL;
    if ( (size_t)Gia_ManObjNum(pGia) > ((size_t)-1) / sizeof(If3_Cut_t) / pPars->nCutsMax ) return NULL;
    if ( Gia_ManMuxNum(pGia) )
    {
        Abc_Print( -1, "&if3 currently requires an AIG without explicit MUX nodes.\n" );
        return NULL;
    }
    Gia_ManForEachAnd( pGia, pObj, i )
        if ( Gia_ObjSibl(pGia, i) >= i ) return NULL;
    if ( pPars->fSynthesis && !pGia->pManTime && !Gia_ManHasChoices(pGia) &&
         !Gia_ManXorNum(pGia) && !Gia_ManBufNum(pGia) && !pGia->fGiaSimple &&
         !pGia->vCiArrs && !pGia->vInArrs && !pGia->vCoReqs && !pGia->vOutReqs )
    {
        If3_Par_t Params = *pPars;
        pTemp = Gia_ManDch2Construct(pGia, !pPars->fArea, pPars->fVerbose);
        if ( pTemp )
        {
            Params.fSynthesis = 0;
            pNew = If3_ManPerformMappingBase(pTemp, &Params);
            pPars->Area = Params.Area;
            pPars->Edge = Params.Edge;
            pPars->Delay = Params.Delay;
            Gia_ManStop(pTemp);
            return pNew;
        }
    }
    if ( pGia->pManTime && Tim_ManBoxNum((Tim_Man_t *)pGia->pManTime) && (Gia_ManBufNum(pGia) || pGia->fGiaSimple) )
    {
        if ( Gia_ManHasChoices(pGia) )
        {
            Abc_Print(-1, "&if3 does not support boxed choices with buffers or simple gates.\n");
            return NULL;
        }
        pTemp = If3_ManFoldBuffers(pGia);
        If3_ManTransferMetadata(pTemp, pGia);
        pNew = If3_ManPerformMappingBase(pTemp, pPars);
        if ( pNew == NULL ) If3_ManTransferMetadata(pGia, pTemp);
        Gia_ManStop(pTemp);
        return pNew;
    }
    if ( pGia->pManTime && Tim_ManBoxNum((Tim_Man_t *)pGia->pManTime) && Gia_ManIsNormalized(pGia) )
    {
        pOrder = pGia;
        if ( Gia_ManRegNum(pGia) )
        {
            pOrder = Gia_ManDupUnshuffleInputs(pGia);
            If3_ManTransferMetadata(pOrder, pGia);
        }
        pTemp = Gia_ManDupUnnormalize(pOrder);
        if ( pTemp == NULL )
        {
            if ( pOrder != pGia ) { If3_ManTransferMetadata(pGia, pOrder); Gia_ManStop(pOrder); }
            return NULL;
        }
        If3_ManTransferMetadata(pTemp, pOrder);
        if ( pOrder != pGia ) Gia_ManStop(pOrder);
        pNew = If3_ManPerformMappingInt( pTemp, pPars );
        if ( pNew == NULL )
        {
            If3_ManTransferMetadata(pGia, pTemp);
            Gia_ManStop(pTemp);
            return NULL;
        }
        If3_ManTransferMetadata( pNew, pTemp );
        Gia_ManStop( pTemp );
        pTemp = pNew;
        pNew = Gia_ManDupNormalize( pTemp, 0 );
        Gia_ManTransferMapping( pNew, pTemp );
        If3_ManTransferMetadata( pNew, pTemp );
        Gia_ManStop( pTemp );
    }
    else
    {
        pNew = If3_ManPerformMappingInt( pGia, pPars );
        if ( pNew == NULL ) return NULL;
        If3_ManTransferMetadata( pNew, pGia );
    }
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Hashes a factored LUT implementation into a GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_ReexprGia( Gia_Man_t * q, Kit_Graph_t * Graph, Vec_Int_t * Fans )
{
    Kit_Node_t * Node;
    int i, a, b, Lit;
    int * Copies;
    if ( Kit_GraphIsConst(Graph) ) return Kit_GraphIsConst1(Graph);
    assert(Graph->nLeaves > 0 && Graph->eRoot.Node < (unsigned)Graph->nSize);
    Copies = ABC_ALLOC(int, Graph->nSize);
    for ( i = 0; i < Graph->nLeaves; i++ ) Copies[i] = Vec_IntEntry(Fans, i);
    Kit_GraphForEachNode(Graph, Node, i)
    {
        a = Copies[Node->eEdge0.Node] ^ Node->eEdge0.fCompl;
        b = Copies[Node->eEdge1.Node] ^ Node->eEdge1.fCompl;
        Copies[i] = Gia_ManHashAnd(q, a, b);
    }
    Lit = Copies[Graph->eRoot.Node] ^ Graph->eRoot.fCompl;
    ABC_FREE(Copies);
    return Lit;
}

// Re-express the selected LUTs with SOP and DSD implementations as choices.
typedef struct If3_Reexpr_t_ If3_Reexpr_t;
struct If3_Reexpr_t_
{
    word Truth;
    int nLeaves;
    Kit_Graph_t * Sop, * Dsd;
};

/**Function*************************************************************

  Synopsis    [Appends a factored graph with supplied leaf edges.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Kit_Edge_t If3_ReexprGraft( Kit_Graph_t * Result, Kit_Graph_t * Graph, Kit_Edge_t * Fans )
{
    Kit_Edge_t * Copies, Edge, a, b;
    Kit_Node_t * Node;
    int i;
    if ( Kit_GraphIsConst(Graph) )
    {
        Edge = Kit_GraphAddNodeAnd(Result, Kit_EdgeCreate(0, 0), Kit_EdgeCreate(0, 1));
        Edge.fCompl ^= Kit_GraphIsConst1(Graph);
        return Edge;
    }
    Copies = ABC_ALLOC(Kit_Edge_t, Graph->nSize);
    for ( i = 0; i < Graph->nLeaves; i++ ) Copies[i] = Fans[i];
    Kit_GraphForEachNode(Graph, Node, i)
    {
        a = Copies[Node->eEdge0.Node];
        b = Copies[Node->eEdge1.Node];
        a.fCompl ^= Node->eEdge0.fCompl;
        b.fCompl ^= Node->eEdge1.fCompl;
        Copies[i] = Kit_GraphAddNodeAnd(Result, a, b);
    }
    Edge = Copies[Graph->eRoot.Node];
    Edge.fCompl ^= Graph->eRoot.fCompl;
    ABC_FREE(Copies);
    return Edge;
}

/**Function*************************************************************

  Synopsis    [Builds an AIG expression from a disjoint-support decomposition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Kit_Edge_t If3_ReexprDsd_rec( Kit_DsdNtk_t * Ntk, int Lit, Kit_Graph_t * Result, Vec_Int_t * Cover )
{
    Kit_Edge_t Fans[6], Edge;
    Kit_DsdObj_t * Obj;
    Kit_Graph_t * Graph;
    int i, Id = Lit>>1;
    if ( Id < Ntk->nVars ) return Kit_EdgeCreate(Id, Lit&1);
    Obj = Kit_DsdNtkObj(Ntk, Id);
    for ( i = 0; i < (int)Obj->nFans; i++ ) Fans[i] = If3_ReexprDsd_rec(Ntk, Obj->pFans[i], Result, Cover);
    if ( Obj->Type == KIT_DSD_CONST1 )
    {
        Edge = Kit_GraphAddNodeAnd(Result, Kit_EdgeCreate(0, 0), Kit_EdgeCreate(0, 1));
        Edge.fCompl ^= 1;
    }
    else if ( Obj->Type == KIT_DSD_VAR ) Edge = Fans[0];
    else if ( Obj->Type == KIT_DSD_AND || Obj->Type == KIT_DSD_XOR )
    {
        assert(Obj->nFans > 1);
        Edge = Fans[0];
        for ( i = 1; i < (int)Obj->nFans; i++ )
            Edge = Obj->Type == KIT_DSD_AND ? Kit_GraphAddNodeAnd(Result, Edge, Fans[i]) : Kit_GraphAddNodeXor(Result, Edge, Fans[i], 0);
    }
    else
    {
        assert(Obj->Type == KIT_DSD_PRIME);
        Graph = Kit_TruthToGraph(Kit_DsdObjTruth(Obj), Obj->nFans, Cover);
        assert(Graph != NULL);
        Edge = If3_ReexprGraft(Result, Graph, Fans);
        Kit_GraphFree(Graph);
    }
    Edge.fCompl ^= Lit&1;
    return Edge;
}

/**Function*************************************************************

  Synopsis    [Computes the complete truth table of a LUT expression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word If3_ReexprTruth( Kit_Graph_t * Graph )
{
    word * Values, Value, a, b;
    Kit_Node_t * Node;
    int i;
    if ( Kit_GraphIsConst(Graph) ) return Kit_GraphIsConst1(Graph) ? ~(word)0 : 0;
    Values = ABC_ALLOC(word, Graph->nSize);
    for ( i = 0; i < Graph->nLeaves; i++ ) Values[i] = If3_PackVariable(i, 0);
    Kit_GraphForEachNode(Graph, Node, i)
    {
        a = Values[Node->eEdge0.Node];
        b = Values[Node->eEdge1.Node];
        Values[i] = (Node->eEdge0.fCompl ? ~a : a) & (Node->eEdge1.fCompl ? ~b : b);
    }
    Value = Values[Graph->eRoot.Node];
    if ( Graph->eRoot.fCompl ) Value = ~Value;
    ABC_FREE(Values);
    return Value;
}

/**Function*************************************************************

  Synopsis    [Releases cached LUT expressions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void If3_ReexprClear( If3_Reexpr_t * Cache )
{
    int i;
    for ( i = 0; i < 4096; i++ )
    {
        if ( Cache[i].Sop ) Kit_GraphFree(Cache[i].Sop);
        if ( Cache[i].Dsd ) Kit_GraphFree(Cache[i].Dsd);
    }
    memset(Cache, 0, sizeof(If3_Reexpr_t)*4096);
}

/**Function*************************************************************

  Synopsis    [Caches independently verified SOP and DSD expressions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static If3_Reexpr_t * If3_ReexprFind( If3_Reexpr_t * Cache, int * nEntries, word Truth, int nLeaves, Vec_Int_t * Cover )
{
    unsigned Words[2] = {(unsigned)Truth, (unsigned)(Truth>>32)};
    word Hash = Truth + ABC_CONST(0x9e3779b97f4a7c15)*(nLeaves+1);
    Kit_DsdNtk_t * Dsd;
    Kit_Edge_t Edge;
    If3_Reexpr_t * Entry;
    int i, Home, Bin;
    Hash = (Hash ^ (Hash >> 30))*ABC_CONST(0xbf58476d1ce4e5b9);
    Hash = (Hash ^ (Hash >> 27))*ABC_CONST(0x94d049bb133111eb);
    Home = Bin = (int)((Hash ^ (Hash >> 31))&4095);
    while ( Cache[Bin].Sop )
    {
        if ( Cache[Bin].Truth == Truth && Cache[Bin].nLeaves == nLeaves ) return Cache+Bin;
        Bin = (Bin+1)&4095;
    }
    if ( *nEntries == 2048 ) { If3_ReexprClear(Cache); *nEntries = 0; Bin = Home; }
    Entry = Cache+Bin;
    Entry->Truth = Truth;
    Entry->nLeaves = nLeaves;
    Entry->Sop = Kit_TruthToGraph(Words, nLeaves, Cover);
    assert(Entry->Sop != NULL);
    Dsd = Kit_DsdDecomposeExpand(Words, nLeaves);
    Entry->Dsd = Kit_GraphCreate(nLeaves);
    Edge = If3_ReexprDsd_rec(Dsd, Dsd->Root, Entry->Dsd, Cover);
    Kit_GraphSetRoot(Entry->Dsd, Edge);
    Kit_DsdNtkFree(Dsd);
    assert(If3_ReexprTruth(Entry->Sop) == Truth);
    assert(If3_ReexprTruth(Entry->Dsd) == Truth);
    if ( Entry->Dsd->nSize == Entry->Sop->nSize && Kit_EdgeToInt(Entry->Dsd->eRoot) == Kit_EdgeToInt(Entry->Sop->eRoot) )
    {
        for ( i = nLeaves; i < Entry->Dsd->nSize; i++ )
            if ( Kit_EdgeToInt(Entry->Dsd->pNodes[i].eEdge0) != Kit_EdgeToInt(Entry->Sop->pNodes[i].eEdge0) ||
                 Kit_EdgeToInt(Entry->Dsd->pNodes[i].eEdge1) != Kit_EdgeToInt(Entry->Sop->pNodes[i].eEdge1) ) break;
        if ( i == Entry->Dsd->nSize ) { Kit_GraphFree(Entry->Dsd); Entry->Dsd = NULL; }
    }
    (*nEntries)++;
    return Entry;
}

/**Function*************************************************************

  Synopsis    [Resolves signed construction equivalences with path compression.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int If3_ReexprEquivFind( Vec_Int_t * v, int Lit )
{
    int Root = Lit, Next;
    while ( ( Next = Vec_IntEntry( v, Root >> 1 ) ) != 2 * ( Root >> 1 ) ) Root = Next ^ ( Root & 1 );
    while ( ( Next = Vec_IntEntry( v, Lit >> 1 ) ) != 2 * ( Lit >> 1 ) )
    {
        Vec_IntWriteEntry( v, Lit >> 1, Root ^ ( Lit & 1 ) );
        Lit = Next ^ ( Lit & 1 );
    }
    return Root;
}
/**Function*************************************************************

  Synopsis    [Builds structural choices from equivalent expressions of mapped LUTs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * If3_Reexpress( Gia_Man_t * p, int fVerbose )
{
    Gia_Man_t * q = Gia_ManStart(Gia_ManObjNum(p)), * Result;
    Vec_Int_t * Copies = Vec_IntStartFull(Gia_ManObjNum(p));
    Vec_Int_t * Equivs = Vec_IntAlloc(Gia_ManObjNum(p));
    Vec_Int_t * Leaves = Vec_IntAlloc(6), * Fans = Vec_IntAlloc(6), * Cover = Vec_IntAlloc(128);
    If3_Reexpr_t * Cache = ABC_CALLOC(If3_Reexpr_t, 4096), * Entry;
    Gia_Obj_t * Obj;
    word Truth;
    int i, j, Leaf, Lit, Alt, a, b, nEntries = 0, Choices = 0;
    q->pName = Abc_UtilStrsav(p->pName);
    q->pSpec = Abc_UtilStrsav(p->pSpec);
    Gia_ManHashAlloc(q);
    Vec_IntWriteEntry(Copies, 0, 0);
    Gia_ManForEachCi(p, Obj, i) Vec_IntWriteEntry(Copies, Gia_ObjId(p, Obj), Gia_ManAppendCi(q));
    Gia_ObjComputeTruthTableStart(p, 6);
    Gia_ManForEachLut(p, i)
    {
        Vec_IntClear(Leaves);
        Vec_IntClear(Fans);
        Gia_LutForEachFanin(p, i, Leaf, j)
        {
            Vec_IntPush(Leaves, Leaf);
            Lit = Vec_IntEntry(Copies, Leaf);
            assert(Lit >= 0);
            Vec_IntPush(Fans, Lit);
        }
        Truth = *Gia_ObjComputeTruthTableCut(p, Gia_ManObj(p, i), Leaves);
        Entry = If3_ReexprFind(Cache, &nEntries, Truth, Vec_IntSize(Leaves), Cover);
        Alt = Entry->Dsd ? If3_ReexprGia(q, Entry->Dsd, Fans) : -1;
        Lit = If3_ReexprGia(q, Entry->Sop, Fans);
        for ( j = Vec_IntSize(Equivs); j < Gia_ManObjNum(q); j++ ) Vec_IntPush(Equivs, 2*j);
        if ( Alt >= 0 )
        {
            a = If3_ReexprEquivFind(Equivs, Alt);
            b = If3_ReexprEquivFind(Equivs, Lit);
            if ( a != b )
            {
                assert((a>>1) != (b>>1));
                if ( a > b ) ABC_SWAP(int, a, b);
                Vec_IntWriteEntry(Equivs, b>>1, a^(b&1));
                Choices++;
            }
        }
        // The literal union preserves the chosen implementation's polarity.
        Vec_IntWriteEntry(Copies, i, If3_ReexprEquivFind(Equivs, Alt >= 0 ? Alt : Lit));
    }
    Gia_ObjComputeTruthTableStop(p);
    Gia_ManForEachCo(p, Obj, i)
    {
        Lit = Vec_IntEntry(Copies, Gia_ObjFaninId0p(p, Obj));
        assert(Lit >= 0);
        Gia_ManAppendCo(q, Lit ^ Gia_ObjFaninC0(Obj));
    }
    Gia_ManHashStop(q);
    Gia_ManSetRegNum(q, Gia_ManRegNum(p));
    q->pReprs = ABC_CALLOC(Gia_Rpr_t, Gia_ManObjNum(q));
    for ( i = 0; i < Gia_ManObjNum(q); i++ ) Gia_ObjSetRepr(q, i, GIA_VOID);
    Gia_ManForEachAnd(q, Obj, i)
    {
        Lit = If3_ReexprEquivFind(Equivs, 2*i);
        if ( (Lit>>1) != i ) Gia_ObjSetRepr(q, i, Lit>>1);
    }
    q->pNexts = Gia_ManDeriveNexts(q);
    Gia_ManSetPhase(q);
    Result = Gia_ManDch2DeriveChoices(q);
    Gia_ManStop(q);
    if ( fVerbose && Result ) Abc_Print(1, "If3 shared LUT choices: %d equalities, %d choices, %d ANDs\n",
                                       Choices, Gia_ManChoiceNum(Result), Gia_ManAndNum(Result));
    // A second mapping is worthwhile only with sufficient alternatives.
    // Require at least one distinct choice per four mapped LUTs; in particular,
    // an empty choice set never triggers another complete mapping and packing.
    if ( Result && (long long)4*Gia_ManChoiceNum(Result) < Abc_MaxInt(1, Gia_ManLutNum(p)) )
    {
        Gia_ManStop(Result);
        Result = NULL;
    }
    If3_ReexprClear(Cache);
    ABC_FREE(Cache);
    Vec_IntFree(Copies);
    Vec_IntFree(Equivs);
    Vec_IntFree(Leaves);
    Vec_IntFree(Fans);
    Vec_IntFree(Cover);
    return Result;
}


/**Function*************************************************************

  Synopsis    [Recovers LUT area with construction choices and bounded resynthesis.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * If3_ManPerformMapping( Gia_Man_t * pGia, If3_Par_t * pPars )
{
    If3_Par_t Params;
    Gia_Man_t * Best, * Choice, * New;
    if ( !pGia || !pPars || pPars->nLutSize < 2 || pPars->nLutSize > IF3_LEAF_MAX ) return NULL;
    // For a network with very few free inputs, map the existing functions
    // directly before investing in structural choice synthesis.
    if ( Gia_ManCiNum(pGia) <= 2*pPars->nLutSize && !Gia_ManHasChoices(pGia) &&
         !pGia->pManTime && !pGia->vCiArrs && !pGia->vInArrs && !pGia->vCoReqs && !pGia->vOutReqs )
    {
        Params = *pPars;
        Params.fSynthesis = 0;
        Best = If3_ManPerformMappingBase(pGia, &Params);
        if ( Best )
        {
            pPars->Area = Params.Area;
            pPars->Edge = Params.Edge;
            pPars->Delay = Params.Delay;
        }
        return Best;
    }
    Best = If3_ManPerformMappingBase(pGia, pPars);
    if ( !Best || pGia->pManTime || pGia->vCiArrs || pGia->vInArrs || pGia->vCoReqs || pGia->vOutReqs ||
         Gia_ManBufNum(pGia) || !pPars->fPack || !pPars->fSynthesis || pPars->nAreaIters < 1 ) return Best;
    // Re-expression targets covers dense in input ANDs per mapped LUT.
    // This is a structural-density threshold, not a circuit-size threshold.
    if ( Gia_ManAndNum(pGia) <= (pPars->nLutSize+2)*(double)Abc_MaxInt(1,pPars->Area) ) return Best;
    Params = *pPars;
    Params.fSynthesis = 0;
    Params.nCutsMax = 12;
    Params.nFlowIters = 1;
    Params.nAreaIters = 1;
    Params.nExploreIters = 0;
    Params.DelayTarget = pPars->Delay;
    Choice = If3_Reexpress(Best, pPars->fVerbose);
    if ( !Choice ) return Best;
    New = If3_ManPerformMappingBase(Choice, &Params);
    Gia_ManStop(Choice);
    if ( New && (pPars->fArea || Params.Delay <= pPars->Delay+IF3_EPSILON) && Params.Area < pPars->Area )
    {
        Gia_ManStop(Best);
        Best = New;
        pPars->Area = Params.Area;
        pPars->Edge = Params.Edge;
        pPars->Delay = Params.Delay;
    }
    else if ( New ) Gia_ManStop(New);
    return Best;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
