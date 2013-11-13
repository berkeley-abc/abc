/**CFile****************************************************************

  FileName    [giaCut.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCut.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__aig__gia__giaAig_h
#define ABC__aig__gia__giaAig_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "gia.h"

ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

#define GIA_CUT_LEAF_MAX   8
#define GIA_CUT_WORD_MAX  ((GIA_CUT_LEAF_MAX > 6) ? 1 << (GIA_CUT_LEAF_MAX-6) : 1)
#define GIA_CUT_NUM_MAX   16

typedef struct Gia_Cut_t_ Gia_Cut_t; 
struct Gia_Cut_t_
{
    word             Sign;        // signature
    int              Id;          // cut ID
    int              iFunc;       // function 
    int              iNext;       // next cut
    int              iFan0;       // left child
    int              iFan1;       // right child
    int              nLeaves;     // number of leaves
    int              pLeaves[GIA_CUT_LEAF_MAX]; // cut
    int              pCompls[GIA_CUT_LEAF_MAX]; // polarity
};

static inline int    Gia_CutSize( int * pCut )       { return pCut[0] & 0xF; }  //  4 bits

#define Gia_ObjForEachCut( pList, pCut, i, AddOn )   for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += Gia_CutSize(pCut) + AddOn )

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

// loads cuts from storage
static inline int Gia_ObjLoadCuts( Gia_Cut_t * pCutsI, int * pCuts, int AddOn )
{
    Gia_Cut_t * pCutsICur;
    int i, k, Lit, * pCut; 
    assert( AddOn == 1 || AddOn == 2 );
    Gia_ObjForEachCut( pCuts, pCut, i, AddOn )
    {
        pCutsICur = pCutsI + i;
        pCutsICur->Id = i;
        pCutsICur->Sign = 0;
        pCutsICur->iFunc = (AddOn == 1) ? -1 : pCut[pCut[0] + 1];
        pCutsICur->nLeaves = pCut[0];    
        for ( k = 0; k < pCut[0]; k++ )
        {
            Lit = pCut[k+1];
            pCutsICur->pCompls[k] = Abc_LitIsCompl(Lit);
            pCutsICur->pLeaves[k] = Abc_Lit2Var(Lit);
            pCutsICur->Sign |= 1 << (Abc_Lit2Var(Lit) & 0x3F);
        }
    }
    return i;
}

static inline int Gia_CutId( Gia_Cut_t * pCutsOut, Gia_Cut_t * pCut )
{
    return pCut - pCutsOut;
}
static inline void Gia_CutInsert( Gia_Cut_t * pCutsOut, Gia_Cut_t * pCut ) // inserts cut into the list
{
    int * pPlace = &pCutsOut[pCut->nLeaves].iNext;
    pCut->iNext = *pPlace; *pPlace = pCut - pCutsOut;
}
static inline void Gia_CutRemove( int * pPlace, Gia_Cut_t * pCut ) // removes cut from the list
{
    *pPlace = pCut->iNext;
}
static inline word Gia_CutGetSign( Gia_Cut_t * pCut )
{
    word Sign = 0; int i; 
    for ( i = 0; i < pCut->nLeaves; i++ )
        Sign |= ((word)1) << (pCut->pLeaves[i] & 0x3F);
    return Sign;
}
static inline int Gia_CutCountBits( word i )
{
    i = i - ((i >> 1) & 0x5555555555555555);
    i = (i & 0x3333333333333333) + ((i >> 2) & 0x3333333333333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F0F0F0F0F);
    return (i*(0x0101010101010101))>>56;
}

static inline int Gia_CutIsContainedOrder( Gia_Cut_t * pBase, Gia_Cut_t * pCut ) // check if pCut is contained pBase
{
    int i, k;
    if ( pBase->nLeaves == pCut->nLeaves )
    {
        for ( i = 1; i <= pCut->nLeaves; i++ )
            if ( pBase->pLeaves[i] != pCut->pLeaves[i] )
                return 0;
        return 1;
    }
    assert( pBase->nLeaves > pCut->nLeaves ); 
    for ( i = k = 1; i <= pBase->nLeaves; i++ )
    {
        if ( pBase->pLeaves[i] > pCut->pLeaves[k] )
            return 0;
        if ( pBase->pLeaves[i] == pCut->pLeaves[k] )
        {
            if ( k++ == pCut->nLeaves )
                return 1;
        }
    }
    return 0;
}


// check if the given cut is contained in previous cuts
static inline int Gia_ObjCheckContainInPrev( Gia_Cut_t * pCutsOut, Gia_Cut_t * pCut )
{
    Gia_Cut_t * pPrev;
    for ( pPrev = pCutsOut; pPrev->iNext; pPrev = pCutsOut + pPrev->iNext )
    {
        if ( pPrev->iFunc == -2 ) // skip sentinels
            continue;
        if ( pPrev->nLeaves > pCut->nLeaves ) // stop when we reached bigger cuts
            return 0;
        if ( (pCut->Sign & pPrev->Sign) != pPrev->Sign )
            continue;
        if ( Gia_CutIsContainedOrder(pPrev, pCut) )
            return 1;
    }
    assert( 0 );
    return 1;
}

// check if the given cut contains following cuts
static inline void Gia_ObjCheckContainsNext( Gia_Cut_t * pCutsOut, Gia_Cut_t * pCut, int ** ppPlace )
{
    Gia_Cut_t * pNext;
    int * pPlace = &pCut->iNext;
    while ( *pPlace )
    {
        pNext = pCutsOut + pNext->iNext;
        if ( pNext->iFunc == -2 ) // skip sentinels
            continue;
        assert( pNext != pCut && pNext->nLeaves >= pCut->nLeaves );
        if ( (pNext->Sign & pCut->Sign) != pCut->Sign )
            continue;
        if ( !Gia_CutIsContainedOrder(pCut, pNext) )
        {
            pPlace = &pNext->iNext;
            continue;
        }
        // shift the pointer
        if ( *ppPlace == &pNext->iNext )
            *ppPlace = pPlace;
         // remove pNext
        Gia_CutRemove( pPlace, pNext );
    }
}

static inline int Gia_ObjMergeCutsOrder( Gia_Cut_t * pCut, Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, int LutSize )
{
    int nSize0 = pCut0->nLeaves;
    int nSize1 = pCut1->nLeaves;
    int * pC0 = pCut0->pLeaves;
    int * pC1 = pCut1->pLeaves;
    int * pC = pCut->pLeaves;
    int i, k, c, s;
    // the case of the largest cut sizes
    if ( nSize0 == LutSize && nSize1 == LutSize )
    {
        for ( i = 0; i < nSize0; i++ )
        {
            if ( pC0[i] != pC1[i] )
                return 0;
            pC[i] = pC0[i];
        }
        pCut->nLeaves = LutSize;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = s = 0;
    while ( 1 )
    {
        if ( c == LutSize ) return 0;
        if ( pC0[i] < pC1[k] )
        {
            pC[c++] = pC0[i++];
            if ( i >= nSize0 ) goto FlushCut1;
        }
        else if ( pC0[i] > pC1[k] )
        {
            pC[c++] = pC1[k++];
            if ( k >= nSize1 ) goto FlushCut0;
        }
        else
        {
            pC[c++] = pC0[i++]; k++;
            if ( i >= nSize0 ) goto FlushCut1;
            if ( k >= nSize1 ) goto FlushCut0;
        }
    }

FlushCut0:
    if ( c + nSize0 > LutSize + i ) return 0;
    while ( i < nSize0 )
        pC[c++] = pC0[i++];
    pCut->nLeaves = c;
    return 1;

FlushCut1:
    if ( c + nSize1 > LutSize + k ) return 0;
    while ( k < nSize1 )
        pC[c++] = pC1[k++];
    pCut->nLeaves = c;
    return 1;
}

static inline int Gia_ObjCombineCuts( Gia_Cut_t * pCutsOut, Gia_Cut_t * pCut, Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, int LutSize )
{
    if ( !Gia_ObjMergeCutsOrder(pCut, pCut0, pCut1, LutSize) )
        return 0;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    if ( !Gia_ObjCheckContainInPrev(pCutsOut, pCut) )
        return 0;
    Gia_CutInsert( pCutsOut, pCut );
    pCut->Id = pCut - pCutsOut;
    pCut->iFan0 = pCut0->Id;
    pCut->iFan1 = pCut1->Id;
    pCut->iFunc = -1;
    return 1;
}

int Gia_TtComputeForCut( Vec_Mem_t * vTtMem, int iFuncLit0, int iFuncLit1, Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, Gia_Cut_t * pCut, int LutSize )
{
    word uTruth[GIA_CUT_WORD_MAX], uTruth0[GIA_CUT_WORD_MAX], uTruth1[GIA_CUT_WORD_MAX];
    int fCompl, truthId;
    int nWords     = Abc_Truth6WordNum(LutSize);
    word * pTruth0 = Vec_MemReadEntry(vTtMem, Abc_Lit2Var(iFuncLit0));
    word * pTruth1 = Vec_MemReadEntry(vTtMem, Abc_Lit2Var(iFuncLit1));
    Abc_TtCopy( uTruth0, pTruth0, nWords, Abc_LitIsCompl(iFuncLit0) );
    Abc_TtCopy( uTruth1, pTruth1, nWords, Abc_LitIsCompl(iFuncLit1) );
    Abc_TtStretch( uTruth0, LutSize, pCut0->pLeaves, pCut0->nLeaves, pCut->pLeaves, pCut->nLeaves );
    Abc_TtStretch( uTruth1, LutSize, pCut1->pLeaves, pCut1->nLeaves, pCut->pLeaves, pCut->nLeaves );
    fCompl         = (int)(uTruth0[0] & uTruth1[0] & 1);
    Abc_TtAnd( uTruth, uTruth0, uTruth1, nWords, fCompl );
    pCut->nLeaves  = Abc_TtMinBase( uTruth, pCut->pLeaves, pCut->nLeaves, LutSize );
    assert( (uTruth[0] & 1) == 0 );
    truthId        = Vec_MemHashInsert(vTtMem, uTruth);
    return Abc_Var2Lit( truthId, fCompl );
}

//  Gia_Cut_t pCutsOut[GIA_CUT_LEAF_MAX + 2 + GIA_CUT_NUM_MAX * GIA_CUT_NUM_MAX]; // LutSize+1 placeholders + CutNum ^ 2 + 1
static inline int Gia_ObjComputeCuts( Gia_Cut_t * pCutsOut, int * pCuts0, int * pCuts1, Vec_Mem_t * vTtMem, int AddOn, int nLutSize, int nCutNum, int fCompl0, int fCompl1 )
{
    Gia_Cut_t * pCut;
    Gia_Cut_t pCuts0i[GIA_CUT_NUM_MAX];
    Gia_Cut_t pCuts1i[GIA_CUT_NUM_MAX];
    int i, nCuts0i = Gia_ObjLoadCuts( pCuts0i, pCuts0, AddOn );
    int k, nCuts1i = Gia_ObjLoadCuts( pCuts1i, pCuts1, AddOn );
    int * pPlace, c = GIA_CUT_NUM_MAX + 1;
    assert( nCuts0i <= GIA_CUT_NUM_MAX );
    assert( nCuts1i <= GIA_CUT_NUM_MAX );
    // prepare cuts
    for ( i = 0; i <= GIA_CUT_NUM_MAX; i++ )
    {
        pCut = pCutsOut + i;
        pCut->nLeaves =   i;
        pCut->iNext   = i+1;
        pCut->iFunc   =  -2;
        pCut->Id      =   i;
    }
    pCut->iNext = 0;
    // enumerate pairs
    for ( i = 0; i < nCuts0i; i++ )
    for ( k = 0; k < nCuts1i; k++ )
        if ( Gia_CutCountBits(pCuts0i[i].Sign | pCuts1i[k].Sign) <= nLutSize )
            Gia_ObjCombineCuts( pCutsOut, pCutsOut + c++, pCuts0i + i, pCuts1i + k, nLutSize );
    assert( c <= GIA_CUT_LEAF_MAX + 2 + GIA_CUT_NUM_MAX * GIA_CUT_NUM_MAX );
    // check containment for cuts
    for ( pPlace = &pCutsOut->iNext; *pPlace; pPlace = &pCut->iNext )
    {
        pCut = pCutsOut + *pPlace;
        if ( pCut->iFunc == -2 )
            continue;
        // compute truth table
        if ( AddOn == 2 )
        {
            Gia_Cut_t * pCut0 = pCuts0i + pCut->iFan0;
            Gia_Cut_t * pCut1 = pCuts1i + pCut->iFan1;
            int iLit0 = Abc_LitNotCond( pCut0->iFunc, fCompl0 );
            int iLit1 = Abc_LitNotCond( pCut1->iFunc, fCompl1 );
            int nLeavesOld = pCut->nLeaves;
            pCut->iFunc = Gia_TtComputeForCut( vTtMem, iLit0, iLit1, pCut0, pCut1, pCut, nLutSize );
            // if size has changed, move the cut closer
            if ( nLeavesOld != pCut->nLeaves )
            {
                Gia_CutRemove( pPlace, pCut );
                Gia_CutInsert( pCutsOut, pCut );
                pCut->Sign = Gia_CutGetSign( pCut );
            }
        }
        // check containment after this cut
        Gia_ObjCheckContainsNext( pCutsOut, pCut, &pPlace );
    }
}


ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

