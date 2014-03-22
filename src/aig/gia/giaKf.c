/**CFile****************************************************************

  FileName    [giaCutt.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCutt.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecSet.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define KF_PROC_MAX   8
#define KF_LEAF_MAX   8
#define KF_WORD_MAX  ((KF_LEAF_MAX > 6) ? 1 << (KF_LEAF_MAX-6) : 1)
#define KF_LOG_TABLE  8
#define KF_NUM_MAX   16

#define KF_ADD_ON1    2  // offset in cut storage for each node (cut count; best cut)
#define KF_ADD_ON2    4  // offset in cut storage for each cut (leaf count; function, cut delay; cut area)

typedef struct Kf_Cut_t_ Kf_Cut_t; 
typedef struct Kf_Set_t_ Kf_Set_t; 
typedef struct Kf_Man_t_ Kf_Man_t; 

struct Kf_Cut_t_
{
    word            Sign;        // signature
    int             Polar;       // polarity
    int             Delay;       // delay
    float           Area;        // area 
    int             iFunc;       // function 
    int             iNext;       // next cut
    int             nLeaves;     // number of leaves
    int             pLeaves[KF_LEAF_MAX]; 
};
struct Kf_Set_t_
{
    Kf_Man_t *      pMan;        // manager
    unsigned short  nLutSize;    // lut size
    unsigned short  nCutNum;     // cut count
    int             nCuts0;      // fanin0 cut count
    int             nCuts1;      // fanin1 cut count
    int             nCuts;       // resulting cut count
    int             nTEntries;   // hash table entries 
    int             TableMask;   // hash table mask
    int             pTable[1 << KF_LOG_TABLE];
    int             pValue[1 << KF_LOG_TABLE];
    int             pPlace[KF_LEAF_MAX];
    int             pList [KF_LEAF_MAX];
    Kf_Cut_t        pCuts0[KF_NUM_MAX];
    Kf_Cut_t        pCuts1[KF_NUM_MAX];
    Kf_Cut_t        pCutsR[KF_NUM_MAX*KF_NUM_MAX];
    Kf_Cut_t *      ppCuts[KF_NUM_MAX];
    word            CutCount[4]; // statistics
};
struct Kf_Man_t_
{
    Gia_Man_t *     pGia;        // user's manager
    Jf_Par_t *      pPars;       // user's parameters
    Vec_Set_t       pMem;        // cut storage
    Vec_Int_t       vCuts;       // node params
    Vec_Int_t       vTime;       // node params
    Vec_Flt_t       vArea;       // node params
    Vec_Flt_t       vRefs;       // node params
    Vec_Int_t *     vTemp;       // temporary
    abctime         clkStart;    // starting time
    Kf_Set_t        pSett[KF_PROC_MAX];
};

static inline int   Kf_SetCutId( Kf_Set_t * p, Kf_Cut_t * pCut )           { return pCut - p->pCutsR;               }
static inline Kf_Cut_t * Kf_SetCut( Kf_Set_t * p, int i )                  { return i >= 0 ? p->pCutsR + i : NULL;  }

static inline int   Kf_ObjTime( Kf_Man_t * p, int i )                      { return Vec_IntEntry(&p->vTime, i);     }
static inline float Kf_ObjArea( Kf_Man_t * p, int i )                      { return Vec_FltEntry(&p->vArea, i);     }
static inline float Kf_ObjRefs( Kf_Man_t * p, int i )                      { return Vec_FltEntry(&p->vRefs, i);     }

static inline void  Kf_ObjSetCuts( Kf_Man_t * p, int i, Vec_Int_t * vVec ) { Vec_IntWriteEntry(&p->vCuts, i, Vec_SetAppend(&p->pMem, Vec_IntArray(vVec), Vec_IntSize(vVec)));  }
static inline int * Kf_ObjCuts( Kf_Man_t * p, int i )                      { return (int *)Vec_SetEntry(&p->pMem, Vec_IntEntry(&p->vCuts, i));    }
static inline int * Kf_ObjCuts0( Kf_Man_t * p, int i )                     { return Kf_ObjCuts(p, Gia_ObjFaninId0(Gia_ManObj(p->pGia, i), i));    }
static inline int * Kf_ObjCuts1( Kf_Man_t * p, int i )                     { return Kf_ObjCuts(p, Gia_ObjFaninId1(Gia_ManObj(p->pGia, i), i));    }
static inline int * Kf_ObjCutBest( Kf_Man_t * p, int i )                   { int * pCuts = Kf_ObjCuts(p, i); return pCuts + pCuts[1];             }

#define Kf_ObjForEachCutInt( pList, pCut, i )         for ( i = 0, pCut = pList + KF_ADD_ON1; i < pList[0]; i++, pCut += pCut[0] + KF_ADD_ON2 )
#define Kf_ListForEachCutt( p, iList, pCut )          for ( pCut = Kf_SetCut(p, p->pList[iList]); pCut; pCut = Kf_SetCut(p, pCut->iNext) )
#define Kf_ListForEachCuttP( p, iList, pCut, pPlace ) for ( pPlace = p->pList+iList, pCut = Kf_SetCut(p, *pPlace); pCut; pCut = Kf_SetCut(p, *pPlace) )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Kf_SetLoadCuts( Kf_Cut_t * pCuts, int * pIntCuts )
{
    Kf_Cut_t * pCut;
    int k, * pIntCut, nCuts = 0; 
    Kf_ObjForEachCutInt( pIntCuts, pIntCut, nCuts )
    {
        pCut = pCuts + nCuts;
        pCut->Sign  = 0;
        pCut->Polar = 0;
        pCut->iFunc = pIntCut[pIntCut[0] + 1];
        pCut->Delay = pIntCut[pIntCut[0] + 2];
        pCut->Area  = Abc_Int2Float(pIntCut[pIntCut[0] + 3]);
        pCut->nLeaves = pIntCut[0];    
        for ( k = 0; k < pIntCut[0]; k++ )
        {
            pCut->pLeaves[k] = Abc_Lit2Var(pIntCut[k+1]);
            pCut->Sign |= ((word)1) << (pCut->pLeaves[k] & 0x3F);
            if ( Abc_LitIsCompl(pIntCut[k+1]) )
                pCut->Polar |= (1 << k);
        }
    }
    return nCuts;
}
static inline void Kf_SetPrepare( Kf_Set_t * p, int * pCuts0, int * pCuts1 )
{
    int i;
    // prepare hash table
    for ( i = 0; i <= p->TableMask; i++ )
        assert( p->pTable[i] == 0 );
    // prepare cut storage
    for ( i = 0; i <= p->nLutSize; i++ )
        p->pList[i] = -1;
    // transfer cuts
    p->nCuts0 = Kf_SetLoadCuts( p->pCuts0, pCuts0 );
    p->nCuts1 = Kf_SetLoadCuts( p->pCuts1, pCuts1 );
    p->nCuts = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Kf_ManStoreStart( Vec_Int_t * vTemp, int nCuts )
{
    Vec_IntClear( vTemp );
    Vec_IntPush( vTemp, nCuts );                // cut count
    Vec_IntPush( vTemp, -1 );                   // best offset
}
static inline void Kf_ManStoreAddUnit( Vec_Int_t * vTemp, int iObj, int Time, float Area )
{
    Vec_IntAddToEntry( vTemp, 0, 1 );
    Vec_IntPush( vTemp, 1 );                    // cut size
    Vec_IntPush( vTemp, Abc_Var2Lit(iObj, 0) ); // leaf
    Vec_IntPush( vTemp, 2 );                    // function
    Vec_IntPush( vTemp, Time );                 // delay
    Vec_IntPush( vTemp, Abc_Float2Int(Area) );  // area
}
static inline void Kf_ManSaveResults( Kf_Cut_t ** ppCuts, int nCuts, Kf_Cut_t * pCutBest, Vec_Int_t * vTemp )
{
    int i, k;
    assert( nCuts > 0 && nCuts < KF_NUM_MAX );
    Kf_ManStoreStart( vTemp, nCuts );
    for ( i = 0; i < nCuts; i++ )
    {
        if ( ppCuts[i] == pCutBest )
            Vec_IntWriteEntry( vTemp, 1, Vec_IntSize(vTemp) );
        Vec_IntPush( vTemp, ppCuts[i]->nLeaves );
//        Vec_IntPushArray( vTemp, ppCuts[i]->pLeaves, ppCuts[i]->nLeaves );
        for ( k = 0; k < ppCuts[i]->nLeaves; k++ )
            Vec_IntPush( vTemp, Abc_Var2Lit(ppCuts[i]->pLeaves[k], 0) );
        Vec_IntPush( vTemp, ppCuts[i]->iFunc );
        Vec_IntPush( vTemp, ppCuts[i]->Delay );
        Vec_IntPush( vTemp, Abc_Float2Int(ppCuts[i]->Area) );
    }
    assert( Vec_IntEntry(vTemp, 1) > 0 );
}
static inline int Kf_SetCompareCuts( Kf_Cut_t * p1, Kf_Cut_t * p2 )
{
    if ( p1 == NULL || p2 == NULL )
        return (p1 != NULL) - (p2 != NULL);
    if ( p1->nLeaves != p2->nLeaves )
        return p1->nLeaves - p2->nLeaves;
    return memcmp( p1->pLeaves, p2->pLeaves, sizeof(int)*p1->nLeaves );
}
static inline void Kf_SetAddToList( Kf_Set_t * p, Kf_Cut_t * pCut, int fSort )
{
    if ( !fSort )
        pCut->iNext = p->pList[pCut->nLeaves], p->pList[pCut->nLeaves] = Kf_SetCutId(p, pCut);
    else
    {
        int Value, * pPlace;
        Kf_Cut_t * pTemp;
        Vec_IntSelectSort( pCut->pLeaves, pCut->nLeaves );
        Kf_ListForEachCuttP( p, pCut->nLeaves, pTemp, pPlace )
        {
            if ( (Value = Kf_SetCompareCuts(pTemp, pCut)) > 0 )
                break;
            assert( Value < 0 );
            pPlace = &pTemp->iNext;
        }
        pCut->iNext = *pPlace, *pPlace = Kf_SetCutId(p, pCut);
    }
}
static inline int Kf_CutCompare( Kf_Cut_t * pCut0, Kf_Cut_t * pCut1, int fArea )
{
    if ( fArea )
    {
        if ( pCut0->Area    < pCut1->Area )    return -1;
        if ( pCut0->Area    > pCut1->Area )    return  1;
        if ( pCut0->Delay   < pCut1->Delay )   return -1;
        if ( pCut0->Delay   > pCut1->Delay )   return  1;
        if ( pCut0->nLeaves < pCut1->nLeaves ) return -1;
        if ( pCut0->nLeaves > pCut1->nLeaves ) return  1;
    }
    else
    {
        if ( pCut0->Delay   < pCut1->Delay )   return -1;
        if ( pCut0->Delay   > pCut1->Delay )   return  1;
        if ( pCut0->nLeaves < pCut1->nLeaves ) return -1;
        if ( pCut0->nLeaves > pCut1->nLeaves ) return  1;
        if ( pCut0->Area    < pCut1->Area )    return -1;
        if ( pCut0->Area    > pCut1->Area )    return  1;
    }
    return 0;
}
static inline int Kf_SetStoreAddOne( Kf_Set_t * p, int nCuts, int nCutNum, Kf_Cut_t * pCut, int fArea )
{
    int i;
    p->ppCuts[nCuts] = pCut;
    if ( nCuts == 0 )
        return 1;
    for ( i = nCuts; i > 0; i-- )
        if ( Kf_CutCompare(p->ppCuts[i-1], p->ppCuts[i], fArea) > 0 )
            ABC_SWAP( Kf_Cut_t *, p->ppCuts[i-1], p->ppCuts[i] )
        else
            break;
    return Abc_MinInt( nCuts+1, nCutNum );
}
static inline Kf_Cut_t * Kf_SetSelectBest( Kf_Set_t * p, int fArea, int fSort )
{
//    int fArea = p->pMan->pPars->fArea;
    Kf_Cut_t * pCut, * pCutBest;
    int i, nCuts = 0;
    for ( i = 0; i <= p->nLutSize; i++ )
        Kf_ListForEachCutt( p, i, pCut )
            nCuts = Kf_SetStoreAddOne( p, nCuts, p->nCutNum-1, pCut, fArea );
    assert( nCuts > 0 && nCuts < p->nCutNum );
    p->nCuts = nCuts;
    if ( !fSort )
        return p->ppCuts[0];
    // sort by size in the reverse order
    pCutBest = p->ppCuts[0];
    for ( i = 0; i <= p->nLutSize; i++ )
        p->pList[i] = -1;
    for ( i = 0; i < nCuts; i++ )
        Kf_SetAddToList( p, p->ppCuts[i], 0 );
    p->nCuts = 0;
    for ( i = p->nLutSize; i >= 0; i-- )
        Kf_ListForEachCutt( p, i, pCut )
            p->ppCuts[p->nCuts++] = pCut;
    assert( p->nCuts == nCuts );
    return pCutBest;
}

/**Function*************************************************************

  Synopsis    [Hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Kf_HashLookup( Kf_Set_t * p, int i )
{
    int k;
    assert( i > 0 );
    for ( k = i & p->TableMask; p->pTable[k]; k = (k + 1) & p->TableMask )
        if ( p->pTable[k] == i )
            return -1;
    return k;
}
static inline int Kf_HashFindOrAdd( Kf_Set_t * p, int i )
{
    int k = Kf_HashLookup( p, i );
    if ( k == -1 )
        return 0;
    if ( p->nTEntries == p->nLutSize )
        return 1;
    assert( p->pTable[k] == 0 );
    p->pTable[k] = i;
    p->pPlace[p->nTEntries] = k;
    p->pValue[k] = p->nTEntries++;
    return 0;
}
static inline void Kf_HashPopulate( Kf_Set_t * p, Kf_Cut_t * pCut )
{
    int i;
    assert( p->nTEntries == 0 );
    for ( i = 0; i < pCut->nLeaves; i++ )
        Kf_HashFindOrAdd( p, pCut->pLeaves[i] );
    assert( p->nTEntries == pCut->nLeaves );
}
static inline void Kf_HashCleanup( Kf_Set_t * p, int iStart )
{
    int i;
    for ( i = iStart; i < p->nTEntries; i++ )
        p->pPlace[i] = 0;
    p->nTEntries = iStart;
}

/**Function*************************************************************

  Synopsis    [Cut merging with arbitary order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// returns 1 if the cut in hash table is dominated by the given one
static inline int Kf_SetCutDominatedByThis( Kf_Set_t * p, Kf_Cut_t * pCut )
{
    int i;
    for ( i = 0; i < pCut->nLeaves; i++ )
        if ( Kf_HashLookup(p, pCut->pLeaves[i]) >= 0 )
            return 0;
    return 1;
}
static inline int Kf_SetRemoveDuplicates( Kf_Set_t * p, int nLeaves, word Sign )
{
    Kf_Cut_t * pCut; 
    Kf_ListForEachCutt( p, nLeaves, pCut )
        if ( pCut->Sign == Sign && Kf_SetCutDominatedByThis(p, pCut) )
            return 1;
    return 0;
}
static inline void Kf_SetFilter( Kf_Set_t * p )
{
    Kf_Cut_t * pCut0, * pCut1; 
    int i, k, * pPlace;
    assert( p->nCuts > 0 );
    for ( i = 0; i <= p->nLutSize; i++ )
        Kf_ListForEachCuttP( p, i, pCut0, pPlace )
        {
            Kf_HashPopulate( p, pCut0 );
            for ( k = 0; k < pCut0->nLeaves; k++ )
                Kf_ListForEachCutt( p, k, pCut1 )
                    if ( (pCut0->Sign & pCut1->Sign) == pCut1->Sign && Kf_SetCutDominatedByThis(p, pCut1) )
                        { k = pCut0->nLeaves + 1; p->nCuts--; break; }
            if ( k == pCut0->nLeaves + 1 ) // remove pCut0
                *pPlace = pCut0->iNext;
            else
                pPlace = &pCut0->iNext;
            Kf_HashCleanup( p, 0 );
        }
    assert( p->nCuts > 0 );
}
static inline void Kf_SetMergePairs( Kf_Set_t * p, Kf_Cut_t * pCut0, Kf_Cut_t * pCuts, int nCuts, int fArea )
{
    Kf_Cut_t * pCut1, * pCutR;  int i;
    Kf_HashPopulate( p, pCut0 );
    for ( pCut1 = pCuts; pCut1 < pCuts + nCuts; pCut1++ )
    {
        Kf_HashCleanup( p, pCut0->nLeaves );
        for ( i = 0; i < pCut1->nLeaves; i++ )
            if ( Kf_HashFindOrAdd(p, pCut1->pLeaves[i]) )
                break;
        if ( i < pCut1->nLeaves )
            continue;
        if ( Kf_SetRemoveDuplicates(p, p->nTEntries, pCut0->Sign | pCut1->Sign) )
            continue;
        // create new cut
        pCutR = p->pCutsR + p->nCuts++;
        pCutR->nLeaves = p->nTEntries;
        for ( i = 0; i < p->nTEntries; i++ )
            pCutR->pLeaves[i] = p->pTable[p->pPlace[i]];
        pCutR->Sign  = pCut0->Sign | pCut1->Sign;
        pCutR->Delay = Abc_MaxInt(pCut0->Delay, pCut1->Delay);
        pCutR->Area  = pCut0->Area + pCut1->Area;
        // add new cut
        Kf_SetAddToList( p, pCutR, 0 );
    }
    Kf_HashCleanup( p, 0 );
}
static inline Kf_Cut_t * Kf_SetMerge( Kf_Set_t * p, int * pCuts0, int * pCuts1, int fArea, int fCutMin )
{
    int c0, c1;
    Kf_SetPrepare( p, pCuts0, pCuts1 );
    for ( c0 = c1 = 0; c0 < p->nCuts0 && c1 < p->nCuts1; )
    {
        if ( p->pCuts0[c0].nLeaves >= p->pCuts1[c1].nLeaves )
            Kf_SetMergePairs( p, p->pCuts0 + c0++, p->pCuts1 + c1, p->nCuts1 - c1, fArea );
        else 
            Kf_SetMergePairs( p, p->pCuts1 + c1++, p->pCuts0 + c0, p->nCuts0 - c0, fArea );
    }
    Kf_SetFilter( p );
    p->CutCount[3] += Abc_MinInt( p->nCuts, p->nCutNum );
    return Kf_SetSelectBest( p, fArea, 1 );
}

/**Function*************************************************************

  Synopsis    [Cut merging with fixed order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Kf_SetCountBits( word i )
{
    i = i - ((i >> 1) & 0x5555555555555555);
    i = (i & 0x3333333333333333) + ((i >> 2) & 0x3333333333333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F0F0F0F0F);
    return (i*(0x0101010101010101))>>56;
}
static inline word Kf_SetCutGetSign( Kf_Cut_t * p )
{
    word Sign = 0; int i; 
    for ( i = 0; i < p->nLeaves; i++ )
        Sign |= ((word)1) << (p->pLeaves[i] & 0x3F);
    return Sign;
}
static inline int Kf_SetCutIsContainedOrder( Kf_Cut_t * pBase, Kf_Cut_t * pCut ) // check if pCut is contained in pBase
{
    int nSizeB = pBase->nLeaves;
    int nSizeC = pCut->nLeaves;
    int i, k;
    if ( nSizeB == nSizeC )
    {
        for ( i = 0; i < nSizeB; i++ )
            if ( pBase->pLeaves[i] != pCut->pLeaves[i] )
                return 0;
        return 1;
    }
    assert( nSizeB > nSizeC ); 
    for ( i = k = 0; i < nSizeB; i++ )
    {
        if ( pBase->pLeaves[i] > pCut->pLeaves[k] )
            return 0;
        if ( pBase->pLeaves[i] == pCut->pLeaves[k] )
        {
            if ( k++ == nSizeC )
                return 1;
        }
    }
    return 0;
}
static inline int Kf_SetMergeOrder( Kf_Cut_t * pCut0, Kf_Cut_t * pCut1, Kf_Cut_t * pCut, int nLutSize )
{ 
    int nSize0 = pCut0->nLeaves;
    int nSize1 = pCut1->nLeaves;
    int * pC0 = pCut0->pLeaves;
    int * pC1 = pCut1->pLeaves;
    int * pC = pCut->pLeaves;
    int i, k, c;
    // the case of the largest cut sizes
    if ( nSize0 == nLutSize && nSize1 == nLutSize )
    {
        for ( i = 0; i < nSize0; i++ )
        {
            if ( pC0[i] != pC1[i] )  return 0;
            pC[i] = pC0[i];
        }
        pCut->nLeaves = nLutSize;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = 0;
    while ( 1 )
    {
        if ( c == nLutSize ) return 0;
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
    if ( c + nSize0 > nLutSize + i ) return 0;
    while ( i < nSize0 )
        pC[c++] = pC0[i++];
    pCut->nLeaves = c;
    return 1;

FlushCut1:
    if ( c + nSize1 > nLutSize + k ) return 0;
    while ( k < nSize1 )
        pC[c++] = pC1[k++];
    pCut->nLeaves = c;
    return 1;
}
static inline int Kf_SetRemoveDuplicates2( Kf_Set_t * p, Kf_Cut_t * pCutNew )
{
    Kf_Cut_t * pCut;
    Kf_ListForEachCutt( p, pCutNew->nLeaves, pCut )
        if ( pCut->Sign == pCutNew->Sign && Kf_SetCutIsContainedOrder(pCut, pCutNew) )
            return 1;
    return 0;
}
static inline void Kf_SetFilter2( Kf_Set_t * p )
{
    Kf_Cut_t * pCut0, * pCut1; 
    int i, k, * pPlace;
    assert( p->nCuts > 0 );
    for ( i = 0; i <= p->nLutSize; i++ )
        Kf_ListForEachCuttP( p, i, pCut0, pPlace )
        {
            for ( k = 0; k < pCut0->nLeaves; k++ )
                Kf_ListForEachCutt( p, k, pCut1 )
                    if ( (pCut0->Sign & pCut1->Sign) == pCut1->Sign && Kf_SetCutIsContainedOrder(pCut0, pCut1) )
                        { k = pCut0->nLeaves + 1; p->nCuts--; break; }
            if ( k == pCut0->nLeaves + 1 ) // remove pCut0
                *pPlace = pCut0->iNext;
            else
                pPlace = &pCut0->iNext;
        }
    assert( p->nCuts > 0 );
}
/*
int Kf_SetComputeTruth( Kf_Man_t * p, int iFuncLit0, int iFuncLit1, int * pCut0, int * pCut1, int * pCutOut )
{
    word uTruth[JF_WORD_MAX], uTruth0[JF_WORD_MAX], uTruth1[JF_WORD_MAX];
    int fCompl, truthId;
    int LutSize    = p->pPars->nLutSize;
    int nWords     = Abc_Truth6WordNum(p->pPars->nLutSize);
    word * pTruth0 = Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(iFuncLit0));
    word * pTruth1 = Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(iFuncLit1));
    Abc_TtCopy( uTruth0, pTruth0, nWords, Abc_LitIsCompl(iFuncLit0) );
    Abc_TtCopy( uTruth1, pTruth1, nWords, Abc_LitIsCompl(iFuncLit1) );
    Abc_TtStretch( uTruth0, LutSize, pCut0 + 1, Kf_CutSize(pCut0), pCutOut + 1, Kf_CutSize(pCutOut) );
    Abc_TtStretch( uTruth1, LutSize, pCut1 + 1, Kf_CutSize(pCut1), pCutOut + 1, Kf_CutSize(pCutOut) );
    fCompl         = (int)(uTruth0[0] & uTruth1[0] & 1);
    Abc_TtAnd( uTruth, uTruth0, uTruth1, nWords, fCompl );
    pCutOut[0]     = Abc_TtMinBase( uTruth, pCutOut + 1, pCutOut[0], LutSize );
    assert( (uTruth[0] & 1) == 0 );
    truthId        = Vec_MemHashInsert(p->vTtMem, uTruth);
    return Abc_Var2Lit( truthId, fCompl );
}
*/
static inline Kf_Cut_t * Kf_SetMerge2( Kf_Set_t * p, int * pCuts0, int * pCuts1, int fArea, int fCutMin )
{
    Kf_Cut_t * pCut0, * pCut1, * pCutR;
    Kf_SetPrepare( p, pCuts0, pCuts1 );
    p->CutCount[0] += p->nCuts0 * p->nCuts1;
    for ( pCut0 = p->pCuts0; pCut0 < p->pCuts0 + p->nCuts0; pCut0++ )
    for ( pCut1 = p->pCuts1; pCut1 < p->pCuts1 + p->nCuts1; pCut1++ )
    {
        if ( Kf_SetCountBits(pCut0->Sign | pCut1->Sign) > p->nLutSize )
            continue;
        p->CutCount[1]++;        
        pCutR = p->pCutsR + p->nCuts;
        if ( !Kf_SetMergeOrder(pCut0, pCut1, pCutR, p->nLutSize) )
            continue;
        p->CutCount[2]++;        
        pCutR->Sign = pCut0->Sign | pCut1->Sign;
        if ( Kf_SetRemoveDuplicates2(p, pCutR) )
            continue;
        p->nCuts++;
        if ( fCutMin )
        {
            int nOldSupp = pCutR->nLeaves;
//            pCutR->iFunc = Kf_SetComputeTruth( p, pCut0->iFunc, pCut1->iFunc, pCut0, pCut1, pCutR );
            assert( pCutR->nLeaves <= nOldSupp );
            if ( pCutR->nLeaves < nOldSupp )
                pCutR->Sign = Kf_SetCutGetSign( pCutR );
            // delay and area are inaccurate
        }
        assert( pCutR->nLeaves > 1 );
        pCutR->Delay = Abc_MaxInt(pCut0->Delay, pCut1->Delay);
        pCutR->Area  = pCut0->Area + pCut1->Area;
        // add new cut
        Kf_SetAddToList( p, pCutR, 0 );
    }
    Kf_SetFilter2( p );
    p->CutCount[3] += Abc_MinInt( p->nCuts, p->nCutNum-1 );
    return Kf_SetSelectBest( p, fArea, 0 );
}


/**Function*************************************************************

  Synopsis    [Cut operations.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int  Kf_CutSize( int * pCut )         { return pCut[0];                          } 
static inline int  Kf_CutFunc( int * pCut )         { return pCut[pCut[0] + 1];                } 
static inline int  Kf_CutLeaf( int * pCut, int i )  { assert(i); return Abc_Lit2Var(pCut[i]);  }
static inline int  Kf_CutTime( Kf_Man_t * p, int * pCut )
{
    int i, Time = 0;
    for ( i = 1; i <= Kf_CutSize(pCut); i++ )
        Time = Abc_MaxInt( Time, Kf_ObjTime(p, Kf_CutLeaf(pCut, i)) );
    return Time + 1; 
}
static inline void Kf_CutRef( Kf_Man_t * p, int * pCut )
{
    int i;
    for ( i = 1; i <= Kf_CutSize(pCut); i++ )
        Gia_ObjRefIncId( p->pGia, Kf_CutLeaf(pCut, i) );
}
static inline void Kf_CutDeref( Kf_Man_t * p, int * pCut )
{
    int i;
    for ( i = 1; i <= Kf_CutSize(pCut); i++ )
        Gia_ObjRefDecId( p->pGia, Kf_CutLeaf(pCut, i) );
}
static inline void Kf_CutPrint( int * pCut )
{
    int i; 
    printf( "%d {", Kf_CutSize(pCut) );
    for ( i = 1; i <= Kf_CutSize(pCut); i++ )
        printf( " %d", Kf_CutLeaf(pCut, i) );
    printf( " } Func = %d\n", Kf_CutFunc(pCut) );
}
static inline void Gia_CutPrintSetPrint( int * pCuts )
{
    int i, * pCut; 
    Kf_ObjForEachCutInt( pCuts, pCut, i )
        Kf_CutPrint( pCut );
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Computing delay/area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kf_ManComputeDelay( Kf_Man_t * p, int fEval )
{
    Gia_Obj_t * pObj; 
    int i, Delay = 0;
    if ( fEval )
    {
        Gia_ManForEachAnd( p->pGia, pObj, i )
            if ( Gia_ObjRefNum(p->pGia, pObj) > 0 )
                Vec_IntWriteEntry( &p->vTime, i, Kf_CutTime(p, Kf_ObjCutBest(p, i)) );
    }
    Gia_ManForEachCoDriver( p->pGia, pObj, i )
    {
        assert( Gia_ObjRefNum(p->pGia, pObj) > 0 );
        Delay = Abc_MaxInt( Delay, Kf_ObjTime(p, Gia_ObjId(p->pGia, pObj)) );
    }
    return Delay;
}
int Kf_ManComputeRefs( Kf_Man_t * p )
{
    Gia_Obj_t * pObj; 
    float nRefsNew; int i, * pCut;
    float * pRefs = Vec_FltArray(&p->vRefs);
    float * pFlow = Vec_FltArray(&p->vArea);
    assert( p->pGia->pRefs != NULL );
    memset( p->pGia->pRefs, 0, sizeof(int) * Gia_ManObjNum(p->pGia) );
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachObjReverse( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) )
            Gia_ObjRefInc( p->pGia, Gia_ObjFanin0(pObj) );
        else if ( Gia_ObjIsAnd(pObj) && Gia_ObjRefNum(p->pGia, pObj) > 0 )
        {
            pCut = Kf_ObjCutBest(p, i);
            Kf_CutRef( p, pCut );
            p->pPars->Edge += Kf_CutSize(pCut);
            p->pPars->Area++;
        }
    }
    // blend references and normalize flow
    for ( i = 0; i < Gia_ManObjNum(p->pGia); i++ )
    {
        if ( p->pPars->fOptEdge )
            nRefsNew = Abc_MaxFloat( 1, 0.8 * pRefs[i] + 0.2 * p->pGia->pRefs[i] );
        else
            nRefsNew = Abc_MaxFloat( 1, 0.2 * pRefs[i] + 0.8 * p->pGia->pRefs[i] );
        pFlow[i] = pFlow[i] * pRefs[i] / nRefsNew;
        pRefs[i] = nRefsNew;
        assert( pFlow[i] >= 0 );
    }
    // compute delay
    p->pPars->Delay = Kf_ManComputeDelay( p, 1 );
    return p->pPars->Area;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kf_ManPrintStats( Kf_Man_t * p, char * pTitle )
{
    if ( !p->pPars->fVerbose )
        return;
    printf( "%s :  ", pTitle );
    printf( "Level =%6lu   ", p->pPars->Delay );
    printf( "Area =%9lu   ",  p->pPars->Area );
    printf( "Edge =%9lu   ",  p->pPars->Edge );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    fflush( stdout );
}
void Kf_ManComputeMapping( Kf_Man_t * p )
{
    Kf_Cut_t * pCutBest;
    Gia_Obj_t * pObj; int i;
    if ( p->pPars->fVerbose )
    {
        printf( "Aig: CI = %d  CO = %d  AND = %d    ", Gia_ManCiNum(p->pGia), Gia_ManCoNum(p->pGia), Gia_ManAndNum(p->pGia) );
        printf( "LutSize = %d  CutMax = %d  Rounds = %d\n", p->pPars->nLutSize, p->pPars->nCutNum, p->pPars->nRounds );
        printf( "Computing cuts...\r" );
        fflush( stdout );
    }
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
        {
            Kf_ManStoreStart( p->vTemp, 0 );
            Kf_ManStoreAddUnit( p->vTemp, i, 0, 0 );
            assert( Vec_IntSize(p->vTemp) == 1 + KF_ADD_ON1 + KF_ADD_ON2 );
            Kf_ObjSetCuts( p, i, p->vTemp );
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            pCutBest = Kf_SetMerge2( p->pSett, Kf_ObjCuts0(p, i), Kf_ObjCuts1(p, i), p->pPars->fAreaOnly, p->pPars->fCutMin );
//            pCutBest = Kf_SetMerge( p->pSett, Kf_ObjCuts0(p, i), Kf_ObjCuts1(p, i), p->pPars->fAreaOnly, p->pPars->fCutMin );
            Kf_ManSaveResults( p->pSett->ppCuts, p->pSett->nCuts, pCutBest, p->vTemp );
            Vec_IntWriteEntry( &p->vTime, i, pCutBest->Delay + 1 );
            Vec_FltWriteEntry( &p->vArea, i, (pCutBest->Area + 1)/Kf_ObjRefs(p, i) );
            if ( pCutBest->nLeaves > 1 )
                Kf_ManStoreAddUnit( p->vTemp, i, Kf_ObjTime(p, i), Kf_ObjArea(p, i) );
            Kf_ObjSetCuts( p, i, p->vTemp );
//            Gia_CutPrintSetPrint( Kf_ObjCuts(p, i) );
        }
    }
    Kf_ManComputeRefs( p );
    if ( p->pPars->fVerbose )
    {
        printf( "CutPair = %lu  ", p->pSett->CutCount[0] );
        printf( "Merge = %lu  ",   p->pSett->CutCount[1] );
        printf( "Eval = %lu  ",    p->pSett->CutCount[2] );
        printf( "Cut = %lu  ",     p->pSett->CutCount[3] );
        Abc_PrintTime( 1, "Time",  Abc_Clock() - p->clkStart );
        printf( "Memory:  " );
        printf( "Gia = %.2f MB  ", Gia_ManMemory(p->pGia) / (1<<20) );
        printf( "Man = %.2f MB  ", 4.0 * sizeof(int) * Gia_ManObjNum(p->pGia) / (1<<20) );
        printf( "Cuts = %.2f MB  ",Vec_ReportMemory(&p->pMem) / (1<<20) );
        printf( "Set = %.2f KB  ", 1.0 * sizeof(Kf_Set_t) / (1<<10) );
        printf( "\n" );
        fflush( stdout );
        Kf_ManPrintStats( p, "Start" );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kf_ManSetInitRefs( Gia_Man_t * p, Vec_Flt_t * vRefs )
{
    Gia_Obj_t * pObj, * pCtrl, * pData0, * pData1; int i;
    Vec_FltFill( vRefs, Gia_ManObjNum(p), 0 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Vec_FltAddToEntry( vRefs, Gia_ObjFaninId0(pObj, i), 1 );
        Vec_FltAddToEntry( vRefs, Gia_ObjFaninId1(pObj, i), 1 );
        if ( !Gia_ObjIsMuxType(pObj) )
            continue;
        // discount XOR/MUX
        pCtrl = Gia_ObjRecognizeMux( pObj, &pData1, &pData0 );
        Vec_FltAddToEntry( vRefs, Gia_ObjId(p, Gia_Regular(pCtrl)), -1 );
        if ( Gia_Regular(pData0) == Gia_Regular(pData1) )
            Vec_FltAddToEntry( vRefs, Gia_ObjId(p, Gia_Regular(pData0)), -1 );
    }
    Gia_ManForEachCo( p, pObj, i )
        Vec_FltAddToEntry( vRefs, Gia_ObjFaninId0(pObj, Gia_ObjId(p, pObj)), 1 );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Vec_FltUpdateEntry( vRefs, i, 1 );
}
Kf_Man_t * Kf_ManAlloc( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    Kf_Man_t * p; int i;
    assert( pPars->nLutSizeMax <= KF_LEAF_MAX );
    assert( pPars->nCutNumMax  <= KF_NUM_MAX  );
    assert( pPars->nProcNumMax <= KF_PROC_MAX );
    Vec_IntFreeP( &pGia->vMapping );
    p = ABC_CALLOC( Kf_Man_t, 1 );
    p->clkStart  = Abc_Clock();
    p->pGia      = pGia;
    p->pPars     = pPars;
    Vec_SetAlloc_( &p->pMem, 20 );
    Vec_IntFill( &p->vCuts, Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vTime, Gia_ManObjNum(pGia), 0 );
    Vec_FltFill( &p->vArea, Gia_ManObjNum(pGia), 0 );
    Kf_ManSetInitRefs( pGia, &p->vRefs );
    p->vTemp     = Vec_IntAlloc( 1000 );
    pGia->pRefs  = ABC_CALLOC( int, Gia_ManObjNum(pGia) );
    // prepare cut sets
    for ( i = 0; i < pPars->nProcNumMax; i++ )
    {
        (p->pSett + i)->pMan      = p;
        (p->pSett + i)->nLutSize  = (unsigned short)pPars->nLutSize;
        (p->pSett + i)->nCutNum   = (unsigned short)pPars->nCutNum;
        (p->pSett + i)->TableMask = (1 << KF_LOG_TABLE) - 1;
    }
    return p;
}
void Kf_ManFree( Kf_Man_t * p )
{
    ABC_FREE( p->pGia->pRefs );
    ABC_FREE( p->vCuts.pArray );
    ABC_FREE( p->vTime.pArray );
    ABC_FREE( p->vArea.pArray );
    ABC_FREE( p->vRefs.pArray );
    Vec_IntFreeP( &p->vTemp );
    Vec_SetFree_( &p->pMem );
    ABC_FREE( p );
}
Gia_Man_t * Kf_ManDerive( Kf_Man_t * p )
{
    Vec_Int_t * vMapping;
    Gia_Obj_t * pObj; 
    int i, k, * pCut;
    assert( !p->pPars->fCutMin );
    vMapping = Vec_IntAlloc( Gia_ManObjNum(p->pGia) + (int)p->pPars->Edge + (int)p->pPars->Area * 2 );
    Vec_IntFill( vMapping, Gia_ManObjNum(p->pGia), 0 );
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) || Gia_ObjRefNum(p->pGia, pObj) == 0 )
            continue;
        pCut = Kf_ObjCutBest( p, i );
        Vec_IntWriteEntry( vMapping, i, Vec_IntSize(vMapping) );
        Vec_IntPush( vMapping, Kf_CutSize(pCut) );
        for ( k = 1; k <= Kf_CutSize(pCut); k++ )
            Vec_IntPush( vMapping, Kf_CutLeaf(pCut, k) );
        Vec_IntPush( vMapping, i );
    }
    assert( Vec_IntCap(vMapping) == 16 || Vec_IntSize(vMapping) == Vec_IntCap(vMapping) );
    p->pGia->vMapping = vMapping;
//    Gia_ManMappingVerify( p->pGia );
    return p->pGia;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kf_ManSetDefaultPars( Jf_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Jf_Par_t) );
    pPars->nLutSize     =  6;
    pPars->nCutNum      =  8;
    pPars->nRounds      =  1;
    pPars->nVerbLimit   =  5;
    pPars->DelayTarget  = -1;
    pPars->fAreaOnly    =  1;
    pPars->fOptEdge     =  1; 
    pPars->fCoarsen     =  0;
    pPars->fCutMin      =  0;
    pPars->fFuncDsd     =  0;
    pPars->fGenCnf      =  0;
    pPars->fPureAig     =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    pPars->nLutSizeMax  =  KF_LEAF_MAX;
    pPars->nCutNumMax   =  KF_NUM_MAX;
    pPars->nProcNumMax  =  1;
}
Gia_Man_t * Kf_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    Kf_Man_t * p;
    Gia_Man_t * pNew;
    p = Kf_ManAlloc( pGia, pPars );
    Kf_ManComputeMapping( p );
    pNew = Kf_ManDerive( p );
    Kf_ManFree( p );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

