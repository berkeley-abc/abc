/**CFile****************************************************************

  FileName    [giaCut.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Stand-alone cut computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaCut.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/util/utilTruth.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define GIA_MAX_CUTSIZE    8
#define GIA_MAX_CUTNUM     257
#define GIA_MAX_TT_WORDS   ((GIA_MAX_CUTSIZE > 6) ? 1 << (GIA_MAX_CUTSIZE-6) : 1)

#define GIA_CUT_NO_LEAF   0xF

typedef struct Gia_Cut_t_ Gia_Cut_t; 
struct Gia_Cut_t_
{
    word            Sign;                      // signature
    int             iFunc;                     // functionality
    int             Cost;                      // cut cost
    int             CostLev;                   // cut cost
    unsigned        nTreeLeaves  : 28;         // tree leaves
    unsigned        nLeaves      :  4;         // leaf count
    int             pLeaves[GIA_MAX_CUTSIZE];  // leaves
    float           CostF;
};

typedef struct Gia_Sto_t_ Gia_Sto_t; 
struct Gia_Sto_t_
{
    int             nCutSize;
    int             nCutNum;
    int             fCutMin;
    int             fTruthMin;
    int             fVerbose;
    Gia_Man_t *     pGia;                      // user's AIG manager (will be modified by adding nodes)
    Vec_Int_t *     vRefs;                     // refs for each node
    Vec_Wec_t *     vCuts;                     // cuts for each node
    Vec_Mem_t *     vTtMem;                    // truth tables
    Gia_Cut_t       pCuts[3][GIA_MAX_CUTNUM];  // temporary cuts
    Gia_Cut_t *     ppCuts[GIA_MAX_CUTNUM];    // temporary cut pointers
    int             nCutsR;                    // the number of cuts
    int             Pivot;                     // current object
    int             iCutBest;                  // best-delay cut
    int             nCutsOver;                 // overflow cuts
    double          CutCount[4];               // cut counters
    abctime         clkStart;                  // starting time
};

static inline word * Gia_CutTruth( Gia_Sto_t * p, Gia_Cut_t * pCut ) { return Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut->iFunc));           }

#define Sdb_ForEachCut( pList, pCut, i ) for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += pCut[0] + 2 )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Check correctness of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Gia_CutGetSign( Gia_Cut_t * pCut )
{
    word Sign = 0; int i; 
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        Sign |= ((word)1) << (pCut->pLeaves[i] & 0x3F);
    return Sign;
}
static inline int Gia_CutCheck( Gia_Cut_t * pBase, Gia_Cut_t * pCut ) // check if pCut is contained in pBase
{
    int nSizeB = pBase->nLeaves;
    int nSizeC = pCut->nLeaves;
    int i, * pB = pBase->pLeaves;
    int k, * pC = pCut->pLeaves;
    for ( i = 0; i < nSizeC; i++ )
    {
        for ( k = 0; k < nSizeB; k++ )
            if ( pC[i] == pB[k] )
                break;
        if ( k == nSizeB )
            return 0;
    }
    return 1;
}
static inline int Gia_CutSetCheckArray( Gia_Cut_t ** ppCuts, int nCuts )
{
    Gia_Cut_t * pCut0, * pCut1; 
    int i, k, m, n, Value;
    assert( nCuts > 0 );
    for ( i = 0; i < nCuts; i++ )
    {
        pCut0 = ppCuts[i];
        assert( pCut0->nLeaves <= GIA_MAX_CUTSIZE );
        assert( pCut0->Sign == Gia_CutGetSign(pCut0) );
        // check duplicates
        for ( m = 0; m < (int)pCut0->nLeaves; m++ )
        for ( n = m + 1; n < (int)pCut0->nLeaves; n++ )
            assert( pCut0->pLeaves[m] < pCut0->pLeaves[n] );
        // check pairs
        for ( k = 0; k < nCuts; k++ )
        {
            pCut1 = ppCuts[k];
            if ( pCut0 == pCut1 )
                continue;
            // check containments
            Value = Gia_CutCheck( pCut0, pCut1 );
            assert( Value == 0 );
        }
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_CutMergeOrder( Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, Gia_Cut_t * pCut, int nCutSize )
{ 
    int nSize0   = pCut0->nLeaves;
    int nSize1   = pCut1->nLeaves;
    int i, * pC0 = pCut0->pLeaves;
    int k, * pC1 = pCut1->pLeaves;
    int c, * pC  = pCut->pLeaves;
    // the case of the largest cut sizes
    if ( nSize0 == nCutSize && nSize1 == nCutSize )
    {
        for ( i = 0; i < nSize0; i++ )
        {
            if ( pC0[i] != pC1[i] )  return 0;
            pC[i] = pC0[i];
        }
        pCut->nLeaves = nCutSize;
        pCut->iFunc = -1;
        pCut->Sign = pCut0->Sign | pCut1->Sign;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = 0;
    if ( nSize0 == 0 ) goto FlushCut1;
    if ( nSize1 == 0 ) goto FlushCut0;
    while ( 1 )
    {
        if ( c == nCutSize ) return 0;
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
    if ( c + nSize0 > nCutSize + i ) return 0;
    while ( i < nSize0 )
        pC[c++] = pC0[i++];
    pCut->nLeaves = c;
    pCut->iFunc = -1;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;

FlushCut1:
    if ( c + nSize1 > nCutSize + k ) return 0;
    while ( k < nSize1 )
        pC[c++] = pC1[k++];
    pCut->nLeaves = c;
    pCut->iFunc = -1;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;
}
static inline int Gia_CutMergeOrder2( Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, Gia_Cut_t * pCut, int nCutSize )
{ 
    int x0, i0 = 0, nSize0 = pCut0->nLeaves, * pC0 = pCut0->pLeaves;
    int x1, i1 = 0, nSize1 = pCut1->nLeaves, * pC1 = pCut1->pLeaves;
    int xMin, c = 0, * pC  = pCut->pLeaves;
    while ( 1 )
    {
        x0 = (i0 == nSize0) ? ABC_INFINITY : pC0[i0];
        x1 = (i1 == nSize1) ? ABC_INFINITY : pC1[i1];
        xMin = Abc_MinInt(x0, x1);
        if ( xMin == ABC_INFINITY ) break;
        if ( c == nCutSize ) return 0;
        pC[c++] = xMin;
        if (x0 == xMin) i0++;
        if (x1 == xMin) i1++;
    }
    pCut->nLeaves = c;
    pCut->iFunc = -1;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;
}
static inline int Gia_CutSetCutIsContainedOrder( Gia_Cut_t * pBase, Gia_Cut_t * pCut ) // check if pCut is contained in pBase
{
    int i, nSizeB = pBase->nLeaves;
    int k, nSizeC = pCut->nLeaves;
    if ( nSizeB == nSizeC )
    {
        for ( i = 0; i < nSizeB; i++ )
            if ( pBase->pLeaves[i] != pCut->pLeaves[i] )
                return 0;
        return 1;
    }
    assert( nSizeB > nSizeC ); 
    if ( nSizeC == 0 )
        return 1;
    for ( i = k = 0; i < nSizeB; i++ )
    {
        if ( pBase->pLeaves[i] > pCut->pLeaves[k] )
            return 0;
        if ( pBase->pLeaves[i] == pCut->pLeaves[k] )
        {
            if ( ++k == nSizeC )
                return 1;
        }
    }
    return 0;
}
static inline int Gia_CutSetLastCutIsContained( Gia_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[i]->nLeaves <= pCuts[nCuts]->nLeaves && (pCuts[i]->Sign & pCuts[nCuts]->Sign) == pCuts[i]->Sign && Gia_CutSetCutIsContainedOrder(pCuts[nCuts], pCuts[i]) )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_CutCompare2( Gia_Cut_t * pCut0, Gia_Cut_t * pCut1 )
{
    if ( pCut0->nTreeLeaves < pCut1->nTreeLeaves )  return -1;
    if ( pCut0->nTreeLeaves > pCut1->nTreeLeaves )  return  1;
    if ( pCut0->nLeaves     < pCut1->nLeaves )      return -1;
    if ( pCut0->nLeaves     > pCut1->nLeaves )      return  1;
    return 0;
}
static inline int Gia_CutCompare( Gia_Cut_t * pCut0, Gia_Cut_t * pCut1 )
{
    if ( pCut0->CostF       > pCut1->CostF )         return -1;
    if ( pCut0->CostF       < pCut1->CostF )         return  1;
    if ( pCut0->nLeaves     < pCut1->nLeaves )      return -1;
    if ( pCut0->nLeaves     > pCut1->nLeaves )      return  1;
    return 0;
}
static inline int Gia_CutSetLastCutContains( Gia_Cut_t ** pCuts, int nCuts )
{
    int i, k, fChanges = 0;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[nCuts]->nLeaves < pCuts[i]->nLeaves && (pCuts[nCuts]->Sign & pCuts[i]->Sign) == pCuts[nCuts]->Sign && Gia_CutSetCutIsContainedOrder(pCuts[i], pCuts[nCuts]) )
            pCuts[i]->nLeaves = GIA_CUT_NO_LEAF, fChanges = 1;
    if ( !fChanges )
        return nCuts;
    for ( i = k = 0; i <= nCuts; i++ )
    {
        if ( pCuts[i]->nLeaves == GIA_CUT_NO_LEAF )
            continue;
        if ( k < i )
            ABC_SWAP( Gia_Cut_t *, pCuts[k], pCuts[i] );
        k++;
    }
    return k - 1;
}
static inline void Gia_CutSetSortByCost( Gia_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = nCuts; i > 0; i-- )
    {
        if ( Gia_CutCompare(pCuts[i - 1], pCuts[i]) < 0 )//!= 1 )
            return;
        ABC_SWAP( Gia_Cut_t *, pCuts[i - 1], pCuts[i] );
    }
}
static inline int Gia_CutSetAddCut( Gia_Cut_t ** pCuts, int nCuts, int nCutNum )
{
    if ( nCuts == 0 )
        return 1;
    nCuts = Gia_CutSetLastCutContains(pCuts, nCuts);
    assert( nCuts >= 0 );
    Gia_CutSetSortByCost( pCuts, nCuts );
    // add new cut if there is room
    return Abc_MinInt( nCuts + 1, nCutNum - 1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_CutComputeTruth6( Gia_Sto_t * p, Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, int fCompl0, int fCompl1, Gia_Cut_t * pCutR, int fIsXor )
{
    int nOldSupp = pCutR->nLeaves, truthId, fCompl; word t;
    word t0 = *Gia_CutTruth(p, pCut0);
    word t1 = *Gia_CutTruth(p, pCut1);
    if ( Abc_LitIsCompl(pCut0->iFunc) ^ fCompl0 ) t0 = ~t0;
    if ( Abc_LitIsCompl(pCut1->iFunc) ^ fCompl1 ) t1 = ~t1;
    t0 = Abc_Tt6Expand( t0, pCut0->pLeaves, pCut0->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t1 = Abc_Tt6Expand( t1, pCut1->pLeaves, pCut1->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t =  fIsXor ? t0 ^ t1 : t0 & t1;
    if ( (fCompl = (int)(t & 1)) ) t = ~t;
    if ( p->fTruthMin )
        pCutR->nLeaves = Abc_Tt6MinBase( &t, pCutR->pLeaves, pCutR->nLeaves );
    assert( (int)(t & 1) == 0 );
    truthId        = Vec_MemHashInsert(p->vTtMem, &t);
    pCutR->iFunc   = Abc_Var2Lit( truthId, fCompl );
    assert( (int)pCutR->nLeaves <= nOldSupp );
    return (int)pCutR->nLeaves < nOldSupp;
}
static inline int Gia_CutComputeTruth( Gia_Sto_t * p, Gia_Cut_t * pCut0, Gia_Cut_t * pCut1, int fCompl0, int fCompl1, Gia_Cut_t * pCutR, int fIsXor )
{
    if ( p->nCutSize <= 6 )
        return Gia_CutComputeTruth6( p, pCut0, pCut1, fCompl0, fCompl1, pCutR, fIsXor );
    {
    word uTruth[GIA_MAX_TT_WORDS], uTruth0[GIA_MAX_TT_WORDS], uTruth1[GIA_MAX_TT_WORDS];
    int nOldSupp   = pCutR->nLeaves, truthId;
    int nCutSize   = p->nCutSize, fCompl;
    int nWords     = Abc_Truth6WordNum(nCutSize);
    word * pTruth0 = Gia_CutTruth(p, pCut0);
    word * pTruth1 = Gia_CutTruth(p, pCut1);
    Abc_TtCopy( uTruth0, pTruth0, nWords, Abc_LitIsCompl(pCut0->iFunc) ^ fCompl0 );
    Abc_TtCopy( uTruth1, pTruth1, nWords, Abc_LitIsCompl(pCut1->iFunc) ^ fCompl1 );
    Abc_TtExpand( uTruth0, nCutSize, pCut0->pLeaves, pCut0->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    Abc_TtExpand( uTruth1, nCutSize, pCut1->pLeaves, pCut1->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    if ( fIsXor )
        Abc_TtXor( uTruth, uTruth0, uTruth1, nWords, (fCompl = (int)((uTruth0[0] ^ uTruth1[0]) & 1)) );
    else
        Abc_TtAnd( uTruth, uTruth0, uTruth1, nWords, (fCompl = (int)((uTruth0[0] & uTruth1[0]) & 1)) );
    if ( p->fTruthMin )
        pCutR->nLeaves = Abc_TtMinBase( uTruth, pCutR->pLeaves, pCutR->nLeaves, nCutSize );
    assert( (uTruth[0] & 1) == 0 );
//Kit_DsdPrintFromTruth( uTruth, pCutR->nLeaves ), printf("\n" ), printf("\n" );
    truthId        = Vec_MemHashInsert(p->vTtMem, uTruth);
    pCutR->iFunc   = Abc_Var2Lit( truthId, fCompl );
    assert( (int)pCutR->nLeaves <= nOldSupp );
    return (int)pCutR->nLeaves < nOldSupp;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_CutCountBits( word i )
{
    i = i - ((i >> 1) & 0x5555555555555555);
    i = (i & 0x3333333333333333) + ((i >> 2) & 0x3333333333333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F0F0F0F0F);
    return (i*(0x0101010101010101))>>56;
}
static inline void Gia_CutAddUnit( Gia_Sto_t * p, int iObj )
{
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    if ( Vec_IntSize(vThis) == 0 )
        Vec_IntPush( vThis, 1 );
    else 
        Vec_IntAddToEntry( vThis, 0, 1 );
    Vec_IntPush( vThis, 1 );
    Vec_IntPush( vThis, iObj );
    Vec_IntPush( vThis, 2 );
}
static inline void Gia_CutAddZero( Gia_Sto_t * p, int iObj )
{
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    assert( Vec_IntSize(vThis) == 0 );
    Vec_IntPush( vThis, 1 );
    Vec_IntPush( vThis, 0 );
    Vec_IntPush( vThis, 0 );
}
static inline int Gia_CutTreeLeaves( Gia_Sto_t * p, Gia_Cut_t * pCut )
{
    int i, Cost = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        Cost += Vec_IntEntry( p->vRefs, pCut->pLeaves[i] ) == 1;
    return Cost;
}
static inline float Gia_CutGetCost( Gia_Sto_t * p, Gia_Cut_t * pCut )
{
    int i, Cost = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        Cost += Vec_IntEntry( p->vRefs, pCut->pLeaves[i] );
    return (float)Cost / Abc_MaxInt(1, pCut->nLeaves);
}
static inline int Gia_StoPrepareSet( Gia_Sto_t * p, int iObj, int Index )
{
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    int i, v, * pCut, * pList = Vec_IntArray( vThis );
    Sdb_ForEachCut( pList, pCut, i )
    {
        Gia_Cut_t * pCutTemp = &p->pCuts[Index][i];
        pCutTemp->nLeaves = pCut[0];
        for ( v = 1; v <= pCut[0]; v++ )
            pCutTemp->pLeaves[v-1] = pCut[v];
        pCutTemp->iFunc = pCut[pCut[0]+1];
        pCutTemp->Sign = Gia_CutGetSign( pCutTemp );
        pCutTemp->nTreeLeaves = Gia_CutTreeLeaves( p, pCutTemp );
        pCutTemp->CostF = Gia_CutGetCost( p, pCutTemp );
    }
    return pList[0];
}
static inline void Gia_StoInitResult( Gia_Sto_t * p )
{
    int i; 
    for ( i = 0; i < GIA_MAX_CUTNUM; i++ )
        p->ppCuts[i] = &p->pCuts[2][i];
}
static inline void Gia_StoStoreResult( Gia_Sto_t * p, int iObj, Gia_Cut_t ** pCuts, int nCuts )
{
    int i, v;
    Vec_Int_t * vList = Vec_WecEntry( p->vCuts, iObj );
    Vec_IntPush( vList, nCuts );
    for ( i = 0; i < nCuts; i++ )
    {
        Vec_IntPush( vList, pCuts[i]->nLeaves );
        for ( v = 0; v < (int)pCuts[i]->nLeaves; v++ )
            Vec_IntPush( vList, pCuts[i]->pLeaves[v] );
        Vec_IntPush( vList, pCuts[i]->iFunc );
    }
}
static inline void Gia_CutPrint( Gia_Sto_t * p, int iObj, Gia_Cut_t * pCut )
{
    int i, nDigits = Abc_Base10Log(Gia_ManObjNum(p->pGia)); 
    if ( pCut == NULL ) { printf( "No cut.\n" ); return; }
    printf( "%d  {", pCut->nLeaves );
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        printf( " %*d", nDigits, pCut->pLeaves[i] );
    for ( ; i < (int)p->nCutSize; i++ )
        printf( " %*s", nDigits, " " );
    printf( "  }  Cost = %3d  CostL = %3d  Tree = %d  ", 
        pCut->Cost, pCut->CostLev, pCut->nTreeLeaves );
    printf( "\n" );
}
void Gia_StoMergeCuts( Gia_Sto_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    int fIsXor       = Gia_ObjIsXor(pObj);
    int nCutSize     = p->nCutSize;
    int nCutNum      = p->nCutNum;
    int fComp0       = Gia_ObjFaninC0(pObj);
    int fComp1       = Gia_ObjFaninC1(pObj);
    int Fan0         = Gia_ObjFaninId0(pObj, iObj);
    int Fan1         = Gia_ObjFaninId1(pObj, iObj);
    int nCuts0       = Gia_StoPrepareSet( p, Fan0, 0 );
    int nCuts1       = Gia_StoPrepareSet( p, Fan1, 1 );
    int i, k, nCutsR = 0;
    Gia_Cut_t * pCut0, * pCut1, ** pCutsR = p->ppCuts;
    assert( !Gia_ObjIsBuf(pObj) );
    assert( !Gia_ObjIsMux(p->pGia, pObj) );
    Gia_StoInitResult( p );
    p->CutCount[0] += nCuts0 * nCuts1;
    for ( i = 0, pCut0 = p->pCuts[0]; i < nCuts0; i++, pCut0++ )
    for ( k = 0, pCut1 = p->pCuts[1]; k < nCuts1; k++, pCut1++ )
    {
        if ( (int)(pCut0->nLeaves + pCut1->nLeaves) > nCutSize && Gia_CutCountBits(pCut0->Sign | pCut1->Sign) > nCutSize )
            continue;
        p->CutCount[1]++; 
        if ( !Gia_CutMergeOrder(pCut0, pCut1, pCutsR[nCutsR], nCutSize) )
            continue;
        if ( Gia_CutSetLastCutIsContained(pCutsR, nCutsR) )
            continue;
        p->CutCount[2]++;
        if ( p->fCutMin && Gia_CutComputeTruth(p, pCut0, pCut1, fComp0, fComp1, pCutsR[nCutsR], fIsXor) )
            pCutsR[nCutsR]->Sign = Gia_CutGetSign(pCutsR[nCutsR]);
        pCutsR[nCutsR]->nTreeLeaves = Gia_CutTreeLeaves( p, pCutsR[nCutsR] );
        pCutsR[nCutsR]->CostF = Gia_CutGetCost( p, pCutsR[nCutsR] );        
        nCutsR = Gia_CutSetAddCut( pCutsR, nCutsR, nCutNum );
    }
    p->CutCount[3] += nCutsR;
    p->nCutsOver += nCutsR == nCutNum-1;
    p->nCutsR = nCutsR;
    p->Pivot = iObj;
    // debug printout
    if ( 0 )
    {
        printf( "*** Obj = %4d  NumCuts = %4d\n", iObj, nCutsR );
        for ( i = 0; i < nCutsR; i++ )
            Gia_CutPrint( p, iObj, pCutsR[i] );
        printf( "\n" );
    }
    // verify
    assert( nCutsR > 0 && nCutsR < nCutNum );
    assert( Gia_CutSetCheckArray(pCutsR, nCutsR) );
    // store the cutset
    Gia_StoStoreResult( p, iObj, pCutsR, nCutsR );
    if ( nCutsR > 1 || pCutsR[0]->nLeaves > 1 )
        Gia_CutAddUnit( p, iObj );
}


/**Function*************************************************************

  Synopsis    [Incremental cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Sto_t * Gia_StoAlloc( Gia_Man_t * pGia, int nCutSize, int nCutNum, int fCutMin, int fTruthMin, int fVerbose )
{
    Gia_Sto_t * p;
    assert( nCutSize < GIA_CUT_NO_LEAF );
    assert( nCutSize > 1 && nCutSize <= GIA_MAX_CUTSIZE );
    assert( nCutNum > 1 && nCutNum < GIA_MAX_CUTNUM );
    p = ABC_CALLOC( Gia_Sto_t, 1 );
    p->clkStart  = Abc_Clock();
    p->nCutSize  = nCutSize;
    p->nCutNum   = nCutNum;
    p->fCutMin   = fCutMin;
    p->fTruthMin = fTruthMin;
    p->fVerbose  = fVerbose;
    p->pGia      = pGia;
    p->vRefs     = Vec_IntAlloc( Gia_ManObjNum(pGia) );
    p->vCuts     = Vec_WecStart( Gia_ManObjNum(pGia) );
    p->vTtMem    = fCutMin ? Vec_MemAllocForTT( nCutSize, 0 ) : NULL;
    return p;
}
void Gia_StoFree( Gia_Sto_t * p )
{
    Vec_IntFree( p->vRefs );
    Vec_WecFree( p->vCuts );
    if ( p->fCutMin )
        Vec_MemHashFree( p->vTtMem );
    if ( p->fCutMin )
        Vec_MemFree( p->vTtMem );
    ABC_FREE( p );
}
void Gia_StoComputeCutsConst0( Gia_Sto_t * p, int iObj )
{
    Gia_CutAddZero( p, iObj );
}
void Gia_StoComputeCutsCi( Gia_Sto_t * p, int iObj )
{
    Gia_CutAddUnit( p, iObj );
}
void Gia_StoComputeCutsNode( Gia_Sto_t * p, int iObj )
{
    Gia_StoMergeCuts( p, iObj );
}
void Gia_StoRefObj( Gia_Sto_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    assert( iObj == Vec_IntSize(p->vRefs) );
    Vec_IntPush( p->vRefs, 0 );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Vec_IntAddToEntry( p->vRefs, Gia_ObjFaninId0(pObj, iObj), 1 );
        Vec_IntAddToEntry( p->vRefs, Gia_ObjFaninId1(pObj, iObj), 1 );
    }
    else if ( Gia_ObjIsCo(pObj) )
        Vec_IntAddToEntry( p->vRefs, Gia_ObjFaninId0(pObj, iObj), 1 );
}
void Gia_StoComputeCuts( Gia_Man_t * pGia )
{
    int nCutSize  =  8;
    int nCutNum   =  6;
    int fCutMin   =  0;
    int fTruthMin =  0;
    int fVerbose  =  1;
    Gia_Sto_t * p = Gia_StoAlloc( pGia, nCutSize, nCutNum, fCutMin, fTruthMin, fVerbose );
    Gia_Obj_t * pObj;  int i, iObj;
    assert( nCutSize <= GIA_MAX_CUTSIZE );
    assert( nCutNum  <  GIA_MAX_CUTNUM  );
    // prepare references
    Gia_ManForEachObj( p->pGia, pObj, iObj )
        Gia_StoRefObj( p, iObj );
    // compute cuts
    Gia_StoComputeCutsConst0( p, 0 );
    Gia_ManForEachCiId( p->pGia, iObj, i )
        Gia_StoComputeCutsCi( p, iObj );
    Gia_ManForEachAnd( p->pGia, pObj, iObj )
        Gia_StoComputeCutsNode( p, iObj );
    if ( p->fVerbose )
    {
        printf( "Running cut computation with CutSize = %d  CutNum = %d  CutMin = %s  TruthMin = %s\n", 
            p->nCutSize, p->nCutNum, p->fCutMin ? "yes":"no", p->fTruthMin ? "yes":"no" );
        printf( "CutPair = %.0f  ",         p->CutCount[0] );
        printf( "Merge = %.0f (%.2f %%)  ", p->CutCount[1], 100.0*p->CutCount[1]/p->CutCount[0] );
        printf( "Eval = %.0f (%.2f %%)  ",  p->CutCount[2], 100.0*p->CutCount[2]/p->CutCount[0] );
        printf( "Cut = %.0f (%.2f %%)  ",   p->CutCount[3], 100.0*p->CutCount[3]/p->CutCount[0] );
        printf( "Cut/Node = %.2f  ",        p->CutCount[3] / Gia_ManAndNum(p->pGia) );
        printf( "\n" );
        printf( "The number of nodes with cut count over the limit (%d cuts) = %d nodes (out of %d).  ", 
            p->nCutNum, p->nCutsOver, Gia_ManAndNum(pGia) );
        Abc_PrintTime( 0, "Time", Abc_Clock() - p->clkStart );
    }
    Gia_StoFree( p );
}


/**Function*************************************************************

  Synopsis    [Extract a given number of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_StoSelectOneCut( Vec_Wec_t * vCuts, int iObj, Vec_Int_t * vCut, int nCutSizeMin )
{
    Vec_Int_t * vThis = Vec_WecEntry( vCuts, iObj );
    int i, v, * pCut, * pList = Vec_IntArray( vThis );
    if ( pList == NULL )
        return 0;
    Vec_IntClear( vCut );
    Sdb_ForEachCut( pList, pCut, i )
    {
        if ( pCut[0] < nCutSizeMin )
            continue;
        for ( v = 0; v <= pCut[0]; v++ )
            Vec_IntPush( vCut, pCut[v] );
        return 1;
    }
    return 0;
}
Vec_Wec_t * Gia_ManSelectCuts( Vec_Wec_t * vCuts, int nCuts, int nCutSizeMin )
{
    Vec_Wec_t * vCutsSel = Vec_WecStart( nCuts );
    int i; srand( time(NULL) );
    for ( i = 0; i < nCuts; i++ )
        while ( !Gia_StoSelectOneCut(vCuts, (rand() | (rand() << 15)) % Vec_WecSize(vCuts), Vec_WecEntry(vCutsSel, i), nCutSizeMin) );
    return vCutsSel;
}
Vec_Wec_t * Gia_ManExtractCuts( Gia_Man_t * pGia, int nCutSize0, int nCuts0, int fVerbose0 )
{
    int nCutSize  =  nCutSize0;
    int nCutNum   =  6;
    int fCutMin   =  0;
    int fTruthMin =  0;
    int fVerbose  =  fVerbose0;
    Vec_Wec_t * vCutsSel;
    Gia_Sto_t * p = Gia_StoAlloc( pGia, nCutSize, nCutNum, fCutMin, fTruthMin, fVerbose );
    Gia_Obj_t * pObj;  int i, iObj;
    assert( nCutSize <= GIA_MAX_CUTSIZE );
    assert( nCutNum  <  GIA_MAX_CUTNUM  );
    // prepare references
    Gia_ManForEachObj( p->pGia, pObj, iObj )
        Gia_StoRefObj( p, iObj );
    // compute cuts
    Gia_StoComputeCutsConst0( p, 0 );
    Gia_ManForEachCiId( p->pGia, iObj, i )
        Gia_StoComputeCutsCi( p, iObj );
    Gia_ManForEachAnd( p->pGia, pObj, iObj )
        Gia_StoComputeCutsNode( p, iObj );
    if ( p->fVerbose )
    {
        printf( "Running cut computation with CutSize = %d  CutNum = %d  CutMin = %s  TruthMin = %s\n", 
            p->nCutSize, p->nCutNum, p->fCutMin ? "yes":"no", p->fTruthMin ? "yes":"no" );
        printf( "CutPair = %.0f  ",         p->CutCount[0] );
        printf( "Merge = %.0f (%.2f %%)  ", p->CutCount[1], 100.0*p->CutCount[1]/p->CutCount[0] );
        printf( "Eval = %.0f (%.2f %%)  ",  p->CutCount[2], 100.0*p->CutCount[2]/p->CutCount[0] );
        printf( "Cut = %.0f (%.2f %%)  ",   p->CutCount[3], 100.0*p->CutCount[3]/p->CutCount[0] );
        printf( "Cut/Node = %.2f  ",        p->CutCount[3] / Gia_ManAndNum(p->pGia) );
        printf( "\n" );
        printf( "The number of nodes with cut count over the limit (%d cuts) = %d nodes (out of %d).  ", 
            p->nCutNum, p->nCutsOver, Gia_ManAndNum(pGia) );
        Abc_PrintTime( 0, "Time", Abc_Clock() - p->clkStart );
    }
    vCutsSel = Gia_ManSelectCuts( p->vCuts, nCuts0, nCutSize0-1 );
    Gia_StoFree( p );
    return vCutsSel;
}
void Gia_ManCreateWins( Gia_Man_t * pGia, Vec_Wec_t * vCuts )
{
    Gia_Obj_t * pObj; 
    Vec_Wec_t * vWins = Vec_WecStart( Gia_ManObjNum(pGia) );
    Vec_Int_t * vTemp = Vec_IntAlloc( 100 );
    Vec_Int_t * vCut; int i, k, Obj, Cut;
    Vec_WecForEachLevel( vCuts, vCut, i )
        Vec_IntForEachEntryStart( vCut, Obj, k, 1 )
            Vec_IntPush( Vec_WecEntry(vWins, Obj), i );
    Gia_ManForEachAnd( pGia, pObj, Obj )
    {
        Vec_Int_t * vWin  = Vec_WecEntry(vWins, Obj);
        Vec_Int_t * vWin0 = Vec_WecEntry(vWins, Gia_ObjFaninId0(pObj, Obj));
        Vec_Int_t * vWin1 = Vec_WecEntry(vWins, Gia_ObjFaninId1(pObj, Obj));
        Vec_IntTwoFindCommon( vWin0, vWin1, vTemp );
        Vec_IntForEachEntry( vTemp, Cut, k )
        {
            Vec_IntPushUniqueOrder( vWin, Cut );
            Vec_IntPush( Vec_WecEntry(vCuts, Cut), Obj );
        }
    }
    Vec_WecFree( vWins );
    Vec_IntFree( vTemp );
}
void Gia_ManPrintWins( Vec_Wec_t * vCuts )
{
    Vec_Int_t * vCut; int i, k, Obj;
    Vec_WecForEachLevel( vCuts, vCut, i )
    {
        int nInputs = Vec_IntEntry(vCut, 0);
        printf( "Cut %5d : ", i );
        printf( "Supp = %d  ", nInputs );
        printf( "Nodes = %d  ", Vec_IntSize(vCut) - 1 - nInputs );
        Vec_IntForEachEntryStartStop( vCut, Obj, k, 1, nInputs+1 )
            printf( "%d ", Obj );
        printf( "  " );
        Vec_IntForEachEntryStart( vCut, Obj, k, nInputs+1 )
            printf( "%d ", Obj );
        printf( "\n" );
    }
}
void Gia_ManPrintWinStats( Vec_Wec_t * vCuts )
{
    Vec_Int_t * vCut; int i, nInputs = 0, nNodes = 0;
    Vec_WecForEachLevel( vCuts, vCut, i )
    {
        nInputs += Vec_IntEntry(vCut, 0);
        nNodes += Vec_IntSize(vCut) - 1 - Vec_IntEntry(vCut, 0);
    }
    printf( "Computed %d windows with average support %.3f and average volume %.3f.\n", 
        Vec_WecSize(vCuts), 1.0*nInputs/Vec_WecSize(vCuts), 1.0*nNodes/Vec_WecSize(vCuts) );
}
void Gia_ManExtractTest( Gia_Man_t * pGia )
{
    extern Vec_Wec_t * Gia_ManExtractCuts2( Gia_Man_t * p, int nCutSize, int nCuts, int fVerbose );
    Vec_Wec_t * vCutsSel = Gia_ManExtractCuts2( pGia, 8, 10000, 1 );
    //Vec_Wec_t * vCutsSel = Gia_ManExtractCuts( pGia, 8, 10000, 1 );
    abctime clk = Abc_Clock();
    Gia_ManCreateWins( pGia, vCutsSel );
    //Gia_ManPrintWins( vCutsSel );
    Gia_ManPrintWinStats( vCutsSel );
    Vec_WecFree( vCutsSel );
    Abc_PrintTime( 0, "Creating windows", Abc_Clock() - clk );
}

/**Function*************************************************************

  Synopsis    [Extract a given number of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_StoCutPrint( int * pCut )
{
    int v; 
    printf( "{" );
    for ( v = 1; v <= pCut[0]; v++ )
        printf( " %d", pCut[v] );
    printf( " }\n" );
}
void Gia_StoPrintCuts( Vec_Int_t * vThis, int iObj, int nCutSize )
{
    int i, * pCut;
    printf( "Cuts of node %d (size = %d):\n", iObj, nCutSize );
    Sdb_ForEachCut( Vec_IntArray(vThis), pCut, i )
        if ( !nCutSize || pCut[0] == nCutSize )
            Gia_StoCutPrint( pCut );
}
Vec_Wec_t * Gia_ManFilterCuts( Gia_Man_t * pGia, Vec_Wec_t * vStore, int nCutSize, int nCuts )
{
    abctime clkStart = Abc_Clock();
    Vec_Wec_t * vCutsSel = Vec_WecAlloc( nCuts ); 
    Vec_Int_t * vLevel, * vCut = Vec_IntAlloc( 10 );
    Vec_Wec_t * vCuts = Vec_WecAlloc( 1000 ); 
    Hsh_VecMan_t * p = Hsh_VecManStart( 1000 ); int i, s;
    Vec_WecForEachLevel( vStore, vLevel, i ) if ( Vec_IntSize(vLevel) )
    {
        int v, k, * pCut, Value;
        Sdb_ForEachCut( Vec_IntArray(vLevel), pCut, k )
        {
            if ( pCut[0] < 2 )
                continue;

            for ( v = 1; v <= pCut[0]; v++ )
                if ( pCut[v] < 9 )
                    break;
            if ( v <= pCut[0] )
                continue;

            Vec_IntClear( vCut );
            Vec_IntPushArray( vCut, pCut+1, pCut[0] );
            Value = Hsh_VecManAdd( p, vCut );
            if ( Value == Vec_WecSize(vCuts) )
            {
                Vec_Int_t * vTemp = Vec_WecPushLevel(vCuts);
                Vec_IntPush( vTemp, 0 );
                Vec_IntAppend( vTemp, vCut );
            }
            Vec_IntAddToEntry( Vec_WecEntry(vCuts, Value), 0, 1 );
        }
    }
    printf( "Collected cuts = %d.\n", Vec_WecSize(vCuts) );
    for ( s = 3; s <= nCutSize; s++ )
        Vec_WecForEachLevel( vCuts, vLevel, i )
            if ( Vec_IntSize(vLevel) - 1 == s )
            {
                int * pCut = Vec_IntEntryP(vLevel, 1);
                int u, v, Value;
                for ( u = 0; u < s; u++ )
                {
                    Vec_IntClear( vCut );
                    for ( v = 0; v < s; v++ ) if ( v != u )
                        Vec_IntPush( vCut, pCut[v] );
                    assert( Vec_IntSize(vCut) == s-1 );
                    Value = Hsh_VecManAdd( p, vCut );
                    if ( Value < Vec_WecSize(vCuts) )
                        Vec_IntAddToEntry( vLevel, 0, Vec_IntEntry(Vec_WecEntry(vCuts, Value), 0) );
                }
            }
    Hsh_VecManStop( p );
    Vec_IntFree( vCut );
    // collect 
    Vec_WecSortByFirstInt( vCuts, 1 );
    Vec_WecForEachLevelStop( vCuts, vLevel, i, Abc_MinInt(Vec_WecSize(vCuts), nCuts) )
        Vec_IntAppend( Vec_WecPushLevel(vCutsSel), vLevel );
    Abc_PrintTime( 0, "Cut filtering time", Abc_Clock() - clkStart );
    return vCutsSel;
}
int Gia_ManCountRefs( Gia_Man_t * pGia, Vec_Int_t * vLevel )
{
    int i, iObj, nRefs = 0;
    Vec_IntForEachEntry( vLevel, iObj, i )
        nRefs += Gia_ObjRefNumId(pGia, iObj);
    return nRefs;
}
Vec_Wrd_t * Gia_ManGenSims( Gia_Man_t * pGia ) 
{
    Vec_Wrd_t * vSims;
    Vec_WrdFreeP( &pGia->vSimsPi );
    pGia->vSimsPi = Vec_WrdStartTruthTables( Gia_ManCiNum(pGia) );
    vSims  = Gia_ManSimPatSim( pGia );
    return vSims;
}
int Gia_ManFindSatDcs( Gia_Man_t * pGia, Vec_Wrd_t * vSims, Vec_Int_t * vLevel ) 
{
    int nWords = Vec_WrdSize(pGia->vSimsPi) / Gia_ManCiNum(pGia);
    int i, w, iObj, Res = 0, Pres[256] = {0}, nMints = 1 << Vec_IntSize(vLevel);
    for ( w = 0; w < 64*nWords; w++ )
    {
        int iInMint = 0;
        Vec_IntForEachEntry( vLevel, iObj, i )
            if ( Abc_TtGetBit( Vec_WrdEntryP(vSims, iObj*nWords), w ) )
                iInMint |= 1 << i;
        Pres[iInMint]++;
    }
    for ( i = 0; i < nMints; i++ )
        Res += Pres[i] == 0;
    return Res;
}


int Gia_ManCollectCutDivs( Gia_Man_t * p, Vec_Int_t * vIns )
{
    Gia_Obj_t * pObj; int i, Res = 0; 
    Vec_Int_t * vRes = Vec_IntAlloc( 100 ); 
    Vec_IntSort( vIns, 0 );

    Vec_IntPush( vRes, 0 );
    Vec_IntAppend( vRes, vIns );

    Gia_ManIncrementTravId( p );
    Gia_ManIncrementTravId( p );
    Gia_ManForEachObjVec( vIns, p, pObj, i )
        Gia_ObjSetTravIdCurrent( p, pObj );

    Gia_ManForEachAnd( p, pObj, i )
        if ( Gia_ObjIsTravIdCurrent(p, pObj) )
            continue;
        else if ( Gia_ObjIsTravIdCurrent(p, Gia_ObjFanin0(pObj)) && Gia_ObjIsTravIdCurrent(p, Gia_ObjFanin1(pObj)) )
        {
            if ( !Gia_ObjIsTravIdPrevious(p, pObj) )
                Vec_IntPush( vRes, i );
            Gia_ObjSetTravIdCurrent( p, pObj );
        }
//    printf( "Divisors: " );
//    Vec_IntPrint( vRes );
    Res = Vec_IntSize(vRes);
    Vec_IntFree( vRes );
    return Res;
}

void Gia_ManConsiderCuts( Gia_Man_t * pGia, Vec_Wec_t * vCuts )
{
    Vec_Wrd_t * vSims = Gia_ManGenSims( pGia ); 
    Vec_Int_t * vLevel; int i;
    Gia_ManCreateRefs( pGia );
    Vec_WecForEachLevel( vCuts, vLevel, i )
    {
        printf( "Cut %3d  ", i );
        printf( "Ref = %3d : ", Vec_IntEntry(vLevel, 0) );

        Vec_IntShift( vLevel, 1 );
        printf( "Ref = %3d : ", Gia_ManCountRefs(pGia, vLevel) );
        printf( "SDC = %3d : ", Gia_ManFindSatDcs(pGia, vSims, vLevel) );
        printf( "Div = %3d : ", Gia_ManCollectCutDivs(pGia, vLevel) );
        Vec_IntPrint( vLevel );
        Vec_IntShift( vLevel, -1 );
    }
    Vec_WrdFree( vSims );
}


Vec_Wec_t * Gia_ManExploreCuts( Gia_Man_t * pGia, int nCutSize0, int nCuts0, int fVerbose0 )
{
    int nCutSize  =  nCutSize0;
    int nCutNum   =  64;
    int fCutMin   =  0;
    int fTruthMin =  0;
    int fVerbose  =  fVerbose0;
    Vec_Wec_t * vCutsSel;
    Gia_Sto_t * p = Gia_StoAlloc( pGia, nCutSize, nCutNum, fCutMin, fTruthMin, fVerbose );
    Gia_Obj_t * pObj;  int i, iObj;
    assert( nCutSize <= GIA_MAX_CUTSIZE );
    assert( nCutNum  <  GIA_MAX_CUTNUM  );
    // prepare references
    Gia_ManForEachObj( p->pGia, pObj, iObj )
        Gia_StoRefObj( p, iObj );
    // compute cuts
    Gia_StoComputeCutsConst0( p, 0 );
    Gia_ManForEachCiId( p->pGia, iObj, i )
        Gia_StoComputeCutsCi( p, iObj );
    Gia_ManForEachAnd( p->pGia, pObj, iObj )
        Gia_StoComputeCutsNode( p, iObj );
    if ( p->fVerbose )
    {
        printf( "Running cut computation with CutSize = %d  CutNum = %d  CutMin = %s  TruthMin = %s\n", 
            p->nCutSize, p->nCutNum, p->fCutMin ? "yes":"no", p->fTruthMin ? "yes":"no" );
        printf( "CutPair = %.0f  ",         p->CutCount[0] );
        printf( "Merge = %.0f (%.2f %%)  ", p->CutCount[1], 100.0*p->CutCount[1]/p->CutCount[0] );
        printf( "Eval = %.0f (%.2f %%)  ",  p->CutCount[2], 100.0*p->CutCount[2]/p->CutCount[0] );
        printf( "Cut = %.0f (%.2f %%)  ",   p->CutCount[3], 100.0*p->CutCount[3]/p->CutCount[0] );
        printf( "Cut/Node = %.2f  ",        p->CutCount[3] / Gia_ManAndNum(p->pGia) );
        printf( "\n" );
        printf( "The number of nodes with cut count over the limit (%d cuts) = %d nodes (out of %d).  ", 
            p->nCutNum, p->nCutsOver, Gia_ManAndNum(pGia) );
        Abc_PrintTime( 0, "Time", Abc_Clock() - p->clkStart );
    }
    vCutsSel = Gia_ManFilterCuts( pGia, p->vCuts, nCutSize0, nCuts0 );
    //Gia_ManConsiderCuts( pGia, vCutsSel );
    Gia_StoFree( p );
    return vCutsSel;
}
void Gia_ManExploreCutsTest( Gia_Man_t * pGia, int nCutSize0, int nCuts0, int fVerbose0 )
{
    Vec_Wec_t * vCutSel = Gia_ManExploreCuts( pGia, nCutSize0, nCuts0, fVerbose0 );
    Vec_WecPrint( vCutSel, 0 );
    Vec_WecFree( vCutSel );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Sto_t * Gia_ManMatchCutsInt( Gia_Man_t * pGia, int nCutSize0, int nCutNum0, int fVerbose0 )
{
    int nCutSize  =  nCutSize0;
    int nCutNum   =  nCutNum0;
    int fCutMin   =  1;
    int fTruthMin =  1;
    int fVerbose  =  fVerbose0;
    Gia_Sto_t * p = Gia_StoAlloc( pGia, nCutSize, nCutNum, fCutMin, fTruthMin, fVerbose );
    Gia_Obj_t * pObj;  int i, iObj;
    assert( nCutSize <= GIA_MAX_CUTSIZE );
    assert( nCutNum  <  GIA_MAX_CUTNUM  );
    // prepare references
    Gia_ManForEachObj( p->pGia, pObj, iObj )
        Gia_StoRefObj( p, iObj );
    // compute cuts
    Gia_StoComputeCutsConst0( p, 0 );
    Gia_ManForEachCiId( p->pGia, iObj, i )
        Gia_StoComputeCutsCi( p, iObj );
    Gia_ManForEachAnd( p->pGia, pObj, iObj )
        Gia_StoComputeCutsNode( p, iObj );
    if ( p->fVerbose )
    {
        printf( "Running cut computation with CutSize = %d  CutNum = %d  CutMin = %s  TruthMin = %s\n", 
            p->nCutSize, p->nCutNum, p->fCutMin ? "yes":"no", p->fTruthMin ? "yes":"no" );
        printf( "CutPair = %.0f  ",         p->CutCount[0] );
        printf( "Merge = %.0f (%.2f %%)  ", p->CutCount[1], 100.0*p->CutCount[1]/p->CutCount[0] );
        printf( "Eval = %.0f (%.2f %%)  ",  p->CutCount[2], 100.0*p->CutCount[2]/p->CutCount[0] );
        printf( "Cut = %.0f (%.2f %%)  ",   p->CutCount[3], 100.0*p->CutCount[3]/p->CutCount[0] );
        printf( "Cut/Node = %.2f  ",        p->CutCount[3] / Gia_ManAndNum(p->pGia) );
        printf( "\n" );
        printf( "The number of nodes with cut count over the limit (%d cuts) = %d nodes (out of %d).  ", 
            p->nCutNum, p->nCutsOver, Gia_ManAndNum(pGia) );
        Abc_PrintTime( 0, "Time", Abc_Clock() - p->clkStart );
    }
    return p;
}
void Gia_ManMatchCuts( Vec_Mem_t * vTtMem, Gia_Man_t * pGia, int nCutSize, int nCutNum, int fVerbose )
{
    Gia_Sto_t * p = Gia_ManMatchCutsInt( pGia, nCutSize, nCutNum, fVerbose );
    Vec_Int_t * vLevel; int i, j, k, * pCut;
    Vec_Int_t * vNodes = Vec_IntAlloc( 100 );
    Vec_Wec_t * vCuts = Vec_WecAlloc( 100 );
    abctime clkStart  = Abc_Clock();
    assert( Abc_Truth6WordNum(nCutSize) == Vec_MemEntrySize(vTtMem) );
    Vec_WecForEachLevel( p->vCuts, vLevel, i ) if ( Vec_IntSize(vLevel) )
    {
        Sdb_ForEachCut( Vec_IntArray(vLevel), pCut, k ) if ( pCut[0] > 1 )
        {
            word * pTruth = Vec_MemReadEntry( p->vTtMem, Abc_Lit2Var(pCut[pCut[0]+1]) );
            int * pSpot = Vec_MemHashLookup( vTtMem, pTruth );
            if ( *pSpot == -1 )
                continue;
            Vec_IntPush( vNodes, i );
            vLevel = Vec_WecPushLevel( vCuts );
            Vec_IntPush( vLevel, i );
            for ( j = 1; j <= pCut[0]; j++ )
                Vec_IntPush( vLevel, pCut[j] );
            break;
        }
    }
    printf( "Nodes with matching cuts: " );
    Vec_IntPrint( vNodes );
    if ( Vec_WecSize(vCuts) > 32 )
        Vec_WecShrink(vCuts, 32);
    Vec_WecPrint( vCuts, 0 );
    Vec_WecFree( vCuts );
    Vec_IntFree( vNodes );
    Gia_StoFree( p );
    if ( fVerbose )
        Abc_PrintTime( 1, "Cut matching time", Abc_Clock() - clkStart );    
}
Vec_Ptr_t * Gia_ManMatchCutsArray( Vec_Ptr_t * vTtMems, Gia_Man_t * pGia, int nCutSize, int nCutNum, int fVerbose )
{
    Vec_Ptr_t * vRes = Vec_PtrAlloc( Vec_PtrSize(vTtMems) );
    Gia_Sto_t * p = Gia_ManMatchCutsInt( pGia, nCutSize, nCutNum, fVerbose );
    Vec_Int_t * vLevel, * vTemp; int i, k, c, * pCut;
    abctime clkStart  = Abc_Clock();
    for ( i = 0; i < Vec_PtrSize(vTtMems); i++ )
        Vec_PtrPush( vRes, Vec_WecAlloc(100) );
    Vec_WecForEachLevel( p->vCuts, vLevel, i ) if ( Vec_IntSize(vLevel) )
    {
        Sdb_ForEachCut( Vec_IntArray(vLevel), pCut, k ) if ( pCut[0] > 1 )
        {
            Vec_Mem_t * vTtMem; int m;
            Vec_PtrForEachEntry( Vec_Mem_t *, vTtMems, vTtMem, m )
            {
                word * pTruth = Vec_MemReadEntry( p->vTtMem, Abc_Lit2Var(pCut[pCut[0]+1]) );
                int * pSpot = Vec_MemHashLookup( vTtMem, pTruth );
                if ( *pSpot == -1 )
                    continue;
                vTemp = Vec_WecPushLevel( (Vec_Wec_t *)Vec_PtrEntry(vRes, m) );
                Vec_IntPush( vTemp, i );
                for ( c = 1; c <= pCut[0]; c++ )
                    Vec_IntPush( vTemp, pCut[c] );
            }
        }
    }
    Gia_StoFree( p );
    if ( fVerbose ) {
        Vec_Wec_t * vCuts; 
        printf( "Detected nodes by type:  " );
        Vec_PtrForEachEntry( Vec_Wec_t *, vRes, vCuts, i )
            printf( "Type%d = %d  ", i, Vec_WecSize(vCuts) );
        Abc_PrintTime( 1, "Cut matching time", Abc_Clock() - clkStart );
    }
    return vRes;  
}
Vec_Ptr_t * Gia_ManMatchCutsMany( Vec_Mem_t * vTtMem, Vec_Int_t * vMap, int nFuncs, Gia_Man_t * pGia, int nCutSize, int nCutNum, int fVerbose )
{
    Gia_Sto_t * p = Gia_ManMatchCutsInt( pGia, nCutSize, nCutNum, fVerbose );
    Vec_Int_t * vLevel; int i, j, k, * pCut;
    abctime clkStart  = Abc_Clock();
    assert( Abc_Truth6WordNum(nCutSize) == Vec_MemEntrySize(vTtMem) );
    Vec_Ptr_t * vRes = Vec_PtrAlloc( nFuncs );
    for ( i = 0; i < nFuncs; i++ )
        Vec_PtrPush( vRes, Vec_WecAlloc(10) );
    Vec_WecForEachLevel( p->vCuts, vLevel, i ) if ( Vec_IntSize(vLevel) )
    {
        Sdb_ForEachCut( Vec_IntArray(vLevel), pCut, k ) if ( pCut[0] > 1 )
        {
            word * pTruth = Vec_MemReadEntry( p->vTtMem, Abc_Lit2Var(pCut[pCut[0]+1]) );
            assert( (pTruth[0] & 1) == 0 );
            int * pSpot = Vec_MemHashLookup( vTtMem, pTruth );
            if ( *pSpot == -1 )
                continue;
            int iFunc = vMap ? Vec_IntEntry( vMap, *pSpot ) : 0;
            assert( iFunc < nFuncs );
            Vec_Wec_t * vCuts = (Vec_Wec_t *)Vec_PtrEntry( vRes, iFunc );
            vLevel = Vec_WecPushLevel( vCuts );
            Vec_IntPush( vLevel, i );
            for ( j = 1; j <= pCut[0]; j++ )
                Vec_IntPush( vLevel, pCut[j] );
            break;
        }
    }
    Gia_StoFree( p );
    if ( fVerbose )
        Abc_PrintTime( 1, "Cut matching time", Abc_Clock() - clkStart );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Function enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDumpCuts( Gia_Man_t * p, int nCutSize, int nCutNum, int fVerbose )
{
    FILE * pFile = fopen( "input.txt", "wb" ); if ( !pFile ) return;
    Gia_Sto_t * pSto = Gia_ManMatchCutsInt( p, nCutSize, nCutNum, 0 );
    Vec_Int_t * vLevel; int i, k, c, * pCut, nCuts = 0, nNodes = 0;
    Vec_WecForEachLevel( pSto->vCuts, vLevel, i ) if ( Vec_IntSize(vLevel) ) {
        if ( !Gia_ObjIsAnd(Gia_ManObj(p, i)) )
            continue;
        Sdb_ForEachCut( Vec_IntArray(vLevel), pCut, k ) {
            if ( pCut[0] == 1 )
                continue;
            fprintf( pFile, "%d ", i );
            for ( c = 1; c <= pCut[0]; c++ )
                fprintf( pFile, "%d ", pCut[c] );
            fprintf( pFile, "1\n" );
            nCuts += pCut[0];
            nNodes++;
        }
    }
    Gia_Obj_t * pObj;
    Gia_ManForEachCo( p, pObj, i ) {
        fprintf( pFile, "%d %d 0\n", Gia_ObjId(p, pObj), Gia_ObjFaninId0p(p, pObj) );
    }
    fclose( pFile );
    Gia_StoFree( pSto );
    if ( fVerbose )
        printf( "Dumped %d cuts for %d nodes into file \"input.txt\".\n", nCuts, nNodes );
}

/**Function*************************************************************

  Synopsis    [Function enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Wrd_t * Gia_ManCollectCutFuncs( Gia_Man_t * p, int nCutSize, int nCutNum, int fVerbose )
{
    Gia_Sto_t * pSto = Gia_ManMatchCutsInt( p, nCutSize, nCutNum, 0 );
    Vec_Wrd_t * vFuncs = Vec_WrdAlloc( 1000 ); Vec_Int_t * vLevel; int i, k, * pCut; 
    Vec_WecForEachLevel( pSto->vCuts, vLevel, i ) if ( Vec_IntSize(vLevel) )
        Sdb_ForEachCut( Vec_IntArray(vLevel), pCut, k ) if ( pCut[0] == nCutSize ) {
            word * pTruth = Vec_MemReadEntry( pSto->vTtMem, Abc_Lit2Var(pCut[pCut[0]+1]) );
            Vec_WrdPush( vFuncs, pTruth[0] );
        }
    Gia_StoFree( pSto );
    if ( fVerbose )
        printf( "Collected %d cut functions using the AIG with %d nodes.\n", Vec_WrdSize(vFuncs), Gia_ManAndNum(p) );
    return vFuncs;
}
Vec_Int_t * Gia_ManCountNpnClasses( Vec_Mem_t * vTtMem, Vec_Int_t * vMap, int nClasses, Vec_Wrd_t * vOrig )
{
    assert( Vec_MemEntryNum(vTtMem) == Vec_IntSize(vMap) );
    Vec_Int_t * vClassCounts = Vec_IntStart( nClasses ); int i; word Func;
    Vec_WrdForEachEntry( vOrig, Func, i ) {
        int * pSpot = Vec_MemHashLookup( vTtMem, &Func );
        if ( *pSpot == -1 )
            continue;
        int iClass = Vec_IntEntry( vMap, *pSpot );
        if ( iClass == -1 )
            continue;
        assert( iClass < Vec_IntSize(vClassCounts) );
        Vec_IntAddToEntry( vClassCounts, iClass, 1 );
    }
    return vClassCounts;
}
Vec_Wrd_t * Gia_ManMatchFilterClasses( Vec_Mem_t * vTtMem, Vec_Int_t * vMap, Vec_Int_t * vClassCounts, int nNumFuncs, int fVerbose )
{
    int * pPerm = Abc_MergeSortCost( Vec_IntArray(vClassCounts), Vec_IntSize(vClassCounts) );
    Vec_Wrd_t * vBest = Vec_WrdAlloc( nNumFuncs );  int i, k, Entry;
    Vec_Int_t * vMapNew = Vec_IntStartFull( Vec_IntSize(vMap) );  
    for ( i = Vec_IntSize(vClassCounts)-1; i >= 0; i-- ) {
        word Best = ~(word)0;
        Vec_IntForEachEntry( vMap, Entry, k ) {
            if ( Entry != pPerm[i] )
                continue;
            if ( Best > Vec_MemReadEntry(vTtMem, k)[0] )
                 Best = Vec_MemReadEntry(vTtMem, k)[0];            
            Vec_IntWriteEntry( vMapNew, k, Vec_WrdSize(vBest) );
        }
        Vec_WrdPush( vBest, Best );
        assert( ~Best );
        if ( Vec_WrdSize(vBest) == nNumFuncs )
            break;
    }
    ABC_SWAP( Vec_Int_t, *vMap, *vMapNew );
    Vec_IntFree( vMapNew );
    ABC_FREE( pPerm );
    if ( fVerbose )
        printf( "Isolated %d (out of %d) most frequently occuring classes.\n", Vec_WrdSize(vBest), Vec_IntSize(vClassCounts) );
    return vBest;
}
void Gia_ManMatchProfileFunctions( Vec_Wrd_t * vBestReprs, Vec_Mem_t * vTtMem, Vec_Int_t * vMap, Vec_Wrd_t * vFuncs, int nCutSize )
{
    int BarSize = 60;
    extern void Dau_DsdPrintFromTruth( word * pTruth, int nVarsInit );
    Vec_Int_t * vCounts = Gia_ManCountNpnClasses( vTtMem, vMap, Vec_WrdSize(vBestReprs), vFuncs ); 
    word Repr; int c, i, MaxCount = Vec_IntFindMax( vCounts );
    Vec_WrdForEachEntry( vBestReprs, Repr, c )
    {
        int nSymb = BarSize*Vec_IntEntry(vCounts, c)/Abc_MaxInt(MaxCount, 1);
        printf( "Class%4d : ", c );
        printf( "Count =%6d   ", Vec_IntEntry(vCounts, c) );
        for ( i = 0; i < nSymb; i++ )
            printf( "*" );
        for ( i = nSymb; i < BarSize+3; i++ )
            printf( " " );        
        Dau_DsdPrintFromTruth( &Repr, nCutSize );
    }
    Vec_IntFree( vCounts );
}
void Gia_ManMatchCones( Gia_Man_t * pBig, Gia_Man_t * pSmall, int nCutSize, int nCutNum, int nNumFuncs, int nNumCones, int fVerbose )
{
    abctime clkStart  = Abc_Clock();
    extern void Dau_CanonicizeArray( Vec_Wrd_t * vFuncs, int nVars, int fVerbose );
    extern Vec_Mem_t * Dau_CollectNpnFunctionsArray( Vec_Wrd_t * vFuncs, int nVars, Vec_Int_t ** pvMap, int fVerbose );
    Vec_Wrd_t * vFuncs = Gia_ManCollectCutFuncs( pSmall, nCutSize, nCutNum, fVerbose );
    Vec_Wrd_t * vOrig = Vec_WrdDup( vFuncs );
    Dau_CanonicizeArray( vFuncs, nCutSize, fVerbose );  
    Vec_Int_t * vMap = NULL; int n;
    Vec_Mem_t * vTtMem = Dau_CollectNpnFunctionsArray( vFuncs, nCutSize, &vMap, fVerbose );
    Vec_WrdFree( vFuncs );
    Vec_Int_t * vClassCounts = Gia_ManCountNpnClasses( vTtMem, vMap, Vec_IntEntryLast(vMap)+1, vOrig );
    Vec_Wrd_t * vBestReprs = Gia_ManMatchFilterClasses( vTtMem, vMap, vClassCounts, nNumFuncs, fVerbose );
    assert( Vec_WrdSize(vBestReprs) == nNumFuncs );
    Vec_IntFree( vClassCounts );
    printf( "Frequency profile for %d most popular classes in the small AIG:\n", nNumFuncs );
    Gia_ManMatchProfileFunctions( vBestReprs, vTtMem, vMap, vOrig, nCutSize );
    Vec_WrdFree( vOrig );
    Abc_Random( 1 );
    for ( n = 0; n < nNumCones; n++ ) {
        int nRand = Abc_Random( 0 ) % Gia_ManCoNum(pBig);
        Gia_Man_t * pCone = Gia_ManDupCones( pBig, &nRand, 1, 1 );
        Vec_Wrd_t * vCutFuncs = Gia_ManCollectCutFuncs( pCone, nCutSize, nCutNum, 0 );
        printf( "ITER %d: Considering output cone %d with %d and-nodes. ", n+1, nRand, Gia_ManAndNum(pCone) );
        printf( "Profiling %d functions of %d-cuts:\n", Vec_WrdSize(vCutFuncs), nCutSize );
        Gia_ManMatchProfileFunctions( vBestReprs, vTtMem, vMap, vCutFuncs, nCutSize );
        Vec_WrdFree( vCutFuncs );
        Gia_ManStop( pCone );
    }
    Vec_WrdFree( vBestReprs );
    Vec_IntFree( vMap );
    Vec_MemHashFree( vTtMem );
    Vec_MemFree( vTtMem );
    Abc_PrintTime( 1, "Total computation time", Abc_Clock() - clkStart );
}

/**Function*************************************************************

  Synopsis    [Function enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManMatchConesMinimizeTts( Vec_Wrd_t * vSims, int nVarsMax )
{
    int nVars = 0;
    int nWordsMax = Abc_Truth6WordNum( nVarsMax ), nWords;
    int i, k = 0, nTruths = Vec_WrdSize(vSims) / nWordsMax;
    assert( nTruths * nWordsMax == Vec_WrdSize(vSims) );
    // support-minimize and find the largest supp size
    for ( i = 0; i < nTruths; i++ ) {
        word * pTruth = Vec_WrdEntryP( vSims, i * nWordsMax );
        int nVarsCur = Abc_TtMinBase( pTruth, NULL, nVarsMax, nVarsMax );
        nVars = Abc_MaxInt( nVars, nVarsCur );
    }
    // remap truth tables
    nWords = Abc_Truth6WordNum( nVars );
    for ( i = 0; i < nTruths; i++ ) {
        word * pTruth = Vec_WrdEntryP( vSims, i * nWordsMax );
        word * pTruth2 = Vec_WrdEntryP( vSims, k * nWords );
        if ( Abc_TtSupportSize(pTruth, nVars) < 3 )
            continue;
        memmove( pTruth2, pTruth, nWords * sizeof(word) );
        k++;
        if ( 0 ) {
            extern void Extra_PrintHexadecimal( FILE * pFile, unsigned Sign[], int nVars );
            printf( "Type%d : ", i );
            Extra_PrintHexadecimal( stdout, (unsigned *)pTruth2, nVars );
            printf( "\n" );
        }
    }
    Vec_WrdShrink ( vSims, k * nWords );
    return nVars;
}
void Gia_ManMatchConesOutputPrint( Vec_Ptr_t * p, int fVerbose )
{
    Vec_Wec_t * vCuts; int i;
    printf( "Nodes with matching cuts:\n" );
    Vec_PtrForEachEntry( Vec_Wec_t *, p, vCuts, i ) {
        if ( fVerbose ) {
            printf( "Type %d:\n", i );
            Vec_WecPrint( vCuts, 0 );
        }
        else 
            printf( "Type %d present in %d cuts\n", i, Vec_WecSize(vCuts) );
    }
}
void Gia_ManMatchConesOutputFree( Vec_Ptr_t * p )
{
    Vec_Wec_t * vCuts; int i;
    Vec_PtrForEachEntry( Vec_Wec_t *, p, vCuts, i )
        Vec_WecFree( vCuts );
    Vec_PtrFree( p );
}
void Gia_ManMatchConesOutput( Gia_Man_t * pBig, Gia_Man_t * pSmall, int nCutNum, int fVerbose )
{
    abctime clkStart  = Abc_Clock();
    extern Vec_Mem_t * Dau_CollectNpnFunctionsArray( Vec_Wrd_t * vFuncs, int nVars, Vec_Int_t ** pvMap, int fVerbose );
    Vec_Wrd_t * vSimsPi = Vec_WrdStartTruthTables( Gia_ManCiNum(pSmall) );
    Vec_Wrd_t * vSims   = Gia_ManSimPatSimOut( pSmall, vSimsPi, 1 );
    int nVars = Gia_ManMatchConesMinimizeTts( vSims, Gia_ManCiNum(pSmall) );
    Vec_WrdFree( vSimsPi );
    if ( nVars > 10 ) {
        printf( "Some output functions have support size more than 10.\n" );
        Vec_WrdFree( vSims );
        return;
    }
    Vec_Int_t * vMap = NULL;
    Vec_Mem_t * vTtMem = Dau_CollectNpnFunctionsArray( vSims, nVars, &vMap, fVerbose );
    int nFuncs = Vec_WrdSize(vSims) / Abc_Truth6WordNum(nVars);
    assert( Vec_WrdSize(vSims) == nFuncs * Abc_Truth6WordNum(nVars) );
    Vec_WrdFree( vSims );
    printf( "Using %d output functions with the support size between 3 and %d.\n", nFuncs, nVars );
    Vec_Ptr_t * vRes = Gia_ManMatchCutsMany( vTtMem, vMap, nFuncs, pBig, nVars, nCutNum, fVerbose );
    Vec_MemHashFree( vTtMem );
    Vec_MemFree( vTtMem );
    Vec_IntFree( vMap );
    Gia_ManMatchConesOutputPrint( vRes, fVerbose );
    Gia_ManMatchConesOutputFree( vRes );
    Abc_PrintTime( 1, "Total computation time", Abc_Clock() - clkStart );    
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

