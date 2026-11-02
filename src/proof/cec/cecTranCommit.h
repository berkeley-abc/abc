// Conflict selection and immutable-snapshot commit.
// Private implementation fragment included only by cecTrans.c.

// Exercise reuse across different roots/supports and Page boundaries, including
// generic callers whose covered/used sets change between Pages.  The legacy
// per-candidate scratch path is the oracle for gains, kill-sets and ordering.
// The conflict graph is stored by object incidence instead of materializing
// every edge.  An even incidence is a removable/MFFC membership and an odd
// incidence is replacement support.  Two vertices conflict on MFFC/MFFC or
// MFFC/support incidence; shared read-only support is intentionally legal.
typedef struct Cec_TranConflictGraph_t_ Cec_TranConflictGraph_t;
struct Cec_TranConflictGraph_t_
{
    Vec_Wec_t * vUsers;
    Vec_Int_t * vMffcBeg;
    Vec_Int_t * vMffcData;
    Vec_Int_t * vSuppBeg;
    Vec_Int_t * vSuppData;
    unsigned *  pSeen;
    unsigned    TravId;
    int         nVertices;
};

static void Cec_TranConflictGraphStart( Cec_TranConflictGraph_t * pGraph,
    int nObjs )
{
    memset( pGraph, 0, sizeof(Cec_TranConflictGraph_t) );
    pGraph->vUsers = Vec_WecStart( nObjs );
    pGraph->vMffcBeg = Vec_IntAlloc( 64 );
    pGraph->vMffcData = Vec_IntAlloc( 256 );
    pGraph->vSuppBeg = Vec_IntAlloc( 64 );
    pGraph->vSuppData = Vec_IntAlloc( 256 );
}

static void Cec_TranConflictGraphAdd( Cec_TranConflictGraph_t * pGraph,
    Vec_Int_t * vMffc, Vec_Int_t * vSupport )
{
    int iVertex = pGraph->nVertices++;
    int i, iObj;
    Vec_IntPush( pGraph->vMffcBeg, Vec_IntSize(pGraph->vMffcData) );
    Vec_IntForEachEntry( vMffc, iObj, i )
    {
        Vec_IntPush( pGraph->vMffcData, iObj );
        Vec_IntPush( Vec_WecEntry(pGraph->vUsers, iObj),
            Abc_Var2Lit(iVertex, 0) );
    }
    Vec_IntPush( pGraph->vSuppBeg, Vec_IntSize(pGraph->vSuppData) );
    Vec_IntForEachEntry( vSupport, iObj, i )
    {
        Vec_IntPush( pGraph->vSuppData, iObj );
        Vec_IntPush( Vec_WecEntry(pGraph->vUsers, iObj),
            Abc_Var2Lit(iVertex, 1) );
    }
}

static void Cec_TranConflictGraphFinalize( Cec_TranConflictGraph_t * pGraph )
{
    Vec_IntPush( pGraph->vMffcBeg, Vec_IntSize(pGraph->vMffcData) );
    Vec_IntPush( pGraph->vSuppBeg, Vec_IntSize(pGraph->vSuppData) );
    pGraph->pSeen = ABC_CALLOC( unsigned, pGraph->nVertices );
}

static void Cec_TranConflictGraphStop( Cec_TranConflictGraph_t * pGraph )
{
    Vec_WecFree( pGraph->vUsers );
    Vec_IntFree( pGraph->vMffcBeg );
    Vec_IntFree( pGraph->vMffcData );
    Vec_IntFree( pGraph->vSuppBeg );
    Vec_IntFree( pGraph->vSuppData );
    ABC_FREE( pGraph->pSeen );
    memset( pGraph, 0, sizeof(Cec_TranConflictGraph_t) );
}

static void Cec_TranConflictGraphCollectList(
    Cec_TranConflictGraph_t * pGraph, Vec_Int_t * vUsers,
    int iVertex, int fRequireMffc, Vec_Int_t * vNeighbors )
{
    int i, User, iOther;
    Vec_IntForEachEntry( vUsers, User, i )
    {
        if ( fRequireMffc && Abc_LitIsCompl(User) )
            continue;
        iOther = Abc_Lit2Var( User );
        if ( iOther == iVertex || pGraph->pSeen[iOther] == pGraph->TravId )
            continue;
        pGraph->pSeen[iOther] = pGraph->TravId;
        Vec_IntPush( vNeighbors, iOther );
    }
}

static void Cec_TranConflictGraphNeighbors(
    Cec_TranConflictGraph_t * pGraph, int iVertex,
    Vec_Int_t * vNeighbors )
{
    int i, iObj;
    Vec_IntClear( vNeighbors );
    if ( ++pGraph->TravId == 0 )
    {
        memset( pGraph->pSeen, 0,
            sizeof(unsigned) * pGraph->nVertices );
        pGraph->TravId = 1;
    }
    pGraph->pSeen[iVertex] = pGraph->TravId;
    for ( i = Vec_IntEntry(pGraph->vMffcBeg, iVertex);
          i < Vec_IntEntry(pGraph->vMffcBeg, iVertex + 1); i++ )
    {
        iObj = Vec_IntEntry( pGraph->vMffcData, i );
        Cec_TranConflictGraphCollectList( pGraph,
            Vec_WecEntry(pGraph->vUsers, iObj), iVertex, 0, vNeighbors );
    }
    for ( i = Vec_IntEntry(pGraph->vSuppBeg, iVertex);
          i < Vec_IntEntry(pGraph->vSuppBeg, iVertex + 1); i++ )
    {
        iObj = Vec_IntEntry( pGraph->vSuppData, i );
        Cec_TranConflictGraphCollectList( pGraph,
            Vec_WecEntry(pGraph->vUsers, iObj), iVertex, 1, vNeighbors );
    }
}

#include "cecTranSelectionDirty.h"

typedef struct Cec_TranWaveHeap_t_ Cec_TranWaveHeap_t;
struct Cec_TranWaveHeap_t_
{
    int * pHeap;
    int * pPos;
    long long * pLoss;
    int   nSize;
    Cec_TranCandVec_t const * pVertices;
};

static int Cec_TranWaveHeapBetter( Cec_TranWaveHeap_t const * pHeap,
    int iV0, int iV1 )
{
    Cec_TranCand_t const * pC0 = pHeap->pVertices->pArray + iV0;
    Cec_TranCand_t const * pC1 = pHeap->pVertices->pArray + iV1;
    // Compare Gain(c)^2 / (Gain(c) + Loss(c)) without division.  long double
    // avoids overflowing a 64-bit cross product on large proved pools while
    // the deterministic tie-breaks below keep equal priorities stable.
    long double Left = (long double)pC0->Gain * pC0->Gain *
        (pC1->Gain + pHeap->pLoss[iV1]);
    long double Right = (long double)pC1->Gain * pC1->Gain *
        (pC0->Gain + pHeap->pLoss[iV0]);
    if ( Left != Right )
        return Left > Right;
    if ( pC0->Gain != pC1->Gain )
        return pC0->Gain > pC1->Gain;
    if ( pC0->nMffc != pC1->nMffc )
        return pC0->nMffc > pC1->nMffc;
    if ( pC0->iTarget != pC1->iTarget )
        return pC0->iTarget > pC1->iTarget;
    return iV0 < iV1;
}

static void Cec_TranWaveHeapSwap( Cec_TranWaveHeap_t * pHeap,
    int i, int k )
{
    int Temp = pHeap->pHeap[i];
    pHeap->pHeap[i] = pHeap->pHeap[k];
    pHeap->pHeap[k] = Temp;
    pHeap->pPos[pHeap->pHeap[i]] = i;
    pHeap->pPos[pHeap->pHeap[k]] = k;
}

static void Cec_TranWaveHeapUp( Cec_TranWaveHeap_t * pHeap, int i )
{
    int Parent;
    while ( i > 0 )
    {
        Parent = (i - 1) >> 1;
        if ( !Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[i],
                pHeap->pHeap[Parent]) )
            break;
        Cec_TranWaveHeapSwap( pHeap, i, Parent );
        i = Parent;
    }
}

static void Cec_TranWaveHeapDown( Cec_TranWaveHeap_t * pHeap, int i )
{
    int Child;
    while ( (Child = 2 * i + 1) < pHeap->nSize )
    {
        if ( Child + 1 < pHeap->nSize &&
             Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[Child + 1],
                pHeap->pHeap[Child]) )
            Child++;
        if ( !Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[Child],
                pHeap->pHeap[i]) )
            break;
        Cec_TranWaveHeapSwap( pHeap, i, Child );
        i = Child;
    }
}

static void Cec_TranWaveHeapStart( Cec_TranWaveHeap_t * pHeap,
    Cec_TranCandVec_t const * pVertices, long long * pLoss )
{
    int i;
    memset( pHeap, 0, sizeof(Cec_TranWaveHeap_t) );
    pHeap->nSize = pVertices->nSize;
    pHeap->pHeap = ABC_ALLOC( int, pHeap->nSize );
    pHeap->pPos = ABC_ALLOC( int, pHeap->nSize );
    pHeap->pLoss = pLoss;
    pHeap->pVertices = pVertices;
    for ( i = 0; i < pHeap->nSize; i++ )
        pHeap->pHeap[i] = pHeap->pPos[i] = i;
    for ( i = pHeap->nSize / 2; i-- > 0; )
        Cec_TranWaveHeapDown( pHeap, i );
}

static void Cec_TranWaveHeapRemove( Cec_TranWaveHeap_t * pHeap,
    int iVertex )
{
    int i = pHeap->pPos[iVertex];
    if ( i < 0 )
        return;
    pHeap->pPos[iVertex] = -1;
    pHeap->nSize--;
    if ( i == pHeap->nSize )
        return;
    pHeap->pHeap[i] = pHeap->pHeap[pHeap->nSize];
    pHeap->pPos[pHeap->pHeap[i]] = i;
    if ( i > 0 && Cec_TranWaveHeapBetter(pHeap, pHeap->pHeap[i],
            pHeap->pHeap[(i - 1) >> 1]) )
        Cec_TranWaveHeapUp( pHeap, i );
    else
        Cec_TranWaveHeapDown( pHeap, i );
}

static int Cec_TranWaveHeapPop( Cec_TranWaveHeap_t * pHeap )
{
    int iVertex = pHeap->pHeap[0];
    Cec_TranWaveHeapRemove( pHeap, iVertex );
    return iVertex;
}

static void Cec_TranWaveHeapStop( Cec_TranWaveHeap_t * pHeap )
{
    ABC_FREE( pHeap->pHeap );
    ABC_FREE( pHeap->pPos );
    memset( pHeap, 0, sizeof(Cec_TranWaveHeap_t) );
}

// Compute the opportunity loss of one candidate in the current induced
// conflict graph.  Conflicting candidates are compressed by root: because at
// most one candidate of a root can be committed, that root contributes only
// the largest gain among its active conflicting candidates.
static long long Cec_TranConflictGraphRootLoss(
    Cec_TranConflictGraph_t * pGraph, Cec_TranCandVec_t const * pVertices,
    int iVertex, char const * pActive, Vec_Int_t * vNeighbors,
    int * pRootBest, unsigned * pRootSeen, unsigned * pRootTravId,
    int * pnActiveNeighbors )
{
    long long Loss = 0;
    int i, iOther, iRoot, Gain, nActive = 0;
    if ( ++*pRootTravId == 0 )
    {
        memset( pRootSeen, 0,
            sizeof(unsigned) * Vec_WecSize(pGraph->vUsers) );
        *pRootTravId = 1;
    }
    Cec_TranConflictGraphNeighbors( pGraph, iVertex, vNeighbors );
    Vec_IntForEachEntry( vNeighbors, iOther, i )
    {
        if ( !pActive[iOther] )
            continue;
        nActive++;
        iRoot = pVertices->pArray[iOther].iTarget;
        Gain = pVertices->pArray[iOther].Gain;
        assert( iRoot >= 0 && iRoot < Vec_WecSize(pGraph->vUsers) );
        assert( Gain > 0 );
        if ( pRootSeen[iRoot] != *pRootTravId )
        {
            pRootSeen[iRoot] = *pRootTravId;
            pRootBest[iRoot] = Gain;
            Loss += Gain;
        }
        else if ( pRootBest[iRoot] < Gain )
        {
            Loss += Gain - pRootBest[iRoot];
            pRootBest[iRoot] = Gain;
        }
    }
    if ( pnActiveNeighbors )
        *pnActiveNeighbors = nActive;
    return Loss;
}

#include "cecTranSelectionRootMax.h"

// Dynamic root-compressed weighted-loss GWMIN.  The priority is
//
//        Gain(c)^2 / (Gain(c) + Loss(c)),
//
// where Loss(c) sums the best conflicting gain once per distinct root in the
// current induced graph.  Removing a closed neighborhood can only decrease
// the loss of its remaining neighbors, so only those heap entries are
// recomputed and promoted.
static void Cec_TranSelectionDirtyTrace(Vec_Int_t * trace,
    Cec_TranWaveHeap_t const * heap, int selected, Vec_Int_t * removed,
    Vec_Int_t * dirty, char const * active, char const * chosen)
{
    int i;
    Vec_IntPush(trace,selected);
    Vec_IntPush(trace,Vec_IntSize(removed));
    for(i=0;i<Vec_IntSize(removed);++i) Vec_IntPush(trace,Vec_IntEntry(removed,i));
    Vec_IntPush(trace,Vec_IntSize(dirty));
    for(i=0;i<Vec_IntSize(dirty);++i) Vec_IntPush(trace,Vec_IntEntry(dirty,i));
    Vec_IntPush(trace,heap->nSize);
    for(i=0;i<heap->nSize;++i) Vec_IntPush(trace,heap->pHeap[i]);
    for(i=0;i<heap->pVertices->nSize;++i)
    {
        Vec_IntPush(trace,heap->pPos[i]);
        Vec_IntPush(trace,(int)(unsigned)(word)heap->pLoss[i]);
        Vec_IntPush(trace,(int)(unsigned)((word)heap->pLoss[i]>>32));
        Vec_IntPush(trace,active[i]); Vec_IntPush(trace,chosen[i]);
    }
}

static long long Cec_TranConflictGraphGwminDirty(
    Cec_TranConflictGraph_t * pGraph, Cec_TranCandVec_t const * pVertices,
    char * pChosen, long long * pnEdges, int * pFirstGain,
    Cec_TranSelectionDirty_t * pDirtyWork, Vec_Int_t * vTestTrace )
{
    Cec_TranWaveHeap_t Heap;
    Vec_Int_t * vNeighbors = Vec_IntAlloc( 64 );
    Vec_Int_t * vRemoved = Vec_IntAlloc( 64 );
    Vec_Int_t * vDirty = Vec_IntAlloc( 64 );
    long long * pLoss = ABC_ALLOC( long long, pVertices->nSize );
    char * pActive = ABC_ALLOC( char, pVertices->nSize );
    char * pDirty = ABC_CALLOC( char, pVertices->nSize );
    int * pRootBest = ABC_ALLOC( int, Vec_WecSize(pGraph->vUsers) );
    unsigned * pRootSeen = ABC_CALLOC( unsigned,
        Vec_WecSize(pGraph->vUsers) );
    unsigned RootTravId = 0;
    long long SumDegree = 0, Weight = 0;
    int i, k, iVertex, iOther, iSelected, nActiveNeighbors;
    int fTime = pDirtyWork && pDirtyWork->Profile;
    abctime clk = 0, maxClk = 0;
    Cec_TranSelectionRootMax_t * pMax = pDirtyWork ? pDirtyWork->RootMax : NULL;
    int fMaxTime = pMax && pMax->Profile;
    memset( pChosen, 0, pVertices->nSize );
    memset( pActive, 1, pVertices->nSize );
    *pFirstGain = 0;
    if ( pMax ) Cec_TranRootMaxStart(pMax,pGraph,pVertices);
    if ( fTime ) clk = Abc_Clock();
    if ( fMaxTime ) maxClk = Abc_Clock();
    for ( i = 0; i < pVertices->nSize; i++ )
    {
        pLoss[i] = Cec_TranConflictGraphRootLoss( pGraph, pVertices, i,
            pActive, vNeighbors, pRootBest, pRootSeen, &RootTravId,
            &nActiveNeighbors );
        SumDegree += nActiveNeighbors;
        if ( pMax )
        {
            ++pMax->InitialCalls;
            Cec_TranRootMaxCapture(pMax,i,vNeighbors);
        }
    }
    *pnEdges = SumDegree / 2;
    if ( pMax ) Cec_TranRootMaxFinish(pMax,pLoss,pActive);
    if ( fMaxTime ) pMax->InitialTicks += Abc_Clock() - maxClk;
    if ( fTime ) pDirtyWork->InitialTicks += Abc_Clock() - clk;
    Cec_TranWaveHeapStart( &Heap, pVertices, pLoss );
    while ( Heap.nSize )
    {
        if ( fTime ) clk = Abc_Clock();
        iVertex = Cec_TranWaveHeapPop( &Heap );
        iSelected = iVertex;
        if ( fTime ) pDirtyWork->PopHash = Cec_TranSelectionDirtyHash(
            pDirtyWork->PopHash, iSelected );
        assert( pActive[iVertex] );
        if ( Weight == 0 )
            *pFirstGain = pVertices->pArray[iVertex].Gain;
        pActive[iVertex] = 0;
        pChosen[iVertex] = 1;
        Weight += pVertices->pArray[iVertex].Gain;
        Vec_IntClear( vRemoved );
        Vec_IntPush( vRemoved, iVertex );
        Cec_TranConflictGraphNeighbors( pGraph, iVertex, vNeighbors );
        Vec_IntForEachEntry( vNeighbors, iOther, i )
            if ( pActive[iOther] )
            {
                pActive[iOther] = 0;
                Cec_TranWaveHeapRemove( &Heap, iOther );
                Vec_IntPush( vRemoved, iOther );
            }
        if ( fTime ) pDirtyWork->RemoveTicks += Abc_Clock() - clk;
        if ( fTime ) clk = Abc_Clock();
        if ( pDirtyWork )
        {
            Cec_TranSelectionDirtyEpoch(pDirtyWork);
            pDirtyWork->Removed += (word)Vec_IntSize(vRemoved);
        }
        Vec_IntClear( vDirty );
        Vec_IntForEachEntry( vRemoved, iOther, i )
        {
            if ( pDirtyWork )
                Cec_TranSelectionDirtyNeighbors(pDirtyWork,pGraph,iOther,vNeighbors);
            else
                Cec_TranConflictGraphNeighbors( pGraph, iOther, vNeighbors );
            Vec_IntForEachEntry( vNeighbors, iVertex, k )
                if ( pActive[iVertex] && !pDirty[iVertex] )
                {
                    pDirty[iVertex] = 1;
                    Vec_IntPush( vDirty, iVertex );
                }
        }
        if ( pDirtyWork ) pDirtyWork->DirtyVertices += (word)Vec_IntSize(vDirty);
        if ( fTime ) pDirtyWork->DirtyTicks += Abc_Clock() - clk;
        if ( pDirtyWork && pDirtyWork->Applied && pDirtyWork->Mode == 2 )
            Cec_TranSelectionDirtyCheck(pDirtyWork,vRemoved,pActive,vDirty);
        if ( fTime ) clk = Abc_Clock();
        if ( fMaxTime ) maxClk = Abc_Clock();
        Vec_IntForEachEntry( vDirty, iVertex, i )
        {
            long long OldLoss = pLoss[iVertex];
            if ( pMax ) ++pMax->UpdateCalls;
            if ( pMax && pMax->Applied )
            {
                ++pMax->CacheUpdates;
                pLoss[iVertex]=Cec_TranRootMaxRead(pMax,iVertex,pActive,
                    pMax->Profile || pMax->Mode==2);
                if ( pMax->Mode==2 )
                    Cec_TranRootMaxOracle(pMax,iVertex,pActive,pLoss[iVertex],0);
            }
            else
            {
                if ( pMax ) ++pMax->OriginalUpdates;
                pLoss[iVertex] = Cec_TranConflictGraphRootLoss( pGraph,
                    pVertices, iVertex, pActive, vNeighbors, pRootBest,
                    pRootSeen, &RootTravId, NULL );
            }
            assert( pLoss[iVertex] <= OldLoss );
            pDirty[iVertex] = 0;
            Cec_TranWaveHeapUp( &Heap, Heap.pPos[iVertex] );
        }
        if ( fMaxTime ) pMax->UpdateTicks += Abc_Clock() - maxClk;
        if ( fTime ) pDirtyWork->UpdateTicks += Abc_Clock() - clk;
        if ( vTestTrace )
            Cec_TranSelectionDirtyTrace(vTestTrace,&Heap,iSelected,
                vRemoved,vDirty,pActive,pChosen);
    }
    Cec_TranWaveHeapStop( &Heap );
    if ( pMax ) Cec_TranRootMaxRelease(pMax);
    Vec_IntFree( vNeighbors );
    Vec_IntFree( vRemoved );
    Vec_IntFree( vDirty );
    ABC_FREE( pLoss );
    ABC_FREE( pActive );
    ABC_FREE( pDirty );
    ABC_FREE( pRootBest );
    ABC_FREE( pRootSeen );
    return Weight;
}

// Audit the frozen-cost independent set with the exact operation used by the
// real commit: one topological bundle duplication followed by cleanup.  The
// structural conflict graph normally makes the individual gains additive,
// but structural hashing can expose an alias which is not represented by an
// object-incidence edge.  Keep the safety property explicit instead of
// weakening the commit assertion.
static int Cec_TranSelectedExactGain( Gia_Man_t * p,
    Cec_TranCandVec_t const * pVertices, char const * pChosen )
{
    Gia_Man_t * pDup, * pClean;
    Vec_Int_t * vSelected = Vec_IntAlloc( 64 );
    int i, Gain;
    for ( i = 0; i < pVertices->nSize; i++ )
        if ( pChosen[i] )
            Vec_IntPush( vSelected, i );
    if ( Vec_IntSize(vSelected) == 0 )
    {
        Vec_IntFree( vSelected );
        return 0;
    }
    pDup = Cec_TranDupRootBundle( p, pVertices->pArray, vSelected );
    pClean = Cec_TranCleanupKeepRegs( pDup, NULL );
    Gain = Cec_TranGain( p, pClean );
    Gia_ManStop( pDup );
    Gia_ManStop( pClean );
    Vec_IntFree( vSelected );
    return Gain;
}

// A rare non-additive bundle is repaired by one global, deterministic rule:
// visit the chosen candidates by decreasing frozen gain (then MFFC, target,
// and stable vertex index), and retain exactly the candidates whose measured
// bundle marginal is positive.  Replacing the estimate by that exact marginal
// makes the accounting telescope to the final cleanup gain.  This is a
// structural safety fallback, not a circuit-specific quality policy.
static long long Cec_TranRepairSelectedExact( Gia_Man_t * p,
    Cec_TranCandVec_t * pVertices, char * pChosen,
    long long Predicted )
{
    char * pOriginal = ABC_ALLOC( char, pVertices->nSize );
    char * pDone = ABC_CALLOC( char, pVertices->nSize );
    int * pFrozenGain = ABC_ALLOC( int, pVertices->nSize );
    int i, k, iBest, nOriginal = 0, nKept = 0;
    int Exact, Audited, Current = 0;
    abctime clk = Abc_Clock();
    memcpy( pOriginal, pChosen, pVertices->nSize );
    for ( i = 0; i < pVertices->nSize; i++ )
        pFrozenGain[i] = pVertices->pArray[i].Gain,
        nOriginal += pOriginal[i] != 0;
    Exact = Cec_TranSelectedExactGain( p, pVertices, pChosen );
    Audited = Exact;
    if ( Exact > 0 && Exact >= Predicted )
    {
        ABC_FREE( pOriginal );
        ABC_FREE( pDone );
        ABC_FREE( pFrozenGain );
        return Predicted;
    }

    memset( pChosen, 0, pVertices->nSize );
    for ( k = 0; k < nOriginal; k++ )
    {
        int Trial;
        iBest = -1;
        for ( i = 0; i < pVertices->nSize; i++ )
            if ( pOriginal[i] && !pDone[i] &&
                 (iBest < 0 || pFrozenGain[i] > pFrozenGain[iBest] ||
                  (pFrozenGain[i] == pFrozenGain[iBest] &&
                   (pVertices->pArray[i].nMffc >
                        pVertices->pArray[iBest].nMffc ||
                    (pVertices->pArray[i].nMffc ==
                         pVertices->pArray[iBest].nMffc &&
                     (pVertices->pArray[i].iTarget >
                          pVertices->pArray[iBest].iTarget ||
                      (pVertices->pArray[i].iTarget ==
                           pVertices->pArray[iBest].iTarget && i < iBest)))))) )
                iBest = i;
        assert( iBest >= 0 );
        pDone[iBest] = 1;
        pChosen[iBest] = 1;
        Trial = Cec_TranSelectedExactGain( p, pVertices, pChosen );
        if ( Trial <= Current )
        {
            pChosen[iBest] = 0;
            continue;
        }
        pVertices->pArray[iBest].Gain = Trial - Current;
        Current = Trial;
        nKept++;
    }
    assert( nKept > 0 && Current > 0 );
    Exact = Cec_TranSelectedExactGain( p, pVertices, pChosen );
    assert( Exact == Current );
    Abc_Print( 1, "stran-root exact bundle repair: predicted=%lld exact=%d original=%d kept=%d repaired-gain=%d audit-sec=%.6f policy=positive-exact-marginal.\n",
        Predicted, Audited, nOriginal, nKept, Current,
        Cec_TranTimeSec(Abc_Clock() - clk) );
    ABC_FREE( pOriginal );
    ABC_FREE( pDone );
    ABC_FREE( pFrozenGain );
    return Current;
}

static int Cec_TranRootConsumeProvedDirty( Gia_Man_t * p,
    Cec_TranCandVec_t * pProved, char * pCovered, char * pUsed,
    char * pSolved, char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    Cec_TranCandVec_t * pSelected, Cec_TranProf_t * pProf,
    Cec_TranSelectionDirty_t * pDirtyWork )
{
    Cec_TranFrozenHash_t FrozenHash;
    Cec_TranConflictGraph_t Graph;
    Cec_TranCandVec_t Vertices = {0};
    Vec_Int_t * vProvedIds = Vec_IntAlloc( 64 );
    Gia_Obj_t * pObj;
    int * pRefs = ABC_ALLOC( int, Gia_ManObjNum(p) );
    char * pChosen;
    long long nEdges = 0, SelectedWeight;
    int i, k, iObj, iFan, iProved, Gain;
    int nSelected = 0, nGainEvals = 0, nInitialProved = 0;
    int nInitialPositive = 0, InitialMaxGain = 0, FirstGain = 0;
    int fTime = pDirtyWork && pDirtyWork->Profile;
    abctime clk = fTime ? Abc_Clock() : 0;

    // This is the one structural refresh for the frozen commit wave.
    memcpy( pRefs, p->pRefs, sizeof(int) * Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
        if ( pCovered[i] )
        {
            iFan = Gia_ObjFaninId0p( p, pObj );
            assert( pRefs[iFan] > 0 );
            pRefs[iFan]--;
            iFan = Gia_ObjFaninId1p( p, pObj );
            assert( pRefs[iFan] > 0 );
            pRefs[iFan]--;
        }
    Cec_TranFrozenHashStart( p, &FrozenHash );
    Cec_TranConflictGraphStart( &Graph, Gia_ManObjNum(p) );
    for ( i = 0; i < pProved->nSize; i++ )
    {
        Cec_TranCand_t Cand = pProved->pArray[i];
        if ( Cand.nStatus != CEC_TRAN_STATE_PROVED_COMB &&
             Cand.nStatus != CEC_TRAN_STATE_PROVED_SEQ )
            continue;
        nInitialProved++;
        if ( pCovered[Cand.iTarget] || pUsed[Cand.iTarget] )
        {
            pProf->nDirtyRootFreed++;
            continue;
        }
        Gain = Cec_TranCandFrozenGainWithRefs( p, &FrozenHash, &Cand,
            pCovered, pUsed, pRefs, pMffc, vMffc, vSupport );
        nGainEvals++;
        if ( Gain <= 0 )
        {
            pProf->nDirtySupportFreed++;
            continue;
        }
        nInitialPositive++;
        InitialMaxGain = Abc_MaxInt( InitialMaxGain, Gain );
        if ( Gain != Cand.Gain || Vec_IntSize(vMffc) != Cand.nMffc )
            pProf->nDirtyMffcChanged++;
        Cand.Gain = Gain;
        Cand.nMffc = Vec_IntSize( vMffc );
        Cand.fPrimaryFrontier = 1;
        pProved->pArray[i].Gain = Gain;
        pProved->pArray[i].nMffc = Cand.nMffc;
        Cec_TranCandVecPush( &Vertices, Cand );
        Vec_IntPush( vProvedIds, i );
        Cec_TranConflictGraphAdd( &Graph, vMffc, vSupport );
    }
    Cec_TranConflictGraphFinalize( &Graph );
    pChosen = ABC_CALLOC( char, Vertices.nSize );
    if ( fTime ) pDirtyWork->PrepareTicks += Abc_Clock() - clk;
    if ( pDirtyWork ) Cec_TranSelectionDirtyStart(pDirtyWork,&Graph,0);
    if ( fTime ) clk = Abc_Clock();
    SelectedWeight = Vertices.nSize ?
        Cec_TranConflictGraphGwminDirty( &Graph, &Vertices,
            pChosen, &nEdges, &FirstGain, pDirtyWork, NULL ) : 0;
    if ( fTime ) pDirtyWork->GwminTicks += Abc_Clock() - clk;
    if ( pDirtyWork ) Cec_TranSelectionDirtyRelease(pDirtyWork);
    if ( fTime ) clk = Abc_Clock();
    if ( SelectedWeight )
        SelectedWeight = Cec_TranRepairSelectedExact( p, &Vertices,
            pChosen, SelectedWeight );
    if ( fTime ) pDirtyWork->RepairTicks += Abc_Clock() - clk;
    if ( fTime ) clk = Abc_Clock();

    // Apply the independent-set decision as metadata only.  No selected
    // candidate is re-evaluated on a partially modified graph in this wave.
    for ( i = 0; i < Vertices.nSize; i++ )
        if ( pChosen[i] )
        {
            Cec_TranCand_t Cand = Vertices.pArray[i];
            int Lane = Cand.nProofLane ? Cand.nProofLane - 1 :
                (Cand.nStatus == CEC_TRAN_STATE_PROVED_COMB ? 0 : 1);
            int Phase = Cand.nProofLane ? Cand.nProofPhase : Lane;
            int Kind = Cand.nProofLane ? Cand.nProofKind : Cand.nKind;
            assert( Cand.nKind != CEC_TRAN_CAND_CONSTR || Cand.Gain > 0 );
            Cand.nStatus = CEC_TRAN_STATE_SELECTED;
            Cec_TranCandVecPush( pSelected, Cand );
            iProved = Vec_IntEntry( vProvedIds, i );
            if ( fTime ) Cec_TranSelectionDirtySelected(pDirtyWork,&Cand,iProved);
            pProved->pArray[iProved].Gain = Cand.Gain;
            pProved->pArray[iProved].nStatus = CEC_TRAN_STATE_SELECTED;
            for ( k = Vec_IntEntry(Graph.vMffcBeg, i);
                  k < Vec_IntEntry(Graph.vMffcBeg, i + 1); k++ )
            {
                iObj = Vec_IntEntry( Graph.vMffcData, k );
                assert( !pCovered[iObj] );
                pCovered[iObj] = pSolved[iObj] = 1;
            }
            for ( k = Vec_IntEntry(Graph.vSuppBeg, i);
                  k < Vec_IntEntry(Graph.vSuppBeg, i + 1); k++ )
            {
                iObj = Vec_IntEntry( Graph.vSuppData, k );
                assert( !pCovered[iObj] );
                pUsed[iObj] = 1;
            }
            pProf->nStageKindSelected[Phase][Kind]++;
            pProf->nStageKindMarginalAndGain[Phase][Kind] += Cand.Gain;
            pProf->nLaneKindSelected[Lane][Kind]++;
            nSelected++;
        }
    assert( (nSelected == 0) == (SelectedWeight == 0) );
    CEC_TRAN_VERBOSE( pProf->fVerbose, "stran-root commit selection: policy=commit-wave-root-loss-gwmin initial-proved=%d initial-positive=%d initial-max-gain=%d first-gain=%d rounds=%d gain-evals=%d graph-vertices=%d graph-edges=%lld selected-weight=%lld refreshes=1.\n",
        nInitialProved, nInitialPositive, InitialMaxGain, FirstGain,
        nSelected, nGainEvals, Vertices.nSize, nEdges, SelectedWeight );
    ABC_FREE( pChosen );
    ABC_FREE( pRefs );
    Cec_TranFrozenHashStop( &FrozenHash );
    Cec_TranConflictGraphStop( &Graph );
    Cec_TranCandVecStop( &Vertices );
    Vec_IntFree( vProvedIds );
    if ( fTime )
    {
        pDirtyWork->ApplyTicks += Abc_Clock() - clk;
        Cec_TranSelectionDirtyPrint(pDirtyWork,nInitialProved,nInitialPositive,
            nEdges,nSelected,SelectedWeight,FirstGain);
    }
    if ( pDirtyWork && pDirtyWork->RootMax && !nInitialPositive )
    {
        pDirtyWork->RootMax->NVertices=0;
        pDirtyWork->RootMax->Reason="empty";
    }
    if ( pDirtyWork && pDirtyWork->RootMax )
        Cec_TranRootMaxPrint(pDirtyWork->RootMax,pDirtyWork,nEdges,nSelected);
    return nSelected;
}

static int Cec_TranRootConsumeProved( Gia_Man_t * p,
    Cec_TranCandVec_t * pProved, char * pCovered, char * pUsed,
    char * pSolved, char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    Cec_TranCandVec_t * pSelected, Cec_TranProf_t * pProf )
{
    return Cec_TranRootConsumeProvedDirty(p,pProved,pCovered,pUsed,pSolved,
        pMffc,vMffc,vSupport,pSelected,pProf,NULL);
}

// Called only by the explicit Strict SEQ discovery microbatch site.
static int Cec_TranRootConsumeProvedScoped( Gia_Man_t * p,
    Cec_TranCandVec_t * pProved, char * pCovered, char * pUsed,
    char * pSolved, char * pMffc, Vec_Int_t * vMffc, Vec_Int_t * vSupport,
    Cec_TranCandVec_t * pSelected, Cec_TranProf_t * pProf, int wave )
{
    static int mode=-1,profile=-1,calls=0,maxMode=-1,maxProfile=-1,maxMiB=0;
    Cec_TranSelectionDirty_t work;
    Cec_TranSelectionRootMax_t maxWork;
    if(mode<0)
    {
        mode=Cec_TranStrictCexOption("ABC_STRICT_SELECTION_DIRTY",0,2);
        profile=Cec_TranStrictCexOption("ABC_STRICT_SELECTION_DIRTY_PROFILE",0,1);
        maxMode=Cec_TranStrictCexOption("ABC_STRICT_SELECTION_ROOTMAX",0,2);
        maxProfile=Cec_TranStrictCexOption("ABC_STRICT_SELECTION_ROOTMAX_PROFILE",0,1);
        maxMiB=Cec_TranStrictCexOption("ABC_STRICT_SELECTION_ROOTMAX_MAX_MIB",8192,INT_MAX);
    }
    if(!mode && !profile && !maxMode && !maxProfile)
        return Cec_TranRootConsumeProved(p,pProved,pCovered,pUsed,pSolved,
            pMffc,vMffc,vSupport,pSelected,pProf);
    Cec_TranSelectionDirtyInit(&work,mode,profile);
    if(maxMode || maxProfile)
    {
        size_t limit=(size_t)maxMiB<=(size_t)-1/1048576 ? (size_t)maxMiB*1048576 : 0;
        Cec_TranRootMaxInit(&maxWork,maxMode,maxProfile,limit,0);
        work.RootMax=&maxWork;
    }
    work.Call=++calls; work.Round=pProf->PreproofRound; work.Wave=wave;
    return Cec_TranRootConsumeProvedDirty(p,pProved,pCovered,pUsed,pSolved,
        pMffc,vMffc,vSupport,pSelected,pProf,&work);
}

// Helper experiments deliberately have no selection heuristic or size cap.
// With helper reuse enabled, every unique, still-valid retained certificate is
// materialized into the temporary proof graph.  With it disabled, none is
// seeded.  Retention and future commit eligibility are identical in both
// modes, so the switch isolates only the inductive value of H.
static void Cec_TranPrepareHelpers( Gia_Man_t * p,
    Cec_TranCandVec_t const * pRetained,
    Cec_TranCandVec_t const * pObligations, int fUseHelpers, int fVerbose,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t * pActive )
{
    Cec_TranCandVec_t Unique = {0};
    Vec_Int_t * vSupport = Vec_IntAlloc( 16 );
    int nObjs = Gia_ManObjNum(p);
    char * pEndpoints = ABC_CALLOC( char, nObjs );
    char * pClasses = ABC_CALLOC( char, nObjs );
    int i, k, iObj, nEndpoints = 0, nGates = 0;
    int nClasses = 0, nEstimate;
    Cec_TranCandVecClear( pActive );
    for ( i = 0; i < pRetained->nSize; i++ )
    {
        Cec_TranCand_t Cand = pRetained->pArray[i];
        if ( !Cec_TranCandVecContains(&Unique, &Cand) )
            Cec_TranCandVecPush( &Unique, Cand );
        else
            pProf->nHelperDedup++;
    }
    if ( fUseHelpers )
        for ( i = 0; i < Unique.nSize; i++ )
            Cec_TranCandVecPush( pActive, Unique.pArray[i] );
    for ( i = 0; i < pActive->nSize; i++ )
    {
        Cec_TranCand_t Cand = pActive->pArray[i];
        if ( !pClasses[Cand.iTarget] )
            pClasses[Cand.iTarget] = 1, nClasses++;
        if ( !pEndpoints[Cand.iTarget] )
            pEndpoints[Cand.iTarget] = 1, nEndpoints++;
        Cec_TranCandCollectSupport( &Cand, vSupport );
        Vec_IntForEachEntry( vSupport, iObj, k )
            if ( !pEndpoints[iObj] )
                pEndpoints[iObj] = 1, nEndpoints++;
        nGates += Cand.nGates;
    }
    nEstimate = Gia_ManObjNum(p) + nGates +
        4 * (pActive->nSize + pObligations->nSize);
    pProf->nHelperRetained = Abc_MaxInt(
        pProf->nHelperRetained, Unique.nSize );
    pProf->nHelperInjected += pActive->nSize;
    pProf->nHelperInactive += Unique.nSize - pActive->nSize;
    pProf->nHelperClasses += nClasses;
    pProf->nHelperEndpoints = Abc_MaxInt(pProf->nHelperEndpoints, nEndpoints);
    pProf->nHelperMaterialGates += nGates;
    if ( fVerbose )
        Abc_Print( 1, "stran-root helper batch: enabled=%s retained=%d active=%d inactive=%d classes=%d endpoints=%d materialized-gates=%d obligations=%d relation-total=%d estimated-srm-nodes=%d.\n",
            fUseHelpers ? "yes" : "no", Unique.nSize, pActive->nSize,
            Unique.nSize - pActive->nSize, nClasses, nEndpoints,
            nGates, pObligations->nSize,
            pActive->nSize + pObligations->nSize, nEstimate );
    Cec_TranCandVecStop( &Unique );
    Vec_IntFree( vSupport );
    ABC_FREE( pEndpoints );
    ABC_FREE( pClasses );
}

// Deterministic structural tests for the root pipeline changes which are too
// small to justify external fixtures: rank-before-B selection, TFI-only
// Existing lookup, zero-gain filtering, H/O proof-graph separation, proof
// history remap, and the temporary/permanent AIG boundary.
// Prove the complete selected frontier on one immutable snapshot.  COMB-only
// closure stops after CBS; the SEQ phase sends every CBS-unproved submitted
// relation to one shared correspondence fixed point.
static int Cec_TranRootProvePortfolio( Gia_Man_t * p,
    Cec_TranCandVec_t const * pHelpers, Cec_TranCandVec_t * pPortfolio,
    Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t * pProved, int fCombOnly,
    int iPhase )
{
    Vec_Int_t * vStatus;
    Vec_Str_t * vStage;
    Cec_TranCand_t Cand;
    int i, iStage, nNew = 0;
    if ( pPortfolio->nSize == 0 )
        return 0;
    Cec_TranPreproofEvent( pProf, p, "portfolio-sort", 0, pPortfolio->nSize, 0 );
    qsort( pPortfolio->pArray, pPortfolio->nSize, sizeof(Cec_TranCand_t),
        Cec_TranCandRootHeuristicCompare );
    Cec_TranPreproofEvent( pProf, p, "portfolio-sort", 1, pPortfolio->nSize, pPortfolio->nSize );
    for ( i = 0; i < pPortfolio->nSize; i++ )
    {
        pProf->nStageKindSubmitted[iPhase][pPortfolio->pArray[i].nKind]++;
        pProf->nLaneKindSubmitted[0][pPortfolio->pArray[i].nKind]++;
        if ( pPortfolio->pArray[i].fKitPortfolio )
            pProf->nRootKitSubmitted++;
        if ( pPortfolio->pArray[i].fBdcPortfolio )
            pProf->nRootBdcSubmitted++;
    }
    vStatus = Cec_TranProveRootBatch( p,
        pHelpers ? pHelpers->pArray : NULL,
        pHelpers ? pHelpers->nSize : 0,
        pPortfolio->pArray, pPortfolio->nSize,
        pPars, pProf, fCombOnly, &vStage );
    for ( i = 0; i < pPortfolio->nSize; i++ )
    {
        iStage = Vec_StrEntry( vStage, i );
        // A COMB-only closure pass stops before correspondence.  Candidates
        // rejected by CBS are therefore not SEQ submissions in this pass.
        if ( !fCombOnly && iStage != 1 )
            pProf->nLaneKindSubmitted[1][pPortfolio->pArray[i].nKind]++;
        if ( !Vec_IntEntry(vStatus, i) )
            continue;
        assert( iStage == 1 || iStage == 2 );
        Cand = pPortfolio->pArray[i];
        Cand.nProofStage = iStage;
        Cand.nProofLane = iStage;
        Cand.nProofPhase = iPhase;
        Cand.nProofKind = Cand.nKind;
        Cand.nStatus = iStage == 1 ?
            CEC_TRAN_STATE_PROVED_COMB : CEC_TRAN_STATE_PROVED_SEQ;
        pProf->nStageKindProved[iPhase][Cand.nKind]++;
        pProf->nLaneKindProved[iStage - 1][Cand.nKind]++;
        if ( Cec_TranCandVecContains(pProved, &Cand) )
            continue;
        Cec_TranCandVecPush( pProved, Cand );
        nNew++;
    }
    Vec_IntFree( vStatus );
    Vec_StrFree( vStage );
    return nNew;
}

static Gia_Man_t * Cec_TranCommitSelectedRootOnly( Gia_Man_t * p,
    Cec_TranCandVec_t * pSelected, Cec_ParTran_t * pPars,
    Cec_TranProf_t * pProf, Cec_TranCandVec_t const * pCarry,
    Cec_TranCandVec_t * pHistory )
{
    Gia_Man_t * pDup, * pClean;
    Gia_Obj_t * pObj;
    Vec_Int_t * vSelected, * vDupToClean, * vOldToClean;
    long long Marginal = 0;
    int i, iLit, iMapped, Gain, fProved = 1;
    abctime clk;
    if ( pSelected->nSize == 0 )
    {
        if ( pPars->fProfile )
            Cec_TranBuildReductionProfile(p,pSelected,p,"strict");
        Cec_TranCandVecClear( pHistory );
        for ( i = 0; i < pCarry->nSize; i++ )
            Cec_TranCandVecPush( pHistory, pCarry->pArray[i] );
        return p;
    }
    vSelected = Vec_IntAlloc( pSelected->nSize );
    for ( i = 0; i < pSelected->nSize; i++ )
    {
        assert(pSelected->pArray[i].nProofStage == 1 ||
            pSelected->pArray[i].nProofStage == 2);
        assert(pSelected->pArray[i].nProofLane == 1 ||
            pSelected->pArray[i].nProofLane == 2);
        Vec_IntPush( vSelected, i ), Marginal += pSelected->pArray[i].Gain;
    }
    clk = Abc_Clock();
    pDup = Cec_TranDupRootBundle( p, pSelected->pArray, vSelected );
    pProf->timeRootBundleDup += Abc_Clock() - clk;
    clk = Abc_Clock();
    pClean = Cec_TranCleanupKeepRegs( pDup, &vDupToClean );
    pProf->timeRootCleanup += Abc_Clock() - clk;
    vOldToClean = Vec_IntStartFull( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, i )
    {
        iLit = Cec_TranMapLitByValue( p, Abc_Var2Lit(i, 0) );
        if ( iLit < 0 || Abc_Lit2Var(iLit) >= Vec_IntSize(vDupToClean) )
            continue;
        iMapped = Vec_IntEntry( vDupToClean, Abc_Lit2Var(iLit) );
        if ( iMapped >= 0 )
            Vec_IntWriteEntry( vOldToClean, i,
                Abc_LitNotCond(iMapped, Abc_LitIsCompl(iLit)) );
    }
    Cec_TranRemapProofHistory( pClean, vOldToClean, pCarry,
        pHistory, pProf );
    clk = Abc_Clock();
    Gain = Cec_TranGain( p, pClean );
    pProf->timeRootExactAudit += Abc_Clock() - clk;
    assert( Gain > 0 && Gain >= Marginal );
    assert( Gia_ManRegNum(p) == Gia_ManRegNum(pClean) );
    if ( pPars->fShadow )
    {
        clk = Abc_Clock();
        fProved = Cec_TranProveWhole( p, pDup, pPars, pProf );
        pProf->timeShadow += Abc_Clock() - clk;
    }
    assert( fProved );
    // Subset duplication overwrites source Values. The actual commit map and
    // remapped history above have already consumed the full-bundle Values.
    if ( pPars->fProfile )
        Cec_TranBuildReductionProfile(p, pSelected, pClean, "strict");
    pProf->nRootBundleAndGain = Gain;
    pProf->nRootBundleRegGain = Gia_ManRegNum(p) - Gia_ManRegNum(pClean);
    pProf->nRootBundleCommits = pSelected->nSize;
    Gia_ManStop( p );
    Gia_ManStop( pDup );
    Vec_IntFree( vSelected );
    Vec_IntFree( vDupToClean );
    Vec_IntFree( vOldToClean );
    return pClean;
}
