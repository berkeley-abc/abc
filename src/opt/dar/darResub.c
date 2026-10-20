/** Native DAR resubstitution: typed port of ABC FIRST/COST/RETAIN search. */
#include "darInt.h"
#include <limits.h>
#include "bool/dec/dec.h"
#include "misc/util/utilTruth.h"
ABC_NAMESPACE_IMPL_START
#define DAR_RS_PAIRS_MAX 500
#define DAR_RS_INDEX_WORDS 8
typedef struct Dar_ResubPairIndex_t_
{
    word Truth[DAR_RS_PAIRS_MAX + 3], Cover[64][DAR_RS_INDEX_WORDS];
    int Order[64], nOrder, nPairs, nWords;
} Dar_ResubPairIndex_t;

typedef struct Dar_ResubZeroScratch_t_
{
    Vec_Ptr_t * vReady;
    Vec_Int_t * vStamp, * vIndex, * vHeight, * vProcessed, * vTruth;
    int Epoch;
} Dar_ResubZeroScratch_t;

typedef struct Dar_Resub_t_ Dar_Resub_t;
typedef struct Dar_ResubMemo_t_ Dar_ResubMemo_t;
typedef struct Dar_ResubReuse_t_ Dar_ResubReuse_t;
typedef struct Dar_ResubCex_t_ Dar_ResubCex_t;
struct Dar_Resub_t_
{
    Aig_Man_t * pAig;
    Dar_RwrPar_t * pPars;
    int nSearchDivs, Required, Epoch, GainVerified;
    Vec_Ptr_t * vLeaves, * vVisited, * vVolume, * vSavedData;
    Vec_Int_t * vSeen, * vReady, * vMffcMark, * vSavedPhase;
    long long Roots, Candidates, Commits, Gain;
    int fProfile;
    double TimeCut, TimeCollect, TimeSim, TimeSearch, TimeUpdate;
    Dar_ResubPairIndex_t Index[2];
    int fIndex;
    int fCexColumns, fCexCheck;
    Dar_ResubCex_t * pCex;
    Vec_Ptr_t * vZeroReady;
    Vec_Int_t * vZeroStamp, * vZeroIndex, * vZeroHeight, * vZeroProcessed, * vZeroTruth;
    long long ZeroQueries, ZeroSkipped;
    int fZeroEnabled;
    int fZeroMixed, fZeroMixedCheck;
    Dar_ResubZeroScratch_t ZeroCheck;
    long long ZeroMixedLayers, ZeroMixedFanoutRows, ZeroMixedPairRows;
    long long ZeroMixedAudits, ZeroMixedAbsentAudits;
    int fCollectReuse, fCollectReuseCheck, CollectStops;
    long long CollectQueries, CollectEligible, CollectClosed, CollectSkipped, CollectShadow;
    long long CollectHighFanout, CollectCapped, CollectLeafAlias, CollectUnsupported;
    Dar_ResubMemo_t * pMemo;
    Dar_ResubReuse_t * pReuse;
    // parameters
    int                nLeavesMax; // the max number of leaves in the cone
    int                nDivsMax;   // the max number of divisors in the cone
    // representation of the cone
    Aig_Obj_t *        pRoot;      // the root of the cone
    int                nLeaves;    // the number of leaves
    int                nDivs;      // the number of all divisor (including leaves)
    int                nMffc;      // the size of MFFC
    Vec_Ptr_t *        vDivs;      // the divisors
    // representation of the simulation info
    int                nBits;      // the number of simulation bits
    int                nWords;     // the number of unsigneds for siminfo
    Vec_Ptr_t        * vSims;      // simulation info
    unsigned         * pInfo;      // pointer to simulation info
    // observability don't-cares
    unsigned *         pCareSet;
    // internal divisor storage
    Vec_Ptr_t        * vDivs1UP;   // the single-node unate divisors
    Vec_Ptr_t        * vDivs1UN;   // the single-node unate divisors
    Vec_Ptr_t        * vDivs1B;    // the single-node binate divisors
    Vec_Ptr_t        * vDivs2UP0;  // the double-node unate divisors
    Vec_Ptr_t        * vDivs2UP1;  // the double-node unate divisors
    Vec_Ptr_t        * vDivs2UN0;  // the double-node unate divisors
    Vec_Ptr_t        * vDivs2UN1;  // the double-node unate divisors
    // other data
    Vec_Ptr_t        * vTemp;      // temporary array of nodes
};


static int Dar_ResubConsider( Dar_Resub_t * p, Dec_Graph_t * pGraph );
static void Dar_ResubIndexBuild( Dar_Resub_t * p, int fUP );
static Dec_Graph_t * Dar_ResubDivs2Indexed( Dar_Resub_t * p );
static Dec_Graph_t * Dar_ResubDivs3Indexed( Dar_Resub_t * p );
static unsigned Dar_ResubPairWord( Aig_Obj_t * a, Aig_Obj_t * b, int w );

#include "darResubMemo.h"
#include "darResubReuse.h"
#include "darResubCex.h"

static Dar_Resub_t * Dar_ResubStart( int nLeavesMax, int nDivsMax )
{
    Dar_Resub_t * p;
    unsigned * pData;
    int i, k, fCertificateAudit;
    assert( sizeof(unsigned) == 4 );
    p = ABC_ALLOC( Dar_Resub_t, 1 );
    memset( p, 0, sizeof(Dar_Resub_t) );
    p->nLeavesMax = nLeavesMax;
    p->nDivsMax   = nDivsMax;
    p->vDivs      = Vec_PtrAlloc( p->nDivsMax );
    // allocate simulation info
    p->nBits      = (1 << p->nLeavesMax);
    p->nWords     = (p->nBits <= 32)? 1 : (p->nBits / 32);
    p->pInfo      = ABC_ALLOC( unsigned, p->nWords * (p->nDivsMax + 1) );
    memset( p->pInfo, 0, sizeof(unsigned) * p->nWords * p->nLeavesMax );
    p->vSims      = Vec_PtrAlloc( p->nDivsMax );
    for ( i = 0; i < p->nDivsMax; i++ )
        Vec_PtrPush( p->vSims, p->pInfo + i * p->nWords );
    // assign the care set
    p->pCareSet  = p->pInfo + p->nDivsMax * p->nWords;
    memset( p->pCareSet, 0xff, sizeof(unsigned) * p->nWords );
    // set elementary truth tables
    for ( k = 0; k < p->nLeavesMax; k++ )
    {
        pData = (unsigned *)p->vSims->pArray[k];
        for ( i = 0; i < p->nBits; i++ )
            if ( i & (1 << k) )
                pData[i>>5] |= (1u << (i&31));
    }
    // create the remaining divisors
    p->vDivs1UP  = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1UN  = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs1B   = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UP0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UP1 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UN0 = Vec_PtrAlloc( p->nDivsMax );
    p->vDivs2UN1 = Vec_PtrAlloc( p->nDivsMax );
    p->vTemp     = Vec_PtrAlloc( p->nDivsMax );
    p->vLeaves = Vec_PtrAlloc(nLeavesMax); p->vVisited = Vec_PtrAlloc(256);
    p->vVolume = Vec_PtrAlloc(256); p->vSavedData = Vec_PtrAlloc(150);
    p->vSeen = Vec_IntAlloc(0); p->vReady = Vec_IntAlloc(0);
    p->vMffcMark = Vec_IntAlloc(0); p->vSavedPhase = Vec_IntAlloc(150);
    p->vZeroReady = Vec_PtrAlloc(150); p->vZeroStamp = Vec_IntAlloc(0);
    p->vZeroIndex = Vec_IntAlloc(0); p->vZeroHeight = Vec_IntAlloc(0);
    p->vZeroProcessed = Vec_IntAlloc(0); p->vZeroTruth = Vec_IntAlloc(0);
    p->fZeroEnabled = getenv("ABC_DRW_ZERO_DISABLE") == NULL;
    p->fZeroMixed = Dar_ResubReuseOption("ABC_DRW_ZERO_MIXED", 1);
    p->fZeroMixedCheck = p->fZeroMixed && Dar_ResubReuseEnabled("ABC_DRW_ZERO_MIXED_CHECK");
    if ( p->fZeroMixedCheck )
    {
        p->ZeroCheck.vReady = Vec_PtrAlloc(150);
        p->ZeroCheck.vStamp = Vec_IntAlloc(0); p->ZeroCheck.vIndex = Vec_IntAlloc(0);
        p->ZeroCheck.vHeight = Vec_IntAlloc(0); p->ZeroCheck.vProcessed = Vec_IntAlloc(0);
        p->ZeroCheck.vTruth = Vec_IntAlloc(0);
    }
    p->fCollectReuse = Dar_ResubReuseOption("ABC_DRW_COLLECT_REUSE", 1);
    p->fCollectReuseCheck = p->fCollectReuse && Dar_ResubReuseEnabled("ABC_DRW_COLLECT_REUSE_CHECK");
    /* Certificate audits must not replay an earlier candidate stream, even
       when collection reuse is explicitly disabled for an ablation. */
    fCertificateAudit = p->fCollectReuseCheck ||
        Dar_ResubReuseEnabled("ABC_DRW_GLOBAL_FAIL_CHECK");
    p->fIndex = getenv("ABC_DRW_INDEX_DISABLE") == NULL;
    if ( !fCertificateAudit && Dar_ResubReuseOption("ABC_DRW_RESUB_MEMO", 1) )
        p->pMemo = Dar_ResubMemoStart();
    if ( nLeavesMax < 5 ) p->pCareSet[0] = (1u << (1 << nLeavesMax)) - 1;
    return p;
}

static void Dar_ResubStop( Dar_Resub_t * p )
{
    Dar_ResubCexStop(p);
    if ( p->fProfile && p->fZeroMixed )
        printf("DAR_ZERO_MIXED enabled=1 check=%d queries=%lld layers=%lld fanout_rows=%lld pair_rows=%lld audits=%lld absent_audits=%lld\n",
            p->fZeroMixedCheck,p->ZeroQueries,p->ZeroMixedLayers,p->ZeroMixedFanoutRows,
            p->ZeroMixedPairRows,p->ZeroMixedAudits,p->ZeroMixedAbsentAudits);
    if ( p->fProfile && p->fCollectReuse )
        printf("DAR_COLLECT_REUSE enabled=1 check=%d queries=%lld eligible=%lld closed=%lld skipped=%lld shadow=%lld high_fanout=%lld capped=%lld leaf_alias=%lld unsupported=%lld\n",
            p->fCollectReuseCheck,p->CollectQueries,p->CollectEligible,p->CollectClosed,
            p->CollectSkipped,p->CollectShadow,p->CollectHighFanout,p->CollectCapped,p->CollectLeafAlias,p->CollectUnsupported);
    Dar_ResubReuseStop(p);
    Dar_ResubMemoStop(p->pMemo, p->fProfile);
    Vec_PtrFree( p->vDivs );
    Vec_PtrFree( p->vSims );
    Vec_PtrFree( p->vDivs1UP );
    Vec_PtrFree( p->vDivs1UN );
    Vec_PtrFree( p->vDivs1B );
    Vec_PtrFree( p->vDivs2UP0 );
    Vec_PtrFree( p->vDivs2UP1 );
    Vec_PtrFree( p->vDivs2UN0 );
    Vec_PtrFree( p->vDivs2UN1 );
    Vec_PtrFree( p->vTemp );
    Vec_PtrFree(p->vLeaves); Vec_PtrFree(p->vVisited); Vec_PtrFree(p->vVolume);
    Vec_PtrFree(p->vSavedData); Vec_IntFree(p->vSeen); Vec_IntFree(p->vReady);
    Vec_IntFree(p->vMffcMark); Vec_IntFree(p->vSavedPhase);
    Vec_PtrFree(p->vZeroReady); Vec_IntFree(p->vZeroStamp); Vec_IntFree(p->vZeroIndex);
    Vec_IntFree(p->vZeroHeight); Vec_IntFree(p->vZeroProcessed); Vec_IntFree(p->vZeroTruth);
    if ( p->fZeroMixedCheck )
    {
        Vec_PtrFree(p->ZeroCheck.vReady); Vec_IntFree(p->ZeroCheck.vStamp);
        Vec_IntFree(p->ZeroCheck.vIndex); Vec_IntFree(p->ZeroCheck.vHeight);
        Vec_IntFree(p->ZeroCheck.vProcessed); Vec_IntFree(p->ZeroCheck.vTruth);
    }
    ABC_FREE( p->pInfo );
    ABC_FREE( p );
}

static void Dar_ResubSimulate( Vec_Ptr_t * vDivs, int nLeaves, Vec_Ptr_t * vSims, int nLeavesMax, int nWords )
{
    Aig_Obj_t * pObj;
    unsigned * puData0, * puData1, * puData;
    int i, k;
    assert( Vec_PtrSize(vDivs) - nLeaves <= Vec_PtrSize(vSims) - nLeavesMax );
    // simulate
    Vec_PtrForEachEntry( Aig_Obj_t *, vDivs, pObj, i )
    {
        if ( i < nLeaves )
        { // initialize the leaf
            pObj->pData = Vec_PtrEntry( vSims, i );
            continue;
        }
        // set storage for the node's simulation info
        pObj->pData = Vec_PtrEntry( vSims, i - nLeaves + nLeavesMax );
        // get pointer to the simulation info
        puData  = (unsigned *)pObj->pData;
        puData0 = (unsigned *)Aig_ObjFanin0(pObj)->pData;
        puData1 = (unsigned *)Aig_ObjFanin1(pObj)->pData;
        // simulate
        if ( Aig_ObjFaninC0(pObj) && Aig_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & ~puData1[k];
        else if ( Aig_ObjFaninC0(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData0[k] & puData1[k];
        else if ( Aig_ObjFaninC1(pObj) )
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & ~puData1[k];
        else
            for ( k = 0; k < nWords; k++ )
                puData[k] = puData0[k] & puData1[k];
    }
    // normalize
    Vec_PtrForEachEntry( Aig_Obj_t *, vDivs, pObj, i )
    {
        puData = (unsigned *)pObj->pData;
        pObj->fPhase = (puData[0] & 1);
        if ( pObj->fPhase )
            for ( k = 0; k < nWords; k++ )
                puData[k] = ~puData[k];
    }
}

static Dec_Graph_t * Dar_ResubQuit0( Aig_Obj_t * pRoot, Aig_Obj_t * pObj )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot;
    pGraph = Dec_GraphCreate( 1 );
    Dec_GraphNode( pGraph, 0 )->pFunc = pObj;
    eRoot = Dec_EdgeCreate( 0, pObj->fPhase );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

static Dec_Graph_t * Dar_ResubQuit1( Aig_Obj_t * pRoot, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1;
    assert( Aig_Regular(pObj0) != Aig_Regular(pObj1) );
    pGraph = Dec_GraphCreate( 2 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Aig_Regular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Aig_Regular(pObj1);
    eNode0 = Dec_EdgeCreate( 0, Aig_Regular(pObj0)->fPhase ^ Aig_IsComplement(pObj0) );
    eNode1 = Dec_EdgeCreate( 1, Aig_Regular(pObj1)->fPhase ^ Aig_IsComplement(pObj1) );
    if ( fOrGate )
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
    else
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

static Dec_Graph_t * Dar_ResubQuit21( Aig_Obj_t * pRoot, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1, Aig_Obj_t * pObj2, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, eNode0, eNode1, eNode2;
    assert( Aig_Regular(pObj0) != Aig_Regular(pObj1) );
    assert( Aig_Regular(pObj0) != Aig_Regular(pObj2) );
    assert( Aig_Regular(pObj1) != Aig_Regular(pObj2) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Aig_Regular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Aig_Regular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Aig_Regular(pObj2);
    eNode0 = Dec_EdgeCreate( 0, Aig_Regular(pObj0)->fPhase ^ Aig_IsComplement(pObj0) );
    eNode1 = Dec_EdgeCreate( 1, Aig_Regular(pObj1)->fPhase ^ Aig_IsComplement(pObj1) );
    eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase ^ Aig_IsComplement(pObj2) );
    if ( fOrGate )
    {
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode2, eRoot );
    }
    else
    {
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode2, eRoot );
    }
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

static Dec_Graph_t * Dar_ResubQuit2( Aig_Obj_t * pRoot, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1, Aig_Obj_t * pObj2, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, ePrev, eNode0, eNode1, eNode2;
    assert( Aig_Regular(pObj0) != Aig_Regular(pObj1) );
    assert( Aig_Regular(pObj0) != Aig_Regular(pObj2) );
    assert( Aig_Regular(pObj1) != Aig_Regular(pObj2) );
    pGraph = Dec_GraphCreate( 3 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Aig_Regular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Aig_Regular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Aig_Regular(pObj2);
    eNode0 = Dec_EdgeCreate( 0, Aig_Regular(pObj0)->fPhase ^ Aig_IsComplement(pObj0) );
    if ( Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
    {
        eNode1 = Dec_EdgeCreate( 1, Aig_Regular(pObj1)->fPhase );
        eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase );
        ePrev  = Dec_GraphAddNodeOr( pGraph, eNode1, eNode2 );
    }
    else
    {
        eNode1 = Dec_EdgeCreate( 1, Aig_Regular(pObj1)->fPhase ^ Aig_IsComplement(pObj1) );
        eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase ^ Aig_IsComplement(pObj2) );
        ePrev  = Dec_GraphAddNodeAnd( pGraph, eNode1, eNode2 );
    }
    if ( fOrGate )
        eRoot  = Dec_GraphAddNodeOr( pGraph, eNode0, ePrev );
    else
        eRoot  = Dec_GraphAddNodeAnd( pGraph, eNode0, ePrev );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

static Dec_Graph_t * Dar_ResubQuit3( Aig_Obj_t * pRoot, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1, Aig_Obj_t * pObj2, Aig_Obj_t * pObj3, int fOrGate )
{
    Dec_Graph_t * pGraph;
    Dec_Edge_t eRoot, ePrev0, ePrev1, eNode0, eNode1, eNode2, eNode3;
    assert( Aig_Regular(pObj0) != Aig_Regular(pObj1) );
    assert( Aig_Regular(pObj2) != Aig_Regular(pObj3) );
    pGraph = Dec_GraphCreate( 4 );
    Dec_GraphNode( pGraph, 0 )->pFunc = Aig_Regular(pObj0);
    Dec_GraphNode( pGraph, 1 )->pFunc = Aig_Regular(pObj1);
    Dec_GraphNode( pGraph, 2 )->pFunc = Aig_Regular(pObj2);
    Dec_GraphNode( pGraph, 3 )->pFunc = Aig_Regular(pObj3);
    if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) )
    {
        eNode0 = Dec_EdgeCreate( 0, Aig_Regular(pObj0)->fPhase );
        eNode1 = Dec_EdgeCreate( 1, Aig_Regular(pObj1)->fPhase );
        ePrev0 = Dec_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        if ( Aig_IsComplement(pObj2) && Aig_IsComplement(pObj3) )
        {
            eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase );
            eNode3 = Dec_EdgeCreate( 3, Aig_Regular(pObj3)->fPhase );
            ePrev1 = Dec_GraphAddNodeOr( pGraph, eNode2, eNode3 );
        }
        else
        {
            eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase ^ Aig_IsComplement(pObj2) );
            eNode3 = Dec_EdgeCreate( 3, Aig_Regular(pObj3)->fPhase ^ Aig_IsComplement(pObj3) );
            ePrev1 = Dec_GraphAddNodeAnd( pGraph, eNode2, eNode3 );
        }
    }
    else
    {
        eNode0 = Dec_EdgeCreate( 0, Aig_Regular(pObj0)->fPhase ^ Aig_IsComplement(pObj0) );
        eNode1 = Dec_EdgeCreate( 1, Aig_Regular(pObj1)->fPhase ^ Aig_IsComplement(pObj1) );
        ePrev0 = Dec_GraphAddNodeAnd( pGraph, eNode0, eNode1 );
        if ( Aig_IsComplement(pObj2) && Aig_IsComplement(pObj3) )
        {
            eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase );
            eNode3 = Dec_EdgeCreate( 3, Aig_Regular(pObj3)->fPhase );
            ePrev1 = Dec_GraphAddNodeOr( pGraph, eNode2, eNode3 );
        }
        else
        {
            eNode2 = Dec_EdgeCreate( 2, Aig_Regular(pObj2)->fPhase ^ Aig_IsComplement(pObj2) );
            eNode3 = Dec_EdgeCreate( 3, Aig_Regular(pObj3)->fPhase ^ Aig_IsComplement(pObj3) );
            ePrev1 = Dec_GraphAddNodeAnd( pGraph, eNode2, eNode3 );
        }
    }
    if ( fOrGate )
        eRoot = Dec_GraphAddNodeOr( pGraph, ePrev0, ePrev1 );
    else
        eRoot = Dec_GraphAddNodeAnd( pGraph, ePrev0, ePrev1 );
    Dec_GraphSetRoot( pGraph, eRoot );
    if ( pRoot->fPhase )
        Dec_GraphComplement( pGraph );
    return pGraph;
}

static void Dar_ResubDivsS( Dar_Resub_t * p, int Required )
{
    int fMoreDivs = 1; // bug fix by Siang-Yun Lee
    Aig_Obj_t * pObj;
    unsigned * puData, * puDataR;
    int i, w;
    Vec_PtrClear( p->vDivs1UP );
    Vec_PtrClear( p->vDivs1UN );
    Vec_PtrClear( p->vDivs1B );
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntryStop( Aig_Obj_t *, p->vDivs, pObj, i, p->nSearchDivs )
    {
        if ( (int)pObj->Level > Required - 1 )
            continue;

        puData = (unsigned *)pObj->pData;
        // check positive containment
        for ( w = 0; w < p->nWords; w++ )
//            if ( puData[w] & ~puDataR[w] )
            if ( puData[w] & ~puDataR[w] & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
        {
            Vec_PtrPush( p->vDivs1UP, pObj );
            continue;
        }
        if ( fMoreDivs )
        {
            for ( w = 0; w < p->nWords; w++ )
    //            if ( ~puData[w] & ~puDataR[w] )
                if ( ~puData[w] & ~puDataR[w] & p->pCareSet[w] ) // care set
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs1UP, Aig_Not(pObj) );
                continue;
            }
        }
        // check negative containment
        for ( w = 0; w < p->nWords; w++ )
//            if ( ~puData[w] & puDataR[w] )
            if ( ~puData[w] & puDataR[w] & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
        {
            Vec_PtrPush( p->vDivs1UN, pObj );
            continue;
        }
        if ( fMoreDivs )
        {
            for ( w = 0; w < p->nWords; w++ )
    //            if ( puData[w] & puDataR[w] )
                if ( puData[w] & puDataR[w] & p->pCareSet[w] ) // care set
                    break;
            if ( w == p->nWords )
            {
                Vec_PtrPush( p->vDivs1UN, Aig_Not(pObj) );
                continue;
            }
        }
        // add the node to binates
        Vec_PtrPush( p->vDivs1B, pObj );
    }
}

static void Dar_ResubDivsD( Dar_Resub_t * p, int Required )
{
    Aig_Obj_t * pObj0, * pObj1;
    unsigned * puData0, * puData1, * puDataR;
    int i, k, w;
    Vec_PtrClear( p->vDivs2UP0 );
    Vec_PtrClear( p->vDivs2UP1 );
    Vec_PtrClear( p->vDivs2UN0 );
    Vec_PtrClear( p->vDivs2UN1 );
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1B, pObj0, i )
    {
        if ( (int)pObj0->Level > Required - 2 )
            continue;

        puData0 = (unsigned *)pObj0->pData;
        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1B, pObj1, k, i + 1 )
        {
            if ( (int)pObj1->Level > Required - 2 )
                continue;

            puData1 = (unsigned *)pObj1->pData;

            if ( Vec_PtrSize(p->vDivs2UP0) < DAR_RS_PAIRS_MAX )
            {
                // get positive unate divisors
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (puData0[w] & puData1[w]) & ~puDataR[w] )
                    if ( (puData0[w] & puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, pObj0 );
                    Vec_PtrPush( p->vDivs2UP1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (~puData0[w] & puData1[w]) & ~puDataR[w] )
                    if ( (~puData0[w] & puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, Aig_Not(pObj0) );
                    Vec_PtrPush( p->vDivs2UP1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (puData0[w] & ~puData1[w]) & ~puDataR[w] )
                    if ( (puData0[w] & ~puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, pObj0 );
                    Vec_PtrPush( p->vDivs2UP1, Aig_Not(pObj1) );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( (puData0[w] | puData1[w]) & ~puDataR[w] )
                    if ( (puData0[w] | puData1[w]) & ~puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UP0, Aig_Not(pObj0) );
                    Vec_PtrPush( p->vDivs2UP1, Aig_Not(pObj1) );
                }
            }

            if ( Vec_PtrSize(p->vDivs2UN0) < DAR_RS_PAIRS_MAX )
            {
                // get negative unate divisors
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(puData0[w] & puData1[w]) & puDataR[w] )
                    if ( ~(puData0[w] & puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, pObj0 );
                    Vec_PtrPush( p->vDivs2UN1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(~puData0[w] & puData1[w]) & puDataR[w] )
                    if ( ~(~puData0[w] & puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, Aig_Not(pObj0) );
                    Vec_PtrPush( p->vDivs2UN1, pObj1 );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(puData0[w] & ~puData1[w]) & puDataR[w] )
                    if ( ~(puData0[w] & ~puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, pObj0 );
                    Vec_PtrPush( p->vDivs2UN1, Aig_Not(pObj1) );
                }
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ~(puData0[w] | puData1[w]) & puDataR[w] )
                    if ( ~(puData0[w] | puData1[w]) & puDataR[w] & p->pCareSet[w] ) // care set
                        break;
                if ( w == p->nWords )
                {
                    Vec_PtrPush( p->vDivs2UN0, Aig_Not(pObj0) );
                    Vec_PtrPush( p->vDivs2UN1, Aig_Not(pObj1) );
                }
            }
        }
    }
//    printf( "%d %d  ", Vec_PtrSize(p->vDivs2UP0), Vec_PtrSize(p->vDivs2UN0) );
}

static Dec_Graph_t * Dar_ResubQuit( Dar_Resub_t * p )
{
    Dec_Graph_t * pGraph;
    unsigned * upData;
    int w;
    upData = (unsigned *)p->pRoot->pData;
    for ( w = 0; w < p->nWords; w++ )
//        if ( upData[w] )
        if ( upData[w] & p->pCareSet[w] ) // care set
            break;
    if ( w != p->nWords )
        return NULL;
    // get constant node graph
    if ( p->pRoot->fPhase )
        pGraph = Dec_GraphCreateConst1();
    else
        pGraph = Dec_GraphCreateConst0();
    return pGraph;
}

static Dec_Graph_t * Dar_ResubDivs0( Dar_Resub_t * p )
{
    Aig_Obj_t * pObj;
    unsigned * puData, * puDataR;
    int i, w;
    puDataR = (unsigned *)p->pRoot->pData;
    Vec_PtrForEachEntryStop( Aig_Obj_t *, p->vDivs, pObj, i, p->nSearchDivs )
    {
        puData = (unsigned *)pObj->pData;
        for ( w = 0; w < p->nWords; w++ )
//            if ( puData[w] != puDataR[w] )
            if ( (puData[w] ^ puDataR[w]) & p->pCareSet[w] ) // care set
                break;
        if ( w == p->nWords )
            { Dec_Graph_t * g = Dar_ResubQuit0( p->pRoot, pObj ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
    }
    return NULL;
}

static Dec_Graph_t * Dar_ResubDivs1( Dar_Resub_t * p, int Required )
{
    Aig_Obj_t * pObj0, * pObj1;
    unsigned * puData0, * puData1, * puDataR;
    int i, k, w;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1UP, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
            if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] | ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Aig_IsComplement(pObj0) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] | puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Aig_IsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] | ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] | puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] | puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( w == p->nWords )
            {
                { Dec_Graph_t * g = Dar_ResubQuit1( p->pRoot, pObj0, pObj1, 1 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1UN, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
            if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] & ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Aig_IsComplement(pObj0) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((~puData0[w] & puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else if ( Aig_IsComplement(pObj1) )
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] & ~puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            else
            {
                for ( w = 0; w < p->nWords; w++ )
    //                if ( (puData0[w] & puData1[w]) != puDataR[w] )
                    if ( ((puData0[w] & puData1[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
            }
            if ( w == p->nWords )
            {
                { Dec_Graph_t * g = Dar_ResubQuit1( p->pRoot, pObj0, pObj1, 0 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
            }
        }
    }
    return NULL;
}

static Dec_Graph_t * Dar_ResubDivs12( Dar_Resub_t * p, int Required )
{
    Aig_Obj_t * pObj0, * pObj1, * pObj2, * pObjMax, * pObjMin0 = NULL, * pObjMin1 = NULL;
    unsigned * puData0, * puData1, * puData2, * puDataR;
    int i, k, j, w, LevelMax;
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1UP, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
            Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1UP, pObj2, j, k + 1 )
            {
                puData2 = (unsigned *)Aig_Regular(pObj2)->pData;
                if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | ~puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | ~puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] | puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | ~puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | ~puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | puData1[w] | ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | puData1[w] | puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] | puData1[w] | puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else assert( 0 );
                if ( w == p->nWords )
                {
                    LevelMax = Abc_MaxInt( Aig_Regular(pObj0)->Level, Abc_MaxInt(Aig_Regular(pObj1)->Level, Aig_Regular(pObj2)->Level) );
                    assert( LevelMax <= Required - 1 );

                    pObjMax = NULL;
                    if ( (int)Aig_Regular(pObj0)->Level == LevelMax )
                        pObjMax = pObj0, pObjMin0 = pObj1, pObjMin1 = pObj2;
                    if ( (int)Aig_Regular(pObj1)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj1, pObjMin0 = pObj0, pObjMin1 = pObj2;
                    }
                    if ( (int)Aig_Regular(pObj2)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj2, pObjMin0 = pObj0, pObjMin1 = pObj1;
                    }

                    assert(pObjMin0);
                    assert(pObjMin1);
                    { Dec_Graph_t * g = Dar_ResubQuit21( p->pRoot, pObjMin0, pObjMin1, pObjMax, 1 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
                }
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1UN, pObj1, k, i + 1 )
        {
            puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
            Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs1UN, pObj2, j, k + 1 )
            {
                puData2 = (unsigned *)Aig_Regular(pObj2)->pData;
                if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & ~puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & ~puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((~puData0[w] & puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & ~puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & ~puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & puData1[w] & ~puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( !Aig_IsComplement(pObj0) && !Aig_IsComplement(pObj1) && !Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & puData1[w] & puData2[w]) != puDataR[w] )
                        if ( ((puData0[w] & puData1[w] & puData2[w]) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else assert( 0 );
                if ( w == p->nWords )
                {
                    LevelMax = Abc_MaxInt( Aig_Regular(pObj0)->Level, Abc_MaxInt(Aig_Regular(pObj1)->Level, Aig_Regular(pObj2)->Level) );
                    assert( LevelMax <= Required - 1 );

                    pObjMax = NULL;
                    if ( (int)Aig_Regular(pObj0)->Level == LevelMax )
                        pObjMax = pObj0, pObjMin0 = pObj1, pObjMin1 = pObj2;
                    if ( (int)Aig_Regular(pObj1)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj1, pObjMin0 = pObj0, pObjMin1 = pObj2;
                    }
                    if ( (int)Aig_Regular(pObj2)->Level == LevelMax )
                    {
                        if ( pObjMax ) continue;
                        pObjMax = pObj2, pObjMin0 = pObj0, pObjMin1 = pObj1;
                    }

                    assert(pObjMin0);
                    assert(pObjMin1);
                    { Dec_Graph_t * g = Dar_ResubQuit21( p->pRoot, pObjMin0, pObjMin1, pObjMax, 0 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
                }
            }
        }
    }
    return NULL;
}

static Dec_Graph_t * Dar_ResubDivs2( Dar_Resub_t * p, int Required )
{
    Aig_Obj_t * pObj0, * pObj1, * pObj2;
    unsigned * puData0, * puData1, * puData2, * puDataR;
    int i, k, w;
    if ( p->fIndex ) return Dar_ResubDivs2Indexed(p);
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1UP, pObj0, i )
    {
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs2UP0, pObj1, k )
        {
            pObj2 = (Aig_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, k );

            puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
            puData2 = (unsigned *)Aig_Regular(pObj2)->pData;
            if ( Aig_IsComplement(pObj0) )
            {
                if ( Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] | (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            else
            {
                if ( Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] | (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] | (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            if ( w == p->nWords )
            {
                { Dec_Graph_t * g = Dar_ResubQuit2( p->pRoot, pObj0, pObj1, pObj2, 1 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
            }
        }
    }
    // check negative unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs1UN, pObj0, i )
    {
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs2UN0, pObj1, k )
        {
            pObj2 = (Aig_Obj_t *)Vec_PtrEntry( p->vDivs2UN1, k );

            puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
            puData2 = (unsigned *)Aig_Regular(pObj2)->pData;
            if ( Aig_IsComplement(pObj0) )
            {
                if ( Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((~puData0[w] & (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            else
            {
                if ( Aig_IsComplement(pObj1) && Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] | puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (puData1[w] | puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj1) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (~puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (~puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else if ( Aig_IsComplement(pObj2) )
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & ~puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (puData1[w] & ~puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
                else
                {
                    for ( w = 0; w < p->nWords; w++ )
    //                    if ( (puData0[w] & (puData1[w] & puData2[w])) != puDataR[w] )
                        if ( ((puData0[w] & (puData1[w] & puData2[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                            break;
                }
            }
            if ( w == p->nWords )
            {
                { Dec_Graph_t * g = Dar_ResubQuit2( p->pRoot, pObj0, pObj1, pObj2, 0 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
            }
        }
    }
    return NULL;
}

static Dec_Graph_t * Dar_ResubDivs3( Dar_Resub_t * p, int Required )
{
    Aig_Obj_t * pObj0, * pObj1, * pObj2, * pObj3;
    unsigned * puData0, * puData1, * puData2, * puData3, * puDataR;
    int i, k, w = 0, Flag;
    if ( p->fIndex ) return Dar_ResubDivs3Indexed(p);
    puDataR = (unsigned *)p->pRoot->pData;
    // check positive unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs2UP0, pObj0, i )
    {
        pObj1 = (Aig_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, i );
        puData0 = (unsigned *)Aig_Regular(pObj0)->pData;
        puData1 = (unsigned *)Aig_Regular(pObj1)->pData;
        Flag = (Aig_IsComplement(pObj0) << 3) | (Aig_IsComplement(pObj1) << 2);

        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs2UP0, pObj2, k, i + 1 )
        {
            pObj3 = (Aig_Obj_t *)Vec_PtrEntry( p->vDivs2UP1, k );
            puData2 = (unsigned *)Aig_Regular(pObj2)->pData;
            puData3 = (unsigned *)Aig_Regular(pObj3)->pData;

            Flag = (Flag & 12) | ((int)Aig_IsComplement(pObj2) << 1) | (int)Aig_IsComplement(pObj3);
            assert( Flag < 16 );
            switch( Flag )
            {
            case 0: // 0000
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 1: // 0001
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 2: // 0010
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 3: // 0011
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;

            case 4: // 0100
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 5: // 0101
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 6: // 0110
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 7: // 0111
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] & ~puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] & ~puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;

            case 8: // 1000
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 9: // 1001
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 10: // 1010
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 11: // 1011
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((~puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((~puData0[w] & puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;

            case 12: // 1100
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] ) // care set
                        break;
                break;
            case 13: // 1101
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (puData2[w] & ~puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 14: // 1110
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (~puData2[w] & puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 15: // 1111
                for ( w = 0; w < p->nWords; w++ )
//                    if ( ((puData0[w] | puData1[w]) | (puData2[w] | puData3[w])) != puDataR[w] )
                    if ( (((puData0[w] | puData1[w]) | (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            }
            if ( w == p->nWords )
            {
                { Dec_Graph_t * g = Dar_ResubQuit3( p->pRoot, pObj0, pObj1, pObj2, pObj3, 1 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
            }
        }
    }

/*
    // check negative unate divisors
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs2UN0, pObj0, i )
    {
        pObj1 = Vec_PtrEntry( p->vDivs2UN1, i );
        puData0 = Aig_Regular(pObj0)->pData;
        puData1 = Aig_Regular(pObj1)->pData;
        Flag = (Aig_IsComplement(pObj0) << 3) | (Aig_IsComplement(pObj1) << 2);

        Vec_PtrForEachEntryStart( Aig_Obj_t *, p->vDivs2UN0, pObj2, k, i + 1 )
        {
            pObj3 = Vec_PtrEntry( p->vDivs2UN1, k );
            puData2 = Aig_Regular(pObj2)->pData;
            puData3 = Aig_Regular(pObj3)->pData;

            Flag = (Flag & 12) | (Aig_IsComplement(pObj2) << 1) | Aig_IsComplement(pObj3);
            assert( Flag < 16 );
            switch( Flag )
            {
            case 0: // 0000
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 1: // 0001
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 2: // 0010
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 3: // 0011
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            case 4: // 0100
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 5: // 0101
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 6: // 0110
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 7: // 0111
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] & ~puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            case 8: // 1000
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 9: // 1001
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 10: // 1010
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 11: // 1011
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((~puData0[w] & puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            case 12: // 1100
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 13: // 1101
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (puData2[w] & ~puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 14: // 1110
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (~puData2[w] & puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;
            case 15: // 1111
                for ( w = 0; w < p->nWords; w++ )
                    if ( (((puData0[w] | puData1[w]) & (puData2[w] | puData3[w])) ^ puDataR[w]) & p->pCareSet[w] )
                        break;
                break;

            }
            if ( w == p->nWords )
            {
                { Dec_Graph_t * g = Dar_ResubQuit3( p->pRoot, pObj0, pObj1, pObj2, pObj3, 0 ); if ( Dar_ResubConsider(p, g) ) return g; Dec_GraphFree(g); }
            }
        }
    }
*/
    return NULL;
}

/* The historical pair coverage index retains pool ordinals. For K>6 its
   first 64 coordinates are a rejection filter; every yielded recipe still
   runs the original predicate on ALL truth words before COST acceptance. */
static unsigned Dar_ResubPairWord( Aig_Obj_t * a, Aig_Obj_t * b, int w )
{
    unsigned x = ((unsigned *)Aig_Regular(a)->pData)[w];
    unsigned y = ((unsigned *)Aig_Regular(b)->pData)[w];
    if ( Aig_IsComplement(a) && Aig_IsComplement(b) ) return x | y;
    return (Aig_IsComplement(a) ? ~x : x) & (Aig_IsComplement(b) ? ~y : y);
}

static word Dar_ResubIndexTruth( Dar_Resub_t * p, Aig_Obj_t * obj )
{
    unsigned * data = (unsigned *)Aig_Regular(obj)->pData;
    return (word)data[0] | (p->nWords > 1 ? (word)data[1] << 32 : 0);
}

static word Dar_ResubIndexCare( Dar_Resub_t * p )
{
    return (word)p->pCareSet[0] | (p->nWords > 1 ? (word)p->pCareSet[1] << 32 : 0);
}

static void Dar_ResubIndexBuild( Dar_Resub_t * p, int fUP )
{
    Dar_ResubPairIndex_t * idx = &p->Index[!fUP];
    Vec_Ptr_t * v0 = fUP ? p->vDivs2UP0 : p->vDivs2UN0;
    Vec_Ptr_t * v1 = fUP ? p->vDivs2UP1 : p->vDivs2UN1;
    word root = Dar_ResubIndexTruth(p, p->pRoot), care = Dar_ResubIndexCare(p);
    word active = (fUP ? root : ~root) & care, bits = active;
    int i, b, j, count[64] = {0};
    idx->nPairs = Vec_PtrSize(v0); idx->nWords = (idx->nPairs + 63) / 64; idx->nOrder = 0;
    assert( idx->nPairs == Vec_PtrSize(v1) && idx->nPairs <= DAR_RS_PAIRS_MAX + 3 );
    while ( bits )
    {
        b = Abc_TtFindFirstBit(&bits, 1);
        memset(idx->Cover[b], 0, sizeof(word) * idx->nWords);
        bits &= bits - 1;
    }
    for ( i = 0; i < idx->nPairs; i++ )
    {
        Aig_Obj_t * a = (Aig_Obj_t *)Vec_PtrEntry(v0,i), * bObj = (Aig_Obj_t *)Vec_PtrEntry(v1,i);
        word truth = Dar_ResubPairWord(a,bObj,0);
        if ( p->nWords > 1 ) truth |= (word)Dar_ResubPairWord(a,bObj,1) << 32;
        idx->Truth[i] = truth;
        assert( !((fUP ? truth & ~root : ~truth & root) & care) );
        bits = (fUP ? truth : ~truth) & active;
        while ( bits )
        {
            b = Abc_TtFindFirstBit(&bits, 1);
            idx->Cover[b][i >> 6] |= (word)1 << (i & 63);
            count[b]++; bits &= bits - 1;
        }
    }
    while ( active )
    {
        b = Abc_TtFindFirstBit(&active, 1);
        for ( j = idx->nOrder; j && count[idx->Order[j-1]] > count[b]; j-- ) idx->Order[j] = idx->Order[j-1];
        idx->Order[j] = b; idx->nOrder++; active &= active - 1;
    }
    if ( p->pCex ) Dar_ResubCexBuild(p, fUP);
}

static void Dar_ResubIndexQuery( Dar_Resub_t * p, Dar_ResubPairIndex_t * idx,
    word outer, int fUP, int start, word * matches )
{
    word root = Dar_ResubIndexTruth(p, p->pRoot), needed;
    int i, j, b;
    needed = (fUP ? root & ~outer : ~root & outer) & Dar_ResubIndexCare(p);
    for ( j = 0; j < idx->nWords; j++ )
    {
        matches[j] = ~(word)0;
        if ( j < (start >> 6) ) matches[j] = 0;
        else if ( j == (start >> 6) ) matches[j] <<= start & 63;
    }
    if ( idx->nWords && (idx->nPairs & 63) ) matches[idx->nWords-1] &= ((word)1 << (idx->nPairs & 63)) - 1;
    for ( i = 0; i < idx->nOrder && needed; i++ )
    {
        word any = 0;
        b = idx->Order[i];
        if ( !(needed & ((word)1 << b)) ) continue;
        needed &= ~((word)1 << b);
        for ( j = 0; j < idx->nWords; j++ ) any |= (matches[j] &= idx->Cover[b][j]);
        if ( !any ) break;
    }
}

static Dec_Graph_t * Dar_ResubDivs2Indexed( Dar_Resub_t * p )
{
    int pass, i, j, k, w;
    word matches[DAR_RS_INDEX_WORDS];
    for ( pass = 0; pass < 2; pass++ )
    {
        int fUP = !pass;
        Dar_ResubPairIndex_t * idx = &p->Index[pass];
        Vec_Ptr_t * singles = fUP ? p->vDivs1UP : p->vDivs1UN;
        Vec_Ptr_t * v0 = fUP ? p->vDivs2UP0 : p->vDivs2UN0;
        Vec_Ptr_t * v1 = fUP ? p->vDivs2UP1 : p->vDivs2UN1;
        Aig_Obj_t * obj;
        Vec_PtrForEachEntry( Aig_Obj_t *, singles, obj, i )
        {
            word outer = Dar_ResubIndexTruth(p,obj);
            if ( Aig_IsComplement(obj) ) outer = ~outer;
            Dar_ResubIndexQuery(p, idx, outer, fUP, 0, matches);
            if ( p->pCex ) Dar_ResubCexQuery(p, fUP, obj, NULL, matches);
            for ( j = 0; j < idx->nWords; j++ )
                while ( matches[j] )
                {
                    Aig_Obj_t * a, * b;
                    Dec_Graph_t * graph;
                    k = (j << 6) + Abc_TtFindFirstBit(&matches[j],1); matches[j] &= matches[j] - 1;
                    a = (Aig_Obj_t *)Vec_PtrEntry(v0,k); b = (Aig_Obj_t *)Vec_PtrEntry(v1,k);
                    for ( w = 0; w < p->nWords; w++ )
                    {
                        unsigned x = ((unsigned *)Aig_Regular(obj)->pData)[w];
                        unsigned y = Dar_ResubPairWord(a,b,w), root = ((unsigned *)p->pRoot->pData)[w];
                        if ( Aig_IsComplement(obj) ) x = ~x;
                        if ( ((fUP ? x | y : x & y) ^ root) & p->pCareSet[w] ) break;
                    }
                    if ( p->pCex ) Dar_ResubCexRecord(p, fUP, obj, NULL, k, w, matches);
                    if ( w != p->nWords ) continue;
                    graph = Dar_ResubQuit2(p->pRoot,obj,a,b,fUP);
                    if ( Dar_ResubConsider(p,graph) ) return graph;
                    Dec_GraphFree(graph);
                }
        }
    }
    return NULL;
}

static Dec_Graph_t * Dar_ResubDivs3Indexed( Dar_Resub_t * p )
{
    Dar_ResubPairIndex_t * idx = &p->Index[0];
    word matches[DAR_RS_INDEX_WORDS];
    int i, j, k, w;
    for ( i = 0; i < idx->nPairs; i++ )
    {
        Aig_Obj_t * outer0 = NULL, * outer1 = NULL;
        Dar_ResubIndexQuery(p,idx,idx->Truth[i],1,i+1,matches);
        if ( p->pCex )
        {
            outer0 = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs2UP0,i);
            outer1 = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs2UP1,i);
            Dar_ResubCexQuery(p, 1, outer0, outer1, matches);
        }
        for ( j = 0; j < idx->nWords; j++ )
            while ( matches[j] )
            {
                Aig_Obj_t * a, * b, * c, * d;
                Dec_Graph_t * graph;
                k = (j << 6) + Abc_TtFindFirstBit(&matches[j],1); matches[j] &= matches[j] - 1;
                a = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs2UP0,i); b = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs2UP1,i);
                c = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs2UP0,k); d = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs2UP1,k);
                for ( w = 0; w < p->nWords; w++ )
                    if ( ((Dar_ResubPairWord(a,b,w) | Dar_ResubPairWord(c,d,w)) ^
                        ((unsigned *)p->pRoot->pData)[w]) & p->pCareSet[w] ) break;
                if ( p->pCex ) Dar_ResubCexRecord(p, 1, outer0, outer1, k, w, matches);
                if ( w != p->nWords ) continue;
                graph = Dar_ResubQuit3(p->pRoot,a,b,c,d,1);
                if ( Dar_ResubConsider(p,graph) ) return graph;
                Dec_GraphFree(graph);
            }
    }
    return NULL;
}

/* Native Aig_Man_t support for the historical FIRST 0--3 gate grammar.
   The grammar below is adapted from ABC abcResub.c (Alan Mishchenko).
   No Abc_Ntk_t conversion, sampling proof, or legacy rewrite call occurs. */

static void Dar_ResubCone( Dar_Resub_t * p, Aig_Obj_t * pObj )
{
    if ( Vec_IntGetEntry(p->vSeen, pObj->Id) == p->Epoch ) return;
    Vec_IntSetEntry( p->vSeen, pObj->Id, p->Epoch );
    assert( Aig_ObjIsAnd(pObj) );
    Dar_ResubCone( p, Aig_ObjFanin0(pObj) );
    Dar_ResubCone( p, Aig_ObjFanin1(pObj) );
    Vec_PtrPush( p->vVolume, pObj );
}

static int Dar_ResubCollect( Dar_Resub_t * p )
{
    Aig_Obj_t * pObj, * pFanout;
    int i, k, iFan, Limit, Added = 0;
    if ( p->fCollectReuse ) p->CollectStops = 0;
    p->Epoch++;
    Vec_PtrClear( p->vVolume );
    Vec_PtrClear( p->vTemp );
    Vec_PtrClear( p->vDivs );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vLeaves, pObj, i )
        Vec_IntSetEntry( p->vSeen, pObj->Id, p->Epoch );
    Dar_ResubCone( p, p->pRoot );
    p->nMffc = Aig_NodeMffcLabelCut( p->pAig, p->pRoot, p->vLeaves );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vVolume, pObj, i )
        if ( Aig_ObjIsTravIdCurrent(p->pAig, pObj) )
        {
            Vec_IntSetEntry( p->vMffcMark, pObj->Id, p->Epoch );
            Vec_PtrPush( p->vTemp, pObj );
        }
    assert( Vec_PtrSize(p->vTemp) == p->nMffc );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vLeaves, pObj, i )
    {
        Vec_PtrPush( p->vDivs, pObj );
        Vec_IntSetEntry( p->vReady, pObj->Id, p->Epoch );
    }
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vVolume, pObj, i )
        if ( Vec_IntGetEntry(p->vMffcMark, pObj->Id) != p->Epoch )
        {
            Vec_PtrPush( p->vDivs, pObj );
            Vec_IntSetEntry( p->vReady, pObj->Id, p->Epoch );
        }
    Limit = p->nDivsMax - p->nLeavesMax -
        (Vec_PtrSize(p->vDivs) - p->nLeaves + p->nMffc);
    if ( Limit <= 0 ) return 0;
    /* No required-level query is needed for a divisor-cap rejection. */
    p->Required = p->pPars->fUpdateLevel ? Aig_ObjRequiredLevel(p->pAig, p->pRoot) : ABC_INFINITY;
    /* Complete-fanin TFO extension, original fanout/total divisor caps.
       Only already-ready inputs can enter; root and its dependencies cannot. */
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs, pObj, i )
    {
        if ( pObj->nRefs > 100 )
        { if ( p->fCollectReuse ) p->CollectStops |= 1; continue; }
        Aig_ObjForEachFanout( p->pAig, pObj, pFanout, iFan, k )
        {
            if ( !Aig_ObjIsAnd(pFanout) || pFanout == p->pRoot ) continue;
            if ( Vec_IntGetEntry(p->vReady, pFanout->Id) == p->Epoch ||
                 Vec_IntGetEntry(p->vMffcMark, pFanout->Id) == p->Epoch ) continue;
            if ( Vec_IntGetEntry(p->vReady, Aig_ObjFanin0(pFanout)->Id) != p->Epoch ||
                 Vec_IntGetEntry(p->vReady, Aig_ObjFanin1(pFanout)->Id) != p->Epoch ) continue;
            if ( Aig_Regular(pFanout)->Level > p->Required ) continue;
            Vec_PtrPush( p->vDivs, pFanout );
            Vec_IntSetEntry( p->vReady, pFanout->Id, p->Epoch );
            if ( ++Added == Limit )
            { if ( p->fCollectReuse ) p->CollectStops |= 2; goto ready; }
        }
    }
ready:
    p->nDivs = Vec_PtrSize(p->vDivs);
    Vec_PtrAppend( p->vDivs, p->vTemp );
    p->nSearchDivs = Vec_PtrSize(p->vDivs) - 1;
    assert( Vec_PtrEntryLast(p->vDivs) == p->pRoot );
    assert( Vec_PtrSize(p->vDivs) - p->nLeaves <= p->nDivsMax - p->nLeavesMax );
    return 1;
}

/* Called only after constant/direct-divisor search fails. An untruncated
   collection already closes all root-free ANDs within Required. For a
   whole-MFFC=1 root, every positive-gain recipe must return an existing
   member of that closure (or a constant). Its cut truth is unique unless
   an opaque cut leaf can be rederived through two ready physical fanins.
   Rejecting that alias case makes the earlier direct search complete for
   zero-added results. This certificate does not cover the SDC fallback. */
static int Dar_ResubCollectAbsent( Dar_Resub_t * p )
{
    Aig_Obj_t * obj, * a = Aig_ObjFanin0(p->pRoot), * b = Aig_ObjFanin1(p->pRoot);
    int i, Edges = a == b ? 2 : 1;
    if ( !p->fCollectReuse ) return 0;
    p->CollectQueries++;
    if ( p->pPars->nMinSaved <= 0 ||
         !(Aig_ObjIsCi(a) || (Aig_ObjIsAnd(a) && a->nRefs > Edges)) ||
         !(Aig_ObjIsCi(b) || (Aig_ObjIsAnd(b) && b->nRefs > Edges)) ) return 0;
    p->CollectEligible++;
    if ( Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) )
    { p->CollectUnsupported++; return 0; }
    p->CollectHighFanout += !!(p->CollectStops & 1);
    p->CollectCapped += !!(p->CollectStops & 2);
    if ( p->CollectStops ) return 0;
    assert(p->nMffc == 1 && p->nSearchDivs == p->nDivs);
    Vec_PtrForEachEntry(Aig_Obj_t *,p->vLeaves,obj,i)
        if ( Aig_ObjIsAnd(obj) &&
             Aig_ObjFanin0(obj)->Id < Vec_IntSize(p->vReady) &&
             Aig_ObjFanin1(obj)->Id < Vec_IntSize(p->vReady) &&
             Vec_IntEntry(p->vReady,Aig_ObjFanin0(obj)->Id) == p->Epoch &&
             Vec_IntEntry(p->vReady,Aig_ObjFanin1(obj)->Id) == p->Epoch )
        { p->CollectLeafAlias++; return 0; }
    p->CollectClosed++;
    return 1;
}

/* Independent full-cut truth verification, then protected current-graph
   area and depth.  Referencing every recipe leaf retains shared MFFC inputs;
   only exact positive gain may commit.  No graph mutation during screening. */
static int Dar_ResubConsider( Dar_Resub_t * p, Dec_Graph_t * pGraph )
{
    unsigned Truth[8][32], a, b, result, target;
    Aig_Obj_t * Lits[8], * pObj, * pAnd, * pA, * pB;
    int Levels[8], i, w, Saved, Added = 0;
    Dec_Node_t * pNode;
    assert( pGraph && pGraph->nSize <= 8 && p->nWords <= 32 );
    Dar_ResubMemoRecord(p, pGraph);
    p->Candidates++;
    for ( w = 0; w < p->nWords; w++ )
    {
        if ( Dec_GraphIsConst(pGraph) ) result = ~0u;
        else
        {
            Dec_GraphForEachLeaf( pGraph, pNode, i )
            {
                pObj = Aig_Regular((Aig_Obj_t *)pNode->pFunc);
                assert( pObj != p->pRoot && pObj->pData );
                Truth[i][w] = ((unsigned *)pObj->pData)[w] ^
                    ((pObj->fPhase ^ Aig_IsComplement((Aig_Obj_t *)pNode->pFunc)) ? ~0u : 0);
            }
            Dec_GraphForEachNode( pGraph, pNode, i )
            {
                a = Truth[pNode->eEdge0.Node][w]; b = Truth[pNode->eEdge1.Node][w];
                Truth[i][w] = (pNode->eEdge0.fCompl ? ~a : a) & (pNode->eEdge1.fCompl ? ~b : b);
            }
            result = Truth[pGraph->eRoot.Node][w];
        }
        if ( Dec_GraphIsComplement(pGraph) ) result = ~result;
        target = ((unsigned *)p->pRoot->pData)[w] ^ (p->pRoot->fPhase ? ~0u : 0);
        assert( !((result ^ target) & p->pCareSet[w]) );
    }
    Dec_GraphForEachLeaf( pGraph, pNode, i )
        Aig_Regular((Aig_Obj_t *)pNode->pFunc)->nRefs++;
    Saved = Aig_NodeMffcLabel( p->pAig, p->pRoot, NULL );
    Dec_GraphForEachLeaf( pGraph, pNode, i )
        Aig_Regular((Aig_Obj_t *)pNode->pFunc)->nRefs--;
    Dec_GraphForEachLeaf( pGraph, pNode, i )
    {
        Lits[i] = (Aig_Obj_t *)pNode->pFunc;
        Levels[i] = Aig_Regular(Lits[i])->Level;
    }
    Dec_GraphForEachNode( pGraph, pNode, i )
    {
        pA = Lits[pNode->eEdge0.Node] ? Aig_NotCond( Lits[pNode->eEdge0.Node], pNode->eEdge0.fCompl ) : NULL;
        pB = Lits[pNode->eEdge1.Node] ? Aig_NotCond( Lits[pNode->eEdge1.Node], pNode->eEdge1.fCompl ) : NULL;
        pAnd = pA && pB ? Aig_TableLookupTwo(p->pAig, pA, pB) : NULL;
        if ( Aig_Regular(pAnd) == p->pRoot ) return 0;
        if ( !pAnd || Aig_ObjIsTravIdCurrent(p->pAig, Aig_Regular(pAnd)) ) Added++;
        if ( Saved - Added < p->pPars->nMinSaved ) return 0;
        Lits[i] = pAnd;
        Levels[i] = pAnd ? Aig_Regular(pAnd)->Level :
            1 + Abc_MaxInt(Levels[pNode->eEdge0.Node], Levels[pNode->eEdge1.Node]);
    }
    i = Dec_GraphIsConst(pGraph) ? 0 : pGraph->eRoot.Node;
    if ( !Dec_GraphIsConst(pGraph) && Levels[i] > p->Required ) return 0;
    if ( Saved - Added < p->pPars->nMinSaved ) return 0;
    p->GainVerified = Saved - Added;
    return 1;
}

static Aig_Obj_t * Dar_ResubBuild( Dar_Resub_t * p, Dec_Graph_t * pGraph )
{
    Aig_Obj_t * Lits[8];
    Dec_Node_t * pNode;
    int i;
    if ( Dec_GraphIsConst(pGraph) )
        return Aig_NotCond( Aig_ManConst1(p->pAig), Dec_GraphIsComplement(pGraph) );
    Dec_GraphForEachLeaf( pGraph, pNode, i ) Lits[i] = (Aig_Obj_t *)pNode->pFunc;
    Dec_GraphForEachNode( pGraph, pNode, i )
        Lits[i] = Aig_And( p->pAig, Aig_NotCond(Lits[pNode->eEdge0.Node], pNode->eEdge0.fCompl),
                                    Aig_NotCond(Lits[pNode->eEdge1.Node], pNode->eEdge1.fCompl) );
    return Aig_NotCond( Lits[pGraph->eRoot.Node], Dec_GraphIsComplement(pGraph) );
}

/* Generalized zero-added failure certificate.  All current physical fanout
   ANDs (with their actual edge signs) reachable in <=3 layers are closed.
   Height-three absence covers every <=3-AND FIRST or Stran recipe. Coordinate
   aliases issue no certificate.  Full K-bit truth words, including K8/K10. */
/* Return nonzero on PRESENT or coordinate alias, never issue absence. */
static int Dar_ResubZeroPhysical( Dar_Resub_t * p, Aig_Obj_t * pFanout, int layer )
{
    Aig_Obj_t * a, * b;
    unsigned truth[32], target, old;
    int w, ia, ib, index, hit, alias;
    if ( !Aig_ObjIsAnd(pFanout) || pFanout == p->pRoot ||
         Vec_IntGetEntry(p->vZeroProcessed, pFanout->Id) == p->Epoch ) return 0;
    a = Aig_ObjFanin0(pFanout); b = Aig_ObjFanin1(pFanout);
    if ( Vec_IntGetEntry(p->vZeroStamp, a->Id) != p->Epoch ||
         Vec_IntGetEntry(p->vZeroStamp, b->Id) != p->Epoch ||
         Vec_IntGetEntry(p->vZeroHeight, a->Id) >= layer ||
         Vec_IntGetEntry(p->vZeroHeight, b->Id) >= layer ) return 0;
    ia = Vec_IntEntry(p->vZeroIndex, a->Id); ib = Vec_IntEntry(p->vZeroIndex, b->Id);
    hit = 1;
    for ( w = 0; w < p->nWords; w++ )
    {
        unsigned x = (unsigned)Vec_IntEntry(p->vZeroTruth, ia * p->nWords + w);
        unsigned y = (unsigned)Vec_IntEntry(p->vZeroTruth, ib * p->nWords + w);
        truth[w] = (Aig_ObjFaninC0(pFanout) ? ~x : x) & (Aig_ObjFaninC1(pFanout) ? ~y : y);
        target = ((unsigned *)p->pRoot->pData)[w] ^ (p->pRoot->fPhase ? ~0u : 0);
        if ( (truth[w] ^ target) & p->pCareSet[w] ) hit = 0;
    }
    /* Both polarities are native searchable signals. */
    if ( !hit )
    {
        hit = 1;
        for ( w = 0; w < p->nWords; w++ )
        {
            target = ((unsigned *)p->pRoot->pData)[w] ^ (p->pRoot->fPhase ? ~0u : 0);
            if ( (~truth[w] ^ target) & p->pCareSet[w] ) hit = 0;
        }
    }
    if ( hit ) return 1;

    if ( Vec_IntGetEntry(p->vZeroStamp, pFanout->Id) == p->Epoch )
    {
        index = Vec_IntEntry(p->vZeroIndex, pFanout->Id);
        alias = 0;
        for ( w = 0; w < p->nWords; w++ )
        {
            old = (unsigned)Vec_IntEntry(p->vZeroTruth, index * p->nWords + w);
            if ( (old ^ truth[w]) & p->pCareSet[w] ) alias = 1;
        }
        if ( alias ) return 1;
        Vec_IntSetEntry(p->vZeroProcessed, pFanout->Id, p->Epoch);
        return 0;
    }
    Vec_IntSetEntry(p->vZeroProcessed, pFanout->Id, p->Epoch);
    index = Vec_PtrSize(p->vZeroReady);
    Vec_PtrPush(p->vZeroReady, pFanout);
    Vec_IntSetEntry(p->vZeroStamp, pFanout->Id, p->Epoch);
    Vec_IntSetEntry(p->vZeroIndex, pFanout->Id, index);
    Vec_IntSetEntry(p->vZeroHeight, pFanout->Id, layer);
    for ( w = 0; w < p->nWords; w++ ) Vec_IntPush(p->vZeroTruth, truth[w]);
    return 0;
}

/* Shared query guard and ordered seed setup. CHECK supplies independent
   vectors and its private epoch before entering the same preparation. */
static int Dar_ResubZeroPrepare( Dar_Resub_t * p )
{
    Aig_Obj_t * pObj, * a, * b;
    int i, w;
    if ( !p->fZeroEnabled ) return 0;
    a = Aig_ObjFanin0(p->pRoot); b = Aig_ObjFanin1(p->pRoot);
    if ( (!Aig_ObjIsTerm(a) && a->nRefs <= (a == b ? 2 : 1)) ||
         (!Aig_ObjIsTerm(b) && b->nRefs <= (a == b ? 2 : 1)) ) return 0;
    p->ZeroQueries++;
    Vec_PtrClear(p->vZeroReady); Vec_IntClear(p->vZeroTruth);
    pObj = Aig_ManConst1(p->pAig);
    Vec_PtrPush(p->vZeroReady,pObj);
    Vec_IntSetEntry(p->vZeroStamp,pObj->Id,p->Epoch);
    Vec_IntSetEntry(p->vZeroIndex,pObj->Id,0);
    Vec_IntSetEntry(p->vZeroHeight,pObj->Id,0);
    for ( w = 0; w < p->nWords; w++ ) Vec_IntPush(p->vZeroTruth,~0u);
    for ( i = 0; i < p->nSearchDivs; i++ )
    {
        pObj = (Aig_Obj_t *)Vec_PtrEntry(p->vDivs, i);
        Vec_PtrPush(p->vZeroReady, pObj);
        Vec_IntSetEntry(p->vZeroStamp, pObj->Id, p->Epoch);
        Vec_IntSetEntry(p->vZeroIndex, pObj->Id, Vec_PtrSize(p->vZeroReady)-1);
        Vec_IntSetEntry(p->vZeroHeight, pObj->Id, 0);
        for ( w = 0; w < p->nWords; w++ )
            Vec_IntPush(p->vZeroTruth, ((unsigned *)pObj->pData)[w] ^ (pObj->fPhase ? ~0u : 0));
    }
    return 1;
}

static int Dar_ResubZeroAbsentOld( Dar_Resub_t * p )
{
    Aig_Obj_t * pObj, * pFanout, * a, * b, * found;
    int i, j, k, iFan, layer, begin = 0, end, oldCount, newCount, c0, c1;
    word fanoutBound, pairBound;
    if ( !Dar_ResubZeroPrepare(p) ) return 0;
    for ( layer = 1; layer <= 3 && begin < Vec_PtrSize(p->vZeroReady); layer++ )
    {
        /* Freeze each frontier: height=layer signals enter next layer.
           Count both strategies before choosing, as in the legacy helper. */
        end = Vec_PtrSize(p->vZeroReady); fanoutBound = 0;
        for ( i = begin; i < end; i++ )
            fanoutBound += ((Aig_Obj_t *)Vec_PtrEntry(p->vZeroReady,i))->nRefs;
        oldCount = Abc_MaxInt(begin-1,0); newCount = end-Abc_MaxInt(begin,1);
        pairBound = (word)4 * ((word)oldCount*newCount + (word)newCount*(newCount-1)/2);
        if ( fanoutBound <= pairBound )
        {
            for ( i = begin; i < end; i++ )
            {
                pObj = (Aig_Obj_t *)Vec_PtrEntry(p->vZeroReady,i);
                Aig_ObjForEachFanout(p->pAig,pObj,pFanout,iFan,k)
                {
                    if ( Dar_ResubZeroPhysical(p,pFanout,layer) ) return 0;
                }
            }
        }
        else
        {
            for ( i = Abc_MaxInt(begin,1); i < end; i++ )
            {
                a = (Aig_Obj_t *)Vec_PtrEntry(p->vZeroReady,i);
                for ( j = 1; j < i; j++ )
                {
                    b = (Aig_Obj_t *)Vec_PtrEntry(p->vZeroReady,j);
                    for ( c0 = 0; c0 < 2; c0++ )
                    for ( c1 = 0; c1 < 2; c1++ )
                    {
                        found = Aig_TableLookupTwo(p->pAig,Aig_NotCond(a,c0),Aig_NotCond(b,c1));
                        if ( found && Dar_ResubZeroPhysical(p,Aig_Regular(found),layer) ) return 0;
                    }
                }
            }
        }
        begin = end;
    }
    p->ZeroSkipped++;
    return 1;
}

/* Each nonconstant pair belongs to its larger frozen-frontier index i.
   Enumerate that row by physical fanouts or by all four literal lookups.
   Added nodes are consumed only in the next layer; ZeroPhysical retains
   the original root/height/care/coordinate-alias checks. */
static int Dar_ResubZeroAbsentMixed( Dar_Resub_t * p )
{
    Aig_Obj_t * a, * b, * fanout, * found;
    int i, j, k, iFan, layer, begin = 0, end, c0, c1;
    if ( !Dar_ResubZeroPrepare(p) ) return 0;
    for ( layer = 1; layer <= 3 && begin < Vec_PtrSize(p->vZeroReady); layer++ )
    {
        end = Vec_PtrSize(p->vZeroReady);
        p->ZeroMixedLayers++;
        for ( i = Abc_MaxInt(begin,1); i < end; i++ )
        {
            a = (Aig_Obj_t *)Vec_PtrEntry(p->vZeroReady,i);
            if ( (word)a->nRefs <= (word)4 * (i-1) )
            {
                p->ZeroMixedFanoutRows++;
                Aig_ObjForEachFanout(p->pAig,a,fanout,iFan,k)
                {
                    if ( !Aig_ObjIsAnd(fanout) ) continue;
                    b = Aig_ObjFanin0(fanout) == a ? Aig_ObjFanin1(fanout) : Aig_ObjFanin0(fanout);
                    if ( Vec_IntGetEntry(p->vZeroStamp,b->Id) != p->Epoch ) continue;
                    j = Vec_IntEntry(p->vZeroIndex,b->Id);
                    if ( j <= 0 || j >= i ) continue;
                    if ( Dar_ResubZeroPhysical(p,fanout,layer) ) return 0;
                }
            }
            else
            {
                p->ZeroMixedPairRows++;
                for ( j = 1; j < i; j++ )
                {
                    b = (Aig_Obj_t *)Vec_PtrEntry(p->vZeroReady,j);
                    for ( c0 = 0; c0 < 2; c0++ )
                    for ( c1 = 0; c1 < 2; c1++ )
                    {
                        found = Aig_TableLookupTwo(p->pAig,Aig_NotCond(a,c0),Aig_NotCond(b,c1));
                        if ( found && Dar_ResubZeroPhysical(p,Aig_Regular(found),layer) ) return 0;
                    }
                }
            }
        }
        begin = end;
    }
    p->ZeroSkipped++;
    return 1;
}

static int Dar_ResubZeroAbsent( Dar_Resub_t * p )
{
    int result;
    if ( !p->fZeroMixed ) return Dar_ResubZeroAbsentOld(p);
    result = Dar_ResubZeroAbsentMixed(p);
    if ( p->fZeroMixedCheck )
    {
        Dar_Resub_t old = *p;
        int reference, i, j, w, equal = 1;
        Aig_Obj_t * obj;
        /* Six independent vectors, including processed stamps. The oracle
           reads only the original graph/divisor data, not the mixed closure.
           Its work counters never enter the measured run's counters. */
        old.vZeroReady = p->ZeroCheck.vReady; old.vZeroStamp = p->ZeroCheck.vStamp;
        old.vZeroIndex = p->ZeroCheck.vIndex; old.vZeroHeight = p->ZeroCheck.vHeight;
        old.vZeroProcessed = p->ZeroCheck.vProcessed; old.vZeroTruth = p->ZeroCheck.vTruth;
        /* Private generations cannot inherit stale production stamps, even
           if a test restarts its production epoch. Avoid signed overflow. */
        if ( p->ZeroCheck.Epoch == INT_MAX )
        {
            Vec_IntFill(old.vZeroStamp,Vec_IntSize(old.vZeroStamp),0);
            Vec_IntFill(old.vZeroProcessed,Vec_IntSize(old.vZeroProcessed),0);
            p->ZeroCheck.Epoch = 0;
        }
        old.Epoch = ++p->ZeroCheck.Epoch;
        reference = Dar_ResubZeroAbsentOld(&old);
        p->ZeroMixedAudits++;
        if ( result != reference ) equal = 0;
        if ( result && reference )
        {
            p->ZeroMixedAbsentAudits++;
            if ( Vec_PtrSize(p->vZeroReady) != Vec_PtrSize(old.vZeroReady) ) equal = 0;
            Vec_PtrForEachEntry(Aig_Obj_t *,p->vZeroReady,obj,i)
            {
                if ( Vec_IntGetEntry(old.vZeroStamp,obj->Id) != old.Epoch ) { equal = 0; break; }
                j = Vec_IntEntry(old.vZeroIndex,obj->Id);
                if ( Vec_IntEntry(p->vZeroHeight,obj->Id) != Vec_IntEntry(old.vZeroHeight,obj->Id) ) equal = 0;
                for ( w = 0; w < p->nWords; w++ )
                    if ( Vec_IntEntry(p->vZeroTruth,i*p->nWords+w) !=
                         Vec_IntEntry(old.vZeroTruth,j*p->nWords+w) ) equal = 0;
            }
        }
        if ( !equal )
        {
            fprintf(stderr,"DAR_ZERO_MIXED_FAIL root=%d epoch=%d mixed=%d old=%d\n",
                p->pRoot->Id,p->Epoch,result,reference);
            abort();
        }
    }
    return result;
}


static int Dar_ResubRoot( Dar_Resub_t * p, Aig_Obj_t * pRoot )
{
    Aig_Obj_t * pObj, * pNew;
    Dec_Graph_t * pGraph = NULL;
    Dar_ResubMemo_t * pSavedMemo = NULL;
    int i, Skip, Before, Accepted = 0, CollectNegative = 0, CollectShadow = 0;
    double Start = p->fProfile ? Abc_Clock() : 0, Next;
    p->Roots++;
    p->pRoot = pRoot;
    /* FindCut uses Level to break ties. Repair the root's dependency cone
       before it reads those fields; collection repairs extra TFO divisors.
       The divisor levels then stay exact throughout this mutation-free root
       search, so its hot FIRST loops need no per-read dispatch. */
    Skip = Dar_ResubReuseRoot(p);
    if ( Skip && !p->fCollectReuseCheck )
    {
        if ( p->fProfile ) p->TimeCut += Abc_Clock() - Start;
        return 0;
    }
    Aig_ManFindCut(pRoot, p->vLeaves, p->vVisited, p->nLeavesMax, 100000);
    if ( p->fProfile ) Next = Abc_Clock(), p->TimeCut += Next - Start, Start = Next;
    p->nLeaves = Vec_PtrSize(p->vLeaves);
    i = Dar_ResubCollect(p);
    if ( p->fProfile ) Next = Abc_Clock(), p->TimeCollect += Next - Start, Start = Next;
    if ( !i )
    {
        Dar_ResubReuseCheckRoot(p, NULL);
        return 0;
    }
    Vec_PtrClear( p->vSavedData ); Vec_IntClear( p->vSavedPhase );
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs, pObj, i )
    {
        Vec_PtrPush( p->vSavedData, pObj->pData );
        Vec_IntPush( p->vSavedPhase, pObj->fPhase );
    }
    Dar_ResubSimulate( p->vDivs, p->nLeaves, p->vSims, p->nLeavesMax, p->nWords );
    if ( p->fProfile ) Next = Abc_Clock(), p->TimeSim += Next - Start, Start = Next;
    pGraph = Dar_ResubQuit(p);
    if ( pGraph && !Dar_ResubConsider(p, pGraph) ) { Dec_GraphFree(pGraph); pGraph = NULL; }
    if ( !pGraph ) pGraph = Dar_ResubDivs0(p);
    if ( !pGraph && Dar_ResubCollectAbsent(p) )
    {
        CollectNegative = 1;
        if ( !p->fCollectReuseCheck && !(p->pReuse &&
            p->pReuse->GlobalNegative && p->pReuse->fGlobalCheck) )
        { p->CollectSkipped++; goto searched; }
        /* Either certificate CHECK flag disables stream caches
           at Start. Suspend FIRST explicitly for manually created contexts. */
        CollectShadow = 1;
        pSavedMemo = p->pMemo; p->pMemo = NULL;
    }
    /* An audited global absence must execute the full ordered search;
       letting the older zero gate skip it would weaken the shadow gate. */
    if ( !pGraph && (CollectNegative || !(p->pReuse &&
        p->pReuse->GlobalNegative && p->pReuse->fGlobalCheck)) )
    {
        Skip = Dar_ResubZeroAbsent(p);
        if ( Skip && !CollectNegative ) goto searched;
    }
    if ( !pGraph )
    {
        Skip = Dar_ResubMemoBegin(p, &pGraph);
        if ( Skip ) goto first_done;
    }
    if ( !pGraph )
    {
        Dar_ResubDivsS( p, p->Required );
        pGraph = Dar_ResubDivs1(p, p->Required);
        if ( !pGraph ) pGraph = Dar_ResubDivs12(p, p->Required);
    }
    if ( !pGraph )
    {
        Dar_ResubDivsD(p, p->Required);
        if ( p->fIndex ) { Dar_ResubIndexBuild(p,1); Dar_ResubIndexBuild(p,0); }
        pGraph = Dar_ResubDivs2(p, p->Required);
        if ( !pGraph ) pGraph = Dar_ResubDivs3(p, p->Required);
    }
    Dar_ResubMemoEnd(p, pGraph == NULL);
first_done:
searched:
    if ( CollectShadow )
    {
        if ( pGraph ) { fprintf(stderr,"DAR_COLLECT_REUSE_FAIL root=%d\n",pRoot->Id); abort(); }
        p->CollectShadow++; p->pMemo = pSavedMemo;
    }
    /* Every successful path, including memo replay, already ran Consider.
       The recipe and AIG structure stay unchanged until the commit below. */
    Dar_ResubReuseCheckRoot(p, pGraph);
    if ( p->fProfile ) Next = Abc_Clock(), p->TimeSearch += Next - Start, Start = Next;
    Vec_PtrForEachEntry( Aig_Obj_t *, p->vDivs, pObj, i )
    {
        pObj->pData = Vec_PtrEntry(p->vSavedData, i);
        pObj->fPhase = Vec_IntEntry(p->vSavedPhase, i);
    }
    if ( pGraph )
    {
        Before = Aig_ManNodeNum(p->pAig);
        pNew = Dar_ResubBuild( p, pGraph );
        assert( Aig_ObjPhaseReal(pNew) == pRoot->fPhase );
        Aig_ObjReplace( p->pAig, pRoot, pNew, p->pPars->fUpdateLevel );
        assert( Before - Aig_ManNodeNum(p->pAig) >= p->GainVerified );
        p->Commits++;
        p->Gain += Before - Aig_ManNodeNum(p->pAig);
        Dec_GraphFree(pGraph);
        Accepted = 1;
    }
    if ( p->fProfile ) p->TimeUpdate += Abc_Clock() - Start;
    return Accepted;
}

int Dar_ManResubRewrite( Aig_Man_t * pAig, Dar_RwrPar_t * pPars )
{
    Dar_Resub_t * p;
    Aig_Obj_t * pObj;
    int i, nOld, fDepthOk;
    assert( pPars->nResubCutSize >= 4 && pPars->nResubCutSize <= 10 && pPars->nMinSaved > 0 );
    Aig_ManCleanup(pAig);
    Aig_ManCleanData(pAig);
    Aig_ManFanoutStart(pAig);
    if ( pPars->fUpdateLevel ) Aig_ManStartReverseLevels(pAig, 0);
    p = Dar_ResubStart(pPars->nResubCutSize, 150);
    p->pAig = pAig; p->pPars = pPars;
    Dar_ResubCexStart(p);
    Dar_ResubReuseStart(p);
    p->fProfile = pPars->fVerbose;
    nOld = Aig_ManObjNumMax(pAig);
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( i >= nOld ) break;
        if ( !Aig_ObjIsAnd(pObj) || pObj->nRefs > 1000 ) continue;
        Dar_ResubRoot(p, pObj);
        if ( p->fProfile && p->Roots % 1000 == 0 )
        {
            printf( "DAR_PROFILE roots=%lld commits=%lld zero=%lld/%lld cut=%.3f collect=%.3f sim=%.3f search=%.3f update=%.3f\n",
                p->Roots, p->Commits, p->ZeroSkipped, p->ZeroQueries, p->TimeCut/CLOCKS_PER_SEC,
                p->TimeCollect/CLOCKS_PER_SEC, p->TimeSim/CLOCKS_PER_SEC,
                p->TimeSearch/CLOCKS_PER_SEC, p->TimeUpdate/CLOCKS_PER_SEC );
            fflush(stdout);
        }
    }
    if ( p->fProfile )
        printf( "DAR_RESUB cut=%d roots=%lld commits=%lld gain=%lld candidates=%lld\n",
            pPars->nResubCutSize, p->Roots, p->Commits, p->Gain, p->Candidates );
    /* Enforce the command contract in release builds too. The wrapper discards
       this AIG on failure, before replacing the caller's original network. */
    fDepthOk = !pPars->fUpdateLevel || Aig_ManLevels(pAig) <= pAig->nLevelMax;
    if ( !fDepthOk ) printf("DAR_RESUB constraint error: output depth exceeds input budget.\n");
    Dar_ResubStop(p);
    if ( pPars->fUpdateLevel ) Aig_ManStopReverseLevels(pAig);
    Aig_ManFanoutStop(pAig);
    Aig_ManCleanup(pAig);
    Aig_ManCheckPhase(pAig);
    return Aig_ManCheck(pAig) && fDepthOk;
}

ABC_NAMESPACE_IMPL_END
