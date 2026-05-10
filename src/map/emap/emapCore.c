/**CFile****************************************************************

  FileName    [emapCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Multi-output gate mapper.]

  Synopsis    [Initial mapping core.]

***********************************************************************/

#include "emap.h"

#include "base/abc/abc.h"
#include "map/mio/mio.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define EMAP_LEAF_MAX 6
#define EMAP_CUT_MAX  128
#define EMAP_FLOAT_LARGE ((float)1.0e20)
#define EMAP_DOUBLE_LARGE ((double)1.0e20)
#define EMAP_DELAY_EPS 0.1

typedef struct Emap_Cut_t_ Emap_Cut_t;
typedef struct Emap_Best_t_ Emap_Best_t;
typedef struct Emap_Obj_t_ Emap_Obj_t;
typedef struct Emap_Cell_t_ Emap_Cell_t;
typedef struct Emap_Mog_t_ Emap_Mog_t;
typedef struct Emap_PackEntry_t_ Emap_PackEntry_t;
typedef struct Emap_Tuple_t_ Emap_Tuple_t;
typedef struct Emap_Tuples_t_ Emap_Tuples_t;
typedef struct Emap_Lib_t_ Emap_Lib_t;

struct Emap_Cut_t_
{
    int              nLeaves;
    int              Leaves[EMAP_LEAF_MAX];
    word             Truth;
};

struct Emap_Best_t_
{
    Mio_Gate_t *     pGate;
    int              Cut;
    int              nPins;
    int              PinToLeaf[EMAP_LEAF_MAX];
    int              PinPhase[EMAP_LEAF_MAX];
    int              TwinObj;
    int              TwinPhase;
    int              fInv;
    double           Arr;
    float            Flow;
};

struct Emap_Obj_t_
{
    int              nCuts;
    Emap_Cut_t       Cuts[EMAP_CUT_MAX];
    Emap_Best_t      Best[2];
};

struct Emap_Cell_t_
{
    Mio_Gate_t *     pGate;
    int              nPins;
    int              PinToLeaf[EMAP_LEAF_MAX];
    int              PinPhase[EMAP_LEAF_MAX];
    word             Truth;
    float            Area;
    float            Delay[EMAP_LEAF_MAX];
};

struct Emap_Mog_t_
{
    Mio_Gate_t *     pGate0;
    Mio_Gate_t *     pGate1;
    int              nPins;
    int              PinToLeaf[EMAP_LEAF_MAX];
    int              PinPhase[EMAP_LEAF_MAX];
    word             Truth0;
    word             Truth1;
    float            Area;
    float            Delay0[EMAP_LEAF_MAX];
    float            Delay1[EMAP_LEAF_MAX];
};

struct Emap_PackEntry_t_
{
    int              ObjId;
    int              Phase;
    int              Cut;
    int              nLeaves;
    int              Leaves[EMAP_LEAF_MAX];
    word             Truth;
};

struct Emap_Tuple_t_
{
    int              Obj0;
    int              Phase0;
    int              Cut0;
    int              Obj1;
    int              Phase1;
    int              Cut1;
    int              Mog;
    int              fSwap;
    int              NextHigh;
    int              NextLow;
};

struct Emap_Tuples_t_
{
    Emap_Tuple_t *   pArray;
    int              nSize;
    int              nCap;
    int *            pFirstHigh;
    int *            pFirstLow;
    int              nAreaCalls;
    int              nAreaCandidates;
    int              nAreaRejectTwin;
    int              nAreaRejectRequired;
    int              nAreaRejectFlow;
    int              nAreaAccepts;
    int              nAreaSamples;
    int              nExactLocalCalls;
    int              nExactLocalCandidates;
    int              nExactLocalRejectUnused;
    int              nExactLocalRejectTwin;
    int              nExactLocalRejectShared;
    int              nExactLocalRejectRequired;
    int              nExactLocalRejectArea;
    int              nExactLocalAccepts;
    int              nExactLocalCand2;
    int              nExactLocalCand3;
    int              nExactLocalAccept2;
    int              nExactLocalAccept3;
};

struct Emap_Lib_t_
{
    Emap_Cell_t *    pCells;
    int              nCells;
    int              nCap;
    Emap_Mog_t *     pMogs;
    int              nMogs;
    int              nMogCap;
    Mio_Gate_t *     pGateInv;
    float            InvArea;
    float            InvDelay;
};

static Abc_Obj_t * Emap_ManCreateInv      ( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanin, Mio_Gate_t * pGateInv );
static Abc_Obj_t * Emap_ManBuildPhase_rec ( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew, Emap_Obj_t * pMaps, Vec_Int_t * vCopy, int ObjId, int Phase, Emap_Lib_t * pLib );
static int         Emap_ObjPairHasDirectDanglingRelation( Abc_Ntk_t * pNtk, int ObjId0, int ObjId1 );
static int         Emap_ObjPairHasTfiRelation( Abc_Ntk_t * pNtk, int ObjId0, int ObjId1 );
static int         Emap_ObjPairHasMffcDanglingRelation( Abc_Ntk_t * pNtk, int ObjId0, int ObjId1, Emap_Cut_t * pCut, char * pLeafMarks, int * pDecs, Vec_Int_t * vTouched );
static double      Emap_MogArrival        ( Emap_Obj_t * pMaps, Emap_Cut_t * pCut, Emap_Mog_t * pMog, int fSwap );
static void        Emap_MogApply          ( Emap_Obj_t * pMaps, Emap_PackEntry_t * pEntry0, Emap_PackEntry_t * pEntry1, Emap_Mog_t * pMog, int fSwap );
static void        Emap_MogSetOppositePhase( Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int ObjId, int Phase, float Flow );
static int         Emap_NodeMatchMogExactLocal( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Emap_Tuples_t * pTuples, int * pRefs, double * pRequired, Vec_Int_t * vTouched, int ObjId );
static float       Emap_ManComputeActualMappedStats( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Mio_Library_t * pMio, double * pDelay );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static inline word Emap_TruthMask( int nVars )
{
    return nVars == 6 ? ~(word)0 : (((word)1) << (1 << nVars)) - 1;
}

static inline word Emap_TruthVar( int Var, int nVars )
{
    word t = 0;
    int m;
    assert( Var < nVars );
    for ( m = 0; m < (1 << nVars); m++ )
        if ( (m >> Var) & 1 )
            t |= ((word)1) << m;
    return t;
}

static word Emap_TruthStretch( word Truth, int * pLeaves, int nLeaves, int * pLeavesNew, int nLeavesNew )
{
    word Res = 0;
    int m, i, k, mOld;
    assert( nLeaves <= nLeavesNew );
    for ( m = 0; m < (1 << nLeavesNew); m++ )
    {
        mOld = 0;
        for ( i = 0; i < nLeaves; i++ )
        {
            for ( k = 0; k < nLeavesNew; k++ )
                if ( pLeaves[i] == pLeavesNew[k] )
                    break;
            assert( k < nLeavesNew );
            if ( (m >> k) & 1 )
                mOld |= 1 << i;
        }
        if ( (Truth >> mOld) & 1 )
            Res |= ((word)1) << m;
    }
    return Res;
}

static word Emap_TruthPermutePhase( word Truth, int nVars, int * pPinToLeaf, int * pPinPhase )
{
    word Res = 0;
    int m, i, mOld, Bit;
    for ( m = 0; m < (1 << nVars); m++ )
    {
        mOld = 0;
        for ( i = 0; i < nVars; i++ )
        {
            Bit = (m >> pPinToLeaf[i]) & 1;
            if ( pPinPhase[i] )
                Bit ^= 1;
            if ( Bit )
                mOld |= 1 << i;
        }
        if ( (Truth >> mOld) & 1 )
            Res |= ((word)1) << m;
    }
    return Res;
}

static word Emap_TruthShrink6( word Truth, int nVars )
{
    word Res = 0;
    int m;
    assert( nVars <= 6 );
    for ( m = 0; m < (1 << nVars); m++ )
        if ( (Truth >> m) & 1 )
            Res |= ((word)1) << m;
    return Res;
}

/**Function*************************************************************

  Synopsis    [Creates a mapped inverter node.]

***********************************************************************/
static Abc_Obj_t * Emap_ManCreateInv( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanin, Mio_Gate_t * pGateInv )
{
    Abc_Obj_t * pObj;
    assert( pGateInv != NULL );
    pObj = Abc_NtkCreateNode( pNtkNew );
    pObj->pData = pGateInv;
    Abc_ObjAddFanin( pObj, pFanin );
    return pObj;
}

static void Emap_BestClean( Emap_Best_t * pBest )
{
    memset( pBest, 0, sizeof(Emap_Best_t) );
    pBest->Cut = -1;
    pBest->TwinObj = -1;
    pBest->TwinPhase = -1;
    pBest->Arr = EMAP_DOUBLE_LARGE;
    pBest->Flow = EMAP_FLOAT_LARGE;
}

static int Emap_BestIsBetterDelay( double ArrNew, float FlowNew, Emap_Best_t * pBest )
{
    if ( ArrNew < pBest->Arr - 0.0001 )
        return 1;
    if ( ArrNew > pBest->Arr + 0.0001 )
        return 0;
    return FlowNew < pBest->Flow - 0.0001;
}

static int Emap_BestIsBetterArea( double ArrNew, float FlowNew, Emap_Best_t * pBest )
{
    if ( FlowNew < pBest->Flow - 0.0001 )
        return 1;
    if ( FlowNew > pBest->Flow + 0.0001 )
        return 0;
    return ArrNew < pBest->Arr - 0.0001;
}

static int Emap_CutEqual( Emap_Cut_t * pCut, int * pLeaves, int nLeaves, word Truth )
{
    int i;
    if ( pCut->nLeaves != nLeaves || pCut->Truth != Truth )
        return 0;
    for ( i = 0; i < nLeaves; i++ )
        if ( pCut->Leaves[i] != pLeaves[i] )
            return 0;
    return 1;
}

static int Emap_CutInsert( Emap_Obj_t * pMap, int * pLeaves, int nLeaves, word Truth )
{
    Emap_Cut_t * pCut;
    int i, iWorst = -1, nWorst = -1;
    Truth &= Emap_TruthMask( nLeaves );
    for ( i = 0; i < pMap->nCuts; i++ )
        if ( Emap_CutEqual( &pMap->Cuts[i], pLeaves, nLeaves, Truth ) )
            return 0;
    if ( pMap->nCuts == EMAP_CUT_MAX )
    {
        for ( i = 0; i < pMap->nCuts; i++ )
            if ( pMap->Cuts[i].nLeaves > nWorst )
                nWorst = pMap->Cuts[i].nLeaves, iWorst = i;
        if ( nLeaves >= nWorst )
            return 0;
        pCut = &pMap->Cuts[iWorst];
    }
    else
        pCut = &pMap->Cuts[pMap->nCuts++];
    pCut->nLeaves = nLeaves;
    pCut->Truth = Truth;
    for ( i = 0; i < nLeaves; i++ )
        pCut->Leaves[i] = pLeaves[i];
    return 1;
}

static int Emap_CutMergeLeaves( Emap_Cut_t * pCut0, Emap_Cut_t * pCut1, int * pLeaves )
{
    int i = 0, k = 0, nLeaves = 0;
    while ( i < pCut0->nLeaves || k < pCut1->nLeaves )
    {
        int Leaf;
        if ( k == pCut1->nLeaves || (i < pCut0->nLeaves && pCut0->Leaves[i] < pCut1->Leaves[k]) )
            Leaf = pCut0->Leaves[i++];
        else if ( i == pCut0->nLeaves || pCut1->Leaves[k] < pCut0->Leaves[i] )
            Leaf = pCut1->Leaves[k++];
        else
        {
            Leaf = pCut0->Leaves[i];
            i++;
            k++;
        }
        if ( nLeaves == EMAP_LEAF_MAX )
            return -1;
        pLeaves[nLeaves++] = Leaf;
    }
    return nLeaves;
}

static void Emap_NodeAddUnitCut( Emap_Obj_t * pMap, int ObjId )
{
    int Leaves[1];
    Leaves[0] = ObjId;
    Emap_CutInsert( pMap, Leaves, 1, Emap_TruthVar( 0, 1 ) );
}

static void Emap_NodeAddConstCut( Emap_Obj_t * pMap )
{
    Emap_CutInsert( pMap, NULL, 0, 1 );
}

static void Emap_LibAddCell( Emap_Lib_t * p, Mio_Gate_t * pGate, int * pPinToLeaf, int * pPinPhase, word Truth )
{
    Emap_Cell_t * pCell;
    Mio_Pin_t * pPin;
    int i;
    if ( p->nCells == p->nCap )
    {
        p->nCap = p->nCap ? 2 * p->nCap : 1024;
        p->pCells = ABC_REALLOC( Emap_Cell_t, p->pCells, p->nCap );
    }
    pCell = &p->pCells[p->nCells++];
    memset( pCell, 0, sizeof(Emap_Cell_t) );
    pCell->pGate = pGate;
    pCell->nPins = Mio_GateReadPinNum( pGate );
    pCell->Truth = Truth;
    pCell->Area = (float)Mio_GateReadArea( pGate );
    for ( i = 0; i < pCell->nPins; i++ )
    {
        pCell->PinToLeaf[i] = pPinToLeaf[i];
        pCell->PinPhase[i] = pPinPhase[i];
    }
    i = 0;
    Mio_GateForEachPin( pGate, pPin )
        pCell->Delay[i++] = (float)Mio_PinReadDelayBlockMax( pPin );
}

static void Emap_LibAddMog( Emap_Lib_t * p, Mio_Gate_t * pGate0, Mio_Gate_t * pGate1, int * pPinToLeaf, int * pPinPhase, word Truth0, word Truth1 )
{
    Emap_Mog_t * pMog;
    Mio_Pin_t * pPin;
    int i;
    if ( p->nMogs == p->nMogCap )
    {
        p->nMogCap = p->nMogCap ? 2 * p->nMogCap : 128;
        p->pMogs = ABC_REALLOC( Emap_Mog_t, p->pMogs, p->nMogCap );
    }
    pMog = &p->pMogs[p->nMogs++];
    memset( pMog, 0, sizeof(Emap_Mog_t) );
    pMog->pGate0 = pGate0;
    pMog->pGate1 = pGate1;
    pMog->nPins = Mio_GateReadPinNum( pGate0 );
    pMog->Truth0 = Truth0;
    pMog->Truth1 = Truth1;
    pMog->Area = (float)Mio_GateReadArea( pGate0 );
    for ( i = 0; i < pMog->nPins; i++ )
    {
        pMog->PinToLeaf[i] = pPinToLeaf[i];
        pMog->PinPhase[i] = pPinPhase[i];
    }
    i = 0;
    Mio_GateForEachPin( pGate0, pPin )
        pMog->Delay0[i++] = (float)Mio_PinReadDelayBlockMax( pPin );
    i = 0;
    Mio_GateForEachPin( pGate1, pPin )
        pMog->Delay1[i++] = (float)Mio_PinReadDelayBlockMax( pPin );
}

static void Emap_LibPermute_rec( Emap_Lib_t * p, Mio_Gate_t * pGate, int nPins, int iPin, int * pPinToLeaf, int * pUsed )
{
    int i;
    if ( iPin == nPins )
    {
        word Truth = Emap_TruthShrink6( Mio_GateReadTruth(pGate), nPins );
        int PinPhase[EMAP_LEAF_MAX];
        int Phase;
        for ( Phase = 0; Phase < (1 << nPins); Phase++ )
        {
            for ( i = 0; i < nPins; i++ )
                PinPhase[i] = (Phase >> i) & 1;
            Emap_LibAddCell( p, pGate, pPinToLeaf, PinPhase, Emap_TruthPermutePhase( Truth, nPins, pPinToLeaf, PinPhase ) );
        }
        return;
    }
    for ( i = 0; i < nPins; i++ )
    {
        if ( pUsed[i] )
            continue;
        pUsed[i] = 1;
        pPinToLeaf[iPin] = i;
        Emap_LibPermute_rec( p, pGate, nPins, iPin + 1, pPinToLeaf, pUsed );
        pUsed[i] = 0;
    }
}

static void Emap_LibMogPermute_rec( Emap_Lib_t * p, Mio_Gate_t * pGate0, Mio_Gate_t * pGate1, int nPins, int iPin, int * pPinToLeaf, int * pUsed )
{
    int i;
    if ( iPin == nPins )
    {
        word Truth0 = Emap_TruthShrink6( Mio_GateReadTruth(pGate0), nPins );
        word Truth1 = Emap_TruthShrink6( Mio_GateReadTruth(pGate1), nPins );
        int PinPhase[EMAP_LEAF_MAX];
        int Phase;
        for ( Phase = 0; Phase < (1 << nPins); Phase++ )
        {
            for ( i = 0; i < nPins; i++ )
                PinPhase[i] = (Phase >> i) & 1;
            Emap_LibAddMog( p, pGate0, pGate1, pPinToLeaf, PinPhase, Emap_TruthPermutePhase( Truth0, nPins, pPinToLeaf, PinPhase ), Emap_TruthPermutePhase( Truth1, nPins, pPinToLeaf, PinPhase ) );
        }
        return;
    }
    for ( i = 0; i < nPins; i++ )
    {
        if ( pUsed[i] )
            continue;
        pUsed[i] = 1;
        pPinToLeaf[iPin] = i;
        Emap_LibMogPermute_rec( p, pGate0, pGate1, nPins, iPin + 1, pPinToLeaf, pUsed );
        pUsed[i] = 0;
    }
}

static void Emap_LibFree( Emap_Lib_t * p )
{
    ABC_FREE( p->pCells );
    ABC_FREE( p->pMogs );
}

static int Emap_CellCompare( void const * p0, void const * p1 )
{
    Emap_Cell_t const * pCell0 = (Emap_Cell_t const *)p0;
    Emap_Cell_t const * pCell1 = (Emap_Cell_t const *)p1;
    if ( pCell0->nPins != pCell1->nPins )
        return pCell0->nPins - pCell1->nPins;
    if ( pCell0->Truth < pCell1->Truth )
        return -1;
    if ( pCell0->Truth > pCell1->Truth )
        return 1;
    return 0;
}

static int Emap_LibFindFirst( Emap_Lib_t * p, int nPins, word Truth )
{
    int Beg = 0, End = p->nCells;
    while ( Beg < End )
    {
        int Mid = (Beg + End) >> 1;
        Emap_Cell_t * pCell = &p->pCells[Mid];
        if ( pCell->nPins < nPins || (pCell->nPins == nPins && pCell->Truth < Truth) )
            Beg = Mid + 1;
        else
            End = Mid;
    }
    if ( Beg == p->nCells || p->pCells[Beg].nPins != nPins || p->pCells[Beg].Truth != Truth )
        return -1;
    return Beg;
}

static int Emap_LibPrepare( Emap_Lib_t * p, Mio_Library_t * pMio )
{
    Mio_Gate_t * pGate;
    int PinToLeaf[EMAP_LEAF_MAX], Used[EMAP_LEAF_MAX];
    memset( p, 0, sizeof(Emap_Lib_t) );
    p->pGateInv = Mio_LibraryReadInv( pMio );
    if ( p->pGateInv == NULL )
    {
        printf( "Cannot find inverter gate in the current GENLIB library.\n" );
        return 0;
    }
    p->InvArea = (float)Mio_GateReadArea( p->pGateInv );
    p->InvDelay = Mio_GateReadPinNum(p->pGateInv) ? Mio_GateReadPinDelay( p->pGateInv, 0 ) : 0;
    Mio_LibraryForEachGate( pMio, pGate )
    {
        int nPins = Mio_GateReadPinNum( pGate );
        Mio_Gate_t * pTwin = Mio_GateReadTwin(pGate);
        if ( nPins < 2 || nPins > EMAP_LEAF_MAX )
            continue;
        if ( pTwin != NULL )
        {
            if ( pGate > pTwin || Mio_GateReadPinNum(pTwin) != nPins )
                continue;
            memset( Used, 0, sizeof(Used) );
            Emap_LibMogPermute_rec( p, pGate, pTwin, nPins, 0, PinToLeaf, Used );
            continue;
        }
        memset( Used, 0, sizeof(Used) );
        Emap_LibPermute_rec( p, pGate, nPins, 0, PinToLeaf, Used );
    }
    qsort( p->pCells, p->nCells, sizeof(Emap_Cell_t), Emap_CellCompare );
    return 1;
}

static int Emap_NodeMergeCuts( Emap_Obj_t * pMaps, Abc_Obj_t * pObj )
{
    Emap_Obj_t * pMap = &pMaps[Abc_ObjId(pObj)];
    Emap_Obj_t * pMap0 = &pMaps[Abc_ObjFaninId0(pObj)];
    Emap_Obj_t * pMap1 = &pMaps[Abc_ObjFaninId1(pObj)];
    Emap_Cut_t * pCut0, * pCut1;
    int Leaves[EMAP_LEAF_MAX];
    int i, k, nLeaves;
    word Truth0, Truth1, Mask;
    Emap_NodeAddUnitCut( pMap, Abc_ObjId(pObj) );
    for ( i = 0; i < pMap0->nCuts; i++ )
    for ( k = 0; k < pMap1->nCuts; k++ )
    {
        pCut0 = &pMap0->Cuts[i];
        pCut1 = &pMap1->Cuts[k];
        nLeaves = Emap_CutMergeLeaves( pCut0, pCut1, Leaves );
        if ( nLeaves < 0 )
            continue;
        Mask = Emap_TruthMask( nLeaves );
        Truth0 = Emap_TruthStretch( pCut0->Truth, pCut0->Leaves, pCut0->nLeaves, Leaves, nLeaves );
        Truth1 = Emap_TruthStretch( pCut1->Truth, pCut1->Leaves, pCut1->nLeaves, Leaves, nLeaves );
        if ( Abc_ObjFaninC0(pObj) ) Truth0 ^= Mask;
        if ( Abc_ObjFaninC1(pObj) ) Truth1 ^= Mask;
        Emap_CutInsert( pMap, Leaves, nLeaves, Truth0 & Truth1 );
    }
    return pMap->nCuts > 1;
}

static int Emap_BestIsBetterMode( double ArrNew, float FlowNew, Emap_Best_t * pBest, int fAreaMode )
{
    return fAreaMode ? Emap_BestIsBetterArea( ArrNew, FlowNew, pBest ) : Emap_BestIsBetterDelay( ArrNew, FlowNew, pBest );
}

static void Emap_NodeMatch( Emap_Obj_t * pMaps, Emap_Obj_t * pMap, Emap_Lib_t * pLib, Abc_Obj_t * pObj, double * pRequired, int * pRefs )
{
    Emap_Cut_t * pCut;
    Emap_Cell_t * pCell;
    word Mask;
    int i, k, c, fCompl, fAreaMode = (pRequired != NULL);
    Emap_BestClean( &pMap->Best[0] );
    Emap_BestClean( &pMap->Best[1] );
    for ( i = 0; i < pMap->nCuts; i++ )
    {
        pCut = &pMap->Cuts[i];
        if ( pCut->nLeaves < 2 )
            continue;
        Mask = Emap_TruthMask( pCut->nLeaves );
        for ( fCompl = 0; fCompl < 2; fCompl++ )
        {
            c = Emap_LibFindFirst( pLib, pCut->nLeaves, fCompl ? (pCut->Truth ^ Mask) : pCut->Truth );
            if ( c < 0 )
                continue;
            for ( ; c < pLib->nCells; c++ )
            {
                double Arr = 0;
                double Required = fAreaMode ? pRequired[2 * Abc_ObjId(pObj) + fCompl] : EMAP_DOUBLE_LARGE;
                float Flow;
                pCell = &pLib->pCells[c];
                if ( pCell->nPins != pCut->nLeaves || pCell->Truth != (fCompl ? (pCut->Truth ^ Mask) : pCut->Truth) )
                    break;
                Flow = pCell->Area;
                for ( k = 0; k < pCut->nLeaves; k++ )
                {
                    Abc_Obj_t * pLeaf = Abc_NtkObj( pObj->pNtk, pCut->Leaves[pCell->PinToLeaf[k]] );
                    Emap_Best_t * pLeafBest = &pMaps[Abc_ObjId(pLeaf)].Best[pCell->PinPhase[k]];
                    int LeafPhase = pCell->PinPhase[k];
                    float Div = (float)Abc_MaxInt( 1, pRefs ? pRefs[2 * Abc_ObjId(pLeaf) + LeafPhase] : Abc_ObjFanoutNum(pLeaf) );
                    Arr = Abc_MaxDouble( Arr, pLeafBest->Arr + pCell->Delay[k] );
                    Flow += pLeafBest->Flow / Div;
                }
                if ( Arr > Required + 0.001 )
                    continue;
                if ( Emap_BestIsBetterMode( Arr, Flow, &pMap->Best[fCompl], fAreaMode ) )
                {
                    pMap->Best[fCompl].pGate = pCell->pGate;
                    pMap->Best[fCompl].Cut = i;
                    pMap->Best[fCompl].nPins = pCell->nPins;
                    pMap->Best[fCompl].Arr = Arr;
                    pMap->Best[fCompl].Flow = Flow;
                    pMap->Best[fCompl].fInv = 0;
                    for ( k = 0; k < pCell->nPins; k++ )
                    {
                        pMap->Best[fCompl].PinToLeaf[k] = pCell->PinToLeaf[k];
                        pMap->Best[fCompl].PinPhase[k] = pCell->PinPhase[k];
                    }
                }
            }
        }
    }
    for ( fCompl = 0; fCompl < 2; fCompl++ )
        if ( pMap->Best[!fCompl].pGate && (!fAreaMode || pMap->Best[!fCompl].Arr + pLib->InvDelay <= pRequired[2 * Abc_ObjId(pObj) + fCompl] + 0.001) && Emap_BestIsBetterMode( pMap->Best[!fCompl].Arr + pLib->InvDelay, pMap->Best[!fCompl].Flow + pLib->InvArea, &pMap->Best[fCompl], fAreaMode ) )
        {
            pMap->Best[fCompl] = pMap->Best[!fCompl];
            pMap->Best[fCompl].fInv = 1;
            pMap->Best[fCompl].Arr += pLib->InvDelay;
            pMap->Best[fCompl].Flow += pLib->InvArea;
        }
}

static void Emap_NodeDropPhaseArea( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired, int * pRefs, int ObjId )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t Best0 = pMap->Best[0];
    Emap_Best_t Best1 = pMap->Best[1];
    float Est0 = (float)Abc_MaxInt( 1, pRefs ? pRefs[2 * ObjId + 0] : Abc_ObjFanoutNum(Abc_NtkObj(pNtk, ObjId)) );
    float Est1 = (float)Abc_MaxInt( 1, pRefs ? pRefs[2 * ObjId + 1] : Abc_ObjFanoutNum(Abc_NtkObj(pNtk, ObjId)) );
    int fUse0, fUse1;
    if ( Best0.pGate == NULL || Best1.pGate == NULL || Best0.fInv || Best1.fInv || Best0.TwinObj >= 0 || Best1.TwinObj >= 0 )
        return;
    fUse0 = Best0.Arr + pLib->InvDelay <= pRequired[2 * ObjId + 1] + 0.001;
    fUse1 = Best1.Arr + pLib->InvDelay <= pRequired[2 * ObjId + 0] + 0.001;
    if ( !fUse0 && !fUse1 )
        return;
    if ( fUse0 && fUse1 )
    {
        float Cost0 = Best0.Flow / Est0 + pLib->InvArea;
        float Cost1 = Best1.Flow / Est1 + pLib->InvArea;
        if ( Cost0 < Cost1 - 0.001 )
            fUse1 = 0;
        else if ( Cost1 < Cost0 - 0.001 )
            fUse0 = 0;
        else if ( Best0.Arr + pLib->InvDelay <= Best1.Arr + pLib->InvDelay )
            fUse1 = 0;
        else
            fUse0 = 0;
    }
    if ( fUse0 )
    {
        pMap->Best[1] = Best0;
        pMap->Best[1].fInv = 1;
        pMap->Best[1].TwinObj = -1;
        pMap->Best[1].TwinPhase = -1;
        pMap->Best[1].Arr = Best0.Arr + pLib->InvDelay;
        pMap->Best[1].Flow = Best0.Flow + pLib->InvArea;
    }
    else
    {
        pMap->Best[0] = Best1;
        pMap->Best[0].fInv = 1;
        pMap->Best[0].TwinObj = -1;
        pMap->Best[0].TwinPhase = -1;
        pMap->Best[0].Arr = Best1.Arr + pLib->InvDelay;
        pMap->Best[0].Flow = Best1.Flow + pLib->InvArea;
    }
}

static void Emap_RequiredUpdate( double * pRequired, int ObjId, int Phase, double Required )
{
    if ( Required < pRequired[2 * ObjId + Phase] )
        pRequired[2 * ObjId + Phase] = Required;
}

static void Emap_RequiredPropagatePhase( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired, int ObjId, int Phase )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t * pBest = &pMap->Best[Phase];
    Emap_Cut_t * pCut;
    double Required = pRequired[2 * ObjId + Phase];
    int i;
    if ( Required >= EMAP_DOUBLE_LARGE / 2 )
        return;
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return;
    if ( pBest->fInv )
    {
        Emap_RequiredUpdate( pRequired, ObjId, !Phase, Required - pLib->InvDelay );
        return;
    }
    if ( pBest->pGate == NULL )
        return;
    pCut = &pMap->Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Emap_RequiredUpdate( pRequired, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i], Required - Mio_GateReadPinDelay(pBest->pGate, i) );
}

static void Emap_RequiredPropagateUsedObj( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired, int * pRefs, int ObjId )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t * pBest;
    Emap_Cut_t * pCut;
    int Phase, i;
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return;
    for ( Phase = 0; Phase < 2; Phase++ )
    {
        pBest = &pMap->Best[Phase];
        if ( pRefs[2 * ObjId + Phase] == 0 || !pBest->fInv || pRequired[2 * ObjId + Phase] >= EMAP_DOUBLE_LARGE / 2 )
            continue;
        Emap_RequiredUpdate( pRequired, ObjId, !Phase, pRequired[2 * ObjId + Phase] - pLib->InvDelay );
    }
    for ( Phase = 0; Phase < 2; Phase++ )
    {
        pBest = &pMap->Best[Phase];
        if ( pBest->pGate == NULL || pBest->fInv || pRequired[2 * ObjId + Phase] >= EMAP_DOUBLE_LARGE / 2 )
            continue;
        pCut = &pMap->Cuts[pBest->Cut];
        for ( i = 0; i < pBest->nPins; i++ )
            Emap_RequiredUpdate( pRequired, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i], pRequired[2 * ObjId + Phase] - Mio_GateReadPinDelay(pBest->pGate, i) );
    }
}

static double Emap_ManComputeRequired( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired )
{
    Abc_Obj_t * pObj;
    double DelayTarget = 0;
    int i, Phase;
    for ( i = 0; i < 2 * Abc_NtkObjNumMax(pNtk); i++ )
        pRequired[i] = EMAP_DOUBLE_LARGE;
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        Phase = Abc_ObjFaninC0(pObj);
        DelayTarget = Abc_MaxDouble( DelayTarget, pMaps[Abc_ObjFaninId0(pObj)].Best[Phase].Arr );
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
        Emap_RequiredUpdate( pRequired, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj), DelayTarget );
    Abc_NtkForEachNodeReverse( pNtk, pObj, i )
    {
        if ( !Abc_AigNodeIsAnd(pObj) )
            continue;
        Emap_RequiredPropagatePhase( pNtk, pMaps, pLib, pRequired, Abc_ObjId(pObj), 0 );
        Emap_RequiredPropagatePhase( pNtk, pMaps, pLib, pRequired, Abc_ObjId(pObj), 1 );
    }
    return DelayTarget;
}

static void Emap_ManComputeRequiredTarget( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired, int * pRefs, double DelayTarget )
{
    Abc_Obj_t * pObj;
    int i;
    for ( i = 0; i < 2 * Abc_NtkObjNumMax(pNtk); i++ )
        pRequired[i] = EMAP_DOUBLE_LARGE;
    Abc_NtkForEachPo( pNtk, pObj, i )
        Emap_RequiredUpdate( pRequired, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj), DelayTarget );
    Abc_NtkForEachNodeReverse( pNtk, pObj, i )
    {
        if ( !Abc_AigNodeIsAnd(pObj) )
            continue;
        Emap_RequiredPropagateUsedObj( pNtk, pMaps, pLib, pRequired, pRefs, Abc_ObjId(pObj) );
    }
}

static void Emap_RefPhase_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t * pBest = &pMap->Best[Phase];
    Emap_Cut_t * pCut;
    int i;
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return;
    if ( pRefs[2 * ObjId + Phase]++ > 0 )
        return;
    if ( pBest->fInv )
    {
        Emap_RefPhase_rec( pNtk, pMaps, pLib, pRefs, ObjId, !Phase );
        return;
    }
    if ( pBest->pGate == NULL )
        return;
    pCut = &pMap->Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Emap_RefPhase_rec( pNtk, pMaps, pLib, pRefs, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
}

static void Emap_ManComputeRefs( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs )
{
    Abc_Obj_t * pObj;
    int i;
    memset( pRefs, 0, sizeof(int) * 2 * Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Emap_RefPhase_rec( pNtk, pMaps, pLib, pRefs, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj) );
}

static float Emap_ManComputeArea( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs )
{
    Abc_Obj_t * pObj;
    float Area = 0;
    int i, f;
    Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emap_Best_t * pBest = &pMaps[Abc_ObjId(pObj)].Best[f];
            if ( pRefs[2 * Abc_ObjId(pObj) + f] == 0 )
                continue;
            if ( pBest->TwinObj >= 0 && 2 * Abc_ObjId(pObj) + f > 2 * pBest->TwinObj + pBest->TwinPhase )
                continue;
            Area += pBest->fInv ? pLib->InvArea : (float)Mio_GateReadArea(pBest->pGate);
        }
    }
    return Area;
}

static void Emap_ManSaveBests( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Best_t * pSave )
{
    int i;
    for ( i = 0; i < Abc_NtkObjNumMax(pNtk); i++ )
    {
        pSave[2 * i + 0] = pMaps[i].Best[0];
        pSave[2 * i + 1] = pMaps[i].Best[1];
    }
}

static void Emap_ManRestoreBests( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Best_t * pSave )
{
    int i;
    for ( i = 0; i < Abc_NtkObjNumMax(pNtk); i++ )
    {
        pMaps[i].Best[0] = pSave[2 * i + 0];
        pMaps[i].Best[1] = pSave[2 * i + 1];
    }
}

static float Emap_PhaseRefVisit_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase );
static float Emap_PhaseRef_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase );
static float Emap_PhaseDeref_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase );

static float Emap_CutRefLeaves_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase )
{
    Emap_Best_t * pBest = &pMaps[ObjId].Best[Phase];
    Emap_Cut_t * pCut;
    float Area;
    int i;
    if ( pBest->pGate == NULL && !pBest->fInv )
        return 0;
    if ( pBest->fInv )
        return pLib->InvArea + Emap_PhaseRef_rec( pNtk, pMaps, pLib, pRefs, ObjId, !Phase );
    Area = (float)Mio_GateReadArea( pBest->pGate );
    pCut = &pMaps[ObjId].Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Area += Emap_PhaseRef_rec( pNtk, pMaps, pLib, pRefs, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
    return Area;
}

static float Emap_CutDerefLeaves_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase )
{
    Emap_Best_t * pBest = &pMaps[ObjId].Best[Phase];
    Emap_Cut_t * pCut;
    float Area;
    int i;
    if ( pBest->pGate == NULL && !pBest->fInv )
        return 0;
    if ( pBest->fInv )
        return pLib->InvArea + Emap_PhaseDeref_rec( pNtk, pMaps, pLib, pRefs, ObjId, !Phase );
    Area = (float)Mio_GateReadArea( pBest->pGate );
    pCut = &pMaps[ObjId].Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Area += Emap_PhaseDeref_rec( pNtk, pMaps, pLib, pRefs, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
    return Area;
}

static float Emap_CutRefOnlyLeaves_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase )
{
    Emap_Best_t * pBest = &pMaps[ObjId].Best[Phase];
    Emap_Cut_t * pCut;
    float Area = 0;
    int i;
    if ( pBest->pGate == NULL && !pBest->fInv )
        return 0;
    if ( pBest->fInv )
        return pLib->InvArea + Emap_PhaseRef_rec( pNtk, pMaps, pLib, pRefs, ObjId, !Phase );
    pCut = &pMaps[ObjId].Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Area += Emap_PhaseRef_rec( pNtk, pMaps, pLib, pRefs, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
    return Area;
}

static float Emap_PhaseRef_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase )
{
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return 0;
    if ( pRefs[2 * ObjId + Phase]++ > 0 )
        return 0;
    return Emap_CutRefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
}

static float Emap_PhaseDeref_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, int ObjId, int Phase )
{
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return 0;
    assert( pRefs[2 * ObjId + Phase] > 0 );
    if ( --pRefs[2 * ObjId + Phase] > 0 )
        return 0;
    return Emap_CutDerefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
}

static float Emap_CutRefVisitLeaves_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase )
{
    Emap_Best_t * pBest = &pMaps[ObjId].Best[Phase];
    Emap_Cut_t * pCut;
    float Area;
    int i;
    if ( pBest->pGate == NULL && !pBest->fInv )
        return 0;
    if ( pBest->fInv )
        return pLib->InvArea + Emap_PhaseRefVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, !Phase );
    Area = (float)Mio_GateReadArea( pBest->pGate );
    pCut = &pMaps[ObjId].Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Area += Emap_PhaseRefVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
    return Area;
}

static float Emap_CutRefOnlyLeavesVisit_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase )
{
    Emap_Best_t * pBest = &pMaps[ObjId].Best[Phase];
    Emap_Cut_t * pCut;
    float Area = 0;
    int i;
    if ( pBest->pGate == NULL && !pBest->fInv )
        return 0;
    if ( pBest->fInv )
        return pLib->InvArea + Emap_PhaseRefVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, !Phase );
    pCut = &pMaps[ObjId].Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Area += Emap_PhaseRefVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
    return Area;
}

static float Emap_PhaseRefVisit_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase )
{
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return 0;
    Vec_IntPush( vTouched, 2 * ObjId + Phase );
    if ( pRefs[2 * ObjId + Phase]++ > 0 )
        return 0;
    return Emap_CutRefVisitLeaves_rec( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, Phase );
}

static float Emap_CutMeasureCandidate( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, Emap_Cut_t * pCut, Emap_Cell_t * pCell )
{
    float Area = pCell->Area;
    int i, Entry;
    Vec_IntClear( vTouched );
    for ( i = 0; i < pCell->nPins; i++ )
        Area += Emap_PhaseRefVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, pCut->Leaves[pCell->PinToLeaf[i]], pCell->PinPhase[i] );
    Vec_IntForEachEntryReverse( vTouched, Entry, i )
        pRefs[Entry]--;
    return Area;
}

static void Emap_NodeRefreshInverterPhase( Emap_Obj_t * pMap, Emap_Lib_t * pLib, int Phase )
{
    if ( !pMap->Best[Phase].fInv )
        return;
    pMap->Best[Phase] = pMap->Best[!Phase];
    pMap->Best[Phase].fInv = 1;
    pMap->Best[Phase].Arr += pLib->InvDelay;
    pMap->Best[Phase].Flow += pLib->InvArea;
}

static int Emap_NodeImproveExactPhase( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, double * pRequired, Vec_Int_t * vTouched, int ObjId, int Phase, int fRelaxArrival )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t OldBest = pMap->Best[Phase];
    Emap_Best_t BestBest = OldBest;
    Emap_Cut_t * pCut;
    Emap_Cell_t * pCell;
    word Mask;
    float AreaOld, AreaBest, AreaCand;
    double Required, ArrBest, ArrCand;
    int i, k, c, fCompl, fChanged = 0;
    if ( pRefs[2 * ObjId + Phase] == 0 )
        return 0;
    if ( OldBest.pGate == NULL || OldBest.fInv || OldBest.TwinObj >= 0 )
        return 0;
    Required = pRequired[2 * ObjId + Phase];
    if ( Required >= EMAP_DOUBLE_LARGE / 2 )
        return 0;
    AreaOld = Emap_CutDerefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    AreaBest = AreaOld;
    ArrBest = OldBest.Arr;
    for ( i = 0; i < pMap->nCuts; i++ )
    {
        pCut = &pMap->Cuts[i];
        if ( pCut->nLeaves < 2 )
            continue;
        Mask = Emap_TruthMask( pCut->nLeaves );
        for ( fCompl = 0; fCompl < 2; fCompl++ )
        {
            if ( fCompl != Phase )
                continue;
            c = Emap_LibFindFirst( pLib, pCut->nLeaves, fCompl ? (pCut->Truth ^ Mask) : pCut->Truth );
            if ( c < 0 )
                continue;
            for ( ; c < pLib->nCells; c++ )
            {
                pCell = &pLib->pCells[c];
                if ( pCell->nPins != pCut->nLeaves || pCell->Truth != (fCompl ? (pCut->Truth ^ Mask) : pCut->Truth) )
                    break;
                ArrCand = 0;
                for ( k = 0; k < pCell->nPins; k++ )
                    ArrCand = Abc_MaxDouble( ArrCand, pMaps[pCut->Leaves[pCell->PinToLeaf[k]]].Best[pCell->PinPhase[k]].Arr + pCell->Delay[k] );
                if ( ArrCand > Required + 0.001 )
                    continue;
                if ( !fRelaxArrival && ArrCand > OldBest.Arr + 0.001 )
                    continue;
                AreaCand = Emap_CutMeasureCandidate( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, pCut, pCell );
                if ( AreaCand < AreaBest - 0.001 || (AreaCand < AreaBest + 0.001 && ArrCand < ArrBest - 0.001) )
                {
                    Emap_BestClean( &BestBest );
                    BestBest.pGate = pCell->pGate;
                    BestBest.Cut = i;
                    BestBest.nPins = pCell->nPins;
                    BestBest.Arr = ArrCand;
                    BestBest.Flow = AreaCand;
                    BestBest.fInv = 0;
                    for ( k = 0; k < pCell->nPins; k++ )
                    {
                        BestBest.PinToLeaf[k] = pCell->PinToLeaf[k];
                        BestBest.PinPhase[k] = pCell->PinPhase[k];
                    }
                    AreaBest = AreaCand;
                    ArrBest = ArrCand;
                }
            }
        }
    }
    fChanged = (BestBest.pGate != OldBest.pGate || BestBest.Cut != OldBest.Cut || memcmp( BestBest.PinToLeaf, OldBest.PinToLeaf, sizeof(int) * EMAP_LEAF_MAX ) || memcmp( BestBest.PinPhase, OldBest.PinPhase, sizeof(int) * EMAP_LEAF_MAX ));
    pMap->Best[Phase] = BestBest;
    Emap_CutRefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    return fChanged;
}

static int Emap_NodeDropPhaseExact( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, double * pRequired, int ObjId, int Phase )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t OldBest = pMap->Best[Phase];
    Emap_Best_t SrcBest = pMap->Best[!Phase];
    float AreaOld, AreaNew;
    if ( pRefs[2 * ObjId + Phase] == 0 )
        return 0;
    if ( SrcBest.pGate == NULL || SrcBest.fInv || SrcBest.TwinObj >= 0 )
        return 0;
    if ( SrcBest.Arr + pLib->InvDelay > pRequired[2 * ObjId + Phase] + 0.001 )
        return 0;
    AreaOld = Emap_CutDerefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    pMap->Best[Phase] = SrcBest;
    pMap->Best[Phase].fInv = 1;
    pMap->Best[Phase].TwinObj = -1;
    pMap->Best[Phase].TwinPhase = -1;
    pMap->Best[Phase].Arr = SrcBest.Arr + pLib->InvDelay;
    pMap->Best[Phase].Flow = SrcBest.Flow + pLib->InvArea;
    AreaNew = Emap_CutRefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    if ( AreaNew < AreaOld - 0.001 )
        return 1;
    Emap_CutDerefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    pMap->Best[Phase] = OldBest;
    Emap_CutRefLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    return 0;
}

static int Emap_ObjSharedPhase( Emap_Obj_t * pMaps, int * pRefs, int ObjId )
{
    Emap_Best_t * pBest0 = &pMaps[ObjId].Best[0];
    Emap_Best_t * pBest1 = &pMaps[ObjId].Best[1];
    if ( pBest0->fInv && !pBest1->fInv && pBest1->pGate != NULL && pBest1->TwinObj < 0 )
        return 1;
    if ( pBest1->fInv && !pBest0->fInv && pBest0->pGate != NULL && pBest0->TwinObj < 0 )
        return 0;
    if ( pRefs[2 * ObjId] && !pRefs[2 * ObjId + 1] && !pBest0->fInv && pBest0->pGate != NULL && pBest0->TwinObj < 0 )
        return 0;
    if ( pRefs[2 * ObjId + 1] && !pRefs[2 * ObjId] && !pBest1->fInv && pBest1->pGate != NULL && pBest1->TwinObj < 0 )
        return 1;
    return -1;
}

static float Emap_CutDerefLeavesLocal_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase );

static float Emap_PhaseDerefLocal_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase )
{
    int Entry = 2 * ObjId + Phase;
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) || Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
        return 0;
    if ( pRefs[Entry] == 0 )
        return 0;
    Vec_IntPush( vTouched, Entry );
    if ( --pRefs[Entry] > 0 )
        return 0;
    return Emap_CutDerefLeavesLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, Phase );
}

static float Emap_CutDerefLeavesLocal_rec( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase )
{
    Emap_Best_t * pBest = &pMaps[ObjId].Best[Phase];
    Emap_Cut_t * pCut;
    float Area;
    int i;
    if ( pBest->pGate == NULL && !pBest->fInv )
        return 0;
    if ( pBest->fInv )
        return pLib->InvArea + Emap_PhaseDerefLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, !Phase );
    Area = (float)Mio_GateReadArea( pBest->pGate );
    pCut = &pMaps[ObjId].Cuts[pBest->Cut];
    for ( i = 0; i < pBest->nPins; i++ )
        Area += Emap_PhaseDerefLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i] );
    return Area;
}

static float Emap_MogRefLeavesForUsedPhases( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int * pRefs, Vec_Int_t * vTouched, int ObjId, int Phase, int fVisit )
{
    float Area = 0;
    if ( pRefs[2 * ObjId + Phase] || pRefs[2 * ObjId + !Phase] )
    {
        if ( fVisit )
            Area += Emap_CutRefOnlyLeavesVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, ObjId, Phase );
        else
            Area += Emap_CutRefOnlyLeaves_rec( pNtk, pMaps, pLib, pRefs, ObjId, Phase );
    }
    if ( pRefs[2 * ObjId + !Phase] )
        Area += pLib->InvArea;
    return Area;
}

static int Emap_NodeMatchMogExactLocal( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Emap_Tuples_t * pTuples, int * pRefs, double * pRequired, Vec_Int_t * vTouched, int ObjId )
{
    int iTuple, nChanged = 0;
    if ( pTuples == NULL || pTuples->pFirstLow == NULL )
        return 0;
    pTuples->nExactLocalCalls++;
    for ( iTuple = pTuples->pFirstLow[ObjId]; iTuple >= 0; iTuple = pTuples->pArray[iTuple].NextLow )
    {
        Emap_Tuple_t * pTuple = &pTuples->pArray[iTuple];
        Emap_Mog_t * pMog = &pLib->pMogs[pTuple->Mog];
        Emap_PackEntry_t Entry0, Entry1;
        Emap_Best_t OldBest00, OldBest01, OldBest10, OldBest11;
        int Shared0, Shared1, Entry, t, fObj0Low, nDerefTouched;
        float AreaOld, AreaNew;
        double Arr0, Arr1;
        int Obj0 = pTuple->Obj0, Obj1 = pTuple->Obj1;
        int Used0 = pRefs[2 * Obj0] || pRefs[2 * Obj0 + 1];
        int Used1 = pRefs[2 * Obj1] || pRefs[2 * Obj1 + 1];
        pTuples->nExactLocalCandidates++;
        if ( pMog->nPins == 2 )
            pTuples->nExactLocalCand2++;
        else if ( pMog->nPins == 3 )
            pTuples->nExactLocalCand3++;
        if ( !Used0 || !Used1 )
        {
            pTuples->nExactLocalRejectUnused++;
            continue;
        }
        if ( pMaps[Obj0].Best[0].TwinObj >= 0 || pMaps[Obj0].Best[1].TwinObj >= 0 || pMaps[Obj1].Best[0].TwinObj >= 0 || pMaps[Obj1].Best[1].TwinObj >= 0 )
        {
            pTuples->nExactLocalRejectTwin++;
            continue;
        }
        Shared0 = Emap_ObjSharedPhase( pMaps, pRefs, Obj0 );
        Shared1 = Emap_ObjSharedPhase( pMaps, pRefs, Obj1 );
        if ( Shared0 < 0 || Shared1 < 0 )
        {
            pTuples->nExactLocalRejectShared++;
            continue;
        }
        Arr0 = Emap_MogArrival( pMaps, &pMaps[Obj0].Cuts[pTuple->Cut0], pMog, pTuple->fSwap );
        Arr1 = Emap_MogArrival( pMaps, &pMaps[Obj1].Cuts[pTuple->Cut1], pMog, !pTuple->fSwap );
        if ( Arr0 > pRequired[2 * Obj0 + pTuple->Phase0] + 0.001 || Arr1 > pRequired[2 * Obj1 + pTuple->Phase1] + 0.001 )
        {
            pTuples->nExactLocalRejectRequired++;
            continue;
        }
        if ( pRefs[2 * Obj0 + !pTuple->Phase0] && Arr0 + pLib->InvDelay > pRequired[2 * Obj0 + !pTuple->Phase0] + 0.001 )
        {
            pTuples->nExactLocalRejectRequired++;
            continue;
        }
        if ( pRefs[2 * Obj1 + !pTuple->Phase1] && Arr1 + pLib->InvDelay > pRequired[2 * Obj1 + !pTuple->Phase1] + 0.001 )
        {
            pTuples->nExactLocalRejectRequired++;
            continue;
        }

        OldBest00 = pMaps[Obj0].Best[0];
        OldBest01 = pMaps[Obj0].Best[1];
        OldBest10 = pMaps[Obj1].Best[0];
        OldBest11 = pMaps[Obj1].Best[1];
        fObj0Low = Obj0 < Obj1;
        Vec_IntClear( vTouched );
        AreaOld = 0;
        if ( fObj0Low )
        {
            AreaOld += Emap_CutDerefLeavesLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, Obj1, Shared1 );
            AreaOld += pRefs[2 * Obj1 + !Shared1] ? pLib->InvArea : 0;
            AreaOld += Emap_CutDerefLeavesLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, Obj0, Shared0 );
            AreaOld += pRefs[2 * Obj0 + !Shared0] ? pLib->InvArea : 0;
        }
        else
        {
            AreaOld += Emap_CutDerefLeavesLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, Obj0, Shared0 );
            AreaOld += pRefs[2 * Obj0 + !Shared0] ? pLib->InvArea : 0;
            AreaOld += Emap_CutDerefLeavesLocal_rec( pNtk, pMaps, pLib, pRefs, vTouched, Obj1, Shared1 );
            AreaOld += pRefs[2 * Obj1 + !Shared1] ? pLib->InvArea : 0;
        }
        nDerefTouched = Vec_IntSize( vTouched );

        memset( &Entry0, 0, sizeof(Entry0) );
        memset( &Entry1, 0, sizeof(Entry1) );
        Entry0.ObjId = Obj0; Entry0.Phase = pTuple->Phase0; Entry0.Cut = pTuple->Cut0;
        Entry1.ObjId = Obj1; Entry1.Phase = pTuple->Phase1; Entry1.Cut = pTuple->Cut1;
        Emap_MogApply( pMaps, &Entry0, &Entry1, pMog, pTuple->fSwap );
        Emap_MogSetOppositePhase( pMaps, pLib, Obj0, pTuple->Phase0, pMog->Area );
        Emap_MogSetOppositePhase( pMaps, pLib, Obj1, pTuple->Phase1, pMog->Area );

        AreaNew = pMog->Area;
        AreaNew += Emap_MogRefLeavesForUsedPhases( pNtk, pMaps, pLib, pRefs, vTouched, Obj0, pTuple->Phase0, 1 );
        AreaNew += Emap_MogRefLeavesForUsedPhases( pNtk, pMaps, pLib, pRefs, vTouched, Obj1, pTuple->Phase1, 1 );
        Vec_IntForEachEntryReverse( vTouched, Entry, t )
        {
            if ( t < nDerefTouched )
                break;
            pRefs[Entry]--;
        }

        if ( AreaNew < AreaOld - 0.001 )
        {
            Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
            pTuples->nExactLocalAccepts++;
            if ( pMog->nPins == 2 )
                pTuples->nExactLocalAccept2++;
            else if ( pMog->nPins == 3 )
                pTuples->nExactLocalAccept3++;
            nChanged++;
            break;
        }
        pTuples->nExactLocalRejectArea++;

        pMaps[Obj0].Best[0] = OldBest00;
        pMaps[Obj0].Best[1] = OldBest01;
        pMaps[Obj1].Best[0] = OldBest10;
        pMaps[Obj1].Best[1] = OldBest11;
        for ( t = 0; t < nDerefTouched; t++ )
            pRefs[Vec_IntEntry(vTouched, t)]++;
    }
    return nChanged;
}

static int Emap_ManRecoverExactArea( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Emap_Tuples_t * pTuples, double * pRequired, int * pRefs, int nRounds, double DelayTarget, int fRelaxArrival, int fDropPhase )
{
    Vec_Int_t * vTouched = Vec_IntAlloc( 1000 );
    Abc_Obj_t * pObj;
    int i, r, f, nChanges = 0;
    for ( r = 0; r < nRounds; r++ )
    {
        int nChangesThis = 0;
        Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
        Emap_ManComputeRequiredTarget( pNtk, pMaps, pLib, pRequired, pRefs, DelayTarget );
        Abc_NtkForEachNodeReverse( pNtk, pObj, i )
        {
            if ( !Abc_AigNodeIsAnd(pObj) )
                continue;
            for ( f = 0; f < 2; f++ )
                nChangesThis += Emap_NodeImproveExactPhase( pNtk, pMaps, pLib, pRefs, pRequired, vTouched, Abc_ObjId(pObj), f, fRelaxArrival );
            Emap_NodeRefreshInverterPhase( &pMaps[Abc_ObjId(pObj)], pLib, 0 );
            Emap_NodeRefreshInverterPhase( &pMaps[Abc_ObjId(pObj)], pLib, 1 );
            if ( fDropPhase )
            {
                nChangesThis += Emap_NodeDropPhaseExact( pNtk, pMaps, pLib, pRefs, pRequired, Abc_ObjId(pObj), 0 );
                nChangesThis += Emap_NodeDropPhaseExact( pNtk, pMaps, pLib, pRefs, pRequired, Abc_ObjId(pObj), 1 );
            }
            if ( pTuples && getenv("ABC_EMAP_LOCAL_MOG_EXACT") )
                nChangesThis += Emap_NodeMatchMogExactLocal( pNtk, pMaps, pLib, pTuples, pRefs, pRequired, vTouched, Abc_ObjId(pObj) );
            Emap_RequiredPropagateUsedObj( pNtk, pMaps, pLib, pRequired, pRefs, Abc_ObjId(pObj) );
        }
        nChanges += nChangesThis;
        if ( nChangesThis == 0 )
            break;
    }
    Vec_IntFree( vTouched );
    return nChanges;
}

static int Emap_PackEntryCompare( void const * p0, void const * p1 )
{
    Emap_PackEntry_t const * pEntry0 = (Emap_PackEntry_t const *)p0;
    Emap_PackEntry_t const * pEntry1 = (Emap_PackEntry_t const *)p1;
    int i;
    if ( pEntry0->nLeaves != pEntry1->nLeaves )
        return pEntry0->nLeaves - pEntry1->nLeaves;
    if ( pEntry0->Truth < pEntry1->Truth )
        return -1;
    if ( pEntry0->Truth > pEntry1->Truth )
        return 1;
    for ( i = 0; i < pEntry0->nLeaves; i++ )
        if ( pEntry0->Leaves[i] != pEntry1->Leaves[i] )
            return pEntry0->Leaves[i] - pEntry1->Leaves[i];
    return 0;
}

static int Emap_PackEntryFindFirst( Emap_PackEntry_t * pEntries, int nEntries, Emap_Cut_t * pCut, word Truth )
{
    Emap_PackEntry_t Key;
    int Beg = 0, End = nEntries, i;
    memset( &Key, 0, sizeof(Key) );
    Key.nLeaves = pCut->nLeaves;
    Key.Truth = Truth;
    for ( i = 0; i < pCut->nLeaves; i++ )
        Key.Leaves[i] = pCut->Leaves[i];
    while ( Beg < End )
    {
        int Mid = (Beg + End) >> 1;
        if ( Emap_PackEntryCompare( &pEntries[Mid], &Key ) < 0 )
            Beg = Mid + 1;
        else
            End = Mid;
    }
    if ( Beg == nEntries || Emap_PackEntryCompare( &pEntries[Beg], &Key ) != 0 )
        return -1;
    return Beg;
}

static void Emap_TuplesFree( Emap_Tuples_t * p )
{
    ABC_FREE( p->pArray );
    ABC_FREE( p->pFirstHigh );
    ABC_FREE( p->pFirstLow );
}

static void Emap_TuplesAdd( Emap_Tuples_t * p, int Obj0, int Phase0, int Cut0, int Obj1, int Phase1, int Cut1, int Mog, int fSwap )
{
    Emap_Tuple_t * pTuple;
    int High = Abc_MaxInt( Obj0, Obj1 );
    int Low = Abc_MinInt( Obj0, Obj1 );
    if ( p->nSize == p->nCap )
    {
        p->nCap = p->nCap ? 2 * p->nCap : 1024;
        p->pArray = ABC_REALLOC( Emap_Tuple_t, p->pArray, p->nCap );
    }
    pTuple = &p->pArray[p->nSize];
    pTuple->Obj0 = Obj0;
    pTuple->Phase0 = Phase0;
    pTuple->Cut0 = Cut0;
    pTuple->Obj1 = Obj1;
    pTuple->Phase1 = Phase1;
    pTuple->Cut1 = Cut1;
    pTuple->Mog = Mog;
    pTuple->fSwap = fSwap;
    pTuple->NextHigh = p->pFirstHigh[High];
    pTuple->NextLow = p->pFirstLow[Low];
    p->pFirstHigh[High] = p->nSize;
    p->pFirstLow[Low] = p->nSize++;
}

static void Emap_ManComputeMogTuples( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Emap_Tuples_t * pTuples )
{
    Emap_PackEntry_t * pEntries;
    int * pAssign;
    Vec_Int_t * vMffcTouched = NULL;
    int * pDecs = NULL;
    char * pLeafMarks = NULL;
    Abc_Obj_t * pObj;
    int i, k, f, nEntries = 0, nGroups = 0, fUseMffc = getenv("ABC_EMAP_MFFC_TUPLES") != NULL;
    memset( pTuples, 0, sizeof(Emap_Tuples_t) );
    if ( pLib->nMogs == 0 )
        return;
    pTuples->pFirstHigh = ABC_ALLOC( int, Abc_NtkObjNumMax(pNtk) );
    pTuples->pFirstLow = ABC_ALLOC( int, Abc_NtkObjNumMax(pNtk) );
    for ( i = 0; i < Abc_NtkObjNumMax(pNtk); i++ )
    {
        pTuples->pFirstHigh[i] = -1;
        pTuples->pFirstLow[i] = -1;
    }
    pEntries = ABC_ALLOC( Emap_PackEntry_t, 2 * EMAP_CUT_MAX * Abc_NtkObjNumMax(pNtk) );
    pAssign = ABC_ALLOC( int, Abc_NtkObjNumMax(pNtk) );
    for ( i = 0; i < Abc_NtkObjNumMax(pNtk); i++ )
        pAssign[i] = -1;
    if ( fUseMffc )
    {
        vMffcTouched = Vec_IntAlloc( 100 );
        pDecs = ABC_CALLOC( int, Abc_NtkObjNumMax(pNtk) );
        pLeafMarks = ABC_CALLOC( char, Abc_NtkObjNumMax(pNtk) );
    }
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emap_Obj_t * pMap = &pMaps[Abc_ObjId(pObj)];
            int c;
            for ( c = 0; c < pMap->nCuts; c++ )
            {
                Emap_Cut_t * pCut = &pMap->Cuts[c];
                word Truth = f ? (pCut->Truth ^ Emap_TruthMask(pCut->nLeaves)) : pCut->Truth;
                if ( pCut->nLeaves < 2 || pCut->nLeaves > 3 )
                    continue;
                pEntries[nEntries].ObjId = Abc_ObjId(pObj);
                pEntries[nEntries].Phase = f;
                pEntries[nEntries].Cut = c;
                pEntries[nEntries].nLeaves = pCut->nLeaves;
                pEntries[nEntries].Truth = Truth;
                for ( k = 0; k < pCut->nLeaves; k++ )
                    pEntries[nEntries].Leaves[k] = pCut->Leaves[k];
                nEntries++;
            }
        }
    }
    qsort( pEntries, nEntries, sizeof(Emap_PackEntry_t), Emap_PackEntryCompare );
    for ( i = nEntries - 1; i >= 0; i-- )
    {
        Emap_PackEntry_t * pEntry0 = &pEntries[i];
        Emap_Cut_t * pCut0 = &pMaps[pEntry0->ObjId].Cuts[pEntry0->Cut];
        for ( k = 0; k < pLib->nMogs; k++ )
        {
            Emap_Mog_t * pMog = &pLib->pMogs[k];
            int s;
            if ( pMog->nPins != pCut0->nLeaves )
                continue;
            for ( s = 0; s < 2; s++ )
            {
                word Truth0 = s ? pMog->Truth1 : pMog->Truth0;
                word Truth1 = s ? pMog->Truth0 : pMog->Truth1;
                int Beg;
                if ( Truth0 != pEntry0->Truth )
                    continue;
                Beg = Emap_PackEntryFindFirst( pEntries, nEntries, pCut0, Truth1 );
                if ( Beg < 0 )
                    continue;
                for ( ; Beg < nEntries && pEntries[Beg].nLeaves == pCut0->nLeaves && pEntries[Beg].Truth == Truth1; Beg++ )
                {
                    Emap_PackEntry_t * pEntry1 = &pEntries[Beg];
                    int m, fSameLeaves = 1;
                    for ( m = 0; m < pCut0->nLeaves; m++ )
                        if ( pEntry1->Leaves[m] != pCut0->Leaves[m] )
                            fSameLeaves = 0;
                    if ( !fSameLeaves )
                        break;
                    if ( pEntry1->ObjId == pEntry0->ObjId )
                        continue;
                    if ( Emap_ObjPairHasDirectDanglingRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    if ( fUseMffc ? Emap_ObjPairHasMffcDanglingRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId, pCut0, pLeafMarks, pDecs, vMffcTouched ) : Emap_ObjPairHasTfiRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    if ( pAssign[pEntry0->ObjId] == -1 && pAssign[pEntry1->ObjId] == -1 )
                        pAssign[pEntry0->ObjId] = pAssign[pEntry1->ObjId] = nGroups++;
                    else if ( pAssign[pEntry0->ObjId] != pAssign[pEntry1->ObjId] || pAssign[pEntry0->ObjId] == -1 )
                        continue;
                    Emap_TuplesAdd( pTuples, pEntry0->ObjId, pEntry0->Phase, pEntry0->Cut, pEntry1->ObjId, pEntry1->Phase, pEntry1->Cut, k, s );
                }
            }
        }
    }
    if ( getenv("ABC_EMAP_DEBUG_MOG") )
        printf( "ABC emap MOG tuple setup: tuples=%d groups=%d mode=%s\n", pTuples->nSize, nGroups, fUseMffc ? "mffc" : "strict" );
    ABC_FREE( pLeafMarks );
    ABC_FREE( pDecs );
    if ( vMffcTouched )
        Vec_IntFree( vMffcTouched );
    ABC_FREE( pAssign );
    ABC_FREE( pEntries );
}

static int Emap_ObjPairHasDirectDanglingRelation( Abc_Ntk_t * pNtk, int ObjId0, int ObjId1 )
{
    Abc_Obj_t * pObj0 = Abc_NtkObj( pNtk, ObjId0 );
    Abc_Obj_t * pObj1 = Abc_NtkObj( pNtk, ObjId1 );
    if ( !Abc_ObjIsPi(pObj0) && !Abc_AigNodeIsConst(pObj0) && (Abc_ObjFaninId0(pObj0) == ObjId1 || Abc_ObjFaninId1(pObj0) == ObjId1) && Abc_ObjFanoutNum(pObj1) == 1 )
        return 1;
    if ( !Abc_ObjIsPi(pObj1) && !Abc_AigNodeIsConst(pObj1) && (Abc_ObjFaninId0(pObj1) == ObjId0 || Abc_ObjFaninId1(pObj1) == ObjId0) && Abc_ObjFanoutNum(pObj0) == 1 )
        return 1;
    return 0;
}

static void Emap_MffcDeref_rec( Abc_Obj_t * pObj, char * pLeafMarks, int * pDecs, Vec_Int_t * vTouched )
{
    Abc_Obj_t * pFanin;
    int i, ObjId;
    if ( Abc_ObjIsPi(pObj) || Abc_AigNodeIsConst(pObj) || pLeafMarks[Abc_ObjId(pObj)] )
        return;
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        ObjId = Abc_ObjId(pFanin);
        if ( pLeafMarks[ObjId] )
            continue;
        if ( pDecs[ObjId]++ == 0 )
            Vec_IntPush( vTouched, ObjId );
        if ( pDecs[ObjId] == Abc_ObjFanoutNum(pFanin) )
            Emap_MffcDeref_rec( pFanin, pLeafMarks, pDecs, vTouched );
    }
}

static int Emap_ObjPairHasMffcDanglingRelation( Abc_Ntk_t * pNtk, int ObjId0, int ObjId1, Emap_Cut_t * pCut, char * pLeafMarks, int * pDecs, Vec_Int_t * vTouched )
{
    int Low = Abc_MinInt( ObjId0, ObjId1 );
    int High = Abc_MaxInt( ObjId0, ObjId1 );
    Abc_Obj_t * pLow = Abc_NtkObj( pNtk, Low );
    Abc_Obj_t * pHigh = Abc_NtkObj( pNtk, High );
    int i, Entry, fDangling;
    assert( Vec_IntSize(vTouched) == 0 );
    if ( !Abc_ObjIsPi(pHigh) && !Abc_AigNodeIsConst(pHigh) && (Abc_ObjFaninId0(pHigh) == Low || Abc_ObjFaninId1(pHigh) == Low) && Abc_ObjFanoutNum(pLow) == 1 )
        return 1;
    for ( i = 0; i < pCut->nLeaves; i++ )
        pLeafMarks[pCut->Leaves[i]] = 1;
    Emap_MffcDeref_rec( pHigh, pLeafMarks, pDecs, vTouched );
    fDangling = Abc_ObjFanoutNum(pLow) - pDecs[Low] <= 0;
    for ( i = 0; i < pCut->nLeaves; i++ )
        pLeafMarks[pCut->Leaves[i]] = 0;
    Vec_IntForEachEntry( vTouched, Entry, i )
        pDecs[Entry] = 0;
    Vec_IntClear( vTouched );
    return fDangling;
}

static int Emap_ObjIsInTfi_rec( Abc_Obj_t * pRoot, int TargetId )
{
    if ( Abc_ObjId(pRoot) == TargetId )
        return 1;
    if ( Abc_ObjIsPi(pRoot) || Abc_AigNodeIsConst(pRoot) )
        return 0;
    if ( Abc_NodeIsTravIdCurrent(pRoot) )
        return 0;
    Abc_NodeSetTravIdCurrent(pRoot);
    return Emap_ObjIsInTfi_rec( Abc_ObjFanin0(pRoot), TargetId ) || Emap_ObjIsInTfi_rec( Abc_ObjFanin1(pRoot), TargetId );
}

static int Emap_ObjPairHasTfiRelation( Abc_Ntk_t * pNtk, int ObjId0, int ObjId1 )
{
    Abc_NtkIncrementTravId( pNtk );
    if ( Emap_ObjIsInTfi_rec( Abc_NtkObj(pNtk, ObjId0), ObjId1 ) )
        return 1;
    Abc_NtkIncrementTravId( pNtk );
    return Emap_ObjIsInTfi_rec( Abc_NtkObj(pNtk, ObjId1), ObjId0 );
}

static double Emap_MogArrival( Emap_Obj_t * pMaps, Emap_Cut_t * pCut, Emap_Mog_t * pMog, int fSwap );

static void Emap_MogApply( Emap_Obj_t * pMaps, Emap_PackEntry_t * pEntry0, Emap_PackEntry_t * pEntry1, Emap_Mog_t * pMog, int fSwap )
{
    Emap_Best_t * pBest0 = &pMaps[pEntry0->ObjId].Best[pEntry0->Phase];
    Emap_Best_t * pBest1 = &pMaps[pEntry1->ObjId].Best[pEntry1->Phase];
    Emap_Cut_t * pCut0 = &pMaps[pEntry0->ObjId].Cuts[pEntry0->Cut];
    Emap_Cut_t * pCut1 = &pMaps[pEntry1->ObjId].Cuts[pEntry1->Cut];
    int i;
    pBest0->pGate = fSwap ? pMog->pGate1 : pMog->pGate0;
    pBest1->pGate = fSwap ? pMog->pGate0 : pMog->pGate1;
    pBest0->Cut = pEntry0->Cut;
    pBest1->Cut = pEntry1->Cut;
    pBest0->nPins = pBest1->nPins = pMog->nPins;
    pBest0->TwinObj = pEntry1->ObjId;
    pBest0->TwinPhase = pEntry1->Phase;
    pBest1->TwinObj = pEntry0->ObjId;
    pBest1->TwinPhase = pEntry0->Phase;
    pBest0->fInv = pBest1->fInv = 0;
    pBest0->Arr = Emap_MogArrival( pMaps, pCut0, pMog, fSwap );
    pBest1->Arr = Emap_MogArrival( pMaps, pCut1, pMog, !fSwap );
    pBest0->Flow = pBest1->Flow = pMog->Area;
    for ( i = 0; i < pMog->nPins; i++ )
    {
        pBest0->PinToLeaf[i] = pBest1->PinToLeaf[i] = pMog->PinToLeaf[i];
        pBest0->PinPhase[i] = pBest1->PinPhase[i] = pMog->PinPhase[i];
    }
}

static double Emap_MogArrival( Emap_Obj_t * pMaps, Emap_Cut_t * pCut, Emap_Mog_t * pMog, int fSwap )
{
    double Arr = 0;
    int i;
    for ( i = 0; i < pMog->nPins; i++ )
    {
        Emap_Best_t * pLeafBest = &pMaps[pCut->Leaves[pMog->PinToLeaf[i]]].Best[pMog->PinPhase[i]];
        Arr = Abc_MaxDouble( Arr, pLeafBest->Arr + (fSwap ? pMog->Delay1[i] : pMog->Delay0[i]) );
    }
    return Arr;
}

static void Emap_MogSetOppositePhase( Emap_Obj_t * pMaps, Emap_Lib_t * pLib, int ObjId, int Phase, float Flow )
{
    pMaps[ObjId].Best[!Phase] = pMaps[ObjId].Best[Phase];
    pMaps[ObjId].Best[!Phase].fInv = 1;
    pMaps[ObjId].Best[!Phase].TwinObj = -1;
    pMaps[ObjId].Best[!Phase].TwinPhase = -1;
    pMaps[ObjId].Best[!Phase].Arr = pMaps[ObjId].Best[Phase].Arr + pLib->InvDelay;
    pMaps[ObjId].Best[!Phase].Flow = Flow + pLib->InvArea;
}

static int Emap_NodeMatchMogArea( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Emap_Tuples_t * pTuples, int * pRefs, double * pRequired, int ObjId, int fCheckRequired )
{
    int iTuple, iBestTuple = -1;
    float BestFlow = (float)EMAP_DOUBLE_LARGE, BestScore = (float)EMAP_DOUBLE_LARGE;
    if ( pTuples == NULL || pTuples->pFirstHigh == NULL )
        return 0;
    pTuples->nAreaCalls++;
    for ( iTuple = pTuples->pFirstHigh[ObjId]; iTuple >= 0; iTuple = pTuples->pArray[iTuple].NextHigh )
    {
        Emap_Tuple_t * pTuple = &pTuples->pArray[iTuple];
        Emap_Mog_t * pMog = &pLib->pMogs[pTuple->Mog];
        Emap_Cut_t * pCut0 = &pMaps[pTuple->Obj0].Cuts[pTuple->Cut0];
        Emap_Cut_t * pCut1 = &pMaps[pTuple->Obj1].Cuts[pTuple->Cut1];
        Emap_Best_t * pBest0 = &pMaps[pTuple->Obj0].Best[pTuple->Phase0];
        Emap_Best_t * pBest1 = &pMaps[pTuple->Obj1].Best[pTuple->Phase1];
        double Arr0, Arr1;
        float OldFlow = 0, NewFlow, NewScore, LeafFlow = 0, CombinedRefs = 0;
        int fRespectsRequired = 1;
        int i;
        pTuples->nAreaCandidates++;
        if ( pBest0->TwinObj >= 0 || pBest1->TwinObj >= 0 )
        {
            pTuples->nAreaRejectTwin++;
            continue;
        }
        Arr0 = Emap_MogArrival( pMaps, pCut0, pMog, pTuple->fSwap );
        Arr1 = Emap_MogArrival( pMaps, pCut1, pMog, !pTuple->fSwap );
        if ( fCheckRequired )
        {
            if ( Arr0 > pRequired[2 * pTuple->Obj0 + pTuple->Phase0] + 0.001 || Arr1 > pRequired[2 * pTuple->Obj1 + pTuple->Phase1] + 0.001 )
            {
                if ( getenv("ABC_EMAP_DEBUG_MOG") && pTuples->nAreaSamples < 8 )
                {
                    printf( "ABC emap MOG req sample %d: roots=(%d,%d) phases=(%d,%d) arr=(%.2f,%.2f) req=(%.2f,%.2f) invreq=(%.2f,%.2f)\n",
                        pTuples->nAreaSamples, pTuple->Obj0, pTuple->Obj1, pTuple->Phase0, pTuple->Phase1, Arr0, Arr1,
                        pRequired[2 * pTuple->Obj0 + pTuple->Phase0], pRequired[2 * pTuple->Obj1 + pTuple->Phase1],
                        pRequired[2 * pTuple->Obj0 + !pTuple->Phase0], pRequired[2 * pTuple->Obj1 + !pTuple->Phase1] );
                    pTuples->nAreaSamples++;
                }
                pTuples->nAreaRejectRequired++;
                continue;
            }
            if ( (pRefs == NULL || pRefs[2 * pTuple->Obj0 + !pTuple->Phase0] > 0) && Arr0 + pLib->InvDelay > pRequired[2 * pTuple->Obj0 + !pTuple->Phase0] + 0.001 )
            {
                if ( getenv("ABC_EMAP_DEBUG_MOG") && pTuples->nAreaSamples < 8 )
                {
                    printf( "ABC emap MOG invreq sample %d: roots=(%d,%d) phases=(%d,%d) arr=(%.2f,%.2f) req=(%.2f,%.2f) invreq=(%.2f,%.2f)\n",
                        pTuples->nAreaSamples, pTuple->Obj0, pTuple->Obj1, pTuple->Phase0, pTuple->Phase1, Arr0, Arr1,
                        pRequired[2 * pTuple->Obj0 + pTuple->Phase0], pRequired[2 * pTuple->Obj1 + pTuple->Phase1],
                        pRequired[2 * pTuple->Obj0 + !pTuple->Phase0], pRequired[2 * pTuple->Obj1 + !pTuple->Phase1] );
                    pTuples->nAreaSamples++;
                }
                pTuples->nAreaRejectRequired++;
                continue;
            }
            if ( (pRefs == NULL || pRefs[2 * pTuple->Obj1 + !pTuple->Phase1] > 0) && Arr1 + pLib->InvDelay > pRequired[2 * pTuple->Obj1 + !pTuple->Phase1] + 0.001 )
            {
                pTuples->nAreaRejectRequired++;
                continue;
            }
        }
        if ( pRequired != NULL )
        {
            if ( pBest0->Arr > pRequired[2 * pTuple->Obj0 + pTuple->Phase0] + 0.001 || pBest1->Arr > pRequired[2 * pTuple->Obj1 + pTuple->Phase1] + 0.001 )
                fRespectsRequired = 0;
            if ( (pRefs == NULL || pRefs[2 * pTuple->Obj0 + !pTuple->Phase0] > 0) && pBest0->Arr + pLib->InvDelay > pRequired[2 * pTuple->Obj0 + !pTuple->Phase0] + 0.001 )
                fRespectsRequired = 0;
            if ( (pRefs == NULL || pRefs[2 * pTuple->Obj1 + !pTuple->Phase1] > 0) && pBest1->Arr + pLib->InvDelay > pRequired[2 * pTuple->Obj1 + !pTuple->Phase1] + 0.001 )
                fRespectsRequired = 0;
        }
        {
            float Est0 = (float)Abc_MaxInt( 1, pRefs ? pRefs[2 * pTuple->Obj0 + pTuple->Phase0] : Abc_ObjFanoutNum(Abc_NtkObj(pNtk, pTuple->Obj0)) );
            float Est1 = (float)Abc_MaxInt( 1, pRefs ? pRefs[2 * pTuple->Obj1 + pTuple->Phase1] : Abc_ObjFanoutNum(Abc_NtkObj(pNtk, pTuple->Obj1)) );
            OldFlow = pBest0->Flow / Est0 + pBest1->Flow / Est1;
            CombinedRefs = Est0 + Est1;
        }
        for ( i = 0; i < pMog->nPins; i++ )
        {
            int Leaf = pCut0->Leaves[pMog->PinToLeaf[i]];
            int LeafPhase = pMog->PinPhase[i];
            float Div = (float)Abc_MaxInt( 1, pRefs ? pRefs[2 * Leaf + LeafPhase] : Abc_ObjFanoutNum(Abc_NtkObj(pNtk, Leaf)) );
            LeafFlow += pMaps[Leaf].Best[LeafPhase].Flow / Div;
        }
        NewFlow = (pMog->Area + 2 * LeafFlow) / Abc_MaxFloat( 1.0f, CombinedRefs );
        NewScore = NewFlow;
        if ( pRefs != NULL )
        {
            if ( pRefs[2 * pTuple->Obj0 + !pTuple->Phase0] > 0 )
                NewScore += pLib->InvArea / Abc_MaxFloat( 1.0f, CombinedRefs );
            if ( pRefs[2 * pTuple->Obj1 + !pTuple->Phase1] > 0 )
                NewScore += pLib->InvArea / Abc_MaxFloat( 1.0f, CombinedRefs );
        }
        if ( fRespectsRequired && NewFlow > OldFlow - 0.001 )
        {
            pTuples->nAreaRejectFlow++;
            continue;
        }
        if ( NewScore < BestScore - 0.001 || (NewScore < BestScore + 0.001 && NewFlow < BestFlow - 0.001) )
        {
            iBestTuple = iTuple;
            BestFlow = NewFlow;
            BestScore = NewScore;
        }
    }
    if ( iBestTuple < 0 )
        return 0;
    {
        Emap_Tuple_t * pTuple = &pTuples->pArray[iBestTuple];
        Emap_Mog_t * pMog = &pLib->pMogs[pTuple->Mog];
        Emap_PackEntry_t Entry0, Entry1;
        memset( &Entry0, 0, sizeof(Entry0) );
        memset( &Entry1, 0, sizeof(Entry1) );
        Entry0.ObjId = pTuple->Obj0;
        Entry0.Phase = pTuple->Phase0;
        Entry0.Cut = pTuple->Cut0;
        Entry1.ObjId = pTuple->Obj1;
        Entry1.Phase = pTuple->Phase1;
        Entry1.Cut = pTuple->Cut1;
        Emap_MogApply( pMaps, &Entry0, &Entry1, pMog, pTuple->fSwap );
        pMaps[pTuple->Obj0].Best[pTuple->Phase0].Flow = BestFlow;
        pMaps[pTuple->Obj1].Best[pTuple->Phase1].Flow = BestFlow;
        Emap_MogSetOppositePhase( pMaps, pLib, pTuple->Obj0, pTuple->Phase0, BestFlow );
        Emap_MogSetOppositePhase( pMaps, pLib, pTuple->Obj1, pTuple->Phase1, BestFlow );
        pTuples->nAreaAccepts++;
        return 1;
    }
}

static int Emap_ManPackMogs( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired, int * pRefs )
{
    Emap_PackEntry_t * pEntries;
    Abc_Obj_t * pObj;
    int i, k, f, nEntries = 0, nPacked = 0;
    if ( pLib->nMogs == 0 )
        return 0;
    Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
    pEntries = ABC_ALLOC( Emap_PackEntry_t, 2 * EMAP_CUT_MAX * Abc_NtkObjNumMax(pNtk) );
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emap_Best_t * pBest = &pMaps[Abc_ObjId(pObj)].Best[f];
            Emap_Obj_t * pMap = &pMaps[Abc_ObjId(pObj)];
            int c;
            if ( pRefs[2 * Abc_ObjId(pObj) + f] == 0 || pBest->TwinObj >= 0 )
                continue;
            for ( c = 0; c < pMap->nCuts; c++ )
            {
                Emap_Cut_t * pCut = &pMap->Cuts[c];
                word Truth = f ? (pCut->Truth ^ Emap_TruthMask(pCut->nLeaves)) : pCut->Truth;
                if ( pCut->nLeaves < 2 )
                    continue;
                pEntries[nEntries].ObjId = Abc_ObjId(pObj);
                pEntries[nEntries].Phase = f;
                pEntries[nEntries].Cut = c;
                pEntries[nEntries].nLeaves = pCut->nLeaves;
                pEntries[nEntries].Truth = Truth;
                for ( k = 0; k < pCut->nLeaves; k++ )
                    pEntries[nEntries].Leaves[k] = pCut->Leaves[k];
                nEntries++;
            }
        }
    }
    qsort( pEntries, nEntries, sizeof(Emap_PackEntry_t), Emap_PackEntryCompare );
    for ( i = 0; i < nEntries; i++ )
    {
        Emap_PackEntry_t * pEntry0 = &pEntries[i];
        Emap_Best_t * pBest0 = &pMaps[pEntry0->ObjId].Best[pEntry0->Phase];
        Emap_Cut_t * pCut0;
        if ( pBest0->TwinObj >= 0 )
            continue;
        pCut0 = &pMaps[pEntry0->ObjId].Cuts[pEntry0->Cut];
        for ( k = 0; k < pLib->nMogs; k++ )
        {
            Emap_Mog_t * pMog = &pLib->pMogs[k];
            int s;
            if ( pMog->nPins != pCut0->nLeaves )
                continue;
            for ( s = 0; s < 2; s++ )
            {
                word Truth0 = s ? pMog->Truth1 : pMog->Truth0;
                word Truth1 = s ? pMog->Truth0 : pMog->Truth1;
                int Beg;
                if ( Truth0 != pEntry0->Truth )
                    continue;
                if ( Emap_MogArrival( pMaps, pCut0, pMog, s ) > pRequired[2 * pEntry0->ObjId + pEntry0->Phase] + 0.001 )
                    continue;
                Beg = Emap_PackEntryFindFirst( pEntries, nEntries, pCut0, Truth1 );
                if ( Beg < 0 )
                    continue;
                for ( ; Beg < nEntries && pEntries[Beg].nLeaves == pCut0->nLeaves && pEntries[Beg].Truth == Truth1; Beg++ )
                {
                    Emap_PackEntry_t * pEntry1 = &pEntries[Beg];
                    Emap_Best_t * pBest1 = &pMaps[pEntry1->ObjId].Best[pEntry1->Phase];
                    Emap_Cut_t * pCut1 = &pMaps[pEntry1->ObjId].Cuts[pEntry1->Cut];
                    int m, fSameLeaves = 1;
                    for ( m = 0; m < pCut0->nLeaves; m++ )
                        if ( pEntry1->Leaves[m] != pCut0->Leaves[m] )
                            fSameLeaves = 0;
                    if ( !fSameLeaves )
                        break;
                    if ( pEntry1->ObjId == pEntry0->ObjId || pBest1->TwinObj >= 0 )
                        continue;
                    if ( Emap_ObjPairHasDirectDanglingRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    if ( Emap_MogArrival( pMaps, pCut1, pMog, !s ) > pRequired[2 * pEntry1->ObjId + pEntry1->Phase] + 0.001 )
                        continue;
                    Emap_MogApply( pMaps, pEntry0, pEntry1, pMog, s );
                    nPacked++;
                    break;
                }
                if ( pBest0->TwinObj >= 0 )
                    break;
            }
            if ( pBest0->TwinObj >= 0 )
                break;
        }
    }
    ABC_FREE( pEntries );
    return nPacked;
}

static int Emap_ManRecoverMogsExact( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, double * pRequired, int * pRefs )
{
    Emap_PackEntry_t * pEntries;
    Vec_Int_t * vTouched;
    Abc_Obj_t * pObj;
    int i, k, f, nEntries = 0, nApplied = 0;
    if ( pLib->nMogs == 0 )
        return 0;
    Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
    pEntries = ABC_ALLOC( Emap_PackEntry_t, 2 * EMAP_CUT_MAX * Abc_NtkObjNumMax(pNtk) );
    vTouched = Vec_IntAlloc( 1000 );
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emap_Obj_t * pMap = &pMaps[Abc_ObjId(pObj)];
            int c;
            if ( pRefs[2 * Abc_ObjId(pObj) + f] == 0 || pMap->Best[f].TwinObj >= 0 )
                continue;
            for ( c = 0; c < pMap->nCuts; c++ )
            {
                Emap_Cut_t * pCut = &pMap->Cuts[c];
                word Truth = f ? (pCut->Truth ^ Emap_TruthMask(pCut->nLeaves)) : pCut->Truth;
                if ( pCut->nLeaves < 2 )
                    continue;
                pEntries[nEntries].ObjId = Abc_ObjId(pObj);
                pEntries[nEntries].Phase = f;
                pEntries[nEntries].Cut = c;
                pEntries[nEntries].nLeaves = pCut->nLeaves;
                pEntries[nEntries].Truth = Truth;
                for ( k = 0; k < pCut->nLeaves; k++ )
                    pEntries[nEntries].Leaves[k] = pCut->Leaves[k];
                nEntries++;
            }
        }
    }
    qsort( pEntries, nEntries, sizeof(Emap_PackEntry_t), Emap_PackEntryCompare );
    for ( i = 0; i < nEntries; i++ )
    {
        Emap_PackEntry_t * pEntry0 = &pEntries[i];
        Emap_Best_t * pBest0 = &pMaps[pEntry0->ObjId].Best[pEntry0->Phase];
        Emap_Cut_t * pCut0;
        if ( pRefs[2 * pEntry0->ObjId + pEntry0->Phase] == 0 || pBest0->TwinObj >= 0 )
            continue;
        pCut0 = &pMaps[pEntry0->ObjId].Cuts[pEntry0->Cut];
        for ( k = 0; k < pLib->nMogs; k++ )
        {
            Emap_Mog_t * pMog = &pLib->pMogs[k];
            int s;
            if ( pMog->nPins != pCut0->nLeaves )
                continue;
            for ( s = 0; s < 2; s++ )
            {
                word Truth0 = s ? pMog->Truth1 : pMog->Truth0;
                word Truth1 = s ? pMog->Truth0 : pMog->Truth1;
                int Beg;
                if ( Truth0 != pEntry0->Truth )
                    continue;
                if ( Emap_MogArrival( pMaps, pCut0, pMog, s ) > pRequired[2 * pEntry0->ObjId + pEntry0->Phase] + 0.001 )
                    continue;
                Beg = Emap_PackEntryFindFirst( pEntries, nEntries, pCut0, Truth1 );
                if ( Beg < 0 )
                    continue;
                for ( ; Beg < nEntries && pEntries[Beg].nLeaves == pCut0->nLeaves && pEntries[Beg].Truth == Truth1; Beg++ )
                {
                    Emap_PackEntry_t * pEntry1 = &pEntries[Beg];
                    Emap_Best_t * pBest1 = &pMaps[pEntry1->ObjId].Best[pEntry1->Phase];
                    Emap_Best_t OldBest0, OldBest1;
                    float AreaOld, AreaNew;
                    int m, Entry, t, fSameLeaves = 1;
                    for ( m = 0; m < pCut0->nLeaves; m++ )
                        if ( pEntry1->Leaves[m] != pCut0->Leaves[m] )
                            fSameLeaves = 0;
                    if ( !fSameLeaves )
                        break;
                    if ( pEntry1->ObjId == pEntry0->ObjId || pRefs[2 * pEntry1->ObjId + pEntry1->Phase] == 0 || pBest1->TwinObj >= 0 )
                        continue;
                    if ( Emap_ObjPairHasDirectDanglingRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    if ( Emap_ObjPairHasTfiRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    if ( Emap_MogArrival( pMaps, &pMaps[pEntry1->ObjId].Cuts[pEntry1->Cut], pMog, !s ) > pRequired[2 * pEntry1->ObjId + pEntry1->Phase] + 0.001 )
                        continue;

                    OldBest0 = *pBest0;
                    OldBest1 = *pBest1;
                    AreaOld = Emap_CutDerefLeaves_rec( pNtk, pMaps, pLib, pRefs, pEntry0->ObjId, pEntry0->Phase );
                    AreaOld += Emap_CutDerefLeaves_rec( pNtk, pMaps, pLib, pRefs, pEntry1->ObjId, pEntry1->Phase );
                    Emap_MogApply( pMaps, pEntry0, pEntry1, pMog, s );
                    AreaNew = pMog->Area;
                    Vec_IntClear( vTouched );
                    AreaNew += Emap_CutRefOnlyLeavesVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, pEntry0->ObjId, pEntry0->Phase );
                    AreaNew += Emap_CutRefOnlyLeavesVisit_rec( pNtk, pMaps, pLib, pRefs, vTouched, pEntry1->ObjId, pEntry1->Phase );
                    Vec_IntForEachEntryReverse( vTouched, Entry, t )
                        pRefs[Entry]--;
                    if ( AreaNew < AreaOld - 0.001 )
                    {
                        Emap_CutRefOnlyLeaves_rec( pNtk, pMaps, pLib, pRefs, pEntry0->ObjId, pEntry0->Phase );
                        Emap_CutRefOnlyLeaves_rec( pNtk, pMaps, pLib, pRefs, pEntry1->ObjId, pEntry1->Phase );
                        nApplied++;
                        break;
                    }
                    *pBest0 = OldBest0;
                    *pBest1 = OldBest1;
                    Emap_CutRefLeaves_rec( pNtk, pMaps, pLib, pRefs, pEntry0->ObjId, pEntry0->Phase );
                    Emap_CutRefLeaves_rec( pNtk, pMaps, pLib, pRefs, pEntry1->ObjId, pEntry1->Phase );
                }
                if ( pBest0->TwinObj >= 0 )
                    break;
            }
            if ( pBest0->TwinObj >= 0 )
                break;
        }
    }
    Vec_IntFree( vTouched );
    ABC_FREE( pEntries );
    return nApplied;
}

static int Emap_ManRecoverMogsExactMffc( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Mio_Library_t * pMio, double * pRequired, int * pRefs, double DelayLimit, float * pAreaBest, double * pDelayBest )
{
    Emap_PackEntry_t * pEntries;
    Vec_Int_t * vMffcTouched;
    int * pDecs;
    char * pLeafMarks;
    Abc_Obj_t * pObj;
    float AreaBest = *pAreaBest;
    double DelayBest = *pDelayBest;
    int i, k, f, nEntries = 0, nApplied = 0, nTried = 0;
    if ( pLib->nMogs == 0 )
        return 0;
    Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
    pEntries = ABC_ALLOC( Emap_PackEntry_t, 2 * EMAP_CUT_MAX * Abc_NtkObjNumMax(pNtk) );
    vMffcTouched = Vec_IntAlloc( 100 );
    pDecs = ABC_CALLOC( int, Abc_NtkObjNumMax(pNtk) );
    pLeafMarks = ABC_CALLOC( char, Abc_NtkObjNumMax(pNtk) );
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emap_Obj_t * pMap = &pMaps[Abc_ObjId(pObj)];
            int c;
            if ( pRefs[2 * Abc_ObjId(pObj)] + pRefs[2 * Abc_ObjId(pObj) + 1] == 0 || pMap->Best[0].TwinObj >= 0 || pMap->Best[1].TwinObj >= 0 )
                continue;
            for ( c = 0; c < pMap->nCuts; c++ )
            {
                Emap_Cut_t * pCut = &pMap->Cuts[c];
                word Truth = f ? (pCut->Truth ^ Emap_TruthMask(pCut->nLeaves)) : pCut->Truth;
                if ( pCut->nLeaves < 2 || pCut->nLeaves > 3 )
                    continue;
                pEntries[nEntries].ObjId = Abc_ObjId(pObj);
                pEntries[nEntries].Phase = f;
                pEntries[nEntries].Cut = c;
                pEntries[nEntries].nLeaves = pCut->nLeaves;
                pEntries[nEntries].Truth = Truth;
                for ( k = 0; k < pCut->nLeaves; k++ )
                    pEntries[nEntries].Leaves[k] = pCut->Leaves[k];
                nEntries++;
            }
        }
    }
    qsort( pEntries, nEntries, sizeof(Emap_PackEntry_t), Emap_PackEntryCompare );
    for ( i = 0; i < nEntries; i++ )
    {
        Emap_PackEntry_t * pEntry0 = &pEntries[i];
        Emap_Obj_t * pMap0 = &pMaps[pEntry0->ObjId];
        Emap_Cut_t * pCut0;
        if ( pRefs[2 * pEntry0->ObjId] + pRefs[2 * pEntry0->ObjId + 1] == 0 || pMap0->Best[0].TwinObj >= 0 || pMap0->Best[1].TwinObj >= 0 )
            continue;
        pCut0 = &pMaps[pEntry0->ObjId].Cuts[pEntry0->Cut];
        for ( k = 0; k < pLib->nMogs; k++ )
        {
            Emap_Mog_t * pMog = &pLib->pMogs[k];
            int s;
            if ( pMog->nPins != pCut0->nLeaves )
                continue;
            for ( s = 0; s < 2; s++ )
            {
                word Truth0 = s ? pMog->Truth1 : pMog->Truth0;
                word Truth1 = s ? pMog->Truth0 : pMog->Truth1;
                int Beg;
                if ( Truth0 != pEntry0->Truth )
                    continue;
                if ( Emap_MogArrival( pMaps, pCut0, pMog, s ) > pRequired[2 * pEntry0->ObjId + pEntry0->Phase] + 0.001 )
                    continue;
                Beg = Emap_PackEntryFindFirst( pEntries, nEntries, pCut0, Truth1 );
                if ( Beg < 0 )
                    continue;
                for ( ; Beg < nEntries && pEntries[Beg].nLeaves == pCut0->nLeaves && pEntries[Beg].Truth == Truth1; Beg++ )
                {
                    Emap_PackEntry_t * pEntry1 = &pEntries[Beg];
                    Emap_Obj_t * pMap1 = &pMaps[pEntry1->ObjId];
                    Emap_Best_t OldBest00, OldBest01, OldBest10, OldBest11;
                    float AreaCur;
                    double DelayCur;
                    int m, fSameLeaves = 1;
                    for ( m = 0; m < pCut0->nLeaves; m++ )
                        if ( pEntry1->Leaves[m] != pCut0->Leaves[m] )
                            fSameLeaves = 0;
                    if ( !fSameLeaves )
                        break;
                    if ( pEntry1->ObjId == pEntry0->ObjId || pRefs[2 * pEntry1->ObjId] + pRefs[2 * pEntry1->ObjId + 1] == 0 || pMap1->Best[0].TwinObj >= 0 || pMap1->Best[1].TwinObj >= 0 )
                        continue;
                    if ( Emap_ObjPairHasMffcDanglingRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId, pCut0, pLeafMarks, pDecs, vMffcTouched ) )
                        continue;
                    if ( Emap_MogArrival( pMaps, &pMaps[pEntry1->ObjId].Cuts[pEntry1->Cut], pMog, !s ) > pRequired[2 * pEntry1->ObjId + pEntry1->Phase] + 0.001 )
                        continue;
                    OldBest00 = pMap0->Best[0];
                    OldBest01 = pMap0->Best[1];
                    OldBest10 = pMap1->Best[0];
                    OldBest11 = pMap1->Best[1];
                    Emap_MogApply( pMaps, pEntry0, pEntry1, pMog, s );
                    Emap_MogSetOppositePhase( pMaps, pLib, pEntry0->ObjId, pEntry0->Phase, pMog->Area );
                    Emap_MogSetOppositePhase( pMaps, pLib, pEntry1->ObjId, pEntry1->Phase, pMog->Area );
                    AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, pLib, pMio, &DelayCur );
                    nTried++;
                    if ( DelayCur <= DelayLimit + EMAP_DELAY_EPS && AreaCur < AreaBest - 0.001 )
                    {
                        AreaBest = AreaCur;
                        DelayBest = DelayCur;
                        nApplied++;
                        Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
                        break;
                    }
                    pMap0->Best[0] = OldBest00;
                    pMap0->Best[1] = OldBest01;
                    pMap1->Best[0] = OldBest10;
                    pMap1->Best[1] = OldBest11;
                }
                if ( pMap0->Best[0].TwinObj >= 0 || pMap0->Best[1].TwinObj >= 0 )
                    break;
            }
            if ( pMap0->Best[0].TwinObj >= 0 || pMap0->Best[1].TwinObj >= 0 )
                break;
        }
    }
    if ( getenv("ABC_EMAP_DEBUG_MOG") )
        printf( "ABC emap MOG MFFC-exact trial: entries=%d tried=%d applied=%d area=%.2f delay=%.2f\n", nEntries, nTried, nApplied, AreaBest, DelayBest );
    *pAreaBest = AreaBest;
    *pDelayBest = DelayBest;
    ABC_FREE( pLeafMarks );
    ABC_FREE( pDecs );
    Vec_IntFree( vMffcTouched );
    ABC_FREE( pEntries );
    return nApplied;
}

static int Emap_ManRecoverMogsTimed( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Mio_Library_t * pMio, int * pRefs, double DelayTarget, float * pAreaBest )
{
    Emap_PackEntry_t * pEntries;
    Abc_Obj_t * pObj;
    float AreaBest = *pAreaBest;
    double DelayCur;
    int i, k, f, nEntries = 0, nApplied = 0;
    if ( pLib->nMogs == 0 )
        return 0;
    Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
    pEntries = ABC_ALLOC( Emap_PackEntry_t, 2 * EMAP_CUT_MAX * Abc_NtkObjNumMax(pNtk) );
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emap_Obj_t * pMap = &pMaps[Abc_ObjId(pObj)];
            int c;
            if ( pRefs[2 * Abc_ObjId(pObj) + f] == 0 )
                continue;
            for ( c = 0; c < pMap->nCuts; c++ )
            {
                Emap_Cut_t * pCut = &pMap->Cuts[c];
                word Truth = f ? (pCut->Truth ^ Emap_TruthMask(pCut->nLeaves)) : pCut->Truth;
                if ( pCut->nLeaves < 2 )
                    continue;
                pEntries[nEntries].ObjId = Abc_ObjId(pObj);
                pEntries[nEntries].Phase = f;
                pEntries[nEntries].Cut = c;
                pEntries[nEntries].nLeaves = pCut->nLeaves;
                pEntries[nEntries].Truth = Truth;
                for ( k = 0; k < pCut->nLeaves; k++ )
                    pEntries[nEntries].Leaves[k] = pCut->Leaves[k];
                nEntries++;
            }
        }
    }
    qsort( pEntries, nEntries, sizeof(Emap_PackEntry_t), Emap_PackEntryCompare );
    for ( i = 0; i < nEntries; i++ )
    {
        Emap_PackEntry_t * pEntry0 = &pEntries[i];
        Emap_Best_t * pBest0 = &pMaps[pEntry0->ObjId].Best[pEntry0->Phase];
        Emap_Cut_t * pCut0;
        if ( pRefs[2 * pEntry0->ObjId + pEntry0->Phase] == 0 || pBest0->TwinObj >= 0 )
            continue;
        pCut0 = &pMaps[pEntry0->ObjId].Cuts[pEntry0->Cut];
        for ( k = 0; k < pLib->nMogs; k++ )
        {
            Emap_Mog_t * pMog = &pLib->pMogs[k];
            int s;
            if ( pMog->nPins != pCut0->nLeaves )
                continue;
            for ( s = 0; s < 2; s++ )
            {
                word Truth0 = s ? pMog->Truth1 : pMog->Truth0;
                word Truth1 = s ? pMog->Truth0 : pMog->Truth1;
                int Beg;
                if ( Truth0 != pEntry0->Truth )
                    continue;
                Beg = Emap_PackEntryFindFirst( pEntries, nEntries, pCut0, Truth1 );
                if ( Beg < 0 )
                    continue;
                for ( ; Beg < nEntries && pEntries[Beg].nLeaves == pCut0->nLeaves && pEntries[Beg].Truth == Truth1; Beg++ )
                {
                    Emap_PackEntry_t * pEntry1 = &pEntries[Beg];
                    Emap_Best_t * pBest1 = &pMaps[pEntry1->ObjId].Best[pEntry1->Phase];
                    Emap_Best_t OldBest0, OldBest1;
                    float AreaCur;
                    int m, fSameLeaves = 1;
                    for ( m = 0; m < pCut0->nLeaves; m++ )
                        if ( pEntry1->Leaves[m] != pCut0->Leaves[m] )
                            fSameLeaves = 0;
                    if ( !fSameLeaves )
                        break;
                    if ( pEntry1->ObjId == pEntry0->ObjId || pRefs[2 * pEntry1->ObjId + pEntry1->Phase] == 0 || pBest1->TwinObj >= 0 )
                        continue;
                    if ( Emap_ObjPairHasDirectDanglingRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    if ( Emap_ObjPairHasTfiRelation( pNtk, pEntry0->ObjId, pEntry1->ObjId ) )
                        continue;
                    OldBest0 = *pBest0;
                    OldBest1 = *pBest1;
                    Emap_MogApply( pMaps, pEntry0, pEntry1, pMog, s );
                    AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, pLib, pMio, &DelayCur );
                    if ( DelayCur <= DelayTarget + EMAP_DELAY_EPS && AreaCur < AreaBest - 0.001 )
                    {
                        AreaBest = AreaCur;
                        nApplied++;
                        Emap_ManComputeRefs( pNtk, pMaps, pLib, pRefs );
                        break;
                    }
                    *pBest0 = OldBest0;
                    *pBest1 = OldBest1;
                }
                if ( pBest0->TwinObj >= 0 )
                    break;
            }
            if ( pBest0->TwinObj >= 0 )
                break;
        }
    }
    *pAreaBest = AreaBest;
    ABC_FREE( pEntries );
    return nApplied;
}

static Abc_Ntk_t * Emap_ManBuildMappedNtk( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Mio_Library_t * pMio )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pObjNew, * pFanin;
    Vec_Int_t * vCopy;
    int i;
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_MAP, 1 );
    pNtkNew->pName = Extra_UtilStrsav( pNtk->pName ? pNtk->pName : "emap" );
    pNtkNew->pManFunc = pMio;
    vCopy = Vec_IntStartFull( 2 * Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        pObjNew = Abc_NtkCreatePi( pNtkNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObj), NULL );
        Vec_IntWriteEntry( vCopy, 2 * Abc_ObjId(pObj) + 0, Abc_ObjId(pObjNew) );
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        pObjNew = Abc_NtkCreatePo( pNtkNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObj), NULL );
        pFanin = Emap_ManBuildPhase_rec( pNtk, pNtkNew, pMaps, vCopy, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj), pLib );
        if ( pFanin == NULL )
        {
            Vec_IntFree( vCopy );
            Abc_NtkDelete( pNtkNew );
            return NULL;
        }
        Abc_ObjAddFanin( pObjNew, pFanin );
    }
    Vec_IntFree( vCopy );
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}

static float Emap_ManComputeActualMappedStats( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Mio_Library_t * pMio, double * pDelay )
{
    Abc_Ntk_t * pNtkNew = Emap_ManBuildMappedNtk( pNtk, pMaps, pLib, pMio );
    float Area;
    if ( pNtkNew == NULL )
    {
        *pDelay = EMAP_DOUBLE_LARGE;
        return EMAP_FLOAT_LARGE;
    }
    *pDelay = Abc_NtkDelayTrace( pNtkNew, NULL, NULL, 0 );
    Area = (float)Abc_NtkGetMappedArea( pNtkNew );
    Abc_NtkDelete( pNtkNew );
    return Area;
}

static int Emap_ManTryExactRecoveries( Abc_Ntk_t * pNtk, Emap_Obj_t * pMaps, Emap_Lib_t * pLib, Mio_Library_t * pMio, Emap_Tuples_t * pTuples, double * pRequired, int * pRefs, Emap_Best_t * pBase, Emap_Best_t * pSave, float * pAreaBest, double * pDelayBest, double DelayTarget )
{
    float AreaCur, AreaBase, AreaBest = EMAP_FLOAT_LARGE;
    double DelayCur, DelayBase, DelayBest = EMAP_DOUBLE_LARGE;
    int Mode, fHaveBest = 0, nChanges, nChangesBest = 0;
    for ( Mode = 0; Mode < 4; Mode++ )
    {
        int fRelax = Mode & 1;
        int fDropPhase = (Mode >> 1) & 1;
        Emap_ManRestoreBests( pNtk, pMaps, pBase );
        nChanges = Emap_ManRecoverExactArea( pNtk, pMaps, pLib, pTuples, pRequired, pRefs, 2, DelayTarget, fRelax, fDropPhase );
        AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, pLib, pMio, &DelayCur );
        if ( DelayCur <= DelayTarget + EMAP_DELAY_EPS && AreaCur < AreaBest - 0.001 )
        {
            AreaBest = AreaCur;
            DelayBest = DelayCur;
            nChangesBest = nChanges;
            Emap_ManSaveBests( pNtk, pMaps, pSave );
            fHaveBest = 1;
        }
    }
    if ( fHaveBest )
    {
        Emap_ManRestoreBests( pNtk, pMaps, pSave );
        *pAreaBest = AreaBest;
        *pDelayBest = DelayBest;
        return nChangesBest;
    }
    Emap_ManRestoreBests( pNtk, pMaps, pBase );
    AreaBase = Emap_ManComputeActualMappedStats( pNtk, pMaps, pLib, pMio, &DelayBase );
    Emap_ManSaveBests( pNtk, pMaps, pSave );
    *pAreaBest = AreaBase;
    *pDelayBest = DelayBase;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Creates a mapped network by cut matching AIG nodes.]

***********************************************************************/
Abc_Ntk_t * Emap_ManMapAigStructural( Abc_Ntk_t * pNtk, Mio_Library_t * pMio, int fUseMogs, int fAreaMode, int fVerbose )
{
    Emap_Lib_t Lib;
    Emap_Tuples_t Tuples;
    Emap_Obj_t * pMaps;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj;
    double * pRequired = NULL, DelayTarget = 0, DelayLimit = 0;
    Emap_Best_t * pBestSave = NULL;
    Emap_Best_t * pBestRound = NULL;
    Emap_Best_t * pBestTrial = NULL;
    float AreaBest, AreaCur;
    double DelayBest, DelayCur;
    int * pRefs = NULL;
    int i, r, nNodesMapped = 0, nNodesFailed = 0, nMogsPacked = 0, nMogsBest = 0, nExactChanges = 0, nExactChangesBest = 0;

    assert( Abc_NtkIsStrash(pNtk) );
    memset( &Tuples, 0, sizeof(Tuples) );
    if ( !Emap_LibPrepare( &Lib, pMio ) )
        return NULL;

    pMaps = ABC_CALLOC( Emap_Obj_t, Abc_NtkObjNumMax(pNtk) );
    Emap_NodeAddConstCut( &pMaps[Abc_ObjId(Abc_AigConst1(pNtk))] );
    pMaps[Abc_ObjId(Abc_AigConst1(pNtk))].Best[0].Arr = 0;
    pMaps[Abc_ObjId(Abc_AigConst1(pNtk))].Best[0].Flow = 0;
    pMaps[Abc_ObjId(Abc_AigConst1(pNtk))].Best[1].Arr = Lib.InvDelay;
    pMaps[Abc_ObjId(Abc_AigConst1(pNtk))].Best[1].Flow = Lib.InvArea;
    pMaps[Abc_ObjId(Abc_AigConst1(pNtk))].Best[1].fInv = 1;

    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Emap_NodeAddUnitCut( &pMaps[Abc_ObjId(pObj)], Abc_ObjId(pObj) );
        pMaps[Abc_ObjId(pObj)].Best[0].Arr = 0;
        pMaps[Abc_ObjId(pObj)].Best[0].Flow = 0;
        pMaps[Abc_ObjId(pObj)].Best[1].Arr = Lib.InvDelay;
        pMaps[Abc_ObjId(pObj)].Best[1].Flow = Lib.InvArea;
        pMaps[Abc_ObjId(pObj)].Best[1].fInv = 1;
    }

    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        Emap_NodeMergeCuts( pMaps, pObj );
        Emap_NodeMatch( pMaps, &pMaps[Abc_ObjId(pObj)], &Lib, pObj, NULL, NULL );
        if ( pMaps[Abc_ObjId(pObj)].Best[0].pGate )
            nNodesMapped++;
        else
            nNodesFailed++;
    }
    if ( nNodesFailed )
        printf( "Warning: %d AIG nodes did not receive a direct cut match.\n", nNodesFailed );
    if ( fUseMogs )
        Emap_ManComputeMogTuples( pNtk, pMaps, &Lib, &Tuples );

    pRequired = ABC_ALLOC( double, 2 * Abc_NtkObjNumMax(pNtk) );
    pRefs = ABC_ALLOC( int, 2 * Abc_NtkObjNumMax(pNtk) );
    pBestSave = ABC_ALLOC( Emap_Best_t, 2 * Abc_NtkObjNumMax(pNtk) );
    pBestRound = ABC_ALLOC( Emap_Best_t, 2 * Abc_NtkObjNumMax(pNtk) );
    pBestTrial = ABC_ALLOC( Emap_Best_t, 2 * Abc_NtkObjNumMax(pNtk) );
    DelayTarget = Emap_ManComputeRequired( pNtk, pMaps, &Lib, pRequired );
    DelayLimit = fAreaMode ? EMAP_DOUBLE_LARGE / 4 : DelayTarget;
    if ( fAreaMode )
        for ( i = 0; i < 2 * Abc_NtkObjNumMax(pNtk); i++ )
            pRequired[i] = EMAP_DOUBLE_LARGE;
    Emap_ManSaveBests( pNtk, pMaps, pBestTrial );
    nExactChangesBest = Emap_ManTryExactRecoveries( pNtk, pMaps, &Lib, pMio, fUseMogs ? &Tuples : NULL, pRequired, pRefs, pBestTrial, pBestRound, &AreaBest, &DelayBest, DelayLimit );
    Emap_ManSaveBests( pNtk, pMaps, pBestSave );
    Emap_ManSaveBests( pNtk, pMaps, pBestRound );
    if ( fUseMogs )
    {
        int fAcceptedThisRound = 0;
        if ( getenv("ABC_EMAP_TIMED_MOG") )
        {
            float AreaTimed = AreaBest;
            Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
            nMogsPacked = Emap_ManRecoverMogsTimed( pNtk, pMaps, &Lib, pMio, pRefs, DelayLimit, &AreaTimed );
            if ( getenv("ABC_EMAP_DEBUG_MOG") )
                printf( "ABC emap MOG timed trial initial: applied=%d area=%.2f best=%.2f\n", nMogsPacked, AreaTimed, AreaBest );
            if ( nMogsPacked && AreaTimed < AreaBest - 0.001 )
            {
                AreaBest = AreaTimed;
                nMogsBest = nMogsPacked;
                Emap_ManSaveBests( pNtk, pMaps, pBestSave );
                fAcceptedThisRound = 1;
            }
            Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
        }
        nMogsPacked = Emap_ManRecoverMogsExact( pNtk, pMaps, &Lib, pRequired, pRefs );
        AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, &Lib, pMio, &DelayCur );
        if ( getenv("ABC_EMAP_DEBUG_MOG") )
            printf( "ABC emap MOG exact trial initial: applied=%d area=%.2f delay=%.2f best=%.2f\n", nMogsPacked, AreaCur, DelayCur, AreaBest );
        if ( nMogsPacked && (fAreaMode || DelayCur <= DelayTarget + EMAP_DELAY_EPS) && AreaCur < AreaBest - 0.001 )
        {
            AreaBest = AreaCur;
            DelayBest = DelayCur;
            nMogsBest = nMogsPacked;
            Emap_ManSaveBests( pNtk, pMaps, pBestSave );
            fAcceptedThisRound = 1;
        }
        Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
        if ( getenv("ABC_EMAP_MFFC_EXACT") )
        {
            float AreaMffc = AreaBest;
            double DelayMffc = DelayBest;
            nMogsPacked = Emap_ManRecoverMogsExactMffc( pNtk, pMaps, &Lib, pMio, pRequired, pRefs, DelayLimit, &AreaMffc, &DelayMffc );
            if ( getenv("ABC_EMAP_DEBUG_MOG") )
                printf( "ABC emap MOG MFFC exact trial initial: applied=%d area=%.2f delay=%.2f best=%.2f\n", nMogsPacked, AreaMffc, DelayMffc, AreaBest );
            if ( nMogsPacked && AreaMffc < AreaBest - 0.001 )
            {
                AreaBest = AreaMffc;
                DelayBest = DelayMffc;
                nMogsBest = nMogsPacked;
                Emap_ManSaveBests( pNtk, pMaps, pBestSave );
                fAcceptedThisRound = 1;
            }
            Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
        }
        nMogsPacked = Emap_ManPackMogs( pNtk, pMaps, &Lib, pRequired, pRefs );
        AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, &Lib, pMio, &DelayCur );
        if ( getenv("ABC_EMAP_DEBUG_MOG") )
            printf( "ABC emap MOG pack trial initial: applied=%d area=%.2f delay=%.2f best=%.2f\n", nMogsPacked, AreaCur, DelayCur, AreaBest );
        if ( nMogsPacked && (fAreaMode || DelayCur <= DelayTarget + EMAP_DELAY_EPS) && AreaCur < AreaBest - 0.001 )
        {
            AreaBest = AreaCur;
            DelayBest = DelayCur;
            nMogsBest = nMogsPacked;
            Emap_ManSaveBests( pNtk, pMaps, pBestSave );
            fAcceptedThisRound = 1;
        }
        Emap_ManRestoreBests( pNtk, pMaps, fAcceptedThisRound ? pBestSave : pBestRound );
    }
    for ( r = 0; r < 6; r++ )
    {
        int nMogsCur;
        Emap_ManComputeRefs( pNtk, pMaps, &Lib, pRefs );
        if ( fAreaMode )
            for ( i = 0; i < 2 * Abc_NtkObjNumMax(pNtk); i++ )
                pRequired[i] = EMAP_DOUBLE_LARGE;
        else
            Emap_ManComputeRequiredTarget( pNtk, pMaps, &Lib, pRequired, pRefs, DelayTarget );
        nNodesMapped = nNodesFailed = 0;
        Abc_AigForEachAnd( pNtk, pObj, i )
        {
            Emap_NodeMatch( pMaps, &pMaps[Abc_ObjId(pObj)], &Lib, pObj, pRequired, pRefs );
            if ( fUseMogs && !getenv("ABC_EMAP_SKIP_MOG_AREA") )
                Emap_NodeMatchMogArea( pNtk, pMaps, &Lib, &Tuples, pRefs, pRequired, Abc_ObjId(pObj), 1 );
            if ( pMaps[Abc_ObjId(pObj)].Best[0].pGate )
                nNodesMapped++;
            else
                nNodesFailed++;
        }
        Emap_ManSaveBests( pNtk, pMaps, pBestTrial );
        AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, &Lib, pMio, &DelayCur );
        if ( fUseMogs && (fAreaMode || DelayCur <= DelayTarget + EMAP_DELAY_EPS) && AreaCur < AreaBest - 0.001 )
        {
            AreaBest = AreaCur;
            DelayBest = DelayCur;
            nMogsBest = Tuples.nAreaAccepts;
            nExactChangesBest = nExactChanges;
            Emap_ManSaveBests( pNtk, pMaps, pBestSave );
            Emap_ManSaveBests( pNtk, pMaps, pBestRound );
        }
        nExactChanges = Emap_ManTryExactRecoveries( pNtk, pMaps, &Lib, pMio, fUseMogs ? &Tuples : NULL, pRequired, pRefs, pBestTrial, pBestRound, &AreaCur, &DelayCur, DelayLimit );
        AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, &Lib, pMio, &DelayCur );
        if ( (fAreaMode || DelayCur <= DelayTarget + EMAP_DELAY_EPS) && AreaCur < AreaBest - 0.001 )
        {
            AreaBest = AreaCur;
            DelayBest = DelayCur;
            nMogsBest = 0;
            nExactChangesBest = nExactChanges;
            Emap_ManSaveBests( pNtk, pMaps, pBestSave );
            Emap_ManSaveBests( pNtk, pMaps, pBestRound );
        }
        if ( fUseMogs )
        {
            int fAcceptedThisRound = 0;
            if ( getenv("ABC_EMAP_TIMED_MOG") )
            {
                float AreaTimed = AreaBest;
                Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
                nMogsCur = Emap_ManRecoverMogsTimed( pNtk, pMaps, &Lib, pMio, pRefs, DelayLimit, &AreaTimed );
                if ( getenv("ABC_EMAP_DEBUG_MOG") )
                    printf( "ABC emap MOG timed trial round %d: applied=%d area=%.2f best=%.2f\n", r, nMogsCur, AreaTimed, AreaBest );
                if ( nMogsCur && AreaTimed < AreaBest - 0.001 )
                {
                    AreaBest = AreaTimed;
                    nMogsBest = nMogsCur;
                    nExactChangesBest = nExactChanges;
                    Emap_ManSaveBests( pNtk, pMaps, pBestSave );
                    fAcceptedThisRound = 1;
                }
                Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
            }
            nMogsCur = Emap_ManRecoverMogsExact( pNtk, pMaps, &Lib, pRequired, pRefs );
            AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, &Lib, pMio, &DelayCur );
            if ( getenv("ABC_EMAP_DEBUG_MOG") )
                printf( "ABC emap MOG exact trial round %d: applied=%d area=%.2f delay=%.2f best=%.2f\n", r, nMogsCur, AreaCur, DelayCur, AreaBest );
            if ( nMogsCur && (fAreaMode || DelayCur <= DelayTarget + EMAP_DELAY_EPS) && AreaCur < AreaBest - 0.001 )
            {
                AreaBest = AreaCur;
                DelayBest = DelayCur;
                nMogsBest = nMogsCur;
                nExactChangesBest = nExactChanges;
                Emap_ManSaveBests( pNtk, pMaps, pBestSave );
                fAcceptedThisRound = 1;
            }
            Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
            if ( getenv("ABC_EMAP_MFFC_EXACT") )
            {
                float AreaMffc = AreaBest;
                double DelayMffc = DelayBest;
                nMogsCur = Emap_ManRecoverMogsExactMffc( pNtk, pMaps, &Lib, pMio, pRequired, pRefs, DelayLimit, &AreaMffc, &DelayMffc );
                if ( getenv("ABC_EMAP_DEBUG_MOG") )
                    printf( "ABC emap MOG MFFC exact trial round %d: applied=%d area=%.2f delay=%.2f best=%.2f\n", r, nMogsCur, AreaMffc, DelayMffc, AreaBest );
                if ( nMogsCur && AreaMffc < AreaBest - 0.001 )
                {
                    AreaBest = AreaMffc;
                    DelayBest = DelayMffc;
                    nMogsBest = nMogsCur;
                    nExactChangesBest = nExactChanges;
                    Emap_ManSaveBests( pNtk, pMaps, pBestSave );
                    fAcceptedThisRound = 1;
                }
                Emap_ManRestoreBests( pNtk, pMaps, pBestRound );
            }
        nMogsCur = Emap_ManPackMogs( pNtk, pMaps, &Lib, pRequired, pRefs );
        AreaCur = Emap_ManComputeActualMappedStats( pNtk, pMaps, &Lib, pMio, &DelayCur );
        if ( getenv("ABC_EMAP_DEBUG_MOG") )
            printf( "ABC emap MOG pack trial round %d: applied=%d area=%.2f delay=%.2f best=%.2f\n", r, nMogsCur, AreaCur, DelayCur, AreaBest );
        if ( nMogsCur && (fAreaMode || DelayCur <= DelayTarget + EMAP_DELAY_EPS) && AreaCur < AreaBest - 0.001 )
            {
                AreaBest = AreaCur;
                DelayBest = DelayCur;
                nMogsBest = nMogsCur;
                nExactChangesBest = nExactChanges;
                Emap_ManSaveBests( pNtk, pMaps, pBestSave );
                fAcceptedThisRound = 1;
            }
            Emap_ManRestoreBests( pNtk, pMaps, fAcceptedThisRound ? pBestSave : pBestRound );
        }
    }
    Emap_ManRestoreBests( pNtk, pMaps, pBestSave );
    nMogsPacked = nMogsBest;
    if ( nNodesFailed )
        printf( "Warning: %d AIG nodes did not receive an area-recovery match.\n", nNodesFailed );

    pNtkNew = Emap_ManBuildMappedNtk( pNtk, pMaps, &Lib, pMio );
    if ( pNtkNew == NULL )
    {
        Emap_LibFree( &Lib );
        Emap_TuplesFree( &Tuples );
        ABC_FREE( pMaps );
        ABC_FREE( pRequired );
        ABC_FREE( pRefs );
        ABC_FREE( pBestSave );
        ABC_FREE( pBestRound );
        ABC_FREE( pBestTrial );
        return NULL;
    }

    if ( getenv("ABC_EMAP_DEBUG_MOG") )
    {
        printf( "ABC emap MOG area: tuples=%d calls=%d candidates=%d accepts=%d reject_twin=%d reject_required=%d reject_flow=%d\n",
            Tuples.nSize, Tuples.nAreaCalls, Tuples.nAreaCandidates, Tuples.nAreaAccepts,
            Tuples.nAreaRejectTwin, Tuples.nAreaRejectRequired, Tuples.nAreaRejectFlow );
        printf( "ABC emap MOG local exact: calls=%d candidates=%d accepts=%d reject_unused=%d reject_twin=%d reject_shared=%d reject_required=%d reject_area=%d\n",
            Tuples.nExactLocalCalls, Tuples.nExactLocalCandidates, Tuples.nExactLocalAccepts,
            Tuples.nExactLocalRejectUnused, Tuples.nExactLocalRejectTwin, Tuples.nExactLocalRejectShared,
            Tuples.nExactLocalRejectRequired, Tuples.nExactLocalRejectArea );
        printf( "ABC emap MOG local exact by arity: cand2=%d cand3=%d accept2=%d accept3=%d\n",
            Tuples.nExactLocalCand2, Tuples.nExactLocalCand3, Tuples.nExactLocalAccept2, Tuples.nExactLocalAccept3 );
    }

    if ( fVerbose )
        printf( "ABC-native emap mapped %d AIG nodes using %d GENLIB truth variants, %d MOG variants, %d exact-cover changes, and packed %d MOG pairs in %s mode with delay target %.2f.\n", nNodesMapped, Lib.nCells, Lib.nMogs, nExactChangesBest, nMogsPacked, fAreaMode ? "area" : "delay", DelayTarget );

    Emap_LibFree( &Lib );
    Emap_TuplesFree( &Tuples );
    ABC_FREE( pMaps );
    ABC_FREE( pRequired );
    ABC_FREE( pRefs );
    ABC_FREE( pBestSave );
    ABC_FREE( pBestRound );
    ABC_FREE( pBestTrial );
    return pNtkNew;
}

static Abc_Obj_t * Emap_ManBuildConst( Abc_Ntk_t * pNtkNew, Vec_Int_t * vCopy, int ObjId, int Phase )
{
    Abc_Obj_t * pObj;
    int Entry = Vec_IntEntry( vCopy, 2 * ObjId + Phase );
    if ( Entry >= 0 )
        return Abc_NtkObj( pNtkNew, Entry );
    pObj = Phase ? Abc_NtkCreateNodeConst0( pNtkNew ) : Abc_NtkCreateNodeConst1( pNtkNew );
    Vec_IntWriteEntry( vCopy, 2 * ObjId + Phase, Abc_ObjId(pObj) );
    return pObj;
}

static Abc_Obj_t * Emap_ManBuildPhase_rec( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkNew, Emap_Obj_t * pMaps, Vec_Int_t * vCopy, int ObjId, int Phase, Emap_Lib_t * pLib )
{
    Emap_Obj_t * pMap = &pMaps[ObjId];
    Emap_Best_t * pBest = &pMap->Best[Phase];
    Emap_Cut_t * pCut;
    Abc_Obj_t * pObj, * pFanin;
    int i, Entry = Vec_IntEntry( vCopy, 2 * ObjId + Phase );
    if ( Entry >= 0 )
        return Abc_NtkObj( pNtkNew, Entry );
    if ( ObjId == Abc_ObjId(Abc_AigConst1(pNtk)) )
        return Emap_ManBuildConst( pNtkNew, vCopy, ObjId, Phase );
    if ( Abc_ObjIsPi(Abc_NtkObj(pNtk, ObjId)) )
    {
        Entry = Vec_IntEntry( vCopy, 2 * ObjId + 0 );
        assert( Entry >= 0 );
        if ( Phase == 0 )
            return Abc_NtkObj( pNtkNew, Entry );
        pObj = Emap_ManCreateInv( pNtkNew, Abc_NtkObj(pNtkNew, Entry), pLib->pGateInv );
        Vec_IntWriteEntry( vCopy, 2 * ObjId + 1, Abc_ObjId(pObj) );
        return pObj;
    }
    if ( pBest->fInv )
    {
        pFanin = Emap_ManBuildPhase_rec( pNtk, pNtkNew, pMaps, vCopy, ObjId, !Phase, pLib );
        if ( pFanin == NULL )
            return NULL;
        pObj = Emap_ManCreateInv( pNtkNew, pFanin, pLib->pGateInv );
        Vec_IntWriteEntry( vCopy, 2 * ObjId + Phase, Abc_ObjId(pObj) );
        return pObj;
    }
    if ( pBest->TwinObj >= 0 )
    {
        Emap_Best_t * pTwinBest = &pMaps[pBest->TwinObj].Best[pBest->TwinPhase];
        Abc_Obj_t * pFanins[EMAP_LEAF_MAX];
        Abc_Obj_t * pObjTwin;
        int fCurrentFirst = pBest->pGate <= pTwinBest->pGate;
        pCut = &pMap->Cuts[pBest->Cut];
        for ( i = 0; i < pBest->nPins; i++ )
        {
            pFanins[i] = Emap_ManBuildPhase_rec( pNtk, pNtkNew, pMaps, vCopy, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i], pLib );
            if ( pFanins[i] == NULL )
                return NULL;
        }
        pObj = Abc_NtkCreateNode( pNtkNew );
        pObjTwin = Abc_NtkCreateNode( pNtkNew );
        pObj->pData = fCurrentFirst ? pBest->pGate : pTwinBest->pGate;
        pObjTwin->pData = fCurrentFirst ? pTwinBest->pGate : pBest->pGate;
        for ( i = 0; i < pBest->nPins; i++ )
        {
            Abc_ObjAddFanin( pObj, pFanins[i] );
            Abc_ObjAddFanin( pObjTwin, pFanins[i] );
        }
        if ( fCurrentFirst )
        {
            Vec_IntWriteEntry( vCopy, 2 * ObjId + Phase, Abc_ObjId(pObj) );
            Vec_IntWriteEntry( vCopy, 2 * pBest->TwinObj + pBest->TwinPhase, Abc_ObjId(pObjTwin) );
            return pObj;
        }
        Vec_IntWriteEntry( vCopy, 2 * pBest->TwinObj + pBest->TwinPhase, Abc_ObjId(pObj) );
        Vec_IntWriteEntry( vCopy, 2 * ObjId + Phase, Abc_ObjId(pObjTwin) );
        return pObjTwin;
    }
    if ( pBest->pGate == NULL )
        return NULL;
    pCut = &pMap->Cuts[pBest->Cut];
    pObj = Abc_NtkCreateNode( pNtkNew );
    pObj->pData = pBest->pGate;
    for ( i = 0; i < pBest->nPins; i++ )
    {
        pFanin = Emap_ManBuildPhase_rec( pNtk, pNtkNew, pMaps, vCopy, pCut->Leaves[pBest->PinToLeaf[i]], pBest->PinPhase[i], pLib );
        if ( pFanin == NULL )
            return NULL;
        Abc_ObjAddFanin( pObj, pFanin );
    }
    Vec_IntWriteEntry( vCopy, 2 * ObjId + Phase, Abc_ObjId(pObj) );
    return pObj;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
