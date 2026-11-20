/**CFile****************************************************************

  FileName    [emapMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Multi-output gate mapper.]

  Synopsis    [Cut-based mapper with priority cuts, cached matches, and
               two-output cells.]

  Date        [20 Oct 2026]

  Revision    [$Id: emapMap.c,v 1.00 2026/11/13 00:00:00 hfthra Exp $]

***********************************************************************/

#include "emap.h"

#include "base/abc/abc.h"
#include "map/mio/mio.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "map/scl/sclLib.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define EMP_LEAF_MAX   6
#define EMP_MOG_LEAF   3
#define EMP_MEM_MAX    32                   // sizes in a cell family
#define EMP_INF        ((double)1.0e20)
#define EMP_FINF       ((float)1.0e20)
#define EMP_FLOW_INF   ((double)1.0e300)    // area flows may grow beyond the float range
#define EMP_EPS        0.001

enum { EMP_NONE = 0, EMP_PI, EMP_CONST, EMP_INV, EMP_WIRE, EMP_GATE, EMP_MOG };

typedef struct Emp_Arc_t_ Emp_Arc_t;
typedef struct Emp_Fam_t_     Emp_Fam_t;
typedef struct Emp_Cell_t_    Emp_Cell_t;
typedef struct Emp_Mog_t_     Emp_Mog_t;
typedef struct Emp_MogKey_t_  Emp_MogKey_t;
typedef struct Emp_Cut_t_     Emp_Cut_t;
typedef struct Emp_Best_t_    Emp_Best_t;
typedef struct Emp_Tup_t_     Emp_Tup_t;
typedef struct Emp_Man_t_     Emp_Man_t;

// cell family: the sizes of one cell by increasing area; matches are made for
// the family and the size is chosen with the NLDM tables
struct Emp_Fam_t_
{
    int              nMem;
    int              nPins;
    int              nOuts;
    Mio_Gate_t *     pGates[EMP_MEM_MAX][2];
    signed char      Perm[EMP_MEM_MAX][EMP_LEAF_MAX];          // the gate pin of each family pin
    float            Area[EMP_MEM_MAX];
    float            Delay[EMP_MEM_MAX][2][EMP_LEAF_MAX];     // linear model: delay at zero load
    float            Slope[EMP_MEM_MAX][2][EMP_LEAF_MAX];     // linear model: delay per unit load
    float            Cin[EMP_MEM_MAX][EMP_LEAF_MAX];          // average of rise and fall capacitance
    float            CinD[EMP_MEM_MAX][EMP_LEAF_MAX];         // half of (fall - rise)
    SC_Timing *      pTime[EMP_MEM_MAX][2][EMP_LEAF_MAX];
    float            Gain[2][EMP_LEAF_MAX];                   // load-independent (gain-based) delay
};

// single-output library cell with a fixed pin-to-leaf assignment;
// pins of one class are interchangeable and get reassigned at match time
struct Emp_Cell_t_
{
    int              iFam;
    word             Truth;                     // function of the leaves (low 2^nPins bits)
    float            Area;
    int              nPins;
    int              nClasses;
    int              LeafSig;                   // bit j = phase of leaf j
    signed char      PinToLeaf[EMP_LEAF_MAX];
    signed char      PinPhase[EMP_LEAF_MAX];    // phase of the leaf feeding the pin
    signed char      ClassBeg[EMP_LEAF_MAX];
    signed char      ClassSize[EMP_LEAF_MAX];
    signed char      ClassPins[EMP_LEAF_MAX];   // pins of each class, by increasing delay
    float            Delay[EMP_LEAF_MAX];       // load-independent pin delay of the family
};

// two-output library cell with a fixed pin-to-leaf assignment
struct Emp_Mog_t_
{
    int              iFam;
    word             Truth[2];
    float            Area;
    int              nPins;
    int              LeafSig;
    signed char      PinToLeaf[EMP_LEAF_MAX];
    signed char      PinPhase[EMP_LEAF_MAX];
    float            Delay[2][EMP_LEAF_MAX];    // load-independent pin delays of the family
};

struct Emp_MogKey_t_
{
    word             Truth0;                    // function of the first root
    word             Truth1;                    // function of the second root
    int              nPins;
    int              iMog;
    int              fSwap;                     // the first root uses output 1
};

struct Emp_Cut_t_
{
    word             Truth;                     // 6-variable truth table
    word             Sign;
    float            Delay;                     // ranking estimate
    float            Flow;                      // ranking estimate
    int              iCell[2];                  // first matching cell for each phase
    int              nCell[2];
    int              fUseless;
    int              nLeaves;
    int              Leaves[EMP_LEAF_MAX];
};

struct Emp_Best_t_
{
    Mio_Gate_t *     pGate;
    int              iFam;                      // family of the cell (gate, MOG, inverter)
    int              iMem;                      // size in the family
    int              Out;                       // output of a two-output cell
    float *          pDelay;                    // pin delays (owned by the library)
    float *          pSlope;                    // pin delays per unit of output load
    float *          pCin;                      // pin capacitances
    SC_Timing **     ppTime;                    // timing arcs of the pins
    SC_Pair          ArrRF;                     // rise and fall arrival; Arr is the larger one
    SC_Pair          SlewRF;                    // rise and fall output transition
    float            Sens;                      // arrival increase per unit of added load
    double           Arr;
    double           Flow;
    float            Area;
    int              Type;
    int              iMog;
    int              Twin;
    int              TwinPhase;
    int              nPins;
    int              Leaves[EMP_LEAF_MAX];
    signed char      Phases[EMP_LEAF_MAX];
};

// a cut with up to three leaves shared by the two roots of a pair (or of a candidate pair)
struct Emp_Tup_t_
{
    int              Node[2];
    word             Truth[2];
    int              nLeaves;
    int              Leaves[EMP_MOG_LEAF];
    float            Gain;                      // estimated area saved by a two-output cell
    int              Id;                        // candidate index
    int              Next;                      // next tuple of the same pair
};

struct Emp_Man_t_
{
    Abc_Ntk_t *      pNtk;
    Mio_Library_t *  pMio;
    Emap_Par_t *     pPars;
    int              nObjs;
    // library
    Emp_Fam_t *      pFams;
    int              nFams;
    int              nFamCap;
    int              iCurFam;                   // the family whose matches are being added
    int              iFamInv;                   // the inverter family
    float            InvArea;
    float            InvGain;                   // load-independent delay of the inverter
    Emp_Cell_t *     pCells;                    // single-output matches, grouped by function
    int              nCells;
    int              nCellCap;
    int              nCellsAll;                 // the number before removing dominated matches
    int *            pGroupSize;                // for the first cell of a group
    float *          pGroupArea;
    float *          pGroupDelay;
    int *            pHash;                     // the first cells of the groups by function
    int              nHashMask;
    Emp_Mog_t *      pMogs;                     // two-output matches
    int              nMogs;
    int              nMogCap;
    int              nMogsAll;                  // the number before removing duplicates
    Emp_MogKey_t *   pMogKeys;                  // two-output matches by the pair of functions
    int              nMogKeys;
    // NLDM timing
    SC_Lib *         pScl;
    int              fNldm;
    int              fNldmDelay;                // NLDM timing under a delay target
    int              fGainMode;                 // match with the load-independent delays
    float            Slew;                      // input transition of the library delays
    float            LoadAvg;                   // typical pin load
    float            PoLoad;
    float *          pLoad;                     // load of each node phase (average of rise and fall)
    float *          pLoadD;                    // half of (fall - rise) load of each node phase
    float            SensK;                     // scales the load sensitivity (2 also covers the slower
                                                // transition of the loaded node)
    int              fNoShift;                  // add loads without arrival updates
    // cuts
    Emp_Cut_t *      pCuts;
    int              nCuts;
    int              nCutCap;
    int *            pCutBeg;
    int *            pCutNum;
    Emp_Cut_t *      pCutSet;
    // cover
    Emp_Best_t *     pBest;                     // implementations of the node phases
    int *            pRefs;
    char *           pImpl;
    float *          pEst;                      // fanout estimates of area flow
    int              nRound;                    // area-flow rounds blended into the estimates
    double *         pReq;
    double           DelayTarget;
    double           Guard;                     // fraction of the target kept as margin for load changes
    Emp_Best_t *     pGood;                     // the smallest cover meeting the target (or the fastest one)
    float            AreaGood;
    double           DelayGood;                 // fastest cover delay while no cover meets the target
    // pairs and the processing order
    Emp_Tup_t *      pTups;
    int              nTups;
    int              nTupCap;
    int *            pPartner;
    int *            pTupFirst;
    char *           pCoPlace;                  // the roots of the pair can be placed next to each other
    int *            pOrder;
    int              nOrder;
    int *            pPos;                      // position in the order
    char *           pMark;
    char *           pPend;
    int *            pTrav;
    int              nTravId;
    Vec_Int_t *      vTemp;
    Vec_Int_t *      vSaved;                    // nodes between the roots retimed by Emp_PairCheckBetween()
    double *         pArrSave;                  // their arrival times before
    // incremental timing: after each decision, the changed nodes are retimed with their fanout cones
    int              fIncr;                     // incremental timing is on
    int              fTrack;                    // record the changed nodes
    int              fImplOnly;                 // time only the phases in the cover
    Vec_Int_t *      vDirty;                    // changed nodes
    Vec_Wec_t *      vFans;                     // fanouts of the nodes in the cover (a superset)
    Vec_Int_t *      vHeap;                     // nodes to retime, in topological order
    char *           pInQ;                      // node is in the heap
    char *           pPoDrv;                    // node phase drives an output
    double *         pPoArr;                    // its arrival after the last accepted decision
    Emp_Arc_t *      pArcs;                     // cached arcs of the cover (EMP_LEAF_MAX per node phase)
    SC_Pair *        pCommit;                   // arrival and transition of each phase at the last propagation
    Vec_Int_t *      vPoTouched;                // output phases retimed by the last propagation
    double           nRetimed;                  // number of retimed nodes
    double           RetimeLimit;               // retiming budget of the current round
    int              fIncrOff;                  // budget used up: no incremental timing from now on
    // statistics
    int              nCands;
    int              nPairs;
    int              nPairsCo;
    abctime          clkStart;
};

static inline Emp_Cut_t *  Emp_ObjCuts( Emp_Man_t * p, int i )          { return p->pCuts + p->pCutBeg[i];              }
static inline Emp_Best_t * Emp_ObjBest( Emp_Man_t * p, int i, int f )   { return p->pBest + 2 * i + f;                  }
static inline double       Emp_ObjArr( Emp_Man_t * p, int i, int f )    { return p->pBest[2 * i + f].Arr;               }
static inline float        Emp_ObjEst( Emp_Man_t * p, int i, int f )    { return p->pEst[2 * i + f];                    }
static inline double       Emp_ObjFlowRef( Emp_Man_t * p, int i, int f ){ return p->pBest[2 * i + f].Flow / p->pEst[2 * i + f]; }
static inline int          Emp_ObjIsUsed( Emp_Man_t * p, int i )        { return p->pImpl[2 * i] || p->pImpl[2 * i + 1]; }
static inline int          Emp_ObjIsAnd( Emp_Man_t * p, int i )         { return Abc_AigNodeIsAnd( Abc_NtkObj(p->pNtk, i) ); }

static inline float        Emp_ObjLoad( Emp_Man_t * p, int i, int f )   { return p->pLoad[2 * i + f];                    }
static inline void Emp_BestSetArr( Emp_Best_t * pB, double Arr )
{
    pB->Arr = Arr;
    pB->ArrRF.rise = pB->ArrRF.fall = (float)Arr;
    pB->SlewRF.rise = pB->SlewRF.fall = 0;
}
static inline void Emp_BestShiftArr( Emp_Best_t * pB, double Shift )
{
    pB->Arr += Shift;
    pB->ArrRF.rise += (float)Shift;
    pB->ArrRF.fall += (float)Shift;
}
static inline void Emp_BestSetTiming( Emp_Best_t * pB, SC_Pair * pArr, SC_Pair * pSlew, float Sens )
{
    pB->ArrRF  = *pArr;
    pB->SlewRF = *pSlew;
    pB->Sens   = Sens;
    pB->Arr    = Abc_MaxFloat( pArr->rise, pArr->fall );
}
// propagates the arrival through a timing arc; without Liberty data, uses the linear model
static inline void Emp_ArcEval( SC_Timing * pTime, float Delay, float Slope, Emp_Best_t * pIn, float Shift, float Load, float LoadD, SC_Pair * pArr, SC_Pair * pSlew )
{
    SC_Pair ArrIn, LoadP;
    if ( pTime == NULL )
    {
        float a = (float)pIn->Arr + Shift + Delay + Slope * Load;
        pArr->rise = Abc_MaxFloat( pArr->rise, a );
        pArr->fall = Abc_MaxFloat( pArr->fall, a );
        return;
    }
    ArrIn.rise = pIn->ArrRF.rise + Shift;
    ArrIn.fall = pIn->ArrRF.fall + Shift;
    LoadP.rise = Load - LoadD;
    LoadP.fall = Load + LoadD;
    Scl_LibPinArrival( pTime, &ArrIn, &pIn->SlewRF, &LoadP, pArr, pSlew );
}
// timing arc of the cover with its delays and transitions cached for the input transition and load
struct Emp_Arc_t_
{
    SC_Timing *      pTime;
    SC_Pair          SlewIn;
    SC_Pair          Load;
    float            Delay[4];                  // rise from rise, fall from fall, rise from fall, fall from rise
    SC_Pair          SlewOut;
};
static inline void Emp_ArcEvalCached( Emp_Arc_t * pC, SC_Timing * pTime, Emp_Best_t * pIn, float Load, float LoadD, SC_Pair * pArr, SC_Pair * pSlew )
{
    SC_Pair LoadP;
    int fPos = pTime->tsense == sc_ts_Pos || pTime->tsense == sc_ts_Non;
    int fNeg = pTime->tsense == sc_ts_Neg || pTime->tsense == sc_ts_Non;
    LoadP.rise = Load - LoadD;
    LoadP.fall = Load + LoadD;
    if ( pC->pTime != pTime || pC->SlewIn.rise != pIn->SlewRF.rise || pC->SlewIn.fall != pIn->SlewRF.fall || pC->Load.rise != LoadP.rise || pC->Load.fall != LoadP.fall )
    {
        pC->pTime = pTime; pC->SlewIn = pIn->SlewRF; pC->Load = LoadP;
        pC->SlewOut.rise = pC->SlewOut.fall = 0;
        if ( fPos )
        {
            pC->Delay[0] = Scl_LibLookup( &pTime->pCellRise, pIn->SlewRF.rise, LoadP.rise );
            pC->Delay[1] = Scl_LibLookup( &pTime->pCellFall, pIn->SlewRF.fall, LoadP.fall );
            pC->SlewOut.rise = Abc_MaxFloat( pC->SlewOut.rise, Scl_LibLookup(&pTime->pRiseTrans, pIn->SlewRF.rise, LoadP.rise) );
            pC->SlewOut.fall = Abc_MaxFloat( pC->SlewOut.fall, Scl_LibLookup(&pTime->pFallTrans, pIn->SlewRF.fall, LoadP.fall) );
        }
        if ( fNeg )
        {
            pC->Delay[2] = Scl_LibLookup( &pTime->pCellRise, pIn->SlewRF.fall, LoadP.rise );
            pC->Delay[3] = Scl_LibLookup( &pTime->pCellFall, pIn->SlewRF.rise, LoadP.fall );
            pC->SlewOut.rise = Abc_MaxFloat( pC->SlewOut.rise, Scl_LibLookup(&pTime->pRiseTrans, pIn->SlewRF.fall, LoadP.rise) );
            pC->SlewOut.fall = Abc_MaxFloat( pC->SlewOut.fall, Scl_LibLookup(&pTime->pFallTrans, pIn->SlewRF.rise, LoadP.fall) );
        }
    }
    if ( fPos )
    {
        pArr->rise = Abc_MaxFloat( pArr->rise, pIn->ArrRF.rise + pC->Delay[0] );
        pArr->fall = Abc_MaxFloat( pArr->fall, pIn->ArrRF.fall + pC->Delay[1] );
    }
    if ( fNeg )
    {
        pArr->rise = Abc_MaxFloat( pArr->rise, pIn->ArrRF.fall + pC->Delay[2] );
        pArr->fall = Abc_MaxFloat( pArr->fall, pIn->ArrRF.rise + pC->Delay[3] );
    }
    pSlew->rise = Abc_MaxFloat( pSlew->rise, pC->SlewOut.rise );
    pSlew->fall = Abc_MaxFloat( pSlew->fall, pC->SlewOut.fall );
}
// evaluates arc k of the implementation of (i, f) in the cover; with incremental timing, the lookups are cached
static inline void Emp_ArcEvalCover( Emp_Man_t * p, int i, int f, int k, SC_Timing * pTime, float Delay, float Slope, Emp_Best_t * pIn, SC_Pair * pArr, SC_Pair * pSlew )
{
    int e = 2 * i + f;
    if ( p->pArcs && pTime )
        Emp_ArcEvalCached( p->pArcs + e * EMP_LEAF_MAX + k, pTime, pIn, p->pLoad[e], p->pLoadD[e], pArr, pSlew );
    else
        Emp_ArcEval( pTime, Delay, Slope, pIn, 0, p->pLoad[e], p->pLoadD[e], pArr, pSlew );
}
// delay of an arc: the latest output arrival minus the latest input arrival
static inline double Emp_ArcDelayMax( SC_Timing * pTime, float Delay, float Slope, Emp_Best_t * pIn, float Load, float LoadD )
{
    SC_Pair ArrOut = { 0.0, 0.0 }, SlewOut = { 0.0, 0.0 }, LoadP;
    if ( pTime == NULL )
        return Delay + Slope * Load;
    LoadP.rise = Load - LoadD;
    LoadP.fall = Load + LoadD;
    ArrOut.rise = ArrOut.fall = -1e30f;
    Scl_LibPinArrival( pTime, &pIn->ArrRF, &pIn->SlewRF, &LoadP, &ArrOut, &SlewOut );
    return Abc_MaxFloat( ArrOut.rise, ArrOut.fall ) - Abc_MaxFloat( pIn->ArrRF.rise, pIn->ArrRF.fall );
}
// size of the inverter producing phase f of node i (the smallest if there is no inverter)
static inline int Emp_InvMem( Emp_Man_t * p, int i, int f )
{
    Emp_Best_t * pB = p->pBest + 2 * i + f;
    return pB->Type == EMP_INV ? pB->iMem : 0;
}
static inline float Emp_InvCin( Emp_Man_t * p, int iMem ) { return p->pFams[p->iFamInv].Cin[iMem][0]; }
static inline float Emp_InvCinD( Emp_Man_t * p, int iMem ) { return p->pFams[p->iFamInv].CinD[iMem][0]; }
// half of (fall - rise) capacitance of pin k of the implementation
static inline float Emp_BestCinD( Emp_Man_t * p, Emp_Best_t * pB, int k )
{
    return p->pFams[pB->iFam].CinD[pB->iMem][k];
}
// the other output (2 * node + phase) of a two-output cell if it is in the cover, else -1
static inline int Emp_BestTwinUsed( Emp_Man_t * p, Emp_Best_t * pB )
{
    int e = 2 * pB->Twin + pB->TwinPhase;
    return pB->Type == EMP_MOG && p->pImpl[e] ? e : -1;
}
// returns 1 if (i, f) is the second output in the cover of a two-output cell
static inline int Emp_ObjIsTwinSecond( Emp_Man_t * p, int i, int f )
{
    int e = Emp_BestTwinUsed( p, Emp_ObjBest(p, i, f) );
    return e >= 0 && e < 2 * i + f;
}
// delay of the inverter producing phase f from phase !f
static inline double Emp_InvDelay( Emp_Man_t * p, int i, int f )
{
    Emp_Fam_t * pFam = p->pFams + p->iFamInv;
    int m = Emp_InvMem( p, i, f );
    if ( p->fGainMode )
        return p->InvGain;
    return Emp_ArcDelayMax( pFam->pTime[m][0][0], pFam->Delay[m][0][0], pFam->Slope[m][0][0], p->pBest + 2 * i + !f, p->pLoad[2 * i + f], p->pLoadD[2 * i + f] );
}
// sets the arrival of the inverter output from the other phase
static inline void Emp_InvTiming( Emp_Man_t * p, int i, int f, Emp_Best_t * pB )
{
    Emp_Fam_t * pFam = p->pFams + p->iFamInv;
    SC_Pair Arr = { 0.0, 0.0 }, Slew = { 0.0, 0.0 };
    int m = pB->iMem;
    if ( p->fGainMode || pFam->pTime[m][0][0] == NULL )
    {
        double Delay = p->fGainMode ? p->InvGain : pFam->Delay[m][0][0] + pFam->Slope[m][0][0] * p->pLoad[2 * i + f];
        Emp_BestSetArr( pB, p->pBest[2 * i + !f].Arr + Delay );
        pB->Sens = pFam->Slope[m][0][0];
        return;
    }
    Emp_ArcEvalCover( p, i, f, 0, pFam->pTime[m][0][0], pFam->Delay[m][0][0], pFam->Slope[m][0][0], Emp_ObjBest(p, i, !f), &Arr, &Slew );
    Emp_BestSetTiming( pB, &Arr, &Slew, pFam->Slope[m][0][0] );
}
static inline double Emp_PinDelay( Emp_Man_t * p, Emp_Best_t * pB, int k, float Load, float LoadD )
{
    return Emp_ArcDelayMax( pB->ppTime[k], pB->pDelay[k], pB->pSlope[k], p->pBest + 2 * pB->Leaves[k] + pB->Phases[k], Load, LoadD );
}

static inline void Emp_CoverCopy( Emp_Man_t * p, Emp_Best_t * pTo, Emp_Best_t * pFrom ) { memcpy( pTo, pFrom, sizeof(Emp_Best_t) * 2 * p->nObjs ); }
static inline word Emp_TruthMask( int nVars ) { return nVars == 6 ? ~(word)0 : (((word)1) << (1 << nVars)) - 1; }

static inline void Emp_TravStart( Emp_Man_t * p )             { p->nTravId++;                                  }
static inline int  Emp_TravIsCur( Emp_Man_t * p, int i )      { return p->pTrav[i] == p->nTravId;              }
static inline void Emp_TravSetCur( Emp_Man_t * p, int i )     { p->pTrav[i] = p->nTravId;                      }

static float Emp_ObjRef_rec( Emp_Man_t * p, int i, int f, int fRef );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Library preparation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// function of the leaves of a gate whose pin i is fed by leaf pPinToLeaf[i] in phase pPinPhase[i]
static word Emp_TruthPermutePhase( word Truth, int nVars, int * pPinToLeaf, int * pPinPhase )
{
    word Res = 0;
    int m, i, mPins;
    for ( m = 0; m < (1 << nVars); m++ )
    {
        for ( mPins = i = 0; i < nVars; i++ )
            if ( ((m >> pPinToLeaf[i]) & 1) ^ pPinPhase[i] )
                mPins |= 1 << i;
        if ( (Truth >> mPins) & 1 )
            Res |= ((word)1) << m;
    }
    return Res;
}
// delay of a timing arc at the library slew and the given load (average of rise and fall)
static float Emp_SclArcDelay( Emp_Man_t * p, SC_Timing * pTime, float Load )
{
    SC_Pair ArrIn = { 0.0, 0.0 }, SlewIn, LoadIn, ArrOut = { 0.0, 0.0 }, SlewOut = { 0.0, 0.0 };
    SlewIn.rise = SlewIn.fall = p->Slew;
    LoadIn.rise = LoadIn.fall = Load;
    Scl_LibPinArrival( pTime, &ArrIn, &SlewIn, &LoadIn, &ArrOut, &SlewOut );
    return 0.5 * ArrOut.rise + 0.5 * ArrOut.fall;
}
// linear pin delays and pin capacitances of a gate, from the Liberty cell of the same name if there is one
static void Emp_LibGateTiming( Emp_Man_t * p, Mio_Gate_t * pGate, float * pDelay, float * pSlope, float * pCin, float * pCinD, SC_Timing ** ppTime )
{
    Mio_Pin_t * pPin;
    SC_Cell * pCell = NULL;
    SC_Pin * pPinSc;
    int k = 0, i, j, iOut = -1, iCell;
    Mio_GateForEachPin( pGate, pPin )
    {
        pDelay[k] = (float)Mio_PinReadDelayBlockMax( pPin );
        pSlope[k] = pCin[k] = pCinD[k] = 0;
        ppTime[k] = NULL;
        k++;
    }
    if ( p->fNldm && (iCell = Abc_SclCellFind(p->pScl, Mio_GateReadName(pGate))) >= 0 )
    {
        pCell = SC_LibCell( p->pScl, iCell );
        SC_CellForEachPinOut( pCell, pPinSc, j )
            if ( !strcmp(pPinSc->pName, Mio_GateReadOutName(pGate)) )
                iOut = j - pCell->n_inputs;
    }
    if ( iOut >= 0 )
    {
        float D[EMP_LEAF_MAX], S[EMP_LEAF_MAX], C[EMP_LEAF_MAX], CD[EMP_LEAF_MAX], L1 = p->LoadAvg, L2 = 4 * p->LoadAvg, d1, d2;
        SC_Timing * T[EMP_LEAF_MAX];
        k = 0;
        Mio_GateForEachPin( pGate, pPin )
        {
            SC_Timing * pTime;
            for ( i = 0; i < pCell->n_inputs; i++ )
                if ( !strcmp(SC_CellPinName(pCell, i), Mio_PinReadName(pPin)) )
                    break;
            if ( i == pCell->n_inputs || (pTime = Scl_CellPinOutTime(pCell, iOut, i)) == NULL )
                return;
            // the line through the delays at one and four times the average pin load
            d1 = Emp_SclArcDelay( p, pTime, L1 );
            d2 = Emp_SclArcDelay( p, pTime, L2 );
            S[k] = (d2 - d1) / (L2 - L1);
            D[k] = Abc_MaxFloat( 0, d1 - S[k] * L1 );
            C[k] = SC_CellPinCap( pCell, i );
            CD[k] = 0.5f * (SC_CellPin(pCell, i)->fall_cap - SC_CellPin(pCell, i)->rise_cap);
            T[k++] = pTime;
        }
        for ( i = 0; i < k; i++ )
            pDelay[i] = D[i], pSlope[i] = S[i], pCin[i] = C[i], pCinD[i] = CD[i], ppTime[i] = T[i];
    }
}
static word Emp_GateTruth( Mio_Gate_t * pGate, int nPins )
{
    return Mio_GateReadTruth(pGate) & Emp_TruthMask(nPins);
}
// adds a match of a gate with the given pin-to-leaf assignment and pin phases
static void Emp_LibAddCell( Emp_Man_t * p, int nPins, int * pPinToLeaf, int * pPinPhase, int * pPinClass, word Truth )
{
    Emp_Fam_t * pFam = p->pFams + p->iCurFam;
    Emp_Cell_t * pCell;
    int i, k, m, nUsed = 0;
    if ( p->nCells == p->nCellCap )
    {
        p->nCellCap = p->nCellCap ? 2 * p->nCellCap : 1024;
        p->pCells = ABC_REALLOC( Emp_Cell_t, p->pCells, p->nCellCap );
    }
    pCell = p->pCells + p->nCells++;
    memset( pCell, 0, sizeof(Emp_Cell_t) );
    pCell->iFam  = p->iCurFam;
    pCell->nPins = nPins;
    pCell->Truth = Truth;
    pCell->Area  = pFam->Area[0];
    for ( i = 0; i < nPins; i++ )
    {
        pCell->PinToLeaf[i] = (signed char)pPinToLeaf[i];
        pCell->PinPhase[i]  = (signed char)pPinPhase[i];
        pCell->Delay[i]     = pFam->Gain[0][i];
        if ( pPinPhase[i] )
            pCell->LeafSig |= 1 << pPinToLeaf[i];
    }
    for ( i = 0; i < nPins; i++ )
    {
        int Beg = nUsed;
        if ( pPinClass[i] != i )
            continue;
        for ( k = i; k < nPins; k++ )
            if ( pPinClass[k] == i )
                pCell->ClassPins[nUsed++] = (signed char)k;
        // order the pins of the class by increasing delay
        for ( k = Beg + 1; k < nUsed; k++ )
            for ( m = k; m > Beg && pCell->Delay[(int)pCell->ClassPins[m]] < pCell->Delay[(int)pCell->ClassPins[m-1]]; m-- )
                ABC_SWAP( signed char, pCell->ClassPins[m], pCell->ClassPins[m-1] );
        pCell->ClassBeg[pCell->nClasses] = (signed char)Beg;
        pCell->ClassSize[pCell->nClasses++] = (signed char)(nUsed - Beg);
    }
    assert( nUsed == nPins );
}
// enumerates pin-to-leaf assignments where pins of one class feed increasing leaves
static void Emp_LibPermute_rec( Emp_Man_t * p, word Truth, int nPins, int iPin, int * pPinToLeaf, int * pUsed, int * pPinClass, int * pPinPrev )
{
    int i, k, Phase, PinPhase[EMP_LEAF_MAX];
    if ( iPin == nPins )
    {
        for ( Phase = 0; Phase < (1 << nPins); Phase++ )
        {
            for ( k = 0; k < nPins; k++ )
                PinPhase[k] = (Phase >> k) & 1;
            Emp_LibAddCell( p, nPins, pPinToLeaf, PinPhase, pPinClass, Emp_TruthPermutePhase(Truth, nPins, pPinToLeaf, PinPhase) );
        }
        return;
    }
    for ( i = 0; i < nPins; i++ )
    {
        if ( pUsed[i] )
            continue;
        if ( pPinPrev[iPin] >= 0 && i < pPinToLeaf[pPinPrev[iPin]] )
            continue;
        pUsed[i] = 1;
        pPinToLeaf[iPin] = i;
        Emp_LibPermute_rec( p, Truth, nPins, iPin + 1, pPinToLeaf, pUsed, pPinClass, pPinPrev );
        pUsed[i] = 0;
    }
}
// adds a match of a two-output cell
static void Emp_LibAddMog( Emp_Man_t * p, Mio_Gate_t * pGate0, Mio_Gate_t * pGate1, int nPins, int * pPinToLeaf, int * pPinPhase )
{
    Emp_Fam_t * pFam = p->pFams + p->iCurFam;
    Emp_Mog_t * pMog;
    int i;
    if ( p->nMogs == p->nMogCap )
    {
        p->nMogCap = p->nMogCap ? 2 * p->nMogCap : 128;
        p->pMogs = ABC_REALLOC( Emp_Mog_t, p->pMogs, p->nMogCap );
    }
    pMog = p->pMogs + p->nMogs++;
    memset( pMog, 0, sizeof(Emp_Mog_t) );
    pMog->iFam     = p->iCurFam;
    pMog->nPins    = nPins;
    pMog->Area     = pFam->Area[0];
    pMog->Truth[0] = Emp_TruthPermutePhase( Emp_GateTruth(pGate0, nPins), nPins, pPinToLeaf, pPinPhase );
    pMog->Truth[1] = Emp_TruthPermutePhase( Emp_GateTruth(pGate1, nPins), nPins, pPinToLeaf, pPinPhase );
    for ( i = 0; i < nPins; i++ )
    {
        pMog->PinToLeaf[i] = (signed char)pPinToLeaf[i];
        pMog->PinPhase[i]  = (signed char)pPinPhase[i];
        pMog->Delay[0][i]  = pFam->Gain[0][i];
        pMog->Delay[1][i]  = pFam->Gain[1][i];
        if ( pPinPhase[i] )
            pMog->LeafSig |= 1 << pPinToLeaf[i];
    }
}
static void Emp_LibMogPermute_rec( Emp_Man_t * p, Mio_Gate_t * pGate0, Mio_Gate_t * pGate1, int nPins, int iPin, int * pPinToLeaf, int * pUsed )
{
    int i, k, Phase, PinPhase[EMP_LEAF_MAX];
    if ( iPin == nPins )
    {
        for ( Phase = 0; Phase < (1 << nPins); Phase++ )
        {
            for ( k = 0; k < nPins; k++ )
                PinPhase[k] = (Phase >> k) & 1;
            Emp_LibAddMog( p, pGate0, pGate1, nPins, pPinToLeaf, PinPhase );
        }
        return;
    }
    for ( i = 0; i < nPins; i++ )
    {
        if ( pUsed[i] )
            continue;
        pUsed[i] = 1;
        pPinToLeaf[iPin] = i;
        Emp_LibMogPermute_rec( p, pGate0, pGate1, nPins, iPin + 1, pPinToLeaf, pUsed );
        pUsed[i] = 0;
    }
}
static int Emp_CellCompare( Emp_Cell_t * p0, Emp_Cell_t * p1 )
{
    if ( p0->nPins != p1->nPins )
        return p0->nPins - p1->nPins;
    if ( p0->Truth != p1->Truth )
        return p0->Truth < p1->Truth ? -1 : 1;
    return 0;
}
static int Emp_CellCompareSort( const void * a, const void * b )
{
    Emp_Cell_t * p0 = (Emp_Cell_t *)a, * p1 = (Emp_Cell_t *)b;
    int Res = Emp_CellCompare( p0, p1 );
    if ( Res )
        return Res;
    // inside a group, by area
    if ( p0->Area != p1->Area )
        return p0->Area < p1->Area ? -1 : 1;
    return 0;
}
// per-leaf view of a cell: phase, class representative, and class delays by rank
static void Emp_CellLeafInfo( Emp_Cell_t * pCell, int * pPhase, int * pRep, float * pDelay )
{
    int c, j, m, Leaves[EMP_LEAF_MAX];
    for ( c = 0; c < pCell->nClasses; c++ )
    {
        int Beg = pCell->ClassBeg[c], Size = pCell->ClassSize[c];
        for ( j = 0; j < Size; j++ )
            Leaves[j] = pCell->PinToLeaf[(int)pCell->ClassPins[Beg + j]];
        for ( j = 1; j < Size; j++ )
            for ( m = j; m > 0 && Leaves[m] < Leaves[m-1]; m-- )
                ABC_SWAP( int, Leaves[m], Leaves[m-1] );
        for ( j = 0; j < Size; j++ )
        {
            int Pin = pCell->ClassPins[Beg + j];
            pRep[Leaves[j]]   = Leaves[0];
            pDelay[Leaves[j]] = pCell->Delay[Pin];
        }
    }
    for ( j = 0; j < pCell->nPins; j++ )
        pPhase[(int)pCell->PinToLeaf[j]] = pCell->PinPhase[j];
}
// returns 1 if cell A is never worse than cell B for any leaf arrival times (load-independent delays)
static int Emp_CellDominates( Emp_Cell_t * pA, Emp_Cell_t * pB, int fTieWins )
{
    int PhA[EMP_LEAF_MAX], PhB[EMP_LEAF_MAX], RepA[EMP_LEAF_MAX], RepB[EMP_LEAF_MAX], j, fBetter = 0;
    float DelA[EMP_LEAF_MAX], DelB[EMP_LEAF_MAX];
    if ( pA->Area > pB->Area + 1e-6 )
        return 0;
    fBetter |= pA->Area < pB->Area - 1e-6;
    Emp_CellLeafInfo( pA, PhA, RepA, DelA );
    Emp_CellLeafInfo( pB, PhB, RepB, DelB );
    for ( j = 0; j < pA->nPins; j++ )
    {
        if ( PhA[j] != PhB[j] || RepA[j] != RepB[j] || DelA[j] > DelB[j] + 1e-6 )
            return 0;
        fBetter |= DelA[j] < DelB[j] - 1e-6;
    }
    return fBetter || fTieWins;
}
static int Emp_MogKeyCompare( const void * a, const void * b )
{
    Emp_MogKey_t * p0 = (Emp_MogKey_t *)a, * p1 = (Emp_MogKey_t *)b;
    if ( p0->nPins != p1->nPins )
        return p0->nPins - p1->nPins;
    if ( p0->Truth0 != p1->Truth0 )
        return p0->Truth0 < p1->Truth0 ? -1 : 1;
    if ( p0->Truth1 != p1->Truth1 )
        return p0->Truth1 < p1->Truth1 ? -1 : 1;
    if ( p0->iMog != p1->iMog )
        return p0->iMog - p1->iMog;
    return p0->fSwap - p1->fSwap;
}
static inline int Emp_HashKey( Emp_Man_t * p, int nPins, word Truth )
{
    word Key = (Truth + (word)nPins) * ABC_CONST(0x9E3779B97F4A7C15);
    return (int)(Key >> 40) & p->nHashMask;
}
static void Emp_LibBuildHash( Emp_Man_t * p )
{
    int i, nGroups = 0, Size = 1;
    for ( i = 0; i < p->nCells; i += p->pGroupSize[i] )
        nGroups++;
    while ( Size < 2 * nGroups + 16 )
        Size <<= 1;
    p->nHashMask = Size - 1;
    p->pHash = ABC_FALLOC( int, Size );
    for ( i = 0; i < p->nCells; i += p->pGroupSize[i] )
    {
        int Key = Emp_HashKey( p, p->pCells[i].nPins, p->pCells[i].Truth );
        while ( p->pHash[Key] >= 0 )
            Key = (Key + 1) & p->nHashMask;
        p->pHash[Key] = i;
    }
}
// returns the first cell matching the function or -1
static inline int Emp_LibLookup( Emp_Man_t * p, int nPins, word Truth, int * pnCells )
{
    int Key = Emp_HashKey( p, nPins, Truth );
    for ( ; p->pHash[Key] >= 0; Key = (Key + 1) & p->nHashMask )
    {
        Emp_Cell_t * pCell = p->pCells + p->pHash[Key];
        if ( pCell->nPins == nPins && pCell->Truth == Truth )
        {
            *pnCells = p->pGroupSize[p->pHash[Key]];
            return p->pHash[Key];
        }
    }
    *pnCells = 0;
    return -1;
}
// returns the first key matching the pair of functions or -1
static int Emp_LibMogLookup( Emp_Man_t * p, int nPins, word Truth0, word Truth1, int * pnKeys )
{
    int Beg = 0, End = p->nMogKeys, Mid, i;
    Emp_MogKey_t Key;
    Key.nPins = nPins; Key.Truth0 = Truth0; Key.Truth1 = Truth1; Key.iMog = -1; Key.fSwap = -1;
    while ( Beg < End )
    {
        Mid = (Beg + End) >> 1;
        if ( Emp_MogKeyCompare( p->pMogKeys + Mid, &Key ) < 0 )
            Beg = Mid + 1;
        else
            End = Mid;
    }
    for ( i = Beg; i < p->nMogKeys; i++ )
        if ( p->pMogKeys[i].nPins != nPins || p->pMogKeys[i].Truth0 != Truth0 || p->pMogKeys[i].Truth1 != Truth1 )
            break;
    *pnKeys = i - Beg;
    return i > Beg ? Beg : -1;
}
// returns 1 if the gates have the same function and pin names
static int Emp_GatesSame( Mio_Gate_t * pA, Mio_Gate_t * pB )
{
    Mio_Pin_t * pPinA, * pPinB;
    int nPins = Mio_GateReadPinNum( pA );
    if ( nPins != Mio_GateReadPinNum(pB) || Emp_GateTruth(pA, nPins) != Emp_GateTruth(pB, nPins) )
        return 0;
    if ( strcmp(Mio_GateReadOutName(pA), Mio_GateReadOutName(pB)) )
        return 0;
    for ( pPinA = Mio_GateReadPins(pA), pPinB = Mio_GateReadPins(pB); pPinA && pPinB; pPinA = Mio_PinReadNext(pPinA), pPinB = Mio_PinReadNext(pPinB) )
        if ( strcmp(Mio_PinReadName(pPinA), Mio_PinReadName(pPinB)) )
            return 0;
    return 1;
}
// finds pPerm[k], the pin of gate B taking pin k of gate A, making the functions equal;
// returns 0 if there is none
static int Emp_GatesPerm_rec( word TruthA, word TruthB, int nPins, int k, int * pUsed, signed char * pPerm )
{
    int j, x, y, b;
    if ( k == nPins )
    {
        for ( x = 0; x < (1 << nPins); x++ )
        {
            for ( y = b = 0; b < nPins; b++ )
                if ( (x >> b) & 1 )
                    y |= 1 << pPerm[b];
            if ( ((TruthA >> x) & 1) != ((TruthB >> y) & 1) )
                return 0;
        }
        return 1;
    }
    for ( j = 0; j < nPins; j++ )
    {
        if ( pUsed[j] )
            continue;
        pUsed[j] = 1; pPerm[k] = (signed char)j;
        if ( Emp_GatesPerm_rec(TruthA, TruthB, nPins, k + 1, pUsed, pPerm) )
            return 1;
        pUsed[j] = 0;
    }
    return 0;
}
static int Emp_GatesPerm( Mio_Gate_t * pA, Mio_Gate_t * pB, signed char * pPerm )
{
    int Used[EMP_LEAF_MAX] = {0}, nPins = Mio_GateReadPinNum( pA ), k;
    word TruthA, TruthB;
    for ( k = 0; k < EMP_LEAF_MAX; k++ )
        pPerm[k] = (signed char)k;
    if ( Emp_GatesSame(pA, pB) )
        return 1;
    if ( nPins != Mio_GateReadPinNum(pB) || nPins > 6 )
        return 0;
    TruthA = Emp_GateTruth( pA, nPins );
    TruthB = Emp_GateTruth( pB, nPins );
    if ( Abc_TtCountOnes(TruthA & Abc_Tt6Mask(1 << nPins)) != Abc_TtCountOnes(TruthB & Abc_Tt6Mask(1 << nPins)) )
        return 0;
    return Emp_GatesPerm_rec( TruthA, TruthB, nPins, 0, Used, pPerm );
}
// appends a size to the family (pPerm = NULL keeps the pin order)
static void Emp_FamAddMember( Emp_Fam_t * pFam, Mio_Gate_t * pGate0, Mio_Gate_t * pGate1, signed char * pPerm )
{
    int k;
    for ( k = 0; k < EMP_LEAF_MAX; k++ )
        pFam->Perm[pFam->nMem][k] = pPerm ? pPerm[k] : (signed char)k;
    pFam->pGates[pFam->nMem][0] = pGate0;
    pFam->pGates[pFam->nMem][1] = pGate1;
    pFam->Area[pFam->nMem++] = (float)Mio_GateReadArea( pGate0 );
}
// adds the gate (or two-output cell) to its family; returns the family
static int Emp_LibAddToFamily( Emp_Man_t * p, Mio_Gate_t * pGate0, Mio_Gate_t * pGate1 )
{
    signed char Perm[EMP_LEAF_MAX];
    Emp_Fam_t * pFam;
    int f;
    // with NLDM timing, the sizes of a cell share a family; otherwise every gate is a family
    for ( f = 0; p->fNldm && f < p->nFams; f++ )
    {
        pFam = p->pFams + f;
        if ( pFam->nOuts != (pGate1 ? 2 : 1) || pFam->nMem == EMP_MEM_MAX )
            continue;
        // sizes of a single-output cell may order the pins differently
        if ( pGate1 ? Emp_GatesSame(pFam->pGates[0][0], pGate0) && Emp_GatesSame(pFam->pGates[0][1], pGate1) : Emp_GatesPerm(pFam->pGates[0][0], pGate0, Perm) )
        {
            Emp_FamAddMember( pFam, pGate0, pGate1, pGate1 ? NULL : Perm );
            return f;
        }
    }
    if ( p->nFams == p->nFamCap )
    {
        p->nFamCap = p->nFamCap ? 2 * p->nFamCap : 256;
        p->pFams = ABC_REALLOC( Emp_Fam_t, p->pFams, p->nFamCap );
    }
    pFam = p->pFams + p->nFams;
    memset( pFam, 0, sizeof(Emp_Fam_t) );
    pFam->nPins = Mio_GateReadPinNum( pGate0 );
    pFam->nOuts = pGate1 ? 2 : 1;
    Emp_FamAddMember( pFam, pGate0, pGate1, NULL );
    return p->nFams++;
}
// orders the sizes by area (pFirst, if given, goes first) and computes their timing
static void Emp_LibFinishFamily( Emp_Man_t * p, Emp_Fam_t * pFam, Mio_Gate_t * pFirst )
{
    int m, n, o, k;
    for ( m = 1; m < pFam->nMem; m++ )
        for ( n = m; n > 0; n-- )
        {
            int fSwap = pFam->pGates[n][0] == pFirst || (pFam->pGates[n-1][0] != pFirst && pFam->Area[n] < pFam->Area[n-1]);
            if ( !fSwap )
                break;
            ABC_SWAP( Mio_Gate_t *, pFam->pGates[n][0], pFam->pGates[n-1][0] );
            ABC_SWAP( Mio_Gate_t *, pFam->pGates[n][1], pFam->pGates[n-1][1] );
            ABC_SWAP( float, pFam->Area[n], pFam->Area[n-1] );
            for ( k = 0; k < EMP_LEAF_MAX; k++ )
                ABC_SWAP( signed char, pFam->Perm[n][k], pFam->Perm[n-1][k] );
        }
    // the family uses the pins of the first size: member m takes family pin k on Perm[m][Perm0^-1[k]]
    if ( pFam->nOuts == 1 )
    {
        signed char Inv0[EMP_LEAF_MAX], New[EMP_MEM_MAX][EMP_LEAF_MAX];
        for ( k = 0; k < pFam->nPins; k++ )
            Inv0[(int)pFam->Perm[0][k]] = (signed char)k;
        for ( m = 0; m < pFam->nMem; m++ )
            for ( k = 0; k < pFam->nPins; k++ )
                New[m][k] = pFam->Perm[m][(int)Inv0[k]];
        for ( m = 0; m < pFam->nMem; m++ )
            memcpy( pFam->Perm[m], New[m], pFam->nPins );
    }
    for ( m = 0; m < pFam->nMem; m++ )
        for ( o = 0; o < pFam->nOuts; o++ )
        {
            float D[EMP_LEAF_MAX], S[EMP_LEAF_MAX], C[EMP_LEAF_MAX], CD[EMP_LEAF_MAX];
            SC_Timing * T[EMP_LEAF_MAX];
            Emp_LibGateTiming( p, pFam->pGates[m][o], D, S, C, CD, T );
            for ( k = 0; k < pFam->nPins; k++ )
            {
                int j = pFam->Perm[m][k];
                pFam->Delay[m][o][k] = D[j]; pFam->Slope[m][o][k] = S[j];
                pFam->Cin[m][k] = C[j];      pFam->pTime[m][o][k] = T[j];
                pFam->CinD[m][k] = CD[j];
            }
        }
    // load-independent delays: average over the sizes, each driving its own input capacitance
    for ( o = 0; o < pFam->nOuts; o++ )
        for ( k = 0; k < pFam->nPins; k++ )
        {
            float Sum = 0;
            for ( m = 0; m < pFam->nMem; m++ )
                Sum += pFam->pTime[m][o][k] ? Emp_SclArcDelay( p, pFam->pTime[m][o][k], pFam->Cin[m][k] ) : pFam->Delay[m][o][k];
            pFam->Gain[o][k] = p->fNldm ? Sum / pFam->nMem : pFam->Delay[0][o][k];
        }
}
// builds the families; with NLDM timing, all inverters form one family
static void Emp_LibBuildFamilies( Emp_Man_t * p, Mio_Gate_t * pGateInv )
{
    Mio_Gate_t * pGate;
    int i, nPins;
    p->InvArea = (float)Mio_GateReadArea( pGateInv );
    p->iFamInv = Emp_LibAddToFamily( p, pGateInv, NULL );
    Mio_LibraryForEachGate( p->pMio, pGate )
        if ( pGate != pGateInv && Mio_GateReadPinNum(pGate) == 1 && Mio_GateReadTwin(pGate) == NULL && p->fNldm &&
             Emp_GateTruth(pGate, 1) == Emp_GateTruth(pGateInv, 1) && p->pFams[p->iFamInv].nMem < EMP_MEM_MAX )
            Emp_FamAddMember( p->pFams + p->iFamInv, pGate, NULL, NULL );
    Mio_LibraryForEachGate( p->pMio, pGate )
    {
        Mio_Gate_t * pTwin = Mio_GateReadTwin( pGate );
        nPins = Mio_GateReadPinNum( pGate );
        if ( nPins < 2 || nPins > EMP_LEAF_MAX )
            continue;
        if ( pTwin != NULL && (pGate > pTwin || Mio_GateReadPinNum(pTwin) != nPins || nPins > EMP_MOG_LEAF) )
            continue;
        Emp_LibAddToFamily( p, pGate, pTwin );
    }
    for ( i = 0; i < p->nFams; i++ )
        Emp_LibFinishFamily( p, p->pFams + i, i == p->iFamInv ? pGateInv : NULL );
    p->InvGain = p->pFams[p->iFamInv].Gain[0][0];
}
// classes of interchangeable pins: the class of a pin is its first pin; PinPrev is the previous pin of the class
static void Emp_LibPinClasses( word Truth, int nPins, int * pPinClass, int * pPinPrev )
{
    int i, k;
    Truth = Abc_Tt6Stretch( Truth, nPins );
    for ( i = 0; i < nPins; i++ )
    {
        pPinClass[i] = i;
        pPinPrev[i] = -1;
        for ( k = 0; k < i; k++ )
            if ( pPinClass[k] == k && Abc_Tt6SwapVars(Truth, k, i) == Truth )
            {
                pPinClass[i] = k;
                break;
            }
        for ( k = i - 1; k >= 0; k-- )
            if ( pPinClass[k] == pPinClass[i] )
            {
                pPinPrev[i] = k;
                break;
            }
    }
}
// matches of the smallest size of each family
static void Emp_LibBuildMatches( Emp_Man_t * p )
{
    int PinToLeaf[EMP_LEAF_MAX], Used[EMP_LEAF_MAX], PinClass[EMP_LEAF_MAX], PinPrev[EMP_LEAF_MAX];
    for ( p->iCurFam = 0; p->iCurFam < p->nFams; p->iCurFam++ )
    {
        Mio_Gate_t * pGate = p->pFams[p->iCurFam].pGates[0][0], * pTwin = p->pFams[p->iCurFam].pGates[0][1];
        int nPins = Mio_GateReadPinNum( pGate );
        if ( nPins < 2 )
            continue;
        memset( Used, 0, sizeof(Used) );
        if ( pTwin != NULL )
            Emp_LibMogPermute_rec( p, pGate, pTwin, nPins, 0, PinToLeaf, Used );
        else
        {
            Emp_LibPinClasses( Emp_GateTruth(pGate, nPins), nPins, PinClass, PinPrev );
            Emp_LibPermute_rec( p, Emp_GateTruth(pGate, nPins), nPins, 0, PinToLeaf, Used, PinClass, PinPrev );
        }
    }
}
// sorts the matches into groups of the same function, removes dominated ones (without NLDM timing), and builds the lookup table
static void Emp_LibFinishCells( Emp_Man_t * p )
{
    int i, j, k, n;
    p->nCellsAll = p->nCells;
    qsort( p->pCells, (size_t)p->nCells, sizeof(Emp_Cell_t), Emp_CellCompareSort );
    if ( !p->fNldm )
    {
        Emp_Cell_t * pNew = ABC_ALLOC( Emp_Cell_t, p->nCells );
        int nNew = 0, Beg, End;
        for ( Beg = 0; Beg < p->nCells; Beg = End )
        {
            for ( End = Beg + 1; End < p->nCells && !Emp_CellCompare(p->pCells + Beg, p->pCells + End); End++ );
            for ( i = Beg; i < End; i++ )
            {
                for ( j = Beg; j < End; j++ )
                    if ( j != i && Emp_CellDominates(p->pCells + j, p->pCells + i, j < i) )
                        break;
                if ( j == End )
                    pNew[nNew++] = p->pCells[i];
            }
        }
        ABC_FREE( p->pCells );
        p->pCells = pNew;
        p->nCells = nNew;
    }
    // the smallest area and delay of each group (stored at its first cell)
    p->pGroupSize  = ABC_CALLOC( int, p->nCells + 1 );
    p->pGroupArea  = ABC_CALLOC( float, p->nCells + 1 );
    p->pGroupDelay = ABC_CALLOC( float, p->nCells + 1 );
    for ( i = 0; i < p->nCells; i = j )
    {
        for ( j = i + 1; j < p->nCells && !Emp_CellCompare(p->pCells + i, p->pCells + j); j++ );
        p->pGroupSize[i]  = j - i;
        p->pGroupArea[i]  = EMP_FINF;
        p->pGroupDelay[i] = EMP_FINF;
        for ( k = i; k < j; k++ )
        {
            float DelayMax = 0;
            for ( n = 0; n < p->pCells[k].nPins; n++ )
                DelayMax = Abc_MaxFloat( DelayMax, p->pCells[k].Delay[n] );
            p->pGroupArea[i]  = Abc_MinFloat( p->pGroupArea[i], p->pCells[k].Area );
            p->pGroupDelay[i] = Abc_MinFloat( p->pGroupDelay[i], DelayMax );
        }
    }
    Emp_LibBuildHash( p );
}
// removes the duplicated matches of two-output cells and builds the lookup table
static void Emp_LibFinishMogs( Emp_Man_t * p )
{
    int i, j, k, n;
    p->nMogsAll = p->nMogs;
    for ( i = n = 0; i < p->nMogs; i++ )
    {
        Emp_Mog_t * pA = p->pMogs + i;
        for ( j = 0; j < n; j++ )
        {
            Emp_Mog_t * pB = p->pMogs + j;
            float DA[2][EMP_LEAF_MAX], DB[2][EMP_LEAF_MAX];
            if ( pA->iFam != pB->iFam || pA->Truth[0] != pB->Truth[0] || pA->Truth[1] != pB->Truth[1] || pA->LeafSig != pB->LeafSig )
                continue;
            // the same delays by leaf
            for ( k = 0; k < pA->nPins; k++ )
            {
                DA[0][(int)pA->PinToLeaf[k]] = pA->Delay[0][k]; DA[1][(int)pA->PinToLeaf[k]] = pA->Delay[1][k];
                DB[0][(int)pB->PinToLeaf[k]] = pB->Delay[0][k]; DB[1][(int)pB->PinToLeaf[k]] = pB->Delay[1][k];
            }
            for ( k = 0; k < pA->nPins; k++ )
                if ( DA[0][k] != DB[0][k] || DA[1][k] != DB[1][k] )
                    break;
            if ( k == pA->nPins )
                break;
        }
        if ( j == n )
            p->pMogs[n++] = *pA;
    }
    p->nMogs = n;
    // each match is listed for both orders of its outputs
    p->pMogKeys = ABC_ALLOC( Emp_MogKey_t, 2 * p->nMogs + 1 );
    for ( i = 0; i < p->nMogs; i++ )
        for ( k = 0; k < 2; k++ )
        {
            Emp_MogKey_t * pKey = p->pMogKeys + p->nMogKeys++;
            pKey->nPins  = p->pMogs[i].nPins;
            pKey->Truth0 = p->pMogs[i].Truth[k];
            pKey->Truth1 = p->pMogs[i].Truth[!k];
            pKey->iMog   = i;
            pKey->fSwap  = k;
        }
    qsort( p->pMogKeys, (size_t)p->nMogKeys, sizeof(Emp_MogKey_t), Emp_MogKeyCompare );
}
// builds the families, the matches of their smallest sizes, and the lookup tables
static int Emp_LibPrepare( Emp_Man_t * p )
{
    Mio_Gate_t * pGateInv = Mio_LibraryReadInv( p->pMio );
    if ( pGateInv == NULL )
    {
        printf( "Cannot find inverter gate in the current GENLIB library.\n" );
        return 0;
    }
    Emp_LibBuildFamilies( p, pGateInv );
    Emp_LibBuildMatches( p );
    Emp_LibFinishCells( p );
    Emp_LibFinishMogs( p );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Cut enumeration with priority cuts.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// merges two sorted leaf sets; returns the number of leaves or -1 if there are more than nMax
static inline int Emp_CutMergeLeaves( int * pLeaves0, int nLeaves0, int * pLeaves1, int nLeaves1, int * pLeaves, int nMax )
{
    int i = 0, k = 0, nLeaves = 0;
    while ( i < nLeaves0 || k < nLeaves1 )
    {
        int Leaf;
        if ( k == nLeaves1 || (i < nLeaves0 && pLeaves0[i] < pLeaves1[k]) )
            Leaf = pLeaves0[i++];
        else if ( i == nLeaves0 || pLeaves1[k] < pLeaves0[i] )
            Leaf = pLeaves1[k++];
        else
            Leaf = pLeaves0[i++], k++;
        if ( nLeaves == nMax )
            return -1;
        pLeaves[nLeaves++] = Leaf;
    }
    return nLeaves;
}
static inline word Emp_CutSign( int * pLeaves, int nLeaves )
{
    word Sign = 0;
    int i;
    for ( i = 0; i < nLeaves; i++ )
        Sign |= ((word)1) << (pLeaves[i] & 63);
    return Sign;
}
static inline int Emp_CutIsContained( Emp_Cut_t * pSmall, Emp_Cut_t * pBig )
{
    int i, k;
    if ( pSmall->nLeaves > pBig->nLeaves || (pSmall->Sign & ~pBig->Sign) )
        return 0;
    for ( i = k = 0; i < pSmall->nLeaves; i++ )
    {
        while ( k < pBig->nLeaves && pBig->Leaves[k] < pSmall->Leaves[i] )
            k++;
        if ( k == pBig->nLeaves || pBig->Leaves[k] != pSmall->Leaves[i] )
            return 0;
        k++;
    }
    return 1;
}
static inline int Emp_CutCompare( Emp_Cut_t * a, Emp_Cut_t * b )
{
    if ( a->fUseless != b->fUseless )
        return a->fUseless - b->fUseless;
    if ( a->Delay < b->Delay - 0.005 ) return -1;
    if ( a->Delay > b->Delay + 0.005 ) return  1;
    if ( a->Flow  < b->Flow  - 0.005 ) return -1;
    if ( a->Flow  > b->Flow  + 0.005 ) return  1;
    return a->nLeaves - b->nLeaves;
}
// finds matches and computes the ranking estimates of a cut
static void Emp_CutEvaluate( Emp_Man_t * p, Emp_Cut_t * pCut )
{
    word Mask = Emp_TruthMask( pCut->nLeaves );
    double ArrMax = 0, LeafFlow = 0;
    float Area = EMP_FINF, Delay = EMP_FINF;
    int f, k;
    pCut->iCell[0] = pCut->iCell[1] = -1;
    pCut->nCell[0] = pCut->nCell[1] = 0;
    pCut->fUseless = 0;
    for ( k = 0; k < pCut->nLeaves; k++ )
    {
        int Leaf = pCut->Leaves[k];
        ArrMax   = Abc_MaxDouble( ArrMax, Abc_MinDouble(Emp_ObjArr(p, Leaf, 0), Emp_ObjArr(p, Leaf, 1)) );
        LeafFlow += Abc_MinDouble( Emp_ObjFlowRef(p, Leaf, 0), Emp_ObjFlowRef(p, Leaf, 1) );
    }
    if ( pCut->nLeaves < 2 )
    {
        pCut->Delay = (float)ArrMax;
        pCut->Flow  = (float)Abc_MinDouble( LeafFlow, 1.0e30 );
        return;
    }
    for ( f = 0; f < 2; f++ )
    {
        pCut->iCell[f] = Emp_LibLookup( p, pCut->nLeaves, f ? (~pCut->Truth & Mask) : (pCut->Truth & Mask), &pCut->nCell[f] );
        if ( pCut->iCell[f] < 0 )
            continue;
        Area  = Abc_MinFloat( Area, p->pGroupArea[pCut->iCell[f]] );
        Delay = Abc_MinFloat( Delay, p->pGroupDelay[pCut->iCell[f]] );
    }
    pCut->fUseless = (pCut->iCell[0] < 0 && pCut->iCell[1] < 0);
    pCut->Delay = pCut->fUseless ? EMP_FINF : (float)ArrMax + Delay;
    pCut->Flow  = pCut->fUseless ? EMP_FINF : (float)Abc_MinDouble( LeafFlow + Area, 1.0e30 );
}
// adds the cut to the sorted set; a dominated cut is kept if it has a match
// (the function over more leaves may have a better gate), a duplicate is not
static int Emp_CutSetInsert( Emp_Cut_t * pSet, int nSet, int nMax, Emp_Cut_t * pNew )
{
    int i, k;
    for ( i = 0; i < nSet; i++ )
        if ( (pNew->fUseless || pSet[i].nLeaves == pNew->nLeaves) && Emp_CutIsContained(pSet + i, pNew) )
            return nSet;
    for ( i = k = 0; i < nSet; i++ )
        if ( !pSet[i].fUseless || !Emp_CutIsContained(pNew, pSet + i) )
            pSet[k++] = pSet[i];
    nSet = k;
    for ( i = nSet; i > 0 && Emp_CutCompare(pNew, pSet + i - 1) < 0; i-- );
    if ( i >= nMax )
        return nSet;
    for ( k = Abc_MinInt(nSet, nMax - 1); k > i; k-- )
        pSet[k] = pSet[k-1];
    pSet[i] = *pNew;
    return Abc_MinInt( nSet + 1, nMax );
}
static void Emp_ObjAddCuts( Emp_Man_t * p, int iObj, Emp_Cut_t * pSet, int nSet )
{
    if ( p->nCuts + nSet > p->nCutCap )
    {
        while ( p->nCuts + nSet > p->nCutCap )
            p->nCutCap = p->nCutCap ? 2 * p->nCutCap : (1 << 16);
        p->pCuts = ABC_REALLOC( Emp_Cut_t, p->pCuts, p->nCutCap );
    }
    memcpy( p->pCuts + p->nCuts, pSet, sizeof(Emp_Cut_t) * nSet );
    p->pCutBeg[iObj] = p->nCuts;
    p->pCutNum[iObj] = nSet;
    p->nCuts += nSet;
}
static void Emp_CutSetUnit( Emp_Cut_t * pCut, int iObj )
{
    memset( pCut, 0, sizeof(Emp_Cut_t) );
    pCut->nLeaves   = 1;
    pCut->Leaves[0] = iObj;
    pCut->Truth     = s_Truths6[0];
    pCut->Sign      = Emp_CutSign( pCut->Leaves, 1 );
    pCut->iCell[0]  = pCut->iCell[1] = -1;
}
static void Emp_ObjComputeCuts( Emp_Man_t * p, Abc_Obj_t * pObj )
{
    int iObj = Abc_ObjId(pObj), iFan0 = Abc_ObjFaninId0(pObj), iFan1 = Abc_ObjFaninId1(pObj);
    word Mask0 = Abc_ObjFaninC0(pObj) ? ~(word)0 : 0, Mask1 = Abc_ObjFaninC1(pObj) ? ~(word)0 : 0;
    int nMax = p->pPars->nCutNum, nSet = 0, a, b, nLeaves;
    Emp_Cut_t New, * pSet = p->pCutSet;
    for ( a = 0; a < p->pCutNum[iFan0]; a++ )
    for ( b = 0; b < p->pCutNum[iFan1]; b++ )
    {
        Emp_Cut_t * pCut0 = Emp_ObjCuts(p, iFan0) + a;
        Emp_Cut_t * pCut1 = Emp_ObjCuts(p, iFan1) + b;
        word t0, t1;
        if ( Abc_TtCountOnes(pCut0->Sign | pCut1->Sign) > EMP_LEAF_MAX )
            continue;
        nLeaves = Emp_CutMergeLeaves( pCut0->Leaves, pCut0->nLeaves, pCut1->Leaves, pCut1->nLeaves, New.Leaves, EMP_LEAF_MAX );
        if ( nLeaves < 0 )
            continue;
        t0 = Abc_Tt6Expand( pCut0->Truth, pCut0->Leaves, pCut0->nLeaves, New.Leaves, nLeaves ) ^ Mask0;
        t1 = Abc_Tt6Expand( pCut1->Truth, pCut1->Leaves, pCut1->nLeaves, New.Leaves, nLeaves ) ^ Mask1;
        New.Truth   = t0 & t1;
        New.nLeaves = Abc_Tt6MinBase( &New.Truth, New.Leaves, nLeaves );
        New.Sign    = Emp_CutSign( New.Leaves, New.nLeaves );
        Emp_CutEvaluate( p, &New );
        nSet = Emp_CutSetInsert( pSet, nSet, nMax, &New );
    }
    Emp_CutSetUnit( pSet + nSet++, iObj );
    Emp_ObjAddCuts( p, iObj, pSet, nSet );
}

/**Function*************************************************************

  Synopsis    [Match records.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Emp_BestClean( Emp_Best_t * pB )
{
    memset( pB, 0, sizeof(Emp_Best_t) );
    pB->Type = EMP_NONE;
    pB->iMog = pB->Twin = pB->TwinPhase = -1;
    pB->Arr  = EMP_INF;
    pB->Flow = EMP_FLOW_INF;
}
static inline void Emp_BestCopyTiming( Emp_Best_t * pB, Emp_Best_t * pFrom )
{
    pB->Arr    = pFrom->Arr;
    pB->ArrRF  = pFrom->ArrRF;
    pB->SlewRF = pFrom->SlewRF;
    pB->Sens   = pFrom->Sens;
}
static inline void Emp_BestSetConst( Emp_Best_t * pB, int Value )
{
    Emp_BestClean( pB );
    pB->Type = EMP_CONST;
    pB->Phases[0] = (signed char)Value;
    Emp_BestSetArr( pB, 0 );
    pB->Flow = 0;
}
static inline void Emp_BestSetWire( Emp_Man_t * p, Emp_Best_t * pB, int Leaf, int Ph, double Flow )
{
    Emp_BestClean( pB );
    pB->Type      = EMP_WIRE;
    pB->nPins     = 1;
    pB->Leaves[0] = Leaf;
    pB->Phases[0] = (signed char)Ph;
    pB->Flow      = Flow;
    Emp_BestCopyTiming( pB, Emp_ObjBest(p, Leaf, Ph) );
}
// compares a match with pB: by arrival, then by flow (in area mode, by flow, then by arrival)
static inline int Emp_BestIsBetter( double Arr, double Flow, Emp_Best_t * pB, int fArea )
{
    double Cost0 = fArea ? Flow : Arr, Cost1 = fArea ? Arr : Flow;
    double Best0 = fArea ? pB->Flow : pB->Arr, Best1 = fArea ? pB->Arr : pB->Flow;
    // any match is better than none (flows of deep reconvergent logic may overflow)
    if ( pB->Type == EMP_NONE )
        return 1;
    if ( Cost0 < Best0 - 0.0001 )
        return 1;
    if ( Cost0 > Best0 + 0.0001 )
        return 0;
    return Cost1 < Best1 - 0.0001;
}
// compares the areas of two choices in exact area, then their arrival times
static inline int Emp_AreaIsBetter( double Area, double Arr, double AreaBest, double ArrBest )
{
    return Area < AreaBest - EMP_EPS || (Area < AreaBest + EMP_EPS && Arr < ArrBest - EMP_EPS);
}

/**Function*************************************************************

  Synopsis    [Arrival time of a cell on a cut at the given output load.]

  Description [Inside each class of interchangeable pins, the latest leaf
               goes to the fastest pin.  Writes the leaf and its phase for
               each pin and the timing of the output to pRes.  With
               fLeafLoad, the leaves are slowed down by the capacitance of
               the pins they drive.  Size iMem < 0 uses the load-independent
               delays of the cell.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// adds the arc from pin k of size m (output Out) of the family
static inline void Emp_FamPinArrival( Emp_Man_t * p, Emp_Fam_t * pFam, int m, int Out, int k, Emp_Best_t * pLeaf, float Load, int fLeafLoad, SC_Pair * pArr, SC_Pair * pSlew, float * pSens )
{
    float Prev = Abc_MaxFloat( pArr->rise, pArr->fall );
    Emp_ArcEval( pFam->pTime[m][Out][k], pFam->Delay[m][Out][k], pFam->Slope[m][Out][k], pLeaf, fLeafLoad ? p->SensK * pLeaf->Sens * pFam->Cin[m][k] : 0, Load, 0, pArr, pSlew );
    if ( Abc_MaxFloat(pArr->rise, pArr->fall) > Prev )
        *pSens = pFam->Slope[m][Out][k];
}
// writes the timing of the output to pRes (if given); returns the arrival
static inline double Emp_ArrivalResult( Emp_Best_t * pRes, int fLinear, double ArrLin, SC_Pair * pArr, SC_Pair * pSlew, float Sens )
{
    if ( pRes == NULL )
        return fLinear ? ArrLin : Abc_MaxFloat( pArr->rise, pArr->fall );
    if ( fLinear )
    {
        Emp_BestSetArr( pRes, ArrLin );
        pRes->Sens = 0;
    }
    else
        Emp_BestSetTiming( pRes, pArr, pSlew, Sens );
    return pRes->Arr;
}
static double Emp_CellArrival( Emp_Man_t * p, Emp_Cell_t * pCell, int * pCutLeaves, float Load, int fLeafLoad, int iMem, Emp_Best_t * pRes )
{
    Emp_Fam_t * pFam = p->pFams + pCell->iFam;
    SC_Pair Arr = { 0.0, 0.0 }, Slew = { 0.0, 0.0 };
    double ArrLin = 0;
    float Sens = 0;
    int c, j, n, m = Abc_MaxInt( iMem, 0 ), fLinear = iMem < 0 || !p->fNldm;
    for ( c = 0; c < pCell->nClasses; c++ )
    {
        int Beg = pCell->ClassBeg[c], Size = pCell->ClassSize[c], Leaf[EMP_LEAF_MAX];
        signed char Ph[EMP_LEAF_MAX];
        double LeafArr[EMP_LEAF_MAX];
        // the leaves of the class by decreasing arrival
        for ( j = 0; j < Size; j++ )
        {
            int Pin = pCell->ClassPins[Beg + j];
            Leaf[j]    = pCutLeaves[(int)pCell->PinToLeaf[Pin]];
            Ph[j]      = pCell->PinPhase[Pin];
            LeafArr[j] = Emp_ObjArr( p, Leaf[j], Ph[j] );
        }
        for ( j = 1; j < Size; j++ )
            for ( n = j; n > 0 && LeafArr[n] > LeafArr[n-1]; n-- )
            {
                ABC_SWAP( int, Leaf[n], Leaf[n-1] );
                ABC_SWAP( signed char, Ph[n], Ph[n-1] );
                ABC_SWAP( double, LeafArr[n], LeafArr[n-1] );
            }
        for ( j = 0; j < Size; j++ )
        {
            int Pin = pCell->ClassPins[Beg + j];
            pRes->Leaves[Pin] = Leaf[j];
            pRes->Phases[Pin] = Ph[j];
            if ( fLinear )
                ArrLin = Abc_MaxDouble( ArrLin, LeafArr[j] + pCell->Delay[Pin] );
            else
                Emp_FamPinArrival( p, pFam, m, 0, Pin, Emp_ObjBest(p, Leaf[j], Ph[j]), Load, fLeafLoad, &Arr, &Slew, &Sens );
        }
    }
    return Emp_ArrivalResult( pRes, fLinear, ArrLin, &Arr, &Slew, Sens );
}
// arrival of output Out of a two-output cell; the same conventions as Emp_CellArrival() (pRes may be NULL)
static double Emp_MogArrival( Emp_Man_t * p, Emp_Mog_t * pMog, int Out, int * pLeaves, float Load, int fLeafLoad, int iMem, Emp_Best_t * pRes )
{
    Emp_Fam_t * pFam = p->pFams + pMog->iFam;
    SC_Pair Arr = { 0.0, 0.0 }, Slew = { 0.0, 0.0 };
    double ArrLin = 0;
    float Sens = 0;
    int k, m = Abc_MaxInt( iMem, 0 ), fLinear = iMem < 0 || !p->fNldm;
    for ( k = 0; k < pMog->nPins; k++ )
    {
        Emp_Best_t * pLeaf = Emp_ObjBest( p, pLeaves[(int)pMog->PinToLeaf[k]], pMog->PinPhase[k] );
        if ( fLinear )
            ArrLin = Abc_MaxDouble( ArrLin, pLeaf->Arr + pMog->Delay[Out][k] );
        else
            Emp_FamPinArrival( p, pFam, m, Out, k, pLeaf, Load, fLeafLoad, &Arr, &Slew, &Sens );
    }
    return Emp_ArrivalResult( pRes, fLinear, ArrLin, &Arr, &Slew, Sens );
}
// returns 0 if the capacitance of the pins would push a leaf beyond its required time
static int Emp_LeavesLoadOk( Emp_Man_t * p, int * pLeaves, signed char * pPhases, float * pCin, int nPins )
{
    int k;
    if ( !p->fNldm )
        return 1;
    for ( k = 0; k < nPins; k++ )
    {
        int e = 2 * pLeaves[k] + pPhases[k];
        if ( p->pBest[e].Arr + p->SensK * p->pBest[e].Sens * pCin[k] > p->pReq[e] + EMP_EPS )
            return 0;
    }
    return 1;
}
// sets a gate with size m; pTim holds the pins and the timing computed by Emp_CellArrival()
static void Emp_BestSetGate( Emp_Man_t * p, Emp_Best_t * pB, Emp_Cell_t * pCell, int m, Emp_Best_t * pTim, double Flow )
{
    Emp_Fam_t * pFam = p->pFams + pCell->iFam;
    Emp_BestClean( pB );
    pB->Type   = EMP_GATE;
    pB->iFam   = pCell->iFam;
    pB->iMem   = m;
    pB->pGate  = pFam->pGates[m][0];
    pB->pDelay = pFam->Delay[m][0];
    pB->pSlope = pFam->Slope[m][0];
    pB->pCin   = pFam->Cin[m];
    pB->ppTime = pFam->pTime[m][0];
    pB->Area   = pFam->Area[m];
    pB->Flow   = Flow;
    pB->nPins  = pCell->nPins;
    memcpy( pB->Leaves, pTim->Leaves, sizeof(int) * pCell->nPins );
    memcpy( pB->Phases, pTim->Phases, sizeof(signed char) * pCell->nPins );
    Emp_BestCopyTiming( pB, pTim );
}
// sets an inverter of the smallest size driven by the other phase
static inline void Emp_BestSetInv( Emp_Man_t * p, int i, int f )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f ), * pO = Emp_ObjBest( p, i, !f );
    assert( pO->Type != EMP_INV && pO->Type != EMP_NONE );
    Emp_BestClean( pB );
    pB->Type = EMP_INV;
    pB->iFam = p->iFamInv;
    pB->iMem = 0;
    pB->pGate = p->pFams[p->iFamInv].pGates[0][0];
    Emp_InvTiming( p, i, f, pB );
    pB->Flow = pO->Flow + p->InvArea;
    pB->Area = p->InvArea;
}
// recomputes the timing of the implementations of the node (with fImplOnly, only of those in the cover)
static void Emp_ObjUpdateArr( Emp_Man_t * p, int i )
{
    int f, k;
    for ( f = 0; f < 2; f++ )
    {
        Emp_Best_t * pB = Emp_ObjBest( p, i, f );
        if ( p->fImplOnly && !p->pImpl[2 * i + f] )
            continue;
        if ( pB->Type == EMP_WIRE )
            Emp_BestCopyTiming( pB, Emp_ObjBest(p, pB->Leaves[0], pB->Phases[0]) );
        else if ( (pB->Type == EMP_GATE || pB->Type == EMP_MOG) && !p->fNldm )
        {
            double ArrD = 0;
            for ( k = 0; k < pB->nPins; k++ )
                ArrD = Abc_MaxDouble( ArrD, Emp_ObjArr(p, pB->Leaves[k], pB->Phases[k]) + pB->pDelay[k] + pB->pSlope[k] * Emp_ObjLoad(p, i, f) );
            Emp_BestSetArr( pB, ArrD );
            pB->Sens = 0;
        }
        else if ( pB->Type == EMP_GATE || pB->Type == EMP_MOG )
        {
            SC_Pair Arr = { 0.0, 0.0 }, Slew = { 0.0, 0.0 };
            float Sens = 0;
            for ( k = 0; k < pB->nPins; k++ )
            {
                float Prev = Abc_MaxFloat( Arr.rise, Arr.fall );
                Emp_ArcEvalCover( p, i, f, k, pB->ppTime[k], pB->pDelay[k], pB->pSlope[k], Emp_ObjBest(p, pB->Leaves[k], pB->Phases[k]), &Arr, &Slew );
                if ( Abc_MaxFloat(Arr.rise, Arr.fall) > Prev )
                    Sens = pB->pSlope[k];
            }
            Emp_BestSetTiming( pB, &Arr, &Slew, Sens );
        }
    }
    // the inverters after the phases driving them
    for ( f = 0; f < 2; f++ )
        if ( Emp_ObjBest(p, i, f)->Type == EMP_INV && !(p->fImplOnly && !p->pImpl[2 * i + f]) )
            Emp_InvTiming( p, i, f, Emp_ObjBest(p, i, f) );
}

/**Function*************************************************************

  Synopsis    [Matching of one node in delay or area-flow mode.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// area flow of a cell on a cut (independent of the pin assignment inside symmetry classes)
static inline double Emp_CellFlow( Emp_Man_t * p, Emp_Cell_t * pCell, int * pCutLeaves )
{
    double Flow = pCell->Area;
    int k;
    for ( k = 0; k < pCell->nPins; k++ )
        Flow += Emp_ObjFlowRef( p, pCutLeaves[(int)pCell->PinToLeaf[k]], pCell->PinPhase[k] );
    return Flow;
}
// tries a cell on a cut for one phase; with the NLDM tables, area mode takes the smallest
// size meeting the required time, delay mode the fastest size
static void Emp_ObjMatchCell( Emp_Man_t * p, Emp_Best_t * pB, Emp_Cell_t * pCell, int * pCutLeaves, float Load, double Req, int fArea, int fLeafLoad )
{
    Emp_Fam_t * pFam = p->pFams + pCell->iFam;
    double LeafFlow = Emp_CellFlow( p, pCell, pCutLeaves ) - pCell->Area, Flow;
    int fLinear = p->fGainMode || !p->fNldm;
    int m, mBest = -1, nMem = fLinear ? 1 : pFam->nMem;
    Emp_Best_t Cand, Best;
    Best.Arr = EMP_INF;
    for ( m = 0; m < nMem; m++ )
    {
        // in area mode, a larger flow cannot win
        Flow = pFam->Area[m] + LeafFlow;
        if ( fArea && pB->Type != EMP_NONE && Flow > pB->Flow + 0.0001 )
            break;
        Emp_CellArrival( p, pCell, pCutLeaves, Load, fLeafLoad, fLinear ? -1 : m, &Cand );
        if ( Cand.Arr > Req + EMP_EPS )
            continue;
        if ( fLeafLoad && fArea && !fLinear && !Emp_LeavesLoadOk(p, Cand.Leaves, Cand.Phases, pFam->Cin[m], pCell->nPins) )
            continue;
        if ( fArea || Cand.Arr < Best.Arr - 0.0001 )
            mBest = m, Best = Cand;
        if ( fArea )
            break;
    }
    if ( mBest < 0 )
        return;
    Flow = pFam->Area[mBest] + LeafFlow;
    if ( Emp_BestIsBetter(Best.Arr, Flow, pB, fArea) )
        Emp_BestSetGate( p, pB, pCell, mBest, &Best, Flow );
}
// the best matches of both phases of the node on its cuts under the required times pReq
static void Emp_ObjMatchCuts( Emp_Man_t * p, int iObj, double * pReq, int fArea, int fLeafLoad )
{
    Emp_Best_t * pB = Emp_ObjBest( p, iObj, 0 );
    Emp_Cut_t * pCut = Emp_ObjCuts( p, iObj );
    float Load[2];
    int c, f, n;
    // a phase without fanouts in the cover is matched for an estimated load
    for ( f = 0; f < 2; f++ )
        Load[f] = Emp_ObjLoad(p, iObj, f) > 0 ? Emp_ObjLoad(p, iObj, f) : p->LoadAvg * p->pEst[2 * iObj + f];
    Emp_BestClean( pB + 0 );
    Emp_BestClean( pB + 1 );
    for ( c = 0; c < p->pCutNum[iObj]; c++, pCut++ )
    {
        if ( pCut->nLeaves == 1 && pCut->Leaves[0] == iObj )
            continue;
        if ( pCut->nLeaves == 0 )
        {
            for ( f = 0; f < 2; f++ )
                Emp_BestSetConst( pB + f, (pCut->Truth != 0) ^ f );
            return;
        }
        if ( pCut->nLeaves == 1 )
        {
            for ( f = 0; f < 2; f++ )
            {
                int Leaf = pCut->Leaves[0], Ph = f ^ (int)(pCut->Truth & 1);
                double Arr = Emp_ObjArr( p, Leaf, Ph ), Flow = Emp_ObjFlowRef( p, Leaf, Ph );
                if ( Arr <= pReq[f] + EMP_EPS && Emp_BestIsBetter(Arr, Flow, pB + f, fArea) )
                    Emp_BestSetWire( p, pB + f, Leaf, Ph, Flow );
            }
            continue;
        }
        for ( f = 0; f < 2; f++ )
            for ( n = 0; n < pCut->nCell[f]; n++ )
                Emp_ObjMatchCell( p, pB + f, p->pCells + pCut->iCell[f] + n, pCut->Leaves, Load[f], pReq[f], fArea, fLeafLoad );
    }
}
// chooses inverters to implement a phase from the other phase
static void Emp_ObjMatchPhases( Emp_Man_t * p, int iObj, double * pReq, int fArea )
{
    Emp_Best_t * pB = Emp_ObjBest( p, iObj, 0 );
    int f, fInv[2] = {0, 0};
    for ( f = 0; f < 2; f++ )
    {
        Emp_Best_t * pOwn = pB + f, * pOth = pB + !f;
        double ArrInv;
        if ( pOth->Type == EMP_NONE || pOth->Type == EMP_INV )
            continue;
        ArrInv = pOth->Arr + Emp_InvDelay( p, iObj, f );
        if ( fArea && ArrInv > pReq[f] + EMP_EPS )
            continue;
        if ( pOwn->Type == EMP_NONE )
            fInv[f] = 1;
        else if ( pOwn->Type == EMP_CONST || pOth->Type == EMP_CONST )
            fInv[f] = 0;
        else if ( fArea )
            fInv[f] = Emp_ObjFlowRef(p, iObj, !f) + p->InvArea < Emp_ObjFlowRef(p, iObj, f) - EMP_EPS;
        else
            fInv[f] = ArrInv < pOwn->Arr - 0.0001 || (ArrInv < pOwn->Arr + 0.0001 && pOth->Flow + p->InvArea < pOwn->Flow - 0.0001);
    }
    if ( fInv[0] && fInv[1] )
    {
        if ( pB[0].Type == EMP_NONE || pB[1].Type == EMP_NONE )
            fInv[pB[0].Type == EMP_NONE ? 1 : 0] = 0;
        else if ( fArea ? Emp_ObjFlowRef(p, iObj, 0) <= Emp_ObjFlowRef(p, iObj, 1) : pB[0].Arr <= pB[1].Arr )
            fInv[0] = 0;
        else
            fInv[1] = 0;
    }
    for ( f = 0; f < 2; f++ )
        if ( fInv[f] )
            Emp_BestSetInv( p, iObj, f );
}
// matches both phases of the node; in area mode, under its required times if possible
static void Emp_ObjMatch( Emp_Man_t * p, int iObj, int fArea, int fLeafLoad )
{
    Emp_Best_t * pB = Emp_ObjBest( p, iObj, 0 );
    double ReqInf[2] = { EMP_INF, EMP_INF };
    double * pReq = fArea ? p->pReq + 2 * iObj : ReqInf;
    Emp_ObjMatchCuts( p, iObj, pReq, fArea, fLeafLoad );
    Emp_ObjMatchPhases( p, iObj, pReq, fArea );
    if ( pB[0].Type != EMP_NONE && pB[1].Type != EMP_NONE )
        return;
    // no match meets the required time: use the fastest matches
    Emp_ObjMatchCuts( p, iObj, ReqInf, 0, fLeafLoad );
    Emp_ObjMatchPhases( p, iObj, ReqInf, 0 );
    assert( pB[0].Type != EMP_NONE && pB[1].Type != EMP_NONE );
}

/**Function*************************************************************

  Synopsis    [The current cover: references, loads, and required times.]

  Description [Refs count the references of a node phase.  Impl marks the
               phases whose implementation is in the cover.  A two-output
               cell is in the cover if one of its outputs is.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Emp_LoadInc( Emp_Man_t * p, int e, float Cap, float CapD )
{
    p->pLoad[e]  += Cap;
    p->pLoadD[e] += CapD;
}
// adds load to a node phase; its arrival moves by the load sensitivity of its driver
static inline void Emp_LoadAdd( Emp_Man_t * p, int i, int f, float Cap, float CapD )
{
    Emp_Best_t * pB = p->pBest + 2 * i + f;
    if ( !p->fNldm )
        return;
    Emp_LoadInc( p, 2 * i + f, Cap, CapD );
    if ( p->fTrack )
        Vec_IntPush( p->vDirty, i );
    if ( !p->fNoShift )
        Emp_BestShiftArr( pB, pB->Sens * Cap );
    if ( p->pImpl[2 * i + f] && pB->Type == EMP_WIRE )
        Emp_LoadAdd( p, pB->Leaves[0], pB->Phases[0], Cap, CapD );
}
// records node i as a fanout of the leaves of the implementation of (i, f) and as changed
static void Emp_ObjAddFanouts( Emp_Man_t * p, int i, int f )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f );
    int k;
    Vec_IntPush( p->vDirty, i );
    if ( !(pB->Type == EMP_GATE || pB->Type == EMP_MOG || pB->Type == EMP_WIRE) )
        return;
    for ( k = 0; k < pB->nPins; k++ )
    {
        Vec_Int_t * vFan = Vec_WecEntry( p->vFans, pB->Leaves[k] );
        if ( Vec_IntSize(vFan) == 0 || Vec_IntEntryLast(vFan) != i )
            Vec_IntPush( vFan, i );
    }
}
// adds (fAdd) or removes the implementation of (i, f) to or from the cover; returns the area added or freed
static float Emp_ObjImpl( Emp_Man_t * p, int i, int f, int fAdd )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f );
    float Sign = fAdd ? 1 : -1, Area;
    int k;
    assert( p->pImpl[2 * i + f] == !fAdd );
    p->pImpl[2 * i + f] = (char)fAdd;
    if ( fAdd && p->fTrack )
        Emp_ObjAddFanouts( p, i, f );
    switch ( pB->Type )
    {
    case EMP_PI:
    case EMP_CONST:
        return 0;
    case EMP_INV:
        Emp_LoadAdd( p, i, !f, Sign * Emp_InvCin(p, pB->iMem), Sign * Emp_InvCinD(p, pB->iMem) );
        return pB->Area + Emp_ObjRef_rec( p, i, !f, fAdd );
    case EMP_WIRE:
        Emp_LoadAdd( p, pB->Leaves[0], pB->Phases[0], Sign * p->pLoad[2 * i + f], Sign * p->pLoadD[2 * i + f] );
        return Emp_ObjRef_rec( p, pB->Leaves[0], pB->Phases[0], fAdd );
    case EMP_MOG:
    case EMP_GATE:
        // the cell of a two-output gate is counted with its first output in the cover
        if ( Emp_BestTwinUsed(p, pB) >= 0 )
            return 0;
        Area = pB->Area;
        for ( k = 0; k < pB->nPins; k++ )
        {
            Emp_LoadAdd( p, pB->Leaves[k], pB->Phases[k], Sign * pB->pCin[k], Sign * Emp_BestCinD(p, pB, k) );
            Area += Emp_ObjRef_rec( p, pB->Leaves[k], pB->Phases[k], fAdd );
        }
        return Area;
    }
    assert( 0 );
    return 0;
}
// references (fRef) or dereferences a node phase; returns the area added to or freed from the cover
static float Emp_ObjRef_rec( Emp_Man_t * p, int i, int f, int fRef )
{
    int e = 2 * i + f;
    if ( fRef )
        p->pRefs[e]++;
    else
    {
        assert( p->pRefs[e] > 0 );
        if ( --p->pRefs[e] > 0 )
            return 0;
    }
    // nothing to do if the phase is already in the cover (reference) or not in it (dereference)
    if ( p->pImpl[e] == fRef )
        return 0;
    return Emp_ObjImpl( p, i, f, fRef );
}
// removes the implementations of the node from the cover (keeps the references)
static float Emp_ObjDetach( Emp_Man_t * p, int i )
{
    float Area = 0;
    int f;
    for ( f = 0; f < 2; f++ )
        if ( p->pImpl[2 * i + f] && Emp_ObjBest(p, i, f)->Type == EMP_INV )
            Area += Emp_ObjImpl( p, i, f, 0 );
    for ( f = 0; f < 2; f++ )
        if ( p->pImpl[2 * i + f] )
            Area += Emp_ObjImpl( p, i, f, 0 );
    return Area;
}
// adds the implementations of the referenced phases of the node to the cover
static float Emp_ObjAttach( Emp_Man_t * p, int i )
{
    float Area = 0;
    int f;
    for ( f = 0; f < 2; f++ )
        if ( p->pRefs[2 * i + f] > 0 && !p->pImpl[2 * i + f] )
            Area += Emp_ObjImpl( p, i, f, 1 );
    return Area;
}
// latest arrival of the referenced phases
static double Emp_ObjNeedArr( Emp_Man_t * p, int i )
{
    double Arr = 0;
    int f;
    for ( f = 0; f < 2; f++ )
        if ( p->pRefs[2 * i + f] > 0 )
            Arr = Abc_MaxDouble( Arr, Emp_ObjArr(p, i, f) );
    return Arr;
}
// references the cover from the outputs; returns its area
static float Emp_ManSetRefs( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    float Area = 0;
    int i;
    memset( p->pRefs, 0, sizeof(int) * 2 * p->nObjs );
    memset( p->pImpl, 0, sizeof(char) * 2 * p->nObjs );
    if ( p->fNldm )
    {
        memset( p->pLoad, 0, sizeof(float) * 2 * p->nObjs );
        memset( p->pLoadD, 0, sizeof(float) * 2 * p->nObjs );
    }
    p->fNoShift = 1;
    Abc_NtkForEachPo( p->pNtk, pObj, i )
    {
        Emp_LoadAdd( p, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj), p->PoLoad, 0 );
        Area += Emp_ObjRef_rec( p, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj), 1 );
    }
    p->fNoShift = 0;
    return Area;
}
// blends the fanout estimates with the references of the cover
static void Emp_ManUpdateEst( Emp_Man_t * p )
{
    float Coef = 1.0f / ((p->nRound + 1.0f) * (p->nRound + 1.0f));
    int i;
    for ( i = 0; i < 2 * p->nObjs; i++ )
        p->pEst[i] = Abc_MaxFloat( 1.0f, Coef * p->pEst[i] + (1 - Coef) * p->pRefs[i] );
    p->nRound++;
}
// propagates the required times of the implemented phases to the fanins
static void Emp_ObjPropagateReq( Emp_Man_t * p, int i )
{
    int f, k;
    if ( !Emp_ObjIsUsed(p, i) )
        return;
    for ( f = 0; f < 2; f++ )
        if ( p->pImpl[2 * i + f] && Emp_ObjBest(p, i, f)->Type == EMP_INV )
            p->pReq[2 * i + !f] = Abc_MinDouble( p->pReq[2 * i + !f], p->pReq[2 * i + f] - Emp_InvDelay(p, i, f) );
    for ( f = 0; f < 2; f++ )
    {
        Emp_Best_t * pB = Emp_ObjBest( p, i, f );
        double R = p->pReq[2 * i + f];
        if ( !p->pImpl[2 * i + f] || R >= EMP_INF / 2 )
            continue;
        if ( pB->Type == EMP_WIRE )
            p->pReq[2 * pB->Leaves[0] + pB->Phases[0]] = Abc_MinDouble( p->pReq[2 * pB->Leaves[0] + pB->Phases[0]], R );
        else if ( pB->Type == EMP_GATE || pB->Type == EMP_MOG )
            for ( k = 0; k < pB->nPins; k++ )
            {
                double * pR = p->pReq + 2 * pB->Leaves[k] + pB->Phases[k];
                *pR = Abc_MinDouble( *pR, R - Emp_PinDelay(p, pB, k, Emp_ObjLoad(p, i, f), p->pLoadD[2 * i + f]) );
            }
    }
}
// computes the delay of the current cover; sets the required times if not in area mode
static double Emp_ManSetRequired( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    double Delay = 0;
    int i;
    for ( i = 0; i < 2 * p->nObjs; i++ )
        p->pReq[i] = EMP_INF;
    Abc_NtkForEachPo( p->pNtk, pObj, i )
        Delay = Abc_MaxDouble( Delay, Emp_ObjArr(p, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj)) );
    if ( p->pPars->fAreaMode )
        return Delay;
    Abc_NtkForEachPo( p->pNtk, pObj, i )
    {
        double * pR = p->pReq + 2 * Abc_ObjFaninId0(pObj) + Abc_ObjFaninC0(pObj);
        *pR = Abc_MinDouble( *pR, p->DelayTarget * (1 - p->Guard) );
    }
    for ( i = p->nObjs - 1; i >= 0; i-- )
        Emp_ObjPropagateReq( p, i );
    return Delay;
}
// loads of the node phases in the current cover (a two-output cell loads its inputs once)
static void Emp_ManSetLoads( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    int i, f, k;
    if ( !p->fNldm )
        return;
    for ( i = 0; i < 2 * p->nObjs; i++ )
        p->pLoad[i] = p->pLoadD[i] = 0;
    Abc_NtkForEachPo( p->pNtk, pObj, i )
        p->pLoad[2 * Abc_ObjFaninId0(pObj) + Abc_ObjFaninC0(pObj)] += p->PoLoad;
    for ( i = p->nObjs - 1; i >= 0; i-- )
    {
        for ( f = 0; f < 2; f++ )
        {
            Emp_Best_t * pB = Emp_ObjBest( p, i, f );
            if ( p->pImpl[2 * i + f] && pB->Type == EMP_INV )
                Emp_LoadInc( p, 2 * i + !f, Emp_InvCin(p, pB->iMem), Emp_InvCinD(p, pB->iMem) );
        }
        for ( f = 0; f < 2; f++ )
        {
            Emp_Best_t * pB = Emp_ObjBest( p, i, f );
            if ( !p->pImpl[2 * i + f] || Emp_ObjIsTwinSecond(p, i, f) )
                continue;
            else if ( pB->Type == EMP_WIRE )
                Emp_LoadInc( p, 2 * pB->Leaves[0] + pB->Phases[0], p->pLoad[2 * i + f], p->pLoadD[2 * i + f] );
            else if ( pB->Type == EMP_GATE || pB->Type == EMP_MOG )
                for ( k = 0; k < pB->nPins; k++ )
                    Emp_LoadInc( p, 2 * pB->Leaves[k] + pB->Phases[k], pB->pCin[k], Emp_BestCinD(p, pB, k) );
        }
    }   
}
// recomputes the loads and the arrival times of the current cover
static void Emp_ManRetime( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    if ( !p->fNldm )
        return;
    Emp_ManSetLoads( p );
    Abc_NtkForEachObj( p->pNtk, pObj, i )
        if ( Abc_ObjIsCi(pObj) || Abc_AigNodeIsAnd(pObj) )
            Emp_ObjUpdateArr( p, i );
}
// recomputes references, loads, arrival and required times of the current cover
static float Emp_ManUpdate( Emp_Man_t * p, double * pDelay )
{
    float Area = Emp_ManSetRefs( p );
    Emp_ManRetime( p );
    *pDelay = Emp_ManSetRequired( p );
    return Area;
}
// counts the two-output cells in the cover (with three and two inputs)
static int Emp_ManCountMogs( Emp_Man_t * p, int * pnFa, int * pnHa )
{
    int i, f, nMogs = 0;
    *pnFa = *pnHa = 0;
    for ( i = 0; i < p->nObjs; i++ )
        for ( f = 0; f < 2; f++ )
        {
            Emp_Best_t * pB = Emp_ObjBest( p, i, f );
            if ( !p->pImpl[2 * i + f] || pB->Type != EMP_MOG || Emp_ObjIsTwinSecond(p, i, f) )
                continue;
            nMogs++;
            *pnFa += pB->nPins == 3;
            *pnHa += pB->nPins == 2;
        }
    return nMogs;
}

/**Function*************************************************************

  Synopsis    [Incremental timing of the cover.]

  Description [After each decision in exact area, the changed nodes and
               their fanout cones are retimed in topological order.  A node
               is propagated further only if its arrival or transition
               differs from the last propagation (not from the current
               values, which may have been shifted when the loads changed).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// starts incremental timing: fanout lists, output drivers and committed timing of the cover
static void Emp_ManStartIncr( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    int i, f;
    Vec_Int_t * vLevel;
    if ( p->pArcs == NULL )
        p->pArcs = ABC_CALLOC( Emp_Arc_t, 2 * EMP_LEAF_MAX * p->nObjs );
    if ( p->vFans == NULL )
        p->vFans = Vec_WecStart( p->nObjs );
    else
        Vec_WecForEachLevel( p->vFans, vLevel, i )
            Vec_IntClear( vLevel );
    memset( p->pPoDrv, 0, sizeof(char) * 2 * p->nObjs );
    Abc_NtkForEachPo( p->pNtk, pObj, i )
    {
        int e = 2 * Abc_ObjFaninId0(pObj) + Abc_ObjFaninC0(pObj);
        p->pPoDrv[e] = 1;
        p->pPoArr[e] = p->pBest[e].Arr;
    }
    for ( i = 0; i < p->nObjs; i++ )
        for ( f = 0; f < 2; f++ )
        {
            if ( p->pImpl[2 * i + f] )
                Emp_ObjAddFanouts( p, i, f );
            p->pCommit[4 * i + 2 * f + 0] = p->pBest[2 * i + f].ArrRF;
            p->pCommit[4 * i + 2 * f + 1] = p->pBest[2 * i + f].SlewRF;
        }
    Vec_IntClear( p->vDirty );
    p->fIncr = 1;
}
// binary heap of nodes ordered by ID (a topological order)
static void Emp_HeapPush( Emp_Man_t * p, int i )
{
    int * pH, k;
    if ( p->pInQ[i] )
        return;
    p->pInQ[i] = 1;
    Vec_IntPush( p->vHeap, i );
    pH = Vec_IntArray( p->vHeap );
    for ( k = Vec_IntSize(p->vHeap) - 1; k > 0 && pH[(k - 1) / 2] > pH[k]; k = (k - 1) / 2 )
        ABC_SWAP( int, pH[k], pH[(k - 1) / 2] );
}
static int Emp_HeapPop( Emp_Man_t * p )
{
    int * pH = Vec_IntArray( p->vHeap ), n = Vec_IntSize( p->vHeap ) - 1, Top = pH[0], k = 0, c;
    pH[0] = pH[n];
    Vec_IntShrink( p->vHeap, n );
    while ( (c = 2 * k + 1) < n )
    {
        if ( c + 1 < n && pH[c + 1] < pH[c] )
            c++;
        if ( pH[k] <= pH[c] )
            break;
        ABC_SWAP( int, pH[k], pH[c] );
        k = c;
    }
    p->pInQ[Top] = 0;
    return Top;
}
static inline int Emp_PairChanged( SC_Pair * pA, SC_Pair * pB )
{
    return Abc_AbsFloat(pA->rise - pB->rise) > 0.001f || Abc_AbsFloat(pA->fall - pB->fall) > 0.001f;
}
// retimes the changed nodes; returns 0 if an output misses the target (and gets later);
// turns incremental timing off when the budget is used up
static int Emp_ManPropagate( Emp_Man_t * p )
{
    int k, i, f, fOk = 1;
    Vec_IntClear( p->vPoTouched );
    Vec_IntForEachEntry( p->vDirty, i, k )
        Emp_HeapPush( p, i );
    Vec_IntClear( p->vDirty );
    while ( Vec_IntSize(p->vHeap) > 0 )
    {
        int fChange = 0;
        i = Emp_HeapPop( p );
        p->fImplOnly = 1;
        Emp_ObjUpdateArr( p, i );
        p->fImplOnly = 0;
        p->nRetimed++;
        for ( f = 0; f < 2; f++ )
        {
            Emp_Best_t * pB = p->pBest + 2 * i + f;
            SC_Pair * pC = p->pCommit + 4 * i + 2 * f;
            int fDiff = Emp_PairChanged( &pC[0], &pB->ArrRF ) || Emp_PairChanged( &pC[1], &pB->SlewRF );
            if ( fDiff )
                pC[0] = pB->ArrRF, pC[1] = pB->SlewRF;
            if ( !p->pImpl[2 * i + f] )
                continue;
            fChange |= fDiff;
            if ( p->pPoDrv[2 * i + f] )
                Vec_IntPush( p->vPoTouched, 2 * i + f );
            // an output may stay above the target but not get later
            if ( p->pPoDrv[2 * i + f] && pB->Arr > p->DelayTarget + EMP_EPS && pB->Arr > p->pPoArr[2 * i + f] + EMP_EPS )
                fOk = 0;
        }
        if ( fChange )
        {
            Vec_Int_t * vFan = Vec_WecEntry( p->vFans, i );
            int j, Fan;
            Vec_IntForEachEntry( vFan, Fan, j )
                if ( Emp_ObjIsUsed(p, Fan) )
                    Emp_HeapPush( p, Fan );
        }
    }
    // budget used up: the rest of the round is timed and repaired as a whole
    if ( p->RetimeLimit > 0 && p->nRetimed > p->RetimeLimit && p->fIncr && fOk )
    {
        p->fIncr = 0;
        p->fIncrOff = 1;
    }
    return fOk;
}
// accepts the output arrival times after a decision with incremental timing
static void Emp_ManAcceptPos( Emp_Man_t * p )
{
    int k, e;
    Vec_IntForEachEntry( p->vPoTouched, e, k )
        p->pPoArr[e] = p->pBest[e].Arr;
}
/**Function*************************************************************

  Synopsis    [Pairs of nodes for two-output cells.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Emp_Small_t_ Emp_Small_t;
struct Emp_Small_t_
{
    word             Truth;
    int              nLeaves;
    int              Leaves[EMP_MOG_LEAF];
    int              Node;
};
static int Emp_SmallCompare( const void * a, const void * b )
{
    Emp_Small_t * p0 = (Emp_Small_t *)a, * p1 = (Emp_Small_t *)b;
    int i;
    if ( p0->nLeaves != p1->nLeaves )
        return p0->nLeaves - p1->nLeaves;
    for ( i = 0; i < p0->nLeaves; i++ )
        if ( p0->Leaves[i] != p1->Leaves[i] )
            return p0->Leaves[i] - p1->Leaves[i];
    return p0->Node - p1->Node;
}
static int Emp_CandCompare( const void * a, const void * b )
{
    Emp_Tup_t * p0 = (Emp_Tup_t *)a, * p1 = (Emp_Tup_t *)b;
    if ( p0->Gain != p1->Gain )
        return p0->Gain > p1->Gain ? -1 : 1;
    return p0->Id - p1->Id;
}
// dereferences the MFFC of the node (the leaves are not entered)
static void Emp_MffcDeref_rec( Abc_Obj_t * pObj, char * pLeafMarks, int * pDecs, Vec_Int_t * vTouched )
{
    Abc_Obj_t * pFanin;
    int i, Id;
    if ( Abc_ObjIsCi(pObj) || Abc_AigNodeIsConst(pObj) || pLeafMarks[Abc_ObjId(pObj)] )
        return;
    Abc_ObjForEachFanin( pObj, pFanin, i )
    {
        Id = Abc_ObjId( pFanin );
        if ( pLeafMarks[Id] )
            continue;
        if ( pDecs[Id]++ == 0 )
            Vec_IntPush( vTouched, Id );
        if ( pDecs[Id] == Abc_ObjFanoutNum(pFanin) )
            Emp_MffcDeref_rec( pFanin, pLeafMarks, pDecs, vTouched );
    }
}
// returns 1 if one root would have no fanouts outside the MFFC of the other root
static int Emp_PairIsDangling( Emp_Man_t * p, int Low, int High, int * pLeaves, int nLeaves, char * pLeafMarks, int * pDecs )
{
    Abc_Obj_t * pLow = Abc_NtkObj( p->pNtk, Low ), * pHigh = Abc_NtkObj( p->pNtk, High );
    int i, Entry, fDangling;
    if ( (Abc_ObjFaninId0(pHigh) == Low || Abc_ObjFaninId1(pHigh) == Low) && Abc_ObjFanoutNum(pLow) == 1 )
        return 1;
    if ( (Abc_ObjFaninId0(pLow) == High || Abc_ObjFaninId1(pLow) == High) && Abc_ObjFanoutNum(pHigh) == 1 )
        return 1;
    for ( i = 0; i < nLeaves; i++ )
        pLeafMarks[pLeaves[i]] = 1;
    Vec_IntClear( p->vTemp );
    Emp_MffcDeref_rec( pHigh, pLeafMarks, pDecs, p->vTemp );
    fDangling = Abc_ObjFanoutNum(pLow) - pDecs[Low] <= 0;
    for ( i = 0; i < nLeaves; i++ )
        pLeafMarks[pLeaves[i]] = 0;
    Vec_IntForEachEntry( p->vTemp, Entry, i )
        pDecs[Entry] = 0;
    return fDangling;
}
// smallest single-output cost of a function on the leaves; complemented leaves
// and a complemented output are charged one inverter each
static float Emp_FuncCost( Emp_Man_t * p, int nLeaves, word Truth )
{
    float Cost = EMP_FINF;
    int f, n, nCells, iCell;
    for ( f = 0; f < 2; f++ )
    {
        iCell = Emp_LibLookup( p, nLeaves, f ? (~Truth & Emp_TruthMask(nLeaves)) : Truth, &nCells );
        for ( n = 0; n < nCells; n++ )
        {
            Emp_Cell_t * pCell = p->pCells + iCell + n;
            Cost = Abc_MinFloat( Cost, pCell->Area + (f + Abc_TtCountOnes((word)pCell->LeafSig)) * p->InvArea );
        }
    }
    return Cost;
}
// area saved by a two-output cell over two single-output cells (-EMP_FINF if there is none)
static float Emp_PairGain( Emp_Man_t * p, int nLeaves, word Truth0, word Truth1 )
{
    float CostMog = EMP_FINF, Cost0, Cost1;
    word Mask = Emp_TruthMask( nLeaves );
    int f0, f1, k, iKey, nKeys;
    for ( f0 = 0; f0 < 2; f0++ )
    for ( f1 = 0; f1 < 2; f1++ )
    {
        iKey = Emp_LibMogLookup( p, nLeaves, (f0 ? ~Truth0 : Truth0) & Mask, (f1 ? ~Truth1 : Truth1) & Mask, &nKeys );
        for ( k = 0; k < nKeys; k++ )
        {
            Emp_Mog_t * pMog = p->pMogs + p->pMogKeys[iKey + k].iMog;
            CostMog = Abc_MinFloat( CostMog, pMog->Area + (f0 + f1 + Abc_TtCountOnes((word)pMog->LeafSig)) * p->InvArea );
        }
    }
    if ( CostMog == EMP_FINF )
        return -EMP_FINF;
    Cost0 = Emp_FuncCost( p, nLeaves, Truth0 );
    Cost1 = Emp_FuncCost( p, nLeaves, Truth1 );
    if ( Cost0 == EMP_FINF || Cost1 == EMP_FINF )
        return 0;
    return Cost0 + Cost1 - CostMog;
}
// exhaustive cuts with up to three leaves; the cuts of node i are pSmall[pBeg[i]] to pSmall[pBeg[i] + pNum[i] - 1]
static Emp_Small_t * Emp_ManSmallCuts( Emp_Man_t * p, int * pBeg, int * pNum, int * pnSmall )
{
    Emp_Small_t * pSmall = NULL;
    Abc_Obj_t * pObj;
    int i, a, b, s, nSmall = 0, nSmallCap = 0;
    Abc_NtkForEachObj( p->pNtk, pObj, i )
    {
        Emp_Small_t Set[256];
        int nSet = 0;
        if ( Abc_ObjIsCi(pObj) || Abc_AigNodeIsAnd(pObj) )
        {
            Set[0].nLeaves = 1; Set[0].Leaves[0] = i; Set[0].Truth = s_Truths6[0]; Set[0].Node = i;
            nSet = 1;
        }
        if ( Abc_AigNodeIsAnd(pObj) )
        {
            int iFan0 = Abc_ObjFaninId0(pObj), iFan1 = Abc_ObjFaninId1(pObj);
            word Mask0 = Abc_ObjFaninC0(pObj) ? ~(word)0 : 0, Mask1 = Abc_ObjFaninC1(pObj) ? ~(word)0 : 0;
            for ( a = 0; a < pNum[iFan0]; a++ )
            for ( b = 0; b < pNum[iFan1]; b++ )
            {
                Emp_Small_t * p0 = pSmall + pBeg[iFan0] + a, * p1 = pSmall + pBeg[iFan1] + b, New;
                int n = Emp_CutMergeLeaves( p0->Leaves, p0->nLeaves, p1->Leaves, p1->nLeaves, New.Leaves, EMP_MOG_LEAF );
                if ( n < 0 )
                    continue;
                New.Truth = (Abc_Tt6Expand(p0->Truth, p0->Leaves, p0->nLeaves, New.Leaves, n) ^ Mask0) &
                            (Abc_Tt6Expand(p1->Truth, p1->Leaves, p1->nLeaves, New.Leaves, n) ^ Mask1);
                New.nLeaves = Abc_Tt6MinBase( &New.Truth, New.Leaves, n );
                New.Node = i;
                if ( New.nLeaves < 1 )
                    continue;
                for ( s = 0; s < nSet; s++ )
                    if ( Set[s].nLeaves == New.nLeaves && !memcmp(Set[s].Leaves, New.Leaves, sizeof(int) * New.nLeaves) )
                        break;
                if ( s == nSet && nSet < 256 )
                    Set[nSet++] = New;
            }
        }
        if ( nSmall + nSet > nSmallCap )
        {
            nSmallCap = Abc_MaxInt( 2 * nSmallCap, nSmall + nSet + 1024 );
            pSmall = ABC_REALLOC( Emp_Small_t, pSmall, nSmallCap );
        }
        memcpy( pSmall + nSmall, Set, sizeof(Emp_Small_t) * nSet );
        pBeg[i] = nSmall;
        pNum[i] = nSet;
        nSmall += nSet;
    }
    *pnSmall = nSmall;
    return pSmall;
}
// collects the pairs of nodes with a common cut of up to three leaves matching a two-output cell
static int Emp_ManFindCands( Emp_Man_t * p, Emp_Tup_t ** ppCands )
{
    int * pBeg = ABC_FALLOC( int, p->nObjs ), * pNum = ABC_CALLOC( int, p->nObjs ), * pDecs = ABC_CALLOC( int, p->nObjs );
    char * pLeafMarks = ABC_CALLOC( char, p->nObjs );
    int i, k, a, b, Beg, End, nSmall, nEntries = 0, nCands = 0, nCandCap = 0;
    Emp_Small_t * pSmall = Emp_ManSmallCuts( p, pBeg, pNum, &nSmall ), * pEntries = ABC_ALLOC( Emp_Small_t, nSmall + 1 );
    Emp_Tup_t * pCands = NULL;
    Abc_Obj_t * pObj;
    // group the cuts by leaves
    Abc_AigForEachAnd( p->pNtk, pObj, i )
        for ( k = 0; k < pNum[i]; k++ )
            if ( pSmall[pBeg[i] + k].nLeaves >= 2 )
                pEntries[nEntries++] = pSmall[pBeg[i] + k];
    qsort( pEntries, (size_t)nEntries, sizeof(Emp_Small_t), Emp_SmallCompare );
    for ( Beg = 0; Beg < nEntries; Beg = End )
    {
        for ( End = Beg + 1; End < nEntries && pEntries[End].nLeaves == pEntries[Beg].nLeaves &&
              !memcmp(pEntries[End].Leaves, pEntries[Beg].Leaves, sizeof(int) * pEntries[Beg].nLeaves); End++ );
        for ( a = Beg; a < End; a++ )
        for ( b = a + 1; b < End; b++ )
        {
            Emp_Small_t * p0 = pEntries + a, * p1 = pEntries + b;
            word Mask = Emp_TruthMask( p0->nLeaves );
            Emp_Tup_t * pCand;
            // the gain is estimated for the most favorable phases of the roots
            float Gain = -EMP_FINF;
            int Ph0, Ph1;
            for ( Ph0 = 0; Ph0 < 2; Ph0++ )
            for ( Ph1 = 0; Ph1 < 2; Ph1++ )
                Gain = Abc_MaxFloat( Gain, Emp_PairGain(p, p0->nLeaves, (Ph0 ? ~p0->Truth : p0->Truth) & Mask, (Ph1 ? ~p1->Truth : p1->Truth) & Mask) );
            if ( Gain == -EMP_FINF )
                continue;
            if ( Emp_PairIsDangling(p, p0->Node, p1->Node, p0->Leaves, p0->nLeaves, pLeafMarks, pDecs) )
                continue;
            if ( nCands == nCandCap )
            {
                nCandCap = nCandCap ? 2 * nCandCap : 1024;
                pCands = ABC_REALLOC( Emp_Tup_t, pCands, nCandCap );
            }
            pCand = pCands + nCands;
            pCand->Node[0]  = p0->Node;
            pCand->Node[1]  = p1->Node;
            pCand->nLeaves  = p0->nLeaves;
            memcpy( pCand->Leaves, p0->Leaves, sizeof(int) * p0->nLeaves );
            pCand->Truth[0] = p0->Truth & Mask;
            pCand->Truth[1] = p1->Truth & Mask;
            pCand->Gain     = Gain;
            pCand->Id       = nCands++;
        }
    }
    ABC_FREE( pEntries );
    ABC_FREE( pSmall );
    ABC_FREE( pBeg );
    ABC_FREE( pNum );
    ABC_FREE( pDecs );
    ABC_FREE( pLeafMarks );
    *ppCands = pCands;
    return nCands;
}
// selects disjoint pairs by decreasing estimated gain and records their tuples
static void Emp_ManSelectPairs( Emp_Man_t * p )
{
    Emp_Tup_t * pCands = NULL;
    int i, nCands = Emp_ManFindCands( p, &pCands );
    p->nCands = nCands;
    qsort( pCands, (size_t)nCands, sizeof(Emp_Tup_t), Emp_CandCompare );
    for ( i = 0; i < nCands; i++ )
    {
        Emp_Tup_t * pCand = pCands + i;
        int n0 = pCand->Node[0], n1 = pCand->Node[1];
        if ( pCand->Gain < 0 )
            continue;
        if ( p->pPartner[n0] == -1 && p->pPartner[n1] == -1 )
        {
            p->pPartner[n0] = n1;
            p->pPartner[n1] = n0;
            p->nPairs++;
        }
        if ( p->pPartner[n0] != n1 )
            continue;
        if ( p->nTups == p->nTupCap )
        {
            p->nTupCap = p->nTupCap ? 2 * p->nTupCap : 256;
            p->pTups = ABC_REALLOC( Emp_Tup_t, p->pTups, p->nTupCap );
        }
        pCand->Next = p->pTupFirst[n0];
        p->pTups[p->nTups] = *pCand;
        p->pTupFirst[n0] = p->pTupFirst[n1] = p->nTups++;
    }
    ABC_FREE( pCands );
}

/**Function*************************************************************

  Synopsis    [Constrained topological order.]

  Description [Places the roots of a pair next to each other: the fanin
               cones of both roots come first, then the two roots.  Pairs
               where a root depends on the other through a path of length
               more than one cannot be placed next to each other.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// returns 1 if iTarget is in the TFI of iRoot
static int Emp_ObjInTfi( Emp_Man_t * p, int iRoot, int iTarget )
{
    Emp_TravStart( p );
    Vec_IntClear( p->vTemp );
    Vec_IntPush( p->vTemp, iRoot );
    while ( Vec_IntSize(p->vTemp) )
    {
        int i = Vec_IntPop( p->vTemp );
        if ( i == iTarget )
            return 1;
        if ( i < iTarget || !Emp_ObjIsAnd(p, i) || Emp_TravIsCur(p, i) )
            continue;
        Emp_TravSetCur( p, i );
        Vec_IntPush( p->vTemp, Abc_ObjFaninId0(Abc_NtkObj(p->pNtk, i)) );
        Vec_IntPush( p->vTemp, Abc_ObjFaninId1(Abc_NtkObj(p->pNtk, i)) );
    }
    return 0;
}
// marks the pairs whose roots can be placed next to each other
static void Emp_ManMarkCoPlace( Emp_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nObjs; i++ )
    {
        Abc_Obj_t * pHigh;
        int Low = i, High = p->pPartner[i];
        if ( High <= Low )
            continue;
        pHigh = Abc_NtkObj( p->pNtk, High );
        p->pCoPlace[Low] = p->pCoPlace[High] =
            (Abc_ObjFaninId0(pHigh) == Low || !Emp_ObjInTfi(p, Abc_ObjFaninId0(pHigh), Low)) &&
            (Abc_ObjFaninId1(pHigh) == Low || !Emp_ObjInTfi(p, Abc_ObjFaninId1(pHigh), Low));
    }
}
static inline void Emp_OrderEmit( Emp_Man_t * p, int i )
{
    p->pPos[i] = p->nOrder;
    p->pOrder[p->nOrder++] = i;
    p->pMark[i] = 2;
}
// returns 1 if the unplaced fanin cone of the node contains no pending node
static int Emp_OrderCheck( Emp_Man_t * p, int iRoot )
{
    Emp_TravStart( p );
    Vec_IntClear( p->vTemp );
    Vec_IntPush( p->vTemp, iRoot );
    while ( Vec_IntSize(p->vTemp) )
    {
        int i = Vec_IntPop( p->vTemp );
        if ( p->pMark[i] == 2 || !Emp_ObjIsAnd(p, i) || Emp_TravIsCur(p, i) )
            continue;
        if ( p->pMark[i] == 1 || p->pPend[i] )
            return 0;
        Emp_TravSetCur( p, i );
        Vec_IntPush( p->vTemp, Abc_ObjFaninId0(Abc_NtkObj(p->pNtk, i)) );
        Vec_IntPush( p->vTemp, Abc_ObjFaninId1(Abc_NtkObj(p->pNtk, i)) );
    }
    return 1;
}
// places the fanin cone of the node, then the node (with its partner if possible)
static void Emp_OrderPlace_rec( Emp_Man_t * p, int i )
{
    Abc_Obj_t * pObj = Abc_NtkObj( p->pNtk, i );
    int m = p->pPartner[i], k, Fan[2], fPair = 0;
    if ( p->pMark[i] == 2 || !Abc_AigNodeIsAnd(pObj) )
        return;
    assert( p->pMark[i] == 0 );
    if ( m >= 0 && p->pCoPlace[i] && p->pMark[m] == 0 && !p->pPend[m] )
    {
        // place the fanin cone of the partner first, then both roots
        Fan[0] = Abc_ObjFaninId0( Abc_NtkObj(p->pNtk, m) );
        Fan[1] = Abc_ObjFaninId1( Abc_NtkObj(p->pNtk, m) );
        p->pPend[i] = 1;
        for ( fPair = 1, k = 0; k < 2 && fPair; k++ )
            if ( Fan[k] != i )
                fPair = Emp_OrderCheck( p, Fan[k] );
        if ( fPair )
        {
            p->pPend[m] = 1;
            for ( k = 0; k < 2; k++ )
                if ( Fan[k] != i )
                    Emp_OrderPlace_rec( p, Fan[k] );
            p->pPend[m] = 0;
        }
        p->pPend[i] = 0;
    }
    p->pMark[i] = 1;
    Emp_OrderPlace_rec( p, Abc_ObjFaninId0(pObj) );
    Emp_OrderPlace_rec( p, Abc_ObjFaninId1(pObj) );
    Emp_OrderEmit( p, i );
    if ( fPair && p->pMark[m] == 0 )
        Emp_OrderEmit( p, m );
    p->nPairsCo += fPair;
}
static void Emp_ManComputeOrder( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    p->nOrder = 0;
    memset( p->pMark, 0, (size_t)p->nObjs );
    memset( p->pPend, 0, (size_t)p->nObjs );
    Emp_ManMarkCoPlace( p );
    Abc_AigForEachAnd( p->pNtk, pObj, i )
        Emp_OrderPlace_rec( p, i );
    assert( p->nOrder == Abc_NtkNodeNum(p->pNtk) );
}

/**Function*************************************************************

  Synopsis    [Two-output cells on pairs of roots.]

  Description [The pair is given by its roots Node[0] and Node[1], their
               phases by Ph[0] and Ph[1].]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// returns 1 if a phase of the node is an output of a two-output cell
static int Emp_ObjIsMog( Emp_Man_t * p, int i )
{
    return Emp_ObjBest(p, i, 0)->Type == EMP_MOG || Emp_ObjBest(p, i, 1)->Type == EMP_MOG;
}
static inline void Emp_PairSaveBest( Emp_Man_t * p, int * Node, Emp_Best_t pSave[2][2] )
{
    memcpy( pSave[0], Emp_ObjBest(p, Node[0], 0), sizeof(Emp_Best_t) * 2 );
    memcpy( pSave[1], Emp_ObjBest(p, Node[1], 0), sizeof(Emp_Best_t) * 2 );
}
// replaces the implementations of the roots and updates their arrival times
static void Emp_PairSetBest( Emp_Man_t * p, int * Node, Emp_Best_t pSave[2][2] )
{
    Emp_ObjDetach( p, Node[1] );
    Emp_ObjDetach( p, Node[0] );
    memcpy( Emp_ObjBest(p, Node[0], 0), pSave[0], sizeof(Emp_Best_t) * 2 );
    memcpy( Emp_ObjBest(p, Node[1], 0), pSave[1], sizeof(Emp_Best_t) * 2 );
    Emp_ObjAttach( p, Node[0] );
    Emp_ObjAttach( p, Node[1] );
    Emp_ObjUpdateArr( p, Node[0] );
    Emp_ObjUpdateArr( p, Node[1] );
}
// latest arrival of the referenced phases of the roots
static inline double Emp_PairNeedArr( Emp_Man_t * p, int * Node )
{
    return Abc_MaxDouble( Emp_ObjNeedArr(p, Node[0]), Emp_ObjNeedArr(p, Node[1]) );
}
// looks up the two-output cells of the tuple for the phases Ph of the roots Node
static Emp_MogKey_t * Emp_TupLookup( Emp_Man_t * p, Emp_Tup_t * pTup, int * Node, int * Ph, int * pnKeys )
{
    word Mask = Emp_TruthMask( pTup->nLeaves );
    int Swap = pTup->Node[0] != Node[0];   // the tuple lists Node[1] first
    word Truth0 = (Ph[Swap] ? ~pTup->Truth[0] : pTup->Truth[0]) & Mask;
    word Truth1 = (Ph[!Swap] ? ~pTup->Truth[1] : pTup->Truth[1]) & Mask;
    int iKey = Emp_LibMogLookup( p, pTup->nLeaves, Truth0, Truth1, pnKeys );
    return iKey >= 0 ? p->pMogKeys + iKey : NULL;
}
// the output of the cell used by Node[o]
static inline int Emp_TupOut( Emp_Tup_t * pTup, Emp_MogKey_t * pKey, int * Node, int o )
{
    return pKey->fSwap ^ o ^ (pTup->Node[0] != Node[0]);
}
// finds the smallest size of a two-output cell meeting the required times of the roots (iMem < 0 is the
// smallest size with the load-independent delays); in exact area (fExact), the referenced phases are
// checked and the pin loads are charged to the leaves; returns 0 if no size meets the required times
static int Emp_PairMogSize( Emp_Man_t * p, int * Node, int * Ph, Emp_Tup_t * pTup, Emp_MogKey_t * pKey, int fExact, double * pArr, int * piMem )
{
    Emp_Mog_t * pMog = p->pMogs + pKey->iMog;
    Emp_Fam_t * pFam = p->pFams + pMog->iFam;
    int fLinear = p->fGainMode || !p->fNldm;
    int m, o, k, nMem = fLinear ? 1 : pFam->nMem;
    for ( m = 0; m < nMem; m++ )
    {
        int iMem = fLinear ? -1 : m, fOk = 1;
        for ( o = 0; o < 2 && fOk; o++ )
        {
            int i = Node[o], f = Ph[o];
            pArr[o] = Emp_MogArrival( p, pMog, Emp_TupOut(pTup, pKey, Node, o), pTup->Leaves, Emp_ObjLoad(p, i, f), fExact, iMem, NULL );
            if ( fExact )
                fOk = p->pRefs[2 * i + f] == 0 || pArr[o] <= p->pReq[2 * i + f] + EMP_EPS;
            else if ( !p->pPars->fAreaMode )
            {
                // in area flow, a referenced opposite phase without its own match gets an inverter
                Emp_Best_t * pOpp = Emp_ObjBest( p, i, !f );
                int fInv = p->pRefs[2 * i + !f] > 0 && pOpp->Type != EMP_GATE && pOpp->Type != EMP_WIRE;
                fOk = pArr[o] <= p->pReq[2 * i + f] + EMP_EPS && (!fInv || pArr[o] + Emp_InvDelay(p, i, !f) <= p->pReq[2 * i + !f] + EMP_EPS);
            }
        }
        if ( fOk && fExact )
        {
            int Leaves[EMP_LEAF_MAX];
            for ( k = 0; k < pMog->nPins; k++ )
                Leaves[k] = pTup->Leaves[(int)pMog->PinToLeaf[k]];
            fOk = Emp_LeavesLoadOk( p, Leaves, pMog->PinPhase, pFam->Cin[m], pMog->nPins );
        }
        if ( fOk )
        {
            *piMem = iMem;
            return 1;
        }
    }
    return 0;
}
// sets a two-output cell with size iMem on both roots
static void Emp_PairSetMog( Emp_Man_t * p, int * Node, int * Ph, Emp_Tup_t * pTup, Emp_MogKey_t * pKey, double * pArr, int iMem )
{
    Emp_Mog_t * pMog = p->pMogs + pKey->iMog;
    Emp_Fam_t * pFam = p->pFams + pMog->iFam;
    int o, k, m = Abc_MaxInt( iMem, 0 );
    for ( o = 0; o < 2; o++ )
    {
        Emp_Best_t * pB = Emp_ObjBest( p, Node[o], Ph[o] );
        int Out = Emp_TupOut( pTup, pKey, Node, o );
        Emp_BestClean( pB );
        pB->Type      = EMP_MOG;
        pB->iFam      = pMog->iFam;
        pB->iMem      = m;
        pB->Out       = Out;
        pB->pGate     = pFam->pGates[m][Out];
        pB->pDelay    = pFam->Delay[m][Out];
        pB->pSlope    = pFam->Slope[m][Out];
        pB->pCin      = pFam->Cin[m];
        pB->ppTime    = pFam->pTime[m][Out];
        pB->Area      = pFam->Area[m];
        pB->iMog      = pKey->iMog;
        pB->Twin      = Node[!o];
        pB->TwinPhase = Ph[!o];
        pB->nPins     = pMog->nPins;
        for ( k = 0; k < pMog->nPins; k++ )
        {
            pB->Leaves[k] = pTup->Leaves[(int)pMog->PinToLeaf[k]];
            pB->Phases[k] = pMog->PinPhase[k];
        }
        // the transitions are computed without the leaf loads
        Emp_MogArrival( p, pMog, Out, pTup->Leaves, Emp_ObjLoad(p, Node[o], Ph[o]), 0, iMem, pB );
        pB->Arr = pArr[o];
    }
}

/**Function*************************************************************

  Synopsis    [Two-output cells in area-flow mode.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// sets the phase opposite to the output of a two-output cell: an inverter, or its own match if better
static void Emp_ObjSetOppositeFlow( Emp_Man_t * p, int i, int f )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, !f );
    double R = p->pReq[2 * i + !f];
    if ( pB->Type == EMP_GATE || pB->Type == EMP_WIRE || pB->Type == EMP_CONST )
    {
        double ArrInv = Emp_ObjArr(p, i, f) + Emp_InvDelay( p, i, !f );
        double FlowInv = Emp_ObjFlowRef(p, i, f) + p->InvArea;
        if ( (p->pPars->fAreaMode || ArrInv <= R + EMP_EPS) && (FlowInv < pB->Flow / Emp_ObjEst(p, i, !f) - EMP_EPS || pB->Arr > R + EMP_EPS) )
            Emp_BestSetInv( p, i, !f );
    }
    else
        Emp_BestSetInv( p, i, !f );
}
// tries the two-output cells of a pair whose nodes are matched as single-output; returns 1 if one is used
static int Emp_PairMatchFlow( Emp_Man_t * p, int n0, int n1 )
{
    Emp_MogKey_t * pKey, * pKeyBest = NULL;
    int Node[2] = { n0, n1 }, Ph[2], PhBest[2] = {0, 0}, iTup, iTupBest = -1, iMem, iMemBest = -1, fLate, j, k, o, nKeys;
    double Arr[2], ArrBest[2] = {0, 0}, Total, TotalBest = EMP_FLOW_INF, TotalOld, Flow[2];
    float Est[2];
    for ( iTup = p->pTupFirst[n0]; iTup >= 0; iTup = p->pTups[iTup].Next )
    {
        Emp_Tup_t * pTup = p->pTups + iTup;
        for ( Ph[0] = 0; Ph[0] < 2; Ph[0]++ )
        for ( Ph[1] = 0; Ph[1] < 2; Ph[1]++ )
        {
            pKey = Emp_TupLookup( p, pTup, Node, Ph, &nKeys );
            for ( j = 0; j < nKeys; j++, pKey++ )
            {
                Emp_Mog_t * pMog = p->pMogs + pKey->iMog;
                double LeafFlow = 0;
                if ( !Emp_PairMogSize(p, Node, Ph, pTup, pKey, 0, Arr, &iMem) )
                    continue;
                for ( k = 0; k < pMog->nPins; k++ )
                    LeafFlow += Emp_ObjFlowRef( p, pTup->Leaves[(int)pMog->PinToLeaf[k]], pMog->PinPhase[k] );
                Total = p->pFams[pMog->iFam].Area[Abc_MaxInt(iMem, 0)] + 2 * LeafFlow;
                if ( Emp_AreaIsBetter(Total, Abc_MaxDouble(Arr[0], Arr[1]), TotalBest, Abc_MaxDouble(ArrBest[0], ArrBest[1])) )
                {
                    TotalBest = Total;
                    iTupBest = iTup; pKeyBest = pKey; iMemBest = iMem;
                    PhBest[0] = Ph[0]; PhBest[1] = Ph[1];
                    ArrBest[0] = Arr[0]; ArrBest[1] = Arr[1];
                }
            }
        }
    }
    if ( iTupBest < 0 )
        return 0;
    // the cell must save area, unless the current matches miss their required times
    TotalOld = Emp_ObjBest(p, n0, PhBest[0])->Flow + Emp_ObjBest(p, n1, PhBest[1])->Flow;
    fLate = !p->pPars->fAreaMode && (Emp_ObjArr(p, n0, PhBest[0]) > p->pReq[2 * n0 + PhBest[0]] + EMP_EPS || Emp_ObjArr(p, n1, PhBest[1]) > p->pReq[2 * n1 + PhBest[1]] + EMP_EPS);
    if ( !fLate && TotalBest > TotalOld - EMP_EPS )
        return 0;
    // the flow is split between the roots by their fanout estimates
    Est[0] = Emp_ObjEst( p, n0, PhBest[0] );
    Est[1] = Emp_ObjEst( p, n1, PhBest[1] );
    for ( o = 0; o < 2; o++ )
        Flow[o] = TotalBest * Est[o] / (Est[0] + Est[1]);
    Emp_PairSetMog( p, Node, PhBest, p->pTups + iTupBest, pKeyBest, ArrBest, iMemBest );
    for ( o = 0; o < 2; o++ )
        Emp_ObjBest(p, Node[o], PhBest[o])->Flow = Flow[o];
    for ( o = 0; o < 2; o++ )
        Emp_ObjSetOppositeFlow( p, Node[o], PhBest[o] );
    return 1;
}
// rematches the nodes between the roots that depend on the earlier root
static void Emp_PairRemapFlow( Emp_Man_t * p, int iFirst, int iLast )
{
    int k, c, l, Beg = p->pPos[iFirst], End = p->pPos[iLast];
    if ( End - Beg <= 1 )
        return;
    Emp_TravStart( p );
    Emp_TravSetCur( p, iFirst );
    for ( k = Beg + 1; k < End; k++ )
    {
        int i = p->pOrder[k], m = p->pPartner[i], fUses = 0, fMog = Emp_ObjIsMog( p, i );
        Emp_Cut_t * pCut = Emp_ObjCuts( p, i );
        for ( c = 0; c < p->pCutNum[i] && !fUses; c++, pCut++ )
            for ( l = 0; l < pCut->nLeaves && !fUses; l++ )
                fUses = Emp_TravIsCur( p, pCut->Leaves[l] );
        // a two-output cell whose partner has been rematched
        if ( !fUses && fMog && !Emp_ObjIsMog(p, m) )
            fUses = 1;
        if ( !fUses )
            continue;
        Emp_ObjMatch( p, i, 1, 0 );
        if ( m >= 0 && p->pPos[m] < k )
        {
            // the partner loses its two-output cell
            if ( fMog )
                Emp_ObjMatch( p, m, 1, 0 );
            Emp_PairMatchFlow( p, m, i );
        }
        Emp_TravSetCur( p, i );
    }
}
// adds (Sign = 1) or removes (Sign = -1) the pin loads of the implemented phases of a node
static void Emp_ObjChangeLoads( Emp_Man_t * p, int i, float Sign )
{
    int f, k;
    if ( !p->fNldm )
        return;
    for ( f = 0; f < 2; f++ )
    {
        Emp_Best_t * pB = Emp_ObjBest( p, i, f );
        if ( !p->pImpl[2 * i + f] || Emp_ObjIsTwinSecond(p, i, f) )
            continue;
        if ( pB->Type == EMP_INV )
            Emp_LoadAdd( p, i, !f, Sign * Emp_InvCin(p, pB->iMem), Sign * Emp_InvCinD(p, pB->iMem) );
        else if ( pB->Type == EMP_GATE || pB->Type == EMP_MOG )
            for ( k = 0; k < pB->nPins; k++ )
                Emp_LoadAdd( p, pB->Leaves[k], pB->Phases[k], Sign * pB->pCin[k], Sign * Emp_BestCinD(p, pB, k) );
    }
}
// one area-flow pass in the processing order
static void Emp_ManAreaFlow( Emp_Man_t * p, int fMogs )
{
    int k;
    for ( k = 0; k < p->nOrder; k++ )
    {
        int i = p->pOrder[k], m = p->pPartner[i];
        // the match is chosen without the pin loads of the old one, charging its own pin loads to the leaves
        Emp_ObjChangeLoads( p, i, -1 );
        Emp_ObjMatch( p, i, 1, p->fNldm );
        Emp_ObjChangeLoads( p, i, 1 );
        if ( !fMogs || m < 0 )
            continue;
        if ( p->pPos[m] > k )
            continue;
        if ( Emp_PairMatchFlow( p, m, i ) )
            Emp_PairRemapFlow( p, m, i );
    }
}

/**Function*************************************************************

  Synopsis    [Exact area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// area that referencing the leaves would add to the cover
static float Emp_MeasureLeaves( Emp_Man_t * p, int * pLeaves, signed char * pPhases, int nLeaves )
{
    float Area = 0;
    int k;
    for ( k = 0; k < nLeaves; k++ )
        Area += Emp_ObjRef_rec( p, pLeaves[k], pPhases[k], 1 );
    for ( k = nLeaves - 1; k >= 0; k-- )
        Emp_ObjRef_rec( p, pLeaves[k], pPhases[k], 0 );
    return Area;
}
// best own implementation of the phase under the arrival limit; the node is detached
static float Emp_ObjFindExact( Emp_Man_t * p, int i, int f, double Limit, Emp_Best_t * pRes )
{
    Emp_Cut_t * pCut = Emp_ObjCuts( p, i );
    float AreaBest = EMP_FINF, Area;
    double ArrBest = EMP_INF;
    int c, n, k;
    for ( c = 0; c < p->pCutNum[i]; c++, pCut++ )
    {
        // area added by the leaves for each combination of leaf phases
        int CacheSig[16], nCache = 0;
        float CacheArea[16];
        if ( pCut->nLeaves == 1 && pCut->Leaves[0] == i )
            continue;
        if ( pCut->nLeaves == 0 )
        {
            if ( AreaBest > 0 || ArrBest > 0 )
            {
                Emp_BestSetConst( pRes, (pCut->Truth != 0) ^ f );
                AreaBest = 0; ArrBest = 0;
            }
            continue;
        }
        if ( pCut->nLeaves == 1 )
        {
            int Leaf = pCut->Leaves[0];
            signed char Ph = (signed char)(f ^ (int)(pCut->Truth & 1));
            double Arr = Emp_ObjArr( p, Leaf, Ph );
            if ( Arr > Limit + EMP_EPS )
                continue;
            Area = Emp_MeasureLeaves( p, &Leaf, &Ph, 1 );
            if ( Emp_AreaIsBetter(Area, Arr, AreaBest, ArrBest) )
            {
                Emp_BestSetWire( p, pRes, Leaf, Ph, Area );
                AreaBest = Area; ArrBest = Arr;
            }
            continue;
        }
        for ( n = 0; n < pCut->nCell[f]; n++ )
        {
            Emp_Cell_t * pCell = p->pCells + pCut->iCell[f] + n;
            Emp_Fam_t * pFam = p->pFams + pCell->iFam;
            int m, nMem = p->fNldm ? pFam->nMem : 1;
            Emp_Best_t Cand;
            if ( pCell->Area > AreaBest + EMP_EPS )
                continue;
            for ( k = 0; k < nCache; k++ )
                if ( CacheSig[k] == pCell->LeafSig )
                    break;
            if ( k == nCache )
            {
                signed char LeafPh[EMP_LEAF_MAX];
                int j;
                for ( j = 0; j < pCut->nLeaves; j++ )
                    LeafPh[j] = (signed char)((pCell->LeafSig >> j) & 1);
                CacheSig[k] = pCell->LeafSig;
                CacheArea[k] = Emp_MeasureLeaves( p, pCut->Leaves, LeafPh, pCut->nLeaves );
                if ( nCache < 15 )
                    nCache++;
            }
            // the smallest size meeting the limit
            for ( m = 0; m < nMem; m++ )
            {
                Area = pFam->Area[m] + CacheArea[k];
                if ( Area > AreaBest + EMP_EPS )
                    break;
                Emp_CellArrival( p, pCell, pCut->Leaves, Emp_ObjLoad(p, i, f), 1, p->fNldm ? m : -1, &Cand );
                if ( Cand.Arr > Limit + EMP_EPS || !Emp_LeavesLoadOk(p, Cand.Leaves, Cand.Phases, pFam->Cin[m], pCell->nPins) )
                    continue;
                if ( Emp_AreaIsBetter(Area, Cand.Arr, AreaBest, ArrBest) )
                {
                    Emp_BestSetGate( p, pRes, pCell, m, &Cand, Area );
                    AreaBest = Area; ArrBest = Cand.Arr;
                }
                break;
            }
        }
    }
    return AreaBest;
}
// chooses the implementation of a detached node and attaches it; returns the area added,
// or EMP_FINF if nothing meets the required times (the node stays detached)
static float Emp_ObjChooseExact( Emp_Man_t * p, int i )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, 0 ), Save[2], Res[2], Tmp;
    int Need[2], f, fFound = 0;
    double * pReq = p->pReq + 2 * i, ArrBest = EMP_INF;
    float AreaBest = EMP_FINF, Area = 0;
    Need[0] = p->pRefs[2 * i] > 0;
    Need[1] = p->pRefs[2 * i + 1] > 0;
    if ( !Need[0] && !Need[1] )
    {
        Emp_ObjUpdateArr( p, i );
        return 0;
    }
    Save[0] = pB[0]; Save[1] = pB[1];
    // own implementation of every needed phase
    for ( f = 0; f < 2; f++ )
    {
        if ( !Need[f] )
            continue;
        if ( Emp_ObjFindExact(p, i, f, pReq[f], &Tmp) == EMP_FINF )
            break;
        pB[f] = Tmp;
        Area += Emp_ObjImpl( p, i, f, 1 );
    }
    if ( f == 2 )
    {
        Res[0] = pB[0]; Res[1] = pB[1];
        AreaBest = Area;
        ArrBest  = Emp_ObjNeedArr( p, i );
        fFound   = 1;
    }
    Emp_ObjDetach( p, i );
    pB[0] = Save[0]; pB[1] = Save[1];
    // one phase with its own gate, the other one with an inverter
    for ( f = 0; f < 2; f++ )
    {
        double Limit;
        if ( !Need[!f] )
            continue;
        Limit = pReq[!f] - Emp_InvDelay( p, i, !f );
        if ( Need[f] )
            Limit = Abc_MinDouble( Limit, pReq[f] );
        if ( Emp_ObjFindExact(p, i, f, Limit, &Tmp) == EMP_FINF )
            continue;
        pB[f] = Tmp;
        Emp_BestSetInv( p, i, !f );
        Area = Emp_ObjAttach( p, i );
        if ( Emp_AreaIsBetter(Area, Emp_ObjNeedArr(p, i), AreaBest, ArrBest) )
        {
            Res[0] = pB[0]; Res[1] = pB[1];
            AreaBest = Area;
            ArrBest  = Emp_ObjNeedArr( p, i );
            fFound   = 1;
        }
        Emp_ObjDetach( p, i );
        pB[0] = Save[0]; pB[1] = Save[1];
    }
    if ( !fFound )
        return EMP_FINF;
    pB[0] = Res[0]; pB[1] = Res[1];
    for ( f = 0; f < 2; f++ )
        if ( pB[f].Type == EMP_NONE && pB[!f].Type != EMP_INV && pB[!f].Type != EMP_NONE )
            Emp_BestSetInv( p, i, f );
    Area = Emp_ObjAttach( p, i );
    Emp_ObjUpdateArr( p, i );
    return Area;
}
// replaces the implementations of the node
static void Emp_ObjSetBest( Emp_Man_t * p, int i, Emp_Best_t * pSave )
{
    Emp_ObjDetach( p, i );
    memcpy( Emp_ObjBest(p, i, 0), pSave, sizeof(Emp_Best_t) * 2 );
    Emp_ObjAttach( p, i );
}
// exact area of one node; the old implementation is restored if the area grows
// or (with incremental timing) an output misses the target
static void Emp_ObjExact( Emp_Man_t * p, int i )
{
    Emp_Best_t Old[2];
    float AreaOld, AreaNew;
    if ( !Emp_ObjIsUsed(p, i) )
    {
        Emp_ObjUpdateArr( p, i );
        return;
    }
    memcpy( Old, Emp_ObjBest(p, i, 0), sizeof(Emp_Best_t) * 2 );
    p->fTrack = p->fIncr;
    AreaOld = Emp_ObjDetach( p, i );
    AreaNew = Emp_ObjChooseExact( p, i );
    if ( AreaNew > AreaOld + EMP_EPS )
    {
        Emp_ObjSetBest( p, i, Old );
        Emp_ObjUpdateArr( p, i );
    }
    else if ( p->fTrack && !Emp_ManPropagate(p) )
    {
        Emp_ObjSetBest( p, i, Old );
        Vec_IntPush( p->vDirty, i );
    }
    if ( p->fTrack )
    {
        // propagates the undo, if any
        Emp_ManPropagate( p );
        Emp_ManAcceptPos( p );
    }
    p->fTrack = 0;
}
// updates the arrival times of the nodes between the roots; returns 0 if one misses its required time
static int Emp_PairCheckBetween( Emp_Man_t * p, int iFirst, int iLast )
{
    int k, f, l, Beg = p->pPos[iFirst], End = p->pPos[iLast], fOk = 1;
    Vec_IntClear( p->vSaved );
    if ( End - Beg <= 1 )
        return 1;
    Emp_TravStart( p );
    Emp_TravSetCur( p, iFirst );
    for ( k = Beg + 1; k < End; k++ )
    {
        int i = p->pOrder[k], fUses = 0;
        for ( f = 0; f < 2 && !fUses; f++ )
        {
            Emp_Best_t * pB = Emp_ObjBest( p, i, f );
            if ( pB->Type == EMP_GATE || pB->Type == EMP_MOG || pB->Type == EMP_WIRE )
                for ( l = 0; l < pB->nPins && !fUses; l++ )
                    fUses = Emp_TravIsCur( p, pB->Leaves[l] );
        }
        if ( !fUses )
            continue;
        Vec_IntPush( p->vSaved, i );
        p->pArrSave[2 * i + 0] = Emp_ObjArr( p, i, 0 );
        p->pArrSave[2 * i + 1] = Emp_ObjArr( p, i, 1 );
        Emp_ObjUpdateArr( p, i );
        if ( Emp_ObjArr(p, i, 0) != p->pArrSave[2 * i + 0] || Emp_ObjArr(p, i, 1) != p->pArrSave[2 * i + 1] )
            Emp_TravSetCur( p, i );
        for ( f = 0; f < 2; f++ )
            if ( p->pImpl[2 * i + f] && Emp_ObjArr(p, i, f) > p->pReq[2 * i + f] + EMP_EPS )
                fOk = 0;
    }
    return fOk;
}
// restores the arrival times saved by Emp_PairCheckBetween()
static void Emp_PairRestoreBetween( Emp_Man_t * p )
{
    int k, i;
    Vec_IntForEachEntry( p->vSaved, i, k )
    {
        Emp_ObjBest(p, i, 0)->Arr = p->pArrSave[2 * i + 0];
        Emp_ObjBest(p, i, 1)->Arr = p->pArrSave[2 * i + 1];
    }
}
// tries a two-output cell for both detached roots; returns the area added or EMP_FINF
static float Emp_PairTryMog( Emp_Man_t * p, int * Node, int * Ph, Emp_Tup_t * pTup, Emp_MogKey_t * pKey, double * pArr, int iMem )
{
    float Area = 0;
    int o;
    Emp_PairSetMog( p, Node, Ph, pTup, pKey, pArr, iMem );
    // the opposite phases: an inverter, or their own implementation if the inverter is too slow
    for ( o = 0; o < 2; o++ )
    {
        int i = Node[o], f = Ph[o];
        if ( p->pRefs[2 * i + !f] > 0 && pArr[o] + Emp_InvDelay(p, i, !f) > p->pReq[2 * i + !f] + EMP_EPS )
        {
            Emp_Best_t Tmp;
            if ( Emp_ObjFindExact(p, i, !f, p->pReq[2 * i + !f], &Tmp) == EMP_FINF )
                return EMP_FINF;
            *Emp_ObjBest( p, i, !f ) = Tmp;
        }
        else
            Emp_BestSetInv( p, i, !f );
    }
    for ( o = 0; o < 2; o++ )
        Area += Emp_ObjAttach( p, Node[o] );
    return Area;
}
// tries the two-output cells for the detached roots; updates the best area, arrival, and implementations
static void Emp_PairExactMogs( Emp_Man_t * p, int * Node, float * pAreaBest, double * pArrBest, Emp_Best_t Res[2][2] )
{
    int Ph[2], iTup, iMem, j, t, nKeys, nTried = 0, TriedSig[64];
    float TriedArea[64], Area;
    double Arr[2];
    for ( iTup = p->pTupFirst[Node[0]]; iTup >= 0; iTup = p->pTups[iTup].Next )
    {
        Emp_Tup_t * pTup = p->pTups + iTup;
        for ( Ph[0] = 0; Ph[0] < 2; Ph[0]++ )
        for ( Ph[1] = 0; Ph[1] < 2; Ph[1]++ )
        {
            Emp_MogKey_t * pKey = Emp_TupLookup( p, pTup, Node, Ph, &nKeys );
            for ( j = 0; j < nKeys; j++, pKey++ )
            {
                Emp_Mog_t * pMog = p->pMogs + pKey->iMog;
                float AreaMog;
                int Sig;
                if ( !Emp_PairMogSize(p, Node, Ph, pTup, pKey, 1, Arr, &iMem) )
                    continue;
                // skip the cell if a cheaper one with the same leaf phases was tried
                AreaMog = p->pFams[pMog->iFam].Area[Abc_MaxInt(iMem, 0)];
                Sig = (iTup << 8) | (Ph[0] << 7) | (Ph[1] << 6) | pMog->LeafSig;
                for ( t = 0; t < nTried; t++ )
                    if ( TriedSig[t] == Sig && TriedArea[t] <= AreaMog + 1e-6 )
                        break;
                if ( t < nTried )
                    continue;
                if ( nTried < 64 )
                {
                    TriedSig[nTried] = Sig;
                    TriedArea[nTried++] = AreaMog;
                }
                Area = Emp_PairTryMog( p, Node, Ph, pTup, pKey, Arr, iMem );
                if ( Area != EMP_FINF && Emp_AreaIsBetter(Area, Emp_PairNeedArr(p, Node), *pAreaBest, *pArrBest) )
                {
                    *pAreaBest = Area;
                    *pArrBest  = Emp_PairNeedArr( p, Node );
                    Emp_PairSaveBest( p, Node, Res );
                }
                Emp_ObjDetach( p, Node[1] );
                Emp_ObjDetach( p, Node[0] );
            }
        }
    }
}
// joint exact area of two roots: single-output implementations versus two-output cells
static void Emp_PairExactInt( Emp_Man_t * p, int n0, int n1, int fCheck )
{
    Emp_Best_t Old[2][2], Res[2][2];
    int Node[2] = { n0, n1 }, o;
    float AreaOld, AreaBest, Area;
    double ArrBest, ReqSave[2] = { -1, -1 };
    if ( !Emp_ObjIsUsed(p, n0) && !Emp_ObjIsUsed(p, n1) )
    {
        Emp_ObjUpdateArr( p, n1 );
        return;
    }
    Emp_PairSaveBest( p, Node, Old );
    // in reverse order, the fanouts of the earlier root between the roots are decided later
    // assuming its current arrival: the root must not become later
    if ( !fCheck && p->pPos[n1] - p->pPos[n0] > 1 )
        for ( o = 0; o < 2; o++ )
        {
            ReqSave[o] = p->pReq[2 * n0 + o];
            p->pReq[2 * n0 + o] = Abc_MinDouble( p->pReq[2 * n0 + o], Emp_ObjArr(p, n0, o) );
        }
    AreaOld  = Emp_ObjDetach( p, n1 );
    AreaOld += Emp_ObjDetach( p, n0 );
    // single-output implementations (a root with a two-output cell is rematched first)
    for ( o = 0; o < 2; o++ )
        if ( Emp_ObjIsMog(p, Node[o]) )
            Emp_ObjMatch( p, Node[o], 0, 0 );
    AreaBest = Emp_ObjChooseExact( p, n0 );
    if ( AreaBest != EMP_FINF )
    {
        Area = Emp_ObjChooseExact( p, n1 );
        AreaBest = Area == EMP_FINF ? EMP_FINF : AreaBest + Area;
    }
    ArrBest = Emp_PairNeedArr( p, Node );
    Emp_PairSaveBest( p, Node, Res );
    Emp_ObjDetach( p, n1 );
    Emp_ObjDetach( p, n0 );
    Emp_PairExactMogs( p, Node, &AreaBest, &ArrBest, Res );
    if ( ReqSave[0] != -1 )
        for ( o = 0; o < 2; o++ )
            p->pReq[2 * n0 + o] = ReqSave[o];
    // commit the best configuration, or restore the old one
    if ( AreaBest > AreaOld - EMP_EPS )
    {
        Emp_PairSetBest( p, Node, Old );
        if ( fCheck )
            Emp_PairCheckBetween( p, n0, n1 );
        return;
    }
    Emp_PairSetBest( p, Node, Res );
    if ( fCheck && !Emp_PairCheckBetween(p, n0, n1) )
    {
        // a node between the roots misses its required time: roll back
        Emp_PairRestoreBetween( p );
        Emp_PairSetBest( p, Node, Old );
    }
}
// the same with incremental timing: the decision is undone if an output misses the target
static void Emp_PairExact( Emp_Man_t * p, int n0, int n1, int fCheck )
{
    Emp_Best_t Old[2][2];
    int Node[2] = { n0, n1 };
    if ( !p->fIncr )
    {
        Emp_PairExactInt( p, n0, n1, fCheck );
        return;
    }
    Emp_PairSaveBest( p, Node, Old );
    p->fTrack = 1;
    Emp_PairExactInt( p, n0, n1, fCheck );
    if ( !Emp_ManPropagate(p) )
    {
        Emp_PairSetBest( p, Node, Old );
        Vec_IntPush( p->vDirty, n0 );
        Vec_IntPush( p->vDirty, n1 );
        Emp_ManPropagate( p );
    }
    Emp_ManAcceptPos( p );
    p->fTrack = 0;
}
// exact area in the processing order; a pair is decided at its later root
static void Emp_ManExactArea( Emp_Man_t * p, int fPairs )
{
    int k;
    for ( k = 0; k < p->nOrder; k++ )
    {
        int i = p->pOrder[k], m = p->pPartner[i];
        if ( m < 0 || (!fPairs && !Emp_ObjIsMog(p, i)) )
            Emp_ObjExact( p, i );
        else if ( fPairs && p->pPos[m] < k )
            Emp_PairExact( p, m, i, 1 );
        else // without pairs, a two-output cell is kept
            Emp_ObjUpdateArr( p, i );
    }
}
// exact area in reverse order; required times are propagated as the nodes are decided
static void Emp_ManExactAreaRev( Emp_Man_t * p, int fPairs )
{
    Abc_Obj_t * pObj;
    int i, k;
    for ( k = p->nOrder - 1; k >= 0; k-- )
    {
        int n = p->pOrder[k], m = p->pPartner[n];
        if ( m < 0 || (!fPairs && !Emp_ObjIsMog(p, n)) )
            Emp_ObjExact( p, n );
        else if ( fPairs && p->pPos[m] < k )
            Emp_PairExact( p, m, n, 0 );
        Emp_ObjPropagateReq( p, n );
    }
    Abc_AigForEachAnd( p->pNtk, pObj, i )
        Emp_ObjUpdateArr( p, i );
}

/**Function*************************************************************

  Synopsis    [Building the mapped network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Obj_t * Emp_ManBuild_rec( Emp_Man_t * p, Abc_Ntk_t * pNew, Vec_Int_t * vCopy, int i, int f )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f ), * pT;
    Abc_Obj_t * pObj, * pTwin, * pFanins[EMP_LEAF_MAX];
    int k, Entry = Vec_IntEntry( vCopy, 2 * i + f );
    if ( Entry >= 0 )
        return Abc_NtkObj( pNew, Entry );
    switch ( pB->Type )
    {
    case EMP_PI:
        return NULL;
    case EMP_CONST:
        pObj = pB->Phases[0] ? Abc_NtkCreateNodeConst1( pNew ) : Abc_NtkCreateNodeConst0( pNew );
        break;
    case EMP_INV:
        pFanins[0] = Emp_ManBuild_rec( p, pNew, vCopy, i, !f );
        if ( pFanins[0] == NULL )
            return NULL;
        pObj = Abc_NtkCreateNode( pNew );
        pObj->pData = pB->pGate;
        Abc_ObjAddFanin( pObj, pFanins[0] );
        break;
    case EMP_WIRE:
        pObj = Emp_ManBuild_rec( p, pNew, vCopy, pB->Leaves[0], pB->Phases[0] );
        break;
    case EMP_GATE:
    case EMP_MOG:
        for ( k = 0; k < pB->nPins; k++ )
            if ( (pFanins[k] = Emp_ManBuild_rec(p, pNew, vCopy, pB->Leaves[k], pB->Phases[k])) == NULL )
                return NULL;
        // a two-output cell may have been built from its other output
        if ( pB->Type == EMP_MOG && (Entry = Vec_IntEntry(vCopy, 2 * i + f)) >= 0 )
            return Abc_NtkObj( pNew, Entry );
        pObj = Abc_NtkCreateNode( pNew );
        pObj->pData = pB->pGate;
        if ( pB->Type == EMP_GATE )
        {
            // the pins of the size may be ordered differently from the family
            Emp_Fam_t * pFam = p->pFams + pB->iFam;
            int iPin[EMP_LEAF_MAX];
            assert( pFam->pGates[pB->iMem][0] == pB->pGate );
            for ( k = 0; k < pB->nPins; k++ )
                iPin[(int)pFam->Perm[pB->iMem][k]] = k;
            for ( k = 0; k < pB->nPins; k++ )
                Abc_ObjAddFanin( pObj, pFanins[iPin[k]] );
            break;
        }
        // the two outputs of a cell are created in the order of their gates
        pT = Emp_ObjBest( p, pB->Twin, pB->TwinPhase );
        assert( pT->Type == EMP_MOG && pT->Twin == i && pT->TwinPhase == f && pT->iMog == pB->iMog );
        pTwin = Abc_NtkCreateNode( pNew );
        if ( pB->pGate > pT->pGate )
            ABC_SWAP( Abc_Obj_t *, pObj, pTwin );
        pObj->pData  = pB->pGate;
        pTwin->pData = pT->pGate;
        for ( k = 0; k < pB->nPins; k++ )
        {
            assert( pB->Leaves[k] == pT->Leaves[k] && pB->Phases[k] == pT->Phases[k] );
            Abc_ObjAddFanin( pObj, pFanins[k] );
            Abc_ObjAddFanin( pTwin, pFanins[k] );
        }
        Vec_IntWriteEntry( vCopy, 2 * pB->Twin + pB->TwinPhase, Abc_ObjId(pTwin) );
        break;
    default:
        return NULL;
    }
    Vec_IntWriteEntry( vCopy, 2 * i + f, Abc_ObjId(pObj) );
    return pObj;
}
static Abc_Ntk_t * Emp_ManBuild( Emp_Man_t * p )
{
    Abc_Ntk_t * pNew;
    Abc_Obj_t * pObj, * pObjNew, * pFanin;
    Vec_Int_t * vCopy;
    int i;
    pNew = Abc_NtkAlloc( ABC_NTK_LOGIC, ABC_FUNC_MAP, 1 );
    pNew->pName = Extra_UtilStrsav( p->pNtk->pName ? p->pNtk->pName : "emap" );
    pNew->pSpec = Extra_UtilStrsav( p->pNtk->pSpec );
    pNew->pManFunc = p->pMio;
    vCopy = Vec_IntStartFull( 2 * p->nObjs );
    Abc_NtkForEachPi( p->pNtk, pObj, i )
    {
        pObjNew = Abc_NtkCreatePi( pNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObj), NULL );
        Vec_IntWriteEntry( vCopy, 2 * Abc_ObjId(pObj), Abc_ObjId(pObjNew) );
    }
    Abc_NtkForEachPo( p->pNtk, pObj, i )
    {
        pObjNew = Abc_NtkCreatePo( pNew );
        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObj), NULL );
        pFanin = Emp_ManBuild_rec( p, pNew, vCopy, Abc_ObjFaninId0(pObj), Abc_ObjFaninC0(pObj) );
        if ( pFanin == NULL )
        {
            Vec_IntFree( vCopy );
            Abc_NtkDelete( pNew );
            return NULL;
        }
        Abc_ObjAddFanin( pObjNew, pFanin );
    }
    Vec_IntFree( vCopy );
    if ( !Abc_NtkCheck( pNew ) )
    {
        Abc_NtkDelete( pNew );
        return NULL;
    }
    return pNew;
}
static void Emp_ManPrintRound( Emp_Man_t * p, char * pTitle, float Area, double Delay )
{
    int nFa, nHa, nMogs;
    if ( !p->pPars->fVerbose )
        return;
    nMogs = Emp_ManCountMogs( p, &nFa, &nHa );
    printf( "%-12s: Area = %12.2f  Delay = %10.2f  MOG = %5d (FA %5d HA %5d)  ", pTitle, Area, Delay, nMogs, nFa, nHa );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
}

/**Function*************************************************************

  Synopsis    [Manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Emp_Man_t * Emp_ManStart( Abc_Ntk_t * pNtk, Mio_Library_t * pMio, Emap_Par_t * pPars )
{
    Emp_Man_t * p = ABC_CALLOC( Emp_Man_t, 1 );
    int n = Abc_NtkObjNumMax( pNtk );
    p->pNtk      = pNtk;
    p->pMio      = pMio;
    p->pPars     = pPars;
    p->nObjs     = n;
    p->pCutBeg   = ABC_CALLOC( int, n );
    p->pCutNum   = ABC_CALLOC( int, n );
    p->pCutSet   = ABC_ALLOC( Emp_Cut_t, pPars->nCutNum + 2 );
    p->pBest     = ABC_ALLOC( Emp_Best_t, 2 * n );
    p->pRefs     = ABC_CALLOC( int, 2 * n );
    p->pImpl     = ABC_CALLOC( char, 2 * n );
    p->pEst      = ABC_ALLOC( float, 2 * n );
    p->pReq      = ABC_ALLOC( double, 2 * n );
    p->pLoad     = ABC_CALLOC( float, 2 * n );
    p->pLoadD    = ABC_CALLOC( float, 2 * n );
    p->pPartner  = ABC_FALLOC( int, n );
    p->pTupFirst = ABC_FALLOC( int, n );
    p->pCoPlace  = ABC_CALLOC( char, n );
    p->pOrder    = ABC_ALLOC( int, n );
    p->pPos      = ABC_FALLOC( int, n );
    p->pMark     = ABC_CALLOC( char, n );
    p->pPend     = ABC_CALLOC( char, n );
    p->pTrav     = ABC_CALLOC( int, n );
    p->vTemp     = Vec_IntAlloc( 1000 );
    p->vSaved    = Vec_IntAlloc( 100 );
    p->vDirty    = Vec_IntAlloc( 100 );
    p->vHeap     = Vec_IntAlloc( 100 );
    p->vPoTouched = Vec_IntAlloc( 100 );
    p->pInQ      = ABC_CALLOC( char, n );
    p->pPoDrv    = ABC_CALLOC( char, 2 * n );
    p->pPoArr    = ABC_CALLOC( double, 2 * n );
    p->pCommit   = ABC_CALLOC( SC_Pair, 4 * n );
    p->pArrSave  = ABC_ALLOC( double, 2 * n );
    p->clkStart  = Abc_Clock();
    p->SensK     = 1;
    p->pGood     = ABC_ALLOC( Emp_Best_t, 2 * n );
    p->AreaGood  = EMP_FINF;
    p->DelayGood = EMP_INF;
    return p;
}
static void Emp_ManStop( Emp_Man_t * p )
{
    ABC_FREE( p->pCells );
    ABC_FREE( p->pHash );
    ABC_FREE( p->pGroupSize );
    ABC_FREE( p->pGroupArea );
    ABC_FREE( p->pGroupDelay );
    ABC_FREE( p->pMogs );
    ABC_FREE( p->pMogKeys );
    ABC_FREE( p->pFams );
    ABC_FREE( p->pCuts );
    ABC_FREE( p->pCutBeg );
    ABC_FREE( p->pCutNum );
    ABC_FREE( p->pCutSet );
    ABC_FREE( p->pBest );
    ABC_FREE( p->pGood );
    ABC_FREE( p->pRefs );
    ABC_FREE( p->pImpl );
    ABC_FREE( p->pEst );
    ABC_FREE( p->pReq );
    ABC_FREE( p->pLoad );
    ABC_FREE( p->pLoadD );
    Vec_IntFree( p->vDirty );
    Vec_IntFree( p->vHeap );
    Vec_IntFree( p->vPoTouched );
    if ( p->vFans ) Vec_WecFree( p->vFans );
    ABC_FREE( p->pInQ );
    ABC_FREE( p->pPoDrv );
    ABC_FREE( p->pPoArr );
    ABC_FREE( p->pCommit );
    ABC_FREE( p->pArcs );
    ABC_FREE( p->pTups );
    ABC_FREE( p->pPartner );
    ABC_FREE( p->pTupFirst );
    ABC_FREE( p->pCoPlace );
    ABC_FREE( p->pOrder );
    ABC_FREE( p->pPos );
    ABC_FREE( p->pMark );
    ABC_FREE( p->pPend );
    ABC_FREE( p->pTrav );
    Vec_IntFree( p->vTemp );
    Vec_IntFree( p->vSaved );
    ABC_FREE( p->pArrSave );
    ABC_FREE( p );
}
static void Emp_ManInitObjs( Emp_Man_t * p )
{
    Abc_Obj_t * pObj;
    int i, Const = Abc_ObjId( Abc_AigConst1(p->pNtk) );
    for ( i = 0; i < 2 * p->nObjs; i++ )
        Emp_BestClean( p->pBest + i );
    Abc_NtkForEachObj( p->pNtk, pObj, i )
    {
        p->pEst[2 * i] = p->pEst[2 * i + 1] = (float)Abc_MaxInt( 1, Abc_ObjFanoutNum(pObj) );
        p->pReq[2 * i] = p->pReq[2 * i + 1] = EMP_INF;
        p->pLoad[2 * i] = p->pLoad[2 * i + 1] = p->LoadAvg * p->pEst[2 * i];
        p->pLoadD[2 * i] = p->pLoadD[2 * i + 1] = 0;
    }
    Emp_BestSetConst( Emp_ObjBest(p, Const, 0), 1 );
    Emp_BestSetConst( Emp_ObjBest(p, Const, 1), 0 );
    {
        Emp_Cut_t Cut;
        memset( &Cut, 0, sizeof(Emp_Cut_t) );
        Cut.Truth = ~(word)0;
        Cut.iCell[0] = Cut.iCell[1] = -1;
        Emp_ObjAddCuts( p, Const, &Cut, 1 );
    }
    Abc_NtkForEachCi( p->pNtk, pObj, i )
    {
        Emp_Best_t * pB = Emp_ObjBest( p, Abc_ObjId(pObj), 0 );
        Emp_Cut_t Cut;
        pB[0].Type = EMP_PI;
        Emp_BestSetArr( pB, 0 );
        pB[0].Flow = 0;
        Emp_BestSetInv( p, Abc_ObjId(pObj), 1 );
        Emp_CutSetUnit( &Cut, Abc_ObjId(pObj) );
        Emp_ObjAddCuts( p, Abc_ObjId(pObj), &Cut, 1 );
    }
}

/**Function*************************************************************

  Synopsis    [Sizing of the cells of the cover with the NLDM tables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Emp_Fam_t * Emp_BestFam( Emp_Man_t * p, Emp_Best_t * pB )
{
    return p->pFams + (pB->Type == EMP_INV ? p->iFamInv : pB->iFam);
}
static inline int Emp_BestIsSized( Emp_Best_t * pB )
{
    return pB->Type == EMP_GATE || pB->Type == EMP_MOG || pB->Type == EMP_INV;
}
// the number of pins of a sized implementation and the fanin (2 * node + phase) of pin k;
// an inverter is driven by the other phase
static inline int Emp_BestFaninNum( Emp_Best_t * pB ) { return pB->Type == EMP_INV ? 1 : pB->nPins; }
static inline int Emp_BestFanin( Emp_Man_t * p, int i, int f, int k )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f );
    return pB->Type == EMP_INV ? 2 * i + !f : 2 * pB->Leaves[k] + pB->Phases[k];
}
// arrival of the implementation of (i, f) with size m, including the change of the leaf loads
static double Emp_BestArrivalMem( Emp_Man_t * p, int i, int f, int m )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f );
    Emp_Fam_t * pFam = Emp_BestFam( p, pB );
    SC_Pair Arr = { 0.0, 0.0 }, Slew = { 0.0, 0.0 };
    int k, Out = pB->Type == EMP_MOG ? pB->Out : 0;
    for ( k = 0; k < Emp_BestFaninNum(pB); k++ )
    {
        Emp_Best_t * pL = p->pBest + Emp_BestFanin( p, i, f, k );
        float Shift = pL->Sens * (pFam->Cin[m][k] - pFam->Cin[pB->iMem][k]);
        Emp_ArcEval( pFam->pTime[m][Out][k], pFam->Delay[m][Out][k], pFam->Slope[m][Out][k], pL, Shift, Emp_ObjLoad(p, i, f), p->pLoadD[2 * i + f], &Arr, &Slew );
    }
    return Abc_MaxFloat( Arr.rise, Arr.fall );
}
// returns 0 if the pin loads of size m push a leaf beyond its required time
static int Emp_BestLeavesOkMem( Emp_Man_t * p, int i, int f, int m )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f );
    Emp_Fam_t * pFam = Emp_BestFam( p, pB );
    int k;
    for ( k = 0; k < Emp_BestFaninNum(pB); k++ )
    {
        int e = Emp_BestFanin( p, i, f, k );
        if ( p->pBest[e].Arr + p->pBest[e].Sens * (pFam->Cin[m][k] - pFam->Cin[pB->iMem][k]) > p->pReq[e] + EMP_EPS )
            return 0;
    }
    return 1;
}
// changes the size of the implementation of (i, f) (both outputs of a two-output cell)
static void Emp_BestSetMem( Emp_Man_t * p, int i, int f, int m )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f ), * pT;
    Emp_Fam_t * pFam = Emp_BestFam( p, pB );
    int k, mOld = pB->iMem;
    if ( m == mOld )
        return;
    for ( k = 0; k < Emp_BestFaninNum(pB); k++ )
    {
        int e = Emp_BestFanin( p, i, f, k );
        Emp_LoadAdd( p, e >> 1, e & 1, pFam->Cin[m][k] - pFam->Cin[mOld][k], pFam->CinD[m][k] - pFam->CinD[mOld][k] );
    }
    pT = pB->Type == EMP_MOG ? Emp_ObjBest( p, pB->Twin, pB->TwinPhase ) : NULL;
    for ( ; pB; pB = pT, pT = NULL )
    {
        int Out = pB->Type == EMP_MOG ? pB->Out : 0;
        pB->iMem   = m;
        pB->pGate  = pFam->pGates[m][Out];
        pB->Area   = pFam->Area[m];
        if ( pB->Type == EMP_INV )
            continue;
        pB->pDelay = pFam->Delay[m][Out];
        pB->pSlope = pFam->Slope[m][Out];
        pB->pCin   = pFam->Cin[m];
        pB->ppTime = pFam->pTime[m][Out];
    }
}
// node phases of the cover that can be resized, in reverse topological order
static void Emp_ManSizedNodes( Emp_Man_t * p, Vec_Int_t * vNodes )
{
    int i, f;
    Vec_IntClear( vNodes );
    for ( i = p->nObjs - 1; i >= 0; i-- )
        for ( f = 0; f < 2; f++ )
        {
            Emp_Best_t * pB = Emp_ObjBest( p, i, f );
            if ( !p->pImpl[2 * i + f] || !Emp_BestIsSized(pB) || Emp_BestFam(p, pB)->nMem < 2 )
                continue;
            // a two-output cell is sized once
            if ( Emp_BestTwinUsed(p, pB) > 2 * i + f )
                continue;
            Vec_IntPush( vNodes, 2 * i + f );
        }
}
// worst slack of the implementation (both outputs of a two-output cell) with size m
static double Emp_BestSlackMem( Emp_Man_t * p, int i, int f, int m )
{
    Emp_Best_t * pB = Emp_ObjBest( p, i, f );
    double Slack = p->pReq[2 * i + f] - Emp_BestArrivalMem( p, i, f, m );
    if ( Emp_BestTwinUsed(p, pB) >= 0 )
        Slack = Abc_MinDouble( Slack, p->pReq[2 * pB->Twin + pB->TwinPhase] - Emp_BestArrivalMem(p, pB->Twin, pB->TwinPhase, m) );
    return Slack;
}
// saves and restores the sizes of the given node phases
static void Emp_ManSaveSizes( Emp_Man_t * p, Vec_Int_t * vNodes, int * pSizes )
{
    int k, e;
    Vec_IntForEachEntry( vNodes, e, k )
        pSizes[k] = p->pBest[e].iMem;
}
static void Emp_ManRestoreSizes( Emp_Man_t * p, Vec_Int_t * vNodes, int * pSizes )
{
    int k, e;
    Vec_IntForEachEntry( vNodes, e, k )
        Emp_BestSetMem( p, e >> 1, e & 1, pSizes[k] );
}
typedef struct Emp_Move_t_ Emp_Move_t;
struct Emp_Move_t_ { double Gain; int Entry; int Mem; };
static int Emp_MoveCompare( const void * a, const void * b )
{
    double ga = ((Emp_Move_t *)a)->Gain, gb = ((Emp_Move_t *)b)->Gain;
    return ga > gb ? -1 : ga < gb ? 1 : ((Emp_Move_t *)a)->Entry - ((Emp_Move_t *)b)->Entry;
}
// the size with the best slack of each near-critical cell; returns the number of cells to resize
static int Emp_ManCollectMoves( Emp_Man_t * p, Vec_Int_t * vNodes, double Delay, Emp_Move_t * pMoves )
{
    int k, e, m, nMoves = 0;
    Vec_IntForEachEntry( vNodes, e, k )
    {
        int i = e >> 1, f = e & 1, mCur = p->pBest[e].iMem, mBest = mCur;
        double Slack0 = Emp_BestSlackMem( p, i, f, mCur ), SlackBest = Slack0;
        if ( Slack0 > 0.01 * Delay )
            continue;
        for ( m = 0; m < Emp_BestFam(p, p->pBest + e)->nMem; m++ )
        {
            double Slack = m == mCur ? Slack0 : Emp_BestSlackMem( p, i, f, m );
            if ( Slack > SlackBest + EMP_EPS )
                SlackBest = Slack, mBest = m;
        }
        if ( mBest == mCur )
            continue;
        pMoves[nMoves].Gain  = SlackBest - Slack0;
        pMoves[nMoves].Entry = e;
        pMoves[nMoves].Mem   = mBest;
        nMoves++;
    }
    return nMoves;
}
/**Function*************************************************************

  Synopsis    [Sizing for delay.]

  Description [Similar to "upsize": each iteration resizes a fraction of
               the near-critical cells with the largest slack gains.  An
               iteration that does not reduce the delay is undone and the
               fraction is halved.  Returns the delay.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Emp_ManSizeDelay( Emp_Man_t * p )
{
    Vec_Int_t * vNodes = Vec_IntAlloc( 1000 );
    Emp_Move_t * pMoves;
    int * pSizes;
    double Delay, DelayBest, TargetSave = p->DelayTarget;
    int r, k, nMoves, nApply, nIters = 100, nDiv = 20, nFails = 0;
    Emp_ManUpdate( p, &Delay );
    Emp_ManSizedNodes( p, vNodes );
    pSizes = ABC_ALLOC( int, Vec_IntSize(vNodes) + 1 );
    pMoves = ABC_ALLOC( Emp_Move_t, Vec_IntSize(vNodes) + 1 );
    Emp_ManSaveSizes( p, vNodes, pSizes );
    DelayBest = Delay;
    for ( r = 0; r < nIters; r++ )
    {
        p->DelayTarget = Delay;
        Emp_ManSetRequired( p );
        nMoves = Emp_ManCollectMoves( p, vNodes, Delay, pMoves );
        if ( nMoves == 0 )
            break;
        qsort( pMoves, (size_t)nMoves, sizeof(Emp_Move_t), Emp_MoveCompare );
        nApply = Abc_MaxInt( 1, nMoves / nDiv );
        for ( k = 0; k < nApply; k++ )
            Emp_BestSetMem( p, pMoves[k].Entry >> 1, pMoves[k].Entry & 1, pMoves[k].Mem );
        Emp_ManUpdate( p, &Delay );
        if ( Delay < DelayBest - 0.0001 * DelayBest )
        {
            DelayBest = Delay;
            Emp_ManSaveSizes( p, vNodes, pSizes );
            nFails = 0;
            continue;
        }
        if ( ++nFails == 5 )
            break;
        // undo and resize fewer cells
        Emp_ManRestoreSizes( p, vNodes, pSizes );
        Emp_ManUpdate( p, &Delay );
        nDiv *= 2;
    }
    Emp_ManRestoreSizes( p, vNodes, pSizes );
    Emp_ManUpdate( p, &Delay );
    p->DelayTarget = TargetSave;
    Emp_ManSetRequired( p );
    Vec_IntFree( vNodes );
    ABC_FREE( pSizes );
    ABC_FREE( pMoves );
    return Delay;
}
/**Function*************************************************************

  Synopsis    [Sizing for area under the delay target.]

  Description [Each cell takes its smallest size meeting the required
               times.  The transitions are not updated while sizing, so if
               the target is missed, sizing is repeated with a growing
               margin; if it is still missed, the sizes are restored.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Emp_ManSizeArea( Emp_Man_t * p )
{
    Vec_Int_t * vNodes = Vec_IntAlloc( 1000 );
    double Delay, Target = p->DelayTarget, Margin = 0;
    int * pSizes, k, e, m;
    Emp_ManUpdate( p, &Delay );
    Emp_ManSizedNodes( p, vNodes );
    pSizes = ABC_ALLOC( int, Vec_IntSize(vNodes) + 1 );
    Emp_ManSaveSizes( p, vNodes, pSizes );
    while ( 1 )
    {
        p->DelayTarget = Target * (1 - Margin);
        Emp_ManSetRequired( p );
        // visited from the outputs: the slack left by the new size bounds the required times of the leaves
        Vec_IntForEachEntry( vNodes, e, k )
        {
            Emp_Best_t * pB = p->pBest + e;
            int i = e >> 1, f = e & 1, j, nMem = Emp_BestFam(p, pB)->nMem;
            double Slack;
            for ( m = 0; m < nMem; m++ )
                if ( m == pB->iMem || (Emp_BestSlackMem(p, i, f, m) >= -EMP_EPS && Emp_BestLeavesOkMem(p, i, f, m)) )
                    break;
            if ( m == nMem || m == pB->iMem )
                continue;
            Emp_BestSetMem( p, i, f, m );
            Slack = Emp_BestSlackMem( p, i, f, m );
            for ( j = 0; j < Emp_BestFaninNum(pB); j++ )
            {
                int l = Emp_BestFanin( p, i, f, j );
                p->pReq[l] = Abc_MinDouble( p->pReq[l], p->pBest[l].Arr + Slack );
            }
        }
        p->DelayTarget = Target;
        Emp_ManUpdate( p, &Delay );
        if ( p->pPars->fAreaMode || Delay <= Target + EMP_EPS )
            break;
        Emp_ManRestoreSizes( p, vNodes, pSizes );
        Emp_ManUpdate( p, &Delay );
        if ( Margin >= 0.08 )
            break;
        Margin = Margin ? 2 * Margin : 0.02;
    }
    Vec_IntFree( vNodes );
    ABC_FREE( pSizes );
    return Delay;
}

/**Function*************************************************************

  Synopsis    [One exact-area round.]

  Description [Runs both orders from the same cover and keeps the smaller
               result; with NLDM timing under a delay target, runs only the
               forward order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Emp_ManExactRound( Emp_Man_t * p, int fPairs )
{
    Emp_Best_t * pStart, * pForward;
    float AreaF, AreaR;
    if ( p->fNldmDelay )
    {
        Emp_ManExactArea( p, fPairs );
        return;
    }
    pStart   = ABC_ALLOC( Emp_Best_t, 2 * p->nObjs );
    pForward = ABC_ALLOC( Emp_Best_t, 2 * p->nObjs );
    Emp_CoverCopy( p, pStart, p->pBest );
    Emp_ManExactArea( p, fPairs );
    AreaF = Emp_ManSetRefs( p );
    Emp_CoverCopy( p, pForward, p->pBest );
    Emp_CoverCopy( p, p->pBest, pStart );
    Emp_ManSetRefs( p );
    Emp_ManSetRequired( p );
    Emp_ManExactAreaRev( p, fPairs );
    AreaR = Emp_ManSetRefs( p );
    if ( AreaF < AreaR - EMP_EPS )
        Emp_CoverCopy( p, p->pBest, pForward );
    ABC_FREE( pStart );
    ABC_FREE( pForward );
}
// timing repair: the nodes missing their required times take their fastest matches
static double Emp_ManRepair( Emp_Man_t * p )
{
    double Delay;
    int r, k, f;
    Emp_ManUpdate( p, &Delay );
    for ( r = 0; r < 3 && Delay > p->DelayTarget + EMP_EPS; r++ )
    {
        for ( k = 0; k < p->nOrder; k++ )
        {
            int i = p->pOrder[k], fLate = 0;
            Emp_ObjUpdateArr( p, i );
            if ( !Emp_ObjIsUsed(p, i) || Emp_ObjIsMog(p, i) )
                continue;
            for ( f = 0; f < 2; f++ )
                fLate |= p->pImpl[2 * i + f] && Emp_ObjArr(p, i, f) > p->pReq[2 * i + f] + EMP_EPS;
            if ( !fLate )
                continue;
            Emp_ObjDetach( p, i );
            Emp_ObjMatch( p, i, 0, 1 );
            Emp_ObjAttach( p, i );
            Emp_ObjUpdateArr( p, i );
        }
        Emp_ManUpdate( p, &Delay );
    }
    return Delay;
}

/**Function*************************************************************

  Synopsis    [Recovery rounds.]

  Description [After each round, the smallest cover meeting the delay
               target is remembered.  With fTighten (NLDM timing without
               an explicit target), a faster cover tightens the target.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
// remembers the smallest cover that meets the delay target
static void Emp_ManCheckpoint( Emp_Man_t * p, float Area, double Delay )
{
    if ( !p->pPars->fAreaMode && Delay > p->DelayTarget + EMP_EPS )
    {
        // until a cover meets the target, the fastest one is kept
        if ( p->AreaGood == EMP_FINF && Delay < p->DelayGood - EMP_EPS )
        {
            p->DelayGood = Delay;
            Emp_CoverCopy( p, p->pGood, p->pBest );
        }
        return;
    }
    if ( Area > p->AreaGood - EMP_EPS )
        return;
    p->AreaGood = Area;
    Emp_CoverCopy( p, p->pGood, p->pBest );
}
// without an explicit target (or if the cover misses it), a recovered cover is sized for delay and,
// with a fixed target that is met, then for area: unsized, it has the smallest cells and looks slower than it is
static void Emp_ManSizeRound( Emp_Man_t * p, int fTighten, float * pArea, double * pDelay )
{
    if ( !fTighten && !(p->fNldmDelay && *pDelay > p->DelayTarget + EMP_EPS) )
        return;
    *pDelay = Emp_ManSizeDelay( p );
    if ( !fTighten && *pDelay <= p->DelayTarget + EMP_EPS )
        *pDelay = Emp_ManSizeArea( p );
    *pArea = Emp_ManSetRefs( p );
}
// a faster cover tightens the target, keeping 1% for transition changes that exact area cannot track;
// returns 1 if the target is tightened
static int Emp_ManTighten( Emp_Man_t * p, double * pDelay )
{
    if ( !(*pDelay * 1.01 < p->DelayTarget - EMP_EPS) )
        return 0;
    p->DelayTarget = *pDelay * 1.01;
    p->AreaGood    = EMP_FINF;
    p->DelayGood   = EMP_INF;
    *pDelay = Emp_ManSetRequired( p );
    return 1;
}
/**Function*************************************************************

  Synopsis    [Exact-area rounds.]

  Description [Stops when a round gains less than 0.1%.  With incremental
               timing, every decision keeps the target.  Without it (after
               the budget is used up), the loads change while the nodes are
               decided, so a margin of the target is kept, doubled while
               the round misses the target, and the timing is repaired.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Emp_ManExactRounds( Emp_Man_t * p, int fPairs, float Area, char * pTitle, int fTighten )
{
    // the starting cover of a round, in case the budget is used up
    Emp_Best_t * pStart = p->fNldmDelay && p->pPars->nPropBudget > 0 ? ABC_ALLOC( Emp_Best_t, 2 * p->nObjs ) : NULL;
    // with NLDM timing, recovery may start from the delay-oriented cover: allow more rounds
    int r, nRounds = p->fNldmDelay ? 3 * p->pPars->nAreaRounds : p->pPars->nAreaRounds;
    float AreaPrev = Area;
    double Delay;
    for ( r = 0; r < nRounds; r++ )
    {
        int fIncrRound = p->fNldmDelay && !p->fIncrOff, fGuard = pStart && !fIncrRound;
        double Guard = 0.01, Target = p->DelayTarget, DelayCur = 0;
        if ( fGuard )
            Emp_CoverCopy( p, pStart, p->pBest );
        // if the cover misses the target, its own delay is the target of this round
        // (the required times of the target are infeasible)
        if ( p->fNldmDelay && !fTighten )
        {
            Emp_ManUpdate( p, &DelayCur );
            if ( DelayCur > Target + EMP_EPS )
                p->DelayTarget = DelayCur;
        }
        while ( 1 )
        {
            p->Guard = fGuard ? Guard : 0;
            p->SensK = fGuard ? 2 : 1;
            Emp_ManSetRequired( p );
            if ( fIncrRound )
            {
                p->RetimeLimit = p->pPars->nPropBudget > 0 ? p->nRetimed + (double)p->pPars->nPropBudget * Abc_NtkNodeNum(p->pNtk) : 0;
                Emp_ManStartIncr( p );
            }
            Emp_ManExactRound( p, fPairs );
            p->fIncr = 0;
            p->RetimeLimit = 0;
            p->Guard = 0;
            p->SensK = 1;
            Area = Emp_ManUpdate( p, &Delay );
            if ( (fGuard || p->fIncrOff) && Delay > p->DelayTarget + EMP_EPS )
            {
                Delay = Emp_ManRepair( p );
                Area = Emp_ManSetRefs( p );
            }
            if ( !fGuard || Delay <= p->DelayTarget + EMP_EPS || Guard >= 0.08 )
                break;
            Emp_CoverCopy( p, p->pBest, pStart );
            Emp_ManUpdate( p, &Delay );
            Guard *= 2;
        }
        p->DelayTarget = Target;
        Emp_ManSizeRound( p, fTighten, &Area, &Delay );
        Emp_ManPrintRound( p, pTitle, Area, Delay );
        if ( fTighten )
            Emp_ManTighten( p, &Delay );
        Emp_ManCheckpoint( p, Area, Delay );
        if ( AreaPrev - Area < 0.001 * AreaPrev )
            break;
        AreaPrev = Area;
    }
    ABC_FREE( pStart );
    return Area;
}

/**Function*************************************************************

  Synopsis    [Area-flow rounds.]

  Description [With NLDM timing, a round that misses the target is
               repeated with a growing margin; if it still misses the
               target, the round is dropped.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Emp_ManAreaFlowRounds( Emp_Man_t * p, int fMogs, char * pTitle, int fTighten )
{
    // the starting cover and fanout estimates of a round, in case the round is dropped
    Emp_Best_t * pStart = p->fNldmDelay ? ABC_ALLOC( Emp_Best_t, 2 * p->nObjs ) : NULL;
    float Area = 0, AreaPrev = EMP_FINF, * pEstSave = pStart ? ABC_ALLOC( float, 2 * p->nObjs ) : NULL;
    double Delay, DelayStart = 0;
    int r, nRounds = pStart ? 3 * p->pPars->nFlowRounds : p->pPars->nFlowRounds;
    for ( r = 0; r < nRounds; r++ )
    {
        double Guard = 0;
        // with NLDM timing, extra rounds continue while they gain 1%
        if ( r >= p->pPars->nFlowRounds && AreaPrev - Area < 0.01 * AreaPrev )
            break;
        AreaPrev = r ? Area : EMP_FINF;
        if ( pStart )
        {
            Emp_CoverCopy( p, pStart, p->pBest );
            memcpy( pEstSave, p->pEst, sizeof(float) * 2 * p->nObjs );
            Emp_ManUpdate( p, &DelayStart );
        }
        while ( 1 )
        {
            // if the starting cover misses the target, its required times are infeasible and the
            // critical cone falls back to the fastest matches: recover against the cover's own delay
            double Target = p->DelayTarget;
            if ( pStart && DelayStart > Target + EMP_EPS )
                p->DelayTarget = DelayStart;
            p->Guard = Guard;
            Emp_ManSetRequired( p );
            Emp_ManAreaFlow( p, fMogs );
            p->Guard = 0;
            p->DelayTarget = Target;
            Area = Emp_ManUpdate( p, &Delay );
            if ( !pStart || Delay <= p->DelayTarget + EMP_EPS || Guard >= 0.08 || DelayStart > p->DelayTarget + EMP_EPS )
                break;
            Emp_CoverCopy( p, p->pBest, pStart );
            Emp_ManUpdate( p, &Delay );
            Guard = Guard ? 2 * Guard : 0.01;
        }
        Emp_ManUpdateEst( p );
        Emp_ManSizeRound( p, fTighten, &Area, &Delay );
        Emp_ManPrintRound( p, pTitle, Area, Delay );
        // area flow may find a faster cover (smaller cells load the previous stage less)
        if ( !(fTighten && Emp_ManTighten(p, &Delay)) && pStart && Delay > p->DelayTarget + EMP_EPS &&
             (DelayStart <= p->DelayTarget + EMP_EPS || Delay > 1.01 * DelayStart) )
        {
            // the round misses the target: drop it
            Emp_CoverCopy( p, p->pBest, pStart );
            memcpy( p->pEst, pEstSave, sizeof(float) * 2 * p->nObjs );
            Area = Emp_ManUpdate( p, &Delay );
        }
        Emp_ManCheckpoint( p, Area, Delay );
    }
    ABC_FREE( pStart );
    ABC_FREE( pEstSave );
    return Area;
}

/**Function*************************************************************

  Synopsis    [Top-level flow.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// NLDM timing from the Liberty library loaded by read_lib
static void Emp_ManStartNldm( Emp_Man_t * p )
{
    Mio_Gate_t * pGateInv = Mio_LibraryReadInv( p->pMio );
    Vec_Flt_t * vCaps;
    SC_Cell * pCell;
    int i;
    p->pScl = p->pPars->fNldm ? (SC_Lib *)Abc_FrameReadLibScl() : NULL;
    if ( p->pScl == NULL || pGateInv == NULL || Abc_SclCellFind(p->pScl, Mio_GateReadName(pGateInv)) < 0 )
        return;
    p->fNldm = 1;
    p->fNldmDelay = !p->pPars->fAreaMode;
    p->Slew = Abc_SclComputeAverageSlew( p->pScl );
    // typical pin load: the median of the average input capacitances of the cells
    vCaps = Vec_FltAlloc( 1000 );
    SC_LibForEachCell( p->pScl, pCell, i )
        if ( pCell->n_inputs > 0 && !pCell->seq && !pCell->fSkip )
            Vec_FltPush( vCaps, SC_CellPinCapAve(pCell) );
    Vec_FltSort( vCaps, 0 );
    p->LoadAvg = Vec_FltSize(vCaps) ? Vec_FltEntry( vCaps, Vec_FltSize(vCaps) / 2 ) : 1;
    Vec_FltFree( vCaps );
    p->PoLoad = Abc_FrameReadMaxLoad();
}
// delay-oriented mapping; with NLDM timing, the structure is chosen with the
// load-independent delays and then sized for delay; sets the delay target
static void Emp_ManMapDelay( Emp_Man_t * p )
{
    Emap_Par_t * pPars = p->pPars;
    Abc_Obj_t * pObj;
    float Area;
    double Delay = 0;
    int i;
    Emp_ManInitObjs( p );
    p->fGainMode = p->fNldm;
    Abc_AigForEachAnd( p->pNtk, pObj, i )
    {
        Emp_ObjComputeCuts( p, pObj );
        Emp_ObjMatch( p, i, 0, 0 );
    }
    p->fGainMode = 0;
    Area = Emp_ManUpdate( p, &Delay );
    Emp_ManPrintRound( p, "Delay", Area, Delay );
    if ( p->fNldm )
    {
        Delay = Emp_ManSizeDelay( p );
        Area = Emp_ManSetRefs( p );
        Emp_ManPrintRound( p, "SizeDelay", Area, Delay );
    }
    Emp_CoverCopy( p, p->pGood, p->pBest );
    if ( pPars->fAreaMode )
        p->DelayTarget = EMP_INF;
    else
    {
        // with NLDM timing, an explicit target is kept even if the delay-oriented cover misses it,
        // because area recovery may find a faster cover
        if ( p->fNldm && pPars->DelayTarget > 0 )
            p->DelayTarget = pPars->DelayTarget;
        else
            p->DelayTarget = Abc_MaxDouble( Delay, pPars->DelayTarget );
        if ( !p->fNldm && pPars->DelayTarget > 0 && pPars->DelayTarget < Delay - EMP_EPS )
            printf( "Warning: the delay target %.2f is below the best delay %.2f; using the best delay.\n", pPars->DelayTarget, Delay );
        Emp_ManSetRequired( p );
    }
    Emp_ManCheckpoint( p, Area, Delay );
    Emp_ManUpdateEst( p );
}

/**Function*************************************************************

  Synopsis    [Performs mapping.]

  Description [Delay-oriented mapping, then area-flow and exact-area
               recovery; returns the smallest cover meeting the delay
               target (or the fastest one if none does).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Emap_ManMapNew( Abc_Ntk_t * pNtk, Mio_Library_t * pMio, Emap_Par_t * pPars )
{
    Emp_Man_t * p;
    Abc_Ntk_t * pNtkNew;
    float Area;
    double Delay = 0;
    int fMogs, fMogFlow, fMogLast, fTighten;
    assert( Abc_NtkIsStrash(pNtk) );
    p = Emp_ManStart( pNtk, pMio, pPars );
    Emp_ManStartNldm( p );
    if ( !Emp_LibPrepare( p ) )
    {
        Emp_ManStop( p );
        return NULL;
    }
    // two-output cells: in area mode, from the start; otherwise, after single-output recovery
    fMogs    = pPars->fUseMogs && p->nMogs > 0;
    fMogFlow = fMogs && pPars->fAreaMode;
    fMogLast = fMogs && !pPars->fAreaMode;
    // without an explicit target, NLDM timing tightens the target
    fTighten = p->fNldmDelay && pPars->DelayTarget == 0;
    if ( pPars->fVerbose )
    {
        printf( "Library: cells %d (single-output variants %d -> %d), two-output variants %d -> %d.  Cuts: %d per node.\n",
            Mio_LibraryReadGateNum(pMio), p->nCellsAll, p->nCells, p->nMogsAll, p->nMogs, pPars->nCutNum );
        if ( p->fNldm )
            printf( "Timing: NLDM from \"%s\" at slew %.2f, average pin load %.2f, output load %.2f.\n", p->pScl->pName, p->Slew, p->LoadAvg, p->PoLoad );
        else
            printf( "Timing: GENLIB pin delays (load-independent).\n" );
    }
    Emp_ManMapDelay( p );
    // pairs, the processing order, area flow, and exact area
    if ( fMogFlow )
        Emp_ManSelectPairs( p );
    Emp_ManComputeOrder( p );
    Area = Emp_ManAreaFlowRounds( p, fMogFlow, "AreaFlow", fTighten );
    Area = Emp_ManExactRounds( p, fMogFlow, Area, "ExactArea", fTighten );
    if ( fMogLast )
    {
        Emp_ManSelectPairs( p );
        Emp_ManComputeOrder( p );
        Area = Emp_ManExactRounds( p, 1, Area, "ExactMog", 0 );
        // area flow with two-output cells from the best cover (skipped with NLDM timing without a target)
        if ( !fTighten )
        {
            Emp_CoverCopy( p, p->pBest, p->pGood );
            Emp_ManUpdate( p, &Delay );
            Area = Emp_ManAreaFlowRounds( p, 1, "AreaFlowMog", 0 );
            Area = Emp_ManExactRounds( p, 1, Area, "ExactMog", 0 );
        }
    }
    // the smallest cover meeting the delay target
    Emp_CoverCopy( p, p->pBest, p->pGood );
    Area = Emp_ManUpdate( p, &Delay );
    // with NLDM timing, the cells off the critical paths are downsized
    if ( p->fNldmDelay && Delay <= p->DelayTarget + EMP_EPS )
    {
        // without an explicit target, the current delay is kept
        if ( pPars->DelayTarget == 0 )
        {
            p->DelayTarget = Delay;
            Emp_ManSetRequired( p );
        }
        Delay = Emp_ManSizeArea( p );
        Area = Emp_ManSetRefs( p );
    }
    if ( pPars->fVerbose )
    {
        if ( fMogs )
            printf( "Pairs: candidates %d, selected %d (placed together %d), cuts %d.  Cut memory %.2f MB.\n",
                p->nCands, p->nPairs, p->nPairsCo, p->nTups, 1.0 * p->nCuts * sizeof(Emp_Cut_t) / (1 << 20) );
        Emp_ManPrintRound( p, "Final", Area, Delay );
        if ( p->fIncrOff )
            printf( "The incremental timing budget (-B) was used up.\n" );
    }
    if ( !pPars->fAreaMode && Delay > p->DelayTarget + EMP_EPS )
        printf( "Warning: emap delay %.2f exceeds the target %.2f.\n", Delay, p->DelayTarget );
    pNtkNew = Emp_ManBuild( p );
    if ( pNtkNew == NULL )
        printf( "Error: emap has produced an invalid cover.\n" );
    Emp_ManStop( p );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
