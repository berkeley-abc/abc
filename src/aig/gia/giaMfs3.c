/**CFile****************************************************************

  FileName    [giaMfs3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [LUT resubstitution by circuit SAT sweeping with local care.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 3, 2026.]

  Revision    [$Id: giaMfs3.c,v 1.00 2026/11/03 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "opt/sfm/sfmInt.h"
#include "opt/dau/dau.h"
#include "sat/glucose3/AbcGlucose3.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MFS3_WIN_MAX  64
#define MFS3_SIDE_MAX 8
#define MFS3_SIDE_LIMIT (15*MFS3_WIN_MAX)
#define MFS3_SIM_WORDS 4
#define MFS3_RECYCLE_VARS 200000
#define MFS3_RECYCLE_CALLS 500
#define MFS3_CACHE_MAX (4*1024*1024)

typedef struct Mfs3_Cache_t_ Mfs3_Cache_t;
struct Mfs3_Cache_t_
{
    word Key[24];                 // Exact function/care context, not a hash.
    int nKey, Removed;
    Vec_Int_t * vDivs;            // Ordered divisor functions tested in this context.
    int AllDivs;
};

typedef struct Mfs3_Man_t_ Mfs3_Man_t;
struct Mfs3_Man_t_
{
    Sfm_Ntk_t * pNtk;
    Sfm_Par_t * pPars;
    Gia_Man_t * pPool;             // Immutable circuit functions, including retired versions.
    bmcg3_sat_solver * pSat;
    int * pFuncs;                 // Current LUT functions as pool literals.
    int * pSlots;                 // Positive window slots and negative side slots.
    int * pMarks;
    int nTrav;
    Vec_Int_t * vStack;
    Vec_Int_t * vFuncStack;
    Vec_Int_t * vLeaves;
    Vec_Int_t * vCover;
    Vec_Int_t * vDivs;
    Vec_Int_t * vSatLits;
    Vec_Int_t * vSatToCi;
    Vec_Int_t * vSimStamp;
    Vec_Wrd_t * vSims;
    Vec_Int_t * vJustValues;
    Vec_Int_t * vJustVisit;
    int nJustLeft, nJustRetries, nJustified, iCex;
    int nSimStamp;
    int nCexes;
    int nCallsSince;
    int nSideMax;
    int Win[MFS3_WIN_MAX], Side[MFS3_SIDE_LIMIT];
    int Bound[MFS3_WIN_MAX];
    int nWin, nSide;
    word Care[4];
    int Cover[256], nCubes;
    int fCareCircuit, CareLit;
    int CareRoot;
    int nBase, nRootSamples;
    word RootSim[4], RootFanSim[8][4], RootSideSim[8][4], RootCareSim[4];
    int RootRows[256], RootValues[256], RootStamp, RootId, BasePosition;
    int Pair0[16], Pair1[16], nPairs, PairStamp;
    int nTried, nChanged, nRemoved, nResub, nReject, nLarge;
    int nSat, nUnsat, nUndec, nRecycles;
    int nSideOver, nNodeOver, nShallower, nWindows, nCareCircuits;
    int Depths[33];
    Mfs3_Cache_t ** pCaches, * pCache;
    int nCacheHits, nCacheEntries, fTryUndec;
    Vec_Int_t * vDivLits;
    abctime timeCare, timeDiv, timeSim, timeCnf, timeSat, timeUpdate, timeJust;
};

extern Sfm_Ntk_t * Gia_ManExtractMfs( Gia_Man_t * p );
extern Gia_Man_t * Gia_ManInsertMfs( Gia_Man_t * p, Sfm_Ntk_t * pNtk, int fAllBoxes );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Extends per-function storage after appending circuit gates.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_Grow( Mfs3_Man_t * p )
{
    int nObjs = Gia_ManObjNum(p->pPool);
    // Solver recycling can resize vSatLits independently of these arrays.
    if ( Vec_IntSize(p->vJustValues) == nObjs ) return;
    Vec_IntFillExtra(p->vSatLits, nObjs, -1);
    Vec_IntFillExtra(p->vSimStamp, nObjs, 0);
    Vec_WrdFillExtra(p->vSims, MFS3_SIM_WORDS*nObjs, 0);
    Vec_IntFillExtra(p->vJustValues,nObjs,0);
}

/**Function*************************************************************

  Synopsis    [Builds current LUT functions without redefining old SAT gates.]

  Description [The explicit stack permits divisors with larger object IDs.]
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Function( Mfs3_Man_t * p, int Root )
{
    int Id, Fan = -1, k;
    if ( p->pFuncs[Root] >= 0 ) return p->pFuncs[Root];
    Vec_IntClear(p->vFuncStack);
    Vec_IntPush(p->vFuncStack, Root);
    while ( Vec_IntSize(p->vFuncStack) )
    {
        Id = Vec_IntEntryLast(p->vFuncStack);
        if ( p->pFuncs[Id] >= 0 ) { Vec_IntPop(p->vFuncStack); continue; }
        Sfm_ObjForEachFanin(p->pNtk, Id, Fan, k)
            if ( p->pFuncs[Fan] < 0 ) break;
        if ( k < Sfm_ObjFaninNum(p->pNtk, Id) )
        {
            Vec_IntPush(p->vFuncStack, Fan);
            continue;
        }
        Vec_IntClear(p->vLeaves);
        Sfm_ObjForEachFanin(p->pNtk, Id, Fan, k)
            Vec_IntPush(p->vLeaves, p->pFuncs[Fan]);
        p->pFuncs[Id] = Dsm_ManTruthToGia(p->pPool, Sfm_NodeReadTruth(p->pNtk,Id), p->vLeaves, p->vCover);
        Vec_IntPop(p->vFuncStack);
    }
    Mfs3_Grow(p);
    return p->pFuncs[Root];
}

/**Function*************************************************************

  Synopsis    [Simulates only functions whose cached patterns are stale.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static word * Mfs3_SimulateSlow( Mfs3_Man_t * p, int Root )
{
    Gia_Obj_t * pObj;
    int Id, Id0, Id1, c0, c1, w;
    if ( Root < Vec_IntSize(p->vSimStamp) && Vec_IntEntry(p->vSimStamp,Root) == p->nSimStamp )
        return Vec_WrdEntryP(p->vSims,MFS3_SIM_WORDS*Root);
    Mfs3_Grow(p);
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack, Root);
    while ( Vec_IntSize(p->vStack) )
    {
        word * pOut, * pIn0, * pIn1;
        Id = Vec_IntEntryLast(p->vStack);
        if ( Vec_IntEntry(p->vSimStamp,Id) == p->nSimStamp ) { Vec_IntPop(p->vStack); continue; }
        pObj = Gia_ManObj(p->pPool,Id);
        if ( Id && !Gia_ObjIsCi(pObj) )
        {
            Id0 = Gia_ObjFaninId0(pObj,Id);
            Id1 = Gia_ObjFaninId1(pObj,Id);
            if ( Vec_IntEntry(p->vSimStamp,Id0) != p->nSimStamp ) { Vec_IntPush(p->vStack,Id0); continue; }
            if ( Vec_IntEntry(p->vSimStamp,Id1) != p->nSimStamp ) { Vec_IntPush(p->vStack,Id1); continue; }
            c0 = Gia_ObjFaninC0(pObj);
            c1 = Gia_ObjFaninC1(pObj);
            pOut = Vec_WrdEntryP(p->vSims, MFS3_SIM_WORDS*Id);
            pIn0 = Vec_WrdEntryP(p->vSims, MFS3_SIM_WORDS*Id0);
            pIn1 = Vec_WrdEntryP(p->vSims, MFS3_SIM_WORDS*Id1);
            // Words 0..2 never change; only new functions need them evaluated.
            for ( w = Vec_IntEntry(p->vSimStamp,Id) ? 3 : 0; w < MFS3_SIM_WORDS; w++ )
                pOut[w] = (c0 ? ~pIn0[w] : pIn0[w]) & (c1 ? ~pIn1[w] : pIn1[w]);
        }
        Vec_IntWriteEntry(p->vSimStamp,Id,p->nSimStamp);
        Vec_IntPop(p->vStack);
    }
    return Vec_WrdEntryP(p->vSims,MFS3_SIM_WORDS*Root);
}

/**Function*************************************************************

  Synopsis    [Simulates short cones directly, with a bounded call stack.]

  Description [All pool objects and storage are stable during simulation.
  Deep cones use the explicit stack, so circuit depth cannot exhaust the C stack.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static word * Mfs3_Simulate_rec( Mfs3_Man_t * p, int Id, int Depth )
{
    word * pOut = Vec_WrdArray(p->vSims) + MFS3_SIM_WORDS*Id;
    word * pIn0, * pIn1, Mask0, Mask1;
    Gia_Obj_t * pObj;
    int w, Stamp = Vec_IntArray(p->vSimStamp)[Id];
    if ( Stamp == p->nSimStamp ) return pOut;
    if ( !Depth ) return Mfs3_SimulateSlow(p,Id);
    pObj = Gia_ManObj(p->pPool,Id);
    if ( Id && !Gia_ObjIsCi(pObj) )
    {
        pIn0 = Mfs3_Simulate_rec(p,Gia_ObjFaninId0(pObj,Id),Depth-1);
        pIn1 = Mfs3_Simulate_rec(p,Gia_ObjFaninId1(pObj,Id),Depth-1);
        Mask0 = Gia_ObjFaninC0(pObj) ? ~(word)0 : 0;
        Mask1 = Gia_ObjFaninC1(pObj) ? ~(word)0 : 0;
        for ( w = Stamp ? 3 : 0; w < MFS3_SIM_WORDS; w++ )
            pOut[w] = (pIn0[w] ^ Mask0) & (pIn1[w] ^ Mask1);
    }
    Vec_IntArray(p->vSimStamp)[Id] = p->nSimStamp;
    return pOut;
}

/**Function*************************************************************

  Synopsis    [Extends simulation storage before entering a short cone.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static word * Mfs3_Simulate( Mfs3_Man_t * p, int Root )
{
    Mfs3_Grow(p);
    return Mfs3_Simulate_rec(p,Root,128);
}

/**Function*************************************************************

  Synopsis    [Copies complemented simulation words for one LUT signal.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_SignalSim( Mfs3_Man_t * p, int Id, word * pOut )
{
    int Lit = Mfs3_Function(p,Id), w;
    word * pIn = Mfs3_Simulate(p,Abc_Lit2Var(Lit));
    for ( w = 0; w < MFS3_SIM_WORDS; w++ ) pOut[w] = Abc_LitIsCompl(Lit) ? ~pIn[w] : pIn[w];
}

/**Function*************************************************************

  Synopsis    [Clears the preceding local observability window.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_WindowClear( Mfs3_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nWin; i++ ) p->pSlots[p->Win[i]] = 0;
    for ( i = 0; i < p->nSide; i++ ) p->pSlots[p->Side[i]] = 0;
    p->nWin = p->nSide = 0;
}

/**Function*************************************************************

  Synopsis    [Collects all fanout paths up to an absolute LUT level.]

  Description [Every exit is observed. Capacity overflow rejects the whole
  window, rather than omitting a path. Absolute levels prevent a side input
  from depending on the pivot through a path outside the window.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Window( Mfs3_Man_t * p, int Root, int Depth )
{
    Sfm_Ntk_t * n = p->pNtk;
    int i, k, Id, Fan, MaxLevel = Sfm_ObjLevel(n,Root) + Depth;
    Mfs3_WindowClear(p);
    p->Win[p->nWin++] = Root;
    p->pSlots[Root] = 1;
    for ( i = 0; i < p->nWin; i++ )
        Sfm_ObjForEachFanout(n,p->Win[i],Fan,k)
        {
            if ( !Depth || Sfm_ObjIsPo(n,Fan) || Sfm_ObjLevel(n,Fan) > MaxLevel || p->pSlots[Fan] ) continue;
            if ( p->nWin == MFS3_WIN_MAX ) { p->nNodeOver++; return 0; }
            p->Win[p->nWin++] = Fan;
            p->pSlots[Fan] = 1;
        }
    for ( i = 1; i < p->nWin; i++ )
    {
        Id = p->Win[i];
        for ( k = i; k && (Sfm_ObjLevel(n,p->Win[k-1]) > Sfm_ObjLevel(n,Id) ||
            (Sfm_ObjLevel(n,p->Win[k-1]) == Sfm_ObjLevel(n,Id) && p->Win[k-1] > Id)); k-- )
            p->Win[k] = p->Win[k-1];
        p->Win[k] = Id;
    }
    // Dedicated mapping muxes add no LUT level. Resolve same-level
    // dependencies explicitly, including divisors with larger object IDs.
    for ( i = 0; i < p->nWin; i++ )
    {
        int j;
        for ( j = i; j < p->nWin; j++ )
        {
            Sfm_ObjForEachFanin(n,p->Win[j],Fan,k)
                if ( p->pSlots[Fan] > 0 ) break;
            if ( k == Sfm_ObjFaninNum(n,p->Win[j]) ) break;
        }
        assert(j < p->nWin);
        Id = p->Win[j];
        for ( ; j > i; j-- ) p->Win[j] = p->Win[j-1];
        p->Win[i] = Id;
        p->pSlots[Id] = -1;
    }
    assert(p->Win[0] == Root);
    for ( i = 0; i < p->nWin; i++ ) p->pSlots[p->Win[i]] = i+1;
    memset(p->Bound,0,sizeof(p->Bound));
    for ( i = 0; i < p->nWin; i++ )
    {
        Sfm_ObjForEachFanout(n,p->Win[i],Fan,k)
            if ( Sfm_ObjIsPo(n,Fan) || p->pSlots[Fan] <= 0 ) p->Bound[i] = 1;
        if ( !i ) continue;
        Sfm_ObjForEachFanin(n,p->Win[i],Fan,k)
        {
            if ( p->pSlots[Fan] || (!Sfm_ObjIsPi(n,Fan) && !Sfm_ObjFaninNum(n,Fan)) ) continue;
            if ( p->nSide == (p->pPars->fMoreEffort ? MFS3_SIDE_LIMIT : p->nSideMax) ) { p->nSideOver++; return 0; }
            p->Side[p->nSide++] = Fan;
            p->pSlots[Fan] = -p->nSide;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Evaluates a LUT on a word of assignments by Shannon expansion.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static word Mfs3_EvalWord_rec( word Truth, int nVars, word * pInputs )
{
    word a, b, Mask;
    int Shift;
    if ( !Truth ) return 0;
    if ( Truth == ~(word)0 ) return ~(word)0;
    if ( !nVars ) return (Truth & 1) ? ~(word)0 : 0;
    Mask = s_Truths6[nVars-1];
    if ( Truth == Mask ) return pInputs[nVars-1];
    if ( Truth == ~Mask ) return ~pInputs[nVars-1];
    Shift = 1 << (nVars-1);
    a = Truth & ~Mask; a |= a << Shift;
    b = Truth & Mask; b |= b >> Shift;
    if ( a == b ) return Mfs3_EvalWord_rec(a,nVars-1,pInputs);
    a = Mfs3_EvalWord_rec(a,nVars-1,pInputs);
    b = Mfs3_EvalWord_rec(b,nVars-1,pInputs);
    return a ^ ((a ^ b) & pInputs[nVars-1]);
}

/**Function*************************************************************

  Synopsis    [Evaluates a larger LUT a truth-table word at a time.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static word Mfs3_Eval_rec( word * pTruth, int nVars, int Offset, word * pInputs )
{
    word a, b;
    if ( nVars <= 6 ) return Mfs3_EvalWord_rec(pTruth[Offset >> 6],nVars,pInputs);
    a = Mfs3_Eval_rec(pTruth,nVars-1,Offset,pInputs);
    b = Mfs3_Eval_rec(pTruth,nVars-1,Offset+(1 << (nVars-1)),pInputs);
    return a ^ ((a ^ b) & pInputs[nVars-1]);
}

/**Function*************************************************************

  Synopsis    [Builds a care circuit when the side truth table is too large.]

  Description [Only the bounded fanout logic is duplicated. Side functions
  share the immutable pool, including all primary-input correlations.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_CareCircuit( Mfs3_Man_t * p )
{
    Sfm_Ntk_t * n = p->pNtk;
    int Values[2][MFS3_WIN_MAX], Fans[16], i, c, k, Fan, Slot;
    Values[0][0] = 0;
    Values[1][0] = 1;
    p->CareLit = 0;
    for ( i = 0; i < p->nWin; i++ )
    {
        if ( i )
            for ( c = 0; c < 2; c++ )
            {
                Sfm_ObjForEachFanin(n,p->Win[i],Fan,k)
                {
                    Slot = p->pSlots[Fan];
                    Fans[k] = Slot > 0 ? Values[c][Slot-1] : Mfs3_Function(p,Fan);
                }
                Vec_IntClear(p->vLeaves);
                for ( k = 0; k < Sfm_ObjFaninNum(n,p->Win[i]); k++ ) Vec_IntPush(p->vLeaves,Fans[k]);
                Values[c][i] = Dsm_ManTruthToGia(p->pPool,Sfm_NodeReadTruth(n,p->Win[i]),p->vLeaves,p->vCover);
            }
        if ( p->Bound[i] )
            p->CareLit = Gia_ManHashOr(p->pPool,p->CareLit,Gia_ManHashXor(p->pPool,Values[0][i],Values[1][i]));
    }
    p->nCubes = p->CareLit != 0;
    Mfs3_Grow(p);
}

/**Function*************************************************************

  Synopsis    [Computes and covers the Boolean difference at all exits.]

  Description [Care depends only on side signals. The SAT solver retains
  their complete fanin functions, and therefore their correlations.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_ComputeCare( Mfs3_Man_t * p, int Root )
{
    Sfm_Ntk_t * n = p->pNtk;
    word Values[2][MFS3_WIN_MAX], Inputs[16], Temp[4];
    int Depth, Requested, i, k, c, w, Fan, Slot;
    abctime clk = Abc_Clock();
    Depth = p->pPars->nTfoLevMax;
    Sfm_ObjForEachFanout(n,Root,Fan,k)
        if ( Sfm_ObjIsPo(n,Fan) ) { Depth = 0; break; }
    Requested = Depth;
    for ( ; !Mfs3_Window(p,Root,Depth); Depth-- ) assert(Depth > 0);
    p->nWindows++;
    p->nShallower += Depth < Requested;
    p->Depths[Depth]++;
    p->fCareCircuit = p->nSide > p->nSideMax;
    if ( p->fCareCircuit )
    {
        p->nCareCircuits++;
        Mfs3_CareCircuit(p);
        p->timeCare += Abc_Clock()-clk;
        return;
    }
    for ( w = 0; w < Abc_Truth6WordNum(p->nSide); w++ )
    {
        p->Care[w] = 0;
        Values[0][0] = 0;
        Values[1][0] = ~(word)0;
        for ( i = 0; i < p->nWin; i++ )
        {
            if ( i )
                for ( c = 0; c < 2; c++ )
                {
                    Sfm_ObjForEachFanin(n,p->Win[i],Fan,k)
                    {
                        Slot = p->pSlots[Fan];
                        if ( Slot > 0 ) Inputs[k] = Values[c][Slot-1];
                        else if ( Slot < 0 ) Inputs[k] = -Slot <= 6 ? s_Truths6[-Slot-1] : ((w >> (-Slot-7)) & 1) ? ~(word)0 : 0;
                        else Inputs[k] = *Sfm_NodeReadTruth(n,Fan) & 1 ? ~(word)0 : 0;
                    }
                    Values[c][i] = Mfs3_Eval_rec(Sfm_NodeReadTruth(n,p->Win[i]),Sfm_ObjFaninNum(n,p->Win[i]),0,Inputs);
                }
            if ( p->Bound[i] ) p->Care[w] |= Values[0][i] ^ Values[1][i];
        }
    }
    for ( ; w < 4; w++ ) p->Care[w] = p->Care[w % Abc_Truth6WordNum(p->nSide)];
    p->nCubes = 0;
    Abc_Tt8IsopCover(p->Care,p->Care,p->nSide,Temp,p->Cover,&p->nCubes);
    assert(p->nCubes <= 256);
    p->timeCare += Abc_Clock()-clk;
}

/**Function*************************************************************

  Synopsis    [Starts or periodically recycles the persistent circuit solver.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_SolverStart( Mfs3_Man_t * p )
{
    int Lit = 1;
    if ( p->pSat ) { bmcg3_sat_solver_reset(p->pSat); p->nRecycles++; }
    else
    {
        p->pSat = bmcg3_sat_solver_start();
        bmcg3_sat_solver_set_jftr(p->pSat,2);
        bmcg3_sat_solver_eliminate(p->pSat,1);
    }
    // The only permanent constraint is constant zero. Other units follow
    // from circuit definitions; care and mismatch remain assumptions.
    bmcg3_sat_solver_set_unit_justification(p->pSat,0);
    bmcg3_sat_solver_addvar(p->pSat);
    bmcg3_sat_solver_addclause(p->pSat,&Lit,1);
    Vec_IntFill(p->vSatLits,Gia_ManObjNum(p->pPool),-1);
    Vec_IntWriteEntry(p->vSatLits,0,0);
    Vec_IntFill(p->vSatToCi,1,0);
    p->nCallsSince = 0;
}

/**Function*************************************************************

  Synopsis    [Lazily installs immutable AND functions in Glucose3.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_SatLit( Mfs3_Man_t * p, int Lit )
{
    Gia_Obj_t * pObj;
    int Root = Abc_Lit2Var(Lit), Id, Id0, Id1, a, b, Var;
    if ( Root < Vec_IntSize(p->vSatLits) && Vec_IntEntry(p->vSatLits,Root) >= 0 )
        return Vec_IntEntry(p->vSatLits,Root) ^ Abc_LitIsCompl(Lit);
    Mfs3_Grow(p);
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack,Root);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntEntryLast(p->vStack);
        if ( Vec_IntEntry(p->vSatLits,Id) >= 0 ) { Vec_IntPop(p->vStack); continue; }
        pObj = Gia_ManObj(p->pPool,Id);
        if ( Gia_ObjIsCi(pObj) )
        {
            Var = bmcg3_sat_solver_addvar(p->pSat);
            assert(Var == Vec_IntSize(p->vSatToCi));
            Vec_IntPush(p->vSatToCi,Id);
            Vec_IntWriteEntry(p->vSatLits,Id,Abc_Var2Lit(Var,0));
            Vec_IntPop(p->vStack);
            continue;
        }
        assert(Gia_ObjIsAnd(pObj));
        Id0 = Gia_ObjFaninId0(pObj,Id);
        Id1 = Gia_ObjFaninId1(pObj,Id);
        if ( Vec_IntEntry(p->vSatLits,Id0) < 0 ) { Vec_IntPush(p->vStack,Id0); continue; }
        if ( Vec_IntEntry(p->vSatLits,Id1) < 0 ) { Vec_IntPush(p->vStack,Id1); continue; }
        a = Vec_IntEntry(p->vSatLits,Id0) ^ Gia_ObjFaninC0(pObj);
        b = Vec_IntEntry(p->vSatLits,Id1) ^ Gia_ObjFaninC1(pObj);
        Var = bmcg3_sat_solver_addvar(p->pSat);
        assert(Var == Vec_IntSize(p->vSatToCi));
        Vec_IntPush(p->vSatToCi,0);
        Vec_IntWriteEntry(p->vSatLits,Id,Abc_Var2Lit(Var,0));
        if ( a > b ) ABC_SWAP(int,a,b);
        bmcg3_sat_solver_set_var_fanin_lit(p->pSat,Var,a,b);
        Vec_IntPop(p->vStack);
    }
    return Vec_IntEntry(p->vSatLits,Root) ^ Abc_LitIsCompl(Lit);
}

/**Function*************************************************************

  Synopsis    [Replays a justified leaf cube as a complete simulation pattern.]

  Description [Unassigned primary inputs retain arbitrary existing values.
  Internal circuit model values are never used as independent assignments.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_SaveCex( Mfs3_Man_t * p )
{
    int * pCex = bmcg3_sat_solver_read_cex(p->pSat);
    int Index = 192 + p->nCexes, i, Id, Lit;
    word Bit = (word)1 << (Index & 63);
    p->nCexes = (p->nCexes+1) & 63;
    for ( i = 1; i <= pCex[0]; i++ )
    {
        Lit = pCex[i];
        if ( !Abc_Lit2Var(Lit) ) continue;
        Id = Vec_IntEntry(p->vSatToCi,Abc_Lit2Var(Lit));
        assert(Id && Gia_ObjIsCi(Gia_ManObj(p->pPool,Id)));
        Vec_WrdEntryP(p->vSims,MFS3_SIM_WORDS*Id)[3] &= ~Bit;
        if ( !Abc_LitIsCompl(Lit) ) Vec_WrdEntryP(p->vSims,MFS3_SIM_WORDS*Id)[3] |= Bit;
    }
    if ( ++p->nSimStamp == ABC_INFINITY )
    {
        Vec_IntFill(p->vSimStamp,Gia_ManObjNum(p->pPool),0);
        p->nSimStamp = 1;
        p->RootStamp = p->PairStamp = 0;
    }
    return Index;
}

/**Function*************************************************************

  Synopsis    [Reads a partially assigned circuit literal.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Assigned( Mfs3_Man_t * p, int Lit )
{
    int Value;
    if ( Lit < 2 ) return Lit;
    Value = Vec_IntEntry(p->vJustValues,Abc_Lit2Var(Lit));
    return Value ? (Value-1) ^ Abc_LitIsCompl(Lit) : -1;
}

/**Function*************************************************************

  Synopsis    [Recognizes implications before choosing an AND's controlling input.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Implied( Mfs3_Man_t * p, int Lit )
{
    int Value = Mfs3_Assigned(p,Lit), Id = Abc_Lit2Var(Lit), a, b;
    Gia_Obj_t * pObj;
    if ( Value >= 0 ) return Value;
    pObj = Gia_ManObj(p->pPool,Id);
    if ( !Gia_ObjIsAnd(pObj) ) return -1;
    a = Mfs3_Assigned(p,Gia_ObjFaninLit0(pObj,Id));
    b = Mfs3_Assigned(p,Gia_ObjFaninLit1(pObj,Id));
    Value = a == 0 || b == 0 ? 0 : (a == 1 && b == 1 ? 1 : -1);
    return Value < 0 ? -1 : Value ^ Abc_LitIsCompl(Lit);
}

/**Function*************************************************************

  Synopsis    [Attempts bounded circuit justification before calling SAT.]

  Description [Success gives a consistent partial CI assignment. Failure is
  inconclusive. All assignments of a failed controlling-input trial are undone.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Justify_rec( Mfs3_Man_t * p, int Lit )
{
    Gia_Obj_t * pObj;
    int Id, Value, a, b, Va, Vb, Save;
again:
    Value = Mfs3_Assigned(p,Lit);
    if ( Value >= 0 ) return Value;
    if ( --p->nJustLeft < 0 ) return 0;
    Id = Abc_Lit2Var(Lit);
    Value = !Abc_LitIsCompl(Lit);
    Vec_IntWriteEntry(p->vJustValues,Id,Value+1);
    Vec_IntPush(p->vJustVisit,Id);
    pObj = Gia_ManObj(p->pPool,Id);
    if ( Gia_ObjIsCi(pObj) ) return 1;
    a = Gia_ObjFaninLit0(pObj,Id);
    b = Gia_ObjFaninLit1(pObj,Id);
    Va = Mfs3_Assigned(p,a);
    Vb = Mfs3_Assigned(p,b);
    if ( Value )
    {
        if ( Va == 0 || Vb == 0 || !Mfs3_Justify_rec(p,a) ) return 0;
        Lit = b;
        goto again;
    }
    if ( Va == 0 || Vb == 0 ) return 1;
    if ( Va == 1 ) { Lit = b ^ 1; goto again; }
    if ( Vb == 1 ) { Lit = a ^ 1; goto again; }
    Va = Mfs3_Implied(p,a);
    Vb = Mfs3_Implied(p,b);
    if ( Va == 0 || Vb == 1 ) { Lit = a ^ 1; goto again; }
    if ( Vb == 0 || Va == 1 ) { Lit = b ^ 1; goto again; }
    if ( p->nJustRetries )
    {
        Save = Vec_IntSize(p->vJustVisit);
        if ( Mfs3_Justify_rec(p,a ^ 1) ) return 1;
        if ( !p->nJustRetries || p->nJustLeft < 0 ) return 0;
        p->nJustRetries--;
        while ( Vec_IntSize(p->vJustVisit) > Save ) Vec_IntWriteEntry(p->vJustValues,Vec_IntPop(p->vJustVisit),0);
        Lit = b ^ 1;
    }
    else Lit = a ^ 1;
    goto again;
}

/**Function*************************************************************

  Synopsis    [Saves a justified witness as a complete simulation pattern.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Justify( Mfs3_Man_t * p, int * Lits, int nLits )
{
    int i, Id, Success = 1;
    abctime clk = Abc_Clock();
    Mfs3_Grow(p);
    p->nJustLeft = 512;
    p->nJustRetries = 4;
    for ( i = 0; i < nLits; i++ )
        if ( !Mfs3_Justify_rec(p,Lits[i]) ) { Success = 0; break; }
    if ( Success )
    {
        word Bit;
        p->iCex = 192 + p->nCexes;
        p->nCexes = (p->nCexes+1) & 63;
        Bit = (word)1 << (p->iCex & 63);
        Vec_IntForEachEntry(p->vJustVisit,Id,i)
            if ( Gia_ObjIsCi(Gia_ManObj(p->pPool,Id)) )
            {
                word * pWord = Vec_WrdEntryP(p->vSims,MFS3_SIM_WORDS*Id+3);
                *pWord &= ~Bit;
                if ( Vec_IntEntry(p->vJustValues,Id) == 2 ) *pWord |= Bit;
            }
        if ( ++p->nSimStamp == ABC_INFINITY )
        {
            Vec_IntFill(p->vSimStamp,Gia_ManObjNum(p->pPool),0);
            p->nSimStamp = 1;
            p->RootStamp = p->PairStamp = 0;
        }
        p->nJustified++;
    }
    while ( Vec_IntSize(p->vJustVisit) ) Vec_IntWriteEntry(p->vJustValues,Vec_IntPop(p->vJustVisit),0);
    p->timeJust += Abc_Clock()-clk;
    return Success;
}

/**Function*************************************************************

  Synopsis    [Checks both polarities of a proposed replacement under care.]

  Description [Only circuit definitions are permanent. Care cubes and the
  inequality are assumptions, so learned clauses remain valid at later LUTs.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Prove( Mfs3_Man_t * p, int RootLit, int NewLit, unsigned * pUsed )
{
    int i, c, k, Pass, nLits, Lits[MFS3_SIDE_MAX+2], Roots[MFS3_SIDE_MAX+2], Status, StartConf;
    int Limit = p->pPars->nBTLimit;
    abctime clk;
    if ( RootLit == NewLit || !p->nCubes ) return GLUCOSE3_UNSAT;
    if ( !p->pSat || (bmcg3_sat_solver_varnum(p->pSat) > MFS3_RECYCLE_VARS && p->nCallsSince >= MFS3_RECYCLE_CALLS) )
        Mfs3_SolverStart(p);
    // Like the redundancy sweeper, look for a cheap witness under every care
    // cube before spending SAT effort proving any one of the cubes impossible.
    for ( Pass = 0; Pass < 2; Pass++ )
        for ( i = 0; i < p->nCubes; i++ )
            for ( c = 0; c < 2; c++ )
            {
                if ( Limit && *pUsed >= (unsigned)Limit ) { p->nUndec++; return GLUCOSE3_UNDEC; }
                nLits = 0;
                Lits[nLits++] = RootLit ^ c;
                Lits[nLits++] = NewLit ^ !c;
                if ( p->fCareCircuit ) Lits[nLits++] = p->CareLit;
                else for ( k = 0; k < p->nSide; k++ )
                {
                    int Pol = (p->Cover[i] >> (2*k)) & 3;
                    if ( Pol ) Lits[nLits++] = Mfs3_Function(p,p->Side[k]) ^ (Pol == 1);
                }
                if ( !Pass )
                {
                    if ( Mfs3_Justify(p,Lits,nLits) ) return GLUCOSE3_SAT;
                    continue;
                }
                clk = Abc_Clock();
                for ( k = 0; k < nLits; k++ ) Lits[k] = Mfs3_SatLit(p,Lits[k]);
                for ( k = 0; k < nLits; k++ ) Roots[k] = Abc_Lit2Var(Lits[k]);
                bmcg3_sat_solver_select_cones(p->pSat,Roots,nLits);
                p->timeCnf += Abc_Clock()-clk;
                clk = Abc_Clock();
                StartConf = bmcg3_sat_solver_conflictnum(p->pSat);
                bmcg3_sat_solver_set_conflict_budget(p->pSat,Limit ? Limit-(int)*pUsed : 0);
                Status = bmcg3_sat_solver_solve(p->pSat,Lits,nLits);
                *pUsed += (unsigned)bmcg3_sat_solver_conflictnum(p->pSat) - (unsigned)StartConf;
                p->timeSat += Abc_Clock()-clk;
                p->nCallsSince++;
                if ( Status == GLUCOSE3_SAT ) { p->nSat++; p->iCex = Mfs3_SaveCex(p); return Status; }
                if ( Status == GLUCOSE3_UNDEC ) { p->nUndec++; return Status; }
                p->nUnsat++;
            }
    return GLUCOSE3_UNSAT;
}

/**Function*************************************************************

  Synopsis    [Records one observed row before stretching the learned tables.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_SetRow( word * pTruth, int Row )
{
    Abc_TtSetBit(pTruth,Row);
}

/**Function*************************************************************

  Synopsis    [Shares sampled care and retained-fanin tuples across divisors.]

  Description [Counterexamples invalidate the cache by its simulation stamp.]
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_BaseSim( Mfs3_Man_t * p, int Root )
{
    int k;
    if ( p->RootStamp != p->nSimStamp || p->RootId != Root )
    {
        Mfs3_SignalSim(p,Root,p->RootSim);
        for ( k = 0; k < Sfm_ObjFaninNum(p->pNtk,Root); k++ )
            Mfs3_SignalSim(p,Sfm_ObjFanin(p->pNtk,Root,k),p->RootFanSim[k]);
        if ( p->fCareCircuit )
        {
            word * pSim = Mfs3_Simulate(p,Abc_Lit2Var(p->CareLit));
            for ( k = 0; k < 4; k++ ) p->RootCareSim[k] = Abc_LitIsCompl(p->CareLit) ? ~pSim[k] : pSim[k];
        }
        else for ( k = 0; k < p->nSide; k++ ) Mfs3_SignalSim(p,p->Side[k],p->RootSideSim[k]);
        p->nRootSamples = p->RootStamp && p->RootId == Root ? Abc_MinInt(p->nRootSamples,192) : 0;
        p->RootStamp = p->nSimStamp;
        p->RootId = Root;
    }
}

/**Function*************************************************************

  Synopsis    [Decodes only the simulation samples actually examined.]

  Description [Most unsuccessful supports need only a few patterns. The
  decoded prefix is shared by all fanin-removal and divisor trials at a LUT.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_Sample( Mfs3_Man_t * p, int Index )
{
    int i, k, Row, Side;
    for ( i = p->nRootSamples; i <= Index; i++ )
    {
        Side = Row = 0;
        if ( !p->fCareCircuit )
            for ( k = 0; k < p->nSide; k++ ) Side |= Abc_TtGetBit(p->RootSideSim[k],i) << k;
        for ( k = 0; k < Sfm_ObjFaninNum(p->pNtk,p->RootId); k++ ) Row |= Abc_TtGetBit(p->RootFanSim[k],i) << k;
        p->RootRows[i] = Row;
        p->RootValues[i] = (p->fCareCircuit ? Abc_TtGetBit(p->RootCareSim,i) : Abc_TtGetBit(p->Care,Side)) ? Abc_TtGetBit(p->RootSim,i) : -1;
    }
    if ( p->nRootSamples <= Index ) p->nRootSamples = Index+1;
}

/**Function*************************************************************

  Synopsis    [Learns a replacement truth table and proves it over all inputs.]

  Description [Samples can reject a support, but never certify a change.
  A SAT witness adds a required on/off row; conflicting requirements reject
  the support. Unspecified rows are completed by ISOP before the next proof.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_TryInt( Mfs3_Man_t * p, int Root, int * Fans, int nFans, word * Result )
{
    word SimRoot[4], SimFans[8][4], SimDiv[4] = {0};
    word On[4] = {0}, Off[4] = {0}, Upper[4];
    int i, k, Row, Value, Lit, Status, Round, Index, FanLits[8], Seen[256];
    unsigned char Values[256];
    unsigned Used = 0;
    abctime clk = Abc_Clock();
    if ( p->PairStamp != p->nSimStamp ) { p->nPairs = 0; p->PairStamp = p->nSimStamp; }
    if ( nFans > p->nBase )
    {
        Mfs3_SignalSim(p,Fans[nFans-1],SimDiv);
        for ( i = 0; i < p->nPairs; i++ )
            if ( Abc_TtGetBit(SimDiv,p->Pair0[i]) == Abc_TtGetBit(SimDiv,p->Pair1[i]) )
            {
                p->nReject++;
                p->timeSim += Abc_Clock()-clk;
                return 0;
            }
    }
    Mfs3_BaseSim(p,Root);
    // Byte states avoid repeated truth-table bit operations for duplicate rows.
    memset(Values,0,sizeof(Values));
    for ( i = 0; i < 256; i++ )
    {
        Mfs3_Sample(p,i);
        Value = p->RootValues[i];
        if ( Value < 0 ) continue;
        Row = p->RootRows[i];
        Row = (Row & ((1 << p->BasePosition)-1)) | ((Row >> (p->BasePosition+1)) << p->BasePosition);
        Row |= Abc_TtGetBit(SimDiv,i) << p->nBase;
        if ( Values[Row] == 2-Value )
        {
            if ( p->nPairs < 16 )
            {
                p->Pair0[p->nPairs] = i;
                p->Pair1[p->nPairs++] = Seen[Row];
            }
            p->nReject++;
            p->timeSim += Abc_Clock()-clk;
            return 0;
        }
        if ( Values[Row] ) continue;
        Seen[Row] = i;
        Values[Row] = (unsigned char)(Value+1);
    }
    for ( Row = 0; Row < (1 << nFans); Row++ )
        if ( Values[Row] ) Mfs3_SetRow(Values[Row] == 2 ? On : Off,Row);
    p->timeSim += Abc_Clock()-clk;
    for ( Round = 0; Round <= (1 << nFans); Round++ )
    {
        // Keep only actual rows while learning; stretch once for the ISOP call.
        if ( nFans < 6 )
        {
            On[0] = Abc_Tt6Stretch(On[0],nFans);
            Off[0] = Abc_Tt6Stretch(Off[0],nFans);
        }
        Abc_TtStretch6(On,nFans,8);
        Abc_TtStretch6(Off,nFans,8);
        for ( k = 0; k < 4; k++ ) Upper[k] = ~Off[k];
        Abc_Tt8Isop(On,Upper,nFans,Result);
        for ( k = 0; k < nFans; k++ ) FanLits[k] = Mfs3_Function(p,Fans[k]);
        Vec_IntClear(p->vLeaves);
        for ( k = 0; k < nFans; k++ ) Vec_IntPush(p->vLeaves,FanLits[k]);
        // Dsm's one-input entry point expects an essential input.
        if ( Abc_TtIsConst0(Result,4) ) Lit = 0;
        else if ( Abc_TtIsConst1(Result,4) ) Lit = 1;
        else Lit = Dsm_ManTruthToGia(p->pPool,Result,p->vLeaves,p->vCover);
        Status = Mfs3_Prove(p,Mfs3_Function(p,Root),Lit,&Used);
        if ( Status == GLUCOSE3_UNSAT ) return 1;
        if ( Status == GLUCOSE3_UNDEC ) return -1;
        Index = p->iCex;
        clk = Abc_Clock();
        Mfs3_SignalSim(p,Root,SimRoot);
        Value = Abc_TtGetBit(SimRoot,Index);
        Row = 0;
        for ( k = 0; k < nFans; k++ )
        {
            Mfs3_SignalSim(p,Fans[k],SimFans[k]);
            Row |= Abc_TtGetBit(SimFans[k],Index) << k;
        }
        assert(Abc_TtGetBit(Result,Row) != Value);
        p->timeSim += Abc_Clock()-clk;
        if ( Abc_TtGetBit(Value ? Off : On,Row) ) return 0;
        assert(!Abc_TtGetBit(Value ? On : Off,Row));
        Mfs3_SetRow(Value ? On : Off,Row);
    }
    assert(0);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Matches an exact context before reusing refuted supports.]

  Description [Pool literals identify immutable functions, including changes
  caused by upstream ODC edits. A care table is keyed by its actual side
  functions; symbolic care is keyed by its pool literal. No timeout is cached.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_CachePrepare( Mfs3_Man_t * p, int Root )
{
    Mfs3_Cache_t * q = p->pCaches[Root];
    word Key[24];
    int i, Fan, nKey = 0;
    Key[nKey++] = Mfs3_Function(p,Root);
    Key[nKey++] = Sfm_ObjFaninNum(p->pNtk,Root);
    Sfm_ObjForEachFanin(p->pNtk,Root,Fan,i) Key[nKey++] = Mfs3_Function(p,Fan);
    Key[nKey++] = p->fCareCircuit ? ~(word)0 : (word)p->nSide;
    if ( p->fCareCircuit ) Key[nKey++] = p->CareLit;
    else
    {
        for ( i = 0; i < p->nSide; i++ ) Key[nKey++] = Mfs3_Function(p,p->Side[i]);
        for ( i = 0; i < 4; i++ ) Key[nKey++] = p->Care[i];
    }
    assert(nKey <= 24);
    if ( !q ) q = p->pCaches[Root] = ABC_CALLOC(Mfs3_Cache_t,1);
    if ( q->nKey != nKey || memcmp(q->Key,Key,sizeof(word)*nKey) )
    {
        memcpy(q->Key,Key,sizeof(word)*nKey);
        q->nKey = nKey;
        q->Removed = 0;
        q->AllDivs = 0;
    }
    p->pCache = q;
}

/**Function*************************************************************

  Synopsis    [Skips only supports already refuted in the identical context.]

  Description [A conflicting pair of cared-for assignments proves that no
  function over the proposed support works. An inconclusive proof does not.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Try( Mfs3_Man_t * p, int Root, int * Fans, int nFans, word * Result )
{
    Mfs3_Cache_t * q = p->pCache;
    int Pos = p->BasePosition, Ret;
    p->fTryUndec = 0;
    if ( nFans == p->nBase && (q->Removed & (1 << Pos)) )
    { p->nCacheHits++; return 0; }
    Ret = Mfs3_TryInt(p,Root,Fans,nFans,Result);
    if ( Ret == 0 && nFans == p->nBase ) q->Removed |= 1 << Pos;
    p->fTryUndec = Ret < 0;
    return Ret == 1;
}

/**Function*************************************************************

  Synopsis    [Checks whether an entire previously refuted divisor list survives.]

  Description [The context already fixes the pivot, fanins and care. Equal
  ordered lists of divisor functions permit skipping their refuted searches
  together, without a lookup per candidate. Changes discard the old verdict.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_CacheDivisors( Mfs3_Man_t * p )
{
    Mfs3_Cache_t * q = p->pCache;
    int i, Div, Size = Vec_IntSize(p->vDivs);
    Vec_IntClear(p->vDivLits);
    Vec_IntForEachEntry(p->vDivs,Div,i) Vec_IntPush(p->vDivLits,Mfs3_Function(p,Div));
    if ( q->vDivs && Vec_IntSize(q->vDivs) == Size &&
        (!Size || !memcmp(Vec_IntArray(q->vDivs),Vec_IntArray(p->vDivLits),sizeof(int)*Size)) ) return 1;
    q->AllDivs = 0;
    if ( q->vDivs )
    {
        p->nCacheEntries -= Vec_IntSize(q->vDivs);
        Vec_IntFreeP(&q->vDivs);
    }
    if ( Size > MFS3_CACHE_MAX-p->nCacheEntries ) return 0;
    q->vDivs = Vec_IntDup(p->vDivLits);
    p->nCacheEntries += Size;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects fanin divisors and nearby independent fanouts.]

  Description [A candidate enters only after all its fanins have entered.
  The pivot never enters, so a candidate cannot depend on the pivot.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_Divisors( Mfs3_Man_t * p, int Root )
{
    Sfm_Ntk_t * n = p->pNtk;
    int i, j, k, Id, Fan = -1, Fo, Limit = p->pPars->nWinSizeMax;
    int MaxLevel = n->nLevelMax - Sfm_ObjLevelR(n,Root);
    abctime clk = Abc_Clock();
    if ( ++p->nTrav == ABC_INFINITY ) { memset(p->pMarks,0,sizeof(int)*n->nObjs); p->nTrav = 1; }
    Vec_IntClear(p->vDivs);
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack,Root);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntEntryLast(p->vStack);
        if ( p->pMarks[Id] == p->nTrav ) { Vec_IntPop(p->vStack); continue; }
        Sfm_ObjForEachFanin(n,Id,Fan,k)
            if ( p->pMarks[Fan] != p->nTrav ) break;
        if ( k < Sfm_ObjFaninNum(n,Id) ) { Vec_IntPush(p->vStack,Fan); continue; }
        p->pMarks[Id] = p->nTrav;
        Vec_IntPop(p->vStack);
        if ( Id != Root ) Vec_IntPush(p->vDivs,Id);
        if ( Limit && Vec_IntSize(p->vDivs) > Limit )
        {
            Vec_IntClear(p->vDivs);
            p->nLarge++;
            p->timeDiv += Abc_Clock()-clk;
            return;
        }
    }
    // Root is marked as unavailable; all other marked nodes are independent.
    Vec_IntForEachEntry(p->vDivs,Id,i)
    {
        if ( Limit && Vec_IntSize(p->vDivs) >= Limit ) break;
        Sfm_ObjForEachFanout(n,Id,Fo,k)
        {
            if ( p->pPars->nFanoutMax && k > p->pPars->nFanoutMax ) break;
            if ( p->pMarks[Fo] == p->nTrav || Sfm_ObjIsPo(n,Fo) || Sfm_ObjLevel(n,Fo) > MaxLevel ) continue;
            Sfm_ObjForEachFanin(n,Fo,Fan,j)
                if ( Fan == Root || p->pMarks[Fan] != p->nTrav ) break;
            if ( j < Sfm_ObjFaninNum(n,Fo) ) continue;
            p->pMarks[Fo] = p->nTrav;
            Vec_IntPush(p->vDivs,Fo);
            if ( Limit && Vec_IntSize(p->vDivs) >= Limit ) break;
        }
    }
    k = 0;
    Vec_IntForEachEntry(p->vDivs,Id,i)
        if ( Sfm_ObjLevel(n,Id) <= MaxLevel && Vec_IntFind(Sfm_ObjFiArray(n,Root),Id) < 0 &&
             (Sfm_ObjIsPi(n,Id) || Sfm_ObjFaninNum(n,Id)) )
            Vec_IntWriteEntry(p->vDivs,k++,Id);
    Vec_IntShrink(p->vDivs,k);
    p->timeDiv += Abc_Clock()-clk;
}

/**Function*************************************************************

  Synopsis    [Commits a proved edit and retires only interior functions.]

  Description [Boundary functions are globally unchanged by the proof.
  Old circuit versions and their learned clauses remain valid indefinitely.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_Update( Mfs3_Man_t * p, int Root, int Position, int Div, word * Truth )
{
    int i;
    abctime clk = Abc_Clock();
    // Materialize boundary functions before changing their implementation.
    for ( i = 0; i < p->nWin; i++ )
        if ( p->Bound[i] ) Mfs3_Function(p,p->Win[i]);
    Sfm_NtkUpdate(p->pNtk,Root,Position,Div,Truth[0],Truth);
    for ( i = 0; i < p->nWin; i++ )
        if ( !p->Bound[i] ) p->pFuncs[p->Win[i]] = -1;
    p->nChanged++;
    p->RootStamp = 0;
    p->nRemoved += Div < 0;
    p->nResub += Div >= 0;
    p->timeUpdate += Abc_Clock()-clk;
}

/**Function*************************************************************

  Synopsis    [Commits a proved constant or one-input replacement atomically.]

  Description [Intermediate fanin-list updates are not exposed to queries.
  All exit functions are saved before editing and only interiors are retired.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_UpdateSimple( Mfs3_Man_t * p, int Root, int Fan, int Phase )
{
    Sfm_Ntk_t * n = p->pNtk;
    word Truth[4];
    int i, k, Position, nOld = Sfm_ObjFaninNum(n,Root);
    abctime clk = Abc_Clock();
    for ( i = 0; i < p->nWin; i++ )
        if ( p->Bound[i] ) Mfs3_Function(p,p->Win[i]);
    if ( Fan < 0 )
    {
        for ( k = 0; k < 4; k++ ) Truth[k] = Phase ? ~(word)0 : 0;
        Sfm_NtkUpdate(n,Root,0,-1,Truth[0],Truth);
    }
    else
        while ( Sfm_ObjFaninNum(n,Root) > 1 )
        {
            Position = Sfm_ObjFanin(n,Root,0) == Fan ? 1 : 0;
            i = Vec_IntFind(Sfm_ObjFiArray(n,Root),Fan);
            assert(i >= 0);
            i -= Position < i;
            for ( k = 0; k < 4; k++ ) Truth[k] = Phase ? ~n->TtElems[i][k] : n->TtElems[i][k];
            Sfm_NtkUpdate(n,Root,Position,-1,Truth[0],Truth);
        }
    for ( i = 0; i < p->nWin; i++ )
        if ( !p->Bound[i] ) p->pFuncs[p->Win[i]] = -1;
    p->RootStamp = 0;
    p->nChanged++;
    p->nRemoved += nOld-Sfm_ObjFaninNum(n,Root);
    p->timeUpdate += Abc_Clock()-clk;
}

/**Function*************************************************************

  Synopsis    [Finds LUT-saving constants and buffers without edge-only trials.]

  Description [This retains the area benefit of successive redundant-edge
  removals while avoiding intermediate searches that cannot remove a LUT.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Simple( Mfs3_Man_t * p, int Root )
{
    word Care[4], Sim[4], Inputs[8];
    int i, k, w, Phase, Fan, Lit, RootLit = Mfs3_Function(p,Root), Status;
    int CareStamp = 0;
    int nFans = Sfm_ObjFaninNum(p->pNtk,Root);
    for ( i = -1; i < (nFans > 1 ? nFans : 0); i++ )
        for ( Phase = 0; Phase < 2; Phase++ )
        {
            unsigned Used = 0;
            Mfs3_BaseSim(p,Root);
            if ( CareStamp != p->nSimStamp )
            {
                if ( p->fCareCircuit ) memcpy(Care,p->RootCareSim,sizeof(Care));
                else if ( Abc_TtIsConst1(p->Care,4) || Abc_TtIsConst0(p->Care,4) )
                    for ( w = 0; w < 4; w++ ) Care[w] = p->Care[0];
                else
                    for ( w = CareStamp ? 3 : 0; w < 4; w++ )
                    {
                        for ( k = 0; k < p->nSide; k++ ) Inputs[k] = p->RootSideSim[k][w];
                        Care[w] = Mfs3_Eval_rec(p->Care,p->nSide,0,Inputs);
                    }
                CareStamp = p->nSimStamp;
            }
            Fan = i < 0 ? -1 : Sfm_ObjFanin(p->pNtk,Root,i);
            Lit = i < 0 ? Phase : Mfs3_Function(p,Fan) ^ Phase;
            for ( w = 0; w < 4; w++ )
            {
                Sim[w] = i < 0 ? 0 : p->RootFanSim[i][w];
                if ( Phase ) Sim[w] = ~Sim[w];
                if ( (Sim[w] ^ p->RootSim[w]) & Care[w] ) break;
            }
            if ( w < 4 ) continue;
            Status = Mfs3_Prove(p,RootLit,Lit,&Used);
            if ( Status != GLUCOSE3_UNSAT ) continue;
            Mfs3_UpdateSimple(p,Root,Fan,Phase);
            return 1;
        }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Tries area-critical fanins first, then redundant edges.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int Mfs3_Node( Mfs3_Man_t * p, int Root )
{
    Sfm_Ntk_t * n = p->pNtk;
    int i, k, j, Pass, Fan, Div, Fans[8], nFans, fArea;
    int fDivsReady = 0, fDivsCached = 0, fUndec;
    word Truth[4];
    if ( !Sfm_ObjFaninNum(n,Root) || !Sfm_ObjFanoutNum(n,Root) ) return 0;
    // A fanin edit leaves this pivot's fanouts and all side functions intact.
    // Keep the original window and its care throughout the pivot's trials.
    if ( p->CareRoot != Root )
    {
        Mfs3_ComputeCare(p,Root);
        p->CareRoot = Root;
    }
    p->nTried++;
    if ( p->pPars->fArea && Mfs3_Simple(p,Root) ) return 1;
    Mfs3_CachePrepare(p,Root);
    Vec_IntClear(p->vDivs);
    for ( Pass = 0; Pass < (p->pPars->fArea ? 1 : 2); Pass++ )
        Sfm_ObjForEachFanin(n,Root,Fan,i)
        {
            fArea = Sfm_ObjIsNode(n,Fan) && !Sfm_ObjIsFixed(n,Fan) && Sfm_ObjFanoutNum(n,Fan) == 1;
            if ( fArea != !Pass ) continue;
            nFans = 0;
            for ( k = 0; k < Sfm_ObjFaninNum(n,Root); k++ )
                if ( k != i ) Fans[nFans++] = Sfm_ObjFanin(n,Root,k);
            p->nBase = nFans;
            p->BasePosition = i;
            p->nPairs = 0;
            if ( Mfs3_Try(p,Root,Fans,nFans,Truth) )
            {
                Mfs3_Update(p,Root,i,-1,Truth);
                return 1;
            }
            if ( !fArea || p->pPars->fRrOnly ) continue;
            if ( !fDivsReady )
            {
                Mfs3_Divisors(p,Root);
                fDivsCached = Mfs3_CacheDivisors(p);
                fDivsReady = 1;
            }
            if ( fDivsCached && (p->pCache->AllDivs & (1 << i)) )
            { p->nCacheHits += Vec_IntSize(p->vDivs); continue; }
            fUndec = 0;
            Vec_IntForEachEntry(p->vDivs,Div,j)
            {
                Fans[nFans] = Div;
                if ( Mfs3_Try(p,Root,Fans,nFans+1,Truth) )
                {
                    Mfs3_Update(p,Root,i,Div,Truth);
                    return 1;
                }
                fUndec |= p->fTryUndec;
            }
            if ( fDivsCached && !fUndec ) p->pCache->AllDivs |= 1 << i;
        }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Initializes immutable functions and deterministic patterns.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static Mfs3_Man_t * Mfs3_Start( Gia_Man_t * pGia, Sfm_Ntk_t * pNtk, Sfm_Par_t * pPars, int nSideMax )
{
    Mfs3_Man_t * p = ABC_CALLOC(Mfs3_Man_t,1);
    Gia_Obj_t * pObj;
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(pGia));
    word Rand = ABC_CONST(0x8e5b791d6a3c024f);
    int i, Id, Lit, a, b, w;
    p->pNtk = pNtk;
    p->pPars = pPars;
    pNtk->pPars = pPars;
    pNtk->nLevelMax = Vec_IntFindMax(&pNtk->vLevels) + pPars->nGrowthLevel;
    p->nSideMax = nSideMax;
    p->nSimStamp = 1;
    p->pPool = Gia_ManStart(Gia_ManObjNum(pGia));
    Gia_ManHashAlloc(p->pPool);
    p->pFuncs = ABC_ALLOC(int,pNtk->nObjs);
    memset(p->pFuncs,0xFF,sizeof(int)*pNtk->nObjs);
    p->pSlots = ABC_CALLOC(int,pNtk->nObjs);
    p->pMarks = ABC_CALLOC(int,pNtk->nObjs);
    p->pCaches = ABC_CALLOC(Mfs3_Cache_t *,pNtk->nObjs);
    p->vStack = Vec_IntAlloc(100);
    p->vFuncStack = Vec_IntAlloc(100);
    p->vLeaves = Vec_IntAlloc(16);
    p->vCover = Vec_IntAlloc(1000);
    p->vDivs = Vec_IntAlloc(1000);
    p->vDivLits = Vec_IntAlloc(1000);
    p->vSatLits = Vec_IntAlloc(1000);
    p->vSatToCi = Vec_IntAlloc(1000);
    p->vSimStamp = Vec_IntAlloc(1000);
    p->vSims = Vec_WrdAlloc(1000);
    p->vJustValues = Vec_IntAlloc(1000);
    p->vJustVisit = Vec_IntAlloc(256);
    Gia_ManForEachCiId(pGia,Id,i)
    {
        Lit = Gia_ManAppendCi(p->pPool);
        Vec_IntWriteEntry(vMap,Id,Lit);
        p->pFuncs[Gia_ObjCopyArray(pGia,Id)] = Lit;
    }
    Gia_ManForEachAnd(pGia,pObj,Id)
    {
        a = Vec_IntEntry(vMap,Gia_ObjFaninId0(pObj,Id)) ^ Gia_ObjFaninC0(pObj);
        b = Vec_IntEntry(vMap,Gia_ObjFaninId1(pObj,Id)) ^ Gia_ObjFaninC1(pObj);
        Vec_IntWriteEntry(vMap,Id,Gia_ManHashAnd(p->pPool,a,b));
    }
    p->pFuncs[Gia_ObjCopyArray(pGia,0)] = 0;
    Gia_ManForEachLut(pGia,Id)
        p->pFuncs[Gia_ObjCopyArray(pGia,Id)] = Vec_IntEntry(vMap,Id);
    Vec_IntFree(vMap);
    Mfs3_Grow(p);
    Gia_ManForEachCiId(p->pPool,Id,i)
        for ( w = 0; w < MFS3_SIM_WORDS; w++ )
        {
            Rand ^= Rand << 13;
            Rand ^= Rand >> 7;
            Rand ^= Rand << 17;
            Vec_WrdWriteEntry(p->vSims,MFS3_SIM_WORDS*Id+w,w ? Rand : (Rand & ~(word)3) | 2);
        }
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the sweeping manager.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void Mfs3_Stop( Mfs3_Man_t * p )
{
    int i;
    for ( i = 0; i < p->pNtk->nObjs; i++ )
        if ( p->pCaches[i] )
        {
            Vec_IntFreeP(&p->pCaches[i]->vDivs);
            ABC_FREE(p->pCaches[i]);
        }
    ABC_FREE(p->pCaches);
    if ( p->pSat ) bmcg3_sat_solver_stop(p->pSat);
    Gia_ManStop(p->pPool);
    ABC_FREE(p->pFuncs);
    ABC_FREE(p->pSlots);
    ABC_FREE(p->pMarks);
    Vec_IntFree(p->vStack);
    Vec_IntFree(p->vFuncStack);
    Vec_IntFree(p->vLeaves);
    Vec_IntFree(p->vCover);
    Vec_IntFree(p->vDivs);
    Vec_IntFree(p->vDivLits);
    Vec_IntFree(p->vSatLits);
    Vec_IntFree(p->vSatToCi);
    Vec_IntFree(p->vSimStamp);
    Vec_WrdFree(p->vSims);
    Vec_IntFree(p->vJustValues);
    Vec_IntFree(p->vJustVisit);
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Sweeps a mapped circuit using one reusable Glucose3 solver.]

  Description [Register boundaries are treated as combinational terminals
  by the command wrapper. The original MFS implementation is unchanged.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManPerformMfs3( Gia_Man_t * pGia, Sfm_Par_t * pPars, int nSideMax, int nRounds, int fSingle )
{
    Sfm_Ntk_t * n;
    Mfs3_Man_t * p;
    Gia_Man_t * pNew;
    int i, r, nTried = 0, Before, nLuts = Gia_ManLutNum(pGia);
    int fArea = pPars->fArea;
    abctime clk = Abc_Clock();
    Gia_ObjComputeTruthTableStop(pGia);
    n = Gia_ManExtractMfs(pGia);
    p = Mfs3_Start(pGia,n,pPars,nSideMax);
    // The area prepass and subsequent full sweeps share functions, patterns,
    // and learned clauses. Explicit area-only and single-pass modes skip it.
    for ( r = !fArea && !fSingle ? -1 : 0; r < nRounds; r++ )
    {
        pPars->fArea = fArea || r < 0;
        Before = p->nChanged;
        Sfm_NtkForEachNode(n,i)
        {
            if ( Sfm_ObjIsFixed(n,i) || !Sfm_ObjFanoutNum(n,i) || Sfm_ObjFaninNum(n,i) > 8 ||
                (pPars->nDepthMax && Sfm_ObjLevel(n,i) > pPars->nDepthMax) ) continue;
            p->CareRoot = -1;
            while ( Mfs3_Node(p,i) ) {}
            if ( pPars->nNodesMax && ++nTried >= pPars->nNodesMax ) break;
        }
        if ( (r >= 0 && Before == p->nChanged) || (pPars->nNodesMax && nTried >= pPars->nNodesMax) ) break;
    }
    pPars->fArea = fArea;
    if ( p->nChanged ) pNew = Gia_ManInsertMfs(pGia,n,0);
    else
    {
        pNew = Gia_ManDup(pGia);
        pNew->vMapping = Vec_IntDup(pGia->vMapping);
    }
    if ( pPars->fVerbose )
    {
        printf("MFS3: LUTs = %d -> %d. Attempts = %d. Removals = %d. Resubs = %d.\n",
            nLuts,Gia_ManLutNum(pNew),p->nTried,p->nRemoved,p->nResub);
        printf("MFS3: simulation rejects = %d. SAT = %d. UNSAT = %d. Unknown = %d. Recycles = %d. Justified = %d.\n",
            p->nReject,p->nSat,p->nUnsat,p->nUndec,p->nRecycles,p->nJustified);
        printf("MFS3: cached refutations = %d. Stored divisor functions = %d.\n",p->nCacheHits,p->nCacheEntries);
        printf("MFS3: windows = %d. Shallower = %d. Side overflows = %d. Node overflows = %d. Care circuits = %d.\n",
            p->nWindows,p->nShallower,p->nSideOver,p->nNodeOver,p->nCareCircuits);
        printf("MFS3: window depths:");
        for ( i = 0; i <= 32; i++ ) if ( p->Depths[i] ) printf(" %d:%d",i,p->Depths[i]);
        printf("\n");
        printf("MFS3: Care %.3f  Div %.3f  Sim %.3f  Encode %.3f  SAT %.3f  Update %.3f  Justify %.3f  Total %.3f sec.\n",
            (double)p->timeCare/CLOCKS_PER_SEC,(double)p->timeDiv/CLOCKS_PER_SEC,
            (double)p->timeSim/CLOCKS_PER_SEC,(double)p->timeCnf/CLOCKS_PER_SEC,
            (double)p->timeSat/CLOCKS_PER_SEC,(double)p->timeUpdate/CLOCKS_PER_SEC,(double)p->timeJust/CLOCKS_PER_SEC,
            (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    }
    Mfs3_Stop(p);
    Sfm_NtkFree(n);
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
