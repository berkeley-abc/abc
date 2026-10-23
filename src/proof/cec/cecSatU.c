/**CFile****************************************************************

  FileName    [cecSatU.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Constant replacement under bounded observability don't-cares.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSatU.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig/gia/giaEdit.h"
#include "cec.h"
#include "misc/util/utilTruth.h"
#include "sat/glucose3/AbcGlucose3.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Every fanout window is closed at an absolute logic level. Therefore no
// external side input depends on the target through a path outside the window.
// All exits are observed. The exact Boolean difference at these exits is
// covered by cubes of existing signals, used only as SAT assumptions.
//
// An accepted replacement preserves every exit function. Only window interiors
// need new SAT definitions; old variables and their learned clauses remain valid
// descriptions of the old functions. In particular, an ODC replacement NEVER
// asserts a permanent constant value for the original SAT variable.

enum { CECU_WINDOW_MAX = 64, CECU_SUPPORT_MAX = 6, CECU_CUBE_MAX = 64,
       CECU_RECYCLE_VARS = 200000, CECU_RECYCLE_CALLS = 500,
       CECU_JUSTIFY_LIMIT = 2048, CECU_JUSTIFY_RETRIES = 4,
       CECU_CACHE_CONE = 4096, CECU_CACHE_DEPTH = 128,
       CECU_CACHE_BINS = 65536, CECU_CACHE_INTS = 4000000 };

typedef struct CecU_Man_t_ CecU_Man_t;
struct CecU_Man_t_
{
    Gia_Man_t * pAig;
    Cec_ParFra_t * pPars;
    bmcg3_sat_solver * pSat;
    bmcg3_sat_solver * pLocal;
    Vec_Int_t * vLocalToCi;
    int nLocal;
    int nObjs, nWords, nOdc;
    int * pRefs;
    int * pFanoutOff;
    int * pFanouts;
    int * pLevels;
    int * pSatLits;
    int * pSlots;
    unsigned char * pConst;       // 0: ordinary signal, 1: zero, 2: one
    unsigned char * pCands;       // potential zero/one replacements
    word * pSims;
    word * pReplay;
    int * pReplayStamp;
    Vec_Int_t * vSatToCi;
    int nReplay, nReplayReject;
    Vec_Int_t * vStack;
    Vec_Int_t * vVisit;
    unsigned char * pValues;
    int nJustifyLeft, nRetries, nJustified;
    int * pCanon;
    int * pCacheBins;
    Vec_Int_t * vCanonIds;
    Vec_Int_t * vProgram;
    Vec_Int_t * vCache;
    unsigned CacheHash;
    int fCacheable, nCacheHits;
    int RootLit, nRootIds, nRootProgram;
    int Win[CECU_WINDOW_MAX], nWin;
    int Side[CECU_SUPPORT_MAX], nSide;
    unsigned char Bound[CECU_WINDOW_MAX];
    int nCands, nWindows, nSimReject, nProved[2], nSat, nUnsat, nUndec;
    int nCubes, nRecycles, nCallsSince;
    abctime timeStart, timeSim, timeWindow, timeCnf, timeSat, timeUpdate, timeJustify, timeCache;
};

static inline word CecU_LitSim( CecU_Man_t * p, int Lit, int w )
{
    word Value = p->pSims[(size_t)Abc_Lit2Var(Lit)*p->nWords + w];
    return Abc_LitIsCompl(Lit) ? ~Value : Value;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Local deterministic random stream, independent of ABC globals.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static word CecU_Random( word * pState )
{
    word z = (*pState += ABC_CONST(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * ABC_CONST(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * ABC_CONST(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

/**Function*************************************************************

  Synopsis    [Simulates and finds constant candidates with compatible cares.]

  Description [At an observed AND with two zero inputs, preserve one controlling
  input rather than declaring both unobservable. This conservative backward
  filter is safe under reconvergence. It is only a candidate filter: every
  accepted change is subsequently proved using the current local circuit.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_Simulate( CecU_Man_t * p )
{
    Gia_Obj_t * pObj;
    word State = ABC_CONST(0x1234567812345678);
    word * pCare = ABC_CALLOC( word, (size_t)p->nObjs*p->nWords );
    int i, w, Id0, Id1, Can0, Can1;
    abctime clk = Abc_Clock();
    Gia_ManForEachObj( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) )
            for ( w = 0; w < p->nWords; w++ )
                p->pSims[(size_t)i*p->nWords+w] = (CecU_Random(&State) & ~(word)3) | 2;
        else if ( Gia_ObjIsAnd(pObj) )
        {
            int Lit0 = Gia_ObjFaninLit0(pObj, i), Lit1 = Gia_ObjFaninLit1(pObj, i);
            p->pRefs[Abc_Lit2Var(Lit0)]++;
            p->pRefs[Abc_Lit2Var(Lit1)]++;
            p->pLevels[i] = 1 + Abc_MaxInt(p->pLevels[Abc_Lit2Var(Lit0)], p->pLevels[Abc_Lit2Var(Lit1)]);
            for ( w = 0; w < p->nWords; w++ )
            {
                word a = CecU_LitSim(p, Lit0, w), b = CecU_LitSim(p, Lit1, w);
                p->pSims[(size_t)i*p->nWords+w] = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
            }
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            p->pRefs[Gia_ObjFaninId0(pObj,i)]++;
            for ( w = 0; w < p->nWords; w++ )
                pCare[(size_t)Gia_ObjFaninId0(pObj,i)*p->nWords+w] = ~(word)0;
        }
    }
    Gia_ManForEachAndReverse( p->pAig, pObj, i )
    {
        Id0 = Gia_ObjFaninId0(pObj, i);
        Id1 = Gia_ObjFaninId1(pObj, i);
        Can0 = Can1 = 1;
        for ( w = 0; w < p->nWords; w++ )
        {
            word Care = pCare[(size_t)i*p->nWords+w];
            word Sim = p->pSims[(size_t)i*p->nWords+w];
            word a = CecU_LitSim(p, Gia_ObjFaninLit0(pObj,i), w);
            word b = CecU_LitSim(p, Gia_ObjFaninLit1(pObj,i), w);
            Can0 &= (Sim & Care) == 0;
            Can1 &= (~Sim & Care) == 0;
            if ( Gia_ObjIsXor(pObj) )
            {
                pCare[(size_t)Id0*p->nWords+w] |= Care;
                pCare[(size_t)Id1*p->nWords+w] |= Care;
            }
            else
            {
                pCare[(size_t)Id0*p->nWords+w] |= Care & b;
                pCare[(size_t)Id1*p->nWords+w] |= Care & (~b | a);
            }
        }
        p->pCands[i] = (unsigned char)(Can0 | (Can1 << 1));
        p->nCands += p->pRefs[i] && p->pCands[i];
    }
    ABC_FREE(pCare);
    p->timeSim += Abc_Clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Stores fanout lists only for possible window interiors.]

  Description [The forward maximum of candidate level bounds marks every
  node that can belong to any window. All fanout edges of marked nodes are
  retained, including edges leaving the region, so every exit is observed.
  Temporary level bounds and insertion counts reuse the empty window slots.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_Fanouts( CecU_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, a, b, Limit, Offset = 1;
    p->pFanoutOff = ABC_CALLOC(int,p->nObjs);
    Gia_ManForEachAnd( p->pAig, pObj, i )
    {
        a = Gia_ObjFaninId0(pObj,i);
        b = Gia_ObjFaninId1(pObj,i);
        Limit = Abc_MaxInt(p->pSlots[a],p->pSlots[b]);
        if ( p->pCands[i] && p->pRefs[i] )
            Limit = Abc_MaxInt(Limit,p->pLevels[i]+p->nOdc+1);
        if ( Limit > p->pLevels[i] && p->pRefs[i] )
            p->pSlots[i] = Limit;
    }
    for ( i = 0; i < p->nObjs; i++ )
        if ( p->pSlots[i] )
        {
            p->pFanoutOff[i] = Offset;
            Offset += p->pRefs[i]+1;
            p->pSlots[i] = 0;
        }
    p->pFanouts = ABC_ALLOC(int,Offset);
    p->pFanouts[0] = 0;
    Gia_ManForEachObj( p->pAig, pObj, i )
    {
        if ( !Gia_ObjIsAnd(pObj) && !Gia_ObjIsCo(pObj) ) continue;
        a = Gia_ObjFaninId0(pObj,i);
        if ( p->pFanoutOff[a] )
            p->pFanouts[p->pFanoutOff[a]+1+p->pSlots[a]++] = i;
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        b = Gia_ObjFaninId1(pObj,i);
        if ( p->pFanoutOff[b] )
            p->pFanouts[p->pFanoutOff[b]+1+p->pSlots[b]++] = i;
    }
    for ( i = 0; i < p->nObjs; i++ )
        if ( p->pFanoutOff[i] )
        {
            assert(p->pSlots[i] == p->pRefs[i]);
            p->pFanouts[p->pFanoutOff[i]] = p->pSlots[i];
            p->pSlots[i] = 0;
        }
}

#define CecU_ForEachFanout( p, Id, Fo, k ) \
    for ( k = 0; k < (p)->pFanouts[(p)->pFanoutOff[Id]] && \
        ((Fo = (p)->pFanouts[(p)->pFanoutOff[Id]+1+k]), 1); k++ )

/**Function*************************************************************

  Synopsis    [Clears only the slots touched by the preceding window.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_WindowClear( CecU_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nWin; i++ ) p->pSlots[p->Win[i]] = 0;
    for ( i = 0; i < p->nSide; i++ ) p->pSlots[p->Side[i]] = 0;
    p->nWin = p->nSide = 0;
}

/**Function*************************************************************

  Synopsis    [Collects a closed bounded fanout window and independent sides.]

  Description [A failed capacity check rejects the whole window. The caller
  can retry a shallower level boundary; no fanout path is silently omitted.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_Window( CecU_Man_t * p, int Root, int Depth )
{
    int i, k, Fo, Id, Fan, MaxLevel = p->pLevels[Root] + Depth;
    Gia_Obj_t * pObj;
    CecU_WindowClear(p);
    p->Win[p->nWin++] = Root;
    p->pSlots[Root] = 1;
    for ( i = 0; i < p->nWin; i++ )
        CecU_ForEachFanout( p, p->Win[i], Fo, k )
        {
            pObj = Gia_ManObj(p->pAig, Fo);
            if ( Gia_ObjIsCo(pObj) || !p->pRefs[Fo] || p->pConst[Fo] || p->pLevels[Fo] > MaxLevel )
                continue;
            if ( p->pSlots[Fo] ) continue;
            if ( p->nWin == CECU_WINDOW_MAX ) return 0;
            p->pSlots[Fo] = 1;
            p->Win[p->nWin++] = Fo;
        }
    // Insertion sort is cheap for these small windows and has a fixed tie order.
    for ( i = 1; i < p->nWin; i++ )
    {
        Id = p->Win[i];
        for ( k = i; k && p->Win[k-1] > Id; k-- ) p->Win[k] = p->Win[k-1];
        p->Win[k] = Id;
    }
    for ( i = 0; i < p->nWin; i++ ) p->pSlots[p->Win[i]] = i+1;
    memset(p->Bound, 0, sizeof(p->Bound));
    for ( i = 0; i < p->nWin; i++ )
    {
        CecU_ForEachFanout( p, p->Win[i], Fo, k )
        {
            pObj = Gia_ManObj(p->pAig, Fo);
            if ( Gia_ObjIsCo(pObj) || (p->pRefs[Fo] && !p->pConst[Fo] && p->pSlots[Fo] <= 0) )
                p->Bound[i] = 1;
        }
        if ( !i ) continue;
        pObj = Gia_ManObj(p->pAig, p->Win[i]);
        for ( k = 0; k < 2; k++ )
        {
            Fan = k ? Gia_ObjFaninId1(pObj,p->Win[i]) : Gia_ObjFaninId0(pObj,p->Win[i]);
            if ( !Fan || p->pConst[Fan] || p->pSlots[Fan] ) continue;
            if ( p->nSide == CECU_SUPPORT_MAX ) return 0;
            p->Side[p->nSide++] = Fan;
            p->pSlots[Fan] = -p->nSide;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Reads a cofactor value from a window or its side boundary.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static inline word CecU_WindowLit( CecU_Man_t * p, int Lit, word * Values, int w )
{
    int Id = Abc_Lit2Var(Lit), Slot = p->pSlots[Id];
    word Value;
    if ( !Id || p->pConst[Id] ) Value = p->pConst[Id] == 2 ? ~(word)0 : 0;
    else if ( Slot > 0 ) Value = Values[Slot-1];
    else
    {
        assert(Slot < 0);
        Value = w == -1 ? s_Truths6[-Slot-1] : w == -2 ? p->pReplay[Id] : p->pSims[(size_t)Id*p->nWords+w];
    }
    return Abc_LitIsCompl(Lit) ? ~Value : Value;
}

/**Function*************************************************************

  Synopsis    [Computes exact local care, as simulation bits or a truth table.]

  Description [Both target values are propagated through every occurrence.
  This handles reconvergence without making individual-path assumptions.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static word CecU_Care( CecU_Man_t * p, int w )
{
    word Values[2][CECU_WINDOW_MAX], Care = 0;
    int i, c;
    Values[0][0] = 0;
    Values[1][0] = ~(word)0;
    for ( i = 0; i < p->nWin; i++ )
    {
        if ( i )
        {
            int Id = p->Win[i];
            Gia_Obj_t * pObj = Gia_ManObj(p->pAig, Id);
            for ( c = 0; c < 2; c++ )
            {
                word a = CecU_WindowLit(p, Gia_ObjFaninLit0(pObj,Id), Values[c], w);
                word b = CecU_WindowLit(p, Gia_ObjFaninLit1(pObj,Id), Values[c], w);
                Values[c][i] = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
            }
        }
        if ( p->Bound[i] ) Care |= Values[0][i] ^ Values[1][i];
    }
    return Care;
}

/**Function*************************************************************

  Synopsis    [Starts or recycles the permanent circuit-function solver.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_SolverStart( CecU_Man_t * p )
{
    int Lit = 1;
    if ( p->pSat )
    {
        bmcg3_sat_solver_reset(p->pSat);
        p->nRecycles++;
    }
    else
    {
        p->pSat = bmcg3_sat_solver_start();
        bmcg3_sat_solver_set_jftr(p->pSat, p->pPars->jType);
        bmcg3_sat_solver_eliminate(p->pSat, 1);
    }
    bmcg3_sat_solver_addvar(p->pSat);
    bmcg3_sat_solver_addclause(p->pSat, &Lit, 1);
    memset(p->pSatLits, 0xFF, sizeof(int)*p->nObjs);
    p->pSatLits[0] = 0;
    Vec_IntFill(p->vSatToCi,1,0);
    p->nCallsSince = 0;
}

/**Function*************************************************************

  Synopsis    [Uses the sweeper's native-XOR recognition when still valid.]

  Description [A forced constant inside the three-AND implementation disables
  recognition. Replacements below its two inputs preserve the XOR identity.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_Fanins( CecU_Man_t * p, int Id, int * pLit0, int * pLit1 )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pAig,Id), * pFan0, * pFan1;
    *pLit0 = Gia_ObjFaninLit0(pObj,Id);
    *pLit1 = Gia_ObjFaninLit1(pObj,Id);
    if ( !p->pAig->pMuxes && !p->pConst[Abc_Lit2Var(*pLit0)] && !p->pConst[Abc_Lit2Var(*pLit1)] &&
         Gia_ObjRecognizeExor(pObj,&pFan0,&pFan1) )
    {
        *pLit0 = Abc_Var2Lit(Gia_ObjId(p->pAig,Gia_Regular(pFan0)),Gia_IsComplement(pFan0));
        *pLit1 = Abc_Var2Lit(Gia_ObjId(p->pAig,Gia_Regular(pFan1)),Gia_IsComplement(pFan1));
        return 1;
    }
    return Gia_ObjIsXor(pObj);
}

/**Function*************************************************************

  Synopsis    [Lazily encodes current functions without changing old variables.]

  Description [The explicit DFS stack also handles very deep input cones.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_SatLit( CecU_Man_t * p, int Root )
{
    int Id, Id0, Id1, a, b, Var, IsXor, Lit0, Lit1;
    Gia_Obj_t * pObj;
    if ( p->pConst[Root] ) return p->pConst[Root]-1;
    if ( p->pSatLits[Root] >= 0 ) return p->pSatLits[Root];
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack, Root);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntEntryLast(p->vStack);
        if ( p->pConst[Id] ) p->pSatLits[Id] = p->pConst[Id]-1;
        if ( p->pSatLits[Id] >= 0 ) { Vec_IntPop(p->vStack); continue; }
        pObj = Gia_ManObj(p->pAig, Id);
        if ( Gia_ObjIsCi(pObj) )
        {
            Var = bmcg3_sat_solver_addvar(p->pSat);
            assert(Vec_IntSize(p->vSatToCi) == Var);
            Vec_IntPush(p->vSatToCi,Id);
            p->pSatLits[Id] = Abc_Var2Lit(Var, 0);
            Vec_IntPop(p->vStack);
            continue;
        }
        assert(Gia_ObjIsAnd(pObj));
        IsXor = CecU_Fanins(p,Id,&Lit0,&Lit1);
        Id0 = Abc_Lit2Var(Lit0);
        Id1 = Abc_Lit2Var(Lit1);
        if ( p->pConst[Id0] ) p->pSatLits[Id0] = p->pConst[Id0]-1;
        if ( p->pConst[Id1] ) p->pSatLits[Id1] = p->pConst[Id1]-1;
        if ( p->pSatLits[Id0] < 0 ) { Vec_IntPush(p->vStack, Id0); continue; }
        if ( p->pSatLits[Id1] < 0 ) { Vec_IntPush(p->vStack, Id1); continue; }
        a = p->pSatLits[Id0] ^ Abc_LitIsCompl(Lit0);
        b = p->pSatLits[Id1] ^ Abc_LitIsCompl(Lit1);
        if ( IsXor && a < 2 ) p->pSatLits[Id] = b ^ a;
        else if ( IsXor && b < 2 ) p->pSatLits[Id] = a ^ b;
        else if ( a == b ) p->pSatLits[Id] = IsXor ? 0 : a;
        else if ( a == (b ^ 1) ) p->pSatLits[Id] = IsXor ? 1 : 0;
        else if ( !IsXor && (!a || !b) ) p->pSatLits[Id] = 0;
        else if ( !IsXor && a == 1 ) p->pSatLits[Id] = b;
        else if ( !IsXor && b == 1 ) p->pSatLits[Id] = a;
        else
        {
            Var = bmcg3_sat_solver_addvar(p->pSat);
            assert(Vec_IntSize(p->vSatToCi) == Var);
            Vec_IntPush(p->vSatToCi,0);
            p->pSatLits[Id] = Abc_Var2Lit(Var,0);
            if ( p->pPars->jType < 2 )
            {
                if ( IsXor ) bmcg3_sat_solver_add_xor(p->pSat,Var,Abc_Lit2Var(a),Abc_Lit2Var(b),(a^b)&1);
                else bmcg3_sat_solver_add_and(p->pSat,Var,Abc_Lit2Var(a),Abc_Lit2Var(b),a&1,b&1,0);
            }
            if ( p->pPars->jType > 0 )
            {
                if ( (a > b) ^ IsXor ) { int Temp = a; a = b; b = Temp; }
                bmcg3_sat_solver_set_var_fanin_lit(p->pSat,Var,a,b);
            }
        }
        Vec_IntPop(p->vStack);
    }
    return p->pSatLits[Root];
}

/**Function*************************************************************

  Synopsis    [Reads a partial assignment of a current circuit literal.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static inline int CecU_Assigned( CecU_Man_t * p, int Lit )
{
    int Id = Abc_Lit2Var(Lit), Value;
    if ( !Id ) return Lit;
    Value = p->pConst[Id] ? p->pConst[Id] : p->pValues[Id];
    return Value ? (Value-1) ^ Abc_LitIsCompl(Lit) : -1;
}

/**Function*************************************************************

  Synopsis    [Looks one gate ahead when choosing a controlling input.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_Implied( CecU_Man_t * p, int Lit )
{
    Gia_Obj_t * pObj;
    int Value = CecU_Assigned(p,Lit), Id = Abc_Lit2Var(Lit), a, b;
    if ( Value >= 0 ) return Value;
    pObj = Gia_ManObj(p->pAig,Id);
    if ( !Gia_ObjIsAnd(pObj) ) return -1;
    a = CecU_Assigned(p,Gia_ObjFaninLit0(pObj,Id));
    b = CecU_Assigned(p,Gia_ObjFaninLit1(pObj,Id));
    if ( Gia_ObjIsXor(pObj) ) Value = a >= 0 && b >= 0 ? a ^ b : -1;
    else Value = a == 0 || b == 0 ? 0 : (a == 1 && b == 1 ? 1 : -1);
    return Value < 0 ? -1 : Value ^ Abc_LitIsCompl(Lit);
}

/**Function*************************************************************

  Synopsis    [Finds a real counterexample by bounded circuit justification.]

  Description [Adapted from CecZ_ManGeneratePatterns_rec: retain assignments
  shared by assumptions, retry a controlling AND input with complete undo, and
  tail-iterate the last child. Success is a consistent partial CI assignment;
  failure is inconclusive and never authorizes a replacement.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_Justify_rec( CecU_Man_t * p, int Lit )
{
    Gia_Obj_t * pObj;
    int Id, Value, a, b, Va, Vb, Choice, Save, IsXor;
again:
    Value = CecU_Assigned(p,Lit);
    if ( Value >= 0 ) return Value;
    if ( --p->nJustifyLeft < 0 ) return 0;
    Id = Abc_Lit2Var(Lit);
    Value = !Abc_LitIsCompl(Lit);
    p->pValues[Id] = (unsigned char)(Value+1);
    Vec_IntPush(p->vVisit,Id);
    pObj = Gia_ManObj(p->pAig,Id);
    if ( Gia_ObjIsCi(pObj) ) return 1;
    IsXor = CecU_Fanins(p,Id,&a,&b);
    Va = CecU_Assigned(p,a);
    Vb = CecU_Assigned(p,b);
    if ( IsXor )
    {
        if ( Va >= 0 ) { Lit = b ^ (1 ^ Value ^ Va); goto again; }
        if ( Vb >= 0 ) { Lit = a ^ (1 ^ Value ^ Vb); goto again; }
        Choice = (int)(CecU_LitSim(p,a,0) & 1);
        if ( !CecU_Justify_rec(p,a ^ !Choice) ) return 0;
        Lit = b ^ (1 ^ Value ^ Choice);
        goto again;
    }
    if ( Value )
    {
        if ( Va == 0 || Vb == 0 ) return 0;
        if ( !CecU_Justify_rec(p,a) ) return 0;
        Lit = b;
        goto again;
    }
    if ( Va == 0 || Vb == 0 ) return 1;
    if ( Va == 1 ) { Lit = b ^ 1; goto again; }
    if ( Vb == 1 ) { Lit = a ^ 1; goto again; }
    Va = CecU_Implied(p,a);
    Vb = CecU_Implied(p,b);
    if ( Va == 0 || Vb == 1 ) { Lit = a ^ 1; goto again; }
    if ( Vb == 0 || Va == 1 ) { Lit = b ^ 1; goto again; }
    Choice = p->pLevels[Abc_Lit2Var(a)] > p->pLevels[Abc_Lit2Var(b)];
    if ( p->nRetries )
    {
        Save = Vec_IntSize(p->vVisit);
        if ( CecU_Justify_rec(p,(Choice ? b : a) ^ 1) ) return 1;
        if ( !p->nRetries || p->nJustifyLeft < 0 ) return 0;
        p->nRetries--;
        while ( Vec_IntSize(p->vVisit) > Save ) p->pValues[Vec_IntPop(p->vVisit)] = 0;
        Choice ^= 1;
    }
    Lit = (Choice ? b : a) ^ 1;
    goto again;
}

/**Function*************************************************************

  Synopsis    [Rejects an observable constant replacement without SAT loading.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_Justify( CecU_Man_t * p, int Root, int Value, int Cube )
{
    int k, Res = 0, Attempt;
    assert(Vec_IntSize(p->vVisit) == 0);
    for ( Attempt = 0; Attempt < (Cube ? 2 : 1) && !Res; Attempt++ )
    {
        p->nJustifyLeft = CECU_JUSTIFY_LIMIT;
        p->nRetries = CECU_JUSTIFY_RETRIES;
        Res = Attempt ? 1 : CecU_Justify_rec(p,Abc_Var2Lit(Root,Value));
        for ( k = 0; Res && k < p->nSide; k++ )
        {
            int Pol = (Cube >> (2*k)) & 3;
            if ( Pol ) Res = CecU_Justify_rec(p,Abc_Var2Lit(p->Side[k],Pol == 1));
        }
        if ( Res && Attempt ) Res = CecU_Justify_rec(p,Abc_Var2Lit(Root,Value));
        while ( Vec_IntSize(p->vVisit) ) p->pValues[Vec_IntPop(p->vVisit)] = 0;
    }
    p->nJustified += Res;
    return Res;
}

/**Function*************************************************************

  Synopsis    [Canonicalizes a complete small query cone, preserving sharing.]

  Description [Adapted from CecZ_LocalBuild. A truncated cone is not cached:
  SAT and UNSAT results of the main solver require the complete definitions.
  CI numbers are replaced by discovery order, so isomorphic queries can share
  results without confusing distinct or reconvergent signals.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_CanonBuild( CecU_Man_t * p, int Id, int Depth )
{
    Gia_Obj_t * pObj;
    int a = -1, b = -1, Lit;
    if ( !Id || p->pConst[Id] ) return p->pConst[Id] ? p->pConst[Id]-1 : 0;
    if ( p->pCanon[Id] ) return p->pCanon[Id]-1;
    if ( !Depth || Vec_IntSize(p->vCanonIds) >= CECU_CACHE_CONE ) return -1;
    pObj = Gia_ManObj(p->pAig,Id);
    if ( Gia_ObjIsAnd(pObj) )
    {
        a = CecU_CanonBuild(p,Gia_ObjFaninId0(pObj,Id),Depth-1);
        if ( a < 0 ) return -1;
        b = CecU_CanonBuild(p,Gia_ObjFaninId1(pObj,Id),Depth-1);
        if ( b < 0 ) return -1;
        a ^= Gia_ObjFaninC0(pObj);
        b ^= Gia_ObjFaninC1(pObj);
        if ( (a > b) ^ Gia_ObjIsXor(pObj) ) { int Temp = a; a = b; b = Temp; }
        // Equal fanins cannot encode an XOR by order; simplify first.
        if ( a == b || a == (b^1) )
        {
            Lit = Gia_ObjIsXor(pObj) ? (a^b) : (a == b ? a : 0);
            p->pCanon[Id] = Lit+1;
            // This alias has no program slot but must be cleared next time.
            Vec_IntPush(p->vCanonIds,Id);
            return Lit;
        }
    }
    Lit = Vec_IntSize(p->vProgram);
    p->pCanon[Id] = Lit+1;
    Vec_IntPush(p->vCanonIds,Id);
    Vec_IntPushTwo(p->vProgram,a,b);
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Builds the common root prefix once for all care cubes.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_CacheStart( CecU_Man_t * p, int Root )
{
    int i, Id;
    if ( !p->pCanon )
    {
        // Zero is unmapped; literal+1 also represents aliases of constant zero.
        p->pCanon = ABC_CALLOC(int,p->nObjs);
        p->pCacheBins = ABC_CALLOC(int,CECU_CACHE_BINS);
        p->vCanonIds = Vec_IntAlloc(CECU_CACHE_CONE+CECU_CACHE_DEPTH);
        p->vProgram = Vec_IntAlloc(2*CECU_CACHE_CONE+2*CECU_CACHE_DEPTH+16);
        p->vCache = Vec_IntAlloc(10000);
        Vec_IntPush(p->vCache,0);
    }
    Vec_IntForEachEntry(p->vCanonIds,Id,i) p->pCanon[Id] = 0;
    Vec_IntClear(p->vCanonIds);
    Vec_IntClear(p->vProgram);
    Vec_IntPushTwo(p->vProgram,-1,-1);
    p->RootLit = CecU_CanonBuild(p,Root,CECU_CACHE_DEPTH);
    p->nRootIds = Vec_IntSize(p->vCanonIds);
    p->nRootProgram = Vec_IntSize(p->vProgram);
}

/**Function*************************************************************

  Synopsis    [Checks exact complete-cone keys for one care cube.]

  Description [Discard the preceding cube's side cones while retaining the
  root's canonical IDs, aliases and program. This produces exactly the same
  key as building each query from scratch. No circuit changes during a proof.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_CacheFind( CecU_Man_t * p, int Value, int Cube )
{
    int i, SideLits[CECU_SUPPORT_MAX], Entry, nSide = 0;
    unsigned Hash = 2166136261u;
    p->fCacheable = 0;
    if ( p->RootLit < 0 ) return -1;
    while ( Vec_IntSize(p->vCanonIds) > p->nRootIds )
        p->pCanon[Vec_IntPop(p->vCanonIds)] = 0;
    Vec_IntShrink(p->vProgram,p->nRootProgram);
    for ( i = 0; i < p->nSide; i++ )
    {
        int Pol = (Cube >> (2*i)) & 3, Lit;
        if ( !Pol ) continue;
        Lit = CecU_CanonBuild(p,p->Side[i],CECU_CACHE_DEPTH);
        if ( Lit < 0 ) return -1;
        SideLits[nSide++] = Lit ^ (Pol == 1);
    }
    // Explicit framing prevents a gate pair from being confused with the
    // trailing query fields of a different-length program.
    Vec_IntWriteEntry(p->vProgram,0,Vec_IntSize(p->vProgram));
    Vec_IntWriteEntry(p->vProgram,1,nSide+1);
    Vec_IntPush(p->vProgram,p->RootLit ^ Value);
    for ( i = 0; i < nSide; i++ ) Vec_IntPush(p->vProgram,SideLits[i]);
    Vec_IntForEachEntry(p->vProgram,Entry,i) Hash = (Hash ^ (unsigned)Entry) * 16777619u;
    p->CacheHash = Hash & (CECU_CACHE_BINS-1);
    p->fCacheable = 1;
    for ( Entry = p->pCacheBins[p->CacheHash]; Entry; Entry = Vec_IntEntry(p->vCache,Entry) )
        if ( Vec_IntEntry(p->vCache,Entry+1) == Vec_IntSize(p->vProgram) &&
             !memcmp(Vec_IntEntryP(p->vCache,Entry+3),Vec_IntArray(p->vProgram),sizeof(int)*Vec_IntSize(p->vProgram)) )
        {
            p->nCacheHits++;
            return Vec_IntEntry(p->vCache,Entry+2);
        }
    return -1;
}

/**Function*************************************************************

  Synopsis    [Stores a complete proof or counterexample under an exact key.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_CacheSave( CecU_Man_t * p, int Result )
{
    int Entry;
    if ( !p->fCacheable ) return;
    if ( Vec_IntSize(p->vCache) > CECU_CACHE_INTS )
    {
        Vec_IntFill(p->vCache,1,0);
        memset(p->pCacheBins,0,sizeof(int)*CECU_CACHE_BINS);
    }
    Entry = Vec_IntSize(p->vCache);
    Vec_IntPushThree(p->vCache,p->pCacheBins[p->CacheHash],Vec_IntSize(p->vProgram),Result);
    Vec_IntAppend(p->vCache,p->vProgram);
    p->pCacheBins[p->CacheHash] = Entry;
}

/**Function*************************************************************

  Synopsis    [Saves the SAT counterexample for lazy bit-parallel replay.]

  Description []

  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_SaveCex( CecU_Man_t * p, bmcg3_sat_solver * pSat, Vec_Int_t * vSatToCi )
{
    int i, Id, Lit, * pCex;
    word Bit;
    if ( !p->pReplay )
    {
        p->pReplay = ABC_CALLOC(word,p->nObjs);
        p->pReplayStamp = ABC_CALLOC(int,p->nObjs);
    }
    if ( p->nReplay == INT_MAX )
    {
        memset(p->pReplayStamp,0,sizeof(int)*p->nObjs);
        p->nReplay = 0;
    }
    Bit = (word)1 << (p->nReplay++ & 63);
    if ( !p->pPars->jType )
    {
        Vec_IntForEachEntry( vSatToCi, Id, i )
            if ( Id )
            {
                p->pReplay[Id] &= ~Bit;
                if ( bmcg3_sat_solver_read_cex_varvalue(pSat,i) ) p->pReplay[Id] |= Bit;
            }
    }
    else
    {
        pCex = bmcg3_sat_solver_read_cex(pSat);
        for ( i = 1; i <= pCex[0]; i++ )
        {
            Lit = pCex[i];
            if ( !Abc_Lit2Var(Lit) ) continue;
            Id = Vec_IntEntry(vSatToCi,Abc_Lit2Var(Lit));
            assert(Id && Gia_ObjIsCi(Gia_ManObj(p->pAig,Id)));
            p->pReplay[Id] &= ~Bit;
            if ( !Abc_LitIsCompl(Lit) ) p->pReplay[Id] |= Bit;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Replays recent counterexamples lazily in the needed cones.]

  Description [Unassigned inputs retain arbitrary values. Every bit is a
  complete CI assignment, including the initially all-zero unused slots.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static word CecU_Replay( CecU_Man_t * p, int Root )
{
    Gia_Obj_t * pObj;
    int Id, Id0, Id1;
    Vec_IntClear(p->vStack);
    Vec_IntPush(p->vStack,Root);
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntEntryLast(p->vStack);
        if ( p->pReplayStamp[Id] == p->nReplay ) { Vec_IntPop(p->vStack); continue; }
        pObj = Gia_ManObj(p->pAig,Id);
        if ( !Id || p->pConst[Id] ) p->pReplay[Id] = p->pConst[Id] == 2 ? ~(word)0 : 0;
        else if ( !Gia_ObjIsCi(pObj) )
        {
            word a, b;
            Id0 = Gia_ObjFaninId0(pObj,Id);
            Id1 = Gia_ObjFaninId1(pObj,Id);
            if ( p->pReplayStamp[Id0] != p->nReplay ) { Vec_IntPush(p->vStack,Id0); continue; }
            if ( p->pReplayStamp[Id1] != p->nReplay ) { Vec_IntPush(p->vStack,Id1); continue; }
            a = Gia_ObjFaninC0(pObj) ? ~p->pReplay[Id0] : p->pReplay[Id0];
            b = Gia_ObjFaninC1(pObj) ? ~p->pReplay[Id1] : p->pReplay[Id1];
            p->pReplay[Id] = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
        }
        p->pReplayStamp[Id] = p->nReplay;
        Vec_IntPop(p->vStack);
    }
    return p->pReplay[Root];
}

/**Function*************************************************************

  Synopsis    [Loads a complete canonical cone and its cube assumptions.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_LocalStart( CecU_Man_t * p, int * pLits )
{
    int * pProg = Vec_IntArray(p->vProgram);
    int Size = pProg[0], i, Id, Lit = 1;
    if ( !p->pLocal )
    {
        p->pLocal = bmcg3_sat_solver_start();
        bmcg3_sat_solver_set_jftr(p->pLocal,p->pPars->jType);
        bmcg3_sat_solver_eliminate(p->pLocal,1);
        p->vLocalToCi = Vec_IntAlloc(128);
    }
    else bmcg3_sat_solver_reset(p->pLocal);
    bmcg3_sat_solver_set_nvars(p->pLocal,Size/2);
    bmcg3_sat_solver_addclause(p->pLocal,&Lit,1);
    Vec_IntFill(p->vLocalToCi,Size/2,0);
    Vec_IntForEachEntry( p->vCanonIds, Id, i )
        if ( Gia_ObjIsCi(Gia_ManObj(p->pAig,Id)) )
            Vec_IntWriteEntry(p->vLocalToCi,Abc_Lit2Var(p->pCanon[Id]-1),Id);
    for ( i = 2; i < Size; i += 2 )
    {
        int a = pProg[i], b = pProg[i+1], Var = i/2;
        if ( a < 0 ) continue;
        if ( p->pPars->jType < 2 )
        {
            if ( a > b ) bmcg3_sat_solver_add_xor(p->pLocal,Var,Abc_Lit2Var(a),Abc_Lit2Var(b),(a^b)&1);
            else bmcg3_sat_solver_add_and(p->pLocal,Var,Abc_Lit2Var(a),Abc_Lit2Var(b),a&1,b&1,0);
        }
        if ( p->pPars->jType > 0 ) bmcg3_sat_solver_set_var_fanin_lit(p->pLocal,Var,a,b);
    }
    for ( i = 0; i < pProg[1]; i++ ) pLits[i] = pProg[Size+i];
    p->nLocal++;
    return pProg[1];
}

/**Function*************************************************************

  Synopsis    [Proves all care cubes with a shared conflict budget.]

  Description [Complete small cones use a recycled private Glucose3 instance,
  avoiding unrelated fanouts accumulated by the large persistent solver.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
static int CecU_Prove( CecU_Man_t * p, int Root, int Value, word Care )
{
    bmcg3_sat_solver * pSat;
    int Cover[CECU_CUBE_MAX], Lits[CECU_SUPPORT_MAX+1];
    int nCubes = 0, i, k, nLits, Status, StartConf, Limit = p->pPars->nBTLimit;
    unsigned Used = 0;
    abctime clk;
    if ( !Care ) return 1;
    Abc_Tt6IsopCover(Care,Care,p->nSide,Cover,&nCubes);
    assert(nCubes <= CECU_CUBE_MAX);
    clk = Abc_Clock();
    for ( i = 0; i < nCubes; i++ )
        if ( CecU_Justify(p,Root,Value,Cover[i]) )
        {
            p->timeJustify += Abc_Clock() - clk;
            return 0;
        }
    p->timeJustify += Abc_Clock() - clk;
    for ( i = 0; i < nCubes; i++ )
    {
        clk = Abc_Clock();
        if ( !i ) CecU_CacheStart(p,Root);
        Status = CecU_CacheFind(p,Value,Cover[i]);
        p->timeCache += Abc_Clock() - clk;
        if ( Status == 0 ) return 0;
        if ( Status == 1 ) continue;
        if ( Limit && Used >= (unsigned)Limit ) { p->nUndec++; return 0; }
        clk = Abc_Clock();
        if ( p->fCacheable )
        {
            nLits = CecU_LocalStart(p,Lits);
            pSat = p->pLocal;
        }
        else
        {
            if ( !p->pSat || (bmcg3_sat_solver_varnum(p->pSat) > CECU_RECYCLE_VARS && p->nCallsSince >= CECU_RECYCLE_CALLS) )
                CecU_SolverStart(p);
            nLits = 0;
            Lits[nLits++] = CecU_SatLit(p,Root) ^ Value;
            for ( k = 0; k < p->nSide; k++ )
            {
                int Pol = (Cover[i] >> (2*k)) & 3;
                if ( Pol ) Lits[nLits++] = CecU_SatLit(p,p->Side[k]) ^ (Pol == 1);
            }
            pSat = p->pSat;
        }
        if ( p->pPars->jType > 0 )
        {
            bmcg3_sat_solver_start_new_round(pSat);
            for ( k = 0; k < nLits; k++ ) bmcg3_sat_solver_mark_cone(pSat,Abc_Lit2Var(Lits[k]));
        }
        p->timeCnf += Abc_Clock() - clk;
        StartConf = bmcg3_sat_solver_conflictnum(pSat);
        clk = Abc_Clock();
        bmcg3_sat_solver_set_conflict_budget(pSat,Limit ? Limit-(int)Used : 0);
        Status = bmcg3_sat_solver_solve(pSat,Lits,nLits);
        Used += (unsigned)bmcg3_sat_solver_conflictnum(pSat) - (unsigned)StartConf;
        p->timeSat += Abc_Clock() - clk;
        p->nCubes++;
        p->nCallsSince += pSat == p->pSat;
        if ( Status == GLUCOSE3_UNSAT )
        {
            p->nUnsat++;
            CecU_CacheSave(p,1);
        }
        else
        {
            if ( Status == GLUCOSE3_SAT )
            {
                p->nSat++;
                CecU_CacheSave(p,0);
                CecU_SaveCex(p,pSat,pSat == p->pLocal ? p->vLocalToCi : p->vSatToCi);
            }
            else p->nUndec++;
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Applies a proved replacement and retires only interior functions.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static void CecU_Replace( CecU_Man_t * p, int Root, int Value )
{
    Gia_Obj_t * pObj;
    int i, w, Id;
    abctime clk = Abc_Clock();
    p->pConst[Root] = (unsigned char)(Value+1);
    p->nProved[Value]++;
    for ( i = 0; i < p->nWin; i++ )
    {
        Id = p->Win[i];
        pObj = Gia_ManObj(p->pAig,Id);
        if ( !p->Bound[i] )
        {
            p->pSatLits[Id] = -1;
            if ( p->pReplayStamp ) p->pReplayStamp[Id] = 0;
        }
        for ( w = 0; w < p->nWords; w++ )
        {
            word Old = p->pSims[(size_t)Id*p->nWords+w], New;
            if ( !i ) New = Value ? ~(word)0 : 0;
            else
            {
                word a = CecU_LitSim(p,Gia_ObjFaninLit0(pObj,Id),w);
                word b = CecU_LitSim(p,Gia_ObjFaninLit1(pObj,Id),w);
                New = Gia_ObjIsXor(pObj) ? a ^ b : a & b;
            }
            assert(!p->Bound[i] || Old == New);
            p->pSims[(size_t)Id*p->nWords+w] = New;
        }
    }
    pObj = Gia_ManObj(p->pAig,Root);
    Vec_IntClear(p->vStack);
    Vec_IntPushTwo(p->vStack,Gia_ObjFaninId0(pObj,Root),Gia_ObjFaninId1(pObj,Root));
    while ( Vec_IntSize(p->vStack) )
    {
        Id = Vec_IntPop(p->vStack);
        assert(p->pRefs[Id] > 0);
        if ( --p->pRefs[Id] || p->pConst[Id] ) continue;
        pObj = Gia_ManObj(p->pAig,Id);
        if ( Gia_ObjIsAnd(pObj) )
            Vec_IntPushTwo(p->vStack,Gia_ObjFaninId0(pObj,Id),Gia_ObjFaninId1(pObj,Id));
    }
    p->timeUpdate += Abc_Clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Exports constant substitutions and structural simplifications.]

  Description []
  SideEffects []
  SeeAlso     []

***********************************************************************/
static Gia_Man_t * CecU_Export( CecU_Man_t * p )
{
    Gia_Man_t * q;
    // Proof is finished. Reuse its scratch arrays for original-ID aliases,
    // output literals, and reachability rather than constructing two GIAs.
    int * pAlias = p->pSatLits, * pCopy = p->pSlots;
    unsigned char * pLive = p->pCands;
    Gia_Obj_t * pObj;
    int i, a, b, nLive = 1 + Gia_ManCiNum(p->pAig) + Gia_ManCoNum(p->pAig);
    pAlias[0] = pCopy[0] = 0;
    memset(pLive,0,p->nObjs);
    Gia_ManForEachObj( p->pAig, pObj, i )
    {
        pAlias[i] = Abc_Var2Lit(i,0);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        if ( p->pConst[i] ) { pAlias[i] = p->pConst[i]-1; continue; }
        a = pAlias[Gia_ObjFaninId0(pObj,i)] ^ Gia_ObjFaninC0(pObj);
        b = pAlias[Gia_ObjFaninId1(pObj,i)] ^ Gia_ObjFaninC1(pObj);
        if ( Gia_ObjIsXor(pObj) )
        {
            if ( a < 2 ) pAlias[i] = b ^ a;
            else if ( b < 2 ) pAlias[i] = a ^ b;
            else if ( (a >> 1) == (b >> 1) ) pAlias[i] = a ^ b;
        }
        else
        {
            if ( a < 2 ) pAlias[i] = a ? b : 0;
            else if ( b < 2 ) pAlias[i] = b ? a : 0;
            else if ( a == b ) pAlias[i] = a;
            else if ( a == (b ^ 1) ) pAlias[i] = 0;
        }
    }
    Gia_ManForEachCo( p->pAig, pObj, i )
        pLive[Abc_Lit2Var(pAlias[Gia_ObjFaninId0p(p->pAig,pObj)])] = 1;
    Gia_ManForEachAndReverse( p->pAig, pObj, i )
        if ( pLive[i] )
        {
            assert(pAlias[i] == Abc_Var2Lit(i,0));
            pLive[Abc_Lit2Var(pAlias[Gia_ObjFaninId0(pObj,i)])] = 1;
            pLive[Abc_Lit2Var(pAlias[Gia_ObjFaninId1(pObj,i)])] = 1;
            nLive++;
        }
    q = Gia_ManStart(nLive);
    q->pName = Abc_UtilStrsav(p->pAig->pName);
    q->pSpec = Abc_UtilStrsav(p->pAig->pSpec);
    if ( p->pAig->pMuxes ) q->pMuxes = ABC_CALLOC(unsigned,q->nObjsAlloc);
    Gia_ManForEachObj( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) pCopy[i] = Gia_ManAppendCi(q);
        else if ( Gia_ObjIsAnd(pObj) )
        {
            if ( !pLive[i] ) continue;
            a = pAlias[Gia_ObjFaninId0(pObj,i)] ^ Gia_ObjFaninC0(pObj);
            b = pAlias[Gia_ObjFaninId1(pObj,i)] ^ Gia_ObjFaninC1(pObj);
            a = pCopy[Abc_Lit2Var(a)] ^ Abc_LitIsCompl(a);
            b = pCopy[Abc_Lit2Var(b)] ^ Abc_LitIsCompl(b);
            // Keep XOR inputs positive; move their polarity to the result.
            pCopy[i] = Gia_ObjIsXor(pObj) ?
                Gia_ManAppendXorReal2(q,Abc_LitRegular(a),Abc_LitRegular(b)) ^ ((a ^ b) & 1) : Gia_ManAppendAnd(q,a,b);
        }
        else if ( Gia_ObjIsCo(pObj) )
        {
            a = pAlias[Gia_ObjFaninId0(pObj,i)] ^ Gia_ObjFaninC0(pObj);
            Gia_ManAppendCo(q,pCopy[Abc_Lit2Var(a)] ^ Abc_LitIsCompl(a));
        }
    }
    assert(Gia_ManObjNum(q) == nLive);
    Gie_ManDupMetadata(q,p->pAig);
    return q;
}

/**Function*************************************************************

  Synopsis    [Performs one pass of bounded-ODC redundancy removal.]

  Description [Sequential interfaces are combinational boundaries. Every CO,
  including each next-state input, must be preserved for every CI assignment.]

  SideEffects []
  SeeAlso     []

***********************************************************************/
Gia_Man_t * CecU_ManPerform( Gia_Man_t * pAig, Cec_ParFra_t * pPars, int nOdc )
{
    CecU_Man_t * p;
    Gia_Man_t * pRes;
    Gia_Obj_t * pObj;
    int i, w, c, d, Can;
    abctime clk;
    if ( Gia_ManBufNum(pAig) || Gia_ManMuxNum(pAig) || pAig->pManTime || Gia_ManHasChoices(pAig) )
    {
        Abc_Print(-1,"&fraig -u requires an AIG without buffers, explicit MUXes, timing boxes, or choices.\n");
        return NULL;
    }
    if ( pPars->fRewriting || pPars->fUseCones || pPars->fDualOut || pPars->fRunCSat || pPars->fCheckMiter || pPars->fBMiterInfo || pPars->pDumpName )
    {
        Abc_Print(-1,"&fraig -u does not support -r, -k, -d, -c, -m, -q, or -F.\n");
        return NULL;
    }
    if ( pPars->nWords < 1 || pPars->nWords > INT_MAX/Gia_ManObjNum(pAig) ||
         Gia_ManObjNum(pAig) > INT_MAX/3 || pPars->nBTLimit < 0 ||
         pPars->jType < 0 || pPars->jType > 2 || nOdc < 0 || nOdc > 32 )
    {
        Abc_Print(-1,"&fraig -u: invalid simulation size, conflict limit, solver type, or ODC depth (0..32).\n");
        return NULL;
    }
    p = ABC_CALLOC(CecU_Man_t,1);
    p->timeStart = Abc_Clock();
    p->pAig = pAig;
    p->pPars = pPars;
    p->nObjs = Gia_ManObjNum(pAig);
    p->nWords = pPars->nWords;
    p->nOdc = nOdc;
    p->pRefs = ABC_CALLOC(int,p->nObjs);
    p->pLevels = ABC_CALLOC(int,p->nObjs);
    p->pSatLits = ABC_ALLOC(int,p->nObjs);
    // Initialized on the first persistent-solver query, if one is needed.
    p->pSlots = ABC_CALLOC(int,p->nObjs);
    p->pConst = ABC_CALLOC(unsigned char,p->nObjs);
    p->pCands = ABC_CALLOC(unsigned char,p->nObjs);
    p->pSims = ABC_CALLOC(word,(size_t)p->nObjs*p->nWords);
    p->vStack = Vec_IntAlloc(256);
    p->vSatToCi = Vec_IntAlloc(256);
    p->vVisit = Vec_IntAlloc(CECU_JUSTIFY_LIMIT);
    p->pValues = ABC_CALLOC(unsigned char,p->nObjs);
    CecU_Simulate(p);
    CecU_Fanouts(p);
    Gia_ManForEachAndReverse( pAig, pObj, i )
    {
        word Care;
        if ( !p->pCands[i] || !p->pRefs[i] || p->pConst[i] ) continue;
        clk = Abc_Clock();
        for ( d = nOdc; d >= 0; d-- ) if ( CecU_Window(p,i,d) ) break;
        assert(d >= 0);
        p->nWindows++;
        Can = p->pCands[i];
        for ( w = 0; w < p->nWords && Can; w++ )
        {
            word Mask = CecU_Care(p,w), Sim = p->pSims[(size_t)i*p->nWords+w];
            if ( Mask & Sim ) Can &= ~1;
            if ( Mask & ~Sim ) Can &= ~2;
        }
        if ( Can && p->nReplay )
        {
            word Mask, Sim = CecU_Replay(p,i);
            for ( w = 0; w < p->nSide; w++ ) CecU_Replay(p,p->Side[w]);
            Mask = CecU_Care(p,-2);
            if ( Mask & Sim ) Can &= ~1;
            if ( Mask & ~Sim ) Can &= ~2;
            if ( !Can ) p->nReplayReject++;
        }
        if ( !Can )
        {
            p->nSimReject++;
            p->timeWindow += Abc_Clock() - clk;
            continue;
        }
        Care = CecU_Care(p,-1);
        for ( w = 0; w < p->nSide; w++ ) p->pSlots[p->Side[w]] = 0;
        p->nSide = Abc_Tt6MinBase(&Care,p->Side,p->nSide);
        for ( w = 0; w < p->nSide; w++ ) p->pSlots[p->Side[w]] = -w-1;
        p->timeWindow += Abc_Clock() - clk;
        for ( c = 0; c < 2; c++ )
            if ( (Can & (1 << c)) && CecU_Prove(p,i,c,Care) )
            {
                CecU_Replace(p,i,c);
                break;
            }
    }
    pRes = CecU_Export(p);
    if ( pPars->fVerbose )
    {
        Abc_Print(1,"ODC: depth=%d words=%d candidates=%d windows=%d sim-reject=%d constants=%d/%d\n",
            nOdc,p->nWords,p->nCands,p->nWindows,p->nSimReject,p->nProved[0],p->nProved[1]);
        Abc_Print(1,"SAT: cubes=%d unsat=%d sat=%d undec=%d recycles=%d justified=%d cache-hits=%d replay-reject=%d\n",
            p->nCubes,p->nUnsat,p->nSat,p->nUndec,p->nRecycles,p->nJustified,p->nCacheHits,p->nReplayReject);
        Abc_Print(1,"Local queries: %d\n",p->nLocal);
        Abc_Print(1,"Time: sim=%.6f window=%.6f encode=%.6f sat=%.6f update=%.6f justify=%.6f cache=%.6f total=%.6f sec\n",
            (double)p->timeSim/CLOCKS_PER_SEC,(double)p->timeWindow/CLOCKS_PER_SEC,(double)p->timeCnf/CLOCKS_PER_SEC,
            (double)p->timeSat/CLOCKS_PER_SEC,(double)p->timeUpdate/CLOCKS_PER_SEC,(double)p->timeJustify/CLOCKS_PER_SEC,(double)p->timeCache/CLOCKS_PER_SEC,(double)(Abc_Clock()-p->timeStart)/CLOCKS_PER_SEC);
    }
    if ( p->pSat ) bmcg3_sat_solver_stop(p->pSat);
    if ( p->pLocal ) bmcg3_sat_solver_stop(p->pLocal);
    Vec_IntFreeP(&p->vLocalToCi);
    ABC_FREE(p->pRefs);
    ABC_FREE(p->pFanoutOff);
    ABC_FREE(p->pFanouts);
    ABC_FREE(p->pLevels);
    ABC_FREE(p->pSatLits);
    ABC_FREE(p->pSlots);
    ABC_FREE(p->pConst);
    ABC_FREE(p->pCands);
    ABC_FREE(p->pSims);
    ABC_FREE(p->pReplay);
    ABC_FREE(p->pReplayStamp);
    ABC_FREE(p->pValues);
    Vec_IntFree(p->vStack);
    Vec_IntFree(p->vSatToCi);
    Vec_IntFree(p->vVisit);
    ABC_FREE(p->pCanon);
    ABC_FREE(p->pCacheBins);
    Vec_IntFreeP(&p->vCanonIds);
    Vec_IntFreeP(&p->vProgram);
    Vec_IntFreeP(&p->vCache);
    ABC_FREE(p);
    return pRes;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
