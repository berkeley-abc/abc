/**CFile****************************************************************

  FileName    [abs2Core.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Incremental flop abstraction.]

  Synopsis    [Incremental flop abstraction using lazy unrolling and CBA/PBA.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 21, 2026.]

  Revision    [$Id: abs2Core.c,v 1.00 2026/10/21 00:00:00 alanmi Exp $]

  Reference   [Een, Mishchenko, Amla, FMCAD 2010, arXiv:1008.2021.
               See also ZZ/Bip/Abstraction.cc (Niklas Een).]

***********************************************************************/

#include "abs2.h"
#include "sat/cadical/ccadical.h"
#include "misc/util/utilTruth.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

typedef struct Abs2_Frame_t_
{
    int * pLits;                  // Original object -> unrolled Gia literal.
    unsigned char * pLinked;      // Full link installed; directional mode: prepared=4, directions=1/2.
} Abs2_Frame_t;

struct Abs2_Man_t_
{
    Gia_Man_t * pGia, * pUnroll, * pGiaOrig;
    Abc_Cex_t * pCex;
    int Depth, Stable, Bad, Result, fCexExternal, fSimplifyPending;
    Vec_Int_t * vKeepUntil;
    CCaDiCaL * pSat;
    Abs2_Par_t * pPars;
    Vec_Ptr_t * vFrames, * vValues;
    Vec_Int_t * vClasses, * vActs, * vFrozen, * vBads, * vAdd;
    Vec_Int_t * vEncoded, * vKeep, * vCnfStack, * vConjStack, * vLeaves;
    Vec_Int_t * vSatVars, * vBadLits, * vCore, * vCbaOrder;
    Vec_Wrd_t * vStack, * vQueue, * vUndo;
    Vec_Wrd_t * vPolStack, * vRoInfo;
    Vec_Int_t * vPolPending;
    Vec_Wec_t * vResolveDefs;
    Vec_Int_t * vResolvePos;
    Vec_Int_t * vCnfRefs, * vResolveMerged, * vMemoMap, * vMemoIds, * vMemoMerged, * vCombine;
    Vec_Wec_t * vMemoDefs;
    int iMemoNext;
    int nConcrete, nSatVars, nInactiveActs, fCompactVars, fStopped, fError;
    abctime clkStart, clkStop;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Expands native mux/XOR nodes while preserving interface order.]

  Description [Expand real mux/XOR nodes without recursive cleanup or register remapping.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Abs2_Normalize( Gia_Man_t * pGia )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    if ( !pGia->pMuxes && !Gia_ManXorNum(pGia) ) return Gia_ManDup(pGia);
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) );
    pNew->pName = Abc_UtilStrsav(pGia->pName);
    pNew->pSpec = Abc_UtilStrsav(pGia->pSpec);
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManHashStart(pNew);
    Gia_ManForEachObj1( pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) pObj->Value = Gia_ManAppendCi(pNew);
        else if ( Gia_ObjIsCo(pObj) ) pObj->Value = Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj));
        else if ( Gia_ObjIsBuf(pObj) ) pObj->Value = Gia_ObjFanin0Copy(pObj);
        else if ( Gia_ObjIsMux(pGia, pObj) )
            pObj->Value = Gia_ManHashMux(pNew, Gia_ObjFanin2Copy(pGia, pObj), Gia_ObjFanin1Copy(pObj), Gia_ObjFanin0Copy(pObj));
        else if ( Gia_ObjIsXor(pObj) ) pObj->Value = Gia_ManHashXor(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
        else pObj->Value = Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
    }
    Gia_ManHashStop(pNew);
    Gia_ManSetRegNum(pNew, Gia_ManRegNum(pGia));
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Packs a frame index and object ID into one unrolling key.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Abs2_Key( int Frame, int Id )
{
    return ((word)(unsigned)Frame << 32) | (unsigned)Id;
}

/**Function*************************************************************

  Synopsis    [Returns the frame index of an unrolling key.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Frame( word Key ) { return (int)(Key >> 32); }

/**Function*************************************************************

  Synopsis    [Returns the object ID of an unrolling key.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Id( word Key ) { return (int)(unsigned)Key; }

/**Function*************************************************************

  Synopsis    [Returns or allocates the SAT literal of an unrolled Gia literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_SatLit( Abs2_Man_t * p, int Lit )
{
    int Var;
    assert(Lit >= 0);
    if ( Lit < 2 ) return Lit ? 1 : -1;
    if ( !p->fCompactVars ) return (Lit & 1) ? -((Lit >> 1) + 1) : (Lit >> 1) + 1;
    Vec_IntFillExtra(p->vSatVars, (Lit >> 1) + 1, 0);
    Var = Vec_IntEntry(p->vSatVars, Lit >> 1);
    if ( !Var ) Vec_IntWriteEntry(p->vSatVars, Lit >> 1, Var = ++p->nSatVars);
    return (Lit & 1) ? -Var : Var;
}

/**Function*************************************************************

  Synopsis    [Latches a resource stop or external cancellation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Stop( void * pData )
{
    Abs2_Man_t * p = (Abs2_Man_t *)pData;
    if ( p->clkStop && Abc_Clock() >= p->clkStop ) p->fStopped = 1;
    if ( !p->fStopped && p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->pStopData) ) p->fStopped = 1;
    return p->fStopped || p->fError;
}

/**Function*************************************************************

  Synopsis    [Records a resumable yield requested by the caller.]

  Description [A worker result may interrupt SAT without retiring the BMC session. Do
  not use this callback inside encoding/refinement: these operations must
  finish before another client can add clauses to the shared unrolling.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Yield( Abs2_Man_t * p )
{
    if ( p->pPars->pFuncYield && p->pPars->pFuncYield(p->pPars->pStopData) )
        p->pPars->fYielded = 1;
    return p->pPars->fYielded;
}

/**Function*************************************************************

  Synopsis    [Checks resource stops and resumable yields during SAT solving.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_StopSat( void * pData )
{
    Abs2_Man_t * p = (Abs2_Man_t *)pData;
    return Abs2_Stop(p) || Abs2_Yield(p);
}

typedef struct Abs2_Order_t_
{
    float Cost;
    int Reg;
} Abs2_Order_t;

/**Function*************************************************************

  Synopsis    [Compares flop costs, breaking ties by register index.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_OrderCompare( const void * p0, const void * p1 )
{
    const Abs2_Order_t * a = (const Abs2_Order_t *)p0, * b = (const Abs2_Order_t *)p1;
    if ( a->Cost != b->Cost ) return a->Cost > b->Cost ? -1 : 1;
    return (a->Reg > b->Reg) - (a->Reg < b->Reg);
}

/**Function*************************************************************

  Synopsis    [Derives the requested order for ternary CBA generalization.]

  Description [Generalization is greedy: trying a flop's X assignment earlier gives it
  an earlier opportunity to stay abstract. Prefer expensive transitions for
  this experiment. Area flow distributes each fanin's cost over its fanouts;
  it is an estimate, not the exact number of distinct gates in a flop cone.
  The original register order breaks ties and remains the default.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Abs2_CreateCbaOrder( Abs2_Man_t * p )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vOrder;
    Abs2_Order_t * pOrder;
    float * pCosts;
    int i, Left, Right, Refs, nRegs = Gia_ManRegNum(p->pGia);
    if ( !p->pPars->nCbaOrder || nRegs < 2 ) return NULL;
    if ( p->pPars->nCbaOrder == 1 )
    {
        vOrder = Vec_IntStartNatural(nRegs);
        Vec_IntReverseOrder(vOrder);
        return vOrder;
    }
    pCosts = ABC_CALLOC(float, Gia_ManObjNum(p->pGia));
    Gia_ManForEachObj1(p->pGia, pObj, i)
    {
        float a, b = 0;
        if ( !(i & 4095) && Abs2_Stop(p) )
        {
            ABC_FREE(pCosts);
            return NULL;
        }
        if ( Gia_ObjIsCi(pObj) ) continue;
        Left = Gia_ObjFaninId0(pObj, i);
        a = pCosts[Left];
        if ( p->pPars->nCbaOrder == 3 )
        {
            Refs = Gia_ObjFanoutNum(p->pGia, Gia_ManObj(p->pGia, Left));
            a /= Refs ? Refs : 1;
        }
        if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) )
        {
            pCosts[i] = a;
            continue;
        }
        assert(Gia_ObjIsAnd(pObj));
        Right = Gia_ObjFaninId1(pObj, i);
        b = pCosts[Right];
        if ( p->pPars->nCbaOrder == 3 )
        {
            Refs = Gia_ObjFanoutNum(p->pGia, Gia_ManObj(p->pGia, Right));
            b /= Refs ? Refs : 1;
        }
        pCosts[i] = 1 + (p->pPars->nCbaOrder == 2 ? (a > b ? a : b) : a + b);
    }
    pOrder = ABC_ALLOC(Abs2_Order_t, nRegs);
    Gia_ManForEachRi(p->pGia, pObj, i)
        pOrder[i].Reg = i, pOrder[i].Cost = pCosts[Gia_ObjId(p->pGia, pObj)];
    ABC_FREE(pCosts);
    qsort(pOrder, nRegs, sizeof(*pOrder), Abs2_OrderCompare);
    vOrder = Vec_IntAlloc(nRegs);
    for ( i = 0; i < nRegs; ++i ) Vec_IntPush(vOrder, pOrder[i].Reg);
    ABC_FREE(pOrder);
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Adds a clause of up to three SAT literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_Clause( Abs2_Man_t * p, int a, int b, int c )
{
    ccadical_add( p->pSat, a );
    if ( b ) ccadical_add( p->pSat, b );
    if ( c ) ccadical_add( p->pSat, c );
    ccadical_add( p->pSat, 0 );
}

/**Function*************************************************************

  Synopsis    [Creates an unrolled input and initializes its encoding metadata.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Input( Abs2_Man_t * p )
{
    int Lit = Gia_ManAppendCi( p->pUnroll );
    if ( p->vRoInfo ) Vec_WrdPush(p->vRoInfo, ~(word)0);
    // Compact encoding allocates inputs when a clause uses them. Inputs
    // eliminated structurally can be completed with zero in a model.
    if ( !p->fCompactVars ) ccadical_resize(p->pSat, Gia_ManObjNum(p->pUnroll));
    if ( p->pPars->fUseCuts )
    {
        Vec_IntFillExtra(p->vEncoded, Gia_ManObjNum(p->pUnroll), 0);
        Vec_IntFillExtra(p->vKeep, Gia_ManObjNum(p->pUnroll), 0);
        Vec_IntWriteEntry(p->vEncoded, Lit >> 1, p->pPars->nCnfMode ? 3 : 1);
    }
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Caches the conditional consequences of an UNSAT prefix query.]

  Description [An UNSAT disjunction of bads under core C establishes C => !bad for
  every queried bad. Keep these conditional consequences in the solver so
  later frames can reuse the proved prefix. No flop assumption becomes a
  permanent unit: removing a flop must still weaken the abstraction.
  With a shared fresh guard g, encode C => g and g => !bad. Existentially
  eliminating g gives exactly the same consequences as the flat clauses.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_CacheProof( Abs2_Man_t * p )
{
    int Reg, Act, Lit, Guard = 0, i, j;
    Vec_IntClear(p->vCore);
    Vec_IntForEachEntry(p->vClasses, Reg, i)
        if ( Reg && (Act = Vec_IntEntry(p->vActs, i)) && ccadical_failed(p->pSat, Act) )
            Vec_IntPush(p->vCore, Act);
    // Consume the entire failed core before allocating or adding clauses.
    if ( p->pPars->nProofMode == 2 && Vec_IntSize(p->vCore) )
    {
        if ( Vec_IntSize(p->vCore) == 1 ) Guard = Vec_IntEntry(p->vCore, 0);
        else
        {
            Guard = Abs2_SatLit(p, Abs2_Input(p));
            Vec_IntForEachEntry(p->vCore, Act, i) ccadical_add(p->pSat, -Act);
            ccadical_add(p->pSat, Guard);
            ccadical_add(p->pSat, 0);
        }
    }
    Vec_IntForEachEntry(p->vBadLits, Lit, i)
    {
        if ( !(i & 63) && Abs2_Stop(p) ) return;
        if ( !Lit ) continue;
        if ( Guard ) ccadical_add(p->pSat, -Guard);
        else Vec_IntForEachEntry(p->vCore, Act, j) ccadical_add(p->pSat, -Act);
        ccadical_add(p->pSat, -Abs2_SatLit(p, Lit));
        ccadical_add(p->pSat, 0);
    }
}

/**Function*************************************************************

  Synopsis    [Simplifies the unrolling after retiring inactive flop guards.]

  Description [Run only after the failed core and temporary query have been consumed.
  Frozen active guards preserve their interfaces; CaDiCaL's extension stack
  restores a retired guard's clauses if CBA later makes that guard active.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_Simplify( Abs2_Man_t * p, int Depth )
{
    int Act, i, Result;
    int64_t Vars, Clauses;
    abctime clk;
    Vec_IntForEachEntry(p->vActs, Act, i)
        if ( Act && !Vec_IntEntry(p->vClasses, i) && Vec_IntEntry(p->vFrozen, i) )
        {
            ccadical_melt(p->pSat, Act);
            Vec_IntWriteEntry(p->vFrozen, i, 0);
            ++p->nInactiveActs;
        }
    if ( Depth % p->pPars->nSimplifyEvery || !p->nInactiveActs || Abs2_Stop(p) ) return;
    Vars = ccadical_active(p->pSat);
    Clauses = ccadical_irredundant(p->pSat);
    clk = Abc_Clock();
    Result = ccadical_simplify_rounds(p->pSat, 1);
    ++p->pPars->nSimplifies;
    p->pPars->timeSimplify += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
    if ( p->pPars->fVerbose )
        Abc_Print(1, "abs2 cleanup: depth=%d inactive=%d active=%lld->%lld clauses=%lld->%lld time=%.3f\n",
            Depth, p->nInactiveActs, (long long)Vars, (long long)ccadical_active(p->pSat),
            (long long)Clauses, (long long)ccadical_irredundant(p->pSat), (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    // The unconditioned transition formula is satisfiable with all guards
    // false. This call must never be interpreted as a property query.
    if ( Result == 20 )
    {
        p->fError = 1;
        Abc_Print(-1, "&abs: simplification found inconsistent transition CNF.\n");
    }
}

/**Function*************************************************************

  Synopsis    [Hashes an unrolled AND and prepares its SAT encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_And( Abs2_Man_t * p, int a, int b )
{
    int i, nOld = Gia_ManObjNum(p->pUnroll);
    int Lit = Gia_ManHashAnd( p->pUnroll, a, b );
    if ( p->pPars->fUseCuts )
    {
        Vec_IntFillExtra(p->vEncoded, Gia_ManObjNum(p->pUnroll), 0);
        Vec_IntFillExtra(p->vKeep, Gia_ManObjNum(p->pUnroll), 0);
        if ( p->vCnfRefs )
        {
            Vec_IntFillExtra(p->vCnfRefs, Gia_ManObjNum(p->pUnroll), 0);
            for ( i = nOld; i < Gia_ManObjNum(p->pUnroll); ++i )
            {
                Gia_Obj_t * pObj = Gia_ManObj(p->pUnroll, i);
                Vec_IntAddToEntry(p->vCnfRefs, Gia_ObjFaninId0(pObj, i), 1);
                Vec_IntAddToEntry(p->vCnfRefs, Gia_ObjFaninId1(pObj, i), 1);
            }
        }
        return Lit;
    }
    // Encode every new node, including any structural simplification nodes.
    for ( i = nOld; i < Gia_ManObjNum(p->pUnroll); ++i )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pUnroll, i);
        int x = Abs2_SatLit(p, Gia_ObjFaninLit0p(p->pUnroll, pObj));
        int y = Abs2_SatLit(p, Gia_ObjFaninLit1p(p->pUnroll, pObj));
        int z = Abs2_SatLit(p, i << 1);
        assert( Gia_ObjIsAnd(pObj) );
        Abs2_Clause( p, -x, -y, z );
        Abs2_Clause( p, x, -z, 0 );
        Abs2_Clause( p, y, -z, 0 );
    }
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Collects the leaves of a bounded positive AND cut.]

  Description [Collect a bounded AND cut. Stop at complemented edges, shared nodes,
  existing SAT definitions and mux roots. A later use of a previously
  absorbed node simply installs its definition; older clauses remain valid.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Conjunction( Abs2_Man_t * p, int Root )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pUnroll, Root);
    int Lit, Id, i, Prev = -2;
    Vec_IntClear(p->vLeaves);
    Vec_IntClear(p->vConjStack);
    Vec_IntPush(p->vConjStack, Gia_ObjFaninLit0p(p->pUnroll, pObj));
    Vec_IntPush(p->vConjStack, Gia_ObjFaninLit1p(p->pUnroll, pObj));
    while ( Vec_IntSize(p->vConjStack) )
    {
        Lit = Vec_IntPop(p->vConjStack);
        if ( !Lit ) return 0;
        if ( Lit == 1 ) continue;
        Id = Lit >> 1;
        pObj = Gia_ManObj(p->pUnroll, Id);
        if ( !(Lit & 1) && Gia_ObjIsAnd(pObj) && !Vec_IntEntry(p->vKeep, Id) &&
             !Vec_IntEntry(p->vEncoded, Id) && !Gia_ObjIsMuxType(pObj) &&
             Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vConjStack) < 63 )
        {
            Vec_IntPush(p->vConjStack, Gia_ObjFaninLit0p(p->pUnroll, pObj));
            Vec_IntPush(p->vConjStack, Gia_ObjFaninLit1p(p->pUnroll, pObj));
        }
        else Vec_IntPush(p->vLeaves, Lit);
    }
    Vec_IntUniqify(p->vLeaves);
    Vec_IntForEachEntry(p->vLeaves, Lit, i)
    {
        if ( Lit == (Prev ^ 1) ) return 0;
        Prev = Lit;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Looks up a leaf or internal truth table in a local cut.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Abs2_CutValue( int Id, int * pLeaves, int nLeaves, int * pNodes, int nNodes, word * pValues )
{
    int i;
    if ( !Id ) return 0;
    for ( i = 0; i < nLeaves; ++i )
        if ( pLeaves[i] == Id ) return pValues[i];
    for ( i = 0; i < nNodes; ++i )
        if ( pNodes[i] == Id ) return pValues[nLeaves+i];
    assert(0);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Derives a small truth-table CNF cover when it saves clauses.]

  Description [Expand a small cone across complemented edges, stopping at shared gates,
  existing definitions and muxes. A bounded local truth table existentially
  eliminates its internal gates. Positive AND cones keep the larger AND-cut
  encoding below; reject covers that do not beat binary Tseitin clause count.
  Both the traversal and scratch storage are bounded independently of AIG depth.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_TruthCut( Abs2_Man_t * p, int Root, int * pCover )
{
    static const word Truths[6] = {
        ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
        ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
        ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000)
    };
    int Nodes[32], Leaves[6], Next[8], BestLeaves[6];
    int nNodes = 1, nLeaves = 0, nNext, Best, nBest, Fan[2];
    int i, j, k, Id, nCubes, fMixed = 0;
    word Values[38];
    Gia_Obj_t * pObj = Gia_ManObj(p->pUnroll, Root);
    Nodes[0] = Root;
    Fan[0] = Gia_ObjFaninId0(pObj, Root);
    Fan[1] = Gia_ObjFaninId1(pObj, Root);
    for ( i = 0; i < 2; ++i )
        if ( Fan[i] && (!nLeaves || Leaves[0] != Fan[i]) ) Leaves[nLeaves++] = Fan[i];
    while ( nNodes < 32 )
    {
        Best = -1;
        nBest = 7;
        for ( i = 0; i < nLeaves; ++i )
        {
            Id = Leaves[i];
            pObj = Gia_ManObj(p->pUnroll, Id);
            if ( !Gia_ObjIsAnd(pObj) || Vec_IntEntry(p->vKeep, Id) ||
                 Vec_IntEntry(p->vEncoded, Id) || Gia_ObjIsMuxType(pObj) ) continue;
            nNext = 0;
            for ( j = 0; j < nLeaves; ++j )
                if ( j != i ) Next[nNext++] = Leaves[j];
            Fan[0] = Gia_ObjFaninId0(pObj, Id);
            Fan[1] = Gia_ObjFaninId1(pObj, Id);
            for ( j = 0; j < 2; ++j )
            {
                if ( !Fan[j] ) continue;
                for ( k = 0; k < nNodes; ++k ) if ( Nodes[k] == Fan[j] ) break;
                if ( k < nNodes ) continue;
                for ( k = 0; k < nNext; ++k ) if ( Next[k] == Fan[j] ) break;
                if ( k == nNext ) Next[nNext++] = Fan[j];
            }
            if ( nNext > p->pPars->nCutMax || nNext >= nBest ) continue;
            Best = i;
            nBest = nNext;
            memcpy(BestLeaves, Next, sizeof(int) * nNext);
        }
        if ( Best < 0 ) break;
        Nodes[nNodes++] = Leaves[Best];
        nLeaves = nBest;
        memcpy(Leaves, BestLeaves, sizeof(int) * nLeaves);
    }
    if ( nNodes == 1 ) return 0;
    // Node IDs give topological order; local insertion sorts have at most
    // 32 and 6 entries, respectively, and never modify Gia object scratch.
    for ( i = 1; i < nNodes; ++i )
    {
        Id = Nodes[i];
        for ( j = i; j && Nodes[j-1] > Id; --j ) Nodes[j] = Nodes[j-1];
        Nodes[j] = Id;
    }
    for ( i = 1; i < nLeaves; ++i )
    {
        Id = Leaves[i];
        for ( j = i; j && Leaves[j-1] > Id; --j ) Leaves[j] = Leaves[j-1];
        Leaves[j] = Id;
    }
    for ( i = 0; i < nLeaves; ++i ) Values[i] = Truths[i];
    for ( i = 0; i < nNodes; ++i )
    {
        word a, b;
        pObj = Gia_ManObj(p->pUnroll, Nodes[i]);
        Fan[0] = Gia_ObjFaninId0(pObj, Nodes[i]);
        Fan[1] = Gia_ObjFaninId1(pObj, Nodes[i]);
        for ( j = 0; j < i; ++j )
            if ( (Gia_ObjFaninC0(pObj) && Nodes[j] == Fan[0]) ||
                 (Gia_ObjFaninC1(pObj) && Nodes[j] == Fan[1]) ) fMixed = 1;
        a = Abs2_CutValue(Fan[0], Leaves, nLeaves, Nodes, i, Values);
        b = Abs2_CutValue(Fan[1], Leaves, nLeaves, Nodes, i, Values);
        Values[nLeaves+i] = (Gia_ObjFaninC0(pObj) ? ~a : a) & (Gia_ObjFaninC1(pObj) ? ~b : b);
    }
    if ( !fMixed ) return 0;
    nCubes = Abc_Tt6Cnf(Values[nLeaves+nNodes-1], nLeaves, pCover);
    if ( nCubes >= 3 * nNodes ) return 0;
    Vec_IntClear(p->vLeaves);
    for ( i = 0; i < nLeaves; ++i ) Vec_IntPush(p->vLeaves, Leaves[i] << 1);
    return nCubes;
}

/**Function*************************************************************

  Synopsis    [Encodes the complete definition of a requested unrolled cone.]

  Description [Iterative clausification follows ZZ's mux / k-input AND encoding. SAT
  Internal nodes need no clauses until an output or guarded transition
  actually uses their value. Compact numbering avoids reserving SAT variables
  for gates absorbed into a mux or a multi-input AND clause.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_EncodeFull( Abs2_Man_t * p, int Lit )
{
    int Id, Leaf, i, IsMux, z, c = 0, t = 0, e = 0;
    int Cover[64], nCubes, Cube, j, k, Field, Var;
    unsigned Visits = 0;
    if ( !p->pPars->fUseCuts ) return 1;
    if ( !p->fCompactVars ) ccadical_resize(p->pSat, Gia_ManObjNum(p->pUnroll));
    Vec_IntClear(p->vCnfStack);
    Vec_IntPush(p->vCnfStack, Lit >> 1);
    while ( Vec_IntSize(p->vCnfStack) )
    {
        Gia_Obj_t * pObj;
        Id = Vec_IntEntryLast(p->vCnfStack);
        if ( !(++Visits & 1023) && Abs2_Stop(p) ) return 0;
        if ( Vec_IntEntry(p->vEncoded, Id) )
        {
            Vec_IntPop(p->vCnfStack);
            continue;
        }
        pObj = Gia_ManObj(p->pUnroll, Id);
        assert(Gia_ObjIsAnd(pObj));
        IsMux = Gia_ObjIsMuxType(pObj);
        nCubes = p->pPars->nCutMax && !IsMux ? Abs2_TruthCut(p, Id, Cover) : 0;
        if ( !nCubes && IsMux )
        {
            c = Gia_ObjRecognizeMuxLits(p->pUnroll, pObj, &t, &e);
            Vec_IntClear(p->vLeaves);
            Vec_IntPush(p->vLeaves, c);
            Vec_IntPush(p->vLeaves, t);
            Vec_IntPush(p->vLeaves, e);
        }
        else if ( !nCubes && !Abs2_Conjunction(p, Id) )
        {
            Abs2_Clause(p, -Abs2_SatLit(p, Id << 1), 0, 0);
            Vec_IntWriteEntry(p->vEncoded, Id, 1);
            Vec_IntPop(p->vCnfStack);
            continue;
        }
        Vec_IntForEachEntry(p->vLeaves, Leaf, i)
            if ( !Vec_IntEntry(p->vEncoded, Leaf >> 1) ) break;
        if ( i < Vec_IntSize(p->vLeaves) )
        {
            Vec_IntPush(p->vCnfStack, Leaf >> 1);
            continue;
        }
        z = Abs2_SatLit(p, Id << 1);
        if ( nCubes )
        {
            ++p->pPars->nTruthCuts;
            for ( j = 0; j < nCubes; ++j )
            {
                Cube = Cover[j];
                for ( k = 0; k <= Vec_IntSize(p->vLeaves); ++k, Cube >>= 2 )
                {
                    Field = Cube & 3;
                    if ( !Field ) continue;
                    assert(Field != 3);
                    Var = k == Vec_IntSize(p->vLeaves) ? z : Abs2_SatLit(p, Vec_IntEntry(p->vLeaves, k));
                    ccadical_add(p->pSat, Field == 1 ? Var : -Var);
                }
                ccadical_add(p->pSat, 0);
            }
        }
        else if ( IsMux )
        {
            c = Abs2_SatLit(p, c); t = Abs2_SatLit(p, t); e = Abs2_SatLit(p, e);
            Abs2_Clause(p, -c, -t, z);
            Abs2_Clause(p, -c, t, -z);
            Abs2_Clause(p, c, -e, z);
            Abs2_Clause(p, c, e, -z);
            if ( p->pPars->fMuxProp )
            {
                // When both data inputs agree, propagate z without first
                // deciding the selector. These are resolvents of the four
                // defining clauses and do not change the represented mux.
                Abs2_Clause(p, -t, -e, z);
                Abs2_Clause(p, t, e, -z);
            }
        }
        else
        {
            Vec_IntForEachEntry(p->vLeaves, Leaf, i)
                Abs2_Clause(p, Abs2_SatLit(p, Leaf), -z, 0);
            Vec_IntForEachEntry(p->vLeaves, Leaf, i)
                ccadical_add(p->pSat, -Abs2_SatLit(p, Leaf));
            ccadical_add(p->pSat, z);
            ccadical_add(p->pSat, 0);
        }
        Vec_IntWriteEntry(p->vEncoded, Id, 1);
        Vec_IntPop(p->vCnfStack);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Allocates the literal and link maps of an unrolling frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abs2_Frame_t * Abs2_GetFrame( Abs2_Man_t * p, int Frame )
{
    while ( Vec_PtrSize(p->vFrames) <= Frame )
    {
        Abs2_Frame_t * pNew = ABC_CALLOC( Abs2_Frame_t, 1 );
        pNew->pLits = ABC_ALLOC( int, Gia_ManObjNum(p->pGia) );
        memset( pNew->pLits, 0xff, sizeof(int) * (size_t)Gia_ManObjNum(p->pGia) );
        pNew->pLits[0] = 0;
        pNew->pLinked = ABC_CALLOC( unsigned char, Gia_ManRegNum(p->pGia) );
        Vec_PtrPush( p->vFrames, pNew );
    }
    return (Abs2_Frame_t *)Vec_PtrEntry(p->vFrames, Frame);
}

/**Function*************************************************************

  Synopsis    [Maps a polarity demand through a complemented literal.]

  Description [Direction bits are relative to the positive variable: 1 encodes z => f,
  2 encodes !z => !f. An occurrence of a complemented literal swaps them.
  Abstract flop outputs remember their demands even while their guard is
  disabled. On reactivation those demands must reach the predecessor again.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_PolMask( int Lit, int Mask )
{
    return Lit & 1 ? ((Mask << 1) & 2) | (Mask >> 1) : Mask;
}

/**Function*************************************************************

  Synopsis    [Returns the polarities that still need CNF definitions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_PolMissing( Abs2_Man_t * p, int Lit, int Mask )
{
    int Id = Lit >> 1, Done = Vec_IntEntry(p->vEncoded, Id);
    Gia_Obj_t * pObj = Gia_ManObj(p->pUnroll, Id);
    if ( p->vRoInfo && Gia_ObjIsCi(pObj) )
    {
        word Key = Vec_WrdEntry(p->vRoInfo, Gia_ObjCioId(pObj));
        if ( Key != ~(word)0 && Vec_IntEntry(p->vClasses, Abs2_Id(Key)) )
            Done = Abs2_GetFrame(p, Abs2_Frame(Key))->pLinked[Abs2_Id(Key)];
    }
    return Abs2_PolMask(Lit, Mask) & ~Done;
}

/**Function*************************************************************

  Synopsis    [Encodes a cone under the requested polarity demands.]

  Description [Demand-driven clausification is iterative through gates AND time frames.
  Each emitted clause requests the polarity of each leaf literal it uses.
  Consequently an asserted bad remains true when internal SAT values are
  replaced by forward simulation of the concrete transition relation.
  Both directions are added when demanded; every original execution always
  satisfies the clauses, including a partially encoded guarded flop link.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_EncodePolar( Abs2_Man_t * p, int Lit, int Mask )
{
    unsigned Visits = 0;
    int Id, Need, Leaf, i, j, k, z, c = 0, t = 0, e = 0;
    int IsMux, Cover[64], Needs[64], nCubes, Cube, Field, Var, Child;
    if ( !p->fCompactVars ) ccadical_resize(p->pSat, Gia_ManObjNum(p->pUnroll));
    Vec_WrdClear(p->vPolStack);
    Vec_WrdPush(p->vPolStack, Abs2_Key(Abs2_PolMask(Lit, Mask), Lit >> 1));
    while ( Vec_WrdSize(p->vPolStack) )
    {
        word Entry = Vec_WrdEntryLast(p->vPolStack);
        Gia_Obj_t * pObj;
        if ( !(++Visits & 1023) && Abs2_Stop(p) ) return 0;
        Id = Abs2_Id(Entry);
        Need = Abs2_PolMissing(p, Id << 1, Abs2_Frame(Entry));
        if ( !Need )
        {
            Vec_WrdPop(p->vPolStack);
            continue;
        }
        pObj = Gia_ManObj(p->pUnroll, Id);
        if ( Gia_ObjIsCi(pObj) )
        {
            word Key = Vec_WrdEntry(p->vRoInfo, Gia_ObjCioId(pObj));
            int Frame = Abs2_Frame(Key), Reg = Abs2_Id(Key);
            assert(Key != ~(word)0);
            Vec_IntWriteEntry(p->vEncoded, Id, Vec_IntEntry(p->vEncoded, Id) | Need);
            if ( Vec_IntEntry(p->vClasses, Reg) )
            {
                Abs2_Frame_t * pFrame = Abs2_GetFrame(p, Frame);
                int a = Vec_IntEntry(p->vActs, Reg);
                int d = Frame ? Abs2_GetFrame(p, Frame-1)->pLits[Gia_ObjId(p->pGia, Gia_ManRi(p->pGia, Reg))] : 0;
                assert((pFrame->pLinked[Reg] & 4) && a && d >= 0);
                Child = Abs2_PolMissing(p, d, Need);
                if ( Child )
                {
                    Vec_WrdPush(p->vPolStack, Abs2_Key(Child, d >> 1));
                    continue;
                }
                z = Abs2_SatLit(p, Id << 1);
                d = Abs2_SatLit(p, d);
                if ( Need & 1 ) Abs2_Clause(p, -a, -z, d);
                if ( Need & 2 ) Abs2_Clause(p, -a, z, -d);
                pFrame->pLinked[Reg] |= Need;
            }
            Vec_WrdPop(p->vPolStack);
            continue;
        }
        assert(Gia_ObjIsAnd(pObj));
        IsMux = Gia_ObjIsMuxType(pObj);
        nCubes = p->pPars->nCutMax && !IsMux ? Abs2_TruthCut(p, Id, Cover) : 0;
        memset(Needs, 0, sizeof(Needs));
        if ( nCubes )
        {
            for ( j = 0; j < nCubes; ++j )
            {
                Field = (Cover[j] >> (2 * Vec_IntSize(p->vLeaves))) & 3;
                assert(Field == 1 || Field == 2);
                if ( !(Need & (Field == 2 ? 1 : 2)) ) continue;
                for ( k = 0, Cube = Cover[j]; k < Vec_IntSize(p->vLeaves); ++k, Cube >>= 2 )
                    Needs[k] |= Cube & 3;
            }
        }
        else if ( IsMux )
        {
            c = Gia_ObjRecognizeMuxLits(p->pUnroll, pObj, &t, &e);
            Vec_IntClear(p->vLeaves);
            Vec_IntPush(p->vLeaves, c);
            Vec_IntPush(p->vLeaves, t);
            Vec_IntPush(p->vLeaves, e);
            Needs[0] = 3;
            Needs[1] = Needs[2] = Need;
        }
        else if ( !Abs2_Conjunction(p, Id) )
        {
            if ( Need & 1 ) Abs2_Clause(p, -Abs2_SatLit(p, Id << 1), 0, 0);
            Vec_IntWriteEntry(p->vEncoded, Id, Vec_IntEntry(p->vEncoded, Id) | Need);
            Vec_WrdPop(p->vPolStack);
            continue;
        }
        else
            for ( i = 0; i < Vec_IntSize(p->vLeaves); ++i ) Needs[i] = Need;
        Vec_IntForEachEntry(p->vLeaves, Leaf, i)
            if ( (Child = Abs2_PolMissing(p, Leaf, Needs[i])) ) break;
        if ( i < Vec_IntSize(p->vLeaves) )
        {
            Vec_WrdPush(p->vPolStack, Abs2_Key(Child, Leaf >> 1));
            continue;
        }
        z = Abs2_SatLit(p, Id << 1);
        if ( nCubes )
        {
            ++p->pPars->nTruthCuts;
            for ( j = 0; j < nCubes; ++j )
            {
                Field = (Cover[j] >> (2 * Vec_IntSize(p->vLeaves))) & 3;
                if ( !(Need & (Field == 2 ? 1 : 2)) ) continue;
                for ( k = 0, Cube = Cover[j]; k <= Vec_IntSize(p->vLeaves); ++k, Cube >>= 2 )
                {
                    Field = Cube & 3;
                    if ( !Field ) continue;
                    assert(Field != 3);
                    Var = k == Vec_IntSize(p->vLeaves) ? z : Abs2_SatLit(p, Vec_IntEntry(p->vLeaves, k));
                    ccadical_add(p->pSat, Field == 1 ? Var : -Var);
                }
                ccadical_add(p->pSat, 0);
            }
        }
        else if ( IsMux )
        {
            c = Abs2_SatLit(p, c); t = Abs2_SatLit(p, t); e = Abs2_SatLit(p, e);
            if ( Need & 1 )
            {
                Abs2_Clause(p, -c, t, -z);
                Abs2_Clause(p, c, e, -z);
                if ( p->pPars->fMuxProp ) Abs2_Clause(p, t, e, -z);
            }
            if ( Need & 2 )
            {
                Abs2_Clause(p, -c, -t, z);
                Abs2_Clause(p, c, -e, z);
                if ( p->pPars->fMuxProp ) Abs2_Clause(p, -t, -e, z);
            }
        }
        else
        {
            if ( Need & 1 )
                Vec_IntForEachEntry(p->vLeaves, Leaf, i)
                    Abs2_Clause(p, Abs2_SatLit(p, Leaf), -z, 0);
            if ( Need & 2 )
            {
                Vec_IntForEachEntry(p->vLeaves, Leaf, i) ccadical_add(p->pSat, -Abs2_SatLit(p, Leaf));
                ccadical_add(p->pSat, z);
                ccadical_add(p->pSat, 0);
            }
        }
        Vec_IntWriteEntry(p->vEncoded, Id, Vec_IntEntry(p->vEncoded, Id) | Need);
        Vec_WrdPop(p->vPolStack);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Encodes a cone using bounded local resolution cuts.]

  Description [Keep each bounded root definition while encoding its leaves. Rebuilding it
  after every leaf would repeat resolution/redundancy work along deep cones.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_EncodeResolve( Abs2_Man_t * p, int Lit )
{
    int Id, Depth, Position, Leaf, i, Added, Saved, fDescend;
    Vec_Int_t * vDef;
    if ( !p->fCompactVars ) ccadical_resize(p->pSat, Gia_ManObjNum(p->pUnroll));
    Vec_IntClear(p->vCnfStack);
    Vec_IntClear(p->vResolvePos);
    Vec_IntPush(p->vCnfStack, Lit >> 1);
    Vec_IntPush(p->vResolvePos, -1);
    while ( Vec_IntSize(p->vCnfStack) )
    {
        if ( Abs2_Stop(p) ) return 0;
        Depth = Vec_IntSize(p->vCnfStack) - 1;
        Id = Vec_IntEntryLast(p->vCnfStack);
        if ( Vec_IntEntry(p->vEncoded, Id) )
        {
            Vec_IntPop(p->vCnfStack);
            Vec_IntPop(p->vResolvePos);
            continue;
        }
        while ( Vec_WecSize(p->vResolveDefs) <= Depth ) Vec_WecPushLevel(p->vResolveDefs);
        vDef = Vec_WecEntry(p->vResolveDefs, Depth);
        Position = Vec_IntEntryLast(p->vResolvePos);
        if ( Position < 0 )
        {
            abctime clk = Abc_Clock();
            Added = Abs2_CnfResolve(p->pUnroll, Id, p->vEncoded, p->vKeep,
                p->pPars->nResolveMode, p->pPars->fMuxProp, vDef, &Saved, Abs2_Stop, p);
            p->pPars->timeResolve += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
            ++p->pPars->nResolveCalls;
            if ( Added < 0 ) return 0;
            p->pPars->nResolveCuts += Added != 0;
            p->pPars->nResolvedNodes += Added;
            p->pPars->nMinimizedCuts += Saved != 0;
            p->pPars->nClausesSaved += Saved;
            Position = 0;
        }
        fDescend = 0;
        while ( Position < Vec_IntSize(vDef) )
        {
            Leaf = Vec_IntEntry(vDef, Position++);
            if ( Leaf && (Leaf >> 1) != Id && !Vec_IntEntry(p->vEncoded, Leaf >> 1) )
            {
                fDescend = 1;
                break;
            }
        }
        Vec_IntWriteEntry(p->vResolvePos, Depth, Position);
        if ( fDescend )
        {
            Vec_IntPush(p->vCnfStack, Leaf >> 1);
            Vec_IntPush(p->vResolvePos, -1);
            continue;
        }
        Vec_IntForEachEntry(vDef, Leaf, i)
            ccadical_add(p->pSat, Leaf ? Abs2_SatLit(p, Leaf) : 0);
        Vec_IntWriteEntry(p->vEncoded, Id, 1);
        Vec_IntPop(p->vCnfStack);
        Vec_IntPop(p->vResolvePos);
    }
    return 1;
}
#define ABS2_CNF_MEMOS 4096

/**Function*************************************************************

  Synopsis    [Caches a definition in the bounded substitution table.]

  Description [Eviction changes construction work only. Each stored definition is exact,
  and all of its boundary variables already have permanent SAT definitions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_MemoStore( Abs2_Man_t * p, int Id, Vec_Int_t * vDef, int Count )
{
    int Slot, Old;
    if ( Vec_IntEntry(p->vMemoMap, Id) ) return;
    Slot = p->iMemoNext;
    if ( ++p->iMemoNext == ABS2_CNF_MEMOS ) p->iMemoNext = 0;
    Old = Vec_IntEntry(p->vMemoIds, Slot);
    if ( Old ) Vec_IntWriteEntry(p->vMemoMap, Old, 0);
    Vec_IntWriteEntry(p->vMemoIds, Slot, Id);
    Vec_IntWriteEntry(p->vMemoMerged, Slot, Count);
    Vec_IntWriteEntry(p->vMemoMap, Id, Slot+1);
    Vec_IntClear(Vec_WecEntry(p->vMemoDefs, Slot));
    Vec_IntAppend(Vec_WecEntry(p->vMemoDefs, Slot), vDef);
}

/**Function*************************************************************

  Synopsis    [Releases a cached definition when it is no longer needed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_MemoDrop( Abs2_Man_t * p, int Id )
{
    int Slot = Vec_IntEntry(p->vMemoMap, Id);
    if ( !Slot ) return;
    Vec_IntWriteEntry(p->vMemoMap, Id, 0);
    Vec_IntWriteEntry(p->vMemoIds, Slot-1, 0);
    Vec_IntClear(Vec_WecEntry(p->vMemoDefs, Slot-1));
}

/**Function*************************************************************

  Synopsis    [Encodes a cone by iterative bottom-up definition substitution.]

  Description [ZZ-style bottom-up clausification, expressed as an explicit stack. A child
  is either substituted into its parent or emitted exactly once. Shared
  definitions may be reused before they acquire their own SAT variable.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_EncodeBottom( Abs2_Man_t * p, int Lit )
{
    int Depth, Id, Position, Leaf, i, Slot, Count, Merged;
    Vec_Int_t * vDef;
    if ( !p->fCompactVars ) ccadical_resize(p->pSat, Gia_ManObjNum(p->pUnroll));
    Vec_IntFillExtra(p->vMemoMap, Gia_ManObjNum(p->pUnroll), 0);
    Vec_IntFillExtra(p->vCnfRefs, Gia_ManObjNum(p->pUnroll), 0);
    Vec_IntClear(p->vCnfStack);
    Vec_IntClear(p->vResolvePos);
    Vec_IntClear(p->vResolveMerged);
    Vec_IntPush(p->vCnfStack, Lit >> 1);
    Vec_IntPush(p->vResolvePos, -1);
    Vec_IntPush(p->vResolveMerged, 0);
    while ( Vec_IntSize(p->vCnfStack) )
    {
        if ( Abs2_Stop(p) ) return 0;
        Depth = Vec_IntSize(p->vCnfStack) - 1;
        Id = Vec_IntEntryLast(p->vCnfStack);
        if ( Vec_IntEntry(p->vEncoded, Id) )
        {
            Vec_IntPop(p->vCnfStack);
            Vec_IntPop(p->vResolvePos);
            Vec_IntPop(p->vResolveMerged);
            continue;
        }
        while ( Vec_WecSize(p->vResolveDefs) <= Depth ) Vec_WecPushLevel(p->vResolveDefs);
        vDef = Vec_WecEntry(p->vResolveDefs, Depth);
        Position = Vec_IntEntryLast(p->vResolvePos);
        if ( Position < 0 )
        {
            abctime clk = Abc_Clock();
            Slot = Vec_IntEntry(p->vMemoMap, Id);
            if ( Slot )
            {
                Vec_IntClear(vDef);
                Vec_IntAppend(vDef, Vec_WecEntry(p->vMemoDefs, Slot-1));
                Vec_IntWriteEntry(p->vResolveMerged, Depth, Vec_IntEntry(p->vMemoMerged, Slot-1));
                ++p->pPars->nCnfMemoHits;
            }
            else Abs2_CnfStart(p->pUnroll, Id, p->pPars->fMuxProp, vDef);
            p->pPars->timeResolve += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
            ++p->pPars->nResolveCalls;
            Position = 0;
        }
        Leaf = 0;
        while ( Position < Vec_IntSize(vDef) )
        {
            int Next = Vec_IntEntry(vDef, Position++);
            if ( Next && (Next >> 1) != Id && !Vec_IntEntry(p->vEncoded, Next >> 1) )
            {
                Leaf = Next;
                break;
            }
        }
        Vec_IntWriteEntry(p->vResolvePos, Depth, Position);
        if ( Leaf )
        {
            Vec_IntPush(p->vCnfStack, Leaf >> 1);
            Vec_IntPush(p->vResolvePos, -1);
            Vec_IntPush(p->vResolveMerged, 0);
            continue;
        }
        Count = Vec_IntEntryLast(p->vResolveMerged);
        Merged = 0;
        if ( Depth && Vec_IntEntry(p->vCnfRefs, Id) < 4 )
        {
            abctime clk = Abc_Clock();
            Merged = Abs2_CnfCombine(Vec_WecEntry(p->vResolveDefs, Depth-1), vDef, Id,
                Vec_IntEntry(p->vKeep, Id), p->vCombine, Abs2_Stop, p);
            p->pPars->timeResolve += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
            if ( Merged < 0 ) return 0;
            if ( Merged )
            {
                if ( Vec_IntEntry(p->vKeep, Id) ) Abs2_MemoStore(p, Id, vDef, Count);
                Vec_IntWriteEntry(p->vResolvePos, Depth-1, 0);
                Vec_IntWriteEntry(p->vResolveMerged, Depth-1, 1);
                ++p->pPars->nResolvedNodes;
            }
        }
        if ( !Merged )
        {
            Vec_IntForEachEntry(vDef, Leaf, i)
                ccadical_add(p->pSat, Leaf ? Abs2_SatLit(p, Leaf) : 0);
            Vec_IntWriteEntry(p->vEncoded, Id, 1);
            Abs2_MemoDrop(p, Id);
            p->pPars->nResolveCuts += Count != 0;
        }
        Vec_IntPop(p->vCnfStack);
        Vec_IntPop(p->vResolvePos);
        Vec_IntPop(p->vResolveMerged);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Dispatches to the selected unrolled-cone encoder.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Encode( Abs2_Man_t * p, int Lit, int Mask )
{
    if ( p->pPars->nResolveMode == 5 ) return Abs2_EncodeBottom(p, Lit);
    if ( p->pPars->nResolveMode ) return Abs2_EncodeResolve(p, Lit);
    return p->pPars->nCnfMode ? Abs2_EncodePolar(p, Lit, Mask) : Abs2_EncodeFull(p, Lit);
}

/**Function*************************************************************

  Synopsis    [Lazily unrolls an object and its required predecessors.]

  Description [The explicit work stack avoids recursion across either gate depth or time.
  A flop gets a free output variable before its guarded predecessor is added.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Insert( Abs2_Man_t * p, int Frame, int Id )
{
    unsigned nVisits = 0;
    Vec_WrdClear( p->vStack );
    Vec_WrdPush( p->vStack, Abs2_Key(Frame, Id) );
    while ( Vec_WrdSize(p->vStack) )
    {
        word Key = Vec_WrdEntryLast(p->vStack);
        int f = Abs2_Frame(Key), i = Abs2_Id(Key), Reg = -1;
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, i);
        Abs2_Frame_t * pFrame = Abs2_GetFrame(p, f);
        if ( !(++nVisits & 1023) && Abs2_Stop(p) ) return -1;
        if ( Gia_ObjIsCi(pObj) )
            Reg = Gia_ObjCioId(pObj) - Gia_ManPiNum(p->pGia);
        if ( pFrame->pLits[i] >= 0 && (Reg < 0 ||
             !Vec_IntEntry(p->vClasses, Reg) || pFrame->pLinked[Reg]) )
        {
            if ( p->vPolPending && Reg >= 0 && Vec_IntEntry(p->vClasses, Reg) &&
                 Vec_IntEntry(p->vEncoded, pFrame->pLits[i] >> 1) )
                Vec_IntPush(p->vPolPending, pFrame->pLits[i]);
            Vec_WrdPop( p->vStack );
            continue;
        }
        if ( Gia_ObjIsCi(pObj) )
        {
            if ( pFrame->pLits[i] < 0 )
            {
                pFrame->pLits[i] = Abs2_Input(p);
                if ( p->vRoInfo && Reg >= 0 )
                {
                    Vec_WrdWriteEntry(p->vRoInfo, Gia_ManCiNum(p->pUnroll)-1, Abs2_Key(f, Reg));
                    Vec_IntWriteEntry(p->vEncoded, pFrame->pLits[i] >> 1, 0);
                }
            }
            if ( Reg >= 0 && Vec_IntEntry(p->vClasses, Reg) )
            {
                int a, d, q = p->vPolPending ? 0 : Abs2_SatLit(p, pFrame->pLits[i]);
                if ( f && Abs2_GetFrame(p, f-1)->pLits[Gia_ObjId(p->pGia, Gia_ManRi(p->pGia, Reg))] < 0 )
                {
                    Vec_WrdPush( p->vStack, Abs2_Key(f-1, Gia_ObjId(p->pGia, Gia_ManRi(p->pGia, Reg))) );
                    continue;
                }
                a = Vec_IntEntry(p->vActs, Reg);
                if ( !a )
                {
                    a = Abs2_SatLit(p, Abs2_Input(p));
                    Vec_IntWriteEntry( p->vActs, Reg, a );
                    ccadical_freeze( p->pSat, a );
                    Vec_IntWriteEntry(p->vFrozen, Reg, 1);
                    if ( p->pPars->nActMode == 1 ) ccadical_phase(p->pSat, -a);
                }
                d = f ? Abs2_GetFrame(p, f-1)->pLits[Gia_ObjId(p->pGia, Gia_ManRi(p->pGia, Reg))] : 0;
                if ( p->vPolPending )
                {
                    pFrame->pLinked[Reg] = 4;
                    if ( Vec_IntEntry(p->vEncoded, pFrame->pLits[i] >> 1) )
                        Vec_IntPush(p->vPolPending, pFrame->pLits[i]);
                }
                else
                {
                    if ( !Abs2_Encode(p, d, 3) ) return -1;
                    d = Abs2_SatLit(p, d);
                    Abs2_Clause( p, -a, -d, q );
                    Abs2_Clause( p, -a, d, -q );
                    pFrame->pLinked[Reg] = 1;
                }
            }
        }
        else
        {
            int Left = Gia_ObjFaninId0(pObj, i), Right = -1;
            int a, b;
            if ( Gia_ObjIsAnd(pObj) && !Gia_ObjIsBuf(pObj) ) Right = Gia_ObjFaninId1(pObj, i);
            if ( pFrame->pLits[Left] < 0 )
            {
                Vec_WrdPush( p->vStack, Abs2_Key(f, Left) );
                continue;
            }
            if ( Right >= 0 && pFrame->pLits[Right] < 0 )
            {
                Vec_WrdPush( p->vStack, Abs2_Key(f, Right) );
                continue;
            }
            a = pFrame->pLits[Left] ^ Gia_ObjFaninC0(pObj);
            b = Right >= 0 ? pFrame->pLits[Right] ^ Gia_ObjFaninC1(pObj) : 0;
            pFrame->pLits[i] = Right >= 0 ? Abs2_And(p, a, b) : a;
        }
        if ( p->pPars->fUseCuts && pFrame->pLits[i] >= 2 && Gia_ObjFanoutNum(p->pGia, pObj) > 1 )
            Vec_IntWriteEntry(p->vKeep, pFrame->pLits[i] >> 1, 1);
        Vec_WrdPop( p->vStack );
    }
    return Abs2_GetFrame(p, Frame)->pLits[Id];
}

/**Function*************************************************************

  Synopsis    [Reads a completed SAT model for an original object and frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Model( Abs2_Man_t * p, int Frame, int Id )
{
    int Lit = Abs2_GetFrame(p, Frame)->pLits[Id];
    int SatLit;
    if ( Lit < 0 ) return 0;
    // Looking up a model must never allocate a new SAT variable.
    if ( Lit >= 2 && p->fCompactVars &&
         ((Lit >> 1) >= Vec_IntSize(p->vSatVars) || !Vec_IntEntry(p->vSatVars, Lit >> 1)) )
        return Lit & 1; // Complete the positive variable with zero, then apply polarity.
    SatLit = Abs2_SatLit(p, Lit);
    return ccadical_val(p->pSat, SatLit) == SatLit;
}

/**Function*************************************************************

  Synopsis    [Complements a ternary value while preserving the unknown value.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned char Abs2_Not( unsigned char Value, int fCompl )
{
    return Value == 2 ? 2 : Value ^ fCompl;
}

/**Function*************************************************************

  Synopsis    [Evaluates one original object under a ternary assignment.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned char Abs2_Eval( Gia_Obj_t * pObj, int Id, unsigned char * pValues )
{
    unsigned char a = Abs2_Not(pValues[Gia_ObjFaninId0(pObj, Id)], Gia_ObjFaninC0(pObj)), b;
    if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) ) return a;
    b = Abs2_Not(pValues[Gia_ObjFaninId1(pObj, Id)], Gia_ObjFaninC1(pObj));
    return a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
}

/**Function*************************************************************

  Synopsis    [Returns the ternary values associated with a frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned char * Abs2_Values( Abs2_Man_t * p, int Frame )
{
    return (unsigned char *)Vec_PtrEntry(p->vValues, Frame);
}

/**Function*************************************************************

  Synopsis    [Simulates the SAT trace with concrete initial states.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Simulate( Abs2_Man_t * p, int Depth )
{
    int f, i;
    Gia_Obj_t * pObj;
    while ( Vec_PtrSize(p->vValues) <= Depth )
        Vec_PtrPush( p->vValues, ABC_CALLOC(unsigned char, Gia_ManObjNum(p->pGia)) );
    for ( f = 0; f <= Depth; ++f )
    {
        unsigned char * pValues = Abs2_Values(p, f);
        Abs2_Frame_t * pFrame = Abs2_GetFrame(p, f);
        if ( Abs2_Stop(p) ) return 0;
        pValues[0] = 0;
        Gia_ManForEachPi( p->pGia, pObj, i )
            if ( pFrame->pLits[Gia_ObjId(p->pGia, pObj)] >= 0 )
                pValues[Gia_ObjId(p->pGia, pObj)] = Abs2_Model(p, f, Gia_ObjId(p->pGia, pObj));
        Gia_ManForEachRo( p->pGia, pObj, i )
            if ( pFrame->pLits[Gia_ObjId(p->pGia, pObj)] >= 0 )
                pValues[Gia_ObjId(p->pGia, pObj)] = Vec_IntEntry(p->vClasses, i) ?
                    (f ? Abs2_Values(p, f-1)[Gia_ObjId(p->pGia, Gia_ManRi(p->pGia, i))] : 0) :
                    Abs2_Model(p, f, Gia_ObjId(p->pGia, pObj));
        Gia_ManForEachAnd( p->pGia, pObj, i )
        {
            if ( !(i & 4095) && Abs2_Stop(p) ) return 0;
            if ( pFrame->pLits[i] >= 0 ) pValues[i] = Abs2_Eval(pObj, i, pValues);
        }
        Gia_ManForEachCo( p->pGia, pObj, i )
            if ( pFrame->pLits[Gia_ObjId(p->pGia, pObj)] >= 0 )
                pValues[Gia_ObjId(p->pGia, pObj)] = Abs2_Eval(pObj, Gia_ObjId(p->pGia, pObj), pValues);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Marks a simulated value unknown and records it for undo.]

  Description [Values only move from 0/1 to X. Each changed object is therefore queued
  at most once per trial; the undo log restores only this trial's changes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_SetX( Abs2_Man_t * p, int Frame, int Id )
{
    unsigned char * pValues = Abs2_Values(p, Frame);
    word Key = Abs2_Key(Frame, Id);
    if ( pValues[Id] == 2 ) return 0;
    Vec_WrdPush( p->vUndo, (Key << 1) | pValues[Id] );
    pValues[Id] = 2;
    Vec_WrdPush( p->vQueue, Key );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Restores the values changed by a trial ternary propagation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_Undo( Abs2_Man_t * p )
{
    while ( Vec_WrdSize(p->vUndo) )
    {
        word Entry = Vec_WrdPop(p->vUndo), Key = Entry >> 1;
        Abs2_Values(p, Abs2_Frame(Key))[Abs2_Id(Key)] = Entry & 1;
    }
}

/**Function*************************************************************

  Synopsis    [Tests whether an unknown assignment preserves the failing output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_PropagateX( Abs2_Man_t * p, int Frame, int Id, int Depth, int BadId )
{
    int Head = 0;
    // The encoded cone is closed under combinational fanins and the
    // predecessors of concrete flops. Unencoded objects cannot influence
    // any queried bad signal, so they need no simulation or X propagation.
    if ( !p->fCexExternal && Abs2_GetFrame(p, Frame)->pLits[Id] < 0 ) return 0;
    Vec_WrdClear( p->vQueue );
    Vec_WrdClear( p->vUndo );
    Abs2_SetX( p, Frame, Id );
    while ( Head < Vec_WrdSize(p->vQueue) )
    {
        word Key = Vec_WrdEntry(p->vQueue, Head++);
        int f = Abs2_Frame(Key), i = Abs2_Id(Key), Fan, k;
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, i);
        if ( !(Head & 4095) && Abs2_Stop(p) ) return -1;
        if ( f == Depth && i == BadId ) return 1;
        Gia_ObjForEachFanoutStaticId( p->pGia, i, Fan, k )
            if ( (p->fCexExternal || Abs2_GetFrame(p, f)->pLits[Fan] >= 0) &&
                 Abs2_Eval(Gia_ManObj(p->pGia, Fan), Fan, Abs2_Values(p, f)) == 2 )
                Abs2_SetX( p, f, Fan );
        if ( Gia_ObjIsCo(pObj) && f < Depth )
        {
            int Reg = Gia_ObjCioId(pObj) - Gia_ManPoNum(p->pGia);
            if ( Reg >= 0 && Vec_IntEntry(p->vClasses, Reg) &&
                 (p->fCexExternal || Abs2_GetFrame(p, f+1)->pLits[Gia_ObjId(p->pGia, Gia_ManRo(p->pGia, Reg))] >= 0) )
                Abs2_SetX( p, f+1, Gia_ObjId(p->pGia, Gia_ManRo(p->pGia, Reg)) );
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Builds and checks a counterexample on the original design.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Abs2_Counterexample( Abs2_Man_t * p, int Depth, int Po )
{
    Abc_Cex_t * pCex;
    int f, i;
    Gia_Obj_t * pObj;
    if ( (ABC_INT64_T)(Depth + 1) * Gia_ManPiNum(p->pGia) + Gia_ManRegNum(p->pGia) > INT_MAX )
    {
        p->fStopped = 1;
        return NULL;
    }
    pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), Depth + 1 );
    pCex->iFrame = Depth;
    pCex->iPo = Po;
    for ( f = 0; f <= Depth; ++f )
        Gia_ManForEachPi( p->pGia, pObj, i )
            if ( Abs2_Model(p, f, Gia_ObjId(p->pGia, pObj)) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + f * pCex->nPis + i );
    if ( !Gia_ManVerifyCex(p->pGia, pCex, 0) )
    {
        Abc_CexFree( pCex );
        p->fError = 1;
        Abc_Print( -1, "&abs: original counterexample simulation failed.\n" );
        return NULL;
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Selects abstract flops needed to exclude a spurious trace.]

  Description [Generalize a simulated trace by replacing unnecessary abstract flops
  with X. The retained registers are sufficient to exclude this trace.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_SelectFlops( Abs2_Man_t * p, int Target, int Po )
{
    Gia_Obj_t * pObj;
    int i, f, Reg;
    Vec_IntClear( p->vAdd );
    for ( i = 0; i < Gia_ManRegNum(p->pGia); ++i )
    {
        Reg = p->vCbaOrder ? Vec_IntEntry(p->vCbaOrder, i) : i;
        pObj = Gia_ManRo(p->pGia, Reg);
        if ( Vec_IntEntry(p->vClasses, Reg) ) continue;
        if ( Abs2_Stop(p) ) return -1;
        for ( f = Target; f >= 0; --f )
        {
            int Result = Abs2_PropagateX(p, f, Gia_ObjId(p->pGia, pObj), Target,
                                        Gia_ObjId(p->pGia, Gia_ManPo(p->pGia, Po)));
            if ( Result < 0 ) return -1;
            if ( Result )
            {
                Abs2_Undo( p );
                Vec_IntPush( p->vAdd, Reg );
                break;
            }
        }
    }
    return Vec_IntSize( p->vAdd );
}

/**Function*************************************************************

  Synopsis    [Adds concrete flop transitions and pins them through a depth.]

  Description [Strengthen the current map and install new links into the existing
  unrolling. Keep externally required flops until their trace is covered.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_ActivateFlops( Abs2_Man_t * p, int KeepUntil )
{
    int i, f, Reg, nAdded = 0;
    Vec_IntForEachEntry( p->vAdd, Reg, i )
    {
        int Act = Vec_IntEntry(p->vActs, Reg);
        if ( KeepUntil > Vec_IntEntry(p->vKeepUntil, Reg) )
            Vec_IntWriteEntry( p->vKeepUntil, Reg, KeepUntil );
        if ( Vec_IntEntry(p->vClasses, Reg) ) continue;
        nAdded++;
        if ( Act && !Vec_IntEntry(p->vFrozen, Reg) )
        {
            assert(p->nInactiveActs > 0);
            ccadical_freeze(p->pSat, Act);
            Vec_IntWriteEntry(p->vFrozen, Reg, 1);
            --p->nInactiveActs;
            ++p->pPars->nReactivations;
        }
        Vec_IntWriteEntry( p->vClasses, Reg, 1 );
        ++p->nConcrete;
        ++p->pPars->nAdded;
        // Existing free flop outputs need their transition in every frame.
        for ( f = 0; f < Vec_PtrSize(p->vFrames); ++f )
        {
            int Id = Gia_ObjId(p->pGia, Gia_ManRo(p->pGia, Reg));
            if ( Abs2_GetFrame(p, f)->pLits[Id] >= 0 && Abs2_Insert(p, f, Id) < 0 ) return -1;
        }
    }
    return nAdded;
}

/**Function*************************************************************

  Synopsis    [Refines a SAT trace or returns a checked original counterexample.]

  Description [Return 1 after refinement, 0 for a checked original CEX, -1 on stopping.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_Refine( Abs2_Man_t * p, int Depth, Abc_Cex_t ** ppCex )
{
    int f, i, Po = -1, Target = -1, Added;
    Gia_Obj_t * pObj;
    abctime clk = Abc_Clock();
    // PBA can expose a counterexample in an earlier frame. Do not assume
    // that the disjunction-of-bads query is satisfied in its latest frame.
    for ( f = 0; f <= Depth && Po < 0; ++f )
        Gia_ManForEachPo( p->pGia, pObj, i )
            if ( Abs2_Model(p, f, Gia_ObjId(p->pGia, pObj)) )
            {
                Po = i;
                Target = f;
                break;
            }
    if ( Po < 0 || !Abs2_Simulate(p, Target) )
    {
        if ( Po < 0 ) p->fError = 1;
        return -1;
    }
    if ( Abs2_Values(p, Target)[Gia_ObjId(p->pGia, Gia_ManPo(p->pGia, Po))] != 1 )
    {
        p->fError = 1;
        Abc_Print( -1, "&abs: SAT model disagrees with ternary simulation.\n" );
        return -1;
    }
    if ( Abs2_SelectFlops(p, Target, Po) < 0 ) return -1;
    Added = Vec_IntSize(p->vAdd);
    if ( !Added )
    {
        *ppCex = Abs2_Counterexample(p, Target, Po);
        p->pPars->timeRefine += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
        return *ppCex ? 0 : -1;
    }
    if ( Abs2_ActivateFlops(p, 0) < 0 ) return -1;
    p->pPars->timeRefine += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Orders flop assumptions by SAT-variable age.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abs2_CompareAssumptions( const void * p0, const void * p1 )
{
    int a = *(const int *)p0, b = *(const int *)p1;
    a = a < 0 ? -a : a;
    b = b < 0 ? -b : b;
    return (a > b) - (a < b);
}

/**Function*************************************************************

  Synopsis    [Applies the current flop-map assumptions to the SAT query.]

  Description [The assumption set is unchanged. Its order can change SAT search and the
  failed core, which in turn changes the abstraction used at the next depth.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Abs2_AssumeFlops( Abs2_Man_t * p )
{
    int i, Reg, Act, Mode = p->pPars->nAssumeOrder;
    if ( !Mode )
    {
        Vec_IntForEachEntry( p->vClasses, Reg, i )
            if ( (Act = Vec_IntEntry(p->vActs, i)) )
            {
                if ( Reg ) ccadical_assume(p->pSat, Act);
                else if ( p->pPars->nActMode == 2 ) ccadical_assume(p->pSat, -Act);
            }
        return;
    }
    // vCore is scratch here; prefix caching rebuilds it after an UNSAT query.
    Vec_IntClear(p->vCore);
    Vec_IntForEachEntry( p->vClasses, Reg, i )
        if ( (Act = Vec_IntEntry(p->vActs, i)) )
        {
            if ( Reg ) Vec_IntPush(p->vCore, Act);
            else if ( p->pPars->nActMode == 2 ) Vec_IntPush(p->vCore, -Act);
        }
    if ( Mode >= 2 && Vec_IntSize(p->vCore) > 1 )
        qsort(Vec_IntArray(p->vCore), Vec_IntSize(p->vCore), sizeof(int), Abs2_CompareAssumptions);
    if ( Mode == 1 || Mode == 3 )
    {
        for ( i = Vec_IntSize(p->vCore)-1; i >= 0; --i )
            ccadical_assume(p->pSat, Vec_IntEntry(p->vCore, i));
    }
    else
        Vec_IntForEachEntry(p->vCore, Act, i) ccadical_assume(p->pSat, Act);
}

/**Function*************************************************************

  Synopsis    [Sets defaults for bounded flop abstraction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs2_SetDefaultParams( Abs2_Par_t * pPars )
{
    memset( pPars, 0, sizeof(*pPars) );
    pPars->nFramesMax = 20;
    pPars->nTimeOut = 60;
    pPars->nSatMode = 2;
    pPars->fUseCuts = 1;
    pPars->nCutMax = 4;
    pPars->fNativeQuery = 1;
    pPars->fUsePba = 1;
    pPars->fStopFull = 1;
    pPars->iFrame = -1;
    pPars->iCompactFrame = -1;
}

/**Function*************************************************************

  Synopsis    [Checks whether explicit register initial values are all zero.]

  Description [A raw AIGER read can retain explicit initial values. The abstraction
  unrolling assumes zero; reject other initial states before deriving any
  bounded result, abstract model, or counterexample from this graph.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_ManCheckZeroInit( Gia_Man_t * pGia )
{
    int i, Init;
    if ( !pGia ) return 0;
    if ( !pGia->vRegInits ) return 1;
    if ( Vec_IntSize(pGia->vRegInits) != Gia_ManRegNum(pGia) ) return 0;
    Vec_IntForEachEntry( pGia->vRegInits, Init, i )
        if ( Init != 0 ) return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Creates an incremental abstraction session on a normalized design.]

  Description [Start an incremental session. Parameters and the original graph must
  outlive the session; the returned abstraction map is borrowed until Stop.
  The graph and parameter structure must remain alive until Stop.
  Returns NULL for invalid input; the session owns its normalized graph copy.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abs2_Man_t * Abs2_ManStart( Gia_Man_t * pGia, Abs2_Par_t * pPars )
{
    Abs2_Man_t * p;
    int i, Reg;
    if ( !pGia || !pPars || !Abs2_ManCheckZeroInit(pGia) || !Gia_ManPoNum(pGia) || Gia_ManConstrNum(pGia) ||
         pPars->nFramesMax < -1 || pPars->nFramesMax > 100000000 ||
         pPars->nTimeOut < 0 || pPars->nConfLimit < 0 || pPars->nStableMin < 0 ||
         pPars->nCompactDepth < 0 ||
         pPars->nSimplifyEvery < 0 ||
         (pPars->nSimplifyEvery && pPars->nSatMode == 3) ||
         pPars->nSatMode < 0 || pPars->nSatMode > 8 ||
         (pPars->nCutMax && (pPars->nCutMax < 3 || pPars->nCutMax > 6)) ||
         pPars->nProofMode < 0 || pPars->nProofMode > 2 ||
         pPars->nActMode < 0 || pPars->nActMode > 2 ||
         pPars->nAssumeOrder < 0 || pPars->nAssumeOrder > 3 ||
         pPars->nCbaOrder < 0 || pPars->nCbaOrder > 3 ||
         pPars->nCnfMode < 0 || pPars->nCnfMode > 2 ||
         (pPars->nCnfMode && !pPars->fUseCuts) ||
         pPars->nResolveMode < 0 || pPars->nResolveMode > 5 ||
         (pPars->nResolveMode && (!pPars->fUseCuts || pPars->nCnfMode)) ||
         (pPars->fClauseQuery && pPars->fNativeQuery) ||
         (pPars->fUseStart && pGia->vFlopClasses &&
          Vec_IntSize(pGia->vFlopClasses) != Gia_ManRegNum(pGia)) ) return NULL;
    p = ABC_CALLOC( Abs2_Man_t, 1 );
    p->pGiaOrig = pGia;
    p->Result = -1;
    p->pPars = pPars;
    p->fCompactVars = pPars->fCompactVars;
    p->clkStart = Abc_Clock();
    p->clkStop = pPars->nTimeOut ? p->clkStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    pPars->iFrame = -1;
    pPars->nCalls = pPars->nCexes = pPars->nAdded = pPars->nRemoved = 0;
    pPars->nTruthCuts = 0;
    pPars->nResolveCalls = pPars->nResolveCuts = pPars->nResolvedNodes = 0;
    pPars->nMinimizedCuts = pPars->nClausesSaved = 0;
    pPars->nCnfMemoHits = 0;
    pPars->nSimplifies = pPars->nReactivations = 0;
    pPars->iCompactFrame = p->fCompactVars ? 0 : -1;
    pPars->timeSat = pPars->timeRefine = pPars->timeSimplify = pPars->timeResolve = pPars->timeTotal = 0;
    p->pGia = Abs2_Normalize(pGia);
    Gia_ManStaticFanoutStart( p->pGia );
    p->pUnroll = Gia_ManStart( 1000 );
    Gia_ManHashStart( p->pUnroll );
    p->pSat = ccadical_init();
    ccadical_set_option( p->pSat, "quiet", 1 );
    if ( pPars->nSatMode )
    {
        ccadical_set_option( p->pSat, "stabilize", 0 );
        ccadical_set_option( p->pSat, "walk", 0 );
    }
    if ( pPars->nSatMode == 2 || pPars->nSatMode >= 4 )
    {
        ccadical_set_option( p->pSat, "inprocessing", 0 );
        ccadical_set_option( p->pSat, "preprocesslight", 0 );
    }
    if ( pPars->nSatMode == 4 ) ccadical_set_option(p->pSat, "phase", 0);
    if ( pPars->nSatMode == 5 || pPars->nSatMode == 6 )
        ccadical_set_option(p->pSat, "ilb", pPars->nSatMode - 4);
    if ( pPars->nSatMode >= 7 )
    {
        ccadical_set_option(p->pSat, "stabilize", 1);
        ccadical_set_option(p->pSat, "stabilizeonly", pPars->nSatMode == 7);
    }
    if ( pPars->nSatMode == 3 )
    {
        ccadical_set_option( p->pSat, "elim", 0 );
        ccadical_set_option( p->pSat, "fastelim", 0 );
    }
    if ( pPars->nSimplifyEvery )
    {
        ccadical_set_option(p->pSat, "inprobing", 0);
        ccadical_set_option(p->pSat, "elimrounds", 1);
    }
    ccadical_set_terminate( p->pSat, p, Abs2_StopSat );
    Abs2_Clause( p, 1, 0, 0 );
    p->vFrames = Vec_PtrAlloc( 16 );
    p->vValues = Vec_PtrAlloc( 16 );
    p->vClasses = Vec_IntStart( Gia_ManRegNum(pGia) );
    p->vKeepUntil = Vec_IntStart( Gia_ManRegNum(pGia) );
    p->vActs = Vec_IntStart( Gia_ManRegNum(pGia) );
    p->vFrozen = Vec_IntStart( Gia_ManRegNum(pGia) );
    p->vBads = Vec_IntAlloc( 16 );
    p->vAdd = Vec_IntAlloc( 16 );
    p->vEncoded = Vec_IntStart( 1 );
    Vec_IntWriteEntry(p->vEncoded, 0, pPars->nCnfMode ? 3 : 1);
    p->vKeep = Vec_IntStart( 1 );
    p->vCnfStack = Vec_IntAlloc( 64 );
    p->vConjStack = Vec_IntAlloc( 64 );
    p->vLeaves = Vec_IntAlloc( 64 );
    p->vSatVars = Vec_IntStart( 1 );
    p->nSatVars = 1;
    p->vBadLits = Vec_IntAlloc( 64 );
    p->vCore = Vec_IntAlloc( 64 );
    p->vStack = Vec_WrdAlloc( 64 );
    p->vQueue = Vec_WrdAlloc( 64 );
    p->vUndo = Vec_WrdAlloc( 64 );
    if ( pPars->nCnfMode ) p->vPolStack = Vec_WrdAlloc(64);
    if ( pPars->nResolveMode )
    {
        p->vResolveDefs = Vec_WecAlloc(64);
        p->vResolvePos = Vec_IntAlloc(64);
    }
    if ( pPars->nResolveMode == 5 )
    {
        p->vCnfRefs = Vec_IntStart(1);
        p->vResolveMerged = Vec_IntAlloc(64);
        p->vMemoMap = Vec_IntStart(1);
        p->vMemoIds = Vec_IntStart(ABS2_CNF_MEMOS);
        p->vMemoMerged = Vec_IntStart(ABS2_CNF_MEMOS);
        p->vMemoDefs = Vec_WecStart(ABS2_CNF_MEMOS);
        p->vCombine = Vec_IntAlloc(256);
    }
    if ( pPars->nCnfMode == 2 )
    {
        p->vRoInfo = Vec_WrdAlloc(64);
        p->vPolPending = Vec_IntAlloc(64);
    }
    if ( pPars->fUseStart && pGia->vFlopClasses )
        Vec_IntForEachEntry( pGia->vFlopClasses, Reg, i )
            if ( Reg ) Vec_IntWriteEntry( p->vClasses, i, 1 ), ++p->nConcrete;
    p->vCbaOrder = Abs2_CreateCbaOrder(p);
    if ( pPars->fVerbose )
        Abc_Print( 1, "abs2: depth  calls  concrete/total  SAT(s)  refine(s)  elapsed(s)\n" );
    return p;
}

/**Function*************************************************************

  Synopsis    [Continues an abstraction session through the requested depth.]

  Description [Continue the same unrolling to the requested inclusive depth. Completed
  queries retain their clauses, assumptions' cores and abstraction state.
  A resource interruption ends the session; explicit yields are resumable.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_ManRun( Abs2_Man_t * p, int nFramesMax, int nStableMin )
{
    Abs2_Par_t * pPars = p->pPars;
    Gia_Obj_t * pObj;
    Abc_Cex_t * pCex = p->pCex;
    int i, Reg, Depth = p->Depth, Stable = p->Stable, Bad = p->Bad, Result = p->Result;
    pPars->fYielded = 0;
    if ( p->fError ) return p->Result = -2;
    if ( Result != -1 || p->fStopped ) return Result;
    assert( nFramesMax >= -1 && nStableMin >= 0 );
    pPars->nFramesMax = nFramesMax;
    pPars->nStableMin = nStableMin;
    while ( !Abs2_Stop(p) )
    {
        int SatResult, Query = 0;
        abctime clk;
        if ( Abs2_Yield(p) ) break;
        if ( pPars->nFramesMax >= 0 && Depth > pPars->nFramesMax && Stable >= pPars->nStableMin ) break;
        if ( pPars->fStopFull && p->nConcrete == Gia_ManRegNum(p->pGia) && Stable && Depth > 5 ) break;
        if ( p->fSimplifyPending )
        {
            p->fSimplifyPending = 0;
            Abs2_Simplify( p, Depth );
            if ( Abs2_Stop(p) || Abs2_Yield(p) ) break;
        }
        if ( !p->fCompactVars && pPars->nCompactDepth && Depth >= pPars->nCompactDepth )
        {
            int Id, nOld = Gia_ManObjNum(p->pUnroll);
            // Preserve every existing SAT identity, including absorbed gates
            // that may acquire definitions later. Allocate only future nodes
            // compactly. The previous query's model/core has been consumed.
            ccadical_resize(p->pSat, nOld);
            p->nSatVars = ccadical_vars(p->pSat);
            Vec_IntFill(p->vSatVars, nOld, 0);
            for ( Id = 1; Id < nOld; ++Id ) Vec_IntWriteEntry(p->vSatVars, Id, Id + 1);
            p->fCompactVars = 1;
            pPars->iCompactFrame = Depth;
        }
        if ( Vec_IntSize(p->vBads) == Depth )
        {
            Gia_ManForEachPo( p->pGia, pObj, i )
            {
                int Lit = Abs2_Insert(p, Depth, Gia_ObjId(p->pGia, pObj));
                if ( Lit < 0 ) break;
                // Preserve a defined SAT value for every bad output, even
                // if the cumulative disjunction later simplifies away.
                if ( !Abs2_Encode(p, Lit, 1) ) break;
                // Every earlier bad is queried again. Keep these roots during
                // explicit preprocessing, which runs without the query clause.
                if ( pPars->nSimplifyEvery && Lit >= 2 ) ccadical_freeze(p->pSat, Abs2_SatLit(p, Lit));
                Vec_IntPush(p->vBadLits, Lit);
                if ( !pPars->fClauseQuery && !pPars->fNativeQuery ) Bad = Abs2_And(p, Bad ^ 1, Lit ^ 1) ^ 1;
            }
            if ( Abs2_Stop(p) ) break;
            Vec_IntPush( p->vBads, Bad );
        }
        // Refinement prepares every new concrete transition first. Only then
        // propagate saved demands; the encoder must not call Insert recursively
        // or overwrite its unrolling stack while a predecessor is incomplete.
        if ( p->vPolPending )
            while ( Vec_IntSize(p->vPolPending) )
            {
                int Lit = Vec_IntPop(p->vPolPending);
                if ( !Abs2_Encode(p, Lit, Vec_IntEntry(p->vEncoded, Lit >> 1)) ) break;
            }
        if ( Abs2_Stop(p) || Abs2_Yield(p) ) break;
        if ( pPars->fNativeQuery )
        {
            int Lit;
            // This clause has the lifetime of assumptions. Its model and
            // failed flop assumptions are consumed before the next mutation.
            Vec_IntForEachEntry(p->vBadLits, Lit, i) ccadical_constrain(p->pSat, Abs2_SatLit(p, Lit));
            ccadical_constrain(p->pSat, 0);
        }
        else if ( pPars->fClauseQuery )
        {
            int Lit;
            Query = Abs2_SatLit(p, Abs2_Input(p));
            ccadical_add(p->pSat, -Query);
            Vec_IntForEachEntry(p->vBadLits, Lit, i) ccadical_add(p->pSat, Abs2_SatLit(p, Lit));
            ccadical_add(p->pSat, 0);
            ccadical_assume(p->pSat, Query);
        }
        else
        {
            if ( !Abs2_Encode(p, Bad, 1) ) break;
            ccadical_assume( p->pSat, Abs2_SatLit(p, Bad) );
        }
        // An inactive flop guard occurs only negatively in permanent input
        // clauses. Assuming it false is as permissive as quantifying it;
        // keep this an assumption so a later CBA step can restore the flop.
        Abs2_AssumeFlops(p);
        ccadical_limit( p->pSat, "conflicts", pPars->nConfLimit ? pPars->nConfLimit : -1 );
        clk = Abc_Clock();
        SatResult = ccadical_solve( p->pSat );
        pPars->timeSat += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
        ++pPars->nCalls;
        // A late worker notification must not discard a completed model or
        // core. Consume it first; only an interrupted solve needs retrying.
        if ( !SatResult ) Abs2_Yield(p);
        if ( Abs2_Stop(p) || !SatResult )
        {
            // solve() resets assumptions, and the next native constraint
            // replaces this one. Retire a guarded query before external
            // refinement, then retry this same depth on the next Run.
            if ( Query ) Abs2_Clause(p, -Query, 0, 0);
            if ( !pPars->fYielded ) p->fStopped = 1;
            break;
        }
        if ( SatResult == 10 )
        {
            int Refined;
            // A concurrent prover must be retired before CBA consumes the
            // model. The callback may publish a proof but must not add SAT
            // clauses or assumptions, which would invalidate this model.
            if ( pPars->pFuncRefine && pPars->pFuncRefine(pPars->pStopData) )
            {
                p->fStopped = 1;
                break;
            }
            Stable = 0;
            ++pPars->nCexes;
            Refined = Abs2_Refine(p, Depth, &pCex);
            if ( Refined <= 0 )
            {
                if ( !Refined ) Result = 0;
                break;
            }
        }
        else
        {
            assert( SatResult == 20 );
            // Consume the failed-assumption core before adding any clauses.
            if ( pPars->fUsePba )
                Vec_IntForEachEntry( p->vClasses, Reg, i )
                    if ( Reg && Depth >= Vec_IntEntry(p->vKeepUntil, i) && (!Vec_IntEntry(p->vActs, i) || !ccadical_failed(p->pSat, Vec_IntEntry(p->vActs, i))) )
                    {
                        Vec_IntWriteEntry( p->vClasses, i, 0 );
                        --p->nConcrete;
                        ++pPars->nRemoved;
                    }
            if ( pPars->nProofMode ) Abs2_CacheProof(p);
            pPars->iFrame = Depth;
            if ( pPars->fVerbose )
                Abc_Print( 1, "abs2: %5d %6d %7d/%-7d %7.3f %9.3f %11.3f\n", Depth,
                    pPars->nCalls, p->nConcrete, Gia_ManRegNum(p->pGia), pPars->timeSat,
                    pPars->timeRefine, (double)(Abc_Clock() - p->clkStart) / CLOCKS_PER_SEC );
            ++Depth;
            ++Stable;
        }
        // Retire the query only after consuming its model or failed core.
        // Unlike a persistent cumulative OR, this matches ZZ's temporary
        // guarded disjunction and permits deleting its obsolete clauses.
        if ( Query ) Abs2_Clause(p, -Query, 0, 0);
        if ( SatResult == 20 && pPars->nSimplifyEvery &&
             !(pPars->fStopFull && p->nConcrete == Gia_ManRegNum(p->pGia) && Stable && Depth > 5) )
        {
            if ( pPars->nFramesMax >= 0 && Depth > pPars->nFramesMax && Stable >= pPars->nStableMin )
                p->fSimplifyPending = 1;
            else
                Abs2_Simplify(p, Depth);
        }
    }
    if ( p->fError ) Result = -2;
    p->Depth = Depth;
    p->Stable = Stable;
    p->Bad = Bad;
    p->pCex = pCex;
    p->Result = Result;
    pPars->timeTotal = (double)(Abc_Clock() - p->clkStart) / CLOCKS_PER_SEC;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Returns the borrowed current flop-abstraction map.]

  Description [The caller must not modify or free the returned vector.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abs2_ManReadClasses( Abs2_Man_t * p )
{
    return p->vClasses;
}

/**Function*************************************************************

  Synopsis    [Checks a trace against the normalized original design.]

  Description [The normalized graph preserves the original PI/PO/register ordering and
  expands real mux/XOR nodes, which Gia_ManVerifyCex does not simulate.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_ManVerifyCex( Abs2_Man_t * p, Abc_Cex_t * pCex )
{
    int i;
    if ( !pCex || pCex->iFrame < 0 || pCex->iFrame == INT_MAX || pCex->iPo < 0 ||
         pCex->iPo >= Gia_ManPoNum(p->pGia) ||
         pCex->nRegs != Gia_ManRegNum(p->pGia) || pCex->nPis != Gia_ManPiNum(p->pGia) ||
         (ABC_INT64_T)pCex->nRegs + ((ABC_INT64_T)pCex->iFrame + 1) * pCex->nPis != pCex->nBits )
        return 0;
    for ( i = 0; i < pCex->nRegs; i++ )
        if ( Abc_InfoHasBit(pCex->pData, i) ) return 0;
    return Gia_ManVerifyCex( p->pGia, pCex, 0 );
}

/**Function*************************************************************

  Synopsis    [Refines the current map using a trace from an older abstraction.]

  Description [A PDR counterexample can reach far beyond the current BMC prefix. Reuse
  ternary CBA on its concrete trace instead of replaying every SAT query.
  All simulated values follow the worker's map; the selected new flops
  strengthen the current map, even when that map has changed meanwhile.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_ManRefine( Abs2_Man_t * p, Abc_Cex_t * pCex, Vec_Int_t * vClasses )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vCurrent;
    int f, i, k, Reg, nConcrete = 0, Result;
    abctime clk = Abc_Clock();
    if ( !pCex || !vClasses || Vec_IntSize(vClasses) != Gia_ManRegNum(p->pGia) ||
         pCex->iFrame < 0 || pCex->iFrame == INT_MAX ||
         pCex->iPo < 0 || pCex->iPo >= Gia_ManPoNum(p->pGia) ) return -2;
    Vec_IntForEachEntry( vClasses, Reg, i ) nConcrete += Reg != 0;
    if ( pCex->nRegs != nConcrete ||
         pCex->nPis != Gia_ManPiNum(p->pGia) + Gia_ManRegNum(p->pGia) - nConcrete ||
         (ABC_INT64_T)pCex->nRegs + ((ABC_INT64_T)pCex->iFrame + 1) * pCex->nPis != pCex->nBits ) return -2;
    for ( i = 0; i < pCex->nRegs; i++ )
        if ( Abc_InfoHasBit(pCex->pData, i) ) return -2;
    while ( Vec_PtrSize(p->vValues) <= pCex->iFrame )
    {
        if ( Abs2_Stop(p) ) return -1;
        Vec_PtrPush( p->vValues, ABC_CALLOC(unsigned char, Gia_ManObjNum(p->pGia)) );
    }
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        unsigned char * pValues = Abs2_Values(p, f);
        if ( Abs2_Stop(p) ) return -1;
        pValues[0] = 0;
        Gia_ManForEachPi( p->pGia, pObj, i )
            pValues[Gia_ObjId(p->pGia, pObj)] = Abc_InfoHasBit(pCex->pData, pCex->nRegs + f * pCex->nPis + i);
        k = Gia_ManPiNum(p->pGia);
        Gia_ManForEachRo( p->pGia, pObj, i )
            pValues[Gia_ObjId(p->pGia, pObj)] = Vec_IntEntry(vClasses, i) ?
                (f ? Abs2_Values(p, f-1)[Gia_ObjId(p->pGia, Gia_ManRi(p->pGia, i))] : 0) :
                Abc_InfoHasBit(pCex->pData, pCex->nRegs + f * pCex->nPis + k++);
        Gia_ManForEachAnd( p->pGia, pObj, i )
        {
            if ( !(i & 4095) && Abs2_Stop(p) ) return -1;
            pValues[i] = Abs2_Eval( pObj, i, pValues );
        }
        Gia_ManForEachCo( p->pGia, pObj, i )
            pValues[Gia_ObjId(p->pGia, pObj)] = Abs2_Eval( pObj, Gia_ObjId(p->pGia, pObj), pValues );
    }
    if ( Abs2_Values(p, pCex->iFrame)[Gia_ObjId(p->pGia, Gia_ManPo(p->pGia, pCex->iPo))] != 1 ) return -2;
    vCurrent = p->vClasses;
    p->vClasses = vClasses;
    p->fCexExternal = 1;
    Result = Abs2_SelectFlops( p, pCex->iFrame, pCex->iPo );
    p->vClasses = vCurrent;
    p->fCexExternal = 0;
    if ( Result >= 0 )
    {
        // Ternary CBA assumed every concrete flop in the worker's map.
        // PBA may have pruned some meanwhile. Restore those dependencies
        // and pin them, together with the newly selected flops, until BMC
        // covers the trace. The two sets are disjoint by construction.
        Vec_IntForEachEntry( vClasses, Reg, i )
            if ( Reg ) Vec_IntPush( p->vAdd, i );
        Result = Abs2_ActivateFlops( p, pCex->iFrame );
        p->Stable = 0;
    }
    p->pPars->timeRefine += (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Transfers the final map and trace and frees the session.]

  Description [Transfer the final map and checked counterexample to the original graph.
  Moves the final map and counterexample to the input Gia manager.
  The input manager and parameter structure remain owned by the caller.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abs2_ManStop( Abs2_Man_t * p )
{
    Gia_Man_t * pGia = p->pGiaOrig;
    Abs2_Par_t * pPars = p->pPars;
    Abc_Cex_t * pCex = p->pCex;
    Abs2_Frame_t * pFrame;
    void * pValues;
    int i, Result = p->Result;
    if ( Result != -2 )
    {
        Vec_IntFreeP( &pGia->vFlopClasses );
        pGia->vFlopClasses = p->vClasses;
        p->vClasses = NULL;
        Abc_CexFreeP( &pGia->pCexSeq );
        pGia->pCexSeq = pCex;
        pCex = NULL;
    }
    Abc_CexFreeP( &pCex );
    if ( pPars->fVerbose )
    {
        Abc_Print( 1, "abs2 CNF: unrolled=%d variables=%d clauses=%d conflicts=%d\n",
            Gia_ManObjNum(p->pUnroll), ccadical_vars(p->pSat),
            ccadical_clauses(p->pSat), ccadical_conflicts(p->pSat) );
        Abc_Print( 1, "abs2 storage: frames=%d values=%d graph=%.2f MiB maps=%.2f MiB compact-frame=%d active-vars=%lld irredundant=%lld\n",
            Vec_PtrSize(p->vFrames), Vec_PtrSize(p->vValues), Gia_ManMemory(p->pUnroll)/(1 << 20),
            ((double)Vec_PtrSize(p->vFrames) * (sizeof(int) * (double)Gia_ManObjNum(p->pGia) + Gia_ManRegNum(p->pGia)) +
             (double)Vec_PtrSize(p->vValues) * Gia_ManObjNum(p->pGia))/(1 << 20),
            pPars->iCompactFrame, (long long)ccadical_active(p->pSat), (long long)ccadical_irredundant(p->pSat) );
    }
    Vec_PtrForEachEntry( Abs2_Frame_t *, p->vFrames, pFrame, i )
    {
        ABC_FREE( pFrame->pLits );
        ABC_FREE( pFrame->pLinked );
        ABC_FREE( pFrame );
    }
    Vec_PtrForEachEntry( void *, p->vValues, pValues, i ) ABC_FREE( pValues );
    Vec_PtrFree( p->vFrames );
    Vec_PtrFree( p->vValues );
    Vec_IntFreeP( &p->vClasses );
    Vec_IntFree( p->vKeepUntil );
    Vec_IntFree( p->vActs );
    Vec_IntFree( p->vFrozen );
    Vec_IntFree( p->vBads );
    Vec_IntFree( p->vAdd );
    Vec_IntFree( p->vEncoded );
    Vec_IntFree( p->vKeep );
    Vec_IntFree( p->vCnfStack );
    Vec_IntFree( p->vConjStack );
    Vec_IntFree( p->vLeaves );
    Vec_IntFree( p->vSatVars );
    Vec_IntFree( p->vBadLits );
    Vec_IntFree( p->vCore );
    Vec_IntFreeP( &p->vCbaOrder );
    Vec_IntFreeP( &p->vPolPending );
    Vec_WrdFreeP( &p->vPolStack );
    Vec_WrdFreeP( &p->vRoInfo );
    Vec_WecFreeP( &p->vResolveDefs );
    Vec_IntFreeP( &p->vResolvePos );
    Vec_IntFreeP( &p->vCnfRefs );
    Vec_IntFreeP( &p->vResolveMerged );
    Vec_IntFreeP( &p->vMemoMap );
    Vec_IntFreeP( &p->vMemoIds );
    Vec_IntFreeP( &p->vMemoMerged );
    Vec_IntFreeP( &p->vCombine );
    Vec_WecFreeP( &p->vMemoDefs );
    Vec_WrdFree( p->vStack );
    Vec_WrdFree( p->vQueue );
    Vec_WrdFree( p->vUndo );
    ccadical_release( p->pSat );
    Gia_ManStop( p->pUnroll );
    Gia_ManStop( p->pGia );
    pPars->timeTotal = (double)(Abc_Clock() - p->clkStart) / CLOCKS_PER_SEC;
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Runs bounded abstraction and releases its incremental session.]

  Description [The one-shot command keeps its existing bounded-abstraction semantics.
  Returns 0 for a checked original counterexample, -1 for a bounded
  abstraction, and -2 for invalid input or an internal failure.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abs2_ManPerform( Gia_Man_t * pGia, Abs2_Par_t * pPars )
{
    Abs2_Man_t * p = Abs2_ManStart( pGia, pPars );
    int Result;
    if ( !p ) return -2;
    Result = Abs2_ManRun( p, pPars->nFramesMax, pPars->nStableMin );
    Abs2_ManStop( p );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Extracts a flop abstraction with a predictable interface order.]

  Description [Iterative extraction; keep register ordering so the selected-register map
  also gives a direct correspondence for a downstream invariant.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Abs2_ManDerive( Gia_Man_t * pGia, Vec_Int_t * vClasses )
{
    Gia_Man_t * p, * pNew, * pClean;
    Gia_Obj_t * pObj;
    Vec_Int_t * vMap;
    int i, nRegs = 0;
    if ( !pGia || !Abs2_ManCheckZeroInit(pGia) || Gia_ManConstrNum(pGia) || !vClasses ||
         Vec_IntSize(vClasses) != Gia_ManRegNum(pGia) ) return NULL;
    p = pGia->pMuxes || Gia_ManXorNum(pGia) ? Abs2_Normalize(pGia) : pGia;
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav(pGia->pName);
    pNew->pSpec = Abc_UtilStrsav(pGia->pSpec);
    vMap = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachPi( p, pObj, i ) Vec_IntWriteEntry(vMap, Gia_ObjId(p, pObj), Gia_ManAppendCi(pNew));
    Gia_ManForEachRo( p, pObj, i )
        if ( !Vec_IntEntry(vClasses, i) ) Vec_IntWriteEntry(vMap, Gia_ObjId(p, pObj), Gia_ManAppendCi(pNew));
    Gia_ManForEachRo( p, pObj, i )
        if ( Vec_IntEntry(vClasses, i) )
            Vec_IntWriteEntry(vMap, Gia_ObjId(p, pObj), Gia_ManAppendCi(pNew)), ++nRegs;
    Gia_ManHashStart( pNew );
    Gia_ManForEachAnd( p, pObj, i )
    {
        int a = Vec_IntEntry(vMap, Gia_ObjFaninId0(pObj, i)) ^ Gia_ObjFaninC0(pObj);
        int b = Gia_ObjIsBuf(pObj) ? 0 : Vec_IntEntry(vMap, Gia_ObjFaninId1(pObj, i)) ^ Gia_ObjFaninC1(pObj);
        Vec_IntWriteEntry( vMap, i, Gia_ObjIsBuf(pObj) ? a : Gia_ManHashAnd(pNew, a, b) );
    }
    Gia_ManForEachPo( p, pObj, i )
        Gia_ManAppendCo( pNew, Vec_IntEntry(vMap, Gia_ObjFaninId0p(p, pObj)) ^ Gia_ObjFaninC0(pObj) );
    Gia_ManForEachRi( p, pObj, i )
        if ( Vec_IntEntry(vClasses, i) )
            Gia_ManAppendCo( pNew, Vec_IntEntry(vMap, Gia_ObjFaninId0p(p, pObj)) ^ Gia_ObjFaninC0(pObj) );
    Gia_ManSetRegNum( pNew, nRegs );
    Gia_ManHashStop( pNew );
    // Backward topological marking avoids the recursive cleanup visitor on
    // deep cones. Keep CIs in order to preserve the register/input mapping.
    Gia_ManForEachAnd( pNew, pObj, i ) pObj->fMark0 = 1;
    Gia_ManForEachCo( pNew, pObj, i ) Gia_ObjFanin0(pObj)->fMark0 = 0;
    for ( i = Gia_ManObjNum(pNew)-1; i > 0; --i )
    {
        pObj = Gia_ManObj(pNew, i);
        if ( !Gia_ObjIsAnd(pObj) || pObj->fMark0 ) continue;
        Gia_ObjFanin0(pObj)->fMark0 = 0;
        Gia_ObjFanin1(pObj)->fMark0 = 0;
    }
    pClean = Gia_ManDupMarked(pNew);
    Gia_ManStop( pNew );
    if ( p != pGia ) Gia_ManStop( p );
    Vec_IntFree( vMap );
    return pClean;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
