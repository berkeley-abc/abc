/**CFile****************************************************************

  FileName    [cecCorr4.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Signal correspondence with selected inductive constraints.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCorr4.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
#include "opt/drw/drw.h"
#include "sat/glucose3/AbcGlucose3.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

enum { CEC4_SIDE_SEARCH_LIMIT = 512, CEC4_SIDE_ADJ_LIMIT = 16 };

struct Cec4_Sat_t_
{
    Gia_Man_t * pCore;
    bmcg3_sat_solver * pSat;
    int nSides, nConfs, nLoaded, nConfLast, fConditional, Stamp;
    int Care, nAvailableMax;
    void * pData;
    int (*pBuild)( void *, int );
    Vec_Int_t * vHeads, * vLinks, * vSideLits, * vSideMarks, * vSideKeys;
    Vec_Int_t * vSeen, * vQueue, * vAssumps, * vRoots;
    ABC_INT64_T nQueries, nSelected, nSearch, nConditional;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts an incremental circuit solver for one immutable core.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Cec4_Sat_t * Cec4_SatStart( int nSides, int nConfs )
{
    Cec4_Sat_t * p = ABC_CALLOC( Cec4_Sat_t, 1 );
    p->nSides = nSides;
    p->nConfs = nConfs;
    p->pSat = bmcg3_sat_solver_start();
    bmcg3_sat_solver_set_jftr( p->pSat, 2 );
    // The only permanent input constraint pins constant zero. All gate
    // units are learned circuit consequences; induction hypotheses remain
    // assumptions and still require full justification on every query.
    bmcg3_sat_solver_set_unit_justification( p->pSat, 0 );
    bmcg3_sat_solver_eliminate( p->pSat, 1 );
    p->vHeads = Vec_IntAlloc( 1000 );
    p->vLinks = Vec_IntAlloc( 1000 );
    p->vSideLits = Vec_IntAlloc( 1000 );
    p->vSideMarks = Vec_IntAlloc( 1000 );
    p->vSideKeys = Vec_IntAlloc( 1000 );
    p->vSeen = Vec_IntAlloc( 1000 );
    p->vQueue = Vec_IntAlloc( 1000 );
    p->vAssumps = Vec_IntAlloc( 16 );
    p->vRoots = Vec_IntAlloc( 16 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the solver and its constraint index.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_SatStop( Cec4_Sat_t * p )
{
    bmcg3_sat_solver_stop( p->pSat );
    Vec_IntFree( p->vHeads );
    Vec_IntFree( p->vLinks );
    Vec_IntFree( p->vSideLits );
    Vec_IntFree( p->vSideMarks );
    Vec_IntFree( p->vSideKeys );
    Vec_IntFree( p->vSeen );
    Vec_IntFree( p->vQueue );
    Vec_IntFree( p->vAssumps );
    Vec_IntFree( p->vRoots );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Indexes a constraint at an incident circuit variable.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec4_SideIndex( Cec4_Sat_t * p, int Var, int Side )
{
    int Link;
    if ( !Var ) return;
    Link = Vec_IntSize( p->vLinks );
    Vec_IntPushTwo( p->vLinks, Side, Vec_IntEntry(p->vHeads, Var) );
    Vec_IntWriteEntry( p->vHeads, Var, Link );
}

/**Function*************************************************************

  Synopsis    [Loads only gates appended since the previous query.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec4_SatLoad( Cec4_Sat_t * p )
{
    Gia_Man_t * pCore = p->pCore;
    Gia_Obj_t * pObj;
    int i, a, b, Lit = 1;
    if ( p->nLoaded == Gia_ManObjNum(pCore) ) return;
    bmcg3_sat_solver_set_nvars( p->pSat, Gia_ManObjNum(pCore) );
    for ( i = p->nLoaded; i < Gia_ManObjNum(pCore); i++ )
    {
        pObj = Gia_ManObj( pCore, i );
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        a = Gia_ObjFaninLit0p( pCore, pObj );
        b = Gia_ObjFaninLit1p( pCore, pObj );
        if ( a > b ) ABC_SWAP( int, a, b );
        bmcg3_sat_solver_set_var_fanin_lit( p->pSat, i, a, b );
    }
    if ( !p->nLoaded )
        bmcg3_sat_solver_addclause( p->pSat, &Lit, 1 );
    p->nLoaded = Gia_ManObjNum( pCore );
}

/**Function*************************************************************

  Synopsis    [Indexes the current induction hypotheses by existing endpoints.]

  Description [Records contain raw, substituted, mismatch literals and key.
  A negative raw endpoint is absent from the lazy core; the existing
  substituted endpoint still indexes the hypothesis. A negative mismatch
  is built through the callback only when selected.
  Hypotheses are assumptions, never clauses; learned clauses remain valid
  when the classes or the selected subset change.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_SatPrepare( Cec4_Sat_t * p, Gia_Man_t * pCore, Vec_Int_t * vSides, int Care,
                     void * pData, int (*pBuild)(void *, int) )
{
    Gia_Obj_t * pObj;
    int i, j, Side, Lit;
    p->pCore = pCore;
    p->Care = Care;
    p->pData = pData;
    p->pBuild = pBuild;
    Cec4_SatLoad( p );
    Vec_IntClear( p->vLinks );
    Vec_IntClear( p->vSideLits );
    Vec_IntClear( p->vSideKeys );
    if ( !Vec_IntSize(vSides) ) return;
    Vec_IntFill( p->vHeads, p->nLoaded, -1 );
    Vec_IntFill( p->vSeen, p->nLoaded, 0 );
    p->Stamp = 0;
    // Push in reverse so each incident list visits earlier hypotheses first.
    for ( i = Vec_IntSize(vSides) - 4; i >= 0; i -= 4 )
    {
        Lit = Vec_IntEntry( vSides, i + 2 );
        if ( !Lit ) continue;
        Side = Vec_IntSize( p->vSideLits );
        Vec_IntPush( p->vSideLits, Lit );
        Vec_IntPush( p->vSideKeys, Vec_IntEntry(vSides, i + 3) );
        for ( j = 0; j < 2; j++ )
        {
            int Endpoint = Vec_IntEntry(vSides, i + j), Var;
            if ( Endpoint < 0 ) continue;
            Var = Abc_Lit2Var( Endpoint );
            Cec4_SideIndex( p, Var, Side );
            pObj = Gia_ManObj( pCore, Var );
            if ( Gia_ObjIsAnd(pObj) )
            {
                Cec4_SideIndex( p, Gia_ObjFaninId0(pObj, Var), Side );
                Cec4_SideIndex( p, Gia_ObjFaninId1(pObj, Var), Side );
            }
        }
    }
    Vec_IntFill( p->vSideMarks, Vec_IntSize(p->vSideLits), 0 );
    p->nAvailableMax = Abc_MaxInt( p->nAvailableMax, Vec_IntSize(p->vSideLits) );
}

/**Function*************************************************************

  Synopsis    [Adds one current hypothesis to the query assumptions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec4_SideSelect( Cec4_Sat_t * p, int Side )
{
    int Lit, i;
    if ( Vec_IntEntry(p->vSideMarks, Side) == p->Stamp ) return;
    Vec_IntWriteEntry( p->vSideMarks, Side, p->Stamp );
    Lit = Vec_IntEntry( p->vSideLits, Side );
    if ( Lit < 0 )
    {
        Lit = p->pBuild( p->pData, Vec_IntEntry(p->vSideKeys, Side) );
        Vec_IntWriteEntry( p->vSideLits, Side, Lit );
    }
    if ( !Lit ) return;
    for ( i = 1; i < Vec_IntSize(p->vAssumps); i++ )
        if ( Vec_IntEntry(p->vAssumps, i) == (Lit ^ 1) ) return;
    Vec_IntPush( p->vAssumps, Lit ^ 1 );
    p->nSelected++;
}

/**Function*************************************************************

  Synopsis    [Selects nearby hypotheses with a bounded fanin traversal.]

  Description [Zero uses no side constraints. Finite limits prioritize
  hypotheses incident on the target cone, with deterministic breadth-first
  ordering and bounded search work. Minus one delays adding all hypotheses
  until the unconstrained query has a counterexample.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cec4_SatSelect( Cec4_Sat_t * p, int Lit )
{
    int i, Var, Link, Count;
    if ( p->nSides <= 0 || !Vec_IntSize(p->vSideLits) )
    {
        Vec_IntClear( p->vAssumps );
        Vec_IntPush( p->vAssumps, Lit );
        p->nQueries++;
        return p->vAssumps;
    }
    Vec_IntFillExtra( p->vSeen, Gia_ManObjNum(p->pCore), 0 );
    Vec_IntFillExtra( p->vHeads, Gia_ManObjNum(p->pCore), -1 );
    if ( p->Stamp == INT_MAX )
    {
        Vec_IntFill( p->vSeen, p->nLoaded, 0 );
        Vec_IntFill( p->vSideMarks, Vec_IntSize(p->vSideLits), 0 );
        p->Stamp = 0;
    }
    p->Stamp++;
    Vec_IntClear( p->vAssumps );
    Vec_IntPush( p->vAssumps, Lit );
    Vec_IntClear( p->vQueue );
    if ( p->nSides > 0 && Vec_IntSize(p->vSideLits) )
    {
        Vec_IntPush( p->vQueue, Abc_Lit2Var(Lit) );
        Vec_IntWriteEntry( p->vSeen, Abc_Lit2Var(Lit), p->Stamp );
        for ( i = 0; i < Vec_IntSize(p->vQueue) && i < CEC4_SIDE_SEARCH_LIMIT; i++ )
        {
            Gia_Obj_t * pObj;
            Var = Vec_IntEntry( p->vQueue, i );
            p->nSearch++;
            Count = 0;
            for ( Link = Vec_IntEntry(p->vHeads, Var); Link >= 0 && Count++ < CEC4_SIDE_ADJ_LIMIT;
                  Link = Vec_IntEntry(p->vLinks, Link + 1) )
            {
                Cec4_SideSelect( p, Vec_IntEntry(p->vLinks, Link) );
                if ( Vec_IntSize(p->vAssumps) > p->nSides ) goto finish;
            }
            pObj = Gia_ManObj( p->pCore, Var );
            if ( Gia_ObjIsAnd(pObj) )
            {
                int k, Fan;
                for ( k = 0; k < 2; k++ )
                {
                    Fan = k ? Gia_ObjFaninId1(pObj, Var) : Gia_ObjFaninId0(pObj, Var);
                    if ( Vec_IntEntry(p->vSeen, Fan) == p->Stamp ) continue;
                    Vec_IntWriteEntry( p->vSeen, Fan, p->Stamp );
                    Vec_IntPush( p->vQueue, Fan );
                }
            }
        }
    }
finish:
    p->nQueries++;
    return p->vAssumps;
}

/**Function*************************************************************

  Synopsis    [Adds all hypotheses only when the unconstrained query is SAT.]

  Description [The balanced conjunction represents the complete hypothesis
  set. Bounded mode already selected its side constraints before solving.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_SatRefine( Cec4_Sat_t * p )
{
    if ( p->nSides >= 0 || !Vec_IntSize(p->vSideLits) || Vec_IntSize(p->vAssumps) > 1 ) return 0;
    Vec_IntPush( p->vAssumps, p->Care );
    p->nSelected += Vec_IntSize( p->vSideLits );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Solves the selected query and extracts a sparse CI assignment.]

  Description [All assumption cones participate in justification. Return
  values match CBS: one is UNSAT, zero is SAT, and minus one is unknown.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_SatSolve( Cec4_Sat_t * p, Vec_Int_t * vModel, int nSpent )
{
    int i, Lit, Status = GLUCOSE3_UNDEC;
    // The shared API returns the low integer word of a cumulative counter.
    // Unsigned subtraction preserves bounded-query counts across its wrap.
    unsigned Used, Conflicts = (unsigned)bmcg3_sat_solver_conflictnum( p->pSat );
    Cec4_SatLoad( p );
    if ( bmcg3_sat_solver_read_unit(p->pSat, Vec_IntEntry(p->vAssumps, 0)) == 0 )
    {
        p->nConfLast = p->fConditional = 0;
        return 1;
    }
    for ( ;; )
    {
        Used = (unsigned)bmcg3_sat_solver_conflictnum(p->pSat) - Conflicts;
        if ( p->nConfs && Used + (unsigned)nSpent >= (unsigned)p->nConfs )
        {
            Status = GLUCOSE3_UNDEC;
            break;
        }
        Vec_IntClear( p->vRoots );
        Vec_IntForEachEntry( p->vAssumps, Lit, i )
            Vec_IntPush( p->vRoots, Abc_Lit2Var(Lit) );
        bmcg3_sat_solver_select_cones( p->pSat, Vec_IntArray(p->vRoots), Vec_IntSize(p->vRoots) );
        bmcg3_sat_solver_set_conflict_budget( p->pSat, p->nConfs ? p->nConfs - nSpent - (int)Used : 0 );
        Status = bmcg3_sat_solver_solve( p->pSat, Vec_IntArray(p->vAssumps), Vec_IntSize(p->vAssumps) );
        if ( Status != GLUCOSE3_SAT ) break;
        {
            int * pCex = bmcg3_sat_solver_read_cex( p->pSat );
            Vec_IntClear( vModel );
            for ( i = 1; i <= pCex[0]; i++ )
            {
                Gia_Obj_t * pObj = Gia_ManObj( p->pCore, Abc_Lit2Var(pCex[i]) );
                if ( Gia_ObjIsConst0(pObj) ) continue;
                assert( Gia_ObjIsCi(pObj) );
                Vec_IntPush( vModel, Abc_Var2Lit(Gia_ObjCioId(pObj), Abc_LitIsCompl(pCex[i])) );
            }
        }
        if ( !Cec4_SatRefine(p) ) break;
    }
    Used = (unsigned)bmcg3_sat_solver_conflictnum(p->pSat) - Conflicts;
    p->nConfLast = Used > INT_MAX ? INT_MAX : (int)Used;
    p->fConditional = 0;
    if ( Status == GLUCOSE3_UNSAT )
    {
        int * pFinal, nFinal = bmcg3_sat_solver_final( p->pSat, &pFinal );
        for ( i = 0; i < nFinal; i++ )
            if ( pFinal[i] != (Vec_IntEntry(p->vAssumps, 0) ^ 1) )
                p->fConditional = 1;
        p->nConditional += p->fConditional;
    }
    return Status == GLUCOSE3_UNSAT ? 1 : Status == GLUCOSE3_SAT ? 0 : -1;
}

/**Function*************************************************************

  Synopsis    [Reads an unconditional circuit consequence before the CBS probe.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_SatProven( Cec4_Sat_t * p, int Lit )
{
    return Abc_Lit2Var(Lit) < p->nLoaded && bmcg3_sat_solver_read_unit(p->pSat, Lit) == 0;
}

/**Function*************************************************************

  Synopsis    [Returns conflicts spent on the most recent query.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_SatConflicts( Cec4_Sat_t * p )
{
    return p->nConfLast;
}

/**Function*************************************************************

  Synopsis    [Checks whether the last proof actually used a side hypothesis.]

  Description [The final assumption core omits side constraints when the
  mismatch alone was inconsistent. Such proofs survive class refinement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_SatConditional( Cec4_Sat_t * p )
{
    return p->fConditional;
}

/**Function*************************************************************

  Synopsis    [Records only the assumptions used by the latest proof.]

  Description [The caller invalidates this proof when a recorded equality
  no longer belongs to the current inductive hypothesis set.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_SatDependencies( Cec4_Sat_t * p, Vec_Int_t * vDeps )
{
    int i, Start = Vec_IntSize(vDeps), * pFinal;
    int nFinal = bmcg3_sat_solver_final( p->pSat, &pFinal );
    Vec_IntPush( vDeps, 0 );
    for ( i = 0; i < nFinal; i++ )
        if ( pFinal[i] != (Vec_IntEntry(p->vAssumps, 0) ^ 1) )
            Vec_IntPush( vDeps, pFinal[i] ^ 1 );
    Vec_IntWriteEntry( vDeps, Start, Vec_IntSize(vDeps) - Start - 1 );
}

/**Function*************************************************************

  Synopsis    [Reports statistics for the current immutable core generation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec4_SatPrint( Cec4_Sat_t * p )
{
    Abc_Print( 1, "scorr4 current core: available=%d selected=%.2f/query searched=%.2f/query conflicts=%d learned=%d peak-available=%d selected-total=%lld conditional=%lld\n",
        Vec_IntSize(p->vSideLits), p->nQueries ? (double)p->nSelected/p->nQueries : 0,
        p->nQueries ? (double)p->nSearch/p->nQueries : 0,
        bmcg3_sat_solver_conflictnum(p->pSat), bmcg3_sat_solver_learntnum(p->pSat),
        p->nAvailableMax, (long long)p->nSelected, (long long)p->nConditional );
}

/**Function*************************************************************

  Synopsis    [Builds independent full-constraint induction obligations.]

  Description [This audit unrolls the original graph without speculative
  substitutions. The first k frames supply all equality hypotheses; only
  frame k supplies queried mismatches. The base case starts at zero.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Cec4_CheckBuild( Gia_Man_t * p, int nFrames, int fBase, Vec_Int_t * vPairs )
{
    Gia_Man_t * q = Gia_ManStart( Gia_ManObjNum(p) );
    Vec_Int_t * vMap = Vec_IntStart( Gia_ManObjNum(p) );
    Vec_Int_t * vRegs = Vec_IntStart( Gia_ManRegNum(p) );
    Vec_Int_t * vOuts = Vec_IntAlloc( 1000 );
    Vec_Int_t * vCare = Vec_IntAlloc( 1000 );
    Gia_Obj_t * pObj;
    int i, f, Repr, Lit, Care = 1;
    Gia_ManHashAlloc( q );
    if ( !fBase )
        Gia_ManForEachRo( p, pObj, i )
            Vec_IntWriteEntry( vRegs, i, Gia_ManAppendCi(q) );
    for ( f = 0; f < nFrames + !fBase; f++ )
    {
        Gia_ManForEachPi( p, pObj, i )
            Vec_IntWriteEntry( vMap, Gia_ObjId(p, pObj), Gia_ManAppendCi(q) );
        Gia_ManForEachRo( p, pObj, i )
            Vec_IntWriteEntry( vMap, Gia_ObjId(p, pObj), Vec_IntEntry(vRegs, i) );
        Gia_ManForEachAnd( p, pObj, i )
        {
            int a = Vec_IntEntry(vMap, Gia_ObjFaninId0(pObj, i)) ^ Gia_ObjFaninC0(pObj);
            int b = Vec_IntEntry(vMap, Gia_ObjFaninId1(pObj, i)) ^ Gia_ObjFaninC1(pObj);
            Vec_IntWriteEntry( vMap, i, Gia_ManHashAnd(q, a, b) );
        }
        Gia_ManForEachObj1( p, pObj, i )
        {
            Repr = Gia_ObjRepr( p, i );
            if ( Repr == GIA_VOID ) continue;
            Lit = Gia_ManHashXor( q, Vec_IntEntry(vMap, i),
                  Vec_IntEntry(vMap, Repr) ^ pObj->fPhase ^ Gia_ManObj(p, Repr)->fPhase );
            if ( !fBase && f < nFrames )
                Vec_IntPush( vCare, Lit ^ 1 );
            else
            {
                Vec_IntPush( vOuts, Lit );
                Vec_IntPushTwo( vPairs, Repr, i );
            }
        }
        Gia_ManForEachRi( p, pObj, i )
            Vec_IntWriteEntry( vRegs, i, Vec_IntEntry(vMap, Gia_ObjFaninId0p(p, pObj)) ^ Gia_ObjFaninC0(pObj) );
    }
    // A balanced conjunction avoids linear-depth audit cones on large
    // designs with many candidate equalities.
    while ( Vec_IntSize(vCare) > 1 )
    {
        int n = Vec_IntSize(vCare), k = 0;
        for ( i = 0; i + 1 < n; i += 2 )
            Vec_IntWriteEntry( vCare, k++, Gia_ManHashAnd(q, Vec_IntEntry(vCare, i), Vec_IntEntry(vCare, i + 1)) );
        if ( n & 1 ) Vec_IntWriteEntry( vCare, k++, Vec_IntEntry(vCare, n - 1) );
        Vec_IntShrink( vCare, k );
    }
    if ( Vec_IntSize(vCare) ) Care = Vec_IntEntry( vCare, 0 );
    Vec_IntForEachEntry( vOuts, Lit, i )
        Vec_IntWriteEntry( vOuts, i, Gia_ManHashAnd(q, Care, Lit) );
    Vec_IntForEachEntry( vOuts, Lit, i )
        Gia_ManAppendCo( q, Lit );
    Gia_ManHashStop( q );
    Vec_IntFree( vMap );
    Vec_IntFree( vRegs );
    Vec_IntFree( vOuts );
    Vec_IntFree( vCare );
    return q;
}

/**Function*************************************************************

  Synopsis    [Audits the final classes independently with Kissat.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec4_Check( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{
    int Phase, Status, Out;
    for ( Phase = 0; Phase < 2; Phase++ )
    {
        Vec_Int_t * vPairs = Vec_IntAlloc( 1000 ), * vCex = NULL;
        Vec_Str_t * vStatus = NULL;
        Gia_Man_t * pSrm = Cec4_CheckBuild( pAig, pPars->nFrames, !Phase, vPairs );
        Status = Cec_ManCorrKissatCertify( pSrm, vPairs, &vCex, &vStatus, &Out, 0 );
        Abc_Print( 1, "scorr4 audit %s: %s\n", Phase ? "step" : "base",
                   Status == 1 ? "PASS" : Status == 0 ? "FAIL" : "UNKNOWN" );
        Gia_ManStop( pSrm );
        Vec_IntFree( vPairs );
        Vec_IntFree( vCex );
        Vec_StrFree( vStatus );
        if ( Status != 1 ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes correspondence with bounded inductive side cones.]

  Description [Optional preprocessing performs one level-preserving rewriting
  pass on a private work GIA. The correspondence-only path remains available
  for callers comparing inductive engines on an unchanged AIG structure.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManLSCorrespondence4( Gia_Man_t * pAig, Cec_ParCor_t * pPars, int nSides, int fRewrite )
{
    Gia_Man_t * pWork, * pResult;
    abctime Start = Abc_Clock();
    if ( nSides < -1 ) return NULL;
    if ( pAig->pManTime || pAig->pAigExtra || Gia_ManRegBoxNum(pAig) )
    {
        Abc_Print( -1, "scorr4: flatten timing/register boxes before correspondence.\n" );
        return NULL;
    }
    // Keep unsupported-input diagnostics and the original input's capacity
    // check independent of preprocessing. Choices and an empty MUX table
    // can bypass rewriting without changing the correspondence interface.
    if ( !fRewrite || !Gia_ManIsNormalized(pAig) || Gia_ManHasChoices(pAig) ||
         pAig->pMuxes || Gia_ManXorNum(pAig) || Gia_ManMuxNum(pAig) || Gia_ManBufNum(pAig) ||
         pPars->nFrames < 1 || 3 * ((ABC_INT64_T)pPars->nFrames + 2) * Gia_ManObjNum(pAig) > INT_MAX - 64 )
        return Cec_ManLSCorrespondenceShared( pAig, pPars, nSides );
    pWork = Drw_ManRewrite( pAig, 1, 0 );
    if ( !pWork )
        return Cec_ManLSCorrespondenceShared( pAig, pPars, nSides );
    if ( pPars->fVerbose )
        Abc_Print( 1, "scorr4 rewriting: ANDs %d -> %d  time=%.3f sec\n",
            Gia_ManAndNum(pAig), Gia_ManAndNum(pWork), (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    if ( pPars->fKissatCert )
    {
        Gia_Man_t * pMiter = Gia_ManMiter( pAig, pWork, 0, 1, 0, 0, 0 );
        Cec_ParCec_t Pars;
        int Status = -1;
        // Treat register boundaries as combinational I/O. Keep audit
        // counterexamples on the temporary miter, not on the caller's GIA.
        if ( pMiter )
        {
            Cec_ManCecSetDefaultParams( &Pars );
            Pars.fVerbose = 0;
            Status = Cec_ManVerify( pMiter, &Pars );
            Gia_ManStop( pMiter );
        }
        Abc_Print( 1, "scorr4 audit rewriting: %s\n",
                   Status == 1 ? "PASS" : Status == 0 ? "FAIL" : "UNKNOWN" );
        if ( Status != 1 )
        {
            Gia_ManStop( pWork );
            return NULL;
        }
    }
    pResult = Cec_ManLSCorrespondenceShared( pWork, pPars, nSides );
    Gia_ManStop( pWork );
    if ( pPars->fVerbose )
        Abc_Print( 1, "scorr4 including rewriting: time=%.3f sec\n", (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    return pResult;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
