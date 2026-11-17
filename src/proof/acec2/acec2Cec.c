/**CFile****************************************************************

  FileName    [acec2Cec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Exact arithmetic proofs and normalization with a CEC fallback.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 11, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"
#include "sat/glucose2/AbcGlucose2.h"
#include "proof/cec/cec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

static int Acec2_ProveSweep( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline,
                             int nIters, int nConflicts, int fFixed, Vec_Int_t * vPairs );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks identical source topology without modifying scratch fields.]

  Description [Pin order, gate kinds and all complemented edges must agree.
  A mismatch requests ordinary verification; it is not a counterexample.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_SameStructure( Gia_Man_t * a, Gia_Man_t * b, Acec2_Par_t * pars, abctime Deadline )
{
    Gia_Obj_t * x, * y; int i;
    if ( Gia_ManObjNum(a) != Gia_ManObjNum(b) || !Vec_IntEqual(a->vCis, b->vCis) || !Vec_IntEqual(a->vCos, b->vCos) ) return 0;
    Gia_ManForEachObj1(a, x, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pars, Deadline) ) return -1;
        y = Gia_ManObj(b, i);
        if ( Gia_ObjIsCi(x) != Gia_ObjIsCi(y) || Gia_ObjIsCo(x) != Gia_ObjIsCo(y) || Gia_ObjIsAnd(x) != Gia_ObjIsAnd(y) ) return 0;
        if ( Gia_ObjIsCi(x) ) continue;
        if ( Gia_ObjFaninLit0p(a, x) != Gia_ObjFaninLit0p(b, y) ) return 0;
        if ( Gia_ObjIsCo(x) ) continue;
        if ( !Gia_ObjIsAnd(x) || Gia_ObjIsXor(x) != Gia_ObjIsXor(y) || Gia_ObjIsMux(a, x) != Gia_ObjIsMux(b, y) ||
             Gia_ObjFaninLit1p(a, x) != Gia_ObjFaninLit1p(b, y) ) return 0;
        if ( Gia_ObjIsMux(a, x) && Gia_ObjFaninLit2p(a, x) != Gia_ObjFaninLit2p(b, y) ) return 0;
    }
    return Acec2_Stop(pars, Deadline) ? -1 : 1;
}

/**Function*************************************************************

  Synopsis    [Simulates a counterexample on an untouched original GIA.]

  Description [Register pins are combinational inputs and outputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CexOutput( Gia_Man_t * p, Abc_Cex_t * pCex, int iOut )
{
    Vec_Bit_t * v = Vec_BitStart(Gia_ManObjNum(p));
    Gia_Obj_t * o; int i, a, b, c, res;
    Gia_ManForEachCi(p, o, i) Acec2_BitWrite(v, Gia_ObjId(p, o), Abc_InfoHasBit(pCex->pData, i));
    Gia_ManForEachAnd(p, o, i)
    {
        a = Vec_BitEntry(v, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o);
        b = Vec_BitEntry(v, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o);
        if ( Gia_ObjIsMux(p, o) )
        {
            c = Vec_BitEntry(v, Gia_ObjFaninId2(p, i)) ^ Gia_ObjFaninC2(p, o);
            res = c ? b : a;
        }
        else res = Gia_ObjIsXor(o) ? a ^ b : a & b;
        Acec2_BitWrite(v, i, res);
    }
    o = Gia_ManCo(p, iOut);
    res = Vec_BitEntry(v, Gia_ObjFaninId0p(p, o)) ^ Gia_ObjFaninC0(o);
    Vec_BitFree(v);
    return res;
}



/**Function*************************************************************

  Synopsis    [Runs a cone-focused query with the caller's resource limits.]

  Description [Glucose2 exposes an absolute deadline. When a caller also
  supplies a cancellation callback, short timed slices keep it responsive
  without introducing shared callback state or changing the solver API.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_SatQuery( bmcg2_sat_solver * pSat, int * pLits, int Limit, Acec2_Par_t * pPars, abctime Deadline )
{
    int status, start = bmcg2_sat_solver_conflictnum(pSat), used;
    abctime stop;
    bmcg2_sat_solver_start_new_round(pSat);
    bmcg2_sat_solver_mark_cone(pSat, Abc_Lit2Var(pLits[0]));
    bmcg2_sat_solver_mark_cone(pSat, Abc_Lit2Var(pLits[1]));
    do
    {
        if ( Acec2_Stop(pPars, Deadline) ) return GLUCOSE_UNDEC;
        used = bmcg2_sat_solver_conflictnum(pSat)-start;
        if ( Limit && used >= Limit ) return GLUCOSE_UNDEC;
        stop = Deadline;
        if ( pPars->pFuncStop && (!stop || stop > Abc_Clock()+CLOCKS_PER_SEC/10) ) stop = Abc_Clock()+CLOCKS_PER_SEC/10;
        bmcg2_sat_solver_set_runtime_limit(pSat, stop);
        bmcg2_sat_solver_set_conflict_budget(pSat, Limit ? Limit-used : 0);
        status = bmcg2_sat_solver_solve(pSat, pLits, 2);
    }
    while ( status == GLUCOSE_UNDEC && pPars->pFuncStop && !Acec2_Stop(pPars, Deadline) );
    return status;
}

/**Function*************************************************************

  Synopsis    [Simulates all outputs using one word of common CI patterns.]

  Description [Includes native XOR/MUX evaluation and uses private scratch.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wrd_t * Acec2_SimOutputs( Gia_Man_t * p, Vec_Wrd_t * vInputs, Acec2_Par_t * pPars, abctime Deadline )
{
    Vec_Wrd_t * v = Vec_WrdStart(Gia_ManObjNum(p)), * vOut = Vec_WrdAlloc(Gia_ManCoNum(p));
    Gia_Obj_t * o; int i; word a;
    Gia_ManForEachCi(p, o, i) Vec_WrdWriteEntry(v, Gia_ObjId(p, o), Vec_WrdEntry(vInputs, i));
    Gia_ManForEachAnd(p, o, i)
    {
        if ( (i & 4095) == 0 && Acec2_Stop(pPars, Deadline) )
        {
            Vec_WrdFree(v); Vec_WrdFree(vOut); return NULL;
        }
        Vec_WrdWriteEntry(v, i, Acec2_SimGate(p, i, v, 1, 0));
    }
    Gia_ManForEachCo(p, o, i)
    {
        a = Vec_WrdEntry(v, Gia_ObjFaninId0p(p, o));
        Vec_WrdPush(vOut, Gia_ObjFaninC0(o) ? ~a : a);
    }
    Vec_WrdFree(v);
    return vOut;
}

/**Function*************************************************************

  Synopsis    [Checks reconstruction against originals and finds easy CEXes.]

  Description [Returns 1 for a passed simulation check, 0 for a real original
  counterexample, -1 for cancellation, and -2 for a reconstruction mismatch.
  Passing simulation is a diagnostic guard, never an equivalence proof.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_CheckSimulationSeed( Gia_Man_t * p0, Gia_Man_t * p1, Gia_Man_t * pMiter,
                                    Acec2_Par_t * pPars, abctime Deadline, Abc_Cex_t ** ppCex, word * pState )
{
    Vec_Wrd_t * vInputs = Vec_WrdAlloc(Gia_ManCiNum(p0)), * v0, * v1, * vM = NULL;
    word state = *pState, diff;
    int i, bit, fail = -1, result = -1;
    *ppCex = NULL;
    for ( i = 0; i < Gia_ManCiNum(p0); i++ )
    {
        Acec2_Random(&state);
        Vec_WrdPush(vInputs, (state & ~ABC_CONST(3)) | ABC_CONST(2));
    }
    *pState = state;
    v0 = Acec2_SimOutputs(p0, vInputs, pPars, Deadline);
    v1 = Acec2_SimOutputs(p1, vInputs, pPars, Deadline);
    if ( pMiter ) vM = Acec2_SimOutputs(pMiter, vInputs, pPars, Deadline);
    if ( !v0 || !v1 || (pMiter && !vM) || Acec2_Stop(pPars, Deadline) ) goto finish;
    for ( i = 0; i < Gia_ManCoNum(p0); i++ )
    {
        if ( pMiter && (Vec_WrdEntry(vM, 2*i) != Vec_WrdEntry(v0, i) || Vec_WrdEntry(vM, 2*i+1) != Vec_WrdEntry(v1, i)) )
        {
            Abc_Print(-1, "&acec2: reconstruction simulation mismatch at output pair %d.\n", i);
            result = -2; goto finish;
        }
        if ( fail < 0 && Vec_WrdEntry(v0, i) != Vec_WrdEntry(v1, i) ) fail = i;
    }
    result = 1;
    if ( fail < 0 ) goto finish;
    diff = Vec_WrdEntry(v0, fail) ^ Vec_WrdEntry(v1, fail);
    for ( bit = 0; bit < 64; bit++ ) if ( (diff >> bit) & 1 ) break;
    *ppCex = Abc_CexAlloc(0, Gia_ManCiNum(p0), 1); (*ppCex)->iPo = fail;
    for ( i = 0; i < Gia_ManCiNum(p0); i++ )
        if ( (Vec_WrdEntry(vInputs, i) >> bit) & 1 ) Abc_InfoSetBit((*ppCex)->pData, i);
    result = 0;
finish:
    Vec_WrdFree(vInputs); Vec_WrdFreeP(&v0); Vec_WrdFreeP(&v1); Vec_WrdFreeP(&vM);
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks one deterministic word of patterns with private state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_CheckSimulation( Gia_Man_t * p0, Gia_Man_t * p1, Gia_Man_t * pMiter,
                           Acec2_Par_t * pPars, abctime Deadline, Abc_Cex_t ** ppCex )
{
    word state = ABC_CONST(0x9E3779B97F4A7C15);
    return Acec2_CheckSimulationSeed(p0, p1, pMiter, pPars, Deadline, ppCex, &state);
}

/**Function*************************************************************

  Synopsis    [Recognizes when primary outputs plausibly form an arithmetic word.]

  Description [This controls only a proof attempt, never its soundness.
  Mixed logic uses local arithmetic words before Boolean CEC instead.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_WholeWord( Acec2_Man_t * p )
{
    Gia_Obj_t * o;
    Vec_Bit_t * vDepends;
    int i, owner, tree = -1, largest = 0, count = 0;
    if ( !p || Gia_ManCoNum(p->pGia) < 4 || (ABC_INT64_T)4*p->nCovered < Gia_ManAndNum(p->pGia) ) return 0;
    Gia_ManForEachCo(p->pGia, o, i)
        count += Vec_IntEntry(p->vOwner, Gia_ObjFaninId0p(p->pGia, o)) >= 0;
    if ( (ABC_INT64_T)4*count >= (ABC_INT64_T)3*Gia_ManCoNum(p->pGia) ) return 1;
    // Synthesis can move the output drivers into a final carry network.
    // Follow dependence on one connected arithmetic region through that
    // logic instead of requiring the drivers themselves to be cell outputs.
    for ( i = 0; i < Vec_WecSize(p->vTrees); i++ )
        if ( Vec_IntSize(Vec_WecEntry(p->vTrees, i)) > largest )
        { largest = Vec_IntSize(Vec_WecEntry(p->vTrees, i)); tree = i; }
    if ( largest < 4 ) return 0;
    vDepends = Vec_BitStart(Gia_ManObjNum(p->pGia)); count = 0;
    Gia_ManForEachAnd(p->pGia, o, i)
    {
        owner = Vec_IntEntry(p->vOwner, i);
        Acec2_BitWrite(vDepends, i, (owner >= 0 && Acec2_Cell(p, owner/2)->Tree == tree) ||
            Vec_BitEntry(vDepends, Gia_ObjFaninId0(o, i)) || Vec_BitEntry(vDepends, Gia_ObjFaninId1(o, i)) ||
            (Gia_ObjIsMux(p->pGia, o) && Vec_BitEntry(vDepends, Gia_ObjFaninId2(p->pGia, i))));
    }
    Gia_ManForEachCo(p->pGia, o, i) count += Vec_BitEntry(vDepends, Gia_ObjFaninId0p(p->pGia, o));
    Vec_BitFree(vDepends);
    return (ABC_INT64_T)4*count >= (ABC_INT64_T)3*Gia_ManCoNum(p->pGia);
}

/**Function*************************************************************

  Synopsis    [Checks output pairs before sweeping or as a bounded fallback.]

  Description [Quick mode tries small queries and preserves proved output
  equalities in the miter. Full mode retries failed directions with growing
  conflict limits while a runtime budget remains. Each UNSAT direction is
  also retained as a clause. No speculative internal sweeping is performed.]

  SideEffects [Replaces proved second outputs in the owned comparison miter.]

  SeeAlso     []

***********************************************************************/
static int Acec2_CheckMiter( Gia_Man_t * p, Acec2_Par_t * pPars, abctime Deadline,
                             int fQuick, Abc_Cex_t ** ppCex )
{
    Vec_Bit_t * vUsed = Vec_BitStart(Gia_ManObjNum(p));
    Vec_Int_t * vVars = Vec_IntStartFull(Gia_ManObjNum(p)), * vDone = Vec_IntStart(Gia_ManCoNum(p)/2);
    bmcg2_sat_solver * pSat = NULL;
    Gia_Obj_t * o, * o0, * o1;
    int i, j, k, a, b, result = -1, status, lits[2], nPairs = Gia_ManCoNum(p)/2, nTriv = 0, nSat = 0, nVars = 1, nLeft, round = 0;
    int limit = fQuick ? 16 : pPars->nBTLimit;
    abctime localStop = Deadline, start = Abc_Clock();
    for ( i = 0; i < nPairs; i++ )
    {
        o0 = Gia_ManCo(p, 2*i); o1 = Gia_ManCo(p, 2*i+1);
        a = Gia_ObjFaninLit0p(p, o0); b = Gia_ObjFaninLit0p(p, o1);
        if ( a == b ) { nTriv++; Vec_IntWriteEntry(vDone, i, 3); continue; }
        if ( a == (b ^ 1) )
        {
            *ppCex = Abc_CexAlloc(0, Gia_ManCiNum(p), 1); (*ppCex)->iPo = i;
            result = 0; goto finish;
        }
        Acec2_BitWrite(vUsed, Abc_Lit2Var(a), 1); Acec2_BitWrite(vUsed, Abc_Lit2Var(b), 1);
    }
    if ( nTriv == nPairs ) { result = 1; goto finish; }
    for ( i = Gia_ManObjNum(p)-1; i > 0; i-- )
    {
        o = Gia_ManObj(p, i);
        if ( !Vec_BitEntry(vUsed, i) || !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(vUsed, Gia_ObjFaninId0(o, i), 1); Acec2_BitWrite(vUsed, Gia_ObjFaninId1(o, i), 1);
    }
    Vec_IntWriteEntry(vVars, 0, 0);
    Gia_ManForEachObj1(p, o, i) if ( Vec_BitEntry(vUsed, i) ) Vec_IntWriteEntry(vVars, i, nVars++);
    pSat = bmcg2_sat_solver_start(); bmcg2_sat_solver_set_jftr(pSat, 1); bmcg2_sat_solver_set_nvars(pSat, nVars);
    lits[0] = 1; status = bmcg2_sat_solver_addclause(pSat, lits, 1); assert(status);
    Gia_ManForEachAnd(p, o, i)
    {
        if ( (i & 255) == 0 && Acec2_Stop(pPars, localStop) ) goto finish;
        if ( !Vec_BitEntry(vUsed, i) ) continue;
        bmcg2_sat_solver_add_and(pSat, Vec_IntEntry(vVars, i), Vec_IntEntry(vVars, Gia_ObjFaninId0(o, i)),
            Vec_IntEntry(vVars, Gia_ObjFaninId1(o, i)), Gia_ObjFaninC0(o), Gia_ObjFaninC1(o), 0);
        a = Abc_Var2Lit(Vec_IntEntry(vVars, Gia_ObjFaninId0(o, i)), Gia_ObjFaninC0(o));
        b = Abc_Var2Lit(Vec_IntEntry(vVars, Gia_ObjFaninId1(o, i)), Gia_ObjFaninC1(o));
        if ( a > b ) ABC_SWAP(int, a, b);
        bmcg2_sat_solver_set_var_fanin_lit(pSat, Vec_IntEntry(vVars, i), a, b);
    }
    do
    {
        nLeft = 0; round++;
        for ( i = 0; i < nPairs; i++ )
        {
            if ( Acec2_Stop(pPars, localStop) ) goto finish;
            if ( Vec_IntEntry(vDone, i) == 3 ) continue;
            o0 = Gia_ManCo(p, 2*i); o1 = Gia_ManCo(p, 2*i+1);
            a = Gia_ObjFaninLit0p(p, o0); b = Gia_ObjFaninLit0p(p, o1);
            for ( j = 0; j < 2; j++ )
            {
                if ( Vec_IntEntry(vDone, i) & (1 << j) ) continue;
                if ( fQuick && (nSat >= (fQuick == 2 ? (nPairs-nTriv <= 256 ? 4096 : 64) : 256) ||
                     (fQuick == 2 && bmcg2_sat_solver_conflictnum(pSat) >= 4000)) ) goto finish;
                lits[0] = Abc_Var2Lit(Vec_IntEntry(vVars, Abc_Lit2Var(a)), (a & 1) ^ j);
                lits[1] = Abc_Var2Lit(Vec_IntEntry(vVars, Abc_Lit2Var(b)), (b & 1) ^ j ^ 1);
                status = Acec2_SatQuery(pSat, lits, limit, pPars, localStop); nSat++;
                if ( status == GLUCOSE_UNDEC )
                {
                    continue;
                }
                if ( status == GLUCOSE_UNSAT )
                {
                    Vec_IntWriteEntry(vDone, i, Vec_IntEntry(vDone, i) | (1 << j));
                    lits[0] ^= 1; lits[1] ^= 1;
                    status = bmcg2_sat_solver_addclause(pSat, lits, 2); assert(status);
                    continue;
                }
                *ppCex = Abc_CexAlloc(0, Gia_ManCiNum(p), 1); (*ppCex)->iPo = i;
                {
                    int * pModel = bmcg2_sat_solver_read_cex(pSat);
                    Vec_Int_t * vValues = Vec_IntStart(nVars);
                    if ( pModel )
                        for ( k = 1; k <= pModel[0]; k++ ) Vec_IntWriteEntry(vValues, Abc_Lit2Var(pModel[k]), !Abc_LitIsCompl(pModel[k]));
                    Gia_ManForEachCi(p, o, k)
                        if ( Vec_IntEntry(vVars, Gia_ObjId(p, o)) >= 0 && Vec_IntEntry(vValues, Vec_IntEntry(vVars, Gia_ObjId(p, o))) )
                            Abc_InfoSetBit((*ppCex)->pData, k);
                    Vec_IntFree(vValues);
                }
                result = 0; goto finish;
            }
            if ( Vec_IntEntry(vDone, i) == 3 ) Gia_ManPatchCoDriver(p, 2*i+1, a);
            else nLeft++;
        }
        if ( !nLeft ) { result = 1; goto finish; }
        if ( fQuick ) break;
        limit = limit > ABC_INT_MAX/4 ? 0 : 4*limit;
        if ( pPars->fVerbose ) Abc_Print(1, "Output SAT retry: %d pairs remain, conflict budget = %d.\n", nLeft, limit);
    }
    while ( !Acec2_Stop(pPars, localStop) );
finish:
    if ( pPars->fVerbose )
        Abc_Print(1, "%s output check: structural = %d / %d, queries = %d, rounds = %d, time = %.3f sec.\n",
            fQuick ? "Quick" : "Final", nTriv, nPairs, nSat, round, (double)(Abc_Clock()-start)/CLOCKS_PER_SEC);
    if ( pSat ) bmcg2_sat_solver_stop(pSat);
    Vec_BitFree(vUsed); Vec_IntFree(vVars); Vec_IntFree(vDone);
    return result;
}

/**Function*************************************************************

  Synopsis    [Checks a completed reconstruction with bounded Boolean effort.]

  Description [At most 64 queries (4096 for a small remaining interface)
  and 4000 accumulated conflicts, with
  sixteen conflicts per query. An unresolved output does not prevent
  proving the remaining outputs before ordinary CEC checks the reduced
  comparison. Cheap completed queries do not prevent checking a wider
  output interface.
  A bounded sweep follows these queries. Completed output and internal
  equalities can be retained by the caller across arithmetic passes.
  Only the caller's deadline applies; machine load does not select a local
  proof budget. A counterexample is left for the original-design fallback.]

  SideEffects [May simplify outputs of the private miter.]

  SeeAlso     []

***********************************************************************/
int Acec2_ProveConcreteEx( Gia_Man_t * p, Acec2_Par_t * pPars, abctime Deadline, Vec_Int_t * vPairs, int fWide )
{
    Abc_Cex_t * pCex = NULL;
    Vec_Int_t * vOld = vPairs ? Vec_IntAlloc(Gia_ManCoNum(p)) : NULL;
    int i, left = 0, result;
    if ( vOld )
        for ( i = 0; i < Gia_ManCoNum(p); i++ ) Vec_IntPush(vOld, Gia_ObjFaninLit0p(p, Gia_ManCo(p, i)));
    result = Acec2_CheckMiter(p, pPars, Deadline, 2, &pCex);
    if ( pCex ) Abc_CexFree(pCex);
    if ( result < 0 && !Acec2_Stop(pPars, Deadline) )
    {
        for ( i = 0; i < Gia_ManCoNum(p); i += 2 )
            left += Gia_ObjFaninLit0p(p, Gia_ManCo(p, i)) != Gia_ObjFaninLit0p(p, Gia_ManCo(p, i+1));
        if ( left <= 256 || fWide )
            result = Acec2_ProveSweep(p, pPars, Deadline, vPairs ? 8*Abc_MaxInt(1, Abc_MinInt(fWide, 4)) : 128, 1000, 1, vPairs);
    }
    if ( vOld )
        for ( i = 0; i < Gia_ManCoNum(p); i += 2 )
            if ( Vec_IntEntry(vOld, i) != Vec_IntEntry(vOld, i+1) &&
                 Gia_ObjFaninLit0p(p, Gia_ManCo(p, i)) == Gia_ObjFaninLit0p(p, Gia_ManCo(p, i+1)) )
                Vec_IntPushTwo(vPairs, Vec_IntEntry(vOld, i), Vec_IntEntry(vOld, i+1));
    Vec_IntFreeP(&vOld);
    return result == 1;
}

/**Function*************************************************************

  Synopsis    [Abstracts common boundaries to prove the remaining Boolean logic.]

  Description [A shared node is replaced by the same free input on both
  sides. Only equivalence of this overapproximation transfers to the original
  miter; counterexamples and unknown results retain the concrete fallback.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Acec2_AbstractShared( Gia_Man_t * p, Acec2_Par_t * pPars, abctime Deadline )
{
    Gia_Man_t * q = NULL;
    Vec_Int_t * vColors = Vec_IntStart(Gia_ManObjNum(p)), * vUsed = Vec_IntStart(Gia_ManObjNum(p));
    Vec_Int_t * vMap = Vec_IntStart(Gia_ManObjNum(p));
    Gia_Obj_t * o;
    int i, color, id, a, b;
    Gia_ManForEachCo(p, o, i)
    {
        id = Gia_ObjFaninId0p(p, o);
        Vec_IntWriteEntry(vColors, id, Vec_IntEntry(vColors, id) | (1 << (i & 1)));
        Vec_IntWriteEntry(vUsed, id, 1);
    }
    Gia_ManForEachAndReverse(p, o, i)
    {
        if ( (i & 1023) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
        color = Vec_IntEntry(vColors, i);
        a = Gia_ObjFaninId0(o, i); b = Gia_ObjFaninId1(o, i);
        Vec_IntWriteEntry(vColors, a, Vec_IntEntry(vColors, a) | color);
        Vec_IntWriteEntry(vColors, b, Vec_IntEntry(vColors, b) | color);
    }
    Gia_ManForEachAndReverse(p, o, i)
        if ( Vec_IntEntry(vUsed, i) && Vec_IntEntry(vColors, i) != 3 )
        {
            Vec_IntWriteEntry(vUsed, Gia_ObjFaninId0(o, i), 1);
            Vec_IntWriteEntry(vUsed, Gia_ObjFaninId1(o, i), 1);
        }
    q = Gia_ManStart(1000); Gia_ManHashAlloc(q);
    Gia_ManForEachObj1(p, o, i)
        if ( !Gia_ObjIsCo(o) && Vec_IntEntry(vUsed, i) && (Gia_ObjIsCi(o) || Vec_IntEntry(vColors, i) == 3) )
            Vec_IntWriteEntry(vMap, i, Gia_ManAppendCi(q));
    Gia_ManForEachAnd(p, o, i)
        if ( Vec_IntEntry(vUsed, i) && Vec_IntEntry(vColors, i) != 3 )
            Vec_IntWriteEntry(vMap, i, Gia_ManHashAnd(q,
                Vec_IntEntry(vMap, Gia_ObjFaninId0(o, i)) ^ Gia_ObjFaninC0(o),
                Vec_IntEntry(vMap, Gia_ObjFaninId1(o, i)) ^ Gia_ObjFaninC1(o)));
    Gia_ManForEachCo(p, o, i)
        Gia_ManAppendCo(q, Vec_IntEntry(vMap, Gia_ObjFaninId0p(p, o)) ^ Gia_ObjFaninC0(o));
    Gia_ManHashStop(q);
finish:
    Vec_IntFree(vColors); Vec_IntFree(vUsed); Vec_IntFree(vMap);
    return q;
}

/**Function*************************************************************

  Synopsis    [Runs ordinary correspondence with a fixed iteration budget.]

  Description [This internal probe never inherits a local wall-clock slice.
  The caller's absolute deadline and cancellation still bound every solver.
  The returned result concerns all original adjacent output pairs.]

  SideEffects [Optionally collects only completed, nonspeculative equalities.]

  SeeAlso     []

***********************************************************************/
static int Acec2_ProveSweep( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline,
                             int nIters, int nConflicts, int fFixed, Vec_Int_t * vPairs )
{
    Gia_Man_t * p, * q;
    Vec_Int_t * vOrig = NULL;
    Cec_ParFra_t Pars; Cec_ParLimit_t Limits; Cec_ParEffort_t Effort;
    int i, a, b, result = -1;
    abctime clk = Abc_Clock();
    if ( Acec2_Stop(pPars, Deadline) || (Gia_ManCoNum(pMiter) & 1) ) return -1;
    p = Gia_ManDup(pMiter); Gia_ManEquivFixOutputPairs(p);
    q = Gia_ManCleanup(p);
    if ( vPairs )
    {
        vOrig = Vec_IntStartFull(Gia_ManObjNum(q)); Vec_IntWriteEntry(vOrig, 0, 0);
        for ( i = 1; i < Gia_ManObjNum(p); i++ )
            if ( !Gia_ObjIsCo(Gia_ManObj(p, i)) && ~Gia_ManObj(p, i)->Value )
                Vec_IntWriteEntry(vOrig, Gia_ManObj(p, i)->Value >> 1, 2*i ^ (Gia_ManObj(p, i)->Value & 1));
    }
    Gia_ManStop(p); p = q;
    Cec_ManFraSetDefaultParams(&Pars);
    Pars.nItersMax = nIters; Pars.nBTLimit = nConflicts;
    Pars.nWords = 4; Pars.nRounds = 8;
    Pars.fSatSweeping = fFixed;
    Pars.fCheckMiter = 1; Pars.fDualOut = 1;
    Pars.fUseOrigIds = Pars.fUseProvedIds = vPairs != NULL;
    Limits.TimeToStop = Deadline; Limits.RunId = pPars->RunId;
    Limits.pFuncStop = pPars->pFuncStop; Limits.pCancelled = pPars->pCancelled; Pars.pLimits = &Limits;
    memset(&Effort, 0, sizeof(Effort));
    {
        int scale = vPairs ? Abc_MaxInt(1, Abc_MinInt(nIters/8, 4)) : 1;
        Effort.nCallsMax = 512*scale; Effort.nConflictsMax = 4000*scale; Pars.pEffort = &Effort;
    }
    q = Cec_ManSatSweeping(p, &Pars, 1);
    if ( q )
    {
        result = 1;
        for ( i = 0; i < Gia_ManCoNum(q); i += 2 )
            if ( Gia_ObjFaninLit0p(q, Gia_ManCo(q, i)) != Gia_ObjFaninLit0p(q, Gia_ManCo(q, i+1)) ) result = -1;
            else if ( vPairs ) Gia_ManPatchCoDriver(pMiter, i+1, Gia_ObjFaninLit0p(pMiter, Gia_ManCo(pMiter, i)));
    }
    else if ( p->pCexComb && Gia_ManVerifyCex(p, p->pCexComb, 1) ) result = 0;
    if ( vPairs && p->vIdsEquiv )
    {
        Gia_ManSetPhase(p);
        for ( i = 0; i < Vec_IntSize(p->vIdsEquiv); i += 2 )
        {
            a = Vec_IntEntry(p->vIdsEquiv, i); b = Vec_IntEntry(p->vIdsEquiv, i+1);
            if ( Vec_IntEntry(vOrig, a) < 0 || Vec_IntEntry(vOrig, b) < 0 ) continue;
            Vec_IntPushTwo(vPairs, Vec_IntEntry(vOrig, a) ^ Gia_ManObj(p, a)->fPhase,
                                  Vec_IntEntry(vOrig, b) ^ Gia_ManObj(p, b)->fPhase);
        }
    }
    if ( Acec2_Stop(pPars, Deadline) ) result = -1;
    if ( q ) Gia_ManStop(q);
    if ( pPars->fVerbose ) Abc_Print(1, "Bounded CEC probe: ANDs = %d, iterations = %d, conflicts per query = %d, result = %d, time = %.3f sec.\n",
        Gia_ManAndNum(pMiter), nIters, nConflicts, result, (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    if ( pPars->fVerbose && Pars.pEffort ) Abc_Print(1, "CEC probe effort: queries = %d / %d, conflicts = %lld / %lld%s.\n",
        Effort.nCalls, Effort.nCallsMax, (long long)Effort.nConflicts, (long long)Effort.nConflictsMax,
        Cec_ManEffortStopped(&Effort) ? "; effort limit" : "");
    Vec_IntFreeP(&vOrig); Gia_ManStop(p); return result;
}

/**Function*************************************************************

  Synopsis    [Runs a small ordinary CEC probe during arithmetic discovery.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveBounded( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline, int nIters )
{
    return Acec2_ProveSweep(pMiter, pPars, Deadline, nIters, 100, 0, NULL);
}

/**Function*************************************************************

  Synopsis    [Bounds the initial whole-output attempt before component matching.]

  Description [Restores per-analysis effort parameters on every result.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_InitialPolynomial( Acec2_Man_t * p0, Acec2_Man_t * p1, abctime Deadline, Abc_Cex_t ** ppCex )
{
    int saved[2] = { p0->Pars.nCecPolyLimit, p1->Pars.nCecPolyLimit };
    int side, result, limit = 65536;
    // Better recognition can make another design eligible for this attempt.
    // Start with bounded work so failed extraction still reaches matching
    // and ordinary CEC. Later component attempts have their own effort tiers.
    for ( side = 0; side < 2; side++ )
    {
        Acec2_Man_t * p = side ? p1 : p0;
        if ( p->Pars.nCecOptions & ACEC2_CEC_DEFER )
            p->Pars.nCecPolyLimit = saved[side] > 0 ? Abc_MinInt(saved[side], limit) : limit;
    }
    if ( p0->Pars.fVerbose )
        Abc_Print(1, "Initial whole-output polynomial: term limits = %d / %d.\n", p0->Pars.nCecPolyLimit, p1->Pars.nCecPolyLimit);
    result = Acec2_PolyCompare(p0, p1, Deadline, ppCex);
    p0->Pars.nCecPolyLimit = saved[0]; p1->Pars.nCecPolyLimit = saved[1];
    return result;
}

/**Function*************************************************************

  Synopsis    [Compares arithmetic boundaries and proves the remaining logic.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_SolveInt( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Acec2_Par_t * pPars, Abc_Cex_t ** ppCex, abctime clk )
{
    Acec2_Par_t Pars = *pPars, PlainPars;
    Acec2_Man_t * p0 = NULL, * p1 = NULL;
    Gia_Man_t * pMiter = NULL, * pReduced = NULL;
    Abc_Cex_t * pCex = NULL;
    Acec2_NormStats_t Stats;
    Cec_ParCec_t ParsCec; Cec_ParLimit_t Limits;
    abctime stage, CecTime = 0, Deadline = pPars->nTimeLimit ? clk+(abctime)pPars->nTimeLimit*CLOCKS_PER_SEC : 0;
    const char * pReason = "conflict or iteration limit";
    const char * pStage = "simulation";
    int result = -1, sim, round, nGuardRounds, fPlain = 0, fCancelled = 0;
    word state = ABC_CONST(0xD1B54A32D192ED03);
    if ( !Pars.pCancelled ) Pars.pCancelled = &fCancelled;
    memset(&Stats, 0, sizeof(Stats));
    pPars = &Pars;
    if ( ppCex ) *ppCex = NULL;
    if ( !pGia0 || !pGia1 || Gia_ManCiNum(pGia0) != Gia_ManCiNum(pGia1) ||
         Gia_ManCoNum(pGia0) != Gia_ManCoNum(pGia1) || Gia_ManRegNum(pGia0) != Gia_ManRegNum(pGia1) )
    {
        Abc_Print(-1, "&acec2: CI, CO, and register counts must agree.\n"); return -1;
    }
    if ( pPars->nCuts < 1 || pPars->nCuts > 64 || pPars->nTimeLimit < 0 || pPars->nBTLimit < 0 || pPars->nMaxWidth < 1 ) return -1;
    if ( Acec2_Stop(pPars, Deadline) ) goto finish;
    sim = Acec2_SameStructure(pGia0, pGia1, pPars, Deadline);
    if ( sim < 0 ) goto finish;
    if ( sim == 1 )
    {
        result = 1; pStage = "identical source topology";
        if ( pPars->fVerbose ) Abc_Print(1, "Source topology and pin order are identical.\n");
        goto finish;
    }
    sim = Acec2_CheckSimulation(pGia0, pGia1, NULL, pPars, Deadline, &pCex);
    if ( sim == 0 ) { result = 0; goto validate; }
    if ( sim < 0 ) goto finish;
    // Try ordinary CEC before paying for arithmetic recognition. A local
    // probe deadline never cancels the caller or establishes an equality.
    // Only a completed proof terminates this path.
    if ( pPars->fSweep && pPars->fNormalize )
    {
        Acec2_NormStats_t plainStats;
        abctime stop, quantum = pPars->nTimeLimit > 0 && pPars->nTimeLimit < 10 ?
            (abctime)pPars->nTimeLimit*CLOCKS_PER_SEC/40 : CLOCKS_PER_SEC/4;
        stage = Abc_Clock(); stop = stage+quantum;
        if ( Deadline && stop > Deadline ) stop = Deadline;
        PlainPars = *pPars; PlainPars.fNormalize = PlainPars.fAlgebra = PlainPars.fSweep = 0; PlainPars.nCecOptions = 0;
        pStage = "initial CEC";
        pMiter = Acec2_BuildMiterEx(pGia0, pGia1, NULL, NULL, &PlainPars, stop, &plainStats);
        if ( pMiter )
        {
            Cec_ManCecSetDefaultParams(&ParsCec);
            ParsCec.nBTLimit = pPars->nBTLimit; ParsCec.fSilent = 1; ParsCec.fVerbose = 0;
            Limits.TimeToStop = stop; Limits.RunId = pPars->RunId;
            Limits.pFuncStop = pPars->pFuncStop; Limits.pCancelled = pPars->pCancelled;
            result = Cec_ManVerifyWithLimits(pMiter, &ParsCec, &Limits, &pReduced);
        }
        CecTime = Abc_Clock()-stage;
        if ( pPars->fVerbose ) Abc_Print(1, "Initial plain CEC: result = %d, time = %.3f sec.\n", result, (double)CecTime/CLOCKS_PER_SEC);
        if ( Acec2_Stop(pPars, Deadline) ) { result = -1; goto finish; }
        if ( result == 1 ) goto finish;
        if ( result == 0 ) { pCex = pMiter->pCexComb; pMiter->pCexComb = NULL; goto validate; }
        result = -1;
        if ( pReduced ) { Gia_ManStop(pReduced); pReduced = NULL; }
        if ( pMiter ) { Gia_ManStop(pMiter); pMiter = NULL; }
        if ( Acec2_Stop(pPars, Deadline) ) goto finish;
    }
    stage = Abc_Clock();
    if ( pPars->fNormalize )
    {
        pStage = "detection";
        p0 = Acec2_AnalyzeCec(pGia0, pPars, Deadline);
        if ( !p0 || Acec2_Stop(pPars, Deadline) ) goto finish;
        p1 = Acec2_AnalyzeCec(pGia1, pPars, Deadline);
        if ( !p1 || Acec2_Stop(pPars, Deadline) ) goto finish;
        if ( pPars->fVerbose ) { Acec2_Print(p0, stdout, 0); Acec2_Print(p1, stdout, 0); }
    }
    if ( pPars->fVerbose ) Abc_Print(1, "Analysis stage = %.3f sec.\n", (double)(Abc_Clock()-stage)/CLOCKS_PER_SEC);
    if ( !(pPars->nCecOptions & ACEC2_CEC_RECORDS_ONLY) && Acec2_WholeWord(p0) && Acec2_WholeWord(p1) )
    {
        pStage = "arithmetic proof";
        result = Acec2_InitialPolynomial(p0, p1, Deadline, &pCex);
        if ( result == 0 ) goto validate;
        if ( result == 1 )
        {
            for ( round = 0; round < 64; round++ )
            {
                sim = Acec2_CheckSimulationSeed(pGia0, pGia1, NULL, pPars, Deadline, &pCex, &state);
                if ( sim != 1 )
                {
                    if ( sim == 0 ) Abc_Print(-1, "&acec2: arithmetic proof failed the simulation guard.\n");
                    result = sim; goto validate;
                }
            }
            if ( pPars->fVerbose ) Abc_Print(1, "Arithmetic proof guard: 4096 patterns passed.\n");
            goto finish;
        }
    }
    else if ( pPars->fVerbose && p0 && p1 && pPars->fAlgebra )
        Abc_Print(1, "Polynomial: whole-output attempt skipped; using internal arithmetic words.\n");
    stage = Abc_Clock();
    pMiter = Acec2_BuildMiterBudget(pGia0, pGia1, p0, p1, pPars, Deadline, CecTime, &Stats);
    pStage = Stats.iLastStage == 3 ? "surrounding CEC" : Stats.iLastStage == 2 ? "arithmetic proof" : "boundary recovery";
    if ( Acec2_Stop(pPars, Deadline) ) goto finish;
    if ( !pMiter ) goto plain;
    if ( pPars->fVerbose )
    {
        Abc_Print(1, "Normalization: regions = %d, growth-limited regions retained = %d, ANDs = %d -> %d, time = %.3f sec.\n",
            Stats.nRegions, Stats.nSkipped, Stats.nBefore, Stats.nAfter, (double)(Abc_Clock()-stage)/CLOCKS_PER_SEC);
        Abc_Print(1, "Normalized roots: candidates = %d / %d, shared = %d / %d, newly shared = %d / %d, selected = %d / %d.\n",
            Stats.nRoots[0], Stats.nRoots[1], Stats.nMatched[0], Stats.nMatched[1], Stats.nNew[0], Stats.nNew[1], Stats.nSelected[0], Stats.nSelected[1]);
        Abc_Print(1, "Local polynomials: completed = %d / %d, attempted = %d / %d.\n",
            Stats.nPolyDone[0], Stats.nPolyDone[1], Stats.nPolyTried[0], Stats.nPolyTried[1]);
        Abc_Print(1, "Certified expressions: normalized = %d / %d.\n", Stats.nExpressions[0], Stats.nExpressions[1]);
        Abc_Print(1, "Local polynomial reuse: requests = %d / %d, including effort limits = %d / %d.\n",
            Stats.nPolyReused[0], Stats.nPolyReused[1], Stats.nPolyLimits[0], Stats.nPolyLimits[1]);
        Abc_Print(1, "Proved component matches: words = %d, new root aliases = %d.\n", Stats.nMacroWords, Stats.nMacroBits);
        Abc_Print(1, "Aliases proved by exact cut matching = %d.\n", Stats.nTruthBits);
        Abc_Print(1, "Matched checked component records: words = %d, new bit equalities = %d.\n", Stats.nRecordWords, Stats.nRecordBits);
        Abc_Print(1, "Standalone record matches: words = %d, new bit equalities = %d.\n", Stats.nProfileWords, Stats.nProfileBits);
        Abc_Print(1, "Arithmetic time by step: setup = %.3f, records = %.3f, local = %.3f, matching = %.3f, rebuild = %.3f, CEC = %.3f, profile = %.3f, other = %.3f sec.\n",
            (double)Stats.TimeSetup/CLOCKS_PER_SEC, (double)Stats.TimeRecords/CLOCKS_PER_SEC,
            (double)Stats.TimeLocal/CLOCKS_PER_SEC, (double)Stats.TimeMatch/CLOCKS_PER_SEC,
            (double)Stats.TimeRebuild/CLOCKS_PER_SEC, (double)Stats.TimeCec/CLOCKS_PER_SEC,
            (double)(Stats.TimeProfile[0]+Stats.TimeProfile[1])/CLOCKS_PER_SEC,
            (double)(Stats.TimeTotal-Stats.TimeSetup-Stats.TimeRecords-Stats.TimeLocal-Stats.TimeMatch-Stats.TimeRebuild-Stats.TimeCec-Stats.TimeProfile[0]-Stats.TimeProfile[1])/CLOCKS_PER_SEC);
        if ( Stats.TimeProfile[0] || Stats.TimeProfile[1] )
            Abc_Print(1, "Standalone source records = %d/%d; analysis limits = %d/%d; time = %.3f/%.3f sec.\n",
                Stats.nProfileRecords[0], Stats.nProfileRecords[1], Stats.fProfileLimited[0], Stats.fProfileLimited[1],
                (double)Stats.TimeProfile[0]/CLOCKS_PER_SEC, (double)Stats.TimeProfile[1]/CLOCKS_PER_SEC);
        Abc_Print(1, "Arithmetic effort: final tier = %d, effort escalations = %d.\n", Stats.nEffortTier, Stats.nEffortEscalations);
        Abc_Print(1, "Arithmetic passes = %d%s.\n", Stats.nPasses, Stats.fPassLimit ? "; pass limit reached" : "");
    }
guard:
    pStage = "reconstruction guard";
    stage = Abc_Clock();
    nGuardRounds = Stats.nMacroBits || Stats.nRecordBits || ((Stats.nPolyDone[0]+Stats.nPolyDone[1]+Stats.nExpressions[0]+Stats.nExpressions[1]) &&
        (Stats.nSelected[0]+Stats.nSelected[1])) ? 64 : 1;
    for ( round = 0; round < nGuardRounds; round++ )
    {
        sim = Acec2_CheckSimulationSeed(pGia0, pGia1, pMiter, pPars, Deadline, &pCex, &state);
        if ( sim == -2 )
        {
            pReason = "reconstruction simulation mismatch";
            if ( !fPlain ) goto plain;
            goto finish;
        }
        if ( sim == 0 ) { result = 0; goto validate; }
        if ( sim < 0 ) goto finish;
    }
    if ( pPars->fVerbose ) Abc_Print(1, "Reconstruction guard: %d patterns passed in %.3f sec.\n", 64*nGuardRounds, (double)(Abc_Clock()-stage)/CLOCKS_PER_SEC);
    if ( Stats.fContextProved ) { result = 1; goto finish; }
    pStage = "surrounding CEC";
    result = Acec2_CheckMiter(pMiter, pPars, Deadline, 1, &pCex);
    if ( result >= 0 || Acec2_Stop(pPars, Deadline) ) goto validate;
    if ( pPars->fSweep )
    {
        Cec_ManCecSetDefaultParams(&ParsCec);
        ParsCec.nBTLimit = pPars->nBTLimit; ParsCec.fSilent = 1; ParsCec.fVerbose = pPars->fVerbose;
        Limits.TimeToStop = Deadline; Limits.RunId = pPars->RunId; Limits.pFuncStop = pPars->pFuncStop; Limits.pCancelled = pPars->pCancelled;
        stage = Abc_Clock();
        result = Cec_ManVerifyWithLimits(pMiter, &ParsCec, &Limits, &pReduced);
        if ( pPars->fVerbose ) Abc_Print(1, "CEC stage = %.3f sec. Result = %d.\n", (double)(Abc_Clock()-stage)/CLOCKS_PER_SEC, result);
        if ( result == 0 ) { pCex = pMiter->pCexComb; pMiter->pCexComb = NULL; }
        if ( result >= 0 || Acec2_Stop(pPars, Deadline) ) goto validate;
    }
    result = Acec2_CheckMiter(pReduced ? pReduced : pMiter, pPars, Deadline, 0, &pCex);
    goto validate;
plain:
    if ( Acec2_Stop(pPars, Deadline) ) goto finish;
    Abc_Print(1, "Arithmetic reconstruction rejected; checking the original miter.\n");
    if ( pMiter ) { Gia_ManStop(pMiter); pMiter = NULL; }
    if ( pCex ) { Abc_CexFree(pCex); pCex = NULL; }
    PlainPars = *pPars; PlainPars.fNormalize = PlainPars.fAlgebra = PlainPars.fSweep = 0;
    pMiter = Acec2_BuildMiterEx(pGia0, pGia1, NULL, NULL, &PlainPars, Deadline, &Stats);
    if ( !pMiter || Acec2_Stop(pPars, Deadline) ) goto finish;
    fPlain = 1;
    goto guard;
validate:
    if ( result == 0 )
    {
        if ( !pCex || pCex->iPo < 0 || pCex->iPo >= Gia_ManCoNum(pGia0) ||
             Acec2_CexOutput(pGia0, pCex, pCex->iPo) == Acec2_CexOutput(pGia1, pCex, pCex->iPo) )
        {
            pReason = "counterexample validation failure"; result = -1;
        }
        else if ( ppCex ) { *ppCex = pCex; pCex = NULL; }
    }
finish:
    if ( pPars->fVerbose || result < 0 )
    {
        Gia_Man_t * g = pReduced ? pReduced : pMiter;
        int open = 0, i, side, tree, openRegions[2] = {0, 0}, boundaryLimits[2] = {0, 0}, arithmeticLimits[2] = {0, 0};
        const char * focus = "surrounding CEC";
        for ( side = 0; side < 2; side++ )
        {
            Acec2_Man_t * m = side ? p1 : p0;
            if ( !m ) continue;
            for ( tree = 0; tree < Vec_WecSize(m->vTrees); tree++ )
                openRegions[side] += Vec_IntSize(Vec_WecEntry(m->vTrees, tree)) >= 2 &&
                    Vec_IntEntry(m->vPrefix, tree) < Vec_IntEntry(m->vWidths, tree);
            boundaryLimits[side] = m->nWordLimits+m->nWeightedLimits;
            arithmeticLimits[side] = m->nProductLimits+m->nWordPolyLimits+m->nGridLimits;
        }
        if ( openRegions[0]+openRegions[1] ) focus = "boundary recovery";
        if ( arithmeticLimits[0]+arithmeticLimits[1] ) focus = "arithmetic proof limits";
        if ( pPars->fNormalize && ((!p0 || !p1) ||
             ((!Vec_PtrSize(p0->vCells) || !Vec_PtrSize(p1->vCells)) && (p0->nParityOnly+p1->nParityOnly))) ) focus = "detection";
        if ( g )
            for ( i = 0; i+1 < Gia_ManCoNum(g); i += 2 )
                open += Gia_ObjFaninLit0p(g, Gia_ManCo(g, i)) != Gia_ObjFaninLit0p(g, Gia_ManCo(g, i+1));
        Abc_Print(1, "CEC progress: last stage = %s, checked records = %d/%d, matched record bits = %d, matcher-only bits = %d, structurally open output pairs = %d%s.\n",
            pStage, p0 ? Vec_PtrSize(p0->vRecords) : 0, p1 ? Vec_PtrSize(p1->vRecords) : 0,
            Stats.nRecordBits, Stats.nMacroBits, open, g ? "" : " (miter unavailable)");
        if ( result < 0 ) Abc_Print(1, "Unresolved diagnostic focus = %s. Open weighted regions = %d/%d; boundary proof limits = %d/%d; arithmetic proof limits = %d/%d; Boolean output pairs = %d.\n",
            focus, openRegions[0], openRegions[1], boundaryLimits[0], boundaryLimits[1], arithmeticLimits[0], arithmeticLimits[1], open);
        if ( result < 0 )
        {
            static const char * names[] = {"setup", "records", "local normalization", "matching", "rebuild", "CEC", "source profiling"};
            Abc_Print(1, "Arithmetic stop: %s; last work = %s; source profiling = %s; limited local obligations = %d/%d.\n",
                Stats.fArithmeticBudget ? "time share" : Stats.fPassLimit ? "pass limit" : "fixed point or caller limit",
                names[Stats.iPendingStep], Stats.fProfileTried ? "requested" : "pending", Stats.nPolyLimits[0], Stats.nPolyLimits[1]);
        }
        if ( p0 && p1 ) Abc_Print(1, "Recognition limits: word boundaries = %d/%d, product proofs = %d/%d, records = %d/%d.\n",
            p0->nWordLimits, p1->nWordLimits, p0->nProductLimits, p1->nProductLimits, p0->nRecordLimits, p1->nRecordLimits);
        if ( p0 && p1 ) Abc_Print(1, "Matcher certificates stored as source records = %d/%d; not imported = %d/%d.\n",
            p0->nCertificateRecords, p1->nCertificateRecords, p0->nCertificateContext, p1->nCertificateContext);
        if ( p0 && p1 ) Abc_Print(1, "Component BDDs: attempts = %d/%d, deterministic limits = %d/%d, reused limits = %d/%d.\n",
            p0->nBddAttempts, p1->nBddAttempts, p0->nBddLimits, p1->nBddLimits, p0->nBddHits, p1->nBddHits);
        if ( p0 && p1 && (p0->nPolyRecords || p1->nPolyRecords) )
            Abc_Print(1, "Whole-output polynomial source records = %d/%d.\n", p0->nPolyRecords, p1->nPolyRecords);
        if ( pPars->fVerbose && p0 && p1 )
            for ( i = 0; i < 2; i++ )
            {
                Acec2_Man_t * m = i ? p1 : p0;
                Abc_Print(1, "Shared analysis side %d: word/product/composition/sum work units = %d/%d/%d/%d; added records = %d.\n",
                    i, m->nStageQueries[0], m->nStageQueries[1], m->nStageQueries[2], m->nStageQueries[3],
                    m->nStageRecords[1]+m->nStageRecords[2]+m->nStageRecords[3]);
                Abc_Print(1, "Shared request queues side %d: region/mask/counter/carry/polynomial work units = %d/%d/%d/%d/%d.\n",
                    i, m->nSourceWork[0], m->nSourceWork[1], m->nSourceWork[2], m->nSourceWork[3], m->nSourceWork[4]);
                Abc_Print(1, "Source carries side %d: proposals = %d, recovered cells = %d, added records = %d, effort limits = %d%s.\n",
                    i, m->nFunctionalProbes, m->nFunctionalCells, m->nCarryRecords, m->nFunctionalLimits,
                    m->fCarryComplete ? ", search finished" : "");
            }
    }
    if ( pCex ) Abc_CexFree(pCex);
    if ( pReduced ) Gia_ManStop(pReduced);
    if ( pMiter ) Gia_ManStop(pMiter);
    Acec2_Free(p0); Acec2_Free(p1);
    if ( result < 0 )
    {
        if ( Acec2_Cancelled(pPars) ) pReason = "caller cancellation";
        else if ( Deadline && Abc_Clock() >= Deadline ) pReason = "time limit";
        Abc_Print(1, "UNDECIDED reason: %s.\n", pReason);
    }
    Abc_Print(1, "Networks are %s.  Time = %.3f sec.\n", result == 1 ? "equivalent" : result == 0 ? "NOT EQUIVALENT" : "UNDECIDED", (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
    return result;
}

/**Function*************************************************************

  Synopsis    [Proves the Boolean context with shared functions as free inputs.]

  Description [This is an overapproximation; only a complete proof transfers.
  A counterexample or timeout requests further arithmetic work instead.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_ProveContext( Gia_Man_t * pMiter, Acec2_Par_t * pPars, abctime Deadline )
{
    Gia_Man_t * pAbstract = Acec2_AbstractShared(pMiter, pPars, Deadline);
    int result;
    abctime stage;
    if ( !pAbstract ) return -1;
    stage = Abc_Clock();
    result = Gia_ManAndNum(pAbstract) <= 20000 ? Acec2_ProveSweep(pAbstract, pPars, Deadline, 32, 1000, 1, NULL) :
             Acec2_ProveBounded(pAbstract, pPars, Deadline, 4);
    if ( pPars->fVerbose ) Abc_Print(1, "Context CEC: ANDs = %d, result = %d, time = %.3f sec.\n",
        Gia_ManAndNum(pAbstract), result, (double)(Abc_Clock()-stage)/CLOCKS_PER_SEC);
    Gia_ManStop(pAbstract);
    return result == 1 ? 1 : -1;
}

/**Function*************************************************************

  Synopsis    [Starts a comparison with one shared runtime budget.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_Solve( Gia_Man_t * pGia0, Gia_Man_t * pGia1, Acec2_Par_t * pPars, Abc_Cex_t ** ppCex )
{
    return Acec2_SolveInt(pGia0, pGia1, pPars, ppCex, Abc_Clock());
}

/**Function*************************************************************

  Synopsis    [Checks adjacent output pairs of the current combinational miter.]

  Description [The input and its scratch remain untouched.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_SolveMiter( Gia_Man_t * pGia, Acec2_Par_t * pPars, Abc_Cex_t ** ppCex )
{
    Acec2_Par_t Pars = *pPars;
    Gia_Man_t * pGias[2] = {NULL, NULL};
    Vec_Int_t * vMap = NULL, * vRoots = NULL;
    Gia_Obj_t * o;
    int side, i, result = -1, fCancelled = 0;
    abctime clk = Abc_Clock(), Deadline = pPars->nTimeLimit ? clk+(abctime)pPars->nTimeLimit*CLOCKS_PER_SEC : 0;
    if ( !Pars.pCancelled ) Pars.pCancelled = &fCancelled;
    pPars = &Pars;
    if ( ppCex ) *ppCex = NULL;
    if ( !pGia || Gia_ManRegNum(pGia) || (Gia_ManCoNum(pGia) & 1) ) return -1;
    for ( side = 0; side < 2; side++ )
    {
        pGias[side] = Gia_ManStart(1000); Gia_ManHashAlloc(pGias[side]);
        vMap = Vec_IntStartFull(Gia_ManObjNum(pGia)); vRoots = Vec_IntAlloc(Gia_ManCoNum(pGia)/2);
        Vec_IntWriteEntry(vMap, 0, 0);
        Gia_ManForEachCo(pGia, o, i)
            if ( (i & 1) == side ) Vec_IntPush(vRoots, Gia_ObjFaninLit0p(pGia, o));
        Gia_ManForEachCi(pGia, o, i) Vec_IntWriteEntry(vMap, Gia_ObjId(pGia, o), Gia_ManAppendCi(pGias[side]));
        if ( !Acec2_CopyCone(pGia, pGias[side], vMap, vRoots, NULL, pPars, Deadline) ) goto cancelled;
        Gia_ManForEachCo(pGia, o, i)
            if ( (i & 1) == side ) Gia_ManAppendCo(pGias[side], Vec_IntEntry(vMap, Gia_ObjFaninId0p(pGia, o)) ^ Gia_ObjFaninC0(o));
        Vec_IntFreeP(&vMap); Vec_IntFreeP(&vRoots); Gia_ManHashStop(pGias[side]);
        {
            Gia_Man_t * pClean = Gia_ManCleanup(pGias[side]);
            Gia_ManStop(pGias[side]); pGias[side] = pClean;
        }
    }
    result = Acec2_SolveInt(pGias[0], pGias[1], pPars, ppCex, clk);
    goto finish;
cancelled:
    Abc_Print(1, "UNDECIDED reason: resource stop during miter extraction.\n");
    Abc_Print(1, "Networks are UNDECIDED.  Time = %.3f sec.\n", (double)(Abc_Clock()-clk)/CLOCKS_PER_SEC);
finish:
    Vec_IntFreeP(&vMap); Vec_IntFreeP(&vRoots);
    if ( pGias[0] ) Gia_ManStop(pGias[0]);
    if ( pGias[1] ) Gia_ManStop(pGias[1]);
    return result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
