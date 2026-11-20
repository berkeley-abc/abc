/**CFile****************************************************************

  FileName    [pdr2Tail.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Separates the reset prefix from the recurring transition relation.]

***********************************************************************/

#include <limits.h>
#include "pdr2Int.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Unrolls initial states and records each symbolic input's trace bit.]

  Description [The suffix may replace the original problem only if the bad
  output has been discharged at every earlier step. Return zero when local
  Boolean simplification cannot establish this.]

***********************************************************************/
static int Pdr2_TailPrefix( Aig_Man_t * p, Vec_Int_t * vInit, int Depth, Aig_Man_t * pPast,
    Vec_Ptr_t * vState, Vec_Int_t * vBit, Pdr2_Par_t * pPars, abctime Stop )
{
    int i, f, Value, nRegs = Aig_ManRegNum(p), nPis = Saig_ManPiNum(p);
    Aig_Obj_t * pObj, * pLit;
    Aig_ManConst1(p)->pData = Aig_ManConst1(pPast);
    Saig_ManForEachLo( p, pObj, i )
    {
        Value = vInit ? Vec_IntEntry(vInit, i) : 0;
        if ( Value == 2 )
        {
            pLit = Aig_ObjCreateCi(pPast);
            Vec_IntPush(vBit, i);
        }
        else pLit = Aig_NotCond(Aig_ManConst1(pPast), !Value);
        Vec_PtrPush(vState, pLit);
    }
    for ( f = 0; f < Depth; f++ )
    {
        if ( (Stop && Abc_Clock() >= Stop) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) return 0;
        Saig_ManForEachPi( p, pObj, i )
        {
            pObj->pData = Aig_ObjCreateCi(pPast);
            Vec_IntPush(vBit, nRegs + f * nPis + i);
        }
        Saig_ManForEachLo( p, pObj, i ) pObj->pData = Vec_PtrEntry(vState, i);
        Aig_ManForEachNode( p, pObj, i )
            pObj->pData = Aig_And(pPast, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
        if ( Aig_ObjChild0Copy(Aig_ManCo(p, 0)) != Aig_ManConst0(pPast) ) return 0;
        Saig_ManForEachLi( p, pObj, i ) Vec_PtrWriteEntry(vState, i, Aig_ObjChild0Copy(pObj));
    }
    return 1;
}

static int Pdr2_TailValue( char * pValues, Aig_Obj_t * pLit )
{
    int Value = pValues[Aig_ObjId(Aig_Regular(pLit))];
    return Value == 2 ? 2 : Value ^ Aig_IsComplement(pLit);
}

/**Function*************************************************************

  Synopsis    [Finds permanent constants implied by the symbolic reset image.]

  Description [Start with all known bits at the end of the prefix. Remove
  every candidate whose next value cannot be established from the remaining
  candidates with arbitrary inputs. A fixed point is an inductive cube.]

***********************************************************************/
static int Pdr2_TailConstants( Aig_Man_t * p, Vec_Ptr_t * vState, char * pStable, Pdr2_Par_t * pPars, abctime Stop )
{
    char * pValues = ABC_ALLOC(char, Aig_ManObjNumMax(p));
    Aig_Obj_t * pObj;
    int i, a, b, Changed, Count = 0;
    memset(pValues, 2, Aig_ManObjNumMax(p));
    pValues[Aig_ObjId(Aig_ManConst1(p))] = 1;
    if ( vState )
        Vec_PtrForEachEntry( Aig_Obj_t *, vState, pObj, i )
            pStable[i] = Aig_ObjIsConst1(Aig_Regular(pObj)) ? !Aig_IsComplement(pObj) : 2;
    for ( i = 0; i < Aig_ManRegNum(p); i++ ) Count += pStable[i] != 2;
    do
    {
        if ( (Stop && Abc_Clock() >= Stop) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) )
        {
            Count = -1;
            break;
        }
        Changed = 0;
        Saig_ManForEachLo( p, pObj, i ) pValues[Aig_ObjId(pObj)] = pStable[i];
        Aig_ManForEachNode( p, pObj, i )
        {
            a = Pdr2_TailValue(pValues, Aig_ObjChild0(pObj));
            b = Pdr2_TailValue(pValues, Aig_ObjChild1(pObj));
            pValues[Aig_ObjId(pObj)] = !a || !b ? 0 : a == 1 && b == 1 ? 1 : 2;
        }
        Saig_ManForEachLi( p, pObj, i )
            if ( pStable[i] != 2 && Pdr2_TailValue(pValues, Aig_ObjChild0(pObj)) != pStable[i] )
            {
                pStable[i] = 2;
                Changed++;
            }
        Count -= Changed;
    } while ( Changed && Count );
    ABC_FREE(pValues);
    return Count;
}

/**Function*************************************************************

  Synopsis    [Cofactors only the inductive constants before projecting the cone.]

***********************************************************************/
static Aig_Man_t * Pdr2_TailCone( Aig_Man_t * p, char * pStable, Vec_Int_t ** pvPis, Vec_Int_t ** pvRegs )
{
    Aig_Man_t * pNew = Aig_ManStart(Aig_ManNodeNum(p)), * pCone;
    Aig_Obj_t * pObj, * pCi;
    int i;
    pNew->pName = Abc_UtilStrsav(p->pName);
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi( p, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    Saig_ManForEachLo( p, pObj, i )
    {
        pCi = Aig_ObjCreateCi(pNew);
        pObj->pData = pStable[i] == 2 ? pCi : Aig_NotCond(Aig_ManConst1(pNew), !pStable[i]);
    }
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ManForEachCo( p, pObj, i ) Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));
    Aig_ManSetRegNum(pNew, Aig_ManRegNum(p));
    pCone = Pdr2_ManDupCoi(pNew, pvPis, pvRegs);
    Aig_ManStop(pNew);
    return pCone;
}

/**Function*************************************************************

  Synopsis    [Removes inductive reset constants and returns original CI indices.]

***********************************************************************/
Aig_Man_t * Pdr2_ManDupResetCoi( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars,
    abctime Stop, Vec_Int_t ** pvPis, Vec_Int_t ** pvRegs )
{
    int Count;
    abctime Limit = Abc_Clock() + 2*(abctime)CLOCKS_PER_SEC;
    char * pStable = ABC_ALLOC(char, Aig_ManRegNum(pAig)+1);
    Aig_Man_t * pNew;
    memcpy(pStable, pInit, Aig_ManRegNum(pAig));
    if ( Stop && Stop < Limit ) Limit = Stop;
    Count = Pdr2_TailConstants(pAig, NULL, pStable, pPars, Limit);
    pNew = Count > 0 ? Pdr2_TailCone(pAig, pStable, pvPis, pvRegs) : Pdr2_ManDupCoi(pAig, pvPis, pvRegs);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Inductive reset constants: %d of %d registers.\n", Abc_MaxInt(0, Count), Aig_ManRegNum(pAig));
    ABC_FREE(pStable);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Encodes the exact image of the prefix over the retained registers.]

  Description [Independent symbolic bits become free initial values. Shared
  inputs and nontrivial expressions are sampled on the first suffix step by
  a one-cycle multiplexer. History variables outside the cone disappear.]

***********************************************************************/
static Aig_Man_t * Pdr2_TailModel( Aig_Man_t * pCone, Aig_Man_t * pPast, char * pKeep,
    Vec_Int_t * vFrom, Vec_Int_t * vInit )
{
    int i, nMux = 0, nRegs = Aig_ManRegNum(pCone);
    Aig_Man_t * pNew = Aig_ManStart(Aig_ManNodeNum(pCone));
    Aig_Obj_t * pObj, * pSignal, * pStarted = NULL, * pCi;
    Vec_Ptr_t * vWork = Vec_PtrAlloc(16);
    pNew->pName = Abc_UtilStrsav(pCone->pName);
    Aig_ManIncrementTravId(pPast);
    Vec_IntFill(vFrom, Aig_ManCiNum(pPast), -1);
    Vec_IntClear(vInit);
    Aig_ManForEachCo( pPast, pObj, i )
    {
        pSignal = Aig_ObjFanin0(pObj);
        if ( Aig_ObjIsConst1(pSignal) ) Vec_IntPush(vInit, !Aig_ObjFaninC0(pObj));
        else if ( pKeep && !pKeep[i] ) Vec_IntPush(vInit, 2);
        else if ( Aig_ObjIsCi(pSignal) && Aig_ObjRefs(pSignal) == 1 )
        {
            Vec_IntPush(vInit, 2);
            Vec_IntWriteEntry(vFrom, Aig_ObjCioId(pSignal), Abc_Var2Lit(i, Aig_ObjFaninC0(pObj)));
        }
        else
        {
            Vec_IntPush(vInit, 0);
            Vec_PtrPush(vWork, pSignal);
            nMux++;
        }
    }
    while ( Vec_PtrSize(vWork) )
    {
        pObj = (Aig_Obj_t *)Vec_PtrPop(vWork);
        if ( Aig_ObjIsTravIdCurrent(pPast, pObj) ) continue;
        Aig_ObjSetTravIdCurrent(pPast, pObj);
        if ( !Aig_ObjIsNode(pObj) ) continue;
        Vec_PtrPush(vWork, Aig_ObjFanin0(pObj)); Vec_PtrPush(vWork, Aig_ObjFanin1(pObj));
    }
    Vec_PtrFree(vWork);
    Aig_ManConst1(pCone)->pData = Aig_ManConst1(pPast)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi( pCone, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    Aig_ManForEachCi( pPast, pObj, i )
    {
        if ( !Aig_ObjIsTravIdCurrent(pPast, pObj) ) continue;
        Vec_IntWriteEntry(vFrom, i, Abc_Var2Lit(nRegs + (nMux != 0) + Aig_ManCiNum(pNew), 0));
        pObj->pData = Aig_ObjCreateCi(pNew);
    }
    Saig_ManForEachLo( pCone, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    if ( nMux )
    {
        pStarted = Aig_ObjCreateCi(pNew);
        Vec_IntPush(vInit, 0);
    }
    Aig_ManForEachNode( pPast, pObj, i )
        if ( Aig_ObjIsTravIdCurrent(pPast, pObj) )
            pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ManForEachCo( pPast, pObj, i )
    {
        pSignal = Aig_ObjFanin0(pObj);
        if ( (pKeep && !pKeep[i]) || Aig_ObjIsConst1(pSignal) || (Aig_ObjIsCi(pSignal) && Aig_ObjRefs(pSignal) == 1) ) continue;
        pCi = Saig_ManLo(pCone, i);
        pCi->pData = Aig_Mux(pNew, pStarted, (Aig_Obj_t *)pCi->pData, Aig_ObjChild0Copy(pObj));
    }
    Aig_ManForEachNode( pCone, pObj, i )
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ManForEachCo( pCone, pObj, i ) Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));
    if ( nMux ) Aig_ObjCreateCo(pNew, Aig_ManConst1(pNew));
    Aig_ManSetRegNum(pNew, Vec_IntSize(vInit));
    Aig_ManSetCioIds(pNew);
    Aig_ManCleanup(pNew);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Restores the original prefix and expands suffix inputs into a trace.]

***********************************************************************/
static Abc_Cex_t * Pdr2_TailCex( Aig_Man_t * p, Vec_Int_t * vInit, int Depth,
    Vec_Int_t * vPis, Vec_Int_t * vBit, Vec_Int_t * vFrom, char * pHistory, Abc_Cex_t * pSmall )
{
    int i, f, r, Lit, nRegs = Aig_ManRegNum(p), nPis = Saig_ManPiNum(p);
    Abc_Cex_t * pBig;
    if ( !pSmall || pSmall->iFrame < 0 || pSmall->iFrame >= INT_MAX - Depth ||
         nRegs + ((ABC_INT64_T)pSmall->iFrame + Depth + 1) * nPis > INT_MAX - 32 ) return NULL;
    pBig = Abc_CexAlloc(nRegs, nPis, pSmall->iFrame + Depth + 1);
    pBig->iFrame = pSmall->iFrame + Depth;
    pBig->iPo = 0;
    if ( vInit )
        Vec_IntForEachEntry( vInit, r, i ) if ( r == 1 ) Abc_InfoSetBit(pBig->pData, i);
    Vec_IntForEachEntry( vFrom, Lit, i )
        if ( pHistory ? pHistory[i] : Lit >= 0 && (Abc_InfoHasBit(pSmall->pData, Abc_Lit2Var(Lit)) ^ Abc_LitIsCompl(Lit)) )
            Abc_InfoSetBit(pBig->pData, Vec_IntEntry(vBit, i));
    for ( f = 0; f <= pSmall->iFrame; f++ )
        Vec_IntForEachEntry( vPis, r, i )
            if ( Abc_InfoHasBit(pSmall->pData, pSmall->nRegs + f * pSmall->nPis + i) )
                Abc_InfoSetBit(pBig->pData, nRegs + (f + Depth) * nPis + r);
    if ( Saig_ManVerifyCex(p, pBig) ) return pBig;
    Abc_CexFree(pBig);
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Tests a suffix initial state against the exact prefix image.]

  Description [A model supplies the missing prefix inputs. An unsatisfiable
  core selects registers whose joint reset functions must be restored. Each
  suffix overapproximates the concrete machine until its trace is matched.]

***********************************************************************/
static int Pdr2_TailMatch( Aig_Man_t * pPast, Cnf_Dat_t * pCnf, sat_solver * pSat,
    Abc_Cex_t * pSmall, Vec_Int_t * vFrom, char * pKeep, char * pHistory, Vec_Int_t * vAssume, char * pCore )
{
    Aig_Obj_t * pObj;
    int i, Lit, Var, Value, Ret, Num, Added = 0, * pFinal;
    char * pValue = ABC_ALLOC(char, Aig_ManObjNumMax(pPast));
    // A restored register reads its reset function on the first step. Its
    // storage bit in the suffix trace is still the mux's unused zero input.
    pValue[Aig_ObjId(Aig_ManConst1(pPast))] = 1;
    Aig_ManForEachCi( pPast, pObj, i )
    {
        Lit = Vec_IntEntry(vFrom, i);
        pValue[Aig_ObjId(pObj)] = Lit >= 0 && (Abc_InfoHasBit(pSmall->pData, Abc_Lit2Var(Lit)) ^ Abc_LitIsCompl(Lit));
    }
    Aig_ManForEachNode( pPast, pObj, i )
        pValue[Aig_ObjId(pObj)] = (pValue[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj)) &
                                 (pValue[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj));
    Vec_IntClear(vAssume);
    Aig_ManForEachCo( pPast, pObj, i )
    {
        if ( Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) ) continue;
        Var = pCnf->pVarNums[Aig_ObjId(pObj)];
        Value = pKeep[i] ? pValue[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj) : Abc_InfoHasBit(pSmall->pData, i);
        Vec_IntPush(vAssume, Abc_Var2Lit(Var, !Value));
    }
    ABC_FREE(pValue);
    Ret = sat_solver_solve(pSat, Vec_IntArray(vAssume), Vec_IntArray(vAssume) + Vec_IntSize(vAssume), 50000, 0, 0, 0);
    if ( Ret == l_True )
    {
        Aig_ManForEachCi( pPast, pObj, i ) pHistory[i] = sat_solver_var_value(pSat, pCnf->pVarNums[Aig_ObjId(pObj)]);
        return 0;
    }
    if ( Ret != l_False ) return -1;
    memset(pCore, 0, pCnf->nVars);
    Num = sat_solver_final(pSat, &pFinal);
    for ( i = 0; i < Num; i++ ) pCore[Abc_Lit2Var(pFinal[i])] = 1;
    Aig_ManForEachCo( pPast, pObj, i )
        if ( !pKeep[i] && pCore[pCnf->pVarNums[Aig_ObjId(pObj)]] ) { pKeep[i] = 1; Added++; }
    return Added ? Added : -1;
}

/**Function*************************************************************

  Synopsis    [Runs PDR from the exact symbolic image after a safe reset prefix.]

***********************************************************************/
int Pdr2_ManSolveTail( Aig_Man_t * p, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Depth )
{
    Aig_Man_t * pPast, * pCone = NULL, * pModel = NULL;
    Vec_Int_t * vBit, * vFrom, * vTailInit, * vRegs = NULL, * vPis = NULL;
    Vec_Ptr_t * vState;
    char * pStable, * pKeep = NULL, * pHistory = NULL, * pCore = NULL;
    Pdr2_Par_t Child = *pPars;
    Cnf_Dat_t * pCnf = NULL;
    sat_solver * pSat = NULL;
    Vec_Int_t * vAssume = NULL;
    int Result = -1, Count, Round, Added, i, r;
    abctime Stop = pPars->nTimeOut ? Abc_Clock() + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    if ( pPars->fVerify && pPars->fVerifyComplete ) return -1;
    if ( Depth < 1 || Depth > 32 || (ABC_INT64_T)Depth * Aig_ManObjNumMax(p) > 8000000 ||
         !Aig_ManRegNum(p) || Saig_ManPoNum(p) != 1 || Saig_ManConstrNum(p) || Aig_ManBufNum(p) || Aig_ManExorNum(p) ) return -1;
    pPast = Aig_ManStart(Aig_ManNodeNum(p));
    vState = Vec_PtrAlloc(Aig_ManRegNum(p));
    vBit = Vec_IntAlloc(Saig_ManPiNum(p)); vFrom = Vec_IntAlloc(16); vTailInit = Vec_IntAlloc(16);
    pStable = ABC_ALLOC(char, Aig_ManRegNum(p));
    if ( !Pdr2_TailPrefix(p, vInit, Depth, pPast, vState, vBit, pPars, Stop) ) goto done;
    Count = Pdr2_TailConstants(p, vState, pStable, pPars, Stop);
    if ( Count < 0 ) goto done;
    pCone = Pdr2_TailCone(p, pStable, &vPis, &vRegs);
    Vec_IntForEachEntry( vRegs, r, i ) Aig_ObjCreateCo(pPast, (Aig_Obj_t *)Vec_PtrEntry(vState, r));
    Aig_ManCleanup(pPast);
    Aig_ManSetCioIds(pPast);
    if ( Gip_OptionGet("PDR2_TAIL_REFINE") && Vec_IntSize(vRegs) )
        pKeep = ABC_CALLOC(char, Vec_IntSize(vRegs));
    for ( Round = 0; Round < 24; Round++ )
    {
        if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) ) break;
        pModel = Pdr2_TailModel(pCone, pPast, pKeep, vFrom, vTailInit);
        if ( pPars->fVerbose )
            Abc_Print(1, "Post-reset model: prefix %d, %d fixed flops, inputs %d -> %d, flops %d -> %d, nodes %d -> %d.\n",
                Depth, Count, Saig_ManPiNum(p), Saig_ManPiNum(pModel), Aig_ManRegNum(p), Aig_ManRegNum(pModel), Aig_ManNodeNum(p), Aig_ManNodeNum(pModel));
        if ( Stop )
        {
            abctime Left = Stop - Abc_Clock();
            if ( Left < CLOCKS_PER_SEC ) break;
            Child.nTimeOut = (int)(Left / CLOCKS_PER_SEC);
        }
        Result = Gip_OptionGet("PDR2_SAMPLE") ?
            Pdr2_ManSampleProperty(pModel, vTailInit, &Child, atoi(Gip_OptionGet("PDR2_SAMPLE"))) :
            Pdr2_ManSolveInit(pModel, vTailInit, &Child);
        if ( Result != 0 ) break;
        Result = -1;
        if ( !pModel->pSeqModel ) break;
        if ( pKeep )
        {
            if ( !pSat )
            {
                pCnf = Cnf_DeriveSimple(pPast, Aig_ManCoNum(pPast));
                pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
                if ( !pSat ) break;
                sat_solver_set_runid(pSat, pPars->RunId);
                sat_solver_set_stop_func(pSat, pPars->pFuncStop);
                sat_solver_set_runtime_limit(pSat, Stop);
                pHistory = ABC_CALLOC(char, 1 + Aig_ManCiNum(pPast));
                pCore = ABC_ALLOC(char, pCnf->nVars);
                vAssume = Vec_IntAlloc(16);
            }
            Added = Pdr2_TailMatch(pPast, pCnf, pSat, pModel->pSeqModel, vFrom, pKeep, pHistory, vAssume, pCore);
            if ( Added < 0 ) break;
            if ( Added )
            {
                if ( pPars->fVerbose ) Abc_Print(1, "Post-reset refinement: restored %d correlated registers.\n", Added);
                Aig_ManStop(pModel); pModel = NULL;
                continue;
            }
        }
        Abc_CexFreeP(&p->pSeqModel);
        p->pSeqModel = Pdr2_TailCex(p, vInit, Depth, vPis, vBit, vFrom, pHistory, pModel->pSeqModel);
        if ( p->pSeqModel ) { pPars->iFrame = p->pSeqModel->iFrame; Result = 0; }
        break;
    }
done:
    if ( pSat ) sat_solver_delete(pSat);
    if ( pCnf ) Cnf_DataFree(pCnf);
    Vec_IntFreeP(&vAssume);
    ABC_FREE(pKeep); ABC_FREE(pHistory); ABC_FREE(pCore);
    if ( pModel ) Aig_ManStop(pModel);
    if ( pCone ) Aig_ManStop(pCone);
    Aig_ManStop(pPast); Vec_PtrFree(vState);
    Vec_IntFreeP(&vPis); Vec_IntFreeP(&vRegs);
    Vec_IntFree(vBit); Vec_IntFree(vFrom); Vec_IntFree(vTailInit);
    ABC_FREE(pStable);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Restores the preceding inputs that loaded each eliminated latch.]

***********************************************************************/
static Abc_Cex_t * Pdr2_InputLatchCex( Aig_Man_t * p, Vec_Int_t * vInit, Vec_Int_t * vDrive,
    Abc_Cex_t * c )
{
    int r, k = 0, i, f, Lit, Bit, Init, nPis = Saig_ManPiNum(p), nRegs = Aig_ManRegNum(p);
    Vec_Int_t * vShift;
    Abc_Cex_t * d;
    if ( !c || c->iFrame < 0 || c->iPo || c->nPis != nPis ||
         ((ABC_INT64_T)c->iFrame + 1)*nPis + nRegs > INT_MAX-32 ) return NULL;
    d = Abc_CexAlloc(nRegs, nPis, c->iFrame+1);
    d->iPo = 0; d->iFrame = c->iFrame;
    vShift = Vec_IntStart(nPis);
    Vec_IntForEachEntry( vDrive, Lit, r )
    {
        Init = vInit ? Vec_IntEntry(vInit,r) : 0;
        if ( Lit < 0 ) Bit = Abc_InfoHasBit(c->pData, k++);
        else
        {
            Vec_IntWriteEntry(vShift, Abc_Lit2Var(Lit), 1 + Abc_LitIsCompl(Lit));
            Bit = Init == 2 ? Abc_InfoHasBit(c->pData, c->nRegs + Abc_Lit2Var(Lit)) : Init;
        }
        if ( Bit ) Abc_InfoSetBit(d->pData, r);
    }
    for ( f = 0; f <= c->iFrame; ++f )
        Vec_IntForEachEntry( vShift, k, i )
        {
            if ( k && f == c->iFrame ) continue;
            Bit = Abc_InfoHasBit(c->pData, c->nRegs + (f + (k != 0))*nPis + i);
            if ( Bit ^ (k == 2) ) Abc_InfoSetBit(d->pData, nRegs + f*nPis + i);
        }
    Vec_IntFree(vShift);
    if ( Saig_ManVerifyCex(p, d) ) return d;
    Abc_CexFree(d);
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Retimes private primary inputs across their only latch.]

  Description [When a PI drives only one RI, that latch is freely
  controllable after reset. Reuse the input for the current latch value.
  One shared register supplies the original fixed values in frame zero.]

***********************************************************************/
int Pdr2_ManSolveInputLatches( Aig_Man_t * p, Vec_Int_t * vInit, Pdr2_Par_t * pPars )
{
    int i, Init, Lit, Removed = 0, fStarted = 0, Result = -1, nRegs = Aig_ManRegNum(p);
    Aig_Man_t * pNew = NULL;
    Aig_Obj_t * pObj, * pFan, * pStarted = NULL;
    Vec_Int_t * vDrive = Vec_IntAlloc(nRegs), * vNewInit = Vec_IntAlloc(nRegs+1);
    Pdr2_Par_t Child = *pPars;
    abctime Stop = pPars->nTimeOut ? Abc_Clock() + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    if ( (pPars->fVerify && pPars->fVerifyComplete) ||
         Saig_ManPoNum(p) != 1 || Saig_ManConstrNum(p) || Aig_ManBufNum(p) || Aig_ManExorNum(p) ||
         (vInit && Vec_IntSize(vInit) != nRegs) ) goto done;
    Aig_ManSetCioIds(p);
    Saig_ManForEachLi( p, pObj, i )
    {
        pFan = Aig_ObjFanin0(pObj);
        Lit = -1;
        if ( Saig_ObjIsPi(p, pFan) && Aig_ObjRefs(pFan) == 1 )
        {
            Lit = Abc_Var2Lit(Aig_ObjCioId(pFan), Aig_ObjFaninC0(pObj));
            fStarted |= !vInit || Vec_IntEntry(vInit,i) != 2;
            Removed++;
        }
        Vec_IntPush(vDrive, Lit);
    }
    if ( !Removed ) goto done;
    pNew = Aig_ManStart(Aig_ManNodeNum(p)+Removed);
    pNew->pName = Abc_UtilStrsav(p->pName);
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Saig_ManForEachPi( p, pObj, i ) pObj->pData = Aig_ObjCreateCi(pNew);
    Saig_ManForEachLo( p, pObj, i ) if ( Vec_IntEntry(vDrive,i) < 0 )
    {
        pObj->pData = Aig_ObjCreateCi(pNew);
        Vec_IntPush(vNewInit, vInit ? Vec_IntEntry(vInit,i) : 0);
    }
    if ( fStarted ) { pStarted = Aig_ObjCreateCi(pNew); Vec_IntPush(vNewInit,0); }
    Saig_ManForEachLo( p, pObj, i ) if ( (Lit = Vec_IntEntry(vDrive,i)) >= 0 )
    {
        pFan = Aig_ManCi(pNew, Abc_Lit2Var(Lit));
        Init = vInit ? Vec_IntEntry(vInit,i) : 0;
        pObj->pData = Init == 2 ? pFan : Aig_Mux(pNew, pStarted, pFan, Aig_NotCond(Aig_ManConst1(pNew), !Init));
    }
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(Aig_ManCo(p, 0)));
    Saig_ManForEachLi( p, pObj, i ) if ( Vec_IntEntry(vDrive,i) < 0 )
        Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));
    if ( fStarted ) Aig_ObjCreateCo(pNew, Aig_ManConst1(pNew));
    Aig_ManSetRegNum(pNew, Vec_IntSize(vNewInit));
    Aig_ManSetCioIds(pNew); Aig_ManCleanup(pNew);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Private input latches: removed %d of %d, remaining state bits %d.\n", Removed, nRegs, Vec_IntSize(vNewInit));
    if ( Stop )
    {
        abctime Left = Stop - Abc_Clock();
        if ( Left < CLOCKS_PER_SEC ) goto done;
        Child.nTimeOut = (int)(Left / CLOCKS_PER_SEC);
    }
    Child.fPartRun = 1;
    Result = Pdr2_ManSolveInit(pNew, vNewInit, &Child);
    pPars->nPhasesRun = Child.nPhasesRun; pPars->nRestartsRun = Child.nRestartsRun;
    pPars->iFrame = Child.iFrame; pPars->fBmcDecided = Child.fBmcDecided;
    if ( Result == 0 )
    {
        Abc_CexFreeP(&p->pSeqModel);
        p->pSeqModel = Pdr2_InputLatchCex(p, vInit, vDrive, pNew->pSeqModel);
        if ( !p->pSeqModel ) Result = -1;
    }
done:
    if ( pNew ) Aig_ManStop(pNew);
    Vec_IntFree(vNewInit); Vec_IntFree(vDrive);
    return Result;
}

ABC_NAMESPACE_IMPL_END
