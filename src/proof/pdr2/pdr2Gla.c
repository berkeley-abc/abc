/**CFile****************************************************************

  FileName    [pdr2Gla.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Refines a gate abstraction along spurious PDR counterexamples.]

***********************************************************************/

#include <limits.h>
#include "pdr2Int.h"
#include "aig/gia/giaAig.h"
#include "proof/abs/abs.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Adds logic behind a boundary gate, crossing latches one layer at a time.]

***********************************************************************/
static void Pdr2_GlaExpand( Gia_Man_t * p, int Id, int Layers )
{
    Gia_Obj_t * pObj = Gia_ManObj(p, Id);
    if ( Layers == 0 || Gia_ObjIsPi(p, pObj) || Vec_IntEntry(p->vGateClasses, Id) ) return;
    Vec_IntWriteEntry(p->vGateClasses, Id, 1);
    if ( Gia_ObjIsRo(p, pObj) )
        Pdr2_GlaExpand(p, Gia_ObjFaninId0p(p, Gia_ObjRoToRi(p, pObj)), Layers-1);
    else if ( Gia_ObjIsAnd(pObj) )
    {
        Pdr2_GlaExpand(p, Gia_ObjFaninId0p(p, pObj), Layers-1);
        Pdr2_GlaExpand(p, Gia_ObjFaninId1p(p, pObj), Layers-1);
    }
}

/**Function*************************************************************

  Synopsis    [Keeps full combinational cones up to a register boundary.]

  Description [A register expansion preserves its entire next-state
  function. Only the preceding register frontier can become free inputs.
  Revisit a shared cone when a path reaches it with a larger depth budget.]

***********************************************************************/
static void Pdr2_GlaExpandRegisters( Gia_Man_t * p, Vec_Int_t * vRoots, int Layers, unsigned char * pBest )
{
    Vec_Int_t * vWork = Vec_IntAlloc(128);
    Gia_Obj_t * pObj;
    int i, Id, Left;
    Vec_IntForEachEntry( vRoots, Id, i ) Vec_IntPushTwo(vWork, Id, Layers);
    while ( Vec_IntSize(vWork) )
    {
        Left = Vec_IntPop(vWork); Id = Vec_IntPop(vWork);
        if ( pBest[Id] >= Left+1 ) continue;
        pBest[Id] = (unsigned char)(Left+1);
        pObj = Gia_ManObj(p, Id);
        if ( Gia_ObjIsRo(p, pObj) )
        {
            if ( !Left ) continue;
            Vec_IntWriteEntry(p->vGateClasses, Id, 1);
            Vec_IntPushTwo(vWork, Gia_ObjFaninId0p(p, Gia_ObjRoToRi(p, pObj)), Left-1);
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntWriteEntry(p->vGateClasses, Id, 1);
            Vec_IntPushTwo(vWork, Gia_ObjFaninId0p(p, pObj), Left);
            Vec_IntPushTwo(vWork, Gia_ObjFaninId1p(p, pObj), Left);
        }
    }
    Vec_IntFree(vWork);
}

/**Function*************************************************************

  Synopsis    [Maps exposed original objects to input literals in the cleaned abstraction.]

***********************************************************************/
static int Pdr2_GlaMap( Gia_Man_t * p, Gia_Man_t * pAbs, Vec_Int_t * vIds, int * pMap )
{
    Gia_Obj_t * pObj;
    int i, Lit, Id;
    Vec_IntForEachEntry( vIds, Id, i )
    {
        Lit = Gia_ManObj(p, Id)->Value;
        if ( Lit == -1 ) continue;
        if ( Lit < 0 || Abc_Lit2Var(Lit) >= Gia_ManObjNum(pAbs) ) return 0;
        pObj = Gia_ManObj(pAbs, Abc_Lit2Var(Lit));
        if ( !Gia_ObjIsPi(pAbs, pObj) ) return 0;
        pMap[Id] = Abc_Var2Lit(Gia_ObjCioId(pObj), Abc_LitIsCompl(Lit));
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Finds boundary discrepancies in the backward cone of the failed output.]

  Description [Each bit names a time and object at which the concrete and
  abstract executions differ. A differing gate has a differing fanin, and a
  differing concrete latch has a differing input at the preceding time.
  Stop at the first abstract input on each such path.]

***********************************************************************/
static int Pdr2_GlaRefine( Gia_Man_t * p, int Depth, int * pMap, unsigned * pDiff, int Layers, unsigned char * pBest )
{
    Vec_Int_t * vWork = Vec_IntAlloc(64), * vCuts = Vec_IntAlloc(16);
    int i, Id, Frame, Entry, nObjs = Gia_ManObjNum(p);
    Gia_Obj_t * pObj;
    Vec_IntPush(vWork, Depth * nObjs + Gia_ObjFaninId0p(p, Gia_ManPo(p, 0)));
    while ( Vec_IntSize(vWork) )
    {
        Entry = Vec_IntPop(vWork);
        if ( !Abc_InfoHasBit(pDiff, Entry) ) continue;
        Abc_InfoXorBit(pDiff, Entry);
        Id = Entry % nObjs;
        Frame = Entry / nObjs;
        pObj = Gia_ManObj(p, Id);
        if ( pMap[Id] >= 0 && !Gia_ObjIsPi(p, pObj) ) Vec_IntPush(vCuts, Id);
        else if ( Gia_ObjIsRo(p, pObj) && Frame )
            Vec_IntPush(vWork, (Frame-1) * nObjs + Gia_ObjFaninId0p(p, Gia_ObjRoToRi(p, pObj)));
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush(vWork, Frame * nObjs + Gia_ObjFaninId0p(p, pObj));
            Vec_IntPush(vWork, Frame * nObjs + Gia_ObjFaninId1p(p, pObj));
        }
    }
    Vec_IntUniqify(vCuts);
    if ( pBest ) Pdr2_GlaExpandRegisters(p, vCuts, Layers, pBest);
    else Vec_IntForEachEntry( vCuts, Id, i ) Pdr2_GlaExpand(p, Id, Layers);
    i = Vec_IntSize(vCuts);
    Vec_IntFree(vCuts); Vec_IntFree(vWork);
    return i;
}

/**Function*************************************************************

  Synopsis    [Replays the abstract inputs on the concrete circuit and refines discrepancies.]

  Description [The low bit of each value is the concrete execution. The
  high bit follows the abstract execution with identical real inputs and
  the supplied free boundary values. Only a replayed concrete witness may
  leave the abstraction loop.]

***********************************************************************/
static int Pdr2_GlaTrace( Gia_Man_t * p, Gia_Man_t * pAbs, Abc_Cex_t * pCex,
    Pdr2_Par_t * pPars, abctime Stop, int Layers, unsigned char * pBest )
{
    Gia_Obj_t * pObj, * pRi, * pRo;
    int i, f, Lit, Bit, Value, First, Result = -1, nObjs = Gia_ManObjNum(p);
    int nRegs = Gia_ManRegNum(p), nPis = Gia_ManPiNum(p), * pMap;
    unsigned * pDiff;
    unsigned char * pVal;
    Vec_Int_t * vPis, * vCuts;
    Abc_Cex_t * pBig;
    if ( !pCex || pCex->iFrame < 0 || pCex->iFrame == INT_MAX || pCex->iPo != 0 ||
         pCex->nRegs != Gia_ManRegNum(pAbs) || pCex->nPis != Gia_ManPiNum(pAbs) ||
         (1 + (ABC_INT64_T)pCex->iFrame) * nObjs > 180000000 ||
         (1 + (ABC_INT64_T)pCex->iFrame) * nPis + nRegs > INT_MAX - 32 ) return -1;
    Gia_ManGlaCollect(p, p->vGateClasses, &vPis, &vCuts, NULL, NULL);
    pMap = ABC_ALLOC(int, nObjs);
    for ( i = 0; i < nObjs; i++ ) pMap[i] = -1;
    pDiff = ABC_CALLOC(unsigned, Abc_BitWordNum((pCex->iFrame + 1) * nObjs));
    pVal = ABC_CALLOC(unsigned char, nObjs);
    pBig = Abc_CexAlloc(nRegs, nPis, pCex->iFrame + 1);
    if ( !Pdr2_GlaMap(p, pAbs, vPis, pMap) || !Pdr2_GlaMap(p, pAbs, vCuts, pMap) ) goto done;
    for ( f = 0; f <= pCex->iFrame; f++ )
    {
        if ( (Stop && Abc_Clock() >= Stop) || (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) goto done;
        First = pCex->nRegs + pCex->nPis * f;
        Gia_ManForEachPi( p, pObj, i )
        {
            Lit = pMap[Gia_ObjId(p, pObj)];
            Bit = Lit >= 0 && (Abc_InfoHasBit(pCex->pData, First + Abc_Lit2Var(Lit)) ^ Abc_LitIsCompl(Lit));
            pVal[Gia_ObjId(p, pObj)] = Bit ? 3 : 0;
            if ( Bit ) Abc_InfoSetBit(pBig->pData, nRegs + f*nPis + i);
        }
        Gia_ManForEachRo( p, pObj, i )
        {
            int Id = Gia_ObjId(p, pObj);
            Lit = pMap[Id];
            if ( Lit >= 0 )
            {
                Bit = Abc_InfoHasBit(pCex->pData, First + Abc_Lit2Var(Lit)) ^ Abc_LitIsCompl(Lit);
                pVal[Id] = (pVal[Id] & 1) | (Bit << 1);
            }
            if ( pVal[Id] == 1 || pVal[Id] == 2 ) Abc_InfoSetBit(pDiff, f*nObjs + Id);
        }
        Gia_ManForEachAnd( p, pObj, i )
        {
            Value = (pVal[Gia_ObjFaninId0(pObj, i)] ^ (Gia_ObjFaninC0(pObj) ? 3 : 0)) &
                    (pVal[Gia_ObjFaninId1(pObj, i)] ^ (Gia_ObjFaninC1(pObj) ? 3 : 0));
            Lit = pMap[i];
            if ( Lit >= 0 )
            {
                Bit = Abc_InfoHasBit(pCex->pData, First + Abc_Lit2Var(Lit)) ^ Abc_LitIsCompl(Lit);
                Value = (Value & 1) | (Bit << 1);
            }
            pVal[i] = Value;
            if ( Value == 1 || Value == 2 ) Abc_InfoSetBit(pDiff, f*nObjs + i);
        }
        Gia_ManForEachCo( p, pObj, i )
            pVal[Gia_ObjId(p, pObj)] = pVal[Gia_ObjFaninId0p(p, pObj)] ^ (Gia_ObjFaninC0(pObj) ? 3 : 0);
        Value = pVal[Gia_ObjId(p, Gia_ManPo(p, 0))];
        if ( Value & 1 )
        {
            pBig->iPo = 0; pBig->iFrame = f; pBig->nBits = nRegs + (f+1)*nPis;
            if ( Gia_ManVerifyCex(p, pBig, 0) )
            {
                Abc_CexFreeP(&p->pCexSeq);
                p->pCexSeq = pBig; pBig = NULL;
                Result = 0;
            }
            goto done;
        }
        if ( f == pCex->iFrame && Value == 2 )
            Result = Pdr2_GlaRefine(p, f, pMap, pDiff, Layers, pBest);
        Gia_ManForEachRiRo( p, pRi, pRo, i ) pVal[Gia_ObjId(p, pRo)] = pVal[Gia_ObjId(p, pRi)];
    }
    if ( !Result ) Result = -1;
done:
    Abc_CexFreeP(&pBig);
    Vec_IntFree(vPis); Vec_IntFree(vCuts);
    ABC_FREE(pDiff); ABC_FREE(pVal); ABC_FREE(pMap);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Translates proposed clauses across the register maps of two abstractions.]

  Description [Dropping an unavailable candidate is always safe. Each candidate
  is checked for initiation and inductiveness by the receiving PDR manager.]

***********************************************************************/
static void Pdr2_GlaMoveCandidates( Gia_Man_t * p, Gia_Man_t * pAbs, Vec_Wec_t * vSrc, Vec_Wec_t * vDst, int fToOriginal )
{
    Vec_Int_t * vMap, * vCube, * vOut;
    Gia_Obj_t * pRo, * pSmall;
    int i, k, Copy, Reg, Lit;
    Vec_WecClear(vDst);
    if ( !Vec_WecSize(vSrc) ) return;
    vMap = Vec_IntStartFull(fToOriginal ? Gia_ManRegNum(pAbs) : Gia_ManRegNum(p));
    Gia_ManForEachRo(p, pRo, i)
    {
        Copy = (int)pRo->Value;
        if ( Copy < 0 ) continue;
        pSmall = Gia_ManObj(pAbs, Abc_Lit2Var(Copy));
        if ( !Gia_ObjIsRo(pAbs, pSmall) ) continue;
        Reg = Gia_ObjCioId(pSmall) - Gia_ManPiNum(pAbs);
        Vec_IntWriteEntry(vMap, fToOriginal ? Reg : i, Abc_Var2Lit(fToOriginal ? i : Reg, Abc_LitIsCompl(Copy)));
    }
    Vec_WecForEachLevel(vSrc, vCube, i)
    {
        Vec_IntForEachEntry(vCube, Lit, k)
            if ( Abc_Lit2Var(Lit) >= Vec_IntSize(vMap) || Vec_IntEntry(vMap, Abc_Lit2Var(Lit)) < 0 ) break;
        if ( k != Vec_IntSize(vCube) ) continue;
        vOut = Vec_WecPushLevel(vDst);
        Vec_IntForEachEntry(vCube, Lit, k)
            Vec_IntPush(vOut, Vec_IntEntry(vMap, Abc_Lit2Var(Lit)) ^ Abc_LitIsCompl(Lit));
        Vec_IntSort(vOut, 0);
    }
    Vec_IntFree(vMap);
}

/**Function*************************************************************

  Synopsis    [Alternates unbounded PDR and trace-directed gate refinement.]

  Description [Every omitted latch or gate is a free input. An abstract
  safety proof therefore covers the concrete circuit. The original zero
  initialization and PI ordering are checked when a witness is transferred.]

***********************************************************************/
int Pdr2_ManSolveGla( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Layers )
{
    Gia_Man_t * p, * pAbs;
    Gia_Obj_t * pRoot;
    Aig_Man_t * pSmall;
    Pdr2_Par_t Child = *pPars;
    Abs_Par_t Init;
    Vec_Wec_t * vOriginal = NULL, * vLocal = NULL;
    int i, Round, Ret, Result = -1, Refs;
    unsigned char * pBest = NULL;
    abctime Stop = pPars->nTimeOut ? Abc_Clock() + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    if ( pPars->fVerify && pPars->fVerifyComplete ) return -1;
    if ( vInit )
        for ( i = 0; i < Vec_IntSize(vInit); ++i ) if ( Vec_IntEntry(vInit, i) ) return -1;
    if ( !Aig_ManRegNum(pAig) || Saig_ManPoNum(pAig) != 1 || Aig_ManObjNumMax(pAig) > 1500000 ) return -1;
    p = Gia_ManFromAigSimple(pAig);
    Child.vPartCandidates = NULL;
    if ( Gip_OptionGet("PDR2_GATE_SHARE") )
    {
        vOriginal = Vec_WecAlloc(64);
        vLocal = Vec_WecAlloc(64);
        Child.vPartCandidates = vLocal;
    }
    pRoot = Gia_ObjFanin0(Gia_ManPo(p, 0));
    if ( Gia_ObjIsConst0(pRoot) || Gia_ObjIsPi(p, pRoot) ) goto done;
    if ( Gip_OptionGet("PDR2_GATE_FLOPS") )
        pBest = ABC_CALLOC(unsigned char, Gia_ManObjNum(p));
    if ( !pBest && Gia_ManAndNum(p) > 500 )
    {
        Abs_ParSetDefaults(&Init);
        Init.nFramesMax = 16;
        Init.nTimeOut = pPars->nTimeOut ? Abc_MinInt(3, pPars->nTimeOut) : 3;
        Init.fSilent = 1;
        Init.RunId = pPars->RunId; Init.pFuncStop = pPars->pFuncStop;
        Ret = Gia_ManPerformGla(p, &Init);
        if ( Ret == 0 && p->pCexSeq ) goto witness;
        if ( Ret == 1 ) { Result = 1; goto done; }
    }
    if ( !p->vGateClasses )
    {
        p->vGateClasses = Vec_IntStart(Gia_ManObjNum(p));
        Vec_IntWriteEntry(p->vGateClasses, 0, 1);
        if ( pBest )
        {
            Vec_Int_t * vRoots = Vec_IntAlloc(1);
            Vec_IntPush(vRoots, Gia_ObjId(p, pRoot));
            Pdr2_GlaExpandRegisters(p, vRoots, Layers, pBest);
            Vec_IntFree(vRoots);
        }
        else Pdr2_GlaExpand(p, Gia_ObjId(p, pRoot), 4);
    }
    for ( Round = 0; Round < 120; ++Round )
    {
        if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) ) break;
        if ( Stop && Stop - Abc_Clock() < CLOCKS_PER_SEC ) break;
        pAbs = Gia_ManDupAbsGates(p, p->vGateClasses);
        pSmall = Gia_ManToAigSimple(pAbs);
        if ( vLocal ) Pdr2_GlaMoveCandidates(p, pAbs, vOriginal, vLocal, 0);
        Child.nTimeOut = Stop ? Abc_MaxInt(1, (int)((Stop - Abc_Clock()) / CLOCKS_PER_SEC)) : 0;
        Child.fVerbose = 0;
        Child.fSilent = 1;
        Ret = Pdr2_ManSolveInit(pSmall, NULL, &Child);
        Refs = Ret == 0 ? Pdr2_GlaTrace(p, pAbs, pSmall->pSeqModel, pPars, Stop, Layers, pBest) : -1;
        if ( vLocal && Refs > 0 )
        {
            Pdr2_GlaMoveCandidates(p, pAbs, vLocal, vOriginal, 1);
            if ( pPars->fVerbose )
                Abc_Print(1, "Gate refinement retained %d candidate clauses for the next round.\n", Vec_WecSize(vOriginal));
        }
        if ( pPars->fVerbose )
            Abc_Print(1, "PDR gate refinement: round %d, %d flops, %d gates, result %d, %d discrepancies.\n",
                Round, Gia_ManRegNum(pAbs), Gia_ManAndNum(pAbs), Ret, Refs);
        Aig_ManStop(pSmall);
        Gia_ManStop(pAbs);
        if ( Ret == 1 ) { Result = 1; break; }
        if ( Ret == 0 && Refs == 0 && p->pCexSeq ) goto witness;
        if ( Refs <= 0 ) break;
    }
    goto done;
witness:
    if ( p->pCexSeq && Saig_ManVerifyCex(pAig, p->pCexSeq) )
    {
        Abc_CexFreeP(&pAig->pSeqModel);
        pAig->pSeqModel = p->pCexSeq;
        p->pCexSeq = NULL;
        pPars->iFrame = pAig->pSeqModel->iFrame;
        Result = 0;
    }
done:
    Vec_WecFreeP(&vLocal);
    Vec_WecFreeP(&vOriginal);
    ABC_FREE(pBest);
    Gia_ManStop(p);
    return Result;
}

ABC_NAMESPACE_IMPL_END
