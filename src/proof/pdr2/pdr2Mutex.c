/**CFile****************************************************************

  FileName    [pdr2Mutex.c]
  SystemName  [ABC: Logic synthesis and verification system.]
  PackageName [Property directed reachability, second implementation.]
  Synopsis    [Binary encoding of mutually exclusive registered inputs.]

***********************************************************************/

#include <limits.h>
#include "pdr2Int.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Returns a signed register literal or -1 for another signal.]

***********************************************************************/
static int Pdr2_MutexRegLit( Aig_Man_t * p, Aig_Obj_t * pLit )
{
    Aig_Obj_t * pObj = Aig_Regular(pLit);
    return Saig_ObjIsLo(p, pObj) ?
        Abc_Var2Lit(Aig_ObjCioId(pObj) - Saig_ManPiNum(p), Aig_IsComplement(pLit)) : -1;
}

/**Function*************************************************************

  Synopsis    [Finds a clique whose members have distinct single-input drivers.]

  Description [An edge requires the same exclusion clause among the
  conjunction leaves of bad and the signed guard's next function. The
  caller checks that both functions require the current guard. Hence all
  states of any bad trace, including the last, satisfy every edge.]

***********************************************************************/
static void Pdr2_MutexClique( Aig_Man_t * p, Vec_Ptr_t * vNext, unsigned char * pBad,
                              int * pDrive, Vec_Int_t * vInit, int Minimum, Vec_Int_t * vGroup )
{
    int n = 2*Aig_ManRegNum(p), i, a, b, Best, Hot = 0;
    unsigned char * pEdge = ABC_CALLOC(unsigned char, n*n);
    int * pDegree = ABC_CALLOC(int, n);
    Aig_Obj_t * pLit, * pObj;
    Vec_PtrForEachEntry( Aig_Obj_t *, vNext, pLit, i )
    {
        pObj = Aig_Regular(pLit);
        if ( !Aig_IsComplement(pLit) || !pBad[Aig_ObjId(pObj)] || !Aig_ObjIsAnd(pObj) ) continue;
        a = Pdr2_MutexRegLit(p, Aig_ObjChild0(pObj));
        b = Pdr2_MutexRegLit(p, Aig_ObjChild1(pObj));
        if ( a < 0 || b < 0 || (a >> 1) == (b >> 1) || pEdge[a*n+b] ||
             pDrive[a >> 1] < 0 || pDrive[b >> 1] < 0 ) continue;
        if ( vInit && (Vec_IntEntry(vInit, a >> 1) == 2 || Vec_IntEntry(vInit, b >> 1) == 2) ) continue;
        pEdge[a*n+b] = pEdge[b*n+a] = 1;
        pDegree[a]++; pDegree[b]++;
    }
    Vec_IntClear(vGroup);
    for ( ;; )
    {
        Best = -1;
        for ( a = 0; a < n; a++ )
            if ( pDegree[a] >= Minimum-1 && (Best < 0 || pDegree[a] > pDegree[Best]) )
                Best = a;
        if ( Best < 0 ) break;
        pDegree[Best] = -1;
        b = (vInit ? Vec_IntEntry(vInit, Best >> 1) : 0) ^ Abc_LitIsCompl(Best);
        if ( Hot && b ) continue;
        Hot |= b;
        Vec_IntPush(vGroup, Best);
        for ( a = 0; a < n; a++ )
            if ( pDegree[a] >= 0 && (!pEdge[Best*n+a] ||
                 Abc_Lit2Var(pDrive[a >> 1]) == Abc_Lit2Var(pDrive[Best >> 1])) )
                pDegree[a] = -1;
    }
    ABC_FREE(pDegree); ABC_FREE(pEdge);
    if ( Vec_IntSize(vGroup) < Minimum ) Vec_IntClear(vGroup);
    else Vec_IntSort(vGroup, 0);
}

/**Function*************************************************************

  Synopsis    [Looks for a trace guard with shared pairwise exclusions.]

***********************************************************************/
static Vec_Int_t * Pdr2_MutexFind( Aig_Man_t * p, int * pDrive, Vec_Int_t * vInit,
                                    Pdr2_Par_t * pPars, abctime Stop, int Minimum )
{
    Vec_Ptr_t * vBad = Vec_PtrAlloc(64), * vNext = Vec_PtrAlloc(64);
    Vec_Int_t * vGroup = Vec_IntAlloc(64);
    unsigned char * pBad = ABC_CALLOC(unsigned char, Aig_ManObjNumMax(p));
    Aig_Obj_t * pLit, * pNext;
    int i, Reg, Trials = 0;
    if ( !Pdr2_ManLogicLeaves(p, Aig_ObjChild0(Aig_ManCo(p,0)), 0, 131072, vBad) ) goto done;
    Vec_PtrForEachEntry( Aig_Obj_t *, vBad, pLit, i )
        if ( Aig_IsComplement(pLit) ) pBad[Aig_ObjId(Aig_Regular(pLit))] = 1;
    Vec_PtrForEachEntry( Aig_Obj_t *, vBad, pLit, i )
    {
        Reg = Pdr2_MutexRegLit(p, pLit);
        if ( Reg < 0 ) continue;
        pNext = Aig_NotCond(Aig_ObjChild0(Saig_ManLi(p, Reg >> 1)), Abc_LitIsCompl(Reg));
        if ( Aig_IsComplement(pNext) || !Aig_ObjIsAnd(Aig_Regular(pNext)) ) continue;
        if ( ++Trials > 32 || (Stop && Abc_Clock() >= Stop) ||
             (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) ) break;
        if ( !Pdr2_ManLogicLeaves(p, pNext, 0, 131072, vNext) || Vec_PtrFind(vNext, pLit) < 0 ) continue;
        Pdr2_MutexClique(p, vNext, pBad, pDrive, vInit, Minimum, vGroup);
        if ( Vec_IntSize(vGroup) ) break;
    }
done:
    ABC_FREE(pBad); Vec_PtrFree(vNext); Vec_PtrFree(vBad);
    return vGroup;
}

/**Function*************************************************************

  Synopsis    [Decodes one member of a binary group.]

***********************************************************************/
static Aig_Obj_t * Pdr2_MutexDecode( Aig_Man_t * p, int First, int Width, int Code )
{
    Aig_Obj_t * pLit = Aig_ManConst1(p);
    int i;
    for ( i = 0; i < Width; i++ )
        pLit = Aig_And(p, pLit, Aig_NotCond(Aig_ManCi(p, First+i), !((Code >> i) & 1)));
    return pLit;
}

/**Function*************************************************************

  Synopsis    [Duplicates one AND using the indicated input mapping.]

***********************************************************************/
static Aig_Obj_t * Pdr2_MutexAnd( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t ** pMap )
{
    return Aig_And(p, Aig_NotCond(pMap[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj)),
                      Aig_NotCond(pMap[Aig_ObjFaninId1(pObj)], Aig_ObjFaninC1(pObj)));
}

/**Function*************************************************************

  Synopsis    [Recodes current states and the corresponding transition inputs.]

  Description [The original PIs remain available to the bad output at
  the last frame. For a transition, the extra input bits choose a legal
  group valuation. Zero and unused codes denote no active member.]

***********************************************************************/
static Aig_Man_t * Pdr2_MutexModel( Aig_Man_t * p, int BadId, Vec_Int_t * vInit, Vec_Int_t * vGroup,
                                     int * pDrive, int * pMember, Vec_Int_t * vNewInit )
{
    int nPis = Saig_ManPiNum(p), nRegs = Aig_ManRegNum(p), nObjs = Aig_ManObjNumMax(p);
    int Width = Abc_Base2Log(Vec_IntSize(vGroup)+1), First = nPis+Width+nRegs-Vec_IntSize(vGroup);
    int i, Id, Lit, Reg, Drive, InitCode = 0, a, b;
    Aig_Man_t * pNew = Aig_ManStart(Aig_ManNodeNum(p));
    Aig_Obj_t ** pBad = ABC_CALLOC(Aig_Obj_t *, nObjs), ** pStep = ABC_CALLOC(Aig_Obj_t *, nObjs);
    unsigned char * pUse = ABC_CALLOC(unsigned char, nObjs);
    Aig_Obj_t * pObj;
    pNew->pName = Abc_UtilStrsav(p->pName);
    pBad[Aig_ObjId(Aig_ManConst1(p))] = pStep[Aig_ObjId(Aig_ManConst1(p))] = Aig_ManConst1(pNew);
    Saig_ManForEachPi(p, pObj, i)
        pBad[Aig_ObjId(pObj)] = pStep[Aig_ObjId(pObj)] = Aig_ObjCreateCi(pNew);
    for ( i = 0; i < Width; i++ ) Aig_ObjCreateCi(pNew);
    Vec_IntForEachEntry(vGroup, Lit, i)
    {
        Reg = Abc_Lit2Var(Lit); pMember[Reg] = Lit;
        if ( (vInit ? Vec_IntEntry(vInit, Reg) : 0) ^ Abc_LitIsCompl(Lit) ) InitCode = i+1;
    }
    Saig_ManForEachLo(p, pObj, i) if ( pMember[i] < 0 )
    {
        pBad[Aig_ObjId(pObj)] = pStep[Aig_ObjId(pObj)] = Aig_ObjCreateCi(pNew);
        Vec_IntPush(vNewInit, vInit ? Vec_IntEntry(vInit,i) : 0);
        pUse[Aig_ObjFaninId0(Saig_ManLi(p,i))] |= 2;
    }
    for ( i = 0; i < Width; i++ )
    {
        Aig_ObjCreateCi(pNew);
        Vec_IntPush(vNewInit, (InitCode >> i) & 1);
    }
    Vec_IntForEachEntry(vGroup, Lit, i)
    {
        Reg = Abc_Lit2Var(Lit); Drive = pDrive[Reg];
        Id = Aig_ObjId(Saig_ManLo(p, Reg));
        pBad[Id] = pStep[Id] = Aig_NotCond(Pdr2_MutexDecode(pNew, First, Width, i+1), Abc_LitIsCompl(Lit));
        Id = Aig_ObjId(Aig_ManCi(p, Abc_Lit2Var(Drive)));
        pStep[Id] = Aig_NotCond(Pdr2_MutexDecode(pNew, nPis, Width, i+1), Abc_LitIsCompl(Lit ^ Drive));
    }
    pUse[BadId] |= 1;
    Aig_ManForEachNodeReverse(p, pObj, i) if ( pUse[i] )
    {
        a = Pdr2_MutexRegLit(p, Aig_ObjChild0(pObj));
        b = Pdr2_MutexRegLit(p, Aig_ObjChild1(pObj));
        if ( a >= 0 && b >= 0 && a != b && pMember[a >> 1] == a && pMember[b >> 1] == b )
            pUse[i] = 4;
        else
        {
            pUse[Aig_ObjFaninId0(pObj)] |= pUse[i];
            pUse[Aig_ObjFaninId1(pObj)] |= pUse[i];
        }
    }
    Aig_ManForEachNode(p, pObj, i)
    {
        if ( pUse[i] == 4 ) pBad[i] = pStep[i] = Aig_ManConst0(pNew);
        if ( pUse[i] & 1 ) pBad[i] = Pdr2_MutexAnd(pNew, pObj, pBad);
        if ( pUse[i] & 2 ) pStep[i] = Pdr2_MutexAnd(pNew, pObj, pStep);
    }
    pObj = Aig_ManCo(p,0);
    Aig_ObjCreateCo(pNew, Aig_NotCond(pBad[BadId], Aig_ObjFaninC0(pObj)));
    Saig_ManForEachLi(p, pObj, i) if ( pMember[i] < 0 )
        Aig_ObjCreateCo(pNew, Aig_NotCond(pStep[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj)));
    for ( i = 0; i < Width; i++ ) Aig_ObjCreateCo(pNew, Aig_ManCi(pNew, nPis+i));
    Aig_ManSetRegNum(pNew, Vec_IntSize(vNewInit));
    Aig_ManCleanup(pNew);
    ABC_FREE(pBad); ABC_FREE(pStep); ABC_FREE(pUse);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Restores and checks a witness using the original input sequence.]

***********************************************************************/
static Abc_Cex_t * Pdr2_MutexCex( Aig_Man_t * p, Vec_Int_t * vInit, Vec_Int_t * vGroup,
                                    int * pDrive, int * pMember, Abc_Cex_t * c )
{
    int nPis = Saig_ManPiNum(p), nRegs = Aig_ManRegNum(p), Width = Abc_Base2Log(Vec_IntSize(vGroup)+1);
    int i, j, f, Offset, Code, Lit, Value, Drive;
    Abc_Cex_t * d;
    if ( !c || c->iFrame < 0 || c->iPo || c->nPis != nPis+Width ||
         c->nRegs != nRegs-Vec_IntSize(vGroup)+Width ||
         ((ABC_INT64_T)c->iFrame+1)*nPis+nRegs > INT_MAX-32 ) return NULL;
    d = Abc_CexAlloc(nRegs, nPis, c->iFrame+1);
    d->iPo = 0; d->iFrame = c->iFrame;
    for ( i = j = 0; i < nRegs; i++ )
    {
        Value = pMember[i] >= 0 ? (vInit ? Vec_IntEntry(vInit,i) : 0) : Abc_InfoHasBit(c->pData, j++);
        if ( Value ) Abc_InfoSetBit(d->pData, i);
    }
    for ( f = 0; f <= c->iFrame; f++ )
    {
        Offset = c->nRegs + f*c->nPis;
        for ( i = 0; i < nPis; i++ )
            if ( Abc_InfoHasBit(c->pData, Offset+i) ) Abc_InfoSetBit(d->pData, nRegs+f*nPis+i);
        if ( f == c->iFrame ) break;
        Code = 0;
        for ( i = 0; i < Width; i++ )
            if ( Abc_InfoHasBit(c->pData, Offset+nPis+i) ) Code |= 1 << i;
        Vec_IntForEachEntry(vGroup, Lit, i)
        {
            Drive = pDrive[Lit >> 1];
            Value = (Code == i+1) ^ Abc_LitIsCompl(Lit ^ Drive);
            j = nRegs + f*nPis + Abc_Lit2Var(Drive);
            if ( Value != Abc_InfoHasBit(d->pData, j) ) Abc_InfoXorBit(d->pData, j);
        }
    }
    if ( Saig_ManVerifyCex(p,d) ) return d;
    Abc_CexFree(d);
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Solves a model with binary-encoded mutually exclusive inputs.]

***********************************************************************/
int Pdr2_ManSolveMutex( Aig_Man_t * p, Vec_Int_t * vInit, Pdr2_Par_t * pPars, int Minimum )
{
    int i, BadId, Count = 0, Result = -1, nRegs = Aig_ManRegNum(p);
    int * pDrive, * pMember;
    Aig_Man_t * pNew = NULL;
    Aig_Obj_t * pObj;
    Vec_Int_t * vGroup = NULL, * vNewInit = NULL;
    Pdr2_Par_t Child = *pPars;
    abctime Stop = pPars->nTimeOut ? Abc_Clock() + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    if ( Minimum < 2 || nRegs < Minimum || nRegs > 1024 || Aig_ManNodeNum(p) > 300000 ||
         Aig_ManBufNum(p) || Aig_ManExorNum(p) || Saig_ManPoNum(p) != 1 || Saig_ManConstrNum(p) ||
         pPars->nInitLiReg || pPars->fDumpInv || pPars->fVerifyComplete || pPars->nPropLimit ||
         pPars->nFrameMax || (vInit && Vec_IntSize(vInit) != nRegs) ) return -1;
    BadId = Aig_ObjFaninId0(Aig_ManCo(p,0));
    if ( BadId < 0 ) return -1;
    pDrive = ABC_ALLOC(int, nRegs); pMember = ABC_ALLOC(int, nRegs);
    Aig_ManSetCioIds(p);
    Saig_ManForEachLi(p, pObj, i)
    {
        Aig_Obj_t * pFan = Aig_ObjFanin0(pObj);
        if ( !pFan ) goto done;
        pDrive[i] = Saig_ObjIsPi(p, pFan) ? Abc_Var2Lit(Aig_ObjCioId(pFan), Aig_ObjFaninC0(pObj)) : -1;
        pMember[i] = -1;
        Count += pDrive[i] >= 0;
    }
    if ( Count < Minimum ) goto done;
    vGroup = Pdr2_MutexFind(p, pDrive, vInit, pPars, Stop, Minimum);
    if ( !Vec_IntSize(vGroup) ) goto done;
    vNewInit = Vec_IntAlloc(nRegs);
    pNew = Pdr2_MutexModel(p, BadId, vInit, vGroup, pDrive, pMember, vNewInit);
    if ( pPars->fVerbose && !pPars->fSilent )
        Abc_Print(1, "Mutex recoding: %d exclusive register literals, %d to %d flops, %d to %d ANDs.\n",
            Vec_IntSize(vGroup), nRegs, Aig_ManRegNum(pNew), Aig_ManNodeNum(p), Aig_ManNodeNum(pNew));
    if ( pPars->pFuncStop && pPars->pFuncStop(pPars->RunId) ) goto done;
    if ( Stop )
    {
        abctime Left = Stop-Abc_Clock();
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
        p->pSeqModel = Pdr2_MutexCex(p, vInit, vGroup, pDrive, pMember, pNew->pSeqModel);
        if ( !p->pSeqModel ) Result = -1;
    }
done:
    if ( pNew ) Aig_ManStop(pNew);
    Vec_IntFreeP(&vNewInit); Vec_IntFreeP(&vGroup);
    ABC_FREE(pMember); ABC_FREE(pDrive);
    return Result;
}

ABC_NAMESPACE_IMPL_END
