/**CFile****************************************************************

  FileName    [pdr2Proj.c]
  SystemName  [ABC: Logic synthesis and verification system.]
  PackageName [Property directed reachability, second implementation.]
  Synopsis    [Small reachable-state projections near the property.]

***********************************************************************/

#include "pdr2Int.h"

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Selects the nearest register outputs by breadth-first search.]

***********************************************************************/
static int Pdr2_ProjRegisters( Pdr2_Man_t * p, int Width, int * pRegs )
{
    Aig_Man_t * pAig = p->pAig;
    Aig_Obj_t * pObj;
    Vec_Int_t * vQueue = Vec_IntAlloc(128);
    char * pSeen = ABC_CALLOC(char, Aig_ManObjNumMax(pAig));
    int i, Id, Reg, Count = 0;
    Vec_IntPush(vQueue, Aig_ObjFaninId0(Aig_ManCo(pAig, 0)));
    Vec_IntForEachEntry(vQueue, Id, i)
    {
        if ( pSeen[Id] ) continue;
        pSeen[Id] = 1;
        pObj = Aig_ManObj(pAig, Id);
        if ( Aig_ObjIsNode(pObj) )
            Vec_IntPushTwo(vQueue, Aig_ObjFaninId0(pObj), Aig_ObjFaninId1(pObj));
        else if ( Aig_ObjIsCi(pObj) && (Reg = Aig_ObjCioId(pObj) - p->nPis) >= 0 )
        {
            pRegs[Count++] = Reg;
            if ( Count == Width ) break;
        }
    }
    Vec_IntFree(vQueue);
    ABC_FREE(pSeen);
    return Count;
}

/**Function*************************************************************

  Synopsis    [Computes the ternary successor of every projected current state.]

  Description [Each lane fixes the selected registers to one minterm.
  Other state bits and primary inputs are unknown. The two bit vectors
  record forced zero and forced one, respectively.]

***********************************************************************/
static int Pdr2_ProjTransfer( Pdr2_Man_t * p, int nRegs, int * pRegs,
    unsigned char * pOff, unsigned char * pOn, abctime Stop )
{
    Aig_Man_t * pAig = p->pAig;
    Aig_Obj_t * pObj;
    word * pZero = ABC_CALLOC(word, Aig_ManObjNumMax(pAig));
    word * pOne = ABC_CALLOC(word, Aig_ManObjNumMax(pAig));
    word a0, a1, b0, b1, Bits;
    int i, j, k, Base, Count, Id, fOk = 0;
    pOne[Aig_ObjId(Aig_ManConst1(pAig))] = ~(word)0;
    for ( Base = 0; Base < (1<<nRegs); Base += 64 )
    {
        Count = Abc_MinInt(64, (1<<nRegs) - Base);
        for ( j = 0; j < nRegs; j++ )
        {
            Bits = 0;
            for ( k = 0; k < Count; k++ )
                if ( (Base+k) & (1<<j) ) Bits |= (word)1 << k;
            Id = Aig_ObjId(Saig_ManLo(pAig, pRegs[j]));
            pZero[Id] = ~Bits;
            pOne[Id] = Bits;
        }
        Aig_ManForEachNode(pAig, pObj, i)
        {
            if ( !(i & 4095) && (Abc_Clock() >= Stop || (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId))) ) goto done;
            Id = Aig_ObjFaninId0(pObj);
            a0 = Aig_ObjFaninC0(pObj) ? pOne[Id] : pZero[Id];
            a1 = Aig_ObjFaninC0(pObj) ? pZero[Id] : pOne[Id];
            Id = Aig_ObjFaninId1(pObj);
            b0 = Aig_ObjFaninC1(pObj) ? pOne[Id] : pZero[Id];
            b1 = Aig_ObjFaninC1(pObj) ? pZero[Id] : pOne[Id];
            pZero[i] = a0 | b0;
            pOne[i] = a1 & b1;
        }
        for ( j = 0; j < nRegs; j++ )
        {
            pObj = Saig_ManLi(pAig, pRegs[j]);
            Id = Aig_ObjFaninId0(pObj);
            a0 = Aig_ObjFaninC0(pObj) ? pOne[Id] : pZero[Id];
            a1 = Aig_ObjFaninC0(pObj) ? pZero[Id] : pOne[Id];
            for ( k = 0; k < Count; k++ )
            {
                if ( (a0 >> k) & 1 ) pOff[Base+k] |= 1<<j;
                if ( (a1 >> k) & 1 ) pOn[Base+k] |= 1<<j;
            }
        }
    }
    fOk = 1;
done:
    ABC_FREE(pZero);
    ABC_FREE(pOne);
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Computes the least fixed point of the projected transition.]

***********************************************************************/
static int Pdr2_ProjReach( Pdr2_Man_t * p, int nRegs, int * pRegs,
    unsigned char * pOff, unsigned char * pOn, unsigned char * pReach )
{
    int Queue[256], nStates = 1<<nRegs, Known = 0, Initial = 0;
    int j, State, Free, Sub, Next, i, Count = 0;
    for ( j = 0; j < nRegs; j++ )
        if ( p->pInit[pRegs[j]] != 2 )
        {
            Known |= 1<<j;
            Initial |= p->pInit[pRegs[j]]<<j;
        }
    for ( State = 0; State < nStates; State++ )
        if ( (State & Known) == Initial ) { Queue[Count++] = State; pReach[State] = 1; }
    for ( i = 0; i < Count && Count < nStates; i++ )
    {
        State = Queue[i];
        Free = (nStates-1) & ~(pOff[State] | pOn[State]);
        for ( Sub = Free; ; Sub = (Sub-1) & Free )
        {
            Next = pOn[State] | Sub;
            if ( !pReach[Next] ) { pReach[Next] = 1; Queue[Count++] = Next; }
            if ( !Sub ) break;
        }
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Covers the complement of the reachability set by forbidden cubes.]

***********************************************************************/
static void Pdr2_ProjCover( int nRegs, int * pRegs, unsigned char * pReach, Vec_Wec_t * vCubes )
{
    unsigned char Covered[256] = {0};
    int State, Mask, Trial, k, j, nStates = 1<<nRegs;
    Vec_Int_t * vCube;
    for ( State = 0; State < nStates; State++ )
    {
        if ( pReach[State] || Covered[State] ) continue;
        Mask = nStates - 1;
        for ( j = 0; j < nRegs; j++ )
        {
            Trial = Mask ^ (1<<j);
            for ( k = 0; k < nStates; k++ )
                if ( pReach[k] && !((State ^ k) & Trial) ) break;
            if ( k == nStates ) Mask = Trial;
        }
        vCube = Vec_WecPushLevel(vCubes);
        for ( j = 0; j < nRegs; j++ )
            if ( Mask & (1<<j) ) Vec_IntPush(vCube, Abc_Var2Lit(pRegs[j], !(State & (1<<j))));
        Vec_IntSort(vCube, 0);
        for ( k = 0; k < nStates; k++ )
            if ( !((State ^ k) & Mask) ) Covered[k] = 1;
    }
}

/**Function*************************************************************

  Synopsis    [Checks initiation and simultaneous consecution on the original CNF.]

***********************************************************************/
static int Pdr2_ProjCertified( Pdr2_Man_t * p, Vec_Wec_t * vCubes, abctime Stop )
{
    Gip_Solver_t * pSat = Gip_SolverNew(p->pCtx);
    Vec_Int_t * vCube;
    int Lits[8], i, k, Lit, Ret = 0;
    pSat->TimeLimit = Stop;
    pSat->nConfLimit = 5000;
    pSat->RunId = p->pPars->RunId;
    pSat->pFuncStop = p->pPars->pFuncStop;
    Vec_WecForEachLevel(vCubes, vCube, i)
    {
        if ( Pdr2_LitsAreInit(p, vCube) ) goto done;
        Vec_IntForEachEntry(vCube, Lit, k) Lits[k] = Abc_LitNot(Pdr2_LitLo(p, Lit));
        Gip_SolverAddLemma(pSat, Lits, Vec_IntSize(vCube));
    }
    Vec_WecForEachLevel(vCubes, vCube, i)
    {
        Vec_IntForEachEntry(vCube, Lit, k) Lits[k] = Pdr2_LitLi(p, Lit);
        if ( Gip_SolverSolve(pSat, Lits, Vec_IntSize(vCube), NULL, NULL, 0, -1) != GIP_UNSAT ) goto done;
    }
    Ret = 1;
done:
    Gip_SolverFree(pSat);
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Derives a small certified invariant over the property support.]

***********************************************************************/
static Vec_Wec_t * Pdr2_ProjDerive( Pdr2_Man_t * p, int Width, abctime Stop )
{
    unsigned char Off[256] = {0}, On[256] = {0}, Reach[256] = {0};
    int Regs[8], nRegs, Count;
    Vec_Wec_t * vCubes = Vec_WecAlloc(16);
    if ( Width < 1 || Width > 8 || !p->nRegs || p->pPars->nInitLiReg ||
         Aig_ManBufNum(p->pAig) || Aig_ManExorNum(p->pAig) ||
         Aig_ManObjNumMax(p->pAig) > 2000000 ) return vCubes;
    Aig_ManSetCioIds(p->pAig);
    nRegs = Pdr2_ProjRegisters(p, Width, Regs);
    if ( !nRegs || Abc_Clock() >= Stop || !Pdr2_ProjTransfer(p, nRegs, Regs, Off, On, Stop) ) return vCubes;
    Count = Pdr2_ProjReach(p, nRegs, Regs, Off, On, Reach);
    if ( Count < (1<<nRegs) ) Pdr2_ProjCover(nRegs, Regs, Reach, vCubes);
    if ( Vec_WecSize(vCubes) && !Pdr2_ProjCertified(p, vCubes, Stop) ) Vec_WecClear(vCubes);
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1, "Property register projection: %d of %d states, %d certified clauses.\n", Count, 1<<nRegs, Vec_WecSize(vCubes));
    return vCubes;
}

/**Function*************************************************************

  Synopsis    [Seeds a newly started PDR manager with the full projected invariant.]

***********************************************************************/
void Pdr2_ManSeedProjection( Pdr2_Man_t * p, int Width )
{
    Pdr2_Cube_t * pCube;
    Pdr2_Lem_t * pLem;
    Vec_Int_t * vCube;
    Vec_Wec_t * vCubes;
    abctime Stop = Abc_Clock() + 3*(abctime)CLOCKS_PER_SEC;
    int k, j, Lit, Reg;
    if ( p->pPars->nPropLimit ) return;
    if ( p->timeLimit && p->timeLimit < Stop ) Stop = p->timeLimit;
    vCubes = Pdr2_ProjDerive(p, Width, Stop);
    Vec_WecForEachLevel(vCubes, vCube, k)
    {
        if ( p->fAbsActive )
            Vec_IntForEachEntry(vCube, Lit, j)
            {
                Reg = Abc_Lit2Var(Lit);
                if ( !p->pAbs[Reg] ) { p->pAbs[Reg] = 1; p->nAbsFlops++; }
            }
        pCube = Pdr2_CubeAllocVec(vCube);
        pLem = Pdr2_LemAlloc(p, pCube, NULL, -1);
        Pdr2_ManSolverAddLemma(p, p->pInf, pCube, pLem->Id);
        Vec_PtrPush(p->vInf, pLem);
        p->nInfLemmas++;
        Pdr2_CubeDeref(pCube);
    }
    Vec_WecFree(vCubes);
}

/**Function*************************************************************

  Synopsis    [Checks the bad output under the certified projected invariant.]

***********************************************************************/
int Pdr2_ManProjectedComb( Aig_Man_t * pAig, Vec_Int_t * vInit, Pdr2_Par_t * pPars, abctime Stop, int Width )
{
    Pdr2_Man_t * p;
    Vec_Int_t * vCube;
    Vec_Wec_t * vCubes;
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pAllowed, * pMatch;
    char * pInit;
    int i, k, Lit, Ret;
    abctime SeedStop = Abc_Clock() + 3*(abctime)CLOCKS_PER_SEC;
    if ( pPars->fVerify && pPars->fVerifyComplete ) return -1;
    if ( !Aig_ManRegNum(pAig) || Saig_ManPoNum(pAig) != 1 || Saig_ManConstrNum(pAig) ||
         Aig_ManBufNum(pAig) || Aig_ManExorNum(pAig) ) return -1;
    Aig_ManSetCioIds(pAig);
    pInit = ABC_CALLOC(char, Aig_ManRegNum(pAig));
    if ( vInit ) Vec_IntForEachEntry(vInit, Lit, i) pInit[i] = (char)Lit;
    p = Pdr2_ManStart(pAig, pInit, pPars);
    ABC_FREE(pInit);
    vCubes = Pdr2_ProjDerive(p, Width, Stop && Stop < SeedStop ? Stop : SeedStop);
    Pdr2_ManStop(p);
    if ( !Vec_WecSize(vCubes) )
    {
        Vec_WecFree(vCubes);
        return Pdr2_ManCombSafe(pAig, pPars, Stop, pAig, vInit);
    }
    pNew = Aig_ManStart(Aig_ManNodeNum(pAig));
    pNew->pName = Abc_UtilStrsav(pAig->pName);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi(pAig, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);
    Vec_WecForEachLevel(vCubes, vCube, i)
        if ( Vec_IntSize(vCube) == 1 )
        {
            Lit = Vec_IntEntry(vCube, 0);
            Saig_ManLo(pAig, Abc_Lit2Var(Lit))->pData = Aig_NotCond(Aig_ManConst1(pNew), !Abc_LitIsCompl(Lit));
        }
    Aig_ManForEachNode(pAig, pObj, i) pObj->pData = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    pAllowed = Aig_ManConst1(pNew);
    Vec_WecForEachLevel(vCubes, vCube, i)
    {
        pMatch = Aig_ManConst1(pNew);
        Vec_IntForEachEntry(vCube, Lit, k)
        {
            pObj = (Aig_Obj_t *)Saig_ManLo(pAig, Abc_Lit2Var(Lit))->pData;
            pMatch = Aig_And(pNew, pMatch, Aig_NotCond(pObj, Abc_LitIsCompl(Lit)));
        }
        pAllowed = Aig_And(pNew, pAllowed, Aig_Not(pMatch));
    }
    Aig_ObjCreateCo(pNew, Aig_And(pNew, pAllowed, Aig_ObjChild0Copy(Aig_ManCo(pAig, 0))));
    Ret = Pdr2_ManCombSafe(pNew, pPars, Stop, pAig, vInit);
    Aig_ManStop(pNew);
    Vec_WecFree(vCubes);
    return Ret;
}

ABC_NAMESPACE_IMPL_END
