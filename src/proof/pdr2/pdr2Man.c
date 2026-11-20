/**CFile****************************************************************

  FileName    [pdr2Man.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Manager, cubes, obligations, queue, invariant and CEX.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2Man.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdr2Int.h"
#include "aig/ioa/ioa.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns a register input's literal, bypassing an exact CNF buffer.]

  Description [The pair (x or a) and (!x or !a) defines x as !a. Read
  both clauses, including their polarities, so the same test works for
  compact variables, inverted drivers, and different CNF mappings.]

  SideEffects []

***********************************************************************/
static int Pdr2_ManInputLit( Gip_Ctx_t * pCtx, Aig_Obj_t * pCo, int fDirect )
{
    int Out = Abc_Var2Lit(Gip_CtxObjVar(pCtx, pCo), 0), Id = Aig_ObjId(pCo);
    Cnf_Dat_t * pCnf = pCtx->pCnf;
    int First, * pA, * pB, i, j;
    if ( !fDirect || pCnf->pObj2Count[Id] != 2 ) return Out;
    First = pCnf->pObj2Clause[Id];
    pA = pCnf->pClauses[First];
    pB = pCnf->pClauses[First + 1];
    if ( pB - pA != 2 || pCnf->pClauses[First + 2] - pB != 2 ) return Out;
    for ( i = 0; i < 2; ++i )
        if ( Abc_Lit2Var(pA[i]) == Abc_Lit2Var(Out) )
            for ( j = 0; j < 2; ++j )
                if ( pB[j] == Abc_LitNot(pA[i]) && pB[1-j] == Abc_LitNot(pA[1-i]) )
                    return pA[1-i] ^ !Abc_LitIsCompl(pA[i]);
    return Out;
}

/**Function*************************************************************

  Synopsis    [Creates the manager.]

  Description [The AIG should have one primary output and no constraints.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr2_Man_t * Pdr2_ManStart( Aig_Man_t * pAig, char * pInit, Pdr2_Par_t * pPars )
{
    Pdr2_Man_t * p;
    Aig_Obj_t * pObj;
    int i;
    assert( Saig_ManPoNum(pAig) == 1 );
    assert( Saig_ManConstrNum(pAig) == 0 );
    p = ABC_CALLOC( Pdr2_Man_t, 1 );
    p->pPars     = pPars;
    p->pAig      = pAig;
    p->nRegs     = Saig_ManRegNum( pAig );
    p->nPis      = Saig_ManPiNum( pAig );
    p->nPredictMode = Gip_OptionGet("PDR2_PREDICT") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_PREDICT")))) : 0;
    p->nStrengthenOnDemand = Gip_OptionGet("PDR2_STRENGTHEN_LATE") ? atoi(Gip_OptionGet("PDR2_STRENGTHEN_LATE")) : 0;
    p->nDropHistory = Gip_OptionGet("PDR2_DROP_HISTORY") ? Abc_MaxInt(0, Abc_MinInt(4, atoi(Gip_OptionGet("PDR2_DROP_HISTORY")))) : 0;
    if ( p->nDropHistory ) p->pDropHistory = ABC_CALLOC(unsigned char, (size_t)16 * p->nRegs);
    p->nJoinPush = Gip_OptionGet("PDR2_JOIN_PUSH") ? Abc_MaxInt(0, Abc_MinInt(3, atoi(Gip_OptionGet("PDR2_JOIN_PUSH")))) : 0;
    p->nResolveLimit = Gip_OptionGet("PDR2_RESOLVE") ? Abc_MaxInt(0, Abc_MinInt(1024, atoi(Gip_OptionGet("PDR2_RESOLVE")))) : 0;
    p->nMicGroup = Gip_OptionGet("PDR2_MIC_GROUP") ? Abc_MaxInt(0, Abc_MinInt(8, atoi(Gip_OptionGet("PDR2_MIC_GROUP")))) : 0;
    p->nDropConfLimit = Gip_OptionGet("PDR2_MIC_CONFS") ? Abc_MaxInt(0, Abc_MinInt(10000, atoi(Gip_OptionGet("PDR2_MIC_CONFS")))) : 0;
    p->nDownMode = Gip_OptionGet("PDR2_DOWN_TRIES") ? Abc_MaxInt(0, Abc_MinInt(3, atoi(Gip_OptionGet("PDR2_DOWN_TRIES")))) : 0;
    p->nMicGap = Gip_OptionGet("PDR2_MIC_GAP") ? Abc_MaxInt(0, atoi(Gip_OptionGet("PDR2_MIC_GAP"))) : 0;
    p->nGenTimeMode = Gip_OptionGet("PDR2_GEN_TIME") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_GEN_TIME")))) : 0;
    p->nHintTime = Gip_OptionGet("PDR2_BMC_HINT") ? Abc_MaxInt(0,Abc_MinInt(60,atoi(Gip_OptionGet("PDR2_BMC_HINT")))) : 0;
    p->nHintNext = Gip_OptionGet("PDR2_BMC_HINT_START") ? Abc_MaxInt(0,Abc_MinInt(32,atoi(Gip_OptionGet("PDR2_BMC_HINT_START")))) : 2;
    p->nKindTime = Gip_OptionGet("PDR2_KIND_TIME") ? Abc_MaxInt(0, Abc_MinInt(60, atoi(Gip_OptionGet("PDR2_KIND_TIME")))) : 0;
    p->nKindNext = Gip_OptionGet("PDR2_KIND_MIN") ? Abc_MaxInt(1, atoi(Gip_OptionGet("PDR2_KIND_MIN"))) : 8;
    p->nKindMax = Gip_OptionGet("PDR2_KIND_MAX") ? Abc_MaxInt(1, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_KIND_MAX")))) : 64;
    // The older induction interface has no external cancellation callback.
    // Embedding callers with cancellation or mandatory invariant extraction
    // retain the regular PDR path.
    if ( pPars->pFuncStop || pPars->fVerifyComplete || pPars->fDumpInv || pPars->nPropLimit ) p->nKindTime = 0;
    p->nMicCexMode = Gip_OptionGet("PDR2_MICCEX") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_MICCEX")))) : 0;
    if ( pPars->fUseAbs || p->nRegs == 0 || (ABC_INT64_T)p->nRegs * 8 * sizeof(word) > ((ABC_INT64_T)128 << 20) )
        p->nMicCexMode = 0;
    if ( p->nMicCexMode ) p->pMicCexBits = ABC_CALLOC( word, 8 * p->nRegs );
    p->nReachStride = Gip_OptionGet("PDR2_REACH") ? Abc_MaxInt(0, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_REACH")))) : 0;
    p->fReachFilter = p->nReachStride > 0;
    p->fReachCex = Gip_OptionGet("PDR2_REACHCEX") && atoi(Gip_OptionGet("PDR2_REACHCEX")) > 0;
    if ( p->fReachCex )
        p->nReachStride = Abc_MaxInt(p->nReachStride, Abc_MinInt(256, atoi(Gip_OptionGet("PDR2_REACHCEX"))));
    if ( p->nRegs )
        p->nReachStride = Abc_MinInt(p->nReachStride, (int)(((ABC_INT64_T)128 << 20) /
            (sizeof(word) * ((ABC_INT64_T)p->nRegs + (p->fReachCex ? p->nPis : 0)))));
    // the initial values (NULL = all 0)
    p->pInit     = ABC_CALLOC( char, p->nRegs + 1 );
    p->pInitState = ABC_CALLOC( char, p->nRegs + 1 );
    if ( pInit )
        memcpy( p->pInit, pInit, (size_t)p->nRegs );
    p->timeStart = Abc_Clock();
    p->timeLimit = pPars->nTimeOut ? p->timeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    // SAT infrastructure: static CNF with an optional compact variable space
    p->pCnfMan   = Cnf_ManStart();
    p->pCtx      = Gip_CtxCreatePdr2( pAig, p->pCnfMan,
        Gip_OptionGet("PDR2_COMPACT") && atoi(Gip_OptionGet("PDR2_COMPACT")) );
    if ( Gip_OptionGet("PDR2_SHARED") && atoi(Gip_OptionGet("PDR2_SHARED")) )
    {
        // The extra variables have no defining circuit clauses. Beyond the
        // reserved range, additional frames use ordinary independent solvers.
        int nDeps = p->pCtx->pDepOffset[p->pCtx->nVars];
        p->nSharedSlots = 4096;
        p->nSharedMode = Abc_MaxInt(1, Abc_MinInt(4, atoi(Gip_OptionGet("PDR2_SHARED"))));
        p->iSharedBase = p->pCtx->nVars;
        p->pCtx->nVars += p->nSharedSlots;
        p->pCtx->pDepOffset = ABC_REALLOC( int, p->pCtx->pDepOffset, p->pCtx->nVars + 1 );
        for ( i = p->iSharedBase; i <= p->pCtx->nVars; i++ )
            p->pCtx->pDepOffset[i] = nDeps;
        p->vSharedLemFrame = Vec_IntAlloc( 1000 );
        p->vSharedAssump = Vec_IntAlloc( 100 );
        p->vSharedSeeds = Vec_IntAlloc( 1000 );
    }
    p->pLoVar    = ABC_ALLOC( int, p->nRegs );
    p->pLiLit    = ABC_ALLOC( int, p->nRegs );
    p->pPiVar    = ABC_ALLOC( int, Abc_MaxInt(p->nPis, 1) );
    Saig_ManForEachLo( pAig, pObj, i )
        p->pLoVar[i] = Gip_CtxObjVar( p->pCtx, pObj );
    {
        int fDirect = Gip_OptionGet("PDR2_LI_DRIVER") && atoi(Gip_OptionGet("PDR2_LI_DRIVER"));
        Saig_ManForEachLi( pAig, pObj, i )
            p->pLiLit[i] = Pdr2_ManInputLit(p->pCtx, pObj, fDirect);
    }
    Saig_ManForEachPi( pAig, pObj, i )
        p->pPiVar[i] = Gip_CtxObjVar( p->pCtx, pObj );
    p->nLiftMemoMode = Gip_OptionGet("PDR2_LIFTMEMO") ? Abc_MaxInt(0, Abc_MinInt(3, atoi(Gip_OptionGet("PDR2_LIFTMEMO")))) : 0;
    p->nLiftPiMode = Gip_OptionGet("PDR2_LIFT_PI") ? atoi(Gip_OptionGet("PDR2_LIFT_PI")) & 3 : 0;
    p->nCnfJustMode = Gip_OptionGet("PDR2_CNFJUST") ? Abc_MaxInt(0, Abc_MinInt(3, atoi(Gip_OptionGet("PDR2_CNFJUST")))) : 0;
    p->nInputScope = Gip_OptionGet("PDR2_INPUT_SCOPE") ? atoi(Gip_OptionGet("PDR2_INPUT_SCOPE")) & 31 : 0;
    p->nInputBadLimit = Gip_OptionGet("PDR2_INPUT_BAD_CONFS") ? Abc_MaxInt(0,atoi(Gip_OptionGet("PDR2_INPUT_BAD_CONFS"))) : -1;
    if ( pPars->fUseAbs || pPars->nInputPolicy ) p->nInputScope = 0;
    if ( p->nInputScope && !Gip_OptionGet("PDR2_CNFJUST") ) p->nCnfJustMode = 3;
    if ( pPars->nInputPolicy ) p->nCnfJustMode = pPars->nInputPolicy < 0 ? 0 : pPars->nInputPolicy == 1 ? 1 : 3;
    if ( pPars->fUseAbs || pPars->nLiftSim ) p->nCnfJustMode = 0;
    if ( p->nCnfJustMode )
    {
        p->pCnfJustMark = ABC_CALLOC( char, p->pCtx->nVars );
        p->vCnfJustWork = Vec_IntAlloc( 1000 );
    }
    p->nBadPhaseConfs = Gip_OptionGet("PDR2_BAD_REPHASE") ? Abc_MaxInt(0, atoi(Gip_OptionGet("PDR2_BAD_REPHASE"))) : 0;
    // Start with the concrete engine; abstract pseudo-inputs need separate mapping.
    if ( pPars->fUseAbs ) p->nLiftMemoMode = 0;
    if ( p->nLiftMemoMode )
    {
        p->pLiftMemo = ABC_CALLOC( Pdr2_LiftMemo_t *, 4096 );
        p->pLiftMemoNext = ABC_CALLOC( unsigned char, 256 );
        p->vLiftMemoKey = Vec_IntAlloc( 100 );
        p->vLiftMemoCore = Vec_IntAlloc( 100 );
    }
    if ( pPars->fSparseLift || p->nLiftMemoMode || p->nCnfJustMode )
    {
        p->pVar2Ci = ABC_ALLOC( int, p->pCtx->nVars + 1 );
        for ( i = 0; i <= p->pCtx->nVars; i++ )
            p->pVar2Ci[i] = -1;
        for ( i = 0; i < p->nPis; i++ )
            p->pVar2Ci[p->pPiVar[i]] = i;
        for ( i = 0; i < p->nRegs; i++ )
            p->pVar2Ci[p->pLoVar[i]] = p->nPis + i;
        p->vLiftCis = Vec_IntAlloc( 100 );
    }
    p->VarBad    = Gip_CtxObjVar( p->pCtx, Aig_ManCo(pAig, 0) );
    p->nBadRootMode = Gip_OptionGet("PDR2_BADROOT") ? Abc_MaxInt(0, Abc_MinInt(2, atoi(Gip_OptionGet("PDR2_BADROOT")))) : 0;
    p->GuardLit = p->GuardLo = p->GuardLi = -1;
    if ( Gip_OptionGet("PDR2_TRACE_GUARD") && !pPars->fUseAbs &&
         !pPars->nInitLiReg && !pPars->nLiftSim &&
         !Aig_ManBufNum(pAig) && !Aig_ManExorNum(pAig) )
    {
        int Mode = atoi(Gip_OptionGet("PDR2_TRACE_GUARD"));
        int Guard = Mode > 0 ? Pdr2_ManFindGuard(pAig, Mode >= 2) : -1;
        if ( Guard >= 0 )
        {
            p->GuardLit = Guard;
            p->GuardLo = Pdr2_LitLo(p, Guard);
            if ( Mode >= 2 ) p->GuardLi = Pdr2_LitLi(p, Guard);
            if ( pPars->fVerbose && !pPars->fSilent )
                Abc_Print(1, "Bad-trace guard: flop %d = %d, next-state restriction %d.\n",
                            Abc_Lit2Var(Guard), !Abc_LitIsCompl(Guard), p->GuardLi >= 0);
        }
    }
    p->vSolvers  = Vec_PtrAlloc( 100 );
    p->pInf      = Pdr2_ManNewSolver( p, 0 );
    p->pLift     = Pdr2_ManNewSolver( p, PDR2_SOLVER_UNRESTRICTED );
    if ( Gip_OptionGet("PDR2_RECYCLE_LIFT") && Gip_OptionGet("PDR2_RECYCLE") )
        p->pLift->nRecycleMode = atoi(Gip_OptionGet("PDR2_RECYCLE")) & 3;
    // frames
    p->vFrames   = Vec_PtrAlloc( 100 );
    p->vInf      = Vec_PtrAlloc( 100 );
    p->vGarbage  = Vec_PtrAlloc( 100 );
    p->vMicScratch = Vec_PtrAlloc( 4 );
    p->pWatch    = ABC_CALLOC( Vec_Ptr_t, 2 * p->nRegs + 2 );
    p->pOcc      = ABC_CALLOC( Vec_Ptr_t, 2 * p->nRegs + 2 );
    p->iEarly    = 1;
    p->vLemFrame = Vec_IntAlloc( 1000 );
    p->IdInit = Vec_IntSize( p->vLemFrame );  Vec_IntPush( p->vLemFrame, 0 );
    p->IdProp = Vec_IntSize( p->vLemFrame );  Vec_IntPush( p->vLemFrame, 0 );
    p->IdInf  = Vec_IntSize( p->vLemFrame );  Vec_IntPush( p->vLemFrame, GIP_FRAME_INF );
    p->iCoreFrame = GIP_FRAME_INF;
    p->fTimeGenCheck = Gip_OptionGet("PDR2_TIMEGEN_CHECK") != NULL;
    p->vLog      = Vec_PtrAlloc( 1000 );
    p->vLogFrame = Vec_IntAlloc( 1000 );
    p->vCtiFree  = Vec_IntAlloc( 100 );
    // obligations
    p->vQueue    = Vec_PtrAlloc( 1000 );
    // abstraction
    p->pAbs      = ABC_CALLOC( char, p->nRegs );
    p->pAbsUsed  = ABC_CALLOC( char, p->nRegs );
    p->pAbsVals  = ABC_ALLOC( char, 2 * Aig_ManObjNumMax(pAig) );
    // activity
    p->pAct      = ABC_CALLOC( double, p->nRegs );
    p->ActInc    = 1.0;
    // scratch
    p->vLastAssump = Vec_IntAlloc( 100 );
    p->vRelInd   = Vec_IntAlloc( 100 );
    p->vLits4    = Vec_IntAlloc( 100 );
    p->vAssump   = Vec_IntAlloc( 100 );
    p->vCst1     = Vec_IntAlloc( 100 );
    p->vCst2     = Vec_IntAlloc( 100 );
    p->vLem      = Vec_IntAlloc( 100 );
    p->vLift1    = Vec_IntAlloc( 100 );
    p->vLift2    = Vec_IntAlloc( 100 );
    p->vLift3    = Vec_IntAlloc( 100 );
    p->pLitMark  = ABC_CALLOC( char, 2 * p->nRegs + 2 );
    p->pVarMark  = ABC_CALLOC( char, p->pCtx->nVars + 1 );
    p->RandState = (unsigned)pPars->nRandomSeed * 2654435761u + 12345u;
    p->iResetFlop = -1;
    if ( pPars->fUseAbs && pPars->nAbsStart == 0 )
        Pdr2_ManAbsStart( p );
    if ( pPars->nInitLiReg )
    {
        assert(pPars->nInitLiReg > 0 && pPars->nInitLiReg <= p->nRegs && !pPars->fUseAbs);
        p->pInitSat = Pdr2_ManNewSolver(p,1);
        p->vInitAssump = Vec_IntAlloc(100);
        p->nHintTime = p->nKindTime = p->nReachStride = p->fReachCex = p->fReachFilter = 0;
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Deletes the manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManStop( Pdr2_Man_t * p )
{
    Gip_Solver_t * pSat;
    Vec_Ptr_t * vFrame;
    Pdr2_Lem_t * pLem;
    Pdr2_Obl_t * pObl;
    int i, k;
    if ( p->pAig->pFanData )
        Aig_ManFanoutStop( p->pAig );
    Pdr2_ManCollectGarbage( p, 1 );
    Pdr2_QueueClear( p );
    Vec_PtrFree( p->vQueue );
    if ( p->pCexObl )
        Pdr2_OblDeref( p->pCexObl );
    Vec_PtrForEachEntry( Vec_Ptr_t *, p->vFrames, vFrame, k )
    {
        Vec_PtrForEachEntry( Pdr2_Lem_t *, vFrame, pLem, i )
        {
            Pdr2_CubeDeref( pLem->pCube );
            if ( pLem->pObl ) Pdr2_OblDeref( pLem->pObl );
            ABC_FREE( pLem );
        }
        Vec_PtrFree( vFrame );
    }
    Vec_PtrFree( p->vFrames );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
    {
        Pdr2_CubeDeref( pLem->pCube );
        if ( pLem->pObl ) Pdr2_OblDeref( pLem->pObl );
        ABC_FREE( pLem );
    }
    Vec_PtrFree( p->vInf );
    Vec_PtrFree( p->vGarbage );
    Vec_PtrFreeFree( p->vMicScratch );
    ABC_FREE( p->pCtiVal );
    ABC_FREE( p->pCtiMask );
    ABC_FREE( p->pCtiLive );
    ABC_FREE( p->pCtiLem );
    ABC_FREE( p->pCtiFrame );
    Vec_IntFree( p->vCtiFree );
    for ( i = 0; i < 2 * p->nRegs + 2; i++ )
    {
        ABC_FREE( p->pWatch[i].pArray );
        ABC_FREE( p->pOcc[i].pArray );
    }
    ABC_FREE( p->pWatch );
    ABC_FREE( p->pOcc );
    {
        Pdr2_Cube_t * pCube;
        Vec_PtrForEachEntry( Pdr2_Cube_t *, p->vLog, pCube, i )
            Pdr2_CubeDeref( pCube );
        Vec_PtrFree( p->vLog );
        Vec_IntFree( p->vLogFrame );
        Vec_IntFree( p->vLemFrame );
    }
    Vec_PtrForEachEntry( Gip_Solver_t *, p->vSolvers, pSat, i )
        if ( pSat->pShared )
        {
            Vec_IntFreeP( &pSat->vSharedDomain );
            ABC_FREE( pSat );
        }
        else
            Gip_SolverFree( pSat );
    Vec_PtrFree( p->vSolvers );
    if ( p->pShared ) Gip_SolverFree( p->pShared );
    Vec_IntFreeP( &p->vSharedLemFrame );
    Vec_IntFreeP( &p->vSharedAssump );
    Vec_IntFreeP( &p->vSharedSeeds );
    Gip_SolverFree( p->pInf );
    Gip_SolverFree( p->pLift );
    Pdr2_ManStopBadSat( p );
    if ( p->pInitSat ) Gip_SolverFree(p->pInitSat);
    if ( p->pBadRoot ) Gip_SolverFree(p->pBadRoot);
    Vec_IntFreeP(&p->vInitAssump);
    Gip_CtxFree( p->pCtx );
    Cnf_ManStop( p->pCnfMan );
    ABC_FREE( p->pLoVar );
    ABC_FREE( p->pLiLit );
    ABC_FREE( p->pPiVar );
    ABC_FREE( p->pVar2Ci );
    ABC_FREE( p->pCnfJustMark );
    Vec_IntFreeP( &p->vCnfJustWork );
    Vec_IntFreeP( &p->vLiftCis );
    if ( p->pLiftMemo )
        for ( i = 0; i < 4096; i++ )
            ABC_FREE( p->pLiftMemo[i] );
    ABC_FREE( p->pLiftMemo );
    ABC_FREE( p->pLiftMemoNext );
    ABC_FREE( p->pMicCexBits );
    Vec_IntFreeP( &p->vLiftMemoKey );
    Vec_IntFreeP( &p->vLiftMemoCore );
    ABC_FREE( p->pDropHistory );
    ABC_FREE( p->pAct );
    ABC_FREE( p->pInit );
    ABC_FREE( p->pSimInitBound );
    ABC_FREE( p->pPhaseSimState );
    ABC_FREE( p->pPhaseSimValues );
    ABC_FREE( p->pInitState );
    ABC_FREE( p->pReachStates );
    ABC_FREE( p->pReachInputs );
    if ( p->pReachCex ) Abc_CexFree( p->pReachCex );
    ABC_FREE( p->pAbs );
    ABC_FREE( p->pAbsUsed );
    ABC_FREE( p->pAbsVals );
    ABC_FREE( p->pLiftVals );
    ABC_FREE( p->pLiftMark );
    ABC_FREE( p->pLiftPi );
    ABC_FREE( p->pLiftTrav );
    Vec_IntFreeP( &p->vLiftCone );
    Vec_IntFreeP( &p->vLiftUndo );
    Vec_IntFreeP( &p->vLiftWork );
    Vec_IntFreeP( &p->vLiftJust );
    Vec_IntFreeP( &p->vLiftVisit );
    Vec_IntFree( p->vLastAssump );
    Vec_IntFree( p->vRelInd );
    Vec_IntFree( p->vLits4 );
    Vec_IntFree( p->vAssump );
    Vec_IntFree( p->vCst1 );
    Vec_IntFree( p->vCst2 );
    Vec_IntFree( p->vLem );
    Vec_IntFree( p->vLift1 );
    Vec_IntFree( p->vLift2 );
    Vec_IntFree( p->vLift3 );
    ABC_FREE( p->pLitMark );
    ABC_FREE( p->pVarMark );
    ABC_FREE( p );
    (void)pObl;
}

/**Function*************************************************************

  Synopsis    [Cubes: sorted, signed, reference counted.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_IntCompare( const void * pa, const void * pb )
{
    return *(const int *)pa - *(const int *)pb;
}
Pdr2_Cube_t * Pdr2_CubeAlloc( int * pLits, int nLits )
{
    Pdr2_Cube_t * p;
    int i;
    p = (Pdr2_Cube_t *)ABC_ALLOC( char, sizeof(Pdr2_Cube_t) + sizeof(int) * Abc_MaxInt(nLits - 1, 0) );
    p->nRefs = 1;
    p->nLits = nLits;
    p->Sign  = 0;
    if ( nLits > 0 )
        memcpy( p->Lits, pLits, sizeof(int) * nLits );
    // insertion sort (cubes are short) with fallback to qsort
    if ( nLits > 32 )
        qsort( p->Lits, (size_t)nLits, sizeof(int), Pdr2_IntCompare );
    else
    {
        int j, k, Lit;
        for ( j = 1; j < nLits; j++ )
        {
            Lit = p->Lits[j];
            for ( k = j - 1; k >= 0 && p->Lits[k] > Lit; k-- )
                p->Lits[k+1] = p->Lits[k];
            p->Lits[k+1] = Lit;
        }
    }
    for ( i = 0; i < nLits; i++ )
    {
        assert( i == 0 || p->Lits[i-1] < p->Lits[i] );
        p->Sign |= Pdr2_LitSign( p->Lits[i] );
    }
    return p;
}
Pdr2_Cube_t * Pdr2_CubeAllocVec( Vec_Int_t * vLits )
{
    return Pdr2_CubeAlloc( Vec_IntArray(vLits), Vec_IntSize(vLits) );
}
void Pdr2_CubeRef( Pdr2_Cube_t * p )
{
    p->nRefs++;
}
void Pdr2_CubeDeref( Pdr2_Cube_t * p )
{
    assert( p->nRefs > 0 );
    if ( --p->nRefs == 0 )
        ABC_FREE( p );
}
// returns 1 if the literal set of pA is contained in that of pB
int Pdr2_CubeSubsume( Pdr2_Cube_t * pA, Pdr2_Cube_t * pB )
{
    int i, k;
    if ( pA->nLits > pB->nLits )
        return 0;
    if ( pA->Sign & ~pB->Sign )
        return 0;
    for ( i = k = 0; i < pA->nLits; i++ )
    {
        while ( k < pB->nLits && pB->Lits[k] < pA->Lits[i] )
            k++;
        if ( k == pB->nLits || pB->Lits[k] != pA->Lits[i] )
            return 0;
        k++;
    }
    return 1;
}
int Pdr2_CubeEqual( Pdr2_Cube_t * pA, Pdr2_Cube_t * pB )
{
    return pA->nLits == pB->nLits && pA->Sign == pB->Sign && !memcmp( pA->Lits, pB->Lits, sizeof(int) * pA->nLits );
}
// returns 1 if the literals of pA are all marked (pB's literals are marked in pLitMark)
int Pdr2_CubeSubsumeMarked( Pdr2_Man_t * p, Pdr2_Cube_t * pA, Pdr2_Cube_t * pB )
{
    int i;
    if ( pA->nLits > pB->nLits )
        return 0;
    if ( pA->Sign & ~pB->Sign )
        return 0;
    for ( i = 0; i < pA->nLits; i++ )
        if ( !p->pLitMark[pA->Lits[i]] )
            return 0;
    return 1;
}
void Pdr2_CubeToVec( Pdr2_Cube_t * p, Vec_Int_t * vLits )
{
    int i;
    Vec_IntClear( vLits );
    for ( i = 0; i < p->nLits; i++ )
        Vec_IntPush( vLits, p->Lits[i] );
}

/**Function*************************************************************

  Synopsis    [Proof obligations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr2_Obl_t * Pdr2_OblAlloc( Pdr2_Man_t * p, int iFrame, Pdr2_Cube_t * pState, Vec_Int_t * vInputs, Vec_Int_t * vPpis, int nDepth, Pdr2_Obl_t * pNext )
{
    Pdr2_Obl_t * pObl = ABC_CALLOC( Pdr2_Obl_t, 1 );
    pObl->nRefs   = 1;
    pObl->iFrame  = iFrame;
    pObl->nDepth  = nDepth;
    pObl->iPos    = -1;
    pObl->Id      = p->nOblIds++;
    pObl->Act     = 0.0;
    pObl->pState  = pState;  Pdr2_CubeRef( pState );
    pObl->vInputs = vInputs ? Vec_IntDup( vInputs ) : Vec_IntAlloc( 0 );
    pObl->vPpis   = vPpis ? Vec_IntDup( vPpis ) : Vec_IntAlloc( 0 );
    pObl->pNext   = pNext;   if ( pNext ) Pdr2_OblRef( pNext );
    p->nObls++;
    p->nOblLits += pState->nLits;
    return pObl;
}
void Pdr2_OblRef( Pdr2_Obl_t * p )
{
    p->nRefs++;
}
void Pdr2_OblDeref( Pdr2_Obl_t * p )
{
    while ( p )
    {
        Pdr2_Obl_t * pNext;
        assert( p->nRefs > 0 );
        if ( --p->nRefs > 0 )
            return;
        assert( p->iPos == -1 );
        pNext = p->pNext;
        Pdr2_CubeDeref( p->pState );
        Vec_IntFree( p->vInputs );
        Vec_IntFree( p->vPpis );
        ABC_FREE( p );
        p = pNext;
    }
}
void Pdr2_OblPushTo( Pdr2_Obl_t * p, int iFrame )
{
    int i;
    for ( i = p->iFrame; i < iFrame; i++ )
        p->Act *= 0.6;
    p->iFrame = iFrame;
}

/**Function*************************************************************

  Synopsis    [Priority queue of obligations: binary heap.]

  Description [Order: lowest frame, then largest depth, then shortest cube,
  then lexicographically smaller cube, then earlier creation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr2_OblBefore( Pdr2_Man_t * p, Pdr2_Obl_t * a, Pdr2_Obl_t * b )
{
    int i;
    if ( a->iFrame != b->iFrame )
        return a->iFrame < b->iFrame;
    if ( p->pPars->nQueueOrder == 1 )
    {
        // shortest cube first, then the newest obligation (treb with -ssize)
        if ( a->pState->nLits != b->pState->nLits )
            return a->pState->nLits < b->pState->nLits;
        return a->Id > b->Id;
    }
    if ( p->pPars->nQueueOrder == 2 )
        return a->Stamp > b->Stamp;  // most recently queued first (treb's default: a requeued obligation is new again)
    if ( p->pPars->nQueueOrder == 3 )
    {
        if ( a->pState->nLits != b->pState->nLits )
            return a->pState->nLits < b->pState->nLits;
        return a->Stamp > b->Stamp;
    }
    if ( a->nDepth != b->nDepth )
        return a->nDepth > b->nDepth;
    if ( a->pState->nLits != b->pState->nLits )
        return a->pState->nLits < b->pState->nLits;
    for ( i = 0; i < a->pState->nLits; i++ )
        if ( a->pState->Lits[i] != b->pState->Lits[i] )
            return a->pState->Lits[i] < b->pState->Lits[i];
    return a->Id < b->Id;
}
static inline void Pdr2_QueueSet( Vec_Ptr_t * vHeap, int i, Pdr2_Obl_t * pObl )
{
    Vec_PtrWriteEntry( vHeap, i, pObl );
    pObl->iPos = i;
}
static void Pdr2_QueueSiftUp( Pdr2_Man_t * p, int i )
{
    Vec_Ptr_t * vHeap = p->vQueue;
    Pdr2_Obl_t * pObl = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, i );
    while ( i > 0 )
    {
        int iPar = (i - 1) >> 1;
        Pdr2_Obl_t * pPar = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, iPar );
        if ( !Pdr2_OblBefore( p, pObl, pPar ) )
            break;
        Pdr2_QueueSet( vHeap, i, pPar );
        i = iPar;
    }
    Pdr2_QueueSet( vHeap, i, pObl );
}
static void Pdr2_QueueSiftDown( Pdr2_Man_t * p, int i )
{
    Vec_Ptr_t * vHeap = p->vQueue;
    Pdr2_Obl_t * pObl = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, i );
    int nSize = Vec_PtrSize( vHeap );
    while ( 1 )
    {
        int iLeft = 2*i + 1, iRight = iLeft + 1, iChild;
        Pdr2_Obl_t * pChild;
        if ( iLeft >= nSize )
            break;
        iChild = iLeft;
        if ( iRight < nSize && Pdr2_OblBefore( p, (Pdr2_Obl_t *)Vec_PtrEntry(vHeap, iRight), (Pdr2_Obl_t *)Vec_PtrEntry(vHeap, iLeft) ) )
            iChild = iRight;
        pChild = (Pdr2_Obl_t *)Vec_PtrEntry( vHeap, iChild );
        if ( !Pdr2_OblBefore( p, pChild, pObl ) )
            break;
        Pdr2_QueueSet( vHeap, i, pChild );
        i = iChild;
    }
    Pdr2_QueueSet( vHeap, i, pObl );
}
void Pdr2_QueuePush( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    assert( pObl->iPos == -1 );
    Pdr2_OblRef( pObl );
    pObl->Stamp = (int)++p->nQueuePushes;
    Vec_PtrPush( p->vQueue, pObl );
    pObl->iPos = Vec_PtrSize(p->vQueue) - 1;
    Pdr2_QueueSiftUp( p, pObl->iPos );
}
// removes the obligation at the given heap position; the caller owns the returned reference
static Pdr2_Obl_t * Pdr2_QueueRemoveAt( Pdr2_Man_t * p, int i )
{
    Pdr2_Obl_t * pObl = (Pdr2_Obl_t *)Vec_PtrEntry( p->vQueue, i );
    Pdr2_Obl_t * pLast = (Pdr2_Obl_t *)Vec_PtrPop( p->vQueue );
    assert( pObl->iPos == i );
    pObl->iPos = -1;
    if ( pLast != pObl )
    {
        Pdr2_QueueSet( p->vQueue, i, pLast );
        Pdr2_QueueSiftUp( p, i );
        Pdr2_QueueSiftDown( p, pLast->iPos );
    }
    return pObl;
}
Pdr2_Obl_t * Pdr2_QueuePop( Pdr2_Man_t * p, int iFrameMax )
{
    Pdr2_Obl_t * pObl;
    if ( Vec_PtrSize(p->vQueue) == 0 )
        return NULL;
    pObl = (Pdr2_Obl_t *)Vec_PtrEntry( p->vQueue, 0 );
    if ( pObl->iFrame > iFrameMax )
        return NULL;
    return Pdr2_QueueRemoveAt( p, 0 );
}
int Pdr2_QueueRemove( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    if ( pObl->iPos == -1 )
        return 0;
    Pdr2_QueueRemoveAt( p, pObl->iPos );
    Pdr2_OblDeref( pObl );
    return 1;
}
void Pdr2_QueueClear( Pdr2_Man_t * p )
{
    Pdr2_Obl_t * pObl;
    int i;
    Vec_PtrForEachEntry( Pdr2_Obl_t *, p->vQueue, pObl, i )
    {
        pObl->iPos = -1;
        Pdr2_OblDeref( pObl );
    }
    Vec_PtrClear( p->vQueue );
}

/**Function*************************************************************

  Synopsis    [Lemma records.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Pdr2_ManIndexAdd( Pdr2_Man_t * p, Pdr2_Lem_t * pLem )
{
    int i, Lit, iBest = -1, nBest = ABC_INFINITY;
    for ( i = 0; i < pLem->pCube->nLits; i++ )
    {
        Lit = pLem->pCube->Lits[i];
        Vec_PtrPush( &p->pOcc[Lit], pLem );
        if ( Vec_PtrSize(&p->pWatch[Lit]) < nBest )
        {
            nBest = Vec_PtrSize( &p->pWatch[Lit] );
            iBest = Lit;
        }
    }
    assert( iBest >= 0 );
    Vec_PtrPush( &p->pWatch[iBest], pLem );
}
// creates a lemma record and, for frames 1 and above, indexes it; the record takes the given id
// (an existing entry of the frame table, whose clauses the record inherits) or a new one (Id < 0)
Pdr2_Lem_t * Pdr2_LemAllocId( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame, int Id )
{
    Pdr2_Lem_t * pLem = ABC_CALLOC( Pdr2_Lem_t, 1 );
    pLem->pCube  = pCube;  Pdr2_CubeRef( pCube );
    pLem->pObl   = pObl;   if ( pObl ) Pdr2_OblRef( pObl );
    pLem->iFrame = iFrame;
    pLem->iSlot  = -1;
    pLem->iCti   = -1;
    pLem->iCtiInf = -1;
    if ( Id >= 0 )
    {
        pLem->Id = Id;
        Vec_IntWriteEntry( p->vLemFrame, Id, iFrame == -1 ? GIP_FRAME_INF : iFrame );
    }
    else
    {
        pLem->Id = Vec_IntSize( p->vLemFrame );
        Vec_IntPush( p->vLemFrame, iFrame == -1 ? GIP_FRAME_INF : iFrame );
    }
    if ( iFrame != 0 )
        Pdr2_ManIndexAdd( p, pLem );
    return pLem;
}
Pdr2_Lem_t * Pdr2_LemAlloc( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, Pdr2_Obl_t * pObl, int iFrame )
{
    return Pdr2_LemAllocId( p, pCube, pObl, iFrame, -1 );
}
// appends a lemma to a frame vector, recording its position
void Pdr2_LemPush( Vec_Ptr_t * vFrame, Pdr2_Lem_t * pLem )
{
    pLem->iSlot = Vec_PtrSize( vFrame );
    Vec_PtrPush( vFrame, pLem );
}
// the position of a lemma in its frame vector: the recorded one if it is still valid
int Pdr2_LemFind( Vec_Ptr_t * vFrame, Pdr2_Lem_t * pLem )
{
    int i;
    if ( pLem->iSlot >= 0 && pLem->iSlot < Vec_PtrSize(vFrame) && Vec_PtrEntry(vFrame, pLem->iSlot) == pLem )
        return pLem->iSlot;
    for ( i = 0; i < Vec_PtrSize(vFrame); i++ )
        if ( Vec_PtrEntry(vFrame, i) == pLem )
            return pLem->iSlot = i;
    return -1;
}
// swap-removes the lemma at the given position; the record goes to the garbage list
// (it stays in the index lists, marked removed, until the next index rebuild)
void Pdr2_LemRemove( Pdr2_Man_t * p, Vec_Ptr_t * vFrame, int iPos )
{
    Pdr2_Lem_t * pLem = (Pdr2_Lem_t *)Vec_PtrEntry( vFrame, iPos );
    Pdr2_Lem_t * pLast = (Pdr2_Lem_t *)Vec_PtrPop( vFrame );
    if ( pLast != pLem )
    {
        Vec_PtrWriteEntry( vFrame, iPos, pLast );
        pLast->iSlot = iPos;
    }
    pLem->fRemoved = 1;
    Pdr2_LemFreeCti( p, pLem, 0 );
    Vec_PtrPush( p->vGarbage, pLem );
}
// rebuilds the index lists from the live records
void Pdr2_ManIndexRebuild( Pdr2_Man_t * p )
{
    Pdr2_Lem_t * pLem;
    int i, k;
    for ( i = 0; i < 2 * p->nRegs + 2; i++ )
    {
        Vec_PtrClear( &p->pWatch[i] );
        Vec_PtrClear( &p->pOcc[i] );
    }
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            Pdr2_ManIndexAdd( p, pLem );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        Pdr2_ManIndexAdd( p, pLem );
}
// finds a live lemma whose cube is contained in pCube, among lemmas of frames
// iFrameMin..iFrameMax (and of infinity if fInf); returns the one with the highest
// frame (infinity counts highest); with fEqualOnly, only an equal lemma qualifies
Pdr2_Lem_t * Pdr2_ManIndexFindSubsuming( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, int iFrameMin, int iFrameMax, int fInf, int fEqualOnly, int fLowest )
{
    Pdr2_Lem_t * pLem, * pBest = NULL;
    int i, k, Lit;
    // (each record is in one watch list and the cube's literals are distinct: no record is
    // visited twice)
    for ( i = 0; i < pCube->nLits; i++ )
        p->pLitMark[pCube->Lits[i]] = 1;
    for ( i = 0; i < pCube->nLits; i++ )
    {
        Lit = pCube->Lits[i];
        Vec_PtrForEachEntry( Pdr2_Lem_t *, &p->pWatch[Lit], pLem, k )
        {
            if ( pLem->fRemoved )
                continue;
            if ( pLem->iFrame == -1 ? !fInf : (pLem->iFrame < iFrameMin || pLem->iFrame > iFrameMax) )
                continue;
            if ( fEqualOnly && pLem->pCube->nLits != pCube->nLits )
                continue;
            if ( !Pdr2_CubeSubsumeMarked( p, pLem->pCube, pCube ) )
                continue;
            if ( fLowest )
            {
                // prefer the lowest finite frame; infinity only if no finite frame qualifies
                if ( pBest == NULL || pBest->iFrame == -1 || (pLem->iFrame != -1 && pLem->iFrame < pBest->iFrame) )
                    pBest = pLem;
                if ( pBest->iFrame == iFrameMin )
                    break;
            }
            else
            {
                if ( pBest == NULL || pLem->iFrame == -1 || (pBest->iFrame != -1 && pLem->iFrame > pBest->iFrame) )
                    pBest = pLem;
                if ( pBest->iFrame == -1 )
                    break;
            }
        }
        if ( pBest && (fLowest ? pBest->iFrame == iFrameMin : pBest->iFrame == -1) )
            break;
    }
    for ( i = 0; i < pCube->nLits; i++ )
        p->pLitMark[pCube->Lits[i]] = 0;
    return pBest;
}
// frees the removed lemma records once they are purged from the index
void Pdr2_ManCollectGarbage( Pdr2_Man_t * p, int fForce )
{
    Pdr2_Lem_t * pLem;
    int i, k, nLive = Vec_PtrSize( p->vInf );
    if ( Vec_PtrSize(p->vGarbage) == 0 )
        return;
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        nLive += Vec_PtrSize( Pdr2_ManFrame(p, k) );
    // the index is rebuilt after 1000 removals or when the removed records reach 1/8 of the live
    // ones; the rebuilds cost under 1% of the run time on the IWLS examples with the most lemmas
    // (Ex76, Ex57: 1.4 s in 250 s, up to 30,000 live lemmas); a proportional threshold alone
    // would change the order of the index lists and thereby the search trajectories
    if ( !fForce && Vec_PtrSize(p->vGarbage) < 1000 && Vec_PtrSize(p->vGarbage) * 8 < nLive )
        return;
    if ( !fForce )
        Pdr2_ManIndexRebuild( p );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vGarbage, pLem, i )
    {
        Pdr2_CubeDeref( pLem->pCube );
        if ( pLem->pObl ) Pdr2_OblDeref( pLem->pObl );
        Pdr2_LemFreeCti( p, pLem, 1 );
        ABC_FREE( pLem );
    }
    Vec_PtrClear( p->vGarbage );
}

/**Function*************************************************************

  Synopsis    [Pool of cached counterexamples to propagation.]

  Description [A failed propagation query of a lemma at frame k yields a
  state of F_k (resp. of the inf lemmas for k = -1) with a transition into
  the lemma's cube. The state stays a counterexample as long as no lemma
  added later to a frame >= k (or to infinity) excludes it; unknown
  (unassigned) latches never let a lemma exclude the state. The states
  are stored bit-parallel (one row of words per flop) so that each new
  lemma is checked against all cached states at once; this check is run
  lazily over the lemma log before a cached state is used.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr2_CtiCapNext( Pdr2_Man_t * p ) { return p->nCtiCap ? 2 * p->nCtiCap : 1024; }
static void Pdr2_CtiPoolGrow( Pdr2_Man_t * p )
{
    int nCapNew = Pdr2_CtiCapNext( p );
    int nOld = p->nCtiCap / 64, nNew = nCapNew / 64, i;
    word * pVal  = ABC_CALLOC( word, (size_t)p->nRegs * nNew );
    word * pMask = ABC_CALLOC( word, (size_t)p->nRegs * nNew );
    for ( i = 0; i < p->nRegs && nOld; i++ )
    {
        memcpy( pVal  + (size_t)i * nNew, p->pCtiVal  + (size_t)i * nOld, sizeof(word) * nOld );
        memcpy( pMask + (size_t)i * nNew, p->pCtiMask + (size_t)i * nOld, sizeof(word) * nOld );
    }
    ABC_FREE( p->pCtiVal );
    ABC_FREE( p->pCtiMask );
    p->pCtiVal  = pVal;
    p->pCtiMask = pMask;
    p->pCtiLive = ABC_REALLOC( word, p->pCtiLive, nNew );
    memset( p->pCtiLive + nOld, 0, sizeof(word) * (nNew - nOld) );
    p->pCtiLem   = ABC_REALLOC( Pdr2_Lem_t *, p->pCtiLem, nCapNew );
    p->pCtiFrame = ABC_REALLOC( int, p->pCtiFrame, nCapNew );
    p->nCtiCap = nCapNew;
}
static inline void Pdr2_CtiSlotFree( Pdr2_Man_t * p, int Slot )
{
    p->pCtiLive[Slot >> 6] &= ~((word)1 << (Slot & 63));
    p->pCtiLem[Slot] = NULL;
    Vec_IntPush( p->vCtiFree, Slot );
}
void Pdr2_LemFreeCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, int fInfToo )
{
    if ( pLem->iCti >= 0 )
    {
        Pdr2_CtiSlotFree( p, pLem->iCti );
        pLem->iCti = -1;
    }
    if ( fInfToo && pLem->iCtiInf >= 0 )
    {
        Pdr2_CtiSlotFree( p, pLem->iCtiInf );
        pLem->iCtiInf = -1;
    }
}
// a pushed lemma (a subset of the literals of pFrom) keeps the counterexample to
// propagation to infinity: the state still has a transition into the larger cube
void Pdr2_LemInheritInfCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, Pdr2_Lem_t * pFrom )
{
    int i, Slot, nStride, Var, fOutside = 0;
    word Bit;
    if ( pFrom == NULL || pFrom->iCtiInf < 0 )
        return;
    assert( pLem->iCtiInf < 0 );
    Slot = pFrom->iCtiInf;
    pFrom->iCtiInf = -1;
    // the state must lie outside the (larger) pushed cube: some literal is known false
    nStride = p->nCtiCap / 64;
    Bit = (word)1 << (Slot & 63);
    for ( i = 0; i < pLem->pCube->nLits && !fOutside; i++ )
    {
        Var = Abc_Lit2Var( pLem->pCube->Lits[i] );
        if ( !(p->pCtiMask[(size_t)Var * nStride + (Slot >> 6)] & Bit) )
            continue;
        if ( ((p->pCtiVal[(size_t)Var * nStride + (Slot >> 6)] & Bit) != 0) == Abc_LitIsCompl(pLem->pCube->Lits[i]) )
            fOutside = 1;
    }
    if ( !fOutside )
    {
        Pdr2_CtiSlotFree( p, Slot );
        return;
    }
    pLem->iCtiInf = Slot;
    p->pCtiLem[Slot] = pLem;
}
// applies the lemmas logged since the last call: a cached state excluded by a new lemma is dropped
static void Pdr2_CtiApplyLog( Pdr2_Man_t * p )
{
    Pdr2_Cube_t * pCube;
    int j, k, w, nWords = (p->nCtiUsed + 63) / 64, nStride = p->nCtiCap / 64, Frame, Slot;
    word r, * pRow;
    for ( j = 0; j < Vec_PtrSize(p->vLog); j++ )
    {
        pCube = (Pdr2_Cube_t *)Vec_PtrEntry( p->vLog, j );
        Frame = Vec_IntEntry( p->vLogFrame, j );
        for ( w = 0; w < nWords; w++ )
        {
            r = p->pCtiLive[w];
            for ( k = 0; k < pCube->nLits && r; k++ )
            {
                int Var = Abc_Lit2Var( pCube->Lits[k] );
                pRow = p->pCtiVal + (size_t)Var * nStride;
                // a literal known to be false in the state keeps the state outside the cube;
                // an unknown latch does not (several lemmas may jointly exclude all completions)
                r &= (Abc_LitIsCompl(pCube->Lits[k]) ? ~pRow[w] : pRow[w]) | ~p->pCtiMask[(size_t)Var * nStride + w];
            }
            // the states in r may satisfy the cube: they are dropped if the new lemma
            // belongs to their frame
            while ( r )
            {
                Slot = 64 * w + Abc_Tt6FirstBit( r );
                r &= r - 1;
                if ( Frame != -1 && (p->pCtiFrame[Slot] == -1 || p->pCtiFrame[Slot] > Frame) )
                    continue;
                assert( p->pCtiLem[Slot] );
                if ( p->pCtiFrame[Slot] == -1 )
                    p->pCtiLem[Slot]->iCtiInf = -1;
                else
                    p->pCtiLem[Slot]->iCti = -1;
                Pdr2_CtiSlotFree( p, Slot );
                p->nCtiKilled++;
            }
        }
    }
    // the entries have been applied to every live slot and are not needed again
    Vec_PtrForEachEntry( Pdr2_Cube_t *, p->vLog, pCube, j )
        Pdr2_CubeDeref( pCube );
    Vec_PtrClear( p->vLog );
    Vec_IntClear( p->vLogFrame );
}
void Pdr2_LemCacheCti( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, Gip_Solver_t * pSat, int iFrame )
{
    int * pSlot = iFrame == -1 ? &pLem->iCtiInf : &pLem->iCti;
    int i, Slot, nStride, Value;
    word Bit;
    pSat = Pdr2_SolverActual( pSat );
    Pdr2_CtiApplyLog( p );
    if ( *pSlot < 0 )
    {
        if ( Vec_IntSize(p->vCtiFree) > 0 )
            Slot = Vec_IntPop( p->vCtiFree );
        else
        {
            // memory guard: the pool takes nRegs * nCtiCap / 4 bytes, checked for the grown capacity
            if ( p->nCtiUsed == p->nCtiCap && (ABC_INT64_T)p->nRegs * Pdr2_CtiCapNext(p) / 4 > ((ABC_INT64_T)512 << 20) )
                return;
            if ( p->nCtiUsed == p->nCtiCap )
                Pdr2_CtiPoolGrow( p );
            Slot = p->nCtiUsed++;
        }
        *pSlot = Slot;
    }
    else
        Slot = *pSlot;
    nStride = p->nCtiCap / 64;
    Bit = (word)1 << (Slot & 63);
    for ( i = 0; i < p->nRegs; i++ )
    {
        word * pVal  = p->pCtiVal  + (size_t)i * nStride + (Slot >> 6);
        word * pMask = p->pCtiMask + (size_t)i * nStride + (Slot >> 6);
        Value = pSat->pValue[p->pLoVar[i]];
        if ( Value == GIP_NONE )
        {
            *pMask &= ~Bit;
            *pVal  &= ~Bit;
            continue;
        }
        *pMask |= Bit;
        if ( Value == GIP_TRUE )
            *pVal |= Bit;
        else
            *pVal &= ~Bit;
    }
    p->pCtiLive[Slot >> 6] |= Bit;
    p->pCtiLem[Slot]   = pLem;
    p->pCtiFrame[Slot] = iFrame;
}
// returns 1 if a cached state still shows that the lemma cannot be pushed from iFrame
int Pdr2_LemCtiValid( Pdr2_Man_t * p, Pdr2_Lem_t * pLem, int iFrame )
{
    int Slot;
    Pdr2_CtiApplyLog( p );
    Slot = iFrame == -1 ? pLem->iCtiInf : pLem->iCti;
    if ( Slot < 0 )
        return 0;
    assert( p->pCtiLem[Slot] == pLem );
    if ( iFrame != -1 && p->pCtiFrame[Slot] != iFrame )
        return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Activity of flop variables (rIC3 style, with decay).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManActBump( Pdr2_Man_t * p, Vec_Int_t * vCube )
{
    int i, Lit;
    p->ActInc *= 1.0 / 0.9;
    Vec_IntForEachEntry( vCube, Lit, i )
    {
        p->pAct[Abc_Lit2Var(Lit)] += p->ActInc;
        if ( p->pAct[Abc_Lit2Var(Lit)] > 1e100 )
        {
            int k;
            for ( k = 0; k < p->nRegs; k++ )
                p->pAct[k] *= 1e-100;
            p->ActInc *= 1e-100;
        }
    }
}
typedef struct Pdr2_ActPair_t_ { double Act; int Idx; int Lit; } Pdr2_ActPair_t;
static int Pdr2_ActPairCmpAsc( const void * pa, const void * pb )
{
    const Pdr2_ActPair_t * a = (const Pdr2_ActPair_t *)pa, * b = (const Pdr2_ActPair_t *)pb;
    if ( a->Act < b->Act ) return -1;
    if ( a->Act > b->Act ) return  1;
    return a->Idx - b->Idx;
}
static int Pdr2_ActPairCmpDesc( const void * pa, const void * pb )
{
    const Pdr2_ActPair_t * a = (const Pdr2_ActPair_t *)pa, * b = (const Pdr2_ActPair_t *)pb;
    if ( a->Act > b->Act ) return -1;
    if ( a->Act < b->Act ) return  1;
    return a->Idx - b->Idx;
}
// stable sort of flop literals by the activity of their variables
void Pdr2_ManSortByAct( Pdr2_Man_t * p, Vec_Int_t * vCube, int fAscending )
{
    Pdr2_ActPair_t Pairs[64];
    Pdr2_ActPair_t * pPairs;
    int i, n = Vec_IntSize(vCube);
    if ( n < 2 )
        return;
    pPairs = n <= 64 ? Pairs : ABC_ALLOC( Pdr2_ActPair_t, n );
    for ( i = 0; i < n; i++ )
    {
        pPairs[i].Lit = Vec_IntEntry( vCube, i );
        pPairs[i].Act = p->pAct[Abc_Lit2Var(pPairs[i].Lit)];
        pPairs[i].Idx = i;
    }
    qsort( pPairs, (size_t)n, sizeof(Pdr2_ActPair_t), fAscending ? Pdr2_ActPairCmpAsc : Pdr2_ActPairCmpDesc );
    for ( i = 0; i < n; i++ )
        Vec_IntWriteEntry( vCube, i, pPairs[i].Lit );
    if ( pPairs != Pairs )
        ABC_FREE( pPairs );
}

/**Function*************************************************************

  Synopsis    [Random numbers (xorshift32).]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Pdr2_ManRandom( Pdr2_Man_t * p )
{
    unsigned x = p->RandState;
    if ( x == 0 ) x = 0x9E3779B9u;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    p->RandState = x;
    return x;
}
int Pdr2_ManRandomBool( Pdr2_Man_t * p, double Prob )
{
    return (Pdr2_ManRandom(p) % 1000000u) < (unsigned)(Prob * 1000000.0);
}
void Pdr2_ManShuffle( Pdr2_Man_t * p, Vec_Int_t * vLits )
{
    int i, j, n = Vec_IntSize(vLits);
    for ( i = n - 1; i > 0; i-- )
    {
        j = (int)(Pdr2_ManRandom(p) % (unsigned)(i + 1));
        if ( j != i )
        {
            int t = Vec_IntEntry( vLits, i );
            Vec_IntWriteEntry( vLits, i, Vec_IntEntry(vLits, j) );
            Vec_IntWriteEntry( vLits, j, t );
        }
    }
}
void Pdr2_ManShufflePtr( Pdr2_Man_t * p, Vec_Ptr_t * vPtrs )
{
    int i, j, n = Vec_PtrSize(vPtrs);
    for ( i = n - 1; i > 0; i-- )
    {
        j = (int)(Pdr2_ManRandom(p) % (unsigned)(i + 1));
        if ( j != i )
        {
            void * t = Vec_PtrEntry( vPtrs, i );
            Vec_PtrWriteEntry( vPtrs, i, Vec_PtrEntry(vPtrs, j) );
            Vec_PtrWriteEntry( vPtrs, j, t );
        }
    }
}


/**Function*************************************************************

  Synopsis    [Tests a cube against the relational initial-state predicate.]

  Description []

***********************************************************************/
int Pdr2_ManInitialQuery( Pdr2_Man_t * p, int * pLits, int nLits )
{
    int i, Ret;
    assert(p->pInitSat != NULL);
    Vec_IntClear(p->vInitAssump);
    for ( i = 0; i < nLits; i++ ) Vec_IntPush(p->vInitAssump,Pdr2_LitLo(p,pLits[i]));
    p->pInitSat->TimeLimit = p->timeGlobal;
    Ret = Gip_SolverSolve(p->pInitSat,Vec_IntArray(p->vInitAssump),nLits,NULL,NULL,0,-1);
    p->nInitQueries++;
    if ( Ret == GIP_UNDEF ) p->fInitUnknown = 1;
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Completes a cube intersecting the initial states into one of them.]

  Description [The flops with a defined initial value take it (the literals
  of the cube agree with it); a don't-care flop takes its value in the cube
  if it has one and 0 otherwise. The counterexample and the simulation of
  the abstraction checks use the same initial state.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManInitState( Pdr2_Man_t * p, Pdr2_Cube_t * pCube, char * pState )
{
    int i;
    if ( p->pInitSat )
    {
        if ( Pdr2_ManInitialQuery(p,pCube->Lits,pCube->nLits) != GIP_SAT )
        { memset(pState,0,p->nRegs); return; }
        for ( i = 0; i < p->nRegs; i++ )
            pState[i] = Gip_SolverVarValue(p->pInitSat,p->pLoVar[i]) == GIP_TRUE;
        return;
    }
    for ( i = 0; i < p->nRegs; i++ )
        pState[i] = p->pInit[i] == 1;
    for ( i = 0; i < pCube->nLits; i++ )
    {
        assert( !Pdr2_ManLitIsNonInit(p, pCube->Lits[i]) );
        pState[Abc_Lit2Var(pCube->Lits[i])] = !Abc_LitIsCompl(pCube->Lits[i]);
    }
}

/**Function*************************************************************

  Synopsis    [Derives the counterexample from the obligation chain.]

  Description [The chain starts at the obligation that reached the initial
  states and follows pNext to the bad state. Each obligation carries the
  input values that take its state into the next state (or into the
  property failure for the last one). The register values of the
  counterexample are the initial state (Pdr2_ManInitState).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Pdr2_ManDeriveCex( Pdr2_Man_t * p )
{
    Abc_Cex_t * pCex;
    Pdr2_Obl_t * pObl;
    int i, f, Lit, nFrames = 0;
    if ( p->pReachCex )
    {
        pCex = p->pReachCex;
        p->pReachCex = NULL;
        return pCex;
    }
    for ( pObl = p->pCexObl; pObl; pObl = pObl->pNext )
        nFrames++;
    assert( nFrames == p->pCexObl->nDepth + 1 );
    pCex = Abc_CexAlloc( p->nRegs, p->nPis, nFrames );
    pCex->iPo    = 0;
    pCex->iFrame = nFrames - 1;
    Pdr2_ManInitState( p, p->pCexObl->pState, p->pInitState );
    for ( i = 0; i < p->nRegs; i++ )
        if ( p->pInitState[i] )
            Abc_InfoSetBit( pCex->pData, i );
    for ( pObl = p->pCexObl, f = 0; pObl; pObl = pObl->pNext, f++ )
        Vec_IntForEachEntry( pObl->vInputs, Lit, i )
            if ( !Abc_LitIsCompl(Lit) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + f * pCex->nPis + Abc_Lit2Var(Lit) );
    assert( f == nFrames );
    // Existential witnesses of the initial-state predicate are independent
    // of transition inputs. Preserve the witness used to complete the first
    // state, for the caller's counterexample mapping.
    if ( p->pPars->nInitWitnessNum )
    {
        int First = p->pPars->nInitWitnessPi - 1;
        assert(p->pInitSat && First >= 0 && First+p->pPars->nInitWitnessNum <= p->nPis);
        for ( i = 0; i < p->pPars->nInitWitnessNum; i++ )
        {
            int Bit = pCex->nRegs + First+i;
            int Value = Gip_SolverVarValue(p->pInitSat,p->pPiVar[First+i]);
            if ( Abc_InfoHasBit(pCex->pData,Bit) != Value ) Abc_InfoXorBit(pCex->pData,Bit);
        }
    }
    return pCex;
}

static void Pdr2_ManCollectCube( Pdr2_Man_t * p, Vec_Ptr_t * vInv, Pdr2_Cube_t * pCube )
{
    int i;
    // A guarded proof establishes g => I.  Its excluded cubes are g & cube.
    if ( p->GuardLit >= 0 )
    {
        for ( i = 0; i < pCube->nLits; i++ )
            if ( Abc_Lit2Var(pCube->Lits[i]) == Abc_Lit2Var(p->GuardLit) )
                break;
        if ( i == pCube->nLits )
        {
            Pdr2_CubeToVec( pCube, p->vLits4 );
            Vec_IntPush( p->vLits4, p->GuardLit );
            Vec_PtrPush( vInv, Pdr2_CubeAllocVec(p->vLits4) );
            return;
        }
        if ( pCube->Lits[i] != p->GuardLit )
            return;
    }
    Pdr2_CubeRef( pCube );
    Vec_PtrPush( vInv, pCube );
}

static void Pdr2_ManFreeInvariant( Vec_Ptr_t * vInv )
{
    Pdr2_Cube_t * pCube;
    int i;
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
        Pdr2_CubeDeref( pCube );
    Vec_PtrFree( vInv );
}

/**Function*************************************************************

  Synopsis    [Collects the inductive invariant as a list of cubes.]

  Description [The invariant consists of the lemmas of all frames starting
  from the first empty one, plus the lemmas at frame infinity.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Ptr_t * Pdr2_ManCollectInvariant( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vInv = Vec_PtrAlloc( 1000 );
    Pdr2_Lem_t * pLem;
    int k, i, kStart = -1;
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        if ( Vec_PtrSize(Pdr2_ManFrame(p, k)) == 0 )
        {
            kStart = k;
            break;
        }
    if ( kStart == -1 )
    {
        // no empty frame: this only happens if the property is proved by inf lemmas alone
        kStart = Pdr2_ManFrameNum(p);
    }
    for ( k = kStart; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            Pdr2_ManCollectCube( p, vInv, pLem->pCube );
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        Pdr2_ManCollectCube( p, vInv, pLem->pCube );
    return vInv;
}


/**Function*************************************************************

  Synopsis    [Checks the invariant's consecution and safety in a single combinational miter.]

  Description []

***********************************************************************/
// Check all consecution obligations and property exclusion in one
// combinational miter: Inv(X) & (Bad(X,I) | !Inv(T(X,I))). Initiation is
// still checked clause by clause against the exact initial-state relation.
static int Pdr2_ManVerifyBatch( Pdr2_Man_t * p, Vec_Ptr_t * vInv, int Backend )
{
    Aig_Man_t * pMiter = NULL;
    Aig_Obj_t * pGood, * pFail, * pLoCube, * pLiCube, * pObj;
    Pdr2_Cube_t * pCube;
    int i, j, Lit, Ret = -1;
    abctime Start = Abc_Clock();
    Vec_PtrForEachEntry(Pdr2_Cube_t *,vInv,pCube,i)
        if ( Pdr2_CubeIsInit(p,pCube) ) return p->fInitUnknown ? -1 : 0;
    pMiter = Aig_ManDupSimple(p->pAig);
    pGood = Aig_ManConst1(pMiter);
    pFail = Aig_ObjChild0(Aig_ManCo(pMiter,0));
    Vec_PtrForEachEntry(Pdr2_Cube_t *,vInv,pCube,i)
    {
        pLoCube = pLiCube = Aig_ManConst1(pMiter);
        for ( j = 0; j < pCube->nLits; j++ )
        {
            Lit = pCube->Lits[j];
            pObj = Saig_ManLo(p->pAig,Abc_Lit2Var(Lit));
            pLoCube = Aig_And(pMiter,pLoCube,Aig_NotCond((Aig_Obj_t *)pObj->pData,Abc_LitIsCompl(Lit)));
            pObj = Saig_ManLi(p->pAig,Abc_Lit2Var(Lit));
            pLiCube = Aig_And(pMiter,pLiCube,Aig_NotCond(Aig_ObjChild0Copy(pObj),Abc_LitIsCompl(Lit)));
        }
        pGood = Aig_And(pMiter,pGood,Aig_Not(pLoCube));
        pFail = Aig_Or(pMiter,pFail,pLiCube);
    }
    pFail = Aig_And(pMiter,pGood,pFail);
    Aig_ObjPatchFanin0(pMiter,Aig_ManCo(pMiter,0),pFail);
    Aig_ManCleanup(pMiter);
    if ( Gip_OptionGet("PDR2_VERIFY_DUMP") )
        Ioa_WriteAiger(pMiter,(char *)Gip_OptionGet("PDR2_VERIFY_DUMP"),0,0);
    if ( pFail == Aig_ManConst0(pMiter) ) Ret = 1;
    else if ( pFail == Aig_ManConst1(pMiter) ) Ret = 0;
    else if ( Backend == 3 )
        Ret = Pdr2_ManMappedInvariant(p, pMiter);
    else if ( Backend == 1 )
    {
        Cnf_Man_t * pCnfMan = Cnf_ManStart();
        Gip_Ctx_t * pCtx = Gip_CtxCreatePdr2(pMiter, pCnfMan, 1);
        Gip_Solver_t * pSat = Gip_SolverNew(pCtx);
        pSat->fInputDecisions = pSat->nInputConfLimit = pSat->nInputMillis = 0;
        pSat->RunId = p->pPars->RunId; pSat->pFuncStop = p->pPars->pFuncStop;
        pSat->TimeLimit = p->timeGlobal;
        Lit = Gip_Lit(Gip_CtxObjVar(pCtx,Aig_ManCo(pMiter,0)),0);
        i = Gip_SolverSolve(pSat,&Lit,1,NULL,NULL,0,-1);
        Ret = i == GIP_UNSAT ? 1 : i == GIP_SAT ? 0 : -1;
        Gip_SolverFree(pSat); Gip_CtxFree(pCtx); Cnf_ManStop(pCnfMan);
    }
    else
    {
        Cnf_Dat_t * pCnf = Cnf_DeriveSimple(pMiter,Aig_ManCoNum(pMiter));
        sat_solver * pSat = sat_solver_new();
        sat_solver_setnvars(pSat,pCnf->nVars);
        sat_solver_set_runtime_limit(pSat,p->timeGlobal);
        sat_solver_set_runid(pSat,p->pPars->RunId);
        sat_solver_set_stop_func(pSat,p->pPars->pFuncStop);
        for ( i = 0; i < pCnf->nClauses; i++ )
        {
            if ( !sat_solver_addclause(pSat,pCnf->pClauses[i],pCnf->pClauses[i+1]) ) { Ret = 1; break; }
            if ( (i & 1023) == 0 && p->timeGlobal && Abc_Clock() >= p->timeGlobal ) break;
        }
        if ( i == pCnf->nClauses )
        {
            Lit = Abc_Var2Lit(pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pMiter,0))],0);
            i = sat_solver_solve(pSat,&Lit,&Lit+1,0,0,0,0);
            Ret = i == l_False ? 1 : i == l_True ? 0 : -1;
        }
        sat_solver_delete(pSat); Cnf_DataFree(pCnf);
    }
    Aig_ManStop(pMiter);
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
        Abc_Print(1,"Batch invariant verification: backend %d, %d clauses, result %d. Time = %.3f sec.\n",
            Backend,Vec_PtrSize(vInv),Ret,(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    return Ret;
}

/**Function*************************************************************

  Synopsis    [Verifies the inductive invariant with a fresh solver.]

  Description [Checks that each cube excludes the initial state, that the
  invariant is closed under the transition relation, and that it excludes
  the bad states. Only the overall deadline and cancellation apply (the propagation
  budgets of the search do not). Returns 1 if all checks pass (verified),
  0 if a check fails, -1 if the checks were stopped (incomplete).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManVerifyInvariant( Pdr2_Man_t * p )
{
    Vec_Ptr_t * vInv = Pdr2_ManCollectInvariant( p );
    int BatchMode = Gip_OptionGet("PDR2_VERIFY_BATCH") ? atoi(Gip_OptionGet("PDR2_VERIFY_BATCH")) : 0;
    int BatchResult = -2;
    Gip_Solver_t * pSat;
    if ( BatchMode > 0 )
    {
        BatchResult = Pdr2_ManVerifyBatch(p,vInv,BatchMode);
        if ( !Gip_OptionGet("PDR2_VERIFY_BATCH_CHECK") )
        {
            Pdr2_ManFreeInvariant( vInv );
            return BatchResult;
        }
    }
    pSat = Pdr2_ManNewSolver( p, PDR2_SOLVER_UNRESTRICTED );
    Pdr2_Cube_t * pCube;
    int i, Lit, RetValue, fOk = 1;
    int VerifyPolicy = Gip_OptionGet("PDR2_VERIFY_POLICY") ? atoi(Gip_OptionGet("PDR2_VERIFY_POLICY")) : 0;
    int InputScopeSaved = p->nInputScope;
    abctime clk = Abc_Clock();
    // Verification has a different query distribution from predecessor
    // search. Choose its branching policy independently, preserving every
    // initiation, consecution and property check and the global deadline.
    if ( VerifyPolicy == 1 || VerifyPolicy == 2 )
    {
        p->nInputScope = 0;
        pSat->fInputDecisions = VerifyPolicy == 2;
        pSat->nInputConfLimit = VerifyPolicy == 2 ? 128 : 0;
    }
    // the slice budgets of the search do not apply to the verification
    p->timeLimit = p->timeGlobal;
    p->propLimit = p->propSlice = 0;
    p->timeSlice = p->timeSliceHard = 0;
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
    {
        if ( Pdr2_CubeIsInit(p, pCube) )
        {
            if ( p->fInitUnknown ) { fOk = -1; break; }
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Invariant check failed: cube %d intersects the initial states.\n", i );
            fOk = 0;
        }
        Pdr2_ManSolverAddLemma( p, pSat, pCube, p->IdInf );
    }
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
    {
        Pdr2_CubeToVec( pCube, p->vLits4 );
        RetValue = Pdr2_ManSolveRelative( p, pSat, p->vLits4, 0, NULL );
        if ( RetValue == -1 )
        {
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Invariant verification is incomplete: stopped at clause %d of %d.\n", i, Vec_PtrSize(vInv) );
            if ( fOk == 1 )
                fOk = -1;
            break;
        }
        if ( RetValue != 1 )
        {
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Invariant check failed: cube %d is not inductive.\n", i );
            fOk = 0;
            break;
        }
    }
    if ( fOk == 1 )
    {
        Lit = Abc_Var2Lit( p->VarBad, 0 );
        pSat->nConfLimit = 0;
        pSat->nPropLimit = 0;
        pSat->TimeLimit = p->timeGlobal;
        RetValue = Gip_SolverSolve( pSat, &Lit, 1, NULL, NULL, 0, -1 );
        if ( RetValue == GIP_UNDEF )
        {
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Invariant verification is incomplete: stopped in the property check.\n" );
            fOk = -1;
        }
        else if ( RetValue != GIP_UNSAT )
        {
            if ( !p->pPars->fSilent )
                Abc_Print( 1, "Invariant check failed: the invariant does not exclude the bad states.\n" );
            fOk = 0;
        }
    }
    if ( p->pPars->fVerbose && !p->pPars->fSilent )
    {
        Abc_Print( 1, "Verification of the invariant with %d clauses %s.  ", Vec_PtrSize(vInv), fOk == 1 ? "passed" : fOk == 0 ? "FAILED" : "incomplete" );
        ABC_PRT( "Time", Abc_Clock() - clk );
    }
    Gip_SolverFree( pSat );
    Pdr2_ManFreeInvariant( vInv );
    p->nInputScope = InputScopeSaved;
    if ( BatchResult >= 0 && fOk >= 0 && BatchResult != fOk )
    {
        Abc_Print(1,"Batch invariant verification differential check FAILED: batch %d, individual %d.\n",BatchResult,fOk);
        return 0;
    }
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Writes the AIG of the design into an AIGER file.]

  Description [The initial values of the flops are written in the latch
  lines (AIGER 1.9: "next init", where init is 0, 1, or the latch literal
  itself for a don't-care value; 0 is the default and is omitted). Returns
  1 on success, 0 if the file could not be written.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManWriteDesign( Aig_Man_t * pAig, char * pInit, char * pFileName )
{
    Vec_Str_t * vBuffer = Ioa_WriteAigerIntoMemoryStr( pAig );
    FILE * pFile = fopen( pFileName, "wb" );
    char * pCur = Vec_StrArray( vBuffer ), * pEnd = pCur + Vec_StrSize( vBuffer ), * pLine;
    int i, fOk = pFile != NULL;
    if ( pFile )
    {
        // the header line, then one latch line per flop (the binary format writes them as text)
        pLine = (char *)memchr( pCur, '\n', (size_t)(pEnd - pCur) ) + 1;
        fOk &= fwrite( pCur, 1, (size_t)(pLine - pCur), pFile ) == (size_t)(pLine - pCur);
        for ( i = 0; i < Aig_ManRegNum(pAig); i++ )
        {
            pCur = pLine;
            pLine = (char *)memchr( pCur, '\n', (size_t)(pEnd - pCur) ) + 1;
            fOk &= fwrite( pCur, 1, (size_t)(pLine - 1 - pCur), pFile ) == (size_t)(pLine - 1 - pCur);
            if ( pInit[i] == 1 )
                fprintf( pFile, " 1" );
            else if ( pInit[i] == 2 )
                fprintf( pFile, " %d", 2 * (Saig_ManPiNum(pAig) + 1 + i) );
            fprintf( pFile, "\n" );
        }
        fOk &= fwrite( pLine, 1, (size_t)(pEnd - pLine), pFile ) == (size_t)(pEnd - pLine);
        fOk &= fclose( pFile ) == 0;
    }
    Vec_StrFree( vBuffer );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Dumps the invariant as a PLA file (one cube per blocked cube).]

  Description [The cubes are over the flops of the design the winning run
  worked on, in their original polarities. This is the input design, with
  its initial values, for the plain runs; it differs from it when a
  combinational network gets a flop, the abstraction runs add a reset
  flop, or -q merges and removes flops (fTransformed). The design is
  therefore always written next to the invariant (as <name>_design.aig,
  flops in the same order, with their initial values). Returns 1 if both
  files were written.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManDumpInvariant( Pdr2_Man_t * p, int fTransformed )
{
    Vec_Ptr_t * vInv;
    char * pFileName = p->pPars->pInvFileName ? p->pPars->pInvFileName : (char *)"inv.pla";
    char * pDesign = ABC_ALLOC( char, strlen(pFileName) + 20 ), * pDot, * pBuffer;
    Pdr2_Cube_t * pCube;
    FILE * pFile;
    int i, k, fOk;
    // the name of the design file: the invariant file name without the extension, plus "_design.aig"
    strcpy( pDesign, pFileName );
    if ( (pDot = strrchr(pDesign, '.')) && !strchr(pDot, '/') )
        *pDot = 0;
    strcat( pDesign, "_design.aig" );
    if ( !Pdr2_ManWriteDesign( p->pAig, p->pInit, pDesign ) )
    {
        if ( !p->pPars->fSilent )
            Abc_Print( 1, "Cannot write the design into file \"%s\"; the invariant is not dumped.\n", pDesign );
        ABC_FREE( pDesign );
        return 0;
    }
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        if ( !p->pPars->fSilent )
            Abc_Print( 1, "Cannot open file \"%s\" for writing the invariant.\n", pFileName );
        ABC_FREE( pDesign );
        return 0;
    }
    vInv = Pdr2_ManCollectInvariant( p );
    pBuffer = ABC_ALLOC( char, p->nRegs + 1 );
    fprintf( pFile, "# Inductive invariant computed by pdr2 (each line is a blocked cube over the flops)\n" );
    fprintf( pFile, "# The flops are those of the %s design in \"%s\" (%d flops), in the same order\n",
        fTransformed ? "transformed" : "solved", pDesign, p->nRegs );
    fprintf( pFile, ".i %d\n.o 1\n.p %d\n", p->nRegs, Vec_PtrSize(vInv) );
    Vec_PtrForEachEntry( Pdr2_Cube_t *, vInv, pCube, i )
    {
        for ( k = 0; k < p->nRegs; k++ )
            pBuffer[k] = '-';
        pBuffer[p->nRegs] = 0;
        for ( k = 0; k < pCube->nLits; k++ )
            pBuffer[Abc_Lit2Var(pCube->Lits[k])] = Abc_LitIsCompl(pCube->Lits[k]) ? '0' : '1';
        fprintf( pFile, "%s 1\n", pBuffer );
    }
    fprintf( pFile, ".e\n" );
    fOk = !ferror( pFile );
    fOk &= fclose( pFile ) == 0;
    if ( !fOk && !p->pPars->fSilent )
        Abc_Print( 1, "Writing the invariant into file \"%s\" has failed.\n", pFileName );
    else if ( !p->pPars->fSilent )
        Abc_Print( 1, "Dumped the inductive invariant with %d cubes into file \"%s\" (over the flops of the design in \"%s\").\n", Vec_PtrSize(vInv), pFileName, pDesign );
    ABC_FREE( pBuffer );
    ABC_FREE( pDesign );
    Pdr2_ManFreeInvariant( vInv );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Progress and statistics.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManTimedOut( Pdr2_Man_t * p )
{
    return Pdr2_ManPastDeadline(p) || (p->propLimit && p->nProps >= p->propLimit) ||
           (p->timeSlice && Abc_Clock() >= p->timeSlice);
}
void Pdr2_ManPrintProgress( Pdr2_Man_t * p, int fForce )
{
    int k, nFrames = Pdr2_ManFrameNum(p), kStart;
    if ( p->pPars->fSilent || (!p->pPars->fVerbose && !fForce) )
        return;
    Abc_Print( 1, "%3d :", Pdr2_ManLevel(p) );
    kStart = nFrames > 40 ? nFrames - 40 : 1;
    if ( kStart > 1 )
        Abc_Print( 1, " ..." );
    for ( k = kStart; k < nFrames; k++ )
        Abc_Print( 1, " %d", Vec_PtrSize(Pdr2_ManFrame(p, k)) );
    Abc_Print( 1, " | inf = %d  obl = %d  lvObl = %d  lvLem = %d  sat = %.0fK  ", Vec_PtrSize(p->vInf), Vec_PtrSize(p->vQueue), p->nOblsLevel, (int)(p->nLemmas - p->nLemmasLevel), (double)p->nSolves / 1000.0 );
    if ( p->fAbsActive )
        Abc_Print( 1, "abs = %d  ", p->nAbsFlops );
    Abc_Print( 1, "%6.2f sec\n", (double)(Abc_Clock() - p->timeStart) / CLOCKS_PER_SEC );
    fflush( stdout );
}
void Pdr2_ManPrintStats( Pdr2_Man_t * p )
{
    abctime timeTotal = p->timeRun ? p->timeRun : Abc_Clock() - p->timeStart;
    if ( p->pPars->fSilent ) return;
    Abc_Print( 1, "Frames = %d. Lemmas = %d (inf = %d). Obligations = %d (dropped = %d). SAT calls = %d. MICs = %d.\n",
        Pdr2_ManLevel(p), (int)p->nLemmas, (int)p->nInfLemmas, (int)p->nObls, (int)p->nOblsDropped, (int)p->nSolves, (int)p->nMics );
    if ( p->pPars->fWarmStart || p->pPars->fSparseLift || Gip_OptionGet("PDR2_WARMLIFT") )
        Abc_Print( 1, "Warm-start SAT facts/clauses copied = %d. Sparse lifting scans = %d.\n",
            (int)p->nWarmCopied, (int)p->nSparseScans );
    if ( p->nSolverClones )
        Abc_Print( 1, "Full root solver clones: %.0f, copying %.3f sec.\n",
            (double)p->nSolverClones, (double)p->timeSolverClone / CLOCKS_PER_SEC );
    if ( p->pSimInitBound )
        Abc_Print( 1, "Simulation frame initialization: %d steps, %.0f unit seeds, %.3f sec simulation.\n",
            p->nSimInitSteps, (double)p->nSimInitSeeds, (double)p->timeSimInit / CLOCKS_PER_SEC );
    if ( p->nPhaseSimSeeds )
        Abc_Print( 1, "Simulation phase initialization: %d frames seeded, %.3f sec simulation.\n",
            p->nPhaseSimSeeds, (double)p->timePhaseSim / CLOCKS_PER_SEC );
    if ( p->nLiftMemoMode )
        Abc_Print( 1, "Lifting implications: %.0f checks, %.0f hits (%.0f non-strengthening), %.0f reused, %.0f stored, %.2f MB.\n",
            (double)p->nLiftMemoChecks, (double)p->nLiftMemoHits, (double)p->nLiftMemoWeakHits,
            (double)p->nLiftMemoReuse, (double)p->nLiftMemoStores, (double)p->nLiftMemoBytes / (1 << 20) );
    if ( p->nMicCexMode )
        Abc_Print( 1, "MIC witness cache: %.0f checks, %.0f hits, %.0f stored, %.0f invalidated (mode %d).\n",
            (double)p->nMicCexChecks, (double)p->nMicCexHits, (double)p->nMicCexStores,
            (double)p->nMicCexKilled, p->nMicCexMode );
    if ( p->nPredictMode )
        Abc_Print( 1, "Parent predictions: %.0f candidates, %.0f queries, %.0f proved, %.0f literals saved, %.3f sec (mode %d).\n",
            (double)p->nPredictCalls, (double)p->nPredictQueries, (double)p->nPredictProved,
            (double)p->nPredictSaved, (double)p->timePredict / CLOCKS_PER_SEC, p->nPredictMode );
    if ( p->pPars->nPrefix )
        Abc_Print( 1, "Short-prefix blocking: %d queries, %d proved, %d literals omitted.\n",
            (int)p->nPrefixCalls, (int)p->nPrefixProved, (int)p->nPrefixSaved );
    if ( p->pPars->nMicFailLimit )
        Abc_Print( 1, "MIC stopped after consecutive failures: %d calls (limit %d).\n",
            (int)p->nMicEarlyStop, p->pPars->nMicFailLimit );
    if ( p->nStrengthenOnDemand )
        Abc_Print( 1, "On-demand strengthening: %.0f probes, %.0f temporary clauses avoided.\n",
                   (double)p->nStrengthenTrials, (double)p->nStrengthenAvoided );
    if ( p->nDropHistory )
        Abc_Print( 1, "Literal-drop history skipped %.0f attempts.\n", (double)p->nDropHistorySkipped );
    if ( p->nResolveLimit )
        Abc_Print(1, "Frame resolution: %.0f cubes strengthened, %.0f literals removed.\n", (double)p->nResolveCubes, (double)p->nResolveLits);
    if ( p->nJoinPush )
        Abc_Print( 1, "Predecessor joins: %.0f cubes, %.0f future proofs, %.0f local proofs, %.0f queries.\n",
                   (double)p->nJoinTries, (double)p->nJoinProofs, (double)p->nJoinLocal, (double)p->nJoinQueries );
    if ( p->nMicGroup )
        Abc_Print( 1, "Grouped generalization: %.0f SAT queries, %.0f literals removed, %.0f assumption levels retained.\n",
            (double)p->nGroupQueries, (double)p->nGroupLits, (double)p->nGroupLevels );
    if ( p->nMicGap || p->nGenTimeMode )
        Abc_Print(1, "Generalization placement: %.0f lower-frame MICs skipped, %.0f blocking-core frame jumps, %.0f invariant cores.\n",
            (double)p->nMicGapSkipped, (double)p->nGenTimeJumps, (double)p->nGenTimeInf);
    if ( p->nKindTime )
        Abc_Print(1, "K-induction after PDR base: %d attempts, %s, %.3f sec.\n",
            p->nKindCalls, p->fKindProved ? "proved" : "no proof", (double)p->timeKind/CLOCKS_PER_SEC);
    if ( p->nReachStride )
        Abc_Print( 1, "Reachable-state filter: %d drops rejected of %d checks; %d frames x 64 traces, initialization %.3f sec.\n",
            (int)p->nReachReject, (int)p->nReachChecks, p->nReachFrames, (double)p->timeReach / CLOCKS_PER_SEC );
    if ( p->fReachCex )
        Abc_Print( 1, "Reachable trace splicing: %.0f obligations checked, %.0f matches, %.0f rejected by concrete replay.\n",
            (double)p->nReachCexChecks, (double)p->nReachCexMatches, (double)p->nReachCexRejected );
    Abc_Print( 1, "Down cache: %d drop rejections (mode %d).\n", (int)p->nDownCacheHits, p->pPars->nDownCacheMode );
    if ( p->pPars->nCtgSmall || p->pPars->nCtgMinRate )
        Abc_Print( 1, "Adaptive CTG: %d obligations used plain down (small core %d, minimum drop rate %d percent).\n",
            (int)p->nCtgBypassed, p->pPars->nCtgSmall, p->pPars->nCtgMinRate );
    Abc_Print( 1, "SAT decisions: %.0f; partial-model skips %.0f of %.0f candidates.\n",
        (double)p->nSatDecisions, (double)p->nJustSkipped, (double)p->nJustTested );
    if ( p->nInputScope || p->pPars->nInputPolicy > 0 || (Gip_OptionGet("PDR2_INPUT_DECISIONS") && atoi(Gip_OptionGet("PDR2_INPUT_DECISIONS"))) )
    {
        Vec_Ptr_t * vSeen = Vec_PtrAlloc(100);
        Gip_Solver_t * pSat;
        ABC_INT64_T Fallbacks = 0, Abandons = 0;
        int i;
        Vec_PtrPushUnique(vSeen, p->pLift);
        Vec_PtrPushUnique(vSeen, p->pInf);
        if ( p->pShared ) Vec_PtrPushUnique(vSeen, p->pShared);
        Vec_PtrForEachEntry(Gip_Solver_t *, p->vSolvers, pSat, i)
            Vec_PtrPushUnique(vSeen, Pdr2_SolverActual(pSat));
        Vec_PtrForEachEntry(Gip_Solver_t *, vSeen, pSat, i)
            Fallbacks += pSat->nInputFallbacks, Abandons += pSat->nInputAbandons;
        Abc_Print(1, "Input-first decisions: %.0f internal fallbacks, %.0f queries switched at the branching budget.\n", (double)Fallbacks, (double)Abandons);
        Vec_PtrFree(vSeen);
    }
    if ( p->nWatchLists )
        Abc_Print( 1, "Irrelevant watch-list skips: %.0f of %.0f lists.\n",
            (double)p->nWatchSkipped, (double)p->nWatchLists );
    if ( Gip_OptionGet("PDR2_RECYCLE") )
    {
        Vec_Ptr_t * vSeen = Vec_PtrAlloc( 100 );
        Gip_Solver_t * pSat;
        ABC_INT64_T Tried = 0, Added = 0;
        int i;
        Vec_PtrPushUnique( vSeen, p->pLift );
        Vec_PtrPushUnique( vSeen, p->pInf );
        Vec_PtrForEachEntry( Gip_Solver_t *, p->vSolvers, pSat, i )
            Vec_PtrPushUnique( vSeen, Pdr2_SolverActual(pSat) );
        Vec_PtrForEachEntry( Gip_Solver_t *, vSeen, pSat, i )
            Tried += pSat->Stats.nRecycleTry, Added += pSat->Stats.nRecycled;
        Abc_Print( 1, "Query-clause recycling: %.0f accepted from %.0f candidates.\n", (double)Added, (double)Tried );
        Vec_PtrFree( vSeen );
    }
    if ( p->pPars->fTimeGen )
        Abc_Print( 1, "Time generalization: %d pushes skipped %d frames, %d lemmas placed in frame infinity directly%s.\n",
            (int)p->nTgJumps, (int)p->nTgFrames, (int)p->nTgInf, p->fTimeGenCheck ? " (checked)" : "" );
    if ( p->nTgChecks )
        Abc_Print( 1, "Time generalization checks: %d, failed %d, undecided (deadline) %d.\n", (int)p->nTgChecks, (int)p->nTgFailed, (int)p->nTgUndecided );
    if ( p->nIdChecks )
        Abc_Print( 1, "Lemma id checks: %d, shared ids %d, new ids for lemmas with a live source %d.\n", (int)p->nIdChecks, (int)p->nIdShared, (int)p->nIdFresh );
    Abc_Print( 1, "Solver propagations = %.1f M (%.1f M/sec). Conflicts = %.2f M. Level restarts = %d. Learnt cleanups = %d (%d removed nothing, %.2f sec).\n",
        p->nProps / 1e6, timeTotal > 0 ? p->nProps / 1e6 / ((double)timeTotal / CLOCKS_PER_SEC) : 0.0, p->nConflicts / 1e6, p->nLevelRestarts,
        (int)p->nCleanL, (int)p->nCleanLNone, (double)p->timeCleanL / CLOCKS_PER_SEC );
    Abc_Print( 1, "Propagation queries: %d (skipped %d). Propagation to inf: %d (skipped %d; promoted %d of %d trials, %d by time generalization). CTIs dropped: %d. Semantically contained obligations: %d.\n",
        (int)p->nPropCalls, (int)p->nPropSkipped, (int)p->nPropInfCalls, (int)p->nPropInfSkipped, (int)p->nInfPromoted, (int)p->nInfPromoteCalls, (int)p->nInfPromotedTg, (int)p->nCtiKilled, (int)p->nSemContained );
    if ( p->pPars->nCtpMax )
        Abc_Print( 1, "Counterexamples to propagation: %d considered, %d blocked, %d successful retries.\n",
            (int)p->nCtpCalls, (int)p->nCtpBlocked, (int)p->nCtpPushed );
    if ( p->nLiftPiMode )
        Abc_Print( 1, "Lifting input premises: %.0f model assignments, %.0f retained (mode %d).\n",
            (double)p->nLiftPiBefore, (double)p->nLiftPiAfter, p->nLiftPiMode );
    if ( p->nBadPhaseConfs )
        Abc_Print(1, "Bad-state phase retries: %d after %d conflicts.\n", p->nBadRephases, p->nBadPhaseConfs);
    if ( p->nCnfJustMode )
        Abc_Print(1, "CNF justification: %.0f successful, %.0f fallback, %.0f visited nodes, %.2f sec (mode %d).\n",
            (double)p->nCnfJustHits, (double)p->nCnfJustFails, (double)p->nCnfJustNodes,
            (double)p->timeCnfJust / CLOCKS_PER_SEC, p->nCnfJustMode);
    Abc_Print( 1, "Lifting: %d calls, average size in the cone = %.1f, after flipping = %.1f, after simulation = %.1f (%d not reproduced, %d cut by the deadline), after the SAT core = %.1f.\n",
        (int)p->nLiftCalls, p->nLiftCalls ? 1.0 * p->nLiftCone / p->nLiftCalls : 0.0, p->nLiftCalls ? 1.0 * p->nLiftFlip / p->nLiftCalls : 0.0,
        p->nLiftCalls ? 1.0 * p->nLiftSim / p->nLiftCalls : 0.0, (int)p->nLiftSimFail, (int)p->nLiftSimCut, p->nLiftCalls ? 1.0 * p->nLiftCore / p->nLiftCalls : 0.0 );
    Abc_Print( 1, "Average cube length: obligation = %.1f, MIC input = %.1f, lemma = %.1f. Literal drops: %d ok, %d failed (%.1f%%). Downs = %d. CTGs blocked = %d.\n",
        p->nObls ? 1.0 * p->nOblLits / p->nObls : 0.0, p->nMics ? 1.0 * p->nMicLits / p->nMics : 0.0, p->nLemmas ? 1.0 * p->nLemmaLits / p->nLemmas : 0.0,
        (int)p->nMicDropOk, (int)p->nMicDropFail, (p->nMicDropOk + p->nMicDropFail) ? 100.0 * p->nMicDropOk / (p->nMicDropOk + p->nMicDropFail) : 0.0,
        (int)p->nDowns, (int)p->nCtgsBlocked );
    Abc_Print( 1, "Plain downs: %d queries, %d proved after joins. Queries canceled by the slice overrun limit: %d.\n", (int)p->nDownQueries, (int)p->nDownJoined, p->nQueryCuts );
    if ( p->nDropConfLimit )
        Abc_Print( 1, "Literal-drop conflict allowance %d exhausted on %.0f trials.\n", p->nDropConfLimit, (double)p->nDropConfCuts );
    if ( p->nDownMode )
        Abc_Print(1, "Down joins: %.0f retry queries, %.0f searches stopped after the first counterexample.\n", (double)p->nDownRetries, (double)p->nDownStopped);
    if ( p->pPars->fUseAbs )
        Abc_Print( 1, "Abstraction: %d of %d flops. Spurious counterexamples = %d (by simulation %d). Refined flops = %d (fixups = %d, stale chains = %d). Cleaned flops = %d. Checks cut by the deadline = %d.\n",
            p->nAbsFlops, p->nRegs, p->nAbsCexes, p->nAbsXsimRefs, p->nAbsRefined, p->nAbsFixups, p->nAbsStale, p->nAbsCleaned, p->nAbsCut );
    ABC_PRTP( "Bad states  ", p->timeGetBad,  timeTotal );
    ABC_PRTP( "Abstraction ", p->timeAbs,     timeTotal );
    ABC_PRTP( "Blocking    ", p->timeBlocked, timeTotal );
    ABC_PRTP( "Predecessors", p->timeGetPred, timeTotal );
    ABC_PRTP( "MIC         ", p->timeMic,     timeTotal );
    ABC_PRTP( "Pushing     ", p->timePush,    timeTotal );
    ABC_PRTP( "Propagation ", p->timeProp,    timeTotal );
    ABC_PRTP( "Prop to inf ", p->timePropInf, timeTotal );
    ABC_PRTP( "Lifting, all", p->timeLift,    timeTotal );
    ABC_PRTP( "  simulation", p->timeLiftSim, timeTotal );
    ABC_PRTP( "TOTAL       ", timeTotal,      timeTotal );
    if ( p->fAlternate || p->timeRun < Abc_Clock() - p->timeStart - CLOCKS_PER_SEC / 10 )
        Abc_Print( 1, "(the total is the time inside this run; %.2f sec elapsed in all runs)\n", (double)(Abc_Clock() - p->timeStart) / CLOCKS_PER_SEC );
}


/**Function*************************************************************

  Synopsis    [Advances the private random generator for sampled reachable states.]

  Description []

***********************************************************************/
static word Pdr2_ReachRandom( word * pState )
{
    word x = *pState;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    *pState = x;
    return x * ABC_CONST(2685821657736338717);
}

/**Function*************************************************************

  Synopsis    [Reads a possibly complemented signal value in a word-parallel simulation.]

  Description []

***********************************************************************/
static word Pdr2_ReachValue( word * pValues, Aig_Obj_t * pObj )
{
    word Value = pValues[Aig_ObjId(Aig_Regular(pObj))];
    return Aig_IsComplement(pObj) ? ~Value : Value;
}

/**Function*************************************************************

  Synopsis    [Samples concrete traces and stores their reachable register assignments.]

  Description []

***********************************************************************/
// Generate 64 concrete traces from the specified initial states. Every stored
// bit is an actually reachable state; no abstraction or SAT-model completion
// is involved. The random stream is separate from the proof search's stream.
static void Pdr2_ManReachInit( Pdr2_Man_t * p )
{
    Aig_Obj_t * pObj;
    word * pValues, * pNext;
    word State = ABC_CONST(0x9e3779b97f4a7c15) ^ (unsigned)p->pPars->nRandomSeed;
    abctime clk = Abc_Clock();
    int i, f;
    p->fReachReady = 1;
    if ( !p->nRegs || !p->nReachStride ) return;
    p->pReachStates = ABC_ALLOC( word, (size_t)p->nRegs * p->nReachStride );
    if ( p->fReachCex && p->nPis )
        p->pReachInputs = ABC_ALLOC( word, (size_t)p->nPis * p->nReachStride );
    pValues = ABC_CALLOC( word, Aig_ManObjNumMax(p->pAig) );
    pNext = ABC_ALLOC( word, p->nRegs );
    pValues[Aig_ObjId(Aig_ManConst1(p->pAig))] = ~(word)0;
    Saig_ManForEachLo( p->pAig, pObj, i )
        pValues[Aig_ObjId(pObj)] = p->pInit[i] == 2 ? Pdr2_ReachRandom(&State) : p->pInit[i] ? ~(word)0 : 0;
    for ( f = 0; f < p->nReachStride; f++ )
    {
        if ( Pdr2_ManPastDeadline(p) ) break;
        Saig_ManForEachLo( p->pAig, pObj, i )
            p->pReachStates[(size_t)i * p->nReachStride + f] = pValues[Aig_ObjId(pObj)];
        p->nReachFrames++;
        if ( f + 1 == p->nReachStride ) break;
        Saig_ManForEachPi( p->pAig, pObj, i )
        {
            pValues[Aig_ObjId(pObj)] = Pdr2_ReachRandom( &State );
            if ( p->pReachInputs )
                p->pReachInputs[(size_t)i * p->nReachStride + f] = pValues[Aig_ObjId(pObj)];
        }
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            word a = Pdr2_ReachValue( pValues, Aig_ObjChild0(pObj) );
            word b = Pdr2_ReachValue( pValues, Aig_ObjChild1(pObj) );
            pValues[Aig_ObjId(pObj)] = Aig_ObjIsExor(pObj) ? a ^ b : a & b;
        }
        Saig_ManForEachLi( p->pAig, pObj, i )
            pNext[i] = Pdr2_ReachValue( pValues, Aig_ObjChild0(pObj) );
        Saig_ManForEachLo( p->pAig, pObj, i )
            pValues[Aig_ObjId(pObj)] = pNext[i];
    }
    ABC_FREE( pNext );
    ABC_FREE( pValues );
    p->timeReach += Abc_Clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Tests a candidate cube against states sampled through the given frame.]

  Description []

***********************************************************************/
// A lemma stored in F_Frame must contain every state reachable in <= Frame
// transitions. If its excluded cube contains one sampled state, neither this
// cube nor any larger cube (obtained by dropping more literals) is admissible.
int Pdr2_ManReachContains( Pdr2_Man_t * p, int Frame, Vec_Int_t * vCube )
{
    int f, i, Lit, nFrames;
    if ( !p->fReachReady ) Pdr2_ManReachInit( p );
    p->nReachChecks++;
    nFrames = Abc_MinInt( p->nReachFrames, Frame + 1 );
    for ( f = 0; f < nFrames; f++ )
    {
        word Match = ~(word)0;
        Vec_IntForEachEntry( vCube, Lit, i )
        {
            word Values = p->pReachStates[(size_t)Abc_Lit2Var(Lit) * p->nReachStride + f];
            Match &= Abc_LitIsCompl(Lit) ? ~Values : Values;
            if ( !Match ) break;
        }
        if ( Match ) return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Connects a sampled prefix to a proof obligation and replays the resulting trace.]

  Description []

***********************************************************************/
// Join a sampled concrete prefix to an obligation's counterexample suffix.
// The prefix need not fit the obligation's frame: any validated finite trace
// disproves the unbounded property. No proof lemma is accepted from a match.
int Pdr2_ManReachTryCex( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    int f, i, b, t, Lit, nFrames;
    Pdr2_Obl_t * pWalk;
    Abc_Cex_t * pCex;
    if ( !p->fReachCex || p->fAbsActive ) return 0;
    if ( !p->fReachReady ) Pdr2_ManReachInit( p );
    p->nReachCexChecks++;
    for ( f = 0; f < p->nReachFrames; f++ )
    {
        word Match = ~(word)0;
        if ( Pdr2_ManPastDeadline(p) ) return 0;
        for ( i = 0; i < pObl->pState->nLits; i++ )
        {
            word Values;
            Lit = pObl->pState->Lits[i];
            Values = p->pReachStates[(size_t)Abc_Lit2Var(Lit) * p->nReachStride + f];
            Match &= Abc_LitIsCompl(Lit) ? ~Values : Values;
            if ( !Match ) break;
        }
        if ( !Match ) continue;
        p->nReachCexMatches++;
        for ( b = 0; b < 64 && !(Match & ((word)1 << b)); b++ ) {}
        assert( b < 64 );
        nFrames = f + pObl->nDepth + 1;
        // The concrete replay buffer is bounded independently of the samples.
        if ( (ABC_INT64_T)p->nRegs + (ABC_INT64_T)p->nPis * nFrames > ((ABC_INT64_T)128 << 23) )
            return 0;
        pCex = Abc_CexAlloc( p->nRegs, p->nPis, nFrames );
        pCex->iPo = 0;
        pCex->iFrame = nFrames - 1;
        for ( i = 0; i < p->nRegs; i++ )
            if ( (p->pReachStates[(size_t)i * p->nReachStride] >> b) & 1 )
                Abc_InfoSetBit( pCex->pData, i );
        for ( t = 0; t < f; t++ )
            for ( i = 0; i < p->nPis; i++ )
                if ( (p->pReachInputs[(size_t)i * p->nReachStride + t] >> b) & 1 )
                    Abc_InfoSetBit( pCex->pData, p->nRegs + t * p->nPis + i );
        for ( pWalk = pObl, t = f; pWalk; pWalk = pWalk->pNext, t++ )
            Vec_IntForEachEntry( pWalk->vInputs, Lit, i )
                if ( !Abc_LitIsCompl(Lit) )
                    Abc_InfoSetBit( pCex->pData, p->nRegs + t * p->nPis + Abc_Lit2Var(Lit) );
        assert( t == nFrames );
        if ( Saig_ManVerifyCex(p->pAig, pCex) )
        {
            p->pReachCex = pCex;
            return 1;
        }
        p->nReachCexRejected++;
        Abc_CexFree( pCex );
    }
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
