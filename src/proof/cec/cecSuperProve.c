/**CFile****************************************************************

  FileName    [cecSuperProve.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Sequential verification orchestration.]

  Synopsis    [A pthread portfolio inspired by Berkeley super_prove.]

  Author      [OpenAI Codex, with Alan Mishchenko]

  Affiliation [ABC project]

  Date        [Ver. 1.0. Started - November 9, 2026.]

  Revision    [$Id: cecSuperProve.c,v 1.00 2026/11/09 00:00:00 Exp $]

  Description [The strategy follows the simplify/prove/abstract races in
  Berkeley's super_prove/par.py. This is a native orchestration of ABC APIs,
  not a Python runtime or a translation of its process management. Only
  proved equivalences become shared models; abstract counterexamples are
  refined by the abstraction engines. All reported concrete traces are
  checked on the input.]

***********************************************************************/

#include "cecSuper.h"
#include "cec.h"
#include "aig/gia/giaAig.h"
#include "base/main/main.h"
#include "opt/drw/drw.h"
#include "opt/abs2/abs2.h"
#include "proof/pdr/pdr.h"
#include "proof/pdr2/pdr2.h"
#include "proof/imc/imc.h"
#include "proof/ssw/ssw.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satSolver.h"
#include <limits.h>

#if defined(ABC_USE_PTHREADS) && ABC_HAS_THREAD_LOCAL
#define SUPER_USE_PTHREADS
#if defined(_WIN32) && !defined(__MINGW32__)
#include "../lib/pthread.h"
#else
#include <pthread.h>
#endif
#if defined(_MSC_VER)
#include <intrin.h>
#endif
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// Keep engine IDs in the same order as Names[] in Cec_ManSuperEngineName.
enum { SUPER_AUTO, SUPER_PDR2, SUPER_FLA, SUPER_INT, SUPER_PDR,
       SUPER_BMC, SUPER_BMC_G, SUPER_RAR, SUPER_KIND, SUPER_SCORR3,
       SUPER_SCORR4, SUPER_SCORR, SUPER_GLA, SUPER_ABS, SUPER_DRWSAT,
       SUPER_PDR_T, SUPER_PDR_T_OR, SUPER_GLA_PDR, SUPER_GLA_PDR_ORIGINAL,
       SUPER_ENGINES, SUPER_COMB = SUPER_ENGINES, SUPER_QUEUE = 128 };

typedef struct Cec_SuperMan_t_ Cec_SuperMan_t;
typedef struct Cec_SuperWorker_t_ Cec_SuperWorker_t;
struct Cec_SuperMan_t_
{
    Gia_Man_t * pOriginal;
    Gia_Man_t * pInitial;
    Gia_Man_t * pBest;
    Cec_ParSuper_t * pPars;
    Abc_Cex_t * pCex;
    abctime Start, Deadline;
    int Result, Generation, Round, Active, ActivePersistent, Head, Tail, Done;
    int Queue[SUPER_QUEUE];
    int fComb, fPersistentBmc;
    long fStop;                 // accessed only through the stop helpers once workers start
    const char * pSource;
#ifdef SUPER_USE_PTHREADS
    pthread_mutex_t Mutex;
    pthread_cond_t Cond;
#endif
};
struct Cec_SuperWorker_t_
{
    Cec_SuperMan_t * pMan;
    Gia_Man_t * pGia;
    abctime Deadline;
    int Id, Engine, Generation, Seconds, fInterrupted, fMerged, fPersistent;
    const char * pSolvedBy;
};
static ABC_THREAD_LOCAL Cec_SuperWorker_t * s_pSuperWorker = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets the initial portfolio defaults.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSuperSetDefaultParams( Cec_ParSuper_t * pPars )
{
    memset( pPars, 0, sizeof(*pPars) );
    pPars->nProcs = 6;
    pPars->nTimeOut = 110;
    pPars->fRewrite = 1;
}

/**Function*************************************************************

  Synopsis    [Names the reproducible engine experiments.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
const char * Cec_ManSuperEngineName( int iEngine )
{
    static const char * Names[SUPER_ENGINES] = {
        "auto", "pdr2", "fla", "int", "pdr", "bmc", "bmc-g", "rar",
        "kind", "scorr3", "scorr4", "scorr", "gla", "abs", "drwsat",
        "pdr-t", "pdr-t-or", "gla-pdr", "gla-pdr-original" };
    if ( iEngine == SUPER_COMB ) return "comb-sat";
    return iEngine >= 0 && iEngine < SUPER_ENGINES ? Names[iEngine] : NULL;
}

/**Function*************************************************************

  Synopsis    [Looks up a named engine without modifying its argument.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSuperEngineId( const char * pName )
{
    int i;
    for ( i = 0; i < SUPER_ENGINES; i++ )
        if ( !strcmp(pName, Cec_ManSuperEngineName(i)) ) return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Locks all shared scheduling and result state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperLock( Cec_SuperMan_t * p )
{
#ifdef SUPER_USE_PTHREADS
    int Status = pthread_mutex_lock( &p->Mutex );
    assert( Status == 0 );
    (void)Status;
#endif
}

/**Function*************************************************************

  Synopsis    [Unlocks shared state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperUnlock( Cec_SuperMan_t * p )
{
#ifdef SUPER_USE_PTHREADS
    int Status = pthread_mutex_unlock( &p->Mutex );
    assert( Status == 0 );
    (void)Status;
#endif
}

/**Function*************************************************************

  Synopsis    [Wakes idle workers after a queue or result change.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperWake( Cec_SuperMan_t * p )
{
#ifdef SUPER_USE_PTHREADS
    int Status = pthread_cond_broadcast( &p->Cond );
    assert( Status == 0 );
    (void)Status;
#endif
}

/**Function*************************************************************

  Synopsis    [Reads the cooperative stop flag without locking when supported.]

  Description [Relaxed atomics suffice: all result data remains protected
  by the scheduler mutex. Other threaded toolchains use that mutex here.]

  SideEffects []

  SeeAlso     [Cec_SuperRequestStop]

***********************************************************************/
static int Cec_SuperReadStop( Cec_SuperMan_t * p )
{
#if !defined(SUPER_USE_PTHREADS)
    return p->fStop != 0;
#elif defined(_MSC_VER)
    return _InterlockedCompareExchange( &p->fStop, 0, 0 ) != 0;
#elif defined(__GNUC__) || defined(__clang__)
    return __atomic_load_n( &p->fStop, __ATOMIC_RELAXED ) != 0;
#else
    int Stop;
    Cec_SuperLock( p );
    Stop = p->fStop != 0;
    Cec_SuperUnlock( p );
    return Stop;
#endif
}

/**Function*************************************************************

  Synopsis    [Signals cancellation while holding the scheduler mutex.]

  Description []

  SideEffects [Stops all remaining solver work.]

  SeeAlso     [Cec_SuperReadStop]

***********************************************************************/
static void Cec_SuperRequestStop( Cec_SuperMan_t * p )
{
#if !defined(SUPER_USE_PTHREADS)
    p->fStop = 1;
#elif defined(_MSC_VER)
    _InterlockedExchange( &p->fStop, 1 );
#elif defined(__GNUC__) || defined(__clang__)
    __atomic_store_n( &p->fStop, 1, __ATOMIC_RELAXED );
#else
    p->fStop = 1;
#endif
    Cec_SuperWake( p );
}

/**Function*************************************************************

  Synopsis    [Cooperatively stops a solver after a result or deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperStop( void * pData )
{
    Cec_SuperWorker_t * pWorker = (Cec_SuperWorker_t *)pData;
    int Stop = Abc_Clock() >= pWorker->Deadline || Cec_SuperReadStop(pWorker->pMan);
    if ( Stop ) pWorker->fInterrupted = 1;
    return Stop;
}

/**Function*************************************************************

  Synopsis    [Adapts integer-only solver callbacks using thread-local data.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperStopId( int RunId )
{
    (void)RunId;
    return s_pSuperWorker && Cec_SuperStop( s_pSuperWorker );
}

/**Function*************************************************************

  Synopsis    [Defers publication until the solver's trace has been checked.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperProgress( void * pData, int fSolved, unsigned Result )
{
    (void)Result;
    return fSolved ? 0 : Cec_SuperStop( pData );
}

/**Function*************************************************************

  Synopsis    [Handles constants and direct primary-input properties.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperConstant( Gia_Man_t * pGia )
{
    Gia_Obj_t * pObj;
    int i, Nonconstant = 0;
    Gia_ManForEachPo( pGia, pObj, i )
    {
        int Lit = Gia_ObjFaninLit0p( pGia, pObj );
        Gia_Obj_t * pDriver = Gia_ManObj( pGia, Abc_Lit2Var(Lit) );
        if ( Lit == 1 || Gia_ObjIsPi(pGia, pDriver) )
        {
            Abc_CexFreeP( &pGia->pCexSeq );
            pGia->pCexSeq = Abc_CexAlloc( Gia_ManRegNum(pGia), Gia_ManPiNum(pGia), 1 );
            pGia->pCexSeq->iPo = i;
            if ( Lit != 1 && !Abc_LitIsCompl(Lit) )
                Abc_InfoSetBit( pGia->pCexSeq->pData, pGia->pCexSeq->nRegs + Gia_ObjCioId(pDriver) );
            return 0;
        }
        Nonconstant |= Lit != 0;
    }
    return Nonconstant ? -1 : 1;
}

/**Function*************************************************************

  Synopsis    [Combines safety outputs for engines requiring one property.]

  Description [Preserves all primary inputs and register transitions.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Cec_SuperMergeOutputs( Gia_Man_t * pGia )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(pGia) ), * pTemp;
    Gia_Obj_t * pObj;
    int i, Bad = 0;
    pNew->pName = Abc_UtilStrsav( pGia->pName );
    pNew->pSpec = Abc_UtilStrsav( pGia->pSpec );
    Gia_ManHashStart( pNew );
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachCi( pGia, pObj, i ) pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pGia, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachPo( pGia, pObj, i ) Bad = Gia_ManHashOr( pNew, Bad, Gia_ObjFanin0Copy(pObj) );
    Gia_ManAppendCo( pNew, Bad );
    Gia_ManForEachRi( pGia, pObj, i ) Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Checks a combinational miter with an interruptible SAT call.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperComb( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pGia = pWorker->pGia;
    Gia_Obj_t * pObj;
    sat_solver * pSat = sat_solver_new();
    int i, k, Lit, Status, Result = 1;
    sat_solver_setnvars( pSat, Gia_ManObjNum(pGia) );
    sat_solver_set_stop_func( pSat, Cec_SuperStopId );
    sat_solver_set_runtime_limit( pSat, pWorker->Deadline );
    sat_solver_add_const( pSat, 0, 1 );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( !(i & 1023) && Cec_SuperStop(pWorker) ) { Result = -1; goto finish; }
        sat_solver_add_and( pSat, i, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninId1(pObj, i),
            Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
    }
    Gia_ManForEachPo( pGia, pObj, i )
    {
        if ( Cec_SuperStop(pWorker) ) { Result = -1; break; }
        Lit = Gia_ObjFaninLit0p( pGia, pObj );
        Status = sat_solver_solve( pSat, &Lit, &Lit + 1, 0, 0, 0, 0 );
        if ( Status == l_False ) continue;
        Result = Status == l_True ? 0 : -1;
        if ( Result == 0 )
        {
            Abc_CexFreeP( &pGia->pCexSeq );
            pGia->pCexSeq = Abc_CexAlloc( 0, Gia_ManPiNum(pGia), 1 );
            pGia->pCexSeq->iPo = i;
            Gia_ManForEachPi( pGia, pObj, k )
                if ( sat_solver_var_value(pSat, Gia_ObjId(pGia, pObj)) )
                    Abc_InfoSetBit( pGia->pCexSeq->pData, k );
        }
        break;
    }
finish:
    sat_solver_delete( pSat );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Publishes a checked result, translating only primary inputs.]

  Description [All transformations keep PI order and zero initialization.
  Reconstructing the original register trajectory by simulation avoids using
  a reduced or abstract state as an original counterexample.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperPublish( Cec_SuperWorker_t * pWorker, int Result )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    Gia_Man_t * pCheck;
    Abc_Cex_t * pCex = NULL, * pSource = pWorker->pGia->pCexSeq;
    ABC_INT64_T nBits;
    int i, Accepted = 0;
    if ( Result != 0 && Result != 1 ) return 0;
    if ( Result == 0 )
    {
        if ( !pSource || pSource->iFrame < 0 || pSource->iFrame == INT_MAX ||
             pSource->nRegs < 0 ||
             pSource->nPis != Gia_ManPiNum(p->pOriginal) ||
             pSource->iPo < 0 || pSource->iPo >= Gia_ManPoNum(p->pOriginal) ) goto rejected;
        nBits = (ABC_INT64_T)pSource->nPis * (pSource->iFrame + 1);
        if ( nBits + Gia_ManRegNum(p->pOriginal) > INT_MAX - 32 ||
             nBits + pSource->nRegs > pSource->nBits ) goto rejected;
        pCex = Abc_CexAlloc( Gia_ManRegNum(p->pOriginal), pSource->nPis, pSource->iFrame + 1 );
        pCex->iFrame = pSource->iFrame;
        pCex->iPo = pSource->iPo;
        for ( i = 0; i < (int)nBits; i++ )
            if ( Abc_InfoHasBit(pSource->pData, pSource->nRegs + i) )
                Abc_InfoSetBit( pCex->pData, pCex->nRegs + i );
        // Duplication writes Value in its source. Simulation then uses only
        // the private copy, so long witnesses do not block scheduling or stops.
        Cec_SuperLock( p );
        pCheck = Gia_ManDup( p->pOriginal );
        Cec_SuperUnlock( p );
        if ( pWorker->fMerged )
            pCex->iPo = Gia_ManFindFailedPoCex( pCheck, pCex, 0 );
        i = pCex->iPo >= 0 && Gia_ManVerifyCex( pCheck, pCex, 0 );
        Gia_ManStop( pCheck );
        if ( !i ) goto rejected;
    }
    Cec_SuperLock( p );
    if ( p->Result == -1 )
    {
        p->Result = Result;
        p->pCex = pCex;
        pCex = NULL;
        p->pPars->pWinner = pWorker->pSolvedBy;
        Accepted = 1;
        Cec_SuperRequestStop( p );
    }
    Cec_SuperUnlock( p );
    Abc_CexFreeP( &pCex );
    return Accepted;
rejected:
    Abc_Print( 1, "Warning: super_prove rejected a counterexample from %s on the original graph.\n",
        pWorker->pSolvedBy );
    Abc_CexFreeP( &pCex );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Moves reduction follow-ups to the front without duplicates.]

  Description [Pending tasks use the latest model when dequeued. Active
  tasks keep their private model and are not removed. Caller holds Mutex.]

  SideEffects [Compacts the pending queue.]

  SeeAlso     [Cec_SuperReduce]

***********************************************************************/
static void Cec_SuperPrioritize( Cec_SuperMan_t * p )
{
    int Queue[SUPER_QUEUE] = { SUPER_KIND, SUPER_PDR2, SUPER_PDR_T_OR };
    int i, nTasks = 3;
    for ( i = p->Head; i < p->Tail; i++ )
        if ( p->Queue[i] != SUPER_KIND && p->Queue[i] != SUPER_PDR2 && p->Queue[i] != SUPER_PDR_T_OR )
        {
            assert( nTasks < SUPER_QUEUE );
            Queue[nTasks++] = p->Queue[i];
        }
    memcpy( p->Queue, Queue, sizeof(int) * nTasks );
    p->Head = 0;
    p->Tail = nTasks;
    Cec_SuperWake( p );
}

/**Function*************************************************************

  Synopsis    [Queues immediate solver attempts on a proved smaller model.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperReduce( Cec_SuperWorker_t * pWorker, Gia_Man_t * pNew )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    if ( !pNew ) return;
    if ( Gia_ManPiNum(pNew) != Gia_ManPiNum(p->pOriginal) ||
         Gia_ManPoNum(pNew) != Gia_ManPoNum(p->pOriginal) )
    {
        Gia_ManStop( pNew );
        return;
    }
    Cec_SuperLock( p );
    if ( p->Result == -1 && (ABC_INT64_T)Gia_ManAndNum(pNew) + 16 * (ABC_INT64_T)Gia_ManRegNum(pNew) <
         (ABC_INT64_T)Gia_ManAndNum(p->pBest) + 16 * (ABC_INT64_T)Gia_ManRegNum(p->pBest) )
    {
        if ( p->pPars->fVerbose )
            Abc_Print( 1, "super_prove: %s reduced ANDs %d -> %d, registers %d -> %d.\n",
                Cec_ManSuperEngineName(pWorker->Engine), Gia_ManAndNum(p->pBest), Gia_ManAndNum(pNew),
                Gia_ManRegNum(p->pBest), Gia_ManRegNum(pNew) );
        Gia_ManStop( p->pBest );
        p->pBest = pNew;
        pNew = NULL;
        p->pSource = Cec_ManSuperEngineName(pWorker->Engine);
        p->Generation++;
        p->pPars->nReduced++;
        if ( !p->pPars->iEngine )
            Cec_SuperPrioritize( p );
    }
    Cec_SuperUnlock( p );
    Gia_ManStopP( &pNew );
}

/**Function*************************************************************

  Synopsis    [Tries a bounded proof of a gate abstraction on this worker.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperGlaProve( Gia_Man_t * pGia, void * pData )
{
    Cec_SuperWorker_t * pWorker = (Cec_SuperWorker_t *)pData;
    Gia_Man_t * pAbs, * pTemp;
    Aig_Man_t * pAig;
    Vec_Int_t * vClasses;
    Pdr_Par_t Pars;
    abctime Deadline = pWorker->Deadline, Now = Abc_Clock();
    int Result, fInterrupted = pWorker->fInterrupted;
    if ( Cec_SuperStop(pWorker) || !pGia->vGateClasses ) return -1;
    vClasses = Vec_IntDup( pGia->vGateClasses );
    pAbs = Gia_ManDupAbsGates( pGia, vClasses );
    Vec_IntFree( vClasses );
    Gia_ManCleanValue( pGia );
    pAbs = Gia_ManDupNormalize( pTemp = pAbs, 1 );
    Gia_ManStop( pTemp );
    pAig = Gia_ManToAigSimple( pAbs );
    Gia_ManStop( pAbs );
    // Keep unrolling responsive if an abstraction needs a long proof.
    if ( Deadline - Now > 2 * (abctime)CLOCKS_PER_SEC )
        pWorker->Deadline = Now + 2 * (abctime)CLOCKS_PER_SEC;
    Pdr_ManSetDefaultParams( &Pars );
    Pars.nTimeOut = 2;
    Pars.fSilent = 1;
    Pars.pFuncStop = Cec_SuperStopId;
    Result = Pdr_ManSolve( pAig, &Pars );
    Aig_ManStop( pAig );
    pWorker->Deadline = Deadline;
    pWorker->fInterrupted = fInterrupted;
    return Result == 1 ? 1 : -1;
}

/**Function*************************************************************

  Synopsis    [Runs one native solver on privately owned data.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperSolve( Cec_SuperWorker_t * pWorker )
{
    Gia_Man_t * pGia = pWorker->pGia, * pNew = NULL, * pNorm;
    Aig_Man_t * pAig, * pTemp;
    int Result = Cec_SuperConstant(pGia), Engine = pWorker->Engine;
    pWorker->pSolvedBy = Result != -1 ? "trivial" : Cec_ManSuperEngineName( Engine );
    if ( Result != -1 || Cec_SuperStop(pWorker) ) return Result;
    if ( !Gia_ManRegNum(pGia) )
    {
        pWorker->pSolvedBy = "comb-sat";
        return Cec_SuperComb(pWorker);
    }
    if ( Gia_ManPoNum(pGia) > 1 && (Engine == SUPER_FLA || Engine == SUPER_INT ||
         Engine == SUPER_GLA || Engine == SUPER_GLA_PDR ||
         Engine == SUPER_GLA_PDR_ORIGINAL || Engine == SUPER_PDR_T_OR) )
    {
        pNew = Cec_SuperMergeOutputs( pGia );
        Gia_ManStop( pGia );
        pWorker->pGia = pGia = pNew;
        pWorker->fMerged = 1;
        pNew = NULL;
        Result = Cec_SuperConstant( pGia );
        if ( Result != -1 ) { pWorker->pSolvedBy = "trivial"; return Result; }
    }
    if ( Engine == SUPER_PDR2 )
    {
        Pdr2_Par_t Pars;
        Pdr2_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.fSilent = 1;
        Pars.pFuncStop = Cec_SuperStopId;
        Pars.fVerifyComplete = 1;
        pAig = Gia_ManToAigSimple( pGia );
        Result = Pdr2_ManSolve( pAig, &Pars );
        pGia->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );
    }
    else if ( Engine == SUPER_PDR || Engine == SUPER_PDR_T || Engine == SUPER_PDR_T_OR )
    {
        Pdr_Par_t Pars;
        Pdr_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.fSilent = 1;
        Pars.fUseAbs = Engine != SUPER_PDR;
        Pars.pFuncStop = Cec_SuperStopId;
        pAig = Gia_ManToAigSimple( pGia );
        Result = Pdr_ManSolve( pAig, &Pars );
        pGia->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );
    }
    else if ( Engine == SUPER_BMC || Engine == SUPER_BMC_G )
    {
        Saig_ParBmc_t Pars;
        Saig_ParBmcSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.fSilent = 1;
        Pars.fUseGlucose = Engine == SUPER_BMC_G;
        Pars.pFuncStop = Cec_SuperStopId;
        pAig = Gia_ManToAigSimple( pGia );
        Result = Saig_ManBmcScalable( pAig, &Pars );
        pGia->pCexSeq = pAig->pSeqModel; pAig->pSeqModel = NULL;
        Aig_ManStop( pAig );
    }
    else if ( Engine == SUPER_RAR )
    {
        Ssw_RarPars_t Pars;
        Ssw_RarSetDefaultParams( &Pars );
        Pars.TimeOut = pWorker->Seconds;
        Pars.fSilent = 1;
        Pars.pFuncProgress = Cec_SuperProgress;
        Pars.pProgress = pWorker;
        Result = Ssw_RarSimulateGia( pGia, &Pars );
    }
    else if ( Engine == SUPER_KIND )
    {
        Cec_ParKind_t Pars;
        Cec_ManKindSetDefaultParams( &Pars );
        Pars.nTimeOutMs = 1000 * pWorker->Seconds;
        Pars.TimeToStop = pWorker->Deadline;
        Pars.nAndMax = 0;
        Pars.nFramesMax = 4;
        Pars.pFuncStop = Cec_SuperStopId;
        Result = Cec_GiaKind( pGia, &Pars );
    }
    else if ( Engine == SUPER_FLA )
    {
        Fla_Par_t Pars;
        if ( Gia_ManPoNum(pGia) != 1 ) return -1;
        Fla_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.fUseThread = 0;
        Pars.fSilent = 1;
        Pars.fRewrite = 0;
        Pars.pFuncStop = Cec_SuperStop;
        Pars.pStopData = pWorker;
        Result = Gia_ManPerformFla( pGia, &Pars );
    }
    else if ( Engine == SUPER_ABS )
    {
        Abs2_Par_t Pars;
        Abs2_SetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Pars.pFuncStop = Cec_SuperStop;
        Pars.pStopData = pWorker;
        Result = Abs2_ManPerform( pGia, &Pars );
        // This is a bounded abstraction experiment, never a safety proof.
        if ( Result != 0 ) Result = -1;
    }
    else if ( Engine == SUPER_INT )
    {
        Imc_Par_t Pars;
        Imc_ManSetDefaultParams( &Pars );
        Pars.nTimeOut = pWorker->Seconds;
        Result = Imc_ManPerform( pGia, &Pars );
    }
    else if ( Engine == SUPER_GLA || Engine == SUPER_GLA_PDR || Engine == SUPER_GLA_PDR_ORIGINAL )
    {
        Abs_Par_t Pars;
        if ( Gia_ManPoNum(pGia) != 1 || !Gia_ManPiNum(pGia) ) return -1;
        Abs_ParSetDefaults( &Pars );
        Pars.fSilent = !pWorker->pMan->pPars->fVerbose;
        Pars.nTimeOut = pWorker->Seconds;
        // Bounded unrolling leaves deeper searches to the BMC lanes.
        Pars.nFramesMax = 1000;
        // The callback runs on this worker and creates no helper threads.
        Pars.fCallProver = 0;
        Pars.pFuncStop = Cec_SuperStopId;
        Pars.pFuncProve = Engine != SUPER_GLA ? Cec_SuperGlaProve : NULL;
        Pars.pProveData = pWorker;
        Result = Gia_ManPerformGla( pGia, &Pars );
    }
    else if ( Engine == SUPER_SCORR )
    {
        Ssw_Pars_t Pars;
        // The old simulator requires at least one real primary input.
        if ( !Gia_ManPiNum(pGia) ) return -1;
        Ssw_ManSetDefaultParams( &Pars );
        Pars.pFunc = (void *)Cec_SuperStop;
        Pars.pData = pWorker;
        pAig = Gia_ManToAigSimple( pGia );
        pTemp = Ssw_SignalCorrespondence( pAig, &Pars );
        // The engine returns its input on interruption; keep this guard too.
        // Never promote an interrupted sweep as a verified simplification.
        if ( pTemp )
        {
            if ( !pWorker->fInterrupted ) pNew = Gia_ManFromAigSimple( pTemp );
            Aig_ManStop( pTemp );
        }
        Aig_ManStop( pAig );
    }
    else if ( Engine == SUPER_SCORR3 || Engine == SUPER_SCORR4 )
    {
        Cec_ParCor_t Pars;
        Cec_ManCorSetDefaultParams( &Pars );
        Pars.nProcs = 1;
        Pars.nBTLimit = 1000;
        Pars.pFunc = (void *)Cec_SuperStop;
        Pars.pData = pWorker;
        pNew = Engine == SUPER_SCORR3 ? Cec_ManLSCorrespondence3(pGia, &Pars)
                                    : Cec_ManLSCorrespondence4(pGia, &Pars, 4, 0);
    }
    else if ( Engine == SUPER_DRWSAT )
        pNew = Drw_ManRwsat( pGia, 0, 0 );
    if ( pNew )
    {
        // Correspondence can export duplicate ANDs. DRWSAT already hashes
        // its result, so it needs no second normalization here.
        if ( Engine != SUPER_DRWSAT )
        {
            pNorm = Gia_ManDupNormalize( pNew, 1 );
            Gia_ManStop( pNew );
            pNew = pNorm;
        }
        Gia_ManStop( pGia );
        pWorker->pGia = pGia = pNew;
        Result = Cec_SuperConstant( pGia );
        if ( Result != -1 ) return Result;
        if ( Engine != SUPER_DRWSAT && pWorker->pMan->pPars->fRewrite && !Cec_SuperStop(pWorker) )
        {
            pNew = Drw_ManRwsat( pGia, 0, 0 );
            if ( pNew ) { Gia_ManStop(pGia); pWorker->pGia = pGia = pNew; }
            Result = Cec_SuperConstant( pGia );
            if ( Result != -1 ) return Result;
        }
        Cec_SuperReduce( pWorker, Gia_ManDup(pGia) );
        if ( pWorker->pMan->pPars->iEngine && !Cec_SuperStop(pWorker) )
        {
            pWorker->Engine = SUPER_PDR2;
            Result = Cec_SuperSolve( pWorker );
            pWorker->Engine = Engine;
        }
    }
    return Result == 0 || Result == 1 ? Result : -1;
}

/**Function*************************************************************

  Synopsis    [Fills progressively longer races, without nested workers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperSchedule( Cec_SuperMan_t * p )
{
    static const int Engines[] = { SUPER_SCORR4, SUPER_GLA_PDR, SUPER_PDR2,
        SUPER_PDR_T_OR, SUPER_RAR, SUPER_BMC_G, SUPER_GLA_PDR_ORIGINAL,
        SUPER_FLA, SUPER_SCORR, SUPER_PDR_T, SUPER_SCORR3, SUPER_PDR, SUPER_BMC };
    int i;
    p->Head = p->Tail = 0;
    if ( p->fComb )
        p->Queue[p->Tail++] = SUPER_COMB;
    else if ( p->pPars->iEngine )
        p->Queue[p->Tail++] = p->pPars->iEngine;
    else
        for ( i = 0; i < (int)(sizeof(Engines) / sizeof(int)); i++ )
            // Rewriting runs initially and after correspondence, not again here.
            // With four or more workers, the first BMC search spans rounds.
            if ( !p->fPersistentBmc || !p->Round || Engines[i] != SUPER_BMC_G )
                p->Queue[p->Tail++] = Engines[i];
}

/**Function*************************************************************

  Synopsis    [Takes a task and an exclusive graph copy, or waits for work.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_SuperNext( Cec_SuperWorker_t * pWorker )
{
    Cec_SuperMan_t * p = pWorker->pMan;
    int HaveTask = 0;
    Cec_SuperLock( p );
    while ( p->Result == -1 && !p->Done && Abc_Clock() < p->Deadline )
    {
        if ( p->Head < p->Tail )
        {
            abctime Now = Abc_Clock(), Budget;
            int fOriginal;
            pWorker->Engine = p->Queue[p->Head++];
            fOriginal = pWorker->Engine == SUPER_GLA_PDR_ORIGINAL || pWorker->Engine == SUPER_BMC_G;
            pWorker->Generation = fOriginal ? 0 : p->Generation;
            pWorker->fInterrupted = 0;
            pWorker->fMerged = 0;
            pWorker->fPersistent = p->fPersistentBmc && !p->pPars->iEngine &&
                !p->Round && pWorker->Engine == SUPER_BMC_G;
            Budget = pWorker->fPersistent || p->fComb || p->pPars->iEngine || p->Round == 2 ? p->Deadline - Now :
                (abctime)(p->Round ? 40 : 20) * CLOCKS_PER_SEC;
            // Give simulation an early chance, then make room for original GLA.
            if ( !p->pPars->iEngine && !p->Round && pWorker->Engine == SUPER_RAR )
                Budget = (abctime)6 * CLOCKS_PER_SEC;
            pWorker->Deadline = Now + Budget;
            if ( pWorker->Deadline > p->Deadline ) pWorker->Deadline = p->Deadline;
            pWorker->Seconds = (int)((pWorker->Deadline - Now + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC);
            pWorker->Seconds = Abc_MaxInt( 1, pWorker->Seconds );
            // Gia_ManDup writes Value in its source. Keep copies serialized.
            pWorker->pGia = Gia_ManDup( fOriginal ? p->pInitial : p->pBest );
            Abc_CexFreeP( &pWorker->pGia->pCexSeq );
            p->Active++;
            p->ActivePersistent += pWorker->fPersistent;
            p->pPars->nStarted++;
            HaveTask = 1;
            if ( p->pPars->fVerbose )
                Abc_Print( 1, "super_prove: start worker=%d engine=%s model=%d source=%s budget=%.3f sec\n",
                    pWorker->Id, Cec_ManSuperEngineName(pWorker->Engine), pWorker->Generation,
                    fOriginal ? "original" : p->pSource,
                    (double)(pWorker->Deadline - Now) / CLOCKS_PER_SEC );
            break;
        }
        // Other workers can advance their rounds while BMC keeps searching.
        if ( !p->Active || (p->Active == p->ActivePersistent && p->Round < 2) )
        {
            if ( p->fComb || p->pPars->iEngine || ++p->Round == 3 )
            {
                p->Done = 1;
                Cec_SuperRequestStop( p );
                break;
            }
            Cec_SuperSchedule( p );
            continue;
        }
#ifdef SUPER_USE_PTHREADS
        {
            int Status = pthread_cond_wait( &p->Cond, &p->Mutex );
            assert( Status == 0 );
            (void)Status;
        }
#else
        break;
#endif
    }
    Cec_SuperUnlock( p );
    return HaveTask;
}

/**Function*************************************************************

  Synopsis    [Owns its frame and solver data until cooperative completion.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void * Cec_SuperWorker( void * pArg )
{
    Cec_SuperWorker_t * pWorker = (Cec_SuperWorker_t *)pArg;
    Cec_SuperMan_t * p = pWorker->pMan;
    Cec_SuperWorker_t * pPreviousWorker = s_pSuperWorker;
    Abc_Frame_t * pFrame = Abc_FrameCreate(), * pPrevious = Abc_FrameEnter(pFrame);
    s_pSuperWorker = pWorker;
    while ( Cec_SuperNext(pWorker) )
    {
        abctime Start = Abc_Clock();
        int Result = Cec_SuperSolve( pWorker );
        if ( Result >= 0 ) Cec_SuperPublish( pWorker, Result );
        Gia_ManStopP( &pWorker->pGia );
        Cec_SuperLock( p );
        p->Active--;
        p->ActivePersistent -= pWorker->fPersistent;
        assert( p->Active >= p->ActivePersistent && p->ActivePersistent >= 0 && p->ActivePersistent <= 1 );
        Cec_SuperWake( p );
        if ( p->pPars->fVerbose )
            Abc_Print( 1, "super_prove: stop worker=%d engine=%s result=%d elapsed=%.3f sec\n",
                pWorker->Id, Cec_ManSuperEngineName(pWorker->Engine), Result,
                (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
        Cec_SuperUnlock( p );
    }
    s_pSuperWorker = pPreviousWorker;
    Abc_FrameLeave( pPrevious );
    Abc_FrameDestroy( pFrame );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Reports the result in the same form as the baseline prover.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec_SuperReport( Gia_Man_t * pGia, Cec_ParSuper_t * pPars, int Result, abctime Start )
{
    const char * pName = pGia->pSpec ? pGia->pSpec : pGia->pName;
    if ( pPars->fSilent ) return;
    Abc_Print( 1, "Problem \"%s\" is %s", pName ? pName : "(none)",
        Result == 1 ? "UNSATISFIABLE" : Result == 0 ? "SATISFIABLE" : "UNDECIDED" );
    if ( Result != -1 ) Abc_Print( 1, " (solved by %s)", pPars->pWinner );
    Abc_Print( 1, ".   Time = %.6f sec\n", (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
}

/**Function*************************************************************

  Synopsis    [Runs the bounded native portfolio and retains the input miter.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_GiaSuperProve( Gia_Man_t * pGia, Cec_ParSuper_t * pPars )
{
    Cec_SuperMan_t Man, * p = &Man;
    Cec_SuperWorker_t * pWorkers;
    int i, nWorkers, nCreated = 0, Result;
#ifdef SUPER_USE_PTHREADS
    pthread_t * pThreads;
#endif
    if ( !pGia || !pPars || pPars->nProcs < 1 || pPars->nProcs > 256 ||
         pPars->nTimeOut < 1 || pPars->nTimeOut > 86400 ||
         pPars->iEngine < 0 || pPars->iEngine >= SUPER_ENGINES ||
         pGia->nConstrs || !Abs2_ManCheckZeroInit(pGia) ||
         Gia_ManHasChoices(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ||
         Gia_ManBufNum(pGia) || Gia_ManBoxNum(pGia) ) return -2;
    pPars->pWinner = NULL;
    pPars->nStarted = pPars->nReduced = 0;
    Abc_CexFreeP( &pGia->pCexSeq );
    Abc_CexFreeP( &pGia->pCexComb );
    memset( p, 0, sizeof(*p) );
    p->Start = Abc_Clock();
    Result = Cec_SuperConstant( pGia );
    if ( Result != -1 )
    {
        pPars->pWinner = "trivial";
        Cec_SuperReport( pGia, pPars, Result, p->Start );
        return Result;
    }
    p->pOriginal = pGia;
    // &miter can interleave new XOR gates and outputs. Normalize and hash
    // only the private solver model, preserving the original PI/PO order.
    p->pInitial = Gia_ManDupNormalize( pGia, 1 );
    p->pBest = Gia_ManDup( p->pInitial );
    p->pPars = pPars;
    p->pSource = "original";
    p->Result = -1;
    p->Deadline = p->Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC;
    if ( !pPars->iEngine && pPars->fRewrite )
    {
        Gia_Man_t * pNew = Drw_ManRwsat( p->pBest, 0, 0 );
        if ( pNew )
        {
            Gia_ManStop( p->pBest );
            p->pBest = pNew;
            p->pSource = "drwsat";
            pPars->nReduced++;
        }
    }
    p->fComb = !Gia_ManRegNum(p->pBest);
    Cec_SuperSchedule( p );
    nWorkers = pPars->iEngine || p->fComb ? 1 : Abc_MinInt(pPars->nProcs, p->Tail);
#ifndef SUPER_USE_PTHREADS
    nWorkers = 1;
#endif
    pWorkers = ABC_CALLOC( Cec_SuperWorker_t, nWorkers );
    for ( i = 0; i < nWorkers; i++ )
    {
        pWorkers[i].pMan = p;
        pWorkers[i].Id = i;
    }
#ifdef SUPER_USE_PTHREADS
    if ( pthread_mutex_init(&p->Mutex, NULL) )
    {
        ABC_FREE(pWorkers); Gia_ManStop(p->pBest); Gia_ManStop(p->pInitial);
        return -3;
    }
    if ( pthread_cond_init(&p->Cond, NULL) )
    {
        pthread_mutex_destroy(&p->Mutex);
        ABC_FREE(pWorkers); Gia_ManStop(p->pBest); Gia_ManStop(p->pInitial);
        return -3;
    }
    pThreads = ABC_ALLOC( pthread_t, nWorkers );
    Cec_SuperLock( p );
    for ( i = 1; i < nWorkers; i++ )
    {
        if ( pthread_create(pThreads + nCreated, NULL, Cec_SuperWorker, pWorkers + i) ) break;
        nCreated++;
    }
    // Base persistence on workers actually created, including the caller.
    p->fPersistentBmc = nCreated + 1 >= 4;
    Cec_SuperUnlock( p );
#endif
    // The caller is a worker; there is no extra spinning controller core.
    Cec_SuperWorker( pWorkers );
#ifdef SUPER_USE_PTHREADS
    for ( i = 0; i < nCreated; i++ ) pthread_join( pThreads[i], NULL );
    pthread_cond_destroy( &p->Cond );
    pthread_mutex_destroy( &p->Mutex );
    ABC_FREE( pThreads );
#else
    (void)nCreated;
#endif
    Result = p->Result;
    pGia->pCexSeq = p->pCex;
    Gia_ManStop( p->pBest );
    Gia_ManStop( p->pInitial );
    ABC_FREE( pWorkers );
    Cec_SuperReport( pGia, pPars, Result, p->Start );
    return Result;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
